import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54080_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54080 : Equation54080 G) : Equation4279 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54080 sK0 sK0 X0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54080 X0 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54080 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← h54080 X0 sK0 sK0 sK0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54080 (X0 ◇ (sK0 ◇ sK0)) sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54080 X0 X1 X1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X1]
    conv => enter [1]; rw [← l13 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4279_4512_implies_Equation54081 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54081 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK3 sK0]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l1 X1 X0 sK1 sK2]
  have l3 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l1 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l4 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ sK1 sK2 X1 X2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK1 sK2 X1 X2 sK0 sK3
    conv => enter [1]; rw [l4 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK0 ◇ sK3) sK3]
  have l7 : ∀ sK1 sK2 X1 X2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2 sK0 sK3
    conv => enter [1]; rw [l6 sK1 sK2 X1 X2 sK0 sK3]
    conv => enter [1, 2, 2, 2]; rw [l0 sK3 sK0 sK1 sK2]
  have l8 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l7 sK1 sK2 X1 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_54081_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54081 : Equation54081 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54081 X0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X1 X2 X0 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X2 X0 sK1 sK2
    conv => enter [1]; rw [h54081 X1 X2 X1 X0]
    conv => enter [1, 2]; rw [h54081 X1 X0 sK1 sK2]
  have l3 : ∀ X0 sK1 sK2 X2 X3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X2 ◇ (X3 ◇ X2))) := by
    intro X0 sK1 sK2 X2 X3
    conv => enter [1]; rw [← h54081 X0 X0 sK1 sK2]
    conv => enter [1]; rw [h54081 X0 X0 X2 X3]
  have l4 : ∀ X1 X2 X3 X0 sK1 sK2 : G, (X1 ◇ (X2 ◇ (X3 ◇ X2))) = ((X0 ◇ X1) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X2 X3 X0 sK1 sK2
    conv => enter [1]; rw [← h54081 (X0 ◇ X1) X1 X2 X3]
    conv => enter [1, 2]; rw [h54081 X1 X0 sK1 sK2]
  have l5 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X2) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [h54081 X1 X0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54081 sK0 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [l5 X1 X0 X2 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) X2]
  have l9 : ∀ X1 X2 X3 X0 sK1 sK2 : G, (X1 ◇ (X2 ◇ (X3 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X1 X2 X3 X0 sK1 sK2
    conv => enter [1]; rw [l4 X1 X2 X3 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l10 : ∀ X0 sK1 sK2 X3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 X3 sK0
    conv => enter [1]; rw [l3 X0 sK1 sK2 X0 X3]
    conv => enter [1, 2]; rw [l1 X0 X3 sK0]
  have l11 : ∀ X2 sK0 X0 sK1 sK2 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X2 sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l1 X2 X2 sK0]
    conv => enter [1]; rw [l2 X2 X2 X0 sK1 sK2]
  have l12 : ∀ X0 sK1 sK2 X2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK1 sK2 X2 X1
    conv => enter [1]; rw [← l8 X1 X0 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l13 : ∀ X1 X3 sK0 X0 sK1 sK2 : G, (X1 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X1 X3 sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [← l1 X1 X3 sK0]
    conv => enter [1]; rw [l9 X1 X1 X3 X0 sK1 sK2]
  have l14 : ∀ X1 X3 sK0 sK1 sK2 : G, (X1 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X3 sK0 sK1 sK2
    conv => enter [1]; rw [l13 X1 X3 sK0 X1 sK1 sK2]
    conv => enter [1]; rw [← l12 X1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) X1]
  have l15 : ∀ X1 sK0 X3 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X3
    conv => enter [1]; rw [l11 X1 sK0 (X1 ◇ (X1 ◇ X1)) X1 X1]
    conv => enter [1]; rw [← l14 X1 X3 sK0 X1 X1]
  have l16 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l10 X1 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [← l15 X1 sK0 X1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54081 (sK1 ◇ (sK2 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 sK0]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54081 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← h54081 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK1 sK2]
    conv => enter [1, 2]; rw [← h54081 sK1 sK2 sK1 sK2]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l20 y z x]

theorem Equation4279_4512_implies_Equation54086 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54086 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z x x]

theorem Equation4512_54086_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54086 : Equation54086 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54086 sK0 X0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54086 sK0 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l8 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l23 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54086 (sK0 ◇ sK0) X0 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [l24 sK0]
    conv => enter [1]; rw [← h54086 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l28 sK0 X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l29 sK0 X0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l26 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [l26 sK0 sK0]
    conv => enter [1]; rw [h54086 (sK0 ◇ sK0) sK0 X1]
  have l33 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [l32 sK0 X1]
    conv => enter [1, 2]; rw [l3 sK0 X1]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l35 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l33 sK0 X1]
    conv => enter [1, 2]; rw [← l19 sK0 X1]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l34 sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1, 2]; rw [← l14 sK0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1, 2]; rw [← l16 sK0]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54086 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l39 sK0 X0]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l40 X0 X1 sK0]
    conv => enter [1]; rw [← l30 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l41 y z x]

theorem Equation4279_4512_implies_Equation54090 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54090 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ X2 X0 X1 sK0 sK1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X2 X0 X1 sK0 sK1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x y x y]

theorem Equation4512_54090_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54090 : Equation54090 G) : Equation4279 G := by
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
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54090 ((sK0 ◇ sK0) ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ X3 X0 X1 X2 : G, (X3 ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h54090 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54090 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54090 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54090 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h54090 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l17 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l10 X3 X0 X1 X2]
  have l18 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l19 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l22 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l18 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ X1)]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l19 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 X0 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l26 sK0 X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [h54090 X0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l21 sK0 X0]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (((sK0 ◇ sK0) ◇ X1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54090 X0 X1 ((sK0 ◇ sK0) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l21 sK0 X1]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l32 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l31 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l29 sK0 X0]
  have l33 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l32 X0 X1 sK0]
    conv => enter [1]; rw [← l28 sK0 X1]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l33 X0 X1 sK0]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l34 y z x]

theorem Equation4279_4512_implies_Equation54093 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54093 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X4 ◇ X3)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [← h4279 X0 X0 X1]
    conv => enter [1]; rw [h4279 X0 X3 X4]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X1) X3]
    conv => enter [1, 1]; rw [← h4279 X0 X1 X2]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X3]
  have l5 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l5 X1 X2 X3 X3 X1]
    conv => enter [1, 2]; rw [← h4279 X0 X3 X1]
  have l7 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l6 X3 X4 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l7 x y x x y]
  conv => enter [1]; rw [l4 x y z x]

theorem Equation4512_54093_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54093 : Equation54093 G) : Equation4279 G := by
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
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h54093 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h54093 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54093 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l17 sK0]
  have l19 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l19 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1, 2]; rw [← l28 sK0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l28 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l30 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l34 sK0 X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [l35 sK0 X0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l31 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1]; rw [← h54093 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l20 sK0 X0]
    conv => enter [1]; rw [l38 sK0 X0]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [l39 sK0 X0]
  have l41 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l36 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l40 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [l42 sK0 X0]
  have l44 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ sK0))) = ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54093 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l45 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l31 sK0 X0]
    conv => enter [1]; rw [h54093 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l46 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54093 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l6 sK0]
  have l47 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54093 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← l36 sK0 X0]
  have l48 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54093 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l32 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))]
    conv => enter [1, 2]; rw [← h54093 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l49 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54093 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l31 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))]
    conv => enter [1, 2]; rw [← h54093 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l47 sK0 X0]
  have l51 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l46 X0 sK0]
  have l52 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l45 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l53 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l44 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l54 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l50 sK0 X0]
  have l55 : ∀ sK0 X0 : G, (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l20 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l51 sK0 X0]
  have l56 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l52 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l16 sK0 X0 X1]
  have l57 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l53 X1 sK0 X0]
    conv => enter [1]; rw [← l48 X0 (sK0 ◇ sK0) sK0]
  have l58 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l55 sK0 X0]
  have l59 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ ((X0 ◇ X1) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l56 sK0 X0 X1]
    conv => enter [1, 2]; rw [l20 sK0 (X0 ◇ X1)]
  have l60 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l57 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ sK0)]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l43 sK0 X0]
    conv => enter [1]; rw [l58 sK0 X0]
  have l62 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l59 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l36 sK0 (X0 ◇ X1)]
  have l63 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l60 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l41 sK0 X0 X1]
  have l64 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l62 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l65 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l61 sK0 X0]
    conv => enter [1]; rw [l63 X0 sK0 X1]
  have l66 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l49 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l64 X1 sK0 X0]
  have l67 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l65 sK0 X0 sK0]
    conv => enter [1]; rw [← l66 X0 sK0 sK0]
  have l68 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l54 sK0 X0]
    conv => enter [1]; rw [← l67 sK0 X0]
  have l69 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54093 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l68 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l69 y z x]

theorem Equation4279_4512_implies_Equation54094 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54094 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK2 sK2]
  have l1 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4279 X0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK2 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4279 X0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4279 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l9 x y z x z]

theorem Equation4512_54094_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54094 : Equation54094 G) : Equation4279 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54094 sK0 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54094 (sK0 ◇ sK0) X0 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h54094 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54094 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l21 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54094 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l26 sK0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1]; rw [h54094 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l32 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l31 X0 X1 sK0]
    conv => enter [1]; rw [← l21 sK0]
  intro x y z
  conv => enter [1]; rw [← l32 y z x]

theorem Equation4279_4512_implies_Equation54095 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54095 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X4 ◇ X3)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [← h4279 X0 X0 X1]
    conv => enter [1]; rw [h4279 X0 X3 X4]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X1) X3]
    conv => enter [1, 1]; rw [← h4279 X0 X1 X2]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X3]
  have l5 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l5 X1 X2 X3 X3 X1]
    conv => enter [1, 2]; rw [← h4279 X0 X3 X1]
  have l7 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l6 X3 X4 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x y x x w]
  conv => enter [1]; rw [l4 x w z x]

theorem Equation4512_54095_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54095 : Equation54095 G) : Equation4279 G := by
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
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54095 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [← h54095 (sK0 ◇ sK0) X1 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h54095 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0 sK0]
    conv => enter [1]; rw [l11 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 X0 sK0]
    conv => enter [1]; rw [h54095 (sK0 ◇ sK0) sK0 sK1 (sK2 ◇ sK1)]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54095 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54095 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h54095 (sK0 ◇ sK0) X0 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54095 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1, 2]; rw [l10 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK0]
  have l29 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l25 sK0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l28 sK0]
  have l32 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l32 sK1 sK0 sK2 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
  have l37 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l38 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0 sK1 sK2]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 sK0 sK0]
    conv => enter [1]; rw [← l38 sK0 X0 sK0 sK0]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l31 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1]; rw [← l41 sK0 X0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l44 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54095 sK0 sK0 sK0 sK0]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l45 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l47 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l46 sK0 X0]
    conv => enter [1]; rw [← l43 sK0 X0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l47 sK0 X0]
  have l49 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l48 sK0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h54095 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X1]
  have l50 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l48 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l49 X1 sK0 sK0]
  have l51 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54095 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK0]
    conv => enter [1]; rw [← l45 sK0]
  intro x y z
  conv => enter [1]; rw [← l52 y z x]

theorem Equation4279_4512_implies_Equation54098 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54098 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z x w]

theorem Equation4512_54098_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54098 : Equation54098 G) : Equation4279 G := by
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
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54098 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54098 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54098 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l10 : ∀ sK0 X0 X2 X3 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X3 ◇ X2))) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [← h54098 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [h54098 X0 sK0 X2 X3]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h54098 (sK0 ◇ sK0) X0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54098 sK1 sK2 sK0 sK0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54098 sK0 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54098 sK0 sK0 sK0 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l35 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l33 sK0 X0]
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 sK0 sK0]
    conv => enter [1]; rw [← l35 sK0 X0 sK0 sK0]
  have l37 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54098 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l37 y z x]

theorem Equation4279_4512_implies_Equation54102 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54102 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK1 sK0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4279 X0 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4279 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK2]
  have l3 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l3 X1 X0 sK0 sK1]
  have l5 : ∀ sK0 sK1 X1 X2 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [l3 sK0 sK1 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK0 sK1 X1 X2 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [l5 sK0 sK1 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l6 sK0 sK1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4279 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK2]
  have l9 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l8 sK0 sK1 X1 X2 sK2]
    conv => enter [1, 2, 2, 1]; rw [l0 sK1 sK0]
  have l10 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l9 sK0 sK1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l10 sK0 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_54102_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54102 : Equation54102 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54102 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54102 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK2]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54102 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l3 X0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 X0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 ((sK2 ◇ sK1) ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4279_4512_implies_Equation54103 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54103 G := by
  have l0 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h4279 X0 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_54103_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54103 : Equation54103 G) : Equation4279 G := by
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
  have l11 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l12 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54103 ((sK0 ◇ sK0) ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54103 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1))) = ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54103 (sK0 ◇ X0) (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2]; rw [← l8 sK0 X0]
  have l15 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54103 sK0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l16 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54103 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54103 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54103 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54103 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54103 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l21 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h54103 X0 X1 X2]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54103 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54103 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l24 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l21 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l28 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l16 X2 X0 X1 X3]
  have l29 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l15 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l30 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l14 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l31 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l32 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l12 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l33 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l24 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l37 : ∀ sK0 X1 : G, (sK0 ◇ (X1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l29 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← h54103 (sK0 ◇ sK0) X1 sK0]
  have l38 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l30 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h54103 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l39 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l31 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h54103 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l40 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l32 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l41 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l33 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0 sK0]
    conv => enter [1]; rw [← l35 sK0 sK0]
  have l43 : ∀ sK0 X1 : G, (sK0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l37 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [← l38 X1 sK0 X0]
  have l45 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [← l39 X1 sK0 X0]
  have l46 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l40 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ X1)]
  have l47 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l41 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l48 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l44 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 X1]
  have l49 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l45 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l50 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [l34 sK0 X0]
    conv => enter [1]; rw [l46 sK0 X0 X1]
  have l51 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l48 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l8 sK0 (X0 ◇ X1)]
  have l52 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l49 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 sK0 (X0 ◇ X1)]
  have l53 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l50 sK0 X1 X0]
  have l54 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l51 sK0 X1 X0]
  have l55 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l52 sK0 X1 X0]
  have l56 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l54 sK0 X1 X0]
  have l57 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l55 sK0 X1 X0]
  have l58 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l56 sK0 sK0 sK0]
    conv => enter [1]; rw [← l57 sK0 sK0 sK0]
  have l59 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l58 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l60 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l58 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l61 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l59 sK0]
  have l62 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l58 sK0]
    conv => enter [1]; rw [l61 sK0]
  have l63 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l19 sK1 sK2 X0]
    conv => enter [1]; rw [← h54103 (sK2 ◇ sK1) X0 X0]
  have l64 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (((sK2 ◇ sK1) ◇ X0) ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h54103 X0 X1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK2 X0]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l19 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK2 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l66 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l43 sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l65 sK0 sK1 sK2]
  have l67 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l64 X0 X1 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) X0 (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l68 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
    conv => enter [1]; rw [l66 sK0 sK2 sK1]
  have l69 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l68 sK1 sK2 sK0]
  have l70 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l68 sK1 sK2 sK0]
    conv => enter [1]; rw [← l69 sK0 sK1 sK2]
  have l71 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l36 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l11 sK2 sK1 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l72 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l67 (sK2 ◇ sK1) (sK0 ◇ sK0) sK2 sK1]
    conv => enter [1]; rw [← l71 sK2 sK0 sK1]
  have l73 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 (sK0 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [l72 sK2 sK1 sK0]
  have l74 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l70 sK1 sK2 sK0]
    conv => enter [1]; rw [l73 sK0 sK1 sK2]
  have l75 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54103 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1, 2]; rw [← h54103 sK0 X0 sK0]
  have l76 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l75 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (X0 ◇ sK0))]
  have l77 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l76 X1 sK0 X0]
    conv => enter [1]; rw [← l47 sK0 (sK0 ◇ sK0) sK0 X0]
  have l78 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l77 X1 sK0 X0]
  have l79 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l78 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l80 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l79 sK0 sK0 X0]
    conv => enter [1]; rw [← l28 (sK0 ◇ sK0) sK0 X0 sK0]
  have l81 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l80 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l82 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l81 sK0 X0]
  have l83 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l60 sK0 sK0]
    conv => enter [1]; rw [l82 sK0 X0]
  have l84 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l83 sK0 X0]
  have l85 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l58 sK0]
    conv => enter [1]; rw [l84 sK0 X0]
  have l86 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54103 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2]; rw [← l85 sK0 X0]
  have l87 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l86 X1 sK0 X0]
  have l88 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l87 X0 sK0 sK0]
  have l89 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l88 sK0 X0]
    conv => enter [1, 2]; rw [← l42 sK0]
  have l90 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l89 sK0 X0]
    conv => enter [1, 2]; rw [← l58 sK0]
  have l91 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l62 sK0]
    conv => enter [1]; rw [l90 sK0 X0]
  have l92 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK2]
    conv => enter [1]; rw [← l74 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l92 x y z]

theorem Equation4279_4512_implies_Equation54106 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54106 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK1 sK1]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4279 X0 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4279 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK2]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4279 sK1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4279 sK1 X1 X0]
  have l4 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [h4279 sK1 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l5 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [l4 sK1 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X1 X2 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X1 X2 sK2
    conv => enter [1]; rw [l5 sK1 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK2]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l9 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 X1 X2 sK2]
    conv => enter [1, 2, 2, 1]; rw [← l0 sK0 sK1]
  have l10 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l9 sK0 sK1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l10 sK0 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_54106_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54106 : Equation54106 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54106 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2, 2]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54106 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X0]
    conv => enter [1]; rw [← l2 X1 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54106 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 (X1 ◇ (X1 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

theorem Equation4279_4512_implies_Equation54107 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54107 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z y y]

theorem Equation4512_54107_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54107 : Equation54107 G) : Equation4279 G := by
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
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ X1))) = ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54107 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54107 X0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54107 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54107 X0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ X1))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l4 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l10 X1 sK0 sK0]
  have l13 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X1]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l14 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l18 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [← l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l23 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l29 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [h54107 sK0 sK0 X1]
  have l30 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h54107 (sK0 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l31 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l30 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l32 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l29 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X1]
  have l33 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l31 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l28 sK0]
  have l34 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l32 sK0 X1]
  have l35 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h54107 ((sK0 ◇ sK0) ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← l34 sK0 X0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l37 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l35 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l33 sK0 X0 sK0]
    conv => enter [1]; rw [l37 sK0 X0 sK0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [l36 sK0]
    conv => enter [1]; rw [← h54107 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l39 sK0 X0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l40 sK0 X0]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l41 sK0 X0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l42 sK0 X0]
  have l44 : ∀ X1 sK1 sK2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ X1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [← h54107 X1 sK1 X1]
    conv => enter [1]; rw [h54107 X1 sK1 (sK2 ◇ sK1)]
  have l45 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [h54107 sK2 sK1 (sK2 ◇ sK1)]
  have l46 : ∀ X1 sK1 sK2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ X1))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [l44 X1 sK1 sK2]
    conv => enter [1]; rw [← l45 sK2 sK1]
  have l47 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l46 sK2 sK1 sK2]
    conv => enter [1]; rw [l33 sK2 sK1 sK0]
  have l48 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ sK2) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l45 sK2 sK1]
    conv => enter [1]; rw [← h54107 X0 sK1 (sK2 ◇ sK1)]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l47 sK2 sK1 sK0]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l47 sK2 sK1 sK0]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
  have l52 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l48 sK2 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
  have l53 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l47 sK2 sK1 sK0]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l54 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54107 X0 sK1 sK1]
    conv => enter [1, 2]; rw [← l48 sK2 sK1 sK1]
  have l55 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l48 sK2 sK1 (sK0 ◇ sK0)]
  have l56 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l48 sK2 sK1 (sK2 ◇ sK1)]
  have l57 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l56 sK1 sK2]
  have l58 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l53 sK2 sK1 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1 sK2]
  have l59 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l54 X0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l58 sK2 sK1 sK0]
    conv => enter [1]; rw [l48 sK2 sK1 (sK2 ◇ sK1)]
  have l61 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l48 sK2 sK1 sK2]
    conv => enter [1]; rw [← l59 sK1 sK2 sK2]
  have l62 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l61 sK2 sK1]
    conv => enter [1]; rw [l48 sK2 sK1 (sK2 ◇ sK1)]
  have l63 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
    conv => enter [1, 1]; rw [l57 sK1 sK2]
  have l64 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l63 sK1 sK2 X0]
  have l65 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l62 sK1 sK2]
    conv => enter [1]; rw [l57 sK1 sK2]
  have l66 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← l62 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
  have l67 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l64 sK1 sK2 X0]
    conv => enter [1]; rw [← l66 sK2 sK1 X0]
  have l68 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l67 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l69 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l48 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l52 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l48 sK2 sK1 (sK2 ◇ sK1)]
  have l70 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l60 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l60 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l60 sK0 sK1 sK2]
  have l72 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54107 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l60 sK0 sK1 sK2]
  have l73 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l72 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l74 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l71 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l75 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l73 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l26 sK0 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l69 sK2 sK1 sK0]
  have l77 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l75 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l70 sK2 sK1 sK0]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l79 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l77 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l80 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l79 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l65 sK2 sK1]
  have l81 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l43 sK0 sK0]
    conv => enter [1]; rw [l80 sK0 sK0 sK2 sK1]
  have l82 : ∀ sK0 X0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 1]; rw [l81 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l83 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l84 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h54107 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l78 sK0 sK1 sK2]
  have l85 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l84 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l68 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l86 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l83 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l81 sK0 sK2 sK1]
  have l87 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l82 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK1]
    conv => enter [1]; rw [← l85 X0 sK1 sK2 sK0]
  have l88 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l87 sK0 X0 sK1 sK2]
  have l89 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l88 sK0 X0 sK1 sK2]
  have l90 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l89 sK0 X0 sK1 sK2]
  have l91 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l90 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 sK1 sK2]
  have l92 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l91 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l48 sK2 sK1 (sK2 ◇ sK1)]
  have l93 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l92 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l81 sK0 sK2 sK1]
  have l94 : ∀ X1 sK2 sK1 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ X1))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK2 sK1
    conv => enter [1]; rw [← h54107 X1 sK2 X1]
    conv => enter [1]; rw [h54107 X1 sK2 sK1]
  have l95 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
  have l96 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l95 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l86 sK2 sK0 sK1]
  have l97 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l93 sK0 sK2 sK1]
    conv => enter [1]; rw [← l96 sK1 sK2 sK0]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l97 sK0 sK1 sK2]
  have l99 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l98 sK0 sK0 sK2]
    conv => enter [1]; rw [← h54107 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l99 x y z]

theorem Equation4279_4512_implies_Equation54110 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54110 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK1 sK2]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4279 X0 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4279 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK2]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0 sK1 sK2]
  have l5 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l0 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l6 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK2]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK0 sK1]
  have l10 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK1 sK2 X1 X2]
    conv => enter [1, 2, 2, 1]; rw [← l1 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l10 sK0 sK1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0 sK0]
  have l12 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l11 sK0 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_54110_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54110 : Equation54110 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54110 X0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54110 X0 X1 X0]
    conv => enter [1]; rw [← h54110 X2 X1 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54110 X0 sK0 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54110 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54110 X0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l13 X0 sK0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54110 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK0 X1]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l18 X0 X1 sK0]
    conv => enter [1]; rw [← l16 sK0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l23 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l25 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l23 sK1 sK2 sK0]
    conv => enter [1]; rw [← l24 sK0]
  intro x y z
  conv => enter [1]; rw [← l25 y z x]

theorem Equation4279_4512_implies_Equation54111 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54111 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK2 sK2]
  have l1 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4279 X0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK2 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4279 X0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4279 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l9 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l8 X0 X1 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l11 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 X0 sK0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) X0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l15 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l14 sK0 sK1 X4]
    conv => enter [1]; rw [← l9 X2 X3 X4 sK0 sK1]
  have l16 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l15 sK0 sK1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  intro x y z
  conv => enter [1]; rw [l16 x y z y z]

theorem Equation4512_54111_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54111 : Equation54111 G) : Equation4279 G := by
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
  have l7 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l8 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (X1 ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54111 ((sK0 ◇ sK0) ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [← h54111 X0 sK2 sK1]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54111 X0 sK0 sK0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 (X1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54111 X0 X1 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54111 X0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l9 sK1 sK2 X0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (X1 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l8 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54111 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l19 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ (X1 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l16 X1 sK0 X1]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l4 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l21 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ (X1 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0
    conv => enter [1]; rw [l19 X1 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK0]
  have l23 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ (X1 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0
    conv => enter [1]; rw [l21 X1 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54111 X0 sK2 sK2]
    conv => enter [1, 2]; rw [← l15 sK1 sK2 sK2]
  have l26 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l15 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l27 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l25 X0 sK2 sK1]
    conv => enter [1]; rw [← l7 sK2 sK1 sK1]
  have l28 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l26 sK2 sK1]
    conv => enter [1]; rw [← l7 sK2 sK1 sK1]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2 sK1]
    conv => enter [1]; rw [l27 sK1 sK2 sK1]
  have l30 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l28 sK2 sK1]
    conv => enter [1]; rw [← l29 sK1 sK2]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l15 sK1 sK2 sK1]
    conv => enter [1]; rw [← l30 sK2 sK1]
  have l32 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l33 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l18 sK0 (X1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54111 X0 X1 sK0]
  have l34 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK0]
  have l35 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l18 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK2 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l36 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l35 sK2 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l38 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l33 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) (X0 ◇ (X1 ◇ X0))]
  have l39 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l36 sK2 sK0 sK0]
  have l40 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l38 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ X0))]
  have l41 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l39 sK0 sK2]
    conv => enter [1, 2]; rw [← l37 sK0]
  have l42 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l40 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X0))]
  have l43 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l42 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X1 sK0]
  have l44 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l43 sK0 X1]
  have l45 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK1]
    conv => enter [1]; rw [h54111 sK1 sK2 sK0]
  have l46 : ∀ X1 sK0 X0 X2 : G, ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (sK0 ◇ (X2 ◇ X2))) := by
    intro X1 sK0 X0 X2
    conv => enter [1, 2]; rw [h54111 X0 X1 sK0]
    conv => enter [1]; rw [h54111 (X1 ◇ (sK0 ◇ sK0)) sK0 X2]
  have l47 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [← l46 X1 sK0 X0 sK0]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l15 sK1 sK2 sK1]
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
  have l49 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l47 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) (X0 ◇ (X1 ◇ X0))]
  have l50 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l49 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X1 sK0]
  have l51 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0 sK0]
    conv => enter [1]; rw [← l50 sK0 sK0]
  have l52 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1, 2]; rw [← l24 sK0]
  have l53 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l52 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l54 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [h54111 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK0]
  have l55 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [← l54 sK0 sK2]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0]
    conv => enter [1]; rw [← l55 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l56 x y z]

theorem Equation4279_4512_implies_Equation54112 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54112 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X4 ◇ X3)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [← h4279 X0 X0 X1]
    conv => enter [1]; rw [h4279 X0 X3 X4]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X1) X3]
    conv => enter [1, 1]; rw [← h4279 X0 X1 X2]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X3]
  have l5 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l5 X1 X2 X3 X3 X1]
    conv => enter [1, 2]; rw [← h4279 X0 X3 X1]
  have l7 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l6 X3 X4 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x y x x w]
  conv => enter [1]; rw [l4 x w z y]

theorem Equation4512_54112_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54112 : Equation54112 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l4 sK0]
    conv => enter [1]; rw [← h54112 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54112 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [l8 sK0 X0]
  have l12 : ∀ sK0 X0 X2 X3 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [← h54112 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [h54112 sK0 X0 X2 X3]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54112 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4512 sK0 (X1 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1, 1]; rw [← h54112 X0 X1 sK0 sK0]
  have l15 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l14 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l15 sK0 X1 X2 X0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l22 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0]
  have l23 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l19 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l4 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l22 sK0]
  have l26 : ∀ sK0 X1 X2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l12 sK0 X1 sK0 X2]
    conv => enter [1]; rw [l23 sK0 X1 X2 sK0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l24 sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54112 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← h54112 X0 sK2 sK1 sK1]
  have l30 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54112 sK1 sK2 sK0 sK0]
  have l31 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [h54112 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← h54112 X0 sK0 sK2 (sK0 ◇ sK0)]
  have l32 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [h54112 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK0)) X0]
  have l33 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l32 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK0 ◇ sK0) X0]
  have l34 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h54112 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l31 sK2 sK1 sK0 sK0]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l30 sK0 sK2 sK1]
    conv => enter [1]; rw [h54112 (sK0 ◇ sK0) sK2 sK1 (sK2 ◇ sK1)]
  have l36 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l33 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l26 sK0 sK2 X0]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l38 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l36 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l28 sK0 sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l38 sK1 sK2 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2]
  have l41 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l42 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [l29 sK1 sK2 X1]
    conv => enter [1]; rw [← h54112 X0 X1 sK2 X1]
  have l43 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l42 sK2 sK1 X0 X1]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l41 sK1 sK2]
    conv => enter [1]; rw [l38 sK1 sK2 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) sK0]
  have l45 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l38 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [l45 sK0 sK0 X0 sK0]
  have l47 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l46 sK0 X0]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l34 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l49 : ∀ sK0 X0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 1]; rw [l34 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l50 : ∀ sK0 X0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l49 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← l9 sK2 sK1 X0]
  have l51 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l48 sK0 sK2 sK1]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l52 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l50 sK0 X0 sK2 sK1]
  have l53 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [← l52 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [l47 sK0 X0 sK1 sK2]
  have l54 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l55 : ∀ X1 X3 X0 X2 sK0 : G, ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (sK0 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X3 X0 X2 sK0
    conv => enter [1, 2]; rw [← h54112 X3 X1 X0 X2]
    conv => enter [1]; rw [h54112 (X1 ◇ X3) X3 sK0 (sK0 ◇ sK0)]
  have l56 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54112 X1 X2 X3 (X0 ◇ X3)]
    conv => enter [1, 2, 2]; rw [h54112 X3 X0 sK0 (sK0 ◇ sK0)]
  have l57 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l38 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [h54112 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 (sK0 ◇ sK0)]
  have l58 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l40 sK0 sK1 sK2]
    conv => enter [1]; rw [l57 sK0 X0]
  have l59 : ∀ sK2 sK1 X3 X2 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (X3 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK2 sK1 X3 X2 sK0 X0
    conv => enter [1]; rw [l43 sK2 sK1 sK2 X2]
    conv => enter [1]; rw [l56 sK2 X2 X3 sK0 X0]
  have l60 : ∀ X1 X3 X0 X2 sK0 : G, (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = (sK0 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X3 X0 X2 sK0
    conv => enter [1]; rw [h4512 X1 X3 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
    conv => enter [1]; rw [l55 X1 X3 X0 X2 sK0]
  have l61 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
    conv => enter [1]; rw [l58 sK0 sK1 sK2 X0]
  have l62 : ∀ sK0 sK1 sK2 X3 X2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X3 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1 sK2 X3 X2 X0
    conv => enter [1]; rw [← l51 sK2 sK1 sK0]
    conv => enter [1]; rw [l59 sK2 sK1 X3 X2 sK0 X0]
  have l63 : ∀ X1 X3 sK0 : G, (X1 ◇ (X3 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X3 sK0
    conv => enter [1, 2, 2]; rw [l12 sK0 X1 X1 X1]
    conv => enter [1]; rw [l60 X1 X3 X1 X1 sK0]
  have l64 : ∀ sK0 sK1 sK2 X3 X2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X3 ◇ (X2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X3 X2
    conv => enter [1]; rw [l62 sK0 sK1 sK2 X3 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l61 sK1 sK2 sK0 sK0]
  have l65 : ∀ sK1 sK2 X1 X3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X3 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 X1 X3 sK0
    conv => enter [1]; rw [l61 sK1 sK2 sK0 X3]
    conv => enter [1]; rw [← l63 X1 X3 sK0]
  have l66 : ∀ sK1 sK2 X3 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X3 ◇ (X2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X3 X2
    conv => enter [1]; rw [l54 sK1 sK2 sK1]
    conv => enter [1]; rw [l64 sK1 sK1 sK2 X3 X2]
  have l67 : ∀ sK1 sK2 X1 X3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 X1 X3 sK0
    conv => enter [1]; rw [l65 sK1 sK2 X1 X3 sK0]
    conv => enter [1, 2, 2]; rw [← l28 sK0 X1]
  have l68 : ∀ sK1 sK2 X1 X3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X3 sK0
    conv => enter [1]; rw [l67 sK1 sK2 X1 X3 sK0]
    conv => enter [1, 2, 2]; rw [l40 sK0 sK1 sK2]
  have l69 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l68 sK1 sK2 X1 sK1 sK1]
    conv => enter [1, 2]; rw [← l66 sK1 sK2 sK1 sK1]
  have l70 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l69 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l71 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l70 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l72 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l71 sK1 sK2 X0]
    conv => enter [1]; rw [l53 sK2 sK1 X0 sK0]
  have l73 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l54 sK1 sK2 sK1]
    conv => enter [1]; rw [← l72 sK1 sK2 X0 sK1]
  have l74 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l73 sK1 sK2 (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))]
    conv => enter [1]; rw [← h54112 X0 X1 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  intro x y z
  conv => enter [1]; rw [l74 x x y z]

theorem Equation4279_4512_implies_Equation54114 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54114 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK2 sK0]
  have l1 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK2 sK0]
  have l2 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4279 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK2 sK3 sK0]
  have l3 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l3 X1 X0 sK1 sK2]
  have l5 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l3 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK1 sK2 X1 X2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK2 X1 X2 sK0 sK3
    conv => enter [1]; rw [l6 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK2 ◇ (sK0 ◇ sK2)) sK3]
  have l9 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 X1 X2 sK0 sK3]
    conv => enter [1, 2, 2, 1]; rw [← l0 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l9 sK1 sK2 X1 X2 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK1 sK1 sK1]
  have l11 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54114_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54114 : Equation54114 G) : Equation4279 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54114 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ X2 X1 X3 sK0 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ X1))) = ((sK0 ◇ X1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X1 X3 sK0 X0
    conv => enter [1]; rw [← h54114 (sK0 ◇ X1) X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X0 sK0 X1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X2 X1 X3 sK0 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X2 X1 X3 sK0 X0
    conv => enter [1]; rw [l2 X2 X1 X3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ X2 X1 X3 sK0 : G, (X2 ◇ (X1 ◇ (X3 ◇ X1))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X1 X3 sK0
    conv => enter [1]; rw [l5 X2 X1 X3 sK0 X2]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X2]
  have l7 : ∀ sK0 X2 X1 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := by
    intro sK0 X2 X1 X3
    conv => enter [1, 2]; rw [l4 sK0 X1]
    conv => enter [1]; rw [← l6 X2 X1 X3 sK0]
  have l8 : ∀ sK0 X2 X1 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := by
    intro sK0 X2 X1 X3
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X2 X1 X3]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X2 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h54114 X1 (sK0 ◇ (sK0 ◇ sK0)) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h54114 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 X1 sK0 sK0 sK0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 X1]
    conv => enter [1]; rw [← l9 sK0 X1 X1]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 (X1 ◇ (sK0 ◇ X1))]
    conv => enter [1]; rw [← h54114 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4279_4512_implies_Equation54115 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54115 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z y w]

theorem Equation4512_54115_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54115 : Equation54115 G) : Equation4279 G := by
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
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54115 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [← h54115 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l13 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [h54115 X2 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 X2 X3 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X3 ◇ X2))) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [← h54115 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [h54115 sK0 X0 X2 X3]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h54115 (sK0 ◇ sK0) X0 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h54115 (sK0 ◇ sK0) X0 sK0 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54115 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l21 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X0 X1 sK0
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l13 X2 X0 X1 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) X0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 sK0 X1]
    conv => enter [1]; rw [l21 sK0 X0 X1 sK0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1, 2]; rw [l24 sK0 X0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l30 sK0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l32 sK0 X0]
  have l34 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54115 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← h54115 X0 sK2 sK1 sK1]
  have l35 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l8 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54115 sK1 sK2 sK0 sK0]
  have l36 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54115 sK1 sK2 sK0 sK0]
  have l37 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54115 sK1 sK2 sK0 sK0]
  have l38 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54115 X0 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h54115 sK1 sK2 sK0 sK0]
  have l39 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h54115 (sK2 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h54115 sK1 sK2 sK0 sK0]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l39 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1))]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54115 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l38 sK0 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l37 sK0 sK2 sK1]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK2 sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l36 sK0 sK2 sK1]
    conv => enter [1]; rw [l24 sK0 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [l35 sK0 sK2 sK1]
  have l45 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
  have l46 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [← l41 sK0 sK0 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
  have l50 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l48 sK0 sK2]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
  have l53 : ∀ X1 X3 X0 X2 sK0 : G, ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X3 X0 X2 sK0
    conv => enter [1, 2]; rw [← h54115 X3 X1 X0 X2]
    conv => enter [1]; rw [h54115 (X1 ◇ X3) X3 (sK0 ◇ sK0) sK0]
  have l54 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [h54115 (X0 ◇ X1) X2 (sK0 ◇ sK0) sK0]
  have l55 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54115 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [h54115 sK0 X0 (sK0 ◇ sK0) sK0]
  have l56 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54115 sK1 sK2 (sK0 ◇ sK0) sK0]
  have l57 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l34 sK1 sK2 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [h54115 sK2 X0 (sK0 ◇ sK0) sK0]
  have l58 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l57 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 sK2 ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l59 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0]
    conv => enter [1]; rw [← l33 sK0 sK2]
  have l60 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l55 sK0 X0]
  have l61 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 X2]
    conv => enter [1]; rw [← l54 X0 X1 X2 sK0]
  have l62 : ∀ sK0 X1 X3 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro sK0 X1 X3 X0 X2
    conv => enter [1]; rw [l33 sK0 X3]
    conv => enter [1]; rw [← l53 X1 X3 X0 X2 sK0]
  have l63 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l58 sK1 sK2 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l33 sK0 X0]
  have l64 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l60 sK0 X0]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l65 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l61 sK0 X0 sK0 X2]
    conv => enter [1, 2]; rw [← l14 sK0 X2 sK0 X0]
  have l66 : ∀ sK0 X1 X3 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro sK0 X1 X3 X0 X2
    conv => enter [1]; rw [l62 sK0 X1 X3 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X3 (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
  have l67 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l63 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l50 sK0 sK2]
  have l68 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l64 sK0 sK0 sK1 sK2]
  have l69 : ∀ sK0 X1 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X3 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X3
    conv => enter [1]; rw [l66 sK0 X1 X3 sK0 sK0]
  have l70 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l67 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l52 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l52 sK0 sK1 sK2]
    conv => enter [1]; rw [l68 sK0 X0 sK1 sK2]
  have l72 : ∀ sK0 X1 X3 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 X1 X3 sK1 sK2
    conv => enter [1]; rw [l69 sK0 X1 X3]
    conv => enter [1, 2, 2]; rw [l64 sK0 X1 sK1 sK2]
  have l73 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l70 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l71 sK0 sK1 sK2 sK1]
  have l74 : ∀ sK0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [l72 sK0 X1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l70 sK1 sK2 sK0 sK0]
  have l75 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l59 sK1 sK2 sK1]
    conv => enter [1]; rw [l74 sK1 X1 sK1 sK2]
  have l76 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54115 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l59 sK1 sK2 sK0]
  have l77 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l76 X0 X1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l75 sK1 sK2 X1]
  have l78 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l51 sK0 sK0 sK0]
    conv => enter [1]; rw [← l77 X0 X1 sK0 sK0 sK0]
  have l79 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l78 sK0 X0 X1]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l80 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l73 sK1 sK2 sK1]
    conv => enter [1]; rw [← l79 X0 X1 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l80 x x y z]

theorem Equation4279_4512_implies_Equation54137 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54137 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w x]

theorem Equation4512_54137_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54137 : Equation54137 G) : Equation4279 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54137 sK0 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54137 sK0 X0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54137 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h54137 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4279_4512_implies_Equation54138 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54138 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK1]
  have l1 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK2 sK0]
  have l2 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4279 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK2 sK3 sK0]
  have l3 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l3 X1 X0 sK1 sK2]
  have l5 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l3 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK1 sK2 X1 X2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK2 X1 X2 sK0 sK3
    conv => enter [1]; rw [l6 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK3]
  have l9 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 X1 X2 sK0 sK3]
    conv => enter [1, 2, 2, 1]; rw [← l0 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l9 sK1 sK2 X1 X2 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK1 sK1 sK1]
  have l11 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54138_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54138 : Equation54138 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54138 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54138 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

theorem Equation4279_4512_implies_Equation54142 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54142 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w y]

theorem Equation4512_54142_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54142 : Equation54142 G) : Equation4279 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54142 sK0 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54142 X0 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54142 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l5 sK0 X1]
    conv => enter [1]; rw [← h54142 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4279_4512_implies_Equation54143 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54143 G := by
  have l0 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK2]
  have l2 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4279 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l2 sK2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0 sK0 sK2]
  have l5 : ∀ sK0 sK2 X1 X2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK2 X1 X2 X0
    conv => enter [1]; rw [l0 sK0 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK0 sK2 X1 X2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK2 X1 X2 X0
    conv => enter [1]; rw [l5 sK0 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l4 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK0))]
  have l8 : ∀ sK0 sK2 X1 X2 sK3 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK2 X1 X2 sK3
    conv => enter [1]; rw [l6 sK0 sK2 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4279 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK3]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
  have l10 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 sK2 X1 X2 sK3]
    conv => enter [1, 2, 2, 1]; rw [l1 sK0 sK2 sK1]
  have l11 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l10 sK1 sK2 X1 X2 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK1 sK1 sK1]
  have l12 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l11 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

theorem Equation4512_54143_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54143 : Equation54143 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [h54143 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) X1]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54143 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54143 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK2]
  have l4 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro X1 sK2 sK1 X0
    conv => enter [1, 2, 2]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← h54143 X0 (sK1 ◇ (sK2 ◇ sK1)) X1 (sK2 ◇ sK1)]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (X1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X0 X0]
    conv => enter [1]; rw [← l4 X1 sK2 sK1 X0]
  have l6 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h54143 sK1 sK2 (sK2 ◇ sK1) sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54143 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1]; rw [← h54143 X0 X1 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

end Semigroup5
