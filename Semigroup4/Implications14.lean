import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

theorem Equation75_4283_4512_implies_Equation56 (G : Type*) [Magma G] (h75 : Equation75 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation56 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← h4283 X0 X1]
    conv => enter [1]; rw [← h75 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h4283 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h75 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4283 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h75 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l0 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l0 (sK1 ◇ sK1) sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1, 2, 2, 2]; rw [l2 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h75 sK1 sK1]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1, 2, 2]; rw [l2 (sK1 ◇ sK1) sK1]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l12 sK1]
    conv => enter [1]; rw [l13 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l14 sK1]
    conv => enter [1]; rw [l6 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l15 sK1 X0]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK1 sK0]
    conv => enter [1]; rw [l16 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation75_4283_implies_Equation43 (G : Type*) [Magma G] (h75 : Equation75 G) (h4283 : Equation4283 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← h4283 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h75 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation75_4283_4512_implies_Equation4276 (G : Type*) [Magma G] (h75 : Equation75 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation4276 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← h4283 X0 X1]
    conv => enter [1]; rw [← h75 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h4283 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h75 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4283 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h75 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2, 2, 2]; rw [l2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h75 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1, 2, 2]; rw [l2 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [l13 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = X0 := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [l15 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l16 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l17 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation56_4320_4512_implies_Equation66 (G : Type*) [Magma G] (h56 : Equation56 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4320 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h56 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← h4320 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [h56 X0 sK1]
    conv => enter [1]; rw [← l2 X0 sK1]
    conv => enter [1]; rw [← h56 X0 sK1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h56 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l7 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h56 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l7 sK1]
    conv => enter [1]; rw [← h56 X0 (sK1 ◇ sK1)]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (((sK1 ◇ sK1) ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l8 ((sK1 ◇ sK1) ◇ sK1) sK1]
    conv => enter [1]; rw [← h4320 ((sK1 ◇ sK1) ◇ sK1) X0]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l9 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ sK1))]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [← l8 X0 sK1]
    conv => enter [1]; rw [← l10 X0 sK1]
    conv => enter [1]; rw [l8 X0 sK1]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4320 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l11 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4320 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4320 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l6 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l11 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l12 sK1 sK0]
  have l20 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h4320 X0 X1]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [l17 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l24 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← l12 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l14 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l11 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l27 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4320 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l27 X2 X0 X1]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l30 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l31 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l33 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l21 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l34 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l20 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l35 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l36 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1 X0]
    conv => enter [1]; rw [← l29 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l37 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l33 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l38 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l34 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l35 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l40 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1]; rw [l32 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l41 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l37 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l32 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l42 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l38 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l40 sK0 sK1 X0]
  have l44 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l41 sK1 X0 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))]
  have l45 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l44 sK1 X0 sK0]
    conv => enter [1]; rw [← l43 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l11 sK1 X0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4320 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l50 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h56 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l51 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← h4320 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4320 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l51 sK1 sK0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1 sK1]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2]; rw [l42 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l45 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l59 sK0 sK1]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [l46 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l61 sK1 sK0]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [l28 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [l42 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l65 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h56 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l64 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l65 x y]

theorem Equation56_4320_4512_implies_Equation73 (G : Type*) [Magma G] (h56 : Equation56 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4320 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h56 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h4320 X0 X1]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h4320 X2 (X0 ◇ X1)]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h56 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation56_4320_4512_implies_Equation75 (G : Type*) [Magma G] (h56 : Equation56 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation75 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4320 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h56 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation56_4320_4512_implies_Equation43 (G : Type*) [Magma G] (h56 : Equation56 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4320 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h56 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4320 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4320 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation73_4512_implies_Equation66 (G : Type*) [Magma G] (h73 : Equation73 G) (h4512 : Equation4512 G) : Equation66 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h73 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h73 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l4 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 (sK1 ◇ sK1) sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l17 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h73 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l17 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l20 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) sK0]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 ((sK1 ◇ sK1) ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0))]
  have l26 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ sK1) ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation73_4512_implies_Equation56 (G : Type*) [Magma G] (h73 : Equation73 G) (h4512 : Equation4512 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h73 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h73 sK1 sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h73 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h73 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation73_4512_implies_Equation75 (G : Type*) [Magma G] (h73 : Equation73 G) (h4512 : Equation4512 G) : Equation75 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h73 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation73_4512_implies_Equation43 (G : Type*) [Magma G] (h73 : Equation73 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h73 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h73 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h73 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation66_4512_implies_Equation73 (G : Type*) [Magma G] (h66 : Equation66 G) (h4512 : Equation4512 G) : Equation73 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h66 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h66 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h66 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation65_4512_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h65 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l0 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h65 (sK0 ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1]; rw [← h65 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation53_4512_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation63_4512_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h63 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h63 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation56_75_implies_Equation4276 (G : Type*) [Magma G] (h56 : Equation56 G) (h75 : Equation75 G) : Equation4276 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [h56 X0 sK1]
    conv => enter [1]; rw [← h75 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [h56 X0 sK0]
    conv => enter [1]; rw [← h75 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation55_4512_implies_Equation10 (G : Type*) [Magma G] (h55 : Equation55 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h55 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h55 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h55 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h55 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation52_4512_implies_Equation10 (G : Type*) [Magma G] (h52 : Equation52 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h52 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h52 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h52 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation49_4512_implies_Equation10 (G : Type*) [Magma G] (h49 : Equation49 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h49 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation40_4297_implies_Equation3269 (G : Type*) [Magma G] (h40 : Equation40 G) (h4297 : Equation4297 G) : Equation3269 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4297 X0 X1 X0]
    conv => enter [1, 2]; rw [h40 X0 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h40 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation317_4369_4512_implies_Equation3273 (G : Type*) [Magma G] (h317 : Equation317 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) : Equation3273 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h317 X0 X1 X2]
    conv => enter [1]; rw [h4369 X3 X1 (X1 ◇ X2)]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h317 X3 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h4369 X2 X1 X0]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X3)]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l1 X3 X2 (X3 ◇ X2) X3]
    conv => enter [1]; rw [l2 X2 (X3 ◇ X2) X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x y x z]

theorem Equation317_4369_4512_implies_Equation3290 (G : Type*) [Magma G] (h317 : Equation317 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) : Equation3290 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h317 X3 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h4369 X2 X1 X0]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X0) = ((X3 ◇ X1) ◇ (X2 ◇ X1)) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [h4369 X1 X2 (X3 ◇ X1)]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X0) = (X3 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X1 (X2 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l2 x y z x]

theorem Equation317_4369_implies_Equation3275 (G : Type*) [Magma G] (h317 : Equation317 G) (h4369 : Equation4369 G) : Equation3275 G := by
  intro x y z
  conv => enter [1]; rw [h317 x y (z ◇ x)]
  conv => enter [1, 2]; rw [h4369 y z x]

theorem Equation40_3292_implies_Equation3273 (G : Type*) [Magma G] (h40 : Equation40 G) (h3292 : Equation3292 G) : Equation3273 G := by
  have l0 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h40 sK0 sK2]
    conv => enter [1]; rw [h3292 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

theorem Equation40_3265_implies_Equation3290 (G : Type*) [Magma G] (h40 : Equation40 G) (h3265 : Equation3265 G) : Equation3290 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h40 sK0 X0]
    conv => enter [1]; rw [h3265 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation40_3274_implies_Equation3290 (G : Type*) [Magma G] (h40 : Equation40 G) (h3274 : Equation3274 G) : Equation3290 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h40 sK0 sK2]
    conv => enter [1]; rw [h3274 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation40_3260_implies_Equation3273 (G : Type*) [Magma G] (h40 : Equation40 G) (h3260 : Equation3260 G) : Equation3273 G := by
  have l0 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h40 sK0 sK1]
    conv => enter [1]; rw [h3260 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

theorem Equation40_3264_implies_Equation3275 (G : Type*) [Magma G] (h40 : Equation40 G) (h3264 : Equation3264 G) : Equation3275 G := by
  have l0 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h40 sK0 sK1]
    conv => enter [1]; rw [h3264 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

theorem Equation40_3300_implies_Equation3277 (G : Type*) [Magma G] (h40 : Equation40 G) (h3300 : Equation3300 G) : Equation3277 G := by
  have l0 : ∀ sK1 X0 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 X1 sK3 sK0
    conv => enter [1]; rw [h40 sK1 sK0]
    conv => enter [1]; rw [h3300 sK0 X0 X1 sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y x z w]

theorem Equation40_3267_implies_Equation3277 (G : Type*) [Magma G] (h40 : Equation40 G) (h3267 : Equation3267 G) : Equation3277 G := by
  have l0 : ∀ sK1 X0 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 X1 sK3 sK0
    conv => enter [1]; rw [h40 sK1 X0]
    conv => enter [1]; rw [h3267 X0 X1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y x z w]

theorem Equation40_309_implies_Equation313 (G : Type*) [Magma G] (h40 : Equation40 G) (h309 : Equation309 G) : Equation313 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h40 sK0 sK1]
    conv => enter [1]; rw [h309 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation40_309_implies_Equation319 (G : Type*) [Magma G] (h40 : Equation40 G) (h309 : Equation309 G) : Equation319 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h40 sK0 sK1]
    conv => enter [1]; rw [h309 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation40_311_implies_Equation314 (G : Type*) [Magma G] (h40 : Equation40 G) (h311 : Equation311 G) : Equation314 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h40 sK0 X0]
    conv => enter [1]; rw [h311 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation43_3323_implies_Equation3350 (G : Type*) [Magma G] (h43 : Equation43 G) (h3323 : Equation3323 G) : Equation3350 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [h3323 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation43_3331_implies_Equation3364 (G : Type*) [Magma G] (h43 : Equation43 G) (h3331 : Equation3331 G) : Equation3364 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [h3331 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation38_39_implies_Equation41 (G : Type*) [Magma G] (h38 : Equation38 G) (h39 : Equation39 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation8_3334_implies_Equation419 (G : Type*) [Magma G] (h8 : Equation8 G) (h3334 : Equation3334 G) : Equation419 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [h3334 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation513_3306_implies_Equation16 (G : Type*) [Magma G] (h513 : Equation513 G) (h3306 : Equation3306 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3306 X1 X0]
    conv => enter [1]; rw [← h513 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation440_3319_implies_Equation11 (G : Type*) [Magma G] (h440 : Equation440 G) (h3319 : Equation3319 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3319 X1 X1]
    conv => enter [1]; rw [← h440 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation8_503_3306_4512_implies_Equation5 (G : Type*) [Magma G] (h8 : Equation8 G) (h503 : Equation503 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h503 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h8 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2]; rw [← h3306 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h8 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h503 X0 X1]
    conv => enter [1, 2]; rw [← h3306 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h503 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h503 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation430_3306_4512_implies_Equation4 (G : Type*) [Magma G] (h430 : Equation430 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h430 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h430 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3306 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h3306 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h430 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation8_474_3306_3319_4512_implies_Equation2 (G : Type*) [Magma G] (h8 : Equation8 G) (h474 : Equation474 G) (h3306 : Equation3306 G) (h3319 : Equation3319 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [h8 X0]
    conv => enter [1]; rw [← h474 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h474 X0 X1]
    conv => enter [1]; rw [← h474 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
    conv => enter [1]; rw [l0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h3306 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h3319 X0 X0]
    conv => enter [1]; rw [l7 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h474 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h3319 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l13 X1 X0]
    conv => enter [1]; rw [← h474 X1 X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation429_3319_3353_4512_implies_Equation16 (G : Type*) [Magma G] (h429 : Equation429 G) (h3319 : Equation3319 G) (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h3353 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h429 sK0 sK1]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3353 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h429 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3319 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h3353 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3353 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h429 ((sK1 ◇ sK0) ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0 (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h429 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l21 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l23 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK1 ◇ sK0) ◇ sK0) sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation429_3306_3315_4512_implies_Equation11 (G : Type*) [Magma G] (h429 : Equation429 G) (h3306 : Equation3306 G) (h3315 : Equation3315 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h429 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h3315 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h3306 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h3306 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h429 X1 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation429_3316_implies_Equation10 (G : Type*) [Magma G] (h429 : Equation429 G) (h3316 : Equation3316 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3316 X1 X0]
    conv => enter [1]; rw [← h429 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation75_323_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_56_323_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h56 : Equation56 G) (h323 : Equation323 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h323 X1 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation329_510_3334_implies_Equation5 (G : Type*) [Magma G] (h329 : Equation329 G) (h510 : Equation510 G) (h3334 : Equation3334 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h3334 X1 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h510 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h329 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation329_420_3312_implies_Equation4 (G : Type*) [Magma G] (h329 : Equation329 G) (h420 : Equation420 G) (h3312 : Equation3312 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h3312 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h420 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h329 X0 X1 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

end Semigroup4
