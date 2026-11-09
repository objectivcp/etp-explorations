import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

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

theorem Equation419_4512_implies_Equation436 (G : Type*) [Magma G] (h419 : Equation419 G) (h4512 : Equation4512 G) : Equation436 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h419 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h419 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l5 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h419 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation436_4512_implies_Equation419 (G : Type*) [Magma G] (h436 : Equation436 G) (h4512 : Equation4512 G) : Equation419 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h436 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l0 X2 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h436 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h436 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0 X0]
    conv => enter [1, 1]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK0 sK1]
  have l11 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h436 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation477_4512_implies_Equation511 (G : Type*) [Magma G] (h477 : Equation477 G) (h4512 : Equation4512 G) : Equation511 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h477 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l1 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h477 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h477 X0 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h477 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h477 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0)) X0]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l0 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l0 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l12 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK0 sK1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l8 sK1 sK0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← l11 (X0 ◇ X0) X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0 X1]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l16 X0 sK0 sK1]
    conv => enter [1]; rw [← l13 X0 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [← l20 X0 sK0 sK1]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l21 sK1 sK0 X0]
    conv => enter [1]; rw [l19 X0 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l22 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation511_4512_implies_Equation477 (G : Type*) [Magma G] (h511 : Equation511 G) (h4512 : Equation4512 G) : Equation477 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h511 sK1 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [h511 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h511 X0 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (X0 ◇ sK1)]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← l6 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 sK1 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h511 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [l9 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h511 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l14 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 (sK1 ◇ sK1) sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h511 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
    conv => enter [1, 2]; rw [← l24 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l26 sK1 sK0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [← l27 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [← l31 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l32 x y]

theorem Equation3342_4512_implies_Equation3355 (G : Type*) [Magma G] (h3342 : Equation3342 G) (h4512 : Equation4512 G) : Equation3355 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h3342 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h3342 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h3342 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h3342 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h3342 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h3342 X2 (X0 ◇ X1)]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h3342 X0 X1]
    conv => enter [1]; rw [l8 X2 X1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h3342 X0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3342 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) sK1 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h3342 X0 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l15 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l16 sK0 sK1 X0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h3342 X0 (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3342 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l22 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
    conv => enter [1]; rw [← h3342 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3342 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK0) sK0 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 sK1]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l27 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [l28 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [← l29 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l36 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l35 sK0 sK1 X0]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [← l30 sK0 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l40 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l39 sK0 sK1 X0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l32 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l44 sK0 sK1]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l45 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l46 sK0 sK1 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l22 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l49 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l50 sK1 sK0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1 (sK0 ◇ sK1)]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2]; rw [l54 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [← l61 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l7 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [← l64 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l36 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l33 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l69 x y]
  conv => enter [1]; rw [l68 y x]

theorem Equation3355_4512_implies_Equation3342 (G : Type*) [Magma G] (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3342 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3355 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [l2 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [l3 sK0]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [l6 sK0]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l8 sK0]
  have l10 : ∀ sK0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3355 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l9 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h3355 sK1 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ sK0) sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 (sK0 ◇ sK0)]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l19 sK0 (X0 ◇ X1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h3355 X0 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l22 sK0 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l27 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 (sK0 ◇ sK1)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK1)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h3355 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l31 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l36 x y]

theorem Equation4512_4949_implies_Equation5097 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4949 : Equation4949 G) : Equation5097 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4949 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4949 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4949 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK1 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_5097_implies_Equation4949 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5097 : Equation5097 G) : Equation4949 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l3 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l4 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l10 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l9 sK1]
  have l11 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h5097 sK1 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 sK1]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ sK1)))) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (X0 ◇ sK1)))]
    conv => enter [1]; rw [← h5097 X0 sK1]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [l14 sK1 X0]
  have l16 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))]
  have l17 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h5097 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [l15 sK1 X0]
  have l19 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← l1 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l20 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK1 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l22 : ∀ sK1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ sK1)]
  have l23 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1, 2]; rw [← l8 sK1]
  have l24 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l22 sK1]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l24 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5097 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2, 2]; rw [l25 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ sK1)]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK1 sK0]
    conv => enter [1]; rw [← l32 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l33 x y]

theorem Equation4512_41585_implies_Equation41619 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41585 : Equation41585 G) : Equation41619 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0]
    conv => enter [1, 1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l8 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41585 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41585 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41585 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h41585 X0 X1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41585 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41585 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l13 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l17 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l20 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l24 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l23 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l26 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l22 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1 X0]
    conv => enter [1, 1]; rw [← l25 sK1 sK0]
  have l29 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l5 sK0 sK1]
  have l32 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l26 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [l29 sK1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l34 sK1 sK0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l35 sK1 sK0]
    conv => enter [1]; rw [l32 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l38 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l32 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1 sK1]
    conv => enter [1]; rw [l47 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l50 sK0 sK1 sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l52 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l53 x y]

theorem Equation4512_41619_implies_Equation41585 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41619 : Equation41619 G) : Equation41585 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41619 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41619 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41619 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41619 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41619 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l7 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l16 sK1 sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l22 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ sK0) X0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l21 sK0 sK1]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0)]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l25 sK1 sK0]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l26 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ sK0) X0]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [l16 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK1) ◇ sK0)]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [l27 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41619 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK1 sK0]
  have l39 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) X0]
  have l40 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l39 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) X0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1, 2]; rw [← l40 sK1 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) sK0]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41619 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l36 sK1 sK0]
  have l48 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) X0]
  have l49 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l48 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) X0]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [← l40 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) sK0]
  have l53 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1, 2]; rw [l20 sK1 sK0 (sK1 ◇ sK1)]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l54 sK1 sK0]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l58 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0 X0]
  have l59 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l58 sK1 X0 sK0]
  have l60 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ sK0) X0]
  have l61 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l60 sK0 X0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l65 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l64 sK1 sK0]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK1]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1, 2]; rw [← l67 sK1 sK0]
  have l70 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l65 sK1 sK0]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l70 sK1 sK0]
    conv => enter [1, 2]; rw [← l69 sK0 sK1]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l71 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [← l61 sK0 (sK0 ◇ sK0) sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l73 sK1 sK0]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1, 2]; rw [l74 sK1 sK0]
  have l76 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [← l59 sK1 (sK0 ◇ sK0) sK0]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l76 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l77 x y]

theorem Equation4512_41883_implies_Equation41933 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41883 : Equation41883 G) : Equation41933 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41883 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41883 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41883 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h41883 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l12 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l6 sK1 sK0 X0]
    conv => enter [1]; rw [← h41883 X0 (sK1 ◇ sK0)]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h41883 X0 X2]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l18 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [l17 sK1 sK0 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l15 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 1]; rw [← l11 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l23 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l22 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l24 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
    conv => enter [1]; rw [l23 X0 sK0 sK1 X1]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l26 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l25 sK1 sK0 X0]
  have l27 : ∀ X1 X3 X0 X2 : G, (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X3 X0 X2
    conv => enter [1]; rw [l13 X1 X3 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [l13 X1 X0 X2]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l16 sK0 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 X0]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l30 sK0 sK1 X0]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l29 sK0 sK1 X0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l32 sK1 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l32 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h41883 X0 (sK1 ◇ sK0)]
  have l35 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41883 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [l35 sK0 sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [l35 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l13 (sK1 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l43 sK0 sK1 X0]
    conv => enter [1]; rw [l32 sK1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 (sK0 ◇ sK0)]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l46 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK0 sK1 ((sK0 ◇ sK0) ◇ X0)]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← l31 sK0 sK1 ((sK0 ◇ sK0) ◇ X0)]
  have l51 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK1 X0]
    conv => enter [1]; rw [l27 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0 X0]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1 X0]
    conv => enter [1]; rw [← l24 sK0 sK0 sK1 X0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [← l27 sK1 sK1 (sK0 ◇ sK1) sK1]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l33 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41883 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l53 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l18 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1, 2]; rw [l28 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1, 2, 2, 1]; rw [← l54 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l54 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1, 2]; rw [l13 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK0 (sK0 ◇ sK1)]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l54 sK0 sK1]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [← l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l67 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l68 y x]

theorem Equation4512_41933_implies_Equation41883 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41933 : Equation41933 G) : Equation41883 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l11 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l12 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l11 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l20 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l18 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l22 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l29 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l29 sK0 X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1 X0]
    conv => enter [1, 1]; rw [l24 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1) X0]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l22 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41933 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h41933 X0 (sK0 ◇ sK0)]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1]; rw [← h41933 X0 sK0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41933 X0 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))]
    conv => enter [1, 2]; rw [← h41933 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l38 sK0 X0]
    conv => enter [1, 2]; rw [l28 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l37 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ (sK0 ◇ X0))]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l36 sK0 X0]
  have l42 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l35 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l44 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41933 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l45 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41933 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h41933 sK1 sK0]
  have l47 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41933 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l40 sK0 X0]
  have l50 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [← l30 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l51 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l52 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l54 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← l42 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) sK0]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l26 sK0 X0]
    conv => enter [1]; rw [l49 sK0 X0]
  have l57 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l50 sK0]
    conv => enter [1, 2]; rw [l22 sK0]
  have l58 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l51 sK0]
  have l59 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l52 sK0]
  have l60 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l55 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0)]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [l56 sK0 X0]
  have l62 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l57 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l60 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l64 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l63 sK0 X0]
    conv => enter [1]; rw [l15 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l65 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l66 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41933 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l54 sK0]
  have l67 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l54 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l68 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l66 sK0]
    conv => enter [1]; rw [l15 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l69 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l68 sK0]
    conv => enter [1]; rw [← l64 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l70 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l69 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l71 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l70 sK0]
    conv => enter [1, 2]; rw [l22 sK0]
  have l72 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l71 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l73 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l72 sK0]
  have l74 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l65 sK0]
    conv => enter [1]; rw [l73 sK0]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l58 sK0]
    conv => enter [1]; rw [← l33 sK1 sK0]
  have l76 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l58 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l77 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l58 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l78 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l62 sK0]
    conv => enter [1]; rw [← l76 sK0]
  have l79 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l59 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l80 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l74 sK0]
    conv => enter [1]; rw [h41933 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l74 sK0]
  have l81 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l74 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l82 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l80 sK0]
    conv => enter [1]; rw [← l42 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) sK0]
  have l83 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l82 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l84 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l83 sK0]
    conv => enter [1]; rw [← l30 sK0 (sK0 ◇ sK0)]
  have l85 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l84 sK0]
    conv => enter [1]; rw [l61 sK0 (sK0 ◇ sK0)]
  have l86 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l85 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l87 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l79 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l88 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← l86 sK0]
  have l89 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l65 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l90 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l78 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41933 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [l53 sK0 sK1]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l93 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1]; rw [← l90 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ sK0)]
  have l95 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l90 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l94 sK0 sK1]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK0 sK1 sK0]
    conv => enter [1]; rw [l95 sK0 sK1]
  have l97 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l41 sK0 X0]
  have l98 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l41 sK0 X0]
  have l99 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l98 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l100 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l89 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l49 sK0 X0]
  have l101 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X1))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l99 sK0 X0 X1]
  have l102 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l100 sK0 X0]
  have l103 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l101 sK0 X0 X1]
  have l104 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41933 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [l97 sK0 X0]
  have l105 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l88 sK1 sK0]
    conv => enter [1]; rw [← l97 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l106 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l104 X0 sK0]
    conv => enter [1]; rw [← l42 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0)) sK0]
  have l107 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l106 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (X0 ◇ sK0) (sK0 ◇ sK0)]
  have l108 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l107 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (sK0 ◇ sK0)]
  have l109 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
    conv => enter [1]; rw [l67 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l4 sK0 sK1 X0]
  have l110 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l111 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41933 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l67 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))]
    conv => enter [1, 2]; rw [← h41933 X0 (sK0 ◇ sK0)]
  have l112 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l110 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK1)]
  have l113 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l109 sK0 sK1 X0]
    conv => enter [1]; rw [← l13 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l114 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l112 sK0 sK1]
    conv => enter [1]; rw [l97 sK0 (sK0 ◇ sK1)]
  have l115 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l113 sK0 sK1 X0]
    conv => enter [1]; rw [l103 sK0 (sK0 ◇ sK1) X0]
  have l116 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l114 sK0 sK1]
    conv => enter [1]; rw [l96 sK0 sK1]
  have l117 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l116 sK0 sK1]
  have l118 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l53 sK0 sK1]
    conv => enter [1]; rw [l117 sK0 sK1]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l118 sK1 sK0]
    conv => enter [1]; rw [← l115 sK0 sK1 (sK0 ◇ sK0)]
  have l120 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l105 sK1 sK0]
  have l121 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1 (sK0 ◇ sK0)]
  have l122 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l121 sK0 sK1]
    conv => enter [1]; rw [← l111 (sK0 ◇ sK1) sK0]
  have l123 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [l122 sK0 sK1]
  have l124 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l119 sK1 sK0]
    conv => enter [1]; rw [← l123 sK0 sK1]
  have l125 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41933 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l124 sK1 sK0]
  have l126 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l125 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l127 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l126 sK1 sK0]
    conv => enter [1]; rw [← l90 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l128 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l127 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ sK0)]
  have l129 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l128 sK1 sK0]
    conv => enter [1]; rw [← l90 sK0 (sK1 ◇ sK0)]
  have l130 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l129 sK1 sK0]
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
  have l131 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l102 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l130 sK1 sK0]
  have l132 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [← l131 sK0 sK1]
  have l133 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l87 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))]
    conv => enter [1, 2]; rw [← h41933 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l134 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l133 sK0 X0]
    conv => enter [1]; rw [← l108 X0 sK0]
  have l135 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l134 sK0 X0]
    conv => enter [1]; rw [l28 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l136 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l135 X0 sK0]
    conv => enter [1]; rw [← l77 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l137 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l136 X0 sK0]
    conv => enter [1]; rw [l28 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l138 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l77 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← l137 X0 sK0]
  have l139 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l103 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l138 sK0 X0]
  have l140 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l41 sK0 X0]
    conv => enter [1]; rw [l139 sK0 X0]
  have l141 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41933 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l140 X0 sK0]
  have l142 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41933 sK0 X0]
    conv => enter [1]; rw [← l141 sK0 X0]
  have l143 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l142 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l144 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l143 sK0 sK1]
    conv => enter [1]; rw [← l132 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l144 x y]

@[equational_result]
theorem Equation2_implies_Equation14 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation14 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation41 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation41 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation66 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation66 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation5 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation477 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation477 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation3345 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3345 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3370 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3370 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (z ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation11 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation16 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation16 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation38 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation38 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation39 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation39 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation314 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation504 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation504 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation3342 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3342 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation10 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation56 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation75 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation75 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3331 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3331 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3388 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3388 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ (z ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4274 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation311 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation311 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation318 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation327 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation327 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation329 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation329 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation343 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation343 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation419 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation429 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation440 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation513 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation513 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3323 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3323 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3334 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3334 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3414 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3414 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (z ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4271 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4271 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation4278 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3308 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3322 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3322 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3326 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3326 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3346 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3346 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation325 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation325 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation333 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4300 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4300 G := by
  intro x y z
  conv => enter [1, 1]; rw [h2 x z]

@[equational_result]
theorem Equation2_implies_Equation4339 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4339 G := by
  intro x y z
  conv => enter [1, 2, 2]; rw [h2 y z]

@[equational_result]
theorem Equation2_implies_Equation4360 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4360 G := by
  intro x y z w
  conv => enter [1, 2, 1]; rw [h2 y w]

@[equational_result]
theorem Equation2_implies_Equation3 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation3309 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3309 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation47 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3315 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3315 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3353 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation313 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3304 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3304 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation2_implies_Equation323 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation323 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation326 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation326 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation3267 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation2_implies_Equation3300 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3300 G := by
  intro x y z w
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (w ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation8 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3316 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3316 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation309 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation309 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation43 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation43 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation411 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation4301 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4301 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4331 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4331 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (z ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4305 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4305 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4325 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4325 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3273 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3273 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3290 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3290 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (x ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3306 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3306 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3319 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3319 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4286 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4286 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ y) (z ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4296 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4296 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4318 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (y ◇ x) (z ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation4327 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4327 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (z ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3260 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3260 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3265 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3265 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3274 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3274 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3292 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3292 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3301 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3301 G := by
  intro x y z w
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (w ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4364 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4364 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ z)) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3264 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3264 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4369 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4369 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ z)) (z ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation316 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation40 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation4279 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4279 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation310 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation310 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation315 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4273 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4299 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4299 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3259 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3259 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3271 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3271 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation4297 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4297 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4288 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4288 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ y) (z ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation4304 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4304 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3261 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3261 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4269 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4269 G := by
  intro x y
  conv => enter [1, 2, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation308 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation312 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3256 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3256 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3278 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3278 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3255 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3255 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3258 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3258 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4358 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4358 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (y ◇ z) (z ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation4362 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4362 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ z)) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4291 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4291 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4314 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4314 G := by
  intro x y
  conv => enter [1, 2, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4277 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4277 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4280 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4280 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4270 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4270 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation4275 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4283 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4283 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 (x ◇ y) (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4284 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4284 G := by
  intro x y
  conv => enter [1, 2, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4320 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4268 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4268 G := by
  intro x y
  conv => enter [1, 2, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4272 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4272 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation307 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation307 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4290 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4321 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4321 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3253 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4293 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4293 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4343 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4343 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (y ◇ y)) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4276 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation3_implies_Equation47 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation326 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation326 G := by
  intro x y
  conv => enter [1, 2]; rw [h3 y]

@[equational_result]
theorem Equation3_implies_Equation8 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation411 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation3319 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3319 G := by
  have l0 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3 sK1]
    conv => enter [1, 2]; rw [h3 sK1]
  intro x y
  conv => enter [1, 2]; rw [l0 y]

@[equational_result]
theorem Equation3_implies_Equation307 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation3253 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l1 x]

theorem Equation3_4512_implies_Equation323 (G : Type*) [Magma G] (h3 : Equation3 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_4512_implies_Equation3306 (G : Type*) [Magma G] (h3 : Equation3 G) (h4512 : Equation4512 G) : Equation3306 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4_implies_Equation11 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation38 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x y]

@[equational_result]
theorem Equation4_implies_Equation10 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation56 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3331 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3331 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ (y ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation311 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation327 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation327 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation329 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation329 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation419 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation429 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation440 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation3323 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3323 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3334 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3334 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation4271 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation3308 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3308 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3322 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3322 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3326 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4 sK0 sK1]
    conv => enter [1]; rw [h4 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4_implies_Equation325 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation325 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4339 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4339 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ y)]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation4360 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4360 G := by
  intro x y z w
  conv => enter [1]; rw [← h4 x (y ◇ z)]
  conv => enter [1]; rw [h4 x (w ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation3 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h4 x x]

@[equational_result]
theorem Equation4_implies_Equation3309 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3309 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3315 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3267 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation4_implies_Equation3316 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4 sK0 sK1]
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation309 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4286 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4286 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (z ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4318 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4318 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ x)]
  conv => enter [1]; rw [h4 x (z ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation3260 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3265 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3264 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation310 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation3259 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation4288 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4288 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (z ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation3261 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation4269 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation308 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation3256 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3255 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3258 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation4358 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4358 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ z)]
  conv => enter [1]; rw [h4 x (z ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4314 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4314 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (y ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4270 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4283 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4283 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4284 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4268 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation16 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation39 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation10 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation75 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation75 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2, 2]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation3388 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3388 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ y)) z]

@[equational_result]
theorem Equation5_implies_Equation318 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation318 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation329 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation329 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x z]

@[equational_result]
theorem Equation5_implies_Equation343 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation343 G := by
  intro x y z
  conv => enter [1]; rw [h5 (x ◇ y) z]

@[equational_result]
theorem Equation5_implies_Equation436 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation436 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation429 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation429 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation513 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation513 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h5 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation3334 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3334 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1, 2]; rw [h5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ y)) x]

@[equational_result]
theorem Equation5_implies_Equation3414 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3414 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation4278 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4278 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation5_implies_Equation3322 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3322 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y z]
  conv => enter [1]; rw [h5 (y ◇ (z ◇ y)) x]

@[equational_result]
theorem Equation5_implies_Equation3326 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation3346 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3346 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ y)) y]

@[equational_result]
theorem Equation5_implies_Equation333 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation4300 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4300 G := by
  intro x y z
  conv => enter [1, 2]; rw [← h5 y x]
  conv => enter [1]; rw [h5 (x ◇ y) z]

@[equational_result]
theorem Equation5_implies_Equation4360 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4360 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, sK3 = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [h5 sK3 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK3) sK1]
  have l1 : ∀ sK3 sK1 sK0 : G, sK3 = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h5 sK3 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK3) sK1]
  intro x y z w
  conv => enter [1]; rw [← l0 z x y]
  conv => enter [1]; rw [l1 z x w]

@[equational_result]
theorem Equation5_implies_Equation3 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h5 x x]

@[equational_result]
theorem Equation5_implies_Equation3309 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3309 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1, 2]; rw [h5 (y ◇ y) x]

@[equational_result]
theorem Equation5_implies_Equation3353 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3353 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1, 2]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation3300 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3300 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  intro x y z w
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3316 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation309 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation309 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation4296 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4296 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK1]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y z]

@[equational_result]
theorem Equation5_implies_Equation4327 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4327 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x z]

@[equational_result]
theorem Equation5_implies_Equation3274 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3274 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3292 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3292 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3264 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3264 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h5 (y ◇ (z ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation315 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation315 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation3271 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3271 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation4304 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4304 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y z]

@[equational_result]
theorem Equation5_implies_Equation3261 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (y ◇ (y ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation4269 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4269 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation312 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h5 (x ◇ x) y]

@[equational_result]
theorem Equation5_implies_Equation3278 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3278 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation3255 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3255 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2]; rw [h5 (y ◇ x) x]

@[equational_result]
theorem Equation5_implies_Equation3258 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3258 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (y ◇ (x ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation4362 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4362 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, sK2 = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 sK2 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  intro x y z
  conv => enter [1]; rw [← l0 z x y]
  conv => enter [1]; rw [l1 z y x]

@[equational_result]
theorem Equation5_implies_Equation4291 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4291 G := by
  intro x y
  conv => enter [1, 2]; rw [← h5 y x]
  conv => enter [1]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation4275 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4275 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4284 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4284 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4320 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4320 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4272 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4272 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation8_implies_Equation411 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 2]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation8_implies_Equation3319 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3319 G := by
  intro x y
  conv => enter [1, 2]; rw [h8 y]

@[equational_result]
theorem Equation8_implies_Equation3253 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h8 x]

theorem Equation8_4512_implies_Equation3306 (G : Type*) [Magma G] (h8 : Equation8 G) (h4512 : Equation4512 G) : Equation3306 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation10_implies_Equation429 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation429 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation10_implies_Equation3322 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation3322 G := by
  intro x y z
  conv => enter [1, 2]; rw [h10 y z]

@[equational_result]
theorem Equation10_implies_Equation8 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h10 x x]

@[equational_result]
theorem Equation10_implies_Equation3316 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation3316 G := by
  intro x y
  conv => enter [1, 2]; rw [h10 y x]

@[equational_result]
theorem Equation10_implies_Equation4269 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h10 x x]
  conv => enter [1]; rw [h10 x y]

@[equational_result]
theorem Equation10_implies_Equation3255 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation3255 G := by
  intro x y
  conv => enter [1, 2]; rw [h10 x y]

theorem Equation10_4512_implies_Equation3326 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation3326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK1) sK2]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [← l4 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation10_4512_implies_Equation3258 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation3258 G := by
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
  intro x y
  conv => enter [1]; rw [l2 x]
  conv => enter [1]; rw [l3 x y]

theorem Equation11_4512_implies_Equation419 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation419 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h11 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1]; rw [l7 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation11_implies_Equation440 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation440 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h11 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation11_implies_Equation3323 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation3323 G := by
  intro x y z
  conv => enter [1, 2]; rw [h11 y z]

@[equational_result]
theorem Equation11_implies_Equation3315 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation3315 G := by
  intro x y
  conv => enter [1, 2]; rw [h11 y x]

@[equational_result]
theorem Equation11_implies_Equation8 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h11 x x]

@[equational_result]
theorem Equation11_implies_Equation3256 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation3256 G := by
  intro x y
  conv => enter [1, 2]; rw [h11 x y]

@[equational_result]
theorem Equation11_implies_Equation4270 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h11 x x]
  conv => enter [1]; rw [h11 x y]

@[equational_result]
theorem Equation16_implies_Equation436 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation436 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK0]
    conv => enter [1, 2]; rw [h16 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation513 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation513 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation3414 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3414 G := by
  intro x y z
  conv => enter [1]; rw [h16 (x ◇ y) z]

@[equational_result]
theorem Equation16_implies_Equation3353 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h16 (x ◇ y) y]

@[equational_result]
theorem Equation16_implies_Equation8 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h16 x x]

@[equational_result]
theorem Equation16_implies_Equation3278 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3278 G := by
  intro x y
  conv => enter [1]; rw [h16 (x ◇ x) y]

@[equational_result]
theorem Equation16_implies_Equation4275 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h16 x x]
  conv => enter [1]; rw [h16 x y]

@[equational_result]
theorem Equation14_implies_Equation477 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation477 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1]; rw [← h14 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation14_4512_implies_Equation11 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h14 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation14_4512_implies_Equation16 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h14 sK1 sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h14 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation14_implies_Equation3331 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation3331 G := by
  intro x y z
  conv => enter [1, 2]; rw [h14 y z]

@[equational_result]
theorem Equation14_implies_Equation3308 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation3308 G := by
  intro x y
  conv => enter [1, 2]; rw [h14 y x]

@[equational_result]
theorem Equation14_implies_Equation4273 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [← h14 x x]
  conv => enter [1]; rw [h14 x y]

@[equational_result]
theorem Equation14_implies_Equation3259 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation3259 G := by
  intro x y
  conv => enter [1, 2]; rw [h14 x y]

theorem Equation14_4512_implies_Equation3388 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3388 G := by
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
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation14_4512_implies_Equation3346 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3346 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation14_4512_implies_Equation3271 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3271 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h14 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation16_implies_Equation3334 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3334 G := by
  intro x y z
  conv => enter [1, 2]; rw [h16 y z]

@[equational_result]
theorem Equation16_implies_Equation3261 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3261 G := by
  intro x y
  conv => enter [1, 2]; rw [h16 x y]

theorem Equation11_4512_implies_Equation3334 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK2 ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← l0 sK2 sK1]
  have l2 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK2 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK2 sK1]
  have l3 : ∀ sK2 sK1 : G, sK2 = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l4 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l5 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h11 sK0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l7 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 (sK1 ◇ X0) sK1]
    conv => enter [1, 2]; rw [l1 sK2 sK1 X0]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l0 sK2 sK1]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [l7 sK2 sK1 X0]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK2) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l8 sK2 sK1]
  have l11 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2 X0]
    conv => enter [1, 1]; rw [l10 sK0 sK2 sK1]
  have l12 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 sK1 sK2]
  have l15 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [h11 (sK2 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l9 sK2 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l15 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation11_4512_implies_Equation3261 (G : Type*) [Magma G] (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation3261 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h11 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h11 X2 (X0 ◇ X1)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  have l4 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l1 X0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l9 X0 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation38_implies_Equation3331 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3331 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation311 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ z)]

@[equational_result]
theorem Equation38_implies_Equation327 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation329 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation329 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3323 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3323 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation3334 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3334 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation4271 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ z)]

@[equational_result]
theorem Equation38_implies_Equation3308 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3308 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3322 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x y z y]

@[equational_result]
theorem Equation38_implies_Equation3326 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation325 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation4339 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation4360 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4360 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h38 sK1 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation38_implies_Equation3309 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3309 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3315 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation323 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation326 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation326 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y y]

@[equational_result]
theorem Equation38_implies_Equation3267 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation38_implies_Equation3316 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation309 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation3306 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3306 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation3319 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3319 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y y]

end Semigroup5
