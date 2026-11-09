import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53899_54014_implies_Equation4291 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53899 : Equation53899 G) (h54014 : Equation54014 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53899 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h53899 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X0 ◇ X1))]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l18 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l15 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l18 X2 X0 X1]
    conv => enter [1]; rw [← l12 X1 X2 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l19 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ X1)]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ X1)]
  have l24 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X1]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l24 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h53899 X1 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1]; rw [l21 X0 X1 (X1 ◇ X0)]
  have l28 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X0]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1, 2]; rw [← h54014 X1 X0]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l29 X1 X0]
    conv => enter [1]; rw [l21 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l30 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l32 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1]; rw [l21 X0 X0 (X1 ◇ X1)]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X0]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l14 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l38 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l43 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l11 sK0 sK1]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1) X0]
    conv => enter [1, 1]; rw [l11 sK0 sK1]
  have l45 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l46 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l47 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l45 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l46 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 (sK0 ◇ sK1)]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l21 (sK0 ◇ sK1) sK1 (sK0 ◇ sK1)]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l47 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← h54014 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l53 sK1 sK0]
  have l55 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ sK1) ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l10 sK0 sK1]
  have l56 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0) X0]
  have l57 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l56 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l58 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l59 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l57 sK0 sK1 X0]
  have l60 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l40 sK0 sK1]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l42 sK0 sK1 X0]
    conv => enter [1]; rw [l59 sK0 sK1 X0]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l60 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1))]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l21 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l61 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← h53899 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l69 sK0 sK1]
  have l71 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l73 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l74 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l7 sK1 sK0]
  have l75 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l74 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l76 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l73 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l72 sK0 sK1]
  have l78 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l75 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l76 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ sK1)]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [l21 (sK1 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ sK1)]
  have l82 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l81 sK0 sK1]
  have l83 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l82 sK1 sK0]
    conv => enter [1]; rw [← l78 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l83 sK1 sK0]
    conv => enter [1]; rw [← h53899 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [l71 sK1 sK0]
  have l86 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l87 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l88 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l37 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l37 sK0 sK1 (sK0 ◇ sK1)]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l90 sK0 sK1]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l89 sK0 sK1]
  have l93 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l93 sK0 sK1]
  have l95 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [l94 sK0 sK1]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l54 sK1 sK0]
  have l97 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l54 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l99 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l96 sK0 sK1]
  have l100 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1]; rw [l21 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l101 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l99 sK0 sK1]
    conv => enter [1]; rw [← h54014 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l102 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l100 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l103 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l101 sK0 sK1]
    conv => enter [1, 2]; rw [← l37 sK0 sK1 sK1]
  have l104 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l102 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l105 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l103 sK0 sK1]
  have l106 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l104 sK1 sK0]
  have l107 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l106 sK1 sK0]
  have l108 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [l107 sK1 sK0]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l110 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1]; rw [l109 sK0 sK1]
  have l111 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l40 sK0 sK1]
  have l112 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK1]
  have l113 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l114 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l113 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l115 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l112 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l116 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1]
    conv => enter [1]; rw [← l88 sK0 sK1 (sK0 ◇ sK1)]
  have l117 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l114 sK0 sK1 X0]
    conv => enter [1]; rw [← l88 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l118 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l115 sK0 sK1]
    conv => enter [1]; rw [← l88 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))]
  have l119 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l117 sK0 sK1 X0]
  have l120 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l42 sK0 sK1 (sK0 ◇ sK1)]
  have l121 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [l21 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l122 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l121 sK0 sK1]
  have l123 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l122 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l124 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l123 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1 (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l125 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l124 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l126 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l125 sK0 sK1]
    conv => enter [1]; rw [← l119 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l127 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l126 sK0 sK1]
    conv => enter [1]; rw [← l119 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l128 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l95 sK0 sK1]
    conv => enter [1]; rw [← l127 sK0 sK1]
  have l129 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l128 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l130 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l129 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l131 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l130 sK0 sK1 X0]
  have l132 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l133 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2]; rw [l35 sK0 sK1]
  have l134 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l133 sK1 sK0]
    conv => enter [1]; rw [← l87 sK0 sK1 sK0]
  have l135 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l110 sK0 sK1]
    conv => enter [1]; rw [← l134 sK1 sK0]
  have l136 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l129 sK0 sK1]
    conv => enter [1]; rw [l135 sK0 sK1]
  have l137 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l132 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l138 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l132 sK0 sK1]
  have l139 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l138 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l140 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l137 sK0 sK1]
  have l141 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l140 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l142 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l105 sK1 sK0]
  have l143 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) X0]
  have l144 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l143 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l145 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l142 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l146 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l144 sK1 sK0 X0]
  have l147 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l145 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l85 sK1 sK0]
  have l148 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l146 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l147 sK0 sK1]
  have l149 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l148 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l150 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l149 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ sK1)]
  have l151 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l150 sK1 sK0]
    conv => enter [1]; rw [l21 (sK0 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ sK1)]
  have l152 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l151 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l153 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l37 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l152 sK1 sK0]
  have l154 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l108 sK1 sK0]
    conv => enter [1]; rw [← l153 sK1 sK0]
  have l155 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l154 sK1 sK0]
    conv => enter [1, 2]; rw [← l137 sK0 sK1]
  have l156 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l155 sK1 sK0]
    conv => enter [1]; rw [← l136 sK0 sK1]
  have l157 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1, 2]; rw [l156 sK1 sK0]
  have l158 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l157 sK0 sK1]
    conv => enter [1]; rw [← l131 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l159 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l158 sK0 sK1]
    conv => enter [1, 2]; rw [l40 sK0 sK1]
  have l160 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l159 sK0 sK1]
    conv => enter [1, 2]; rw [← l137 sK0 sK1]
  have l161 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54014 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l162 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54014 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l132 sK0 sK1]
  have l163 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l164 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l165 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l37 sK0 sK1 sK0]
  have l166 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h54014 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l167 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53899 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h54014 X0 X1]
  have l168 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54014 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
  have l169 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 sK0 X0]
  have l170 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 (sK0 ◇ sK1) X0]
  have l171 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l170 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1))]
  have l172 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l169 sK0 sK1 X0]
    conv => enter [1]; rw [← l37 sK0 sK1 (X0 ◇ sK0)]
  have l173 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l168 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l174 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l167 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l175 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l166 sK1 sK0]
  have l176 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l165 sK1 sK0]
    conv => enter [1]; rw [l86 sK1 sK0]
  have l177 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l164 sK1 sK0]
    conv => enter [1, 2]; rw [← l37 sK0 sK1 sK1]
  have l178 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l163 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l179 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l161 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h53899 X1 X0]
  have l180 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l171 sK0 sK1 X0]
    conv => enter [1]; rw [l141 sK0 sK1 (X0 ◇ X0)]
  have l181 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l172 sK0 sK1 X0]
    conv => enter [1]; rw [← l131 sK0 sK1 (X0 ◇ X0)]
  have l182 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l173 X0 X1 X2]
    conv => enter [1]; rw [l21 X0 X1 (X2 ◇ X2)]
  have l183 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l174 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X0))]
  have l184 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l175 sK0 sK1]
    conv => enter [1]; rw [← l88 sK0 sK1 (sK0 ◇ sK1)]
  have l185 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l176 sK1 sK0]
    conv => enter [1]; rw [← l136 sK0 sK1]
  have l186 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l177 sK1 sK0]
  have l187 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l178 sK0 sK1]
  have l188 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l179 X2 X0 X1]
  have l189 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l180 sK0 sK1 X0]
    conv => enter [1]; rw [← l181 sK0 sK1 X0]
  have l190 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l182 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X2 X0]
  have l191 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l183 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h53899 X0 X1]
  have l192 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l116 sK0 sK1]
    conv => enter [1]; rw [← l184 sK0 sK1]
  have l193 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l185 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l194 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l156 sK1 sK0]
    conv => enter [1]; rw [l186 sK1 sK0]
  have l195 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l190 X0 X1 X2]
    conv => enter [1]; rw [← l188 X1 X0 X2]
  have l196 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0 X0]
    conv => enter [1]; rw [← l191 X0 X1]
  have l197 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l192 sK0 sK1]
    conv => enter [1]; rw [l141 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l198 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l187 sK0 sK1]
    conv => enter [1]; rw [← l194 sK0 sK1]
  have l199 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l195 X0 X1 X2]
  have l200 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l196 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
  have l201 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l197 sK0 sK1]
    conv => enter [1, 2]; rw [← l193 sK0 sK1]
  have l202 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l198 sK1 sK0]
  have l203 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l200 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
  have l204 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l160 sK0 sK1]
    conv => enter [1]; rw [← l201 sK0 sK1]
  have l205 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l202 sK1 sK0]
  have l206 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l203 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l207 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l206 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X0]
  have l208 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l207 X1 X0]
    conv => enter [1, 2]; rw [← l12 X0 X1 X1]
  have l209 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l208 X1 X0]
    conv => enter [1, 2]; rw [← h54014 X0 X1]
  have l210 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l205 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l211 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l187 sK0 sK1]
    conv => enter [1]; rw [← l105 sK1 sK0]
  have l212 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l187 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l213 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [l212 sK0 sK1 X0]
  have l214 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l211 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l215 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l214 sK1 sK0]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l216 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l215 sK1 sK0]
    conv => enter [1]; rw [← l137 sK0 sK1]
  have l217 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l205 sK0 sK1]
    conv => enter [1]; rw [← l216 sK1 sK0]
  have l218 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l204 sK0 sK1]
    conv => enter [1]; rw [← l137 sK0 sK1]
  have l219 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l205 sK0 sK1]
    conv => enter [1]; rw [← l218 sK0 sK1]
  have l220 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l219 sK0 sK1]
  have l221 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l217 sK0 sK1]
    conv => enter [1]; rw [l220 sK1 sK0]
  have l222 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l221 sK0 sK1]
  have l223 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l205 sK0 sK1]
    conv => enter [1]; rw [← l222 sK0 sK1]
  have l224 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l223 sK0 sK1]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l225 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l223 sK0 sK1]
    conv => enter [1]; rw [l224 sK0 sK1]
  have l226 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l187 sK0 sK1]
    conv => enter [1]; rw [l210 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l187 sK0 sK1]
  have l227 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [← l210 sK0 sK1 X0]
  have l228 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [← l227 sK0 sK1 X0]
  have l229 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l226 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l230 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l228 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK0)]
  have l231 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l225 sK0 sK1]
    conv => enter [1]; rw [← l229 sK0 sK1]
  have l232 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l230 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l233 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l21 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [← l232 sK0 sK1 X0]
  have l234 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l210 sK0 sK1 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))]
    conv => enter [1]; rw [← l233 X0 sK0 sK1]
  have l235 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l162 X0 sK0 sK1]
    conv => enter [1]; rw [← l234 sK0 sK1 X0]
  have l236 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l235 X0 sK0 sK1]
    conv => enter [1]; rw [← h53899 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l237 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l231 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l238 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l231 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l239 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l223 sK0 sK1]
    conv => enter [1]; rw [l237 sK0 sK1]
  have l240 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l239 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l241 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l238 sK0 sK1 sK1]
    conv => enter [1]; rw [← l187 sK0 sK1]
  have l242 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l238 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l243 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l242 sK0 sK1 X0]
    conv => enter [1]; rw [← l213 sK0 sK1 X0]
  have l244 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l231 sK0 sK1]
    conv => enter [1]; rw [← l241 sK0 sK1]
  have l245 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l238 sK0 sK1 X0]
    conv => enter [1]; rw [← l243 sK0 sK1 X0]
  have l246 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l245 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l247 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54014 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l244 sK0 sK1]
  have l248 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l209 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l210 sK0 sK1 X0]
  have l249 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l209 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 X0]
  have l250 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h54014 X1 X0]
    conv => enter [1]; rw [l209 X1 X0]
  have l251 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l249 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) X0 (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l252 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l248 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))]
  have l253 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l251 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) X0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l254 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l252 sK0 sK1 X0]
    conv => enter [1]; rw [l199 (sK0 ◇ (sK0 ◇ sK1)) X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l255 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l253 sK0 sK1 X0]
    conv => enter [1]; rw [l21 (sK1 ◇ (sK0 ◇ sK1)) X0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l256 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l254 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X0]
  have l257 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l255 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) (sK1 ◇ (sK0 ◇ sK1))]
  have l258 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l256 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h54014 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l259 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l257 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK1) X0 (sK1 ◇ (sK0 ◇ sK1))]
  have l260 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l258 sK0 sK1 X0]
  have l261 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l259 sK0 sK1 X0]
    conv => enter [1]; rw [← l188 X0 (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l262 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l260 sK0 sK1 X0]
    conv => enter [1]; rw [← h54014 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l263 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l261 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ X0)]
  have l264 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l262 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l265 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l263 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l87 sK0 sK1 X0]
  have l266 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l264 sK0 sK1 X0]
    conv => enter [1]; rw [← l210 sK0 sK1 (X0 ◇ sK0)]
  have l267 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l265 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l213 sK0 sK1 X0]
  have l268 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l139 sK0 sK1 X0]
    conv => enter [1]; rw [l266 sK0 sK1 X0]
  have l269 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l267 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l238 sK0 sK1 X0]
  have l270 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l210 sK0 sK1 X0]
    conv => enter [1]; rw [l268 sK0 sK1 X0]
  have l271 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l250 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l269 sK0 sK1 X0]
  have l272 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l271 sK0 sK1 X0]
    conv => enter [1]; rw [← h54014 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l273 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l272 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l274 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l273 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ sK0)]
  have l275 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l246 sK0 sK1 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l274 sK0 sK1 X0]
  have l276 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l189 sK0 sK1 X0]
    conv => enter [1]; rw [l275 sK0 sK1 X0]
  have l277 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((X0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53899 (X0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l270 sK0 sK1 X0]
  have l278 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l277 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l279 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l278 X0 sK0 sK1]
    conv => enter [1]; rw [l199 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l280 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l279 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l131 sK0 sK1 X0]
  have l281 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l210 sK0 sK1 X0]
    conv => enter [1]; rw [← l280 X0 sK0 sK1]
  have l282 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK0 ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l281 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 sK0 ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l283 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l282 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l284 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l283 X0 sK0 sK1]
    conv => enter [1]; rw [l21 X0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l285 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l284 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l210 sK0 sK1 X0]
  have l286 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l210 sK0 sK1 X0]
    conv => enter [1]; rw [← l285 X0 sK0 sK1]
  have l287 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l209 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l240 sK0 sK1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l288 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l287 X0 sK0 sK1]
    conv => enter [1]; rw [← l276 sK0 sK1 X0]
  have l289 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54014 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l288 X0 sK0 sK1]
  have l290 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l286 sK0 sK1 X0]
    conv => enter [1]; rw [l289 X0 sK0 sK1]
  have l291 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l209 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l246 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l292 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l290 sK0 sK1 X0]
    conv => enter [1]; rw [← l291 X0 sK0 sK1]
  have l293 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l292 sK0 sK1 X0]
    conv => enter [1]; rw [← h54014 X0 (sK0 ◇ sK1)]
  have l294 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1]; rw [l21 sK1 sK0 X0]
  have l295 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1]; rw [l294 sK1 sK0 X0]
  have l296 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [l295 sK1 sK0 X0]
  have l297 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l296 sK0 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 sK0 sK1]
  have l298 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l250 sK1 sK0]
    conv => enter [1]; rw [← l297 sK0 sK1]
  have l299 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l298 sK1 sK0]
    conv => enter [1]; rw [l236 sK0 sK0 sK1]
  have l300 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l299 sK1 sK0]
    conv => enter [1]; rw [← l247 sK0 sK0 sK1]
  have l301 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l300 sK1 sK0]
    conv => enter [1]; rw [← l293 sK0 sK1 sK0]
  have l302 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l301 sK1 sK0]
    conv => enter [1]; rw [l129 sK0 sK1]
  have l303 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l302 sK1 sK0]
    conv => enter [1]; rw [← l205 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l303 y x]

theorem Equation4512_53899_54014_implies_Equation54060 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53899 : Equation53899 G) (h54014 : Equation54014 G) : Equation54060 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l13 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l17 X2 X0 X1]
    conv => enter [1]; rw [← l11 X1 X2 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l26 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l18 (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ sK1)]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l32 sK0 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l36 sK0 sK1]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l41 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l14 sK1 sK0]
  have l42 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l43 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l42 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l46 sK0 sK1]
  have l49 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l53 sK0 sK1]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l56 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK1)]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 sK1]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1]; rw [← l59 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK0)]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l55 sK0 sK1]
  have l64 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK0) X0]
  have l65 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l64 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
  have l66 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l67 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0 sK0]
    conv => enter [1]; rw [← l62 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l66 sK1 sK0]
  have l69 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l67 sK1 sK0]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 sK0 (sK0 ◇ sK1)]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l77 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 (sK0 ◇ sK1) X0]
  have l78 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l77 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1))]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l81 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l78 sK0 sK1 X0]
    conv => enter [1]; rw [← l47 sK0 sK1 (X0 ◇ X0)]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l80 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l82 sK0 sK1]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l83 sK0 sK1]
  have l86 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [← l83 sK0 sK1]
  have l87 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [← l86 sK0 sK1 X0]
  have l88 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l88 sK1 sK0]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l89 sK0 sK1]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l90 sK0 sK1]
  have l92 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1, 2]; rw [l84 sK0 sK1]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l84 sK0 sK1]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l84 sK0 sK1]
  have l95 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [l84 sK0 sK1]
  have l96 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l95 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l97 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l92 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [l96 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l99 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l97 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l100 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1]
    conv => enter [1]; rw [← h53899 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l99 sK0 sK1]
  have l102 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l100 sK0 sK1]
    conv => enter [1]; rw [l38 sK0 sK1 sK0]
  have l103 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [l96 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l104 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l102 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1 sK0]
  have l105 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l103 sK0 sK1]
    conv => enter [1, 2]; rw [l32 sK0 sK1]
  have l106 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l104 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1 sK0]
  have l107 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l105 sK0 sK1]
    conv => enter [1, 2]; rw [l36 sK0 sK1]
  have l108 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l107 sK0 sK1]
    conv => enter [1, 2]; rw [← l46 sK0 sK1]
  have l109 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2, 2]; rw [← l91 sK0 sK1]
  have l110 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l111 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l110 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l112 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l109 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l113 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l112 sK1 sK0]
  have l114 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l115 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l114 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l116 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l115 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l117 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l116 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1 (sK1 ◇ sK1)]
  have l118 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l117 sK0 sK1]
    conv => enter [1]; rw [← l47 sK0 sK1 (sK1 ◇ sK1)]
  have l119 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [← l81 sK0 sK1 sK1]
  have l120 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l119 sK0 sK1]
  have l121 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l122 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l121 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l123 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l122 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l124 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l125 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l124 sK1 sK0]
  have l126 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l123 sK0 sK1]
  have l127 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l123 sK0 sK1]
  have l128 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l127 sK0 sK1]
    conv => enter [1]; rw [← l108 sK0 sK1]
  have l129 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [← l126 sK0 sK1]
  have l130 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l128 sK0 sK1]
  have l131 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l129 sK0 sK1]
    conv => enter [1, 2]; rw [l69 sK1 sK0]
  have l132 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l131 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l133 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← h53899 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l134 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l135 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l38 sK0 sK1 sK0]
    conv => enter [1]; rw [← l133 sK0 sK1]
  have l136 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l134 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l135 sK0 sK1]
  have l137 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l136 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1 sK0]
  have l138 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l137 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1 sK0]
  have l139 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l138 sK0 sK1]
    conv => enter [1]; rw [← l106 sK0 sK1]
  have l140 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← l139 sK0 sK1]
  have l141 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l140 sK0 sK1]
    conv => enter [1]; rw [l74 sK0 sK1]
  have l142 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l141 sK0 sK1]
  have l143 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l141 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l144 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l143 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l142 sK1 sK0]
  have l145 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l144 sK0 sK1]
  have l146 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l140 sK0 sK1]
    conv => enter [1]; rw [← l145 sK0 sK1]
  have l147 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l146 sK0 sK1]
  have l148 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l146 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l149 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l147 sK1 sK0]
  have l150 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l132 sK0 sK1]
    conv => enter [1]; rw [l125 sK0 sK1]
  have l151 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l149 sK0 sK1]
    conv => enter [1]; rw [← l150 sK0 sK1]
  have l152 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l18 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ X0))]
  have l153 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l148 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l152 sK1 X0 sK0]
  have l154 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l143 sK0 sK1 X0]
    conv => enter [1]; rw [l153 sK0 sK1 X0]
  have l155 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l151 sK0 sK1]
    conv => enter [1]; rw [l154 sK0 sK1 X0]
  have l156 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 sK0]
    conv => enter [1]; rw [← l155 sK0 sK1 sK0]
  have l157 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l156 sK1 sK0]
    conv => enter [1]; rw [l84 sK0 sK1]
  have l158 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l157 sK1 sK0]
    conv => enter [1]; rw [← l130 sK0 sK1]
  have l159 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l158 sK1 sK0]
    conv => enter [1]; rw [← l151 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l159 x y]
  conv => enter [1]; rw [l151 y x]

theorem Equation4512_53899_54014_implies_Equation54057 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53899 : Equation53899 G) (h54014 : Equation54014 G) : Equation54057 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l6 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l18 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l16 sK1 sK0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l20 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l17 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l21 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l25 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l7 sK1 sK0]
  have l26 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l26 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l29 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l10 sK1 sK0]
  have l30 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l29 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l30 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l14 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [l9 sK0 sK1 X0]
  have l33 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2, 2]; rw [← l17 sK1 sK0]
  have l35 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h53899 (sK0 ◇ sK1) sK1]
  have l40 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l15 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l19 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l16 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l50 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l40 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l53 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l35 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l55 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53899 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l14 sK0 sK1 sK1]
  have l57 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53899 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← h53899 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l43 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l63 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l53 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l65 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l67 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l58 sK1 sK0]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l61 sK0 sK1]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l72 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l63 X2 X0 X1]
    conv => enter [1]; rw [← l50 X1 X2 X0]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l74 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l74 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l79 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l75 sK1 sK0]
  have l80 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l76 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l82 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) sK1]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l80 sK1 sK0]
  have l84 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [l72 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l85 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l82 sK1 sK0]
    conv => enter [1]; rw [l72 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) sK1]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1, 2]; rw [l19 sK1 sK0 sK0]
  have l88 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l90 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l88 sK1 sK0]
    conv => enter [1, 2]; rw [l19 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1, 2]; rw [l42 sK0 sK1]
  have l92 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l91 sK0 sK1]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l92 sK1 sK0]
  have l95 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l93 sK0 sK1]
    conv => enter [1, 2]; rw [l79 sK1 sK0]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1, 2]; rw [l79 sK1 sK0]
  have l97 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l96 sK0 sK1]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l57 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l99 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l57 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l100 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l99 sK1 X0]
  have l101 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l98 sK0 sK1]
  have l102 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l101 sK0 sK1]
  have l103 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l79 sK1 sK0]
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l79 sK1 sK0]
  have l104 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l79 sK1 sK0]
  have l105 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l104 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l106 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l97 sK0 sK1]
    conv => enter [1]; rw [l103 sK1 sK0]
    conv => enter [1, 2]; rw [← l97 sK0 sK1]
  have l107 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [← l52 sK0 sK1]
  have l108 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l107 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l109 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
  have l110 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l36 sK0 sK1]
  have l111 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) X0]
  have l112 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l111 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l113 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l110 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l114 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l112 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l113 sK0 sK1]
  have l115 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l114 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l116 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l115 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK1 ◇ sK1)]
  have l117 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l116 sK0 sK1]
    conv => enter [1]; rw [l72 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK1 ◇ sK1)]
  have l118 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l117 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l119 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l120 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l70 sK0 sK1]
  have l121 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l70 sK0 sK1]
  have l122 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK0 X0]
  have l123 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l122 sK0 sK1 X0]
  have l124 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1]; rw [l121 sK0 sK1]
  have l125 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l123 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l124 sK0 sK1]
  have l126 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l125 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l127 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l126 sK0 sK1]
    conv => enter [1]; rw [← h53899 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l128 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l127 sK0 sK1]
    conv => enter [1]; rw [l105 sK1 sK0 sK0]
  have l129 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l102 sK0 sK1]
  have l130 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l102 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l131 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l130 sK0 sK1 X0]
  have l132 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l129 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l133 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l134 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l135 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l134 sK1 sK0 X0]
  have l136 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l133 sK0 sK1]
  have l137 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l136 sK0 sK1]
  have l138 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l119 sK0 sK1]
  have l139 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l138 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l140 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l132 sK0 sK1]
  have l141 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l132 sK0 sK1]
  have l142 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l141 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l143 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l140 sK1 sK0]
    conv => enter [1]; rw [← l100 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l144 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l143 sK0 sK1]
    conv => enter [1]; rw [l142 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l145 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l144 sK1 sK0]
    conv => enter [1]; rw [← h53899 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l146 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l145 sK1 sK0]
  have l147 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l137 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l148 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l147 sK0 sK1 X0]
  have l149 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [l42 sK0 sK1]
  have l150 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l42 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) X0]
  have l151 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l150 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l152 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l149 sK0 sK1]
    conv => enter [1, 2]; rw [l119 sK0 sK1]
  have l153 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l151 sK0 sK1 X0]
    conv => enter [1]; rw [← l135 sK1 sK0 (sK0 ◇ X0)]
  have l154 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l152 sK0 sK1]
    conv => enter [1, 2]; rw [← l137 sK0 sK1]
  have l155 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l153 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l108 sK1 sK0 X0]
  have l156 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l154 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1)]
  have l157 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l155 sK0 sK1 X0]
  have l158 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l148 sK0 sK1 sK0]
    conv => enter [1]; rw [l156 sK0 sK1]
  have l159 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l139 sK0 sK1 X0]
    conv => enter [1]; rw [l157 sK0 sK1 X0]
  have l160 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l148 sK0 sK1 X0]
    conv => enter [1]; rw [l159 sK0 sK1 X0]
  have l161 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l41 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 ((sK1 ◇ sK1) ◇ sK0)]
  have l162 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l161 sK0 sK1]
  have l163 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l162 sK0 sK1]
  have l164 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l163 sK0 sK1]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l165 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l164 sK0 sK1]
  have l166 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)]
    conv => enter [1, 2]; rw [← l37 sK0 sK1]
  have l167 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l139 sK0 sK1 sK0]
    conv => enter [1]; rw [l166 sK0 sK1]
  have l168 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l148 sK0 sK1 sK0]
    conv => enter [1]; rw [l167 sK0 sK1]
  have l169 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l158 sK0 sK1]
    conv => enter [1]; rw [l168 sK0 sK1]
  have l170 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l106 sK0 sK1]
    conv => enter [1]; rw [← h53899 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l171 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l106 sK0 sK1]
  have l172 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l106 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l173 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l172 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l174 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l171 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l175 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l170 sK0 sK1]
    conv => enter [1]; rw [l105 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l176 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l173 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l174 sK0 sK1]
  have l177 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l175 sK0 sK1]
  have l178 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l176 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l179 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l135 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l177 sK0 sK1]
  have l180 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l178 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l181 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l179 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l182 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l180 sK0 sK1]
    conv => enter [1]; rw [l72 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l183 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l181 sK1 sK0]
    conv => enter [1, 2]; rw [l79 sK1 sK0]
  have l184 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [l105 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l185 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l183 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l186 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l184 sK0 sK1]
  have l187 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l185 sK0 sK1]
    conv => enter [1]; rw [l186 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l185 sK0 sK1]
  have l188 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l135 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l187 sK1 sK0]
  have l189 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1]; rw [← l188 sK0 sK1]
  have l190 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l189 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l191 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l190 sK0 sK1]
    conv => enter [1, 2]; rw [l79 sK1 sK0]
  have l192 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l185 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l193 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l185 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l194 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l193 sK0 sK1 X0]
  have l195 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l191 sK0 sK1]
    conv => enter [1]; rw [← l192 sK0 sK1]
  have l196 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [l71 sK1 sK0]
  have l197 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l196 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l198 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l197 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l199 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l198 sK0 sK1]
    conv => enter [1]; rw [l105 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l200 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l199 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l201 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l200 sK0 sK1]
    conv => enter [1, 2]; rw [l105 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l202 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l201 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l68 sK1 sK0]
  have l203 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l202 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l204 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l203 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l205 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ sK1)]
    conv => enter [1]; rw [l204 sK0 sK1]
  have l206 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l205 sK0 sK1]
  have l207 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l72 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l206 sK0 sK1]
  have l208 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l207 sK0 sK1]
  have l209 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l19 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l208 sK0 sK1]
  have l210 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l209 sK0 sK1]
  have l211 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [l210 sK0 sK1]
  have l212 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l211 sK0 sK1]
  have l213 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l212 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l214 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l213 sK0 sK1 X0]
  have l215 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l42 sK0 sK1]
    conv => enter [1]; rw [l109 sK0 sK1]
  have l216 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l109 sK0 sK1]
  have l217 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l216 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l218 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l217 sK0 sK1]
    conv => enter [1]; rw [← l135 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l219 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l218 sK0 sK1]
    conv => enter [1, 2]; rw [l108 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l220 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l219 sK0 sK1]
    conv => enter [1]; rw [← l160 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l221 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l220 sK0 sK1]
  have l222 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l221 sK0 sK1]
  have l223 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l72 (sK0 ◇ (sK1 ◇ sK1)) sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l222 sK0 sK1]
  have l224 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l223 sK0 sK1]
  have l225 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [l224 sK0 sK1]
  have l226 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l215 sK0 sK1]
    conv => enter [1]; rw [l119 sK0 sK1]
  have l227 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l137 sK0 sK1]
    conv => enter [1]; rw [← l226 sK0 sK1]
  have l228 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l226 sK0 sK1]
  have l229 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l228 sK0 sK1]
    conv => enter [1]; rw [← l148 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l230 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l225 sK0 sK1]
    conv => enter [1]; rw [← l229 sK0 sK1]
  have l231 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l230 sK0 sK1]
    conv => enter [1]; rw [← l135 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l232 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l71 sK1 sK0]
    conv => enter [1, 2]; rw [l227 sK0 sK1]
  have l233 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l24 sK1 sK0]
    conv => enter [1, 2]; rw [l227 sK0 sK1]
  have l234 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 sK0 sK1]
    conv => enter [1, 2]; rw [l227 sK0 sK1]
  have l235 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l227 sK0 sK1]
  have l236 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l227 sK0 sK1]
  have l237 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l236 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l238 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l225 sK0 sK1]
    conv => enter [1]; rw [← l235 sK0 sK1]
  have l239 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l79 sK1 sK0]
    conv => enter [1]; rw [l234 sK0 sK1]
  have l240 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l233 sK1 sK0]
    conv => enter [1]; rw [← l123 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l241 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l238 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l242 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l95 sK1 sK0]
    conv => enter [1]; rw [l239 sK0 sK1]
  have l243 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l79 sK1 sK0]
    conv => enter [1]; rw [l240 sK1 sK0]
  have l244 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l241 sK0 sK1]
    conv => enter [1, 2]; rw [← l185 sK0 sK1]
  have l245 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l119 sK0 sK1]
    conv => enter [1]; rw [l242 sK1 sK0]
  have l246 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l243 sK1 sK0]
  have l247 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l244 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l248 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l137 sK0 sK1]
    conv => enter [1]; rw [l245 sK1 sK0]
  have l249 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l185 sK0 sK1]
    conv => enter [1]; rw [l246 sK1 sK0]
  have l250 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l212 sK0 sK1]
    conv => enter [1]; rw [← l247 sK0 sK1]
  have l251 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l248 sK1 sK0]
  have l252 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l79 sK1 sK0]
    conv => enter [1]; rw [l251 sK1 sK0]
  have l253 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1, 2]; rw [← l250 sK0 sK1]
  have l254 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l250 sK0 sK1]
  have l255 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l254 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l256 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l135 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l253 sK0 sK1]
  have l257 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l255 sK0 sK1]
    conv => enter [1]; rw [l139 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l258 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l256 sK1 sK0]
    conv => enter [1, 2]; rw [l79 sK1 sK0]
  have l259 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l148 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l257 sK0 sK1]
  have l260 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l258 sK0 sK1]
  have l261 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l259 sK0 sK1]
    conv => enter [1]; rw [← l169 sK0 sK1]
  have l262 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l261 sK0 sK1]
    conv => enter [1]; rw [l237 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l263 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l262 sK0 sK1]
    conv => enter [1, 2]; rw [← l212 sK0 sK1]
  have l264 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l263 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l265 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l212 sK0 sK1]
    conv => enter [1]; rw [← l264 sK0 sK1]
  have l266 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l185 sK0 sK1]
    conv => enter [1]; rw [l260 sK1 sK0]
  have l267 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l260 sK1 sK0]
  have l268 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l260 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l269 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l194 sK0 sK1 X0]
    conv => enter [1]; rw [← l268 sK0 sK1 X0]
  have l270 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l252 sK0 sK1]
    conv => enter [1]; rw [← l267 sK0 sK1]
  have l271 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l269 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l272 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l270 sK0 sK1]
    conv => enter [1]; rw [← l191 sK0 sK1]
  have l273 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l272 sK0 sK1]
    conv => enter [1]; rw [l266 sK0 sK1]
  have l274 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l265 sK0 sK1]
  have l275 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l195 sK0 sK1]
    conv => enter [1]; rw [← l274 sK0 sK1]
  have l276 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l275 sK0 sK1]
  have l277 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l148 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l276 sK0 sK1]
  have l278 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l277 sK0 sK1]
    conv => enter [1]; rw [← l249 sK0 sK1]
  have l279 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l278 sK0 sK1]
    conv => enter [1]; rw [l266 sK0 sK1]
  have l280 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l279 sK0 sK1]
    conv => enter [1]; rw [l237 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l281 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l280 sK0 sK1]
    conv => enter [1, 2]; rw [← l212 sK0 sK1]
  have l282 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l281 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l283 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l266 sK0 sK1]
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1, 2]; rw [l266 sK0 sK1]
  have l284 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l266 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l285 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l212 sK0 sK1]
    conv => enter [1]; rw [← l284 sK0 sK1]
  have l286 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l283 sK0 sK1]
    conv => enter [1]; rw [l108 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l287 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l266 sK0 sK1]
    conv => enter [1]; rw [l285 sK0 sK1]
  have l288 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l273 sK0 sK1]
  have l289 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l288 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l290 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l128 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l291 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l290 sK1 sK0]
    conv => enter [1]; rw [← l194 sK0 sK1 sK0]
  have l292 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l291 sK1 sK0]
    conv => enter [1]; rw [l271 sK0 sK1 sK0]
  have l293 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l292 sK1 sK0]
    conv => enter [1, 2]; rw [← l250 sK0 sK1]
  have l294 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l293 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l295 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l212 sK0 sK1]
    conv => enter [1]; rw [← l294 sK1 sK0]
  have l296 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l295 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l297 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l296 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l298 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l266 sK0 sK1]
    conv => enter [1]; rw [l297 sK0 sK1]
  have l299 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l298 sK0 sK1]
  have l300 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l299 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l301 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l302 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l303 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54014 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l304 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54014 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l15 sK0 sK1 sK1]
  have l305 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54014 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l306 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l307 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54014 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l308 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l307 sK0 sK1 X0]
    conv => enter [1]; rw [l9 sK0 sK1 (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l309 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l306 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l310 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l304 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l311 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l303 sK1 sK0]
  have l312 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l302 sK0 sK1]
    conv => enter [1]; rw [l300 sK0 sK1 sK1]
  have l313 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l301 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l314 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l308 sK0 sK1 X0]
    conv => enter [1]; rw [l237 sK0 sK1 (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l315 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l309 sK0 sK1 X0]
    conv => enter [1]; rw [← l148 sK0 sK1 (X0 ◇ X0)]
  have l316 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l310 sK0 sK1]
    conv => enter [1]; rw [l86 sK0 sK1]
  have l317 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l16 sK1 sK0]
    conv => enter [1]; rw [l311 sK1 sK0]
  have l318 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l312 sK0 sK1]
  have l319 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l313 sK0 sK1]
    conv => enter [1]; rw [l132 sK0 sK1]
  have l320 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l314 sK0 sK1 X0]
    conv => enter [1]; rw [l237 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))]
  have l321 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l315 sK0 sK1 X0]
    conv => enter [1]; rw [l237 sK0 sK1 (X0 ◇ X0)]
  have l322 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l316 sK0 sK1]
  have l323 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l319 sK0 sK1]
  have l324 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l320 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l214 sK0 sK1 (X0 ◇ X0)]
  have l325 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l322 sK0 sK1]
    conv => enter [1]; rw [l227 sK0 sK1]
  have l326 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l324 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))]
  have l327 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l326 sK0 sK1 X0]
    conv => enter [1]; rw [← l214 sK0 sK1 (X0 ◇ X0)]
  have l328 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l327 sK0 sK1 X0]
    conv => enter [1]; rw [l271 sK0 sK1 (X0 ◇ X0)]
  have l329 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l321 sK0 sK1 X0]
    conv => enter [1]; rw [← l328 sK0 sK1 X0]
  have l330 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l323 sK0 sK1]
  have l331 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l323 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l332 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
    conv => enter [1]; rw [l331 sK0 sK1 X0]
  have l333 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l330 sK1 sK0]
  have l334 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l332 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1]; rw [← l333 sK1 sK0]
  have l335 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l334 sK0 sK1]
  have l336 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l325 sK1 sK0]
  have l337 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l325 sK1 sK0]
  have l338 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l337 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l339 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l252 sK0 sK1]
    conv => enter [1]; rw [← l336 sK0 sK1]
  have l340 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l273 sK0 sK1]
    conv => enter [1]; rw [l339 sK0 sK1]
  have l341 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l335 sK0 sK1]
  have l342 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l335 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l343 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l342 sK0 sK1 X0]
  have l344 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l341 sK0 sK1]
    conv => enter [1]; rw [← l287 sK0 sK1]
  have l345 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l344 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l346 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l345 sK0 sK1 X0]
  have l347 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l317 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l348 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l317 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l349 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l317 sK1 sK0]
  have l350 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l349 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l351 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l348 sK0 sK1]
    conv => enter [1]; rw [← l165 sK0 sK1]
  have l352 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l165 sK0 sK1]
    conv => enter [1]; rw [← l347 sK1 sK0]
  have l353 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l350 sK1 sK0]
    conv => enter [1]; rw [l338 sK1 sK0 (sK0 ◇ sK1)]
  have l354 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l351 sK0 sK1]
    conv => enter [1]; rw [l266 sK0 sK1]
  have l355 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l352 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l356 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l353 sK1 sK0]
    conv => enter [1, 2]; rw [← l265 sK0 sK1]
  have l357 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l354 sK0 sK1]
  have l358 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l355 sK1 sK0]
  have l359 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l356 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l360 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [l357 sK0 sK1]
  have l361 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l358 sK1 sK0]
    conv => enter [1, 2]; rw [l266 sK0 sK1]
  have l362 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l359 sK1 sK0]
    conv => enter [1]; rw [← l282 sK0 sK1]
  have l363 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l361 sK1 sK0]
    conv => enter [1]; rw [← l232 sK0 sK1]
  have l364 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l362 sK1 sK0]
  have l365 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l363 sK1 sK0]
    conv => enter [1]; rw [l273 sK0 sK1]
  have l366 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l365 sK1 sK0]
  have l367 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l366 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l368 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l369 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l368 sK1 sK0 X0]
  have l370 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l364 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l371 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l370 sK0 sK1]
  have l372 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l371 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l373 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l372 sK1 sK0]
  have l374 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l373 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l375 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l374 sK1 sK0]
    conv => enter [1]; rw [l237 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l376 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l375 sK1 sK0]
    conv => enter [1]; rw [← l329 sK0 sK1 sK1]
  have l377 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l376 sK1 sK0]
    conv => enter [1]; rw [← l332 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l378 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l377 sK1 sK0]
    conv => enter [1]; rw [l344 sK0 sK1]
  have l379 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l378 sK1 sK0]
  have l380 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l379 sK1 sK0]
    conv => enter [1]; rw [l105 sK1 sK0 (sK0 ◇ sK1)]
  have l381 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l380 sK1 sK0]
    conv => enter [1]; rw [l289 sK0 sK1 (sK0 ◇ sK1)]
  have l382 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l381 sK1 sK0]
    conv => enter [1]; rw [← l369 sK1 sK0 (sK0 ◇ sK1)]
  have l383 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l382 sK1 sK0]
    conv => enter [1]; rw [← l317 sK1 sK0]
  have l384 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l367 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l385 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l384 sK0 sK1]
    conv => enter [1]; rw [← l340 sK0 sK1]
  have l386 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l385 sK0 sK1]
  have l387 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l386 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l388 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l383 sK1 sK0]
    conv => enter [1]; rw [l387 sK1 sK0]
  have l389 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l383 sK1 sK0]
  have l390 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l389 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l391 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l388 sK1 sK0]
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1, 2]; rw [← l388 sK1 sK0]
  have l392 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l391 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l393 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l392 sK1 sK0]
    conv => enter [1, 2]; rw [← l68 sK1 sK0]
  have l394 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l393 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l395 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = (sK1 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
    conv => enter [1, 2, 2]; rw [← l146 sK1 sK0]
  have l396 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l395 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l397 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l396 sK1 sK0]
    conv => enter [1, 2]; rw [← l343 sK0 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l398 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l397 sK1 sK0]
    conv => enter [1, 2]; rw [← l369 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l399 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l398 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l400 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l399 sK1 sK0]
    conv => enter [1]; rw [l338 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l401 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l400 sK1 sK0]
    conv => enter [1]; rw [← l369 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l402 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l390 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l401 sK1 sK0]
  have l403 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l402 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l404 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l403 sK1 sK0]
    conv => enter [1]; rw [← l343 sK0 sK1 (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l405 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l404 sK1 sK0]
    conv => enter [1]; rw [← l369 sK1 sK0 (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l406 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l405 sK1 sK0]
    conv => enter [1]; rw [l390 sK1 sK0 (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l407 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l406 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l408 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l407 sK1 sK0]
    conv => enter [1, 2]; rw [← l131 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l409 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l408 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l410 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l409 sK1 sK0]
    conv => enter [1, 2]; rw [← l343 sK0 sK1 sK1]
  have l411 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l410 sK1 sK0]
    conv => enter [1]; rw [l108 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l412 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l411 sK1 sK0]
    conv => enter [1]; rw [l300 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l413 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l412 sK1 sK0]
    conv => enter [1]; rw [← l369 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l414 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l413 sK1 sK0]
    conv => enter [1]; rw [l390 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l415 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l414 sK1 sK0]
    conv => enter [1, 2]; rw [← l346 sK0 sK1 sK1]
  have l416 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l318 sK0 sK1]
    conv => enter [1]; rw [← l415 sK1 sK0]
  have l417 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l416 sK1 sK0]
    conv => enter [1, 2]; rw [← l131 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l418 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l417 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l419 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l418 sK1 sK0]
    conv => enter [1, 2]; rw [← l335 sK0 sK1]
  have l420 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l419 sK1 sK0]
    conv => enter [1]; rw [l108 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l421 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l420 sK1 sK0]
    conv => enter [1]; rw [← l286 sK0 sK1]
  have l422 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l421 sK1 sK0]
  have l423 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l422 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l424 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l383 sK1 sK0]
    conv => enter [1]; rw [l423 sK1 sK0]
  have l425 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l424 sK1 sK0]
  have l426 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l425 sK0 sK1]
    conv => enter [1]; rw [l108 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l427 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l426 sK0 sK1]
    conv => enter [1]; rw [l300 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l428 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l427 sK0 sK1]
    conv => enter [1]; rw [← l369 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l429 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l390 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l428 sK0 sK1]
  have l430 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [← l429 sK1 sK0]
  have l431 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l430 sK0 sK1]
    conv => enter [1]; rw [← l31 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l432 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0]
    conv => enter [1]; rw [← l431 sK0 sK1]
  have l433 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l432 sK1 sK0]
    conv => enter [1]; rw [l325 sK1 sK0]
  have l434 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l433 sK0 sK1]
  have l435 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l383 sK1 sK0]
    conv => enter [1]; rw [l434 sK1 sK0]
  have l436 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1, 2]; rw [← l435 sK1 sK0]
  have l437 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l436 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l438 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l437 sK0 sK1]
    conv => enter [1, 2]; rw [← l364 sK1 sK0]
  have l439 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l438 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l440 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l439 sK0 sK1]
    conv => enter [1]; rw [← l394 sK1 sK0]
  have l441 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l439 sK0 sK1]
    conv => enter [1]; rw [← l367 sK1 sK0]
  have l442 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l439 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l443 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l340 sK0 sK1]
    conv => enter [1]; rw [← l442 sK0 sK1]
  have l444 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [l443 sK0 sK1]
  have l445 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l383 sK1 sK0]
    conv => enter [1]; rw [l444 sK1 sK0]
  have l446 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l440 sK0 sK1]
    conv => enter [1]; rw [l445 sK1 sK0]
  have l447 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l440 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l448 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l441 sK0 sK1]
  have l449 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l394 sK1 sK0]
    conv => enter [1]; rw [l448 sK1 sK0]
  have l450 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l440 sK0 sK1]
    conv => enter [1]; rw [l449 sK1 sK0]
  have l451 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l450 sK0 sK1]
  have l452 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l450 sK0 sK1]
    conv => enter [1]; rw [← l451 sK1 sK0]
  have l453 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53899 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l452 sK0 sK1]
  have l454 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l343 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l453 sK0 sK1]
  have l455 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l454 sK0 sK1]
    conv => enter [1]; rw [l139 sK0 sK1 (sK1 ◇ sK1)]
  have l456 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l148 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l455 sK0 sK1]
  have l457 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l456 sK0 sK1]
    conv => enter [1]; rw [← l369 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l458 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l457 sK0 sK1]
    conv => enter [1]; rw [← l231 sK0 sK1]
  have l459 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l458 sK0 sK1]
    conv => enter [1]; rw [← l250 sK0 sK1]
  have l460 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l459 sK0 sK1]
    conv => enter [1]; rw [l266 sK0 sK1]
  have l461 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l360 sK1 sK0]
    conv => enter [1]; rw [← l460 sK0 sK1]
  have l462 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l461 sK1 sK0]
    conv => enter [1]; rw [l237 sK0 sK1 (sK1 ◇ sK1)]
  have l463 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l462 sK1 sK0]
    conv => enter [1]; rw [← l369 sK1 sK0 (sK1 ◇ sK1)]
  have l464 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l463 sK1 sK0]
    conv => enter [1]; rw [l390 sK1 sK0 (sK1 ◇ sK1)]
  have l465 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l464 sK1 sK0]
    conv => enter [1]; rw [← l447 sK0 sK1 (sK1 ◇ sK1)]
  have l466 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l383 sK1 sK0]
    conv => enter [1]; rw [l465 sK1 sK0]
  have l467 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l440 sK0 sK1]
    conv => enter [1]; rw [l466 sK1 sK0]
  have l468 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l467 sK0 sK1]
    conv => enter [1]; rw [l132 sK0 sK1]
  have l469 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l468 sK0 sK1]
    conv => enter [1]; rw [← l323 sK0 sK1]
  have l470 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l128 sK0 sK1]
    conv => enter [1, 2]; rw [← l469 sK0 sK1]
  have l471 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l446 sK0 sK1]
    conv => enter [1]; rw [← l470 sK0 sK1]
  have l472 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l471 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l473 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l472 sK0 sK1 sK1]
    conv => enter [1]; rw [← l323 sK0 sK1]
  have l474 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l473 sK0 sK1]
    conv => enter [1]; rw [← l435 sK1 sK0]
  have l475 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l440 sK0 sK1]
    conv => enter [1]; rw [← l474 sK0 sK1]
  have l476 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l475 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l477 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l476 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l478 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l305 sK1 sK0]
    conv => enter [1]; rw [← l123 sK0 sK1 sK0]
  have l479 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l478 sK1 sK0]
    conv => enter [1]; rw [← l477 sK0 sK1 sK0]
  have l480 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l479 sK1 sK0]
    conv => enter [1]; rw [← l250 sK0 sK1]
  have l481 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l480 sK1 sK0]
    conv => enter [1]; rw [l266 sK0 sK1]
  have l482 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l481 sK1 sK0]
    conv => enter [1]; rw [← l360 sK1 sK0]
  have l483 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l482 sK1 sK0]
    conv => enter [1]; rw [l383 sK1 sK0]
  have l484 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l483 sK1 sK0]
    conv => enter [1]; rw [← l440 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l484 x y]

end Semigroup5
