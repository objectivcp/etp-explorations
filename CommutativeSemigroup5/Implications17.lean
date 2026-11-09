import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_53890_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53890 : Equation53890 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l4 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [h53890 X1 X2 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X0]
  have l5 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [h53890 X1 X2 sK0 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK2 X0]
  have l6 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [l5 X1 X2 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l7 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [l4 X1 X2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l8 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h53890 X0 X0 sK0 sK1]
    conv => enter [1]; rw [h53890 X0 X0 sK0 (sK2 ◇ sK2)]
  have l9 : ∀ X1 sK0 sK2 X0 sK1 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l6 X1 X1 sK0 sK2 X0]
    conv => enter [1]; rw [h53890 X1 X1 sK0 sK1]
  have l10 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l7 X1 X1 sK0 sK1 X0]
    conv => enter [1]; rw [h53890 X1 X1 sK0 sK1]
  have l11 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1]; rw [← l8 X0 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [← l0 X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X1]
    conv => enter [1, 1]; rw [← l8 X0 sK0 sK1 sK2]
  have l13 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l8 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X1]
  have l14 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← l9 X0 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l13 X1 X0 sK0 sK1 X0]
  have l15 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [l12 sK0 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l16 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [l15 sK0 sK2 X0 X1 sK1]
    conv => enter [1]; rw [l10 X0 sK0 sK1 X1]
  have l17 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l11 sK0 sK2 X0 sK1]
  have l18 : ∀ sK0 sK1 X1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 X1 X0 sK2
    conv => enter [1]; rw [← l1 X1 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l11 sK0 sK2 X0 sK1]
  have l19 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X1 X0 sK0]
    conv => enter [1]; rw [l9 X1 sK0 sK0 X0 sK1]
  have l20 : ∀ sK0 sK2 X1 X2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X1 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 X1 X2 sK1 X0
    conv => enter [1]; rw [← h53890 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0 X1 X2]
    conv => enter [1, 2]; rw [← l17 sK0 sK1 X0 sK2]
  have l21 : ∀ sK0 sK2 X1 X2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X1 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK2 X1 X2 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK2 X1 X2 sK1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l22 : ∀ X0 sK0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [← l19 sK0 sK1 X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l21 sK0 sK2 X1 X2 sK1 X0]
  have l23 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l22 X0 sK0 sK1 X0 X1 X0]
    conv => enter [1]; rw [l16 sK0 X0 X1 (X1 ◇ X0) sK1]
  have l24 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h53890 sK2 X0 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK2)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l24 sK2 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK2]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53890 sK0 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h53890 sK0 sK1 sK0 sK0]
  have l27 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l25 sK2 X0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK2 sK2 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK0 sK1 sK0]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK0 sK1 X0]
  have l30 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← l1 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l27 sK2 X0 sK0 sK1]
  have l31 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l30 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l14 sK0 sK0 sK1 sK0]
  have l32 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK0]
    conv => enter [1]; rw [← l31 X0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l32 x y x z]

theorem Equation43_4512_53890_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53890 : Equation53890 G) : Equation53868 G := by
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
  have l3 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l4 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l5 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l4 sK0 sK3 X0]
  have l6 : ∀ X1 X2 sK1 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) := by
    intro X1 X2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53890 X1 X2 sK1 (X0 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK3 sK0 X0]
  have l7 : ∀ X1 X2 sK1 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X1 X2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l6 X1 X2 sK1 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l8 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h53890 X0 X0 sK1 sK2]
    conv => enter [1]; rw [h53890 X0 X0 sK1 (sK3 ◇ sK0)]
  have l9 : ∀ X1 sK1 sK3 sK0 X0 sK2 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [← l7 X1 X1 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [h53890 X1 X1 sK1 sK2]
  have l10 : ∀ X1 X0 sK1 sK2 sK3 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro X1 X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l8 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 X0 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1]
  have l11 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l9 X0 sK1 X0 X0 X1 sK2]
    conv => enter [1]; rw [← l10 X1 X0 sK1 sK2 X0 X0]
  have l12 : ∀ sK0 X0 sK3 sK1 : G, (sK0 ◇ (X0 ◇ (sK3 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK0 X0 sK3 sK1
    conv => enter [1, 2]; rw [← l5 sK0 X0 sK3]
    conv => enter [1]; rw [h53890 sK0 (X0 ◇ sK3) sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l13 : ∀ X0 X1 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 sK1 sK3 sK0
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [h53890 X0 X1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l14 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK0]
    conv => enter [1]; rw [h53890 sK0 sK3 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53890 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h53890 sK1 sK2 sK1 sK1]
  have l16 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l14 sK3 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l17 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 sK1 X0 X0]
    conv => enter [1, 2]; rw [← l8 sK1 sK1 sK2 X0 X0]
  have l18 : ∀ sK0 X0 sK3 sK1 : G, (sK0 ◇ (X0 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK3 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK3 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l11 sK1 sK1 sK2 sK1]
  have l20 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK0)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l16 sK3 sK0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK0 sK1]
  have l21 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK1 sK1 sK2 X0]
    conv => enter [1]; rw [← l17 X0 X1 sK1 sK2]
  have l22 : ∀ sK0 X0 sK3 sK1 : G, (sK0 ◇ (X0 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK0)) := by
    intro sK0 X0 sK3 sK1
    conv => enter [1]; rw [l18 sK0 X0 sK3 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK0 sK1]
  have l23 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK3 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK3 sK0 sK0 sK2]
  have l24 : ∀ sK1 sK2 sK0 X0 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [← l9 sK1 sK1 sK3 sK0 sK0 sK2]
    conv => enter [1]; rw [← l22 sK0 X0 sK3 sK1]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK3 ◇ sK0) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← l23 sK3 sK0 sK1 sK2]
  have l26 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK2 sK0 X0 sK3]
    conv => enter [1]; rw [l1 sK0 X0 (sK3 ◇ sK0)]
  have l27 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK3 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK0 X0]
  have l28 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l25 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 (sK3 ◇ sK0) sK0 X0]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l27 sK1 sK2 sK1 sK1 X0]
    conv => enter [1]; rw [← l28 X0 sK1 sK2 sK1 sK1]
  have l30 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l1 sK1 (sK3 ◇ sK0) sK1]
    conv => enter [1]; rw [← l21 sK1 sK2 sK1 (sK3 ◇ sK0)]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK1]
    conv => enter [1]; rw [← l30 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l31 x y z w]

theorem Equation43_4512_53890_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53890 : Equation53890 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l4 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [h53890 X1 X2 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X0]
  have l5 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53890 X0 X1 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l6 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h53890 X0 X1 X2 X3]
    conv => enter [1]; rw [l0 X0 (X2 ◇ (X2 ◇ X3)) X4]
  have l7 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l6 X0 X1 X4 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ X3) (X0 ◇ X4)]
  have l8 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [l4 X1 X2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l9 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 X3 (X0 ◇ X4)]
  have l10 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h53890 X1 X1 sK1 sK2]
    conv => enter [1]; rw [l8 X1 X1 sK0 sK1 X0]
  have l11 : ∀ X0 X1 X4 X2 sK0 sK1 sK2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro X0 X1 X4 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l9 X0 X1 X4 X2 X0]
    conv => enter [1]; rw [l5 X2 (X0 ◇ (X0 ◇ X4)) sK0 sK1 sK2]
  have l12 : ∀ X0 X1 X4 X2 sK1 sK2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X4 X2 sK1 sK2
    conv => enter [1]; rw [l11 X0 X1 X4 X2 X0 sK1 sK2]
    conv => enter [1]; rw [← l10 X2 sK1 sK2 X0 sK2]
  have l13 : ∀ X0 X1 X4 X2 sK1 sK2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X4)) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X4 X2 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X4]
    conv => enter [1]; rw [l12 X0 X1 X4 X2 sK1 sK2]
  have l14 : ∀ X0 X1 X4 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X4))) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X4 X2 sK1 sK2
    conv => enter [1, 2]; rw [h4512 X0 X1 X4]
    conv => enter [1]; rw [l13 X0 X1 X4 X2 sK1 sK2]
  have l15 : ∀ X0 sK0 sK1 sK2 X2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2 X2
    conv => enter [1]; rw [← l5 X0 (X0 ◇ X0) sK0 sK1 sK2]
    conv => enter [1]; rw [l14 X0 X0 X0 X2 sK1 sK2]
  have l16 : ∀ X0 sK1 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X2
    conv => enter [1]; rw [l10 X0 sK1 sK2 X0 sK2]
    conv => enter [1]; rw [l15 X0 X0 sK1 sK2 X2]
  have l17 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l16 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h43 X1 (sK1 ◇ (sK1 ◇ sK2))]
  have l18 : ∀ X0 sK1 sK2 X2 X1 : G, ((X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X2)) := by
    intro X0 sK1 sK2 X2 X1
    conv => enter [1, 1]; rw [l16 X0 sK1 sK2 X1]
    conv => enter [1]; rw [l0 X1 (sK1 ◇ (sK1 ◇ sK2)) X2]
  have l19 : ∀ X2 X0 sK1 sK2 X1 : G, (X2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro X2 X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l16 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← l1 X1 (sK1 ◇ (sK1 ◇ sK2)) X2]
  have l20 : ∀ X2 sK0 sK1 sK2 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro X2 sK0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2 X2]
    conv => enter [1]; rw [l19 X2 X2 sK1 sK2 X1]
  have l21 : ∀ sK1 sK2 X1 X2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X2)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [← l18 X0 sK1 sK2 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK2)) X2]
  have l22 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X1]
  have l23 : ∀ X2 sK0 sK1 sK2 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X2)) := by
    intro X2 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l20 X2 sK0 sK1 sK2 X2]
    conv => enter [1]; rw [← l21 sK1 sK2 X1 X2 X2]
  have l24 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l22 sK0 sK1 sK2 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l23 X2 sK0 sK1 sK2 sK0]
  have l25 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [h53890 X0 X1 X2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l16 X2 sK1 sK2 sK0]
  have l26 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l25 X0 X1 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 sK2 X0]
  have l27 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l26 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l27 x y x y z]

theorem Equation43_4512_53890_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53890 : Equation53890 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l10 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53890 X0 X1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l7 sK0 sK1]
  have l11 : ∀ X0 X3 X4 X1 X2 : G, (X0 ◇ ((X0 ◇ X3) ◇ X4)) = (X4 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X3 X4 X1 X2
    conv => enter [1]; rw [l0 X0 (X0 ◇ X3) X4]
    conv => enter [1, 2]; rw [h53890 X0 X3 X1 X2]
  have l12 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l11 X0 X3 X4 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X3 X4]
  have l13 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l14 : ∀ X0 sK2 X4 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X4 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 sK2 X4 X1 X2
    conv => enter [1]; rw [← h53890 X0 (X0 ◇ X4) sK2 sK2]
    conv => enter [1]; rw [← l12 X4 X0 X1 X2 X0]
  have l15 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l16 : ∀ X0 sK2 X4 X1 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X4 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK2 X4 X1 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK2 X4 X1 X0]
    conv => enter [1, 2, 2]; rw [h53890 X1 X0 sK0 sK1]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h53890 X0 X0 sK0 sK1]
    conv => enter [1]; rw [l15 X0 X0 sK1 sK0]
  have l18 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l17 X0 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK2 X0 (sK0 ◇ sK1) sK0 sK1]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l18 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 sK2]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l21 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l20 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← l20 X1 sK0 sK1 X0]
  have l22 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l21 X0 sK0 sK1 X1]
    conv => enter [1]; rw [h43 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 X0 sK0 sK1 (sK2 ◇ sK2)]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 X0 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h53890 sK2 X0 sK0 sK1]
  have l26 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l25 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 sK2]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53890 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 sK0]
  have l29 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l26 sK2 X0 sK0 sK1]
  have l30 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l29 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
  have l31 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l32 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l31 X0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l32 x y x z]

theorem Equation43_4512_53890_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53890 : Equation53890 G) : Equation53914 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK1 sK0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l6 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [h53890 X1 X2 sK1 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 X0]
  have l7 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [l6 X1 X2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l8 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l7 X1 X1 sK1 sK2 X0]
    conv => enter [1]; rw [h53890 X1 X1 sK1 (sK2 ◇ sK2)]
  have l9 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h53890 sK1 (X0 ◇ sK0) sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53890 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h53890 X0 X1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l1 X0 X0 X1]
  have l12 : ∀ X0 sK1 sK2 X2 X3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 sK1 sK2 X2 X3
    conv => enter [1]; rw [← h53890 X0 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h53890 X0 X0 X2 X3]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53890 sK1 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
  have l14 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h53890 sK2 X0 sK1 (sK2 ◇ sK2)]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (((sK2 ◇ sK2) ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h53890 (sK2 ◇ sK2) X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
  have l16 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0]
    conv => enter [1]; rw [h43 ((sK2 ◇ sK2) ◇ X0) (sK1 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0 sK2]
    conv => enter [1]; rw [← h53890 sK2 sK2 sK2 (sK2 ◇ sK2)]
  have l18 : ∀ X0 sK1 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK1 sK2 X2
    conv => enter [1]; rw [l12 X0 sK1 sK2 X2 X0]
    conv => enter [1, 2]; rw [h53890 X2 X0 sK1 (sK2 ◇ sK2)]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53890 sK1 (sK2 ◇ sK2) sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l13 sK1 sK1 sK0]
    conv => enter [1]; rw [l9 sK1 sK1 sK0 X0]
  have l22 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK2) X0 (sK1 ◇ (sK2 ◇ sK2))]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l24 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l17 sK2 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l22 sK1 sK2 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l26 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l24 sK2 sK1]
    conv => enter [1]; rw [← l18 sK1 sK1 sK2 (sK2 ◇ sK2)]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l28 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l26 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l29 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
    conv => enter [1]; rw [l28 sK1 sK2 sK2]
  have l30 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l31 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l30 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l21 sK1 sK0 X0]
  have l32 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
    conv => enter [1]; rw [← l31 sK1 sK2 X0 sK1]
  have l33 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) sK1 sK2 X0]
    conv => enter [1]; rw [← l33 X0 sK1 sK2 sK0]
  have l35 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l27 sK1 sK2 sK1]
    conv => enter [1]; rw [l34 sK1 sK1 sK2 X0]
  have l36 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53890 X0 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1, 2, 2]; rw [← l32 sK1 sK2 X0]
  have l37 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l36 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l11 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK2 X0]
  have l38 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l37 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l35 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l39 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l17 sK2 X0]
  have l40 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l29 sK1 sK2]
    conv => enter [1]; rw [← l39 X0 sK2]
  have l41 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l38 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l1 X0 X0 X1]
  have l42 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l40 sK1 sK2 sK1]
    conv => enter [1]; rw [l41 sK1 sK2 X1 X0]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
    conv => enter [1]; rw [l42 sK1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l43 x y z]
  conv => enter [1]; rw [← l40 y z y]

theorem Equation43_4512_53878_implies_Equation53895 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53895 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l1 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK4 ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1, 1]; rw [h43 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK4 X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l4 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK4)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l1 sK4 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l5 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l3 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l6 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l5 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h53878 sK2 X0 X1 sK3]
  have l7 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53878 sK0 sK1 X0 X1]
  have l8 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h53878 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ X1)]
  have l9 : ∀ sK2 sK3 X0 X1 X2 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ X0))) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK2 sK3 X0 X1 X2
    conv => enter [1, 2]; rw [h53878 sK3 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ (X1 ◇ X2))]
  have l10 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ X0))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h53878 (sK2 ◇ sK3) X0 sK2 sK2]
    conv => enter [1]; rw [← l9 sK2 sK3 X0 sK2 sK2]
  have l11 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ sK2) = ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l3 sK2 sK3 sK2]
    conv => enter [1]; rw [l8 sK2 sK3 X0 X1]
  have l12 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l7 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
  have l13 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h53878 sK2 sK3 sK3 X0]
    conv => enter [1]; rw [← l10 sK2 sK3 X0]
  have l14 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l11 sK2 sK3 X0 X1]
  have l15 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l13 sK2 sK3 sK2]
    conv => enter [1]; rw [l6 sK2 sK3 (sK2 ◇ sK3) sK2]
  have l16 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l15 sK2 sK3]
    conv => enter [1]; rw [← h53878 sK2 sK2 sK2 sK3]
  have l17 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l3 sK2 sK3 sK2]
    conv => enter [1]; rw [l16 sK2 sK3]
  have l18 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l17 sK2 sK3]
  have l19 : ∀ sK2 sK3 X0 X1 X2 : G, ((sK2 ◇ sK3) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l14 sK2 sK3 X0 X1]
  have l20 : ∀ sK2 sK3 X2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X2) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 X2 X0 X1
    conv => enter [1]; rw [← l19 sK2 sK3 X0 X1 X2]
    conv => enter [1]; rw [l6 sK2 sK3 (X0 ◇ X1) X2]
  have l21 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [h53878 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← l20 sK2 sK3 X2 sK2 sK2]
  have l22 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X2) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l18 sK2 sK3]
    conv => enter [1]; rw [l21 sK2 sK3 X2]
  have l23 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l22 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l24 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h53878 X0 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [← l18 sK2 sK3]
  have l25 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l23 sK2 sK3 X0]
    conv => enter [1]; rw [← l24 X0 sK2 sK3]
  have l26 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ sK2))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l25 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ sK2)]
  have l27 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l26 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h53878 X0 X1 (X0 ◇ X1) sK2]
  have l28 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l27 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
  have l29 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [l12 sK1 sK0 X0 sK4]
  have l30 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l28 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l29 sK4 sK1 sK0 X0]
  have l31 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l30 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) X0]
  intro x y z w u
  conv => enter [1]; rw [l31 x y x z w u]

theorem Equation43_4512_53877_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h53877 X2 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X0 X1]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h53877 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ X2)) X3]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53877 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53877 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h53877 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ X1))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53877 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 X0 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l10 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l3 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X2) X3]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0]
  have l14 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l10 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X2 X3]
  have l15 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 sK1]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X1 X0 (X1 ◇ X0)]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l14 X0 (sK0 ◇ sK1) X0 sK0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l15 sK0 X0 sK1]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) X0 X0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l20 x y]

theorem Equation43_4512_53877_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l12 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK2]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK2)]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
  have l15 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((X0 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK2) X1]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l15 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK2)]
  have l17 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l12 sK1 sK2 X1 X0]
  have l18 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l17 sK1 sK2 X0 X1]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53877 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53877 X0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l21 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53877 X0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2 sK2]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53877 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53877 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X0)]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l26 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l20 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 X0 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1 sK0]
    conv => enter [1]; rw [← l26 sK1 sK0 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l37 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h53877 X0 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l38 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l30 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l39 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l38 sK1 sK0 sK2]
    conv => enter [1]; rw [l18 sK1 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 sK2 sK0]
  have l41 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l39 sK1 sK0 sK2]
    conv => enter [1]; rw [← l21 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l42 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l41 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l43 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l42 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l44 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l43 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l45 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l44 sK1 sK0 sK2]
    conv => enter [1]; rw [← l27 sK1 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 sK1 sK0]
    conv => enter [1]; rw [← l45 sK1 sK0 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l49 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l50 x y z]

theorem Equation43_4512_53877_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK2 ◇ sK2)]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK1) X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l4 sK0 sK1 X1 X0]
  have l9 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53877 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l11 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h53877 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (X0 ◇ X0)]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK0]
    conv => enter [1]; rw [l11 sK0 sK2 X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l14 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l12 sK0 sK2 X0]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l16 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK2 X0]
    conv => enter [1]; rw [← l1 X0 X0 (sK0 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK1) X0 X0]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  have l20 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1]
    conv => enter [1]; rw [← h53877 (sK0 ◇ sK1) (sK0 ◇ sK1) sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l21 sK0 sK2 sK1]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation43_4512_53877_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation53868 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 sK0 sK3 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK3]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l6 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l7 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l8 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l9 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l10 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l9 sK1 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
  have l11 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = ((X0 ◇ sK3) ◇ (sK0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [l3 sK3 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK3) X1]
  have l12 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK3))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l11 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l2 sK0 X1 (X0 ◇ sK3)]
  have l13 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l12 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l8 sK3 sK0 X1 X0]
  have l14 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l13 sK3 sK0 X0 X1]
  have l15 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53877 X0 sK1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l2 sK1 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK3 ◇ sK0))]
  have l16 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53877 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l17 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53877 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) (X0 ◇ X0)]
  have l18 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l17 sK1 sK3 sK0 X0]
  have l19 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [l16 sK1 sK2 X0]
  have l20 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l18 sK1 sK3 sK0 X0]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l19 sK1 sK2 X0]
  have l22 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l10 sK1 sK3 sK0]
  have l23 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← l2 X0 X0 (sK1 ◇ (sK3 ◇ sK0))]
  have l24 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK3 sK0]
    conv => enter [1]; rw [← l2 (sK3 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK1 ◇ (sK3 ◇ sK0))]
  have l25 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK3 sK0]
    conv => enter [1]; rw [l14 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK1 ◇ (sK3 ◇ sK0))]
  have l26 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l25 sK1 sK3 sK0]
    conv => enter [1]; rw [← l15 (sK3 ◇ sK0) sK1 sK3 sK0]
  have l27 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK3 sK0]
    conv => enter [1]; rw [l2 (sK3 ◇ sK0) (sK3 ◇ sK0) sK1]
  have l28 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l27 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) (sK3 ◇ sK0)]
  have l29 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l28 sK1 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
  have l30 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l7 sK1 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← l29 sK1 sK3 sK0]
  have l31 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l30 sK1 sK3 sK0]
  have l32 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l10 sK1 sK3 sK0]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l31 sK3 sK0 sK1]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK1 ◇ sK2)]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l5 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l36 : ∀ sK1 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ X1))) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l23 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [h53877 X0 (sK1 ◇ (sK3 ◇ sK0)) X1]
  have l37 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l36 sK1 sK3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l20 sK1 sK3 sK0 sK1]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l37 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z w
  conv => enter [1]; rw [l38 x y z w]

theorem Equation43_4512_53877_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53877 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53877 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0]
    conv => enter [1]; rw [← l0 X0 X0 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [h53877 X0 (sK1 ◇ sK2) X1]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK1 sK2 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l13 x y z]
  conv => enter [1]; rw [l11 y z x]

theorem Equation43_4512_53877_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53877 : Equation53877 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53877 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l4 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h53877 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK3 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ sK3) = ((sK3 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l4 sK3 sK0 X0]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 X0]
  have l7 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l5 sK3 sK0 X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l9 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l7 sK3 sK0 X0]
    conv => enter [1]; rw [← l0 X0 X0 (sK3 ◇ sK0)]
  have l10 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ ((sK3 ◇ sK0) ◇ (X1 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l9 sK3 sK0 X0]
    conv => enter [1]; rw [h53877 X0 (sK3 ◇ sK0) X1]
  have l11 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l10 sK3 sK0 X0 sK3]
    conv => enter [1, 2]; rw [← l7 sK3 sK0 sK3]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l11 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l11 sK3 sK0 (sK1 ◇ sK2)]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]
  conv => enter [1]; rw [l11 z w x]

theorem Equation43_4512_53874_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (sK1 ◇ X0) X1]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l4 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l6 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l5 X1 sK0 sK1 sK0]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53874 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1 X1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 X1]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l8 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l10 x y x]

theorem Equation43_4512_53874_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53874 X1 sK0 (X0 ◇ (sK1 ◇ sK2))]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53874 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0)]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK0 ◇ sK1)]
  have l9 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l4 X1 sK0 sK1 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l12 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 X1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h53874 X1 sK0 (sK1 ◇ sK2)]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l16 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 (sK1 ◇ sK2) (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l17 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l18 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 X1 sK0]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK2 sK0]
  have l20 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l12 (sK1 ◇ sK2) sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l19 sK1 sK2 sK0 X0]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l20 sK1 sK2 sK0 X0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation43_4512_53874_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l3 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0))) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1, 2, 2]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h53874 X1 sK0 (X0 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l3 X1 sK0 sK2 X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l8 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h53874 X0 sK0 sK1]
    conv => enter [1]; rw [h53874 X0 sK0 (sK2 ◇ sK2)]
  have l9 : ∀ X1 sK0 sK2 X0 sK1 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l6 X1 sK0 sK2 X0]
    conv => enter [1]; rw [h53874 X1 sK0 sK1]
  have l10 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l8 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X1]
  have l11 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← l9 X0 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l10 X1 X0 sK0 sK1 X0]
  have l12 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (sK1 ◇ X0) X1]
  have l13 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l12 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l14 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l13 X1 sK0 sK1 sK0]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53874 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l14 sK0 sK1 X1]
  have l16 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l15 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l11 X1 sK0 sK1 X0]
  have l17 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l16 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 X1]
  intro x y z
  conv => enter [1]; rw [l17 x y x (z ◇ z)]

theorem Equation43_4512_53874_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53868 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l3 sK1 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
  have l5 : ∀ X1 sK1 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) = (X1 ◇ (X1 ◇ sK1)) := by
    intro X1 sK1 sK3 sK0 X0
    conv => enter [1, 2, 2]; rw [l2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h53874 X1 sK1 (X0 ◇ (sK3 ◇ sK0))]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53874 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ X0)]
  have l7 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53874 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) ((sK3 ◇ sK0) ◇ X0)]
  have l8 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← l0 (sK3 ◇ sK0) X0 (sK1 ◇ (sK3 ◇ sK0))]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l10 : ∀ X1 sK1 sK3 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X1 ◇ (X1 ◇ sK1)) := by
    intro X1 sK1 sK3 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 X1 sK1 sK3 sK0 X0]
  have l11 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1) = ((sK3 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK3 sK0 X0]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l9 sK1 sK2 X0]
  have l13 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h53874 X0 sK1 sK2]
    conv => enter [1]; rw [h53874 X0 sK1 (sK3 ◇ sK0)]
  have l14 : ∀ X1 sK1 sK3 sK0 X0 sK2 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l10 X1 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [h53874 X1 sK1 sK2]
  have l15 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l11 sK1 sK3 sK0 X0]
  have l16 : ∀ X1 X0 sK1 sK2 sK3 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro X1 X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l13 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 X0 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1]
  have l17 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l14 X0 sK1 X0 X0 X1 sK2]
    conv => enter [1]; rw [← l16 X1 X0 sK1 sK2 X0 X0]
  have l18 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK2) (sK2 ◇ X0) X1]
  have l19 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l18 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l20 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l12 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l19 X1 sK1 sK2 sK1]
  have l21 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53874 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK2 X1]
  have l22 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l21 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l17 X1 sK1 sK2 X0]
  have l23 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l22 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l20 sK1 sK2 X1]
  have l24 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l4 sK1 sK3 sK0]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2 (sK3 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l24 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l25 x y z w]

theorem Equation43_4512_53874_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53874 : Equation53874 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h53874 X1 sK0 (X0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53874 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 X0 (sK0 ◇ sK1)]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l2 X1 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l7 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l5 X1 sK0 sK1 X0]
    conv => enter [1]; rw [h53874 X1 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) (sK0 ◇ sK1)]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l7 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [l10 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53874 X0 (sK0 ◇ sK1) (sK1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1 X0]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 X0 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [l14 X0 sK0 sK1]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 (sK0 ◇ sK1)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation43_4512_53868_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53868 : Equation53868 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h53868 sK0 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l1 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 sK0 X0 X1 X2]
  have l2 : ∀ sK0 X0 X3 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X3) := by
    intro sK0 X0 X3
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X3]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [← l4 x y x]

theorem Equation43_4512_53868_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53868 : Equation53868 G) : Equation53864 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53868 X0 X1 X0 X0]
    conv => enter [1]; rw [← h53868 X0 X2 X0 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation43_4512_53868_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53868 : Equation53868 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← h53868 sK2 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 X2]
  have l2 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 sK2 X0 X1 X2]
  have l3 : ∀ sK2 X0 X3 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ X3) := by
    intro sK2 X0 X3
    conv => enter [1]; rw [← l2 sK2 sK2 sK2 X0]
    conv => enter [1]; rw [l2 sK2 sK2 sK2 X3]
  have l4 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← l2 sK2 X1 X2 X0]
    conv => enter [1]; rw [← l0 X1 X2 (sK2 ◇ sK2)]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l3 sK2 X0 X1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) X1]
  have l6 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l5 sK2 X1 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) X1]
  have l7 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l6 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2) X0]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 sK2 sK0]
  have l11 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK2 X0 sK0]
  have l12 : ∀ X1 X2 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X1 X2 sK2 X0
    conv => enter [1]; rw [h53868 X1 X2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l4 sK2 X0 X1 X1]
  have l13 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [l12 X1 X2 sK2 X1]
    conv => enter [1, 2]; rw [← l9 sK0 sK2 X1]
  have l14 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [l13 X1 X2 sK0 sK2]
    conv => enter [1]; rw [← l11 sK0 sK2 X1]
  intro x y z
  conv => enter [1]; rw [l14 x y x z]
  conv => enter [1]; rw [l10 x z]

theorem Equation43_4512_53868_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53868 : Equation53868 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53868 X0 X1 X0 X0]
    conv => enter [1]; rw [← h53868 X0 X2 X0 X0]
  have l8 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l7 (sK0 ◇ sK1) X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK1) X0]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [l7 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 (sK1 ◇ sK2)]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l17 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l14 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK0 sK1 X0 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK1 sK2]
  have l26 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l26 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 (sK1 ◇ sK2)]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l27 sK1 sK0 sK2]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l29 sK1 sK2 sK0]
  have l34 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l34 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l35 x y z]
  conv => enter [1]; rw [l29 y z x]

theorem Equation43_4512_53867_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53867 : Equation53867 G) : Equation4268 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h53867 sK0 X1 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X1 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [← l4 x y x]

theorem Equation43_4512_53867_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53867 : Equation53867 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l7 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53867 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK1]
    conv => enter [1]; rw [← h53867 sK0 X0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK2) sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK0]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation43_4512_53867_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53867 : Equation53867 G) : Equation53868 G := by
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
  have l3 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ sK2)]
  have l5 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 2]; rw [← l0 sK1 (sK3 ◇ sK0) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h53867 sK1 X0 (sK3 ◇ sK0)]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [← h53867 sK1 X0 sK2]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53867 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 (sK1 ◇ sK2)]
  have l8 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h53867 sK1 X0 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l9 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l8 sK1 X0 sK3 sK0]
    conv => enter [1]; rw [← l3 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l10 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l7 sK1 X0 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l12 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l5 sK1 sK3 sK0 X0]
  have l13 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2 sK1]
    conv => enter [1]; rw [l10 sK1 sK1 sK2]
  have l14 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l12 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK1 sK2]
  have l15 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 sK2]
  have l16 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK0 sK2]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 sK3 sK0 sK2]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l17 sK1 sK2 sK3 sK0]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l19 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l21 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l20 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l21 sK1 sK3 sK0 sK2]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
  have l24 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l25 : ∀ sK1 X0 X1 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 X0 X1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 2]; rw [l9 sK1 X0 sK3 sK0]
  have l26 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l25 sK1 X0 X1 sK1 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 sK1 sK1]
  have l27 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l24 sK1 sK3 sK0]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l29 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (X1 ◇ X0))) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [← l25 sK1 X1 X0 sK3 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 X1 X0]
  have l30 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 X0 X1]
    conv => enter [1]; rw [l26 sK1 X0 X1 sK2]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1]
  have l32 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l28 sK1 sK2 sK3 sK0]
  have l33 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ X0) sK3 sK0]
    conv => enter [1]; rw [← l29 X0 sK1 sK3 sK0 sK1]
  have l34 : ∀ sK1 sK3 sK0 X1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 X1 sK2
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ X1) sK3 sK0]
    conv => enter [1]; rw [l30 sK1 sK1 X1 sK2]
  have l35 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l22 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l33 sK1 sK1 sK1 X0]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 sK1 sK1]
  have l36 : ∀ sK1 sK3 sK0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 X1
    conv => enter [1]; rw [l34 sK1 sK3 sK0 X1 sK1]
    conv => enter [1, 2]; rw [l31 sK1 sK1 sK3 sK0]
  have l37 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l31 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [l35 sK1 sK1 X0]
    conv => enter [1, 2]; rw [l31 sK1 sK1 sK3 sK0]
  have l38 : ∀ X1 sK1 sK2 sK3 sK0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l32 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l36 sK1 sK3 sK0 X1]
  have l39 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l37 sK1 sK1 sK1 X0]
    conv => enter [1, 2]; rw [← l32 sK1 sK2 sK1 sK1]
  have l40 : ∀ sK1 sK3 sK0 X1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 X1 sK2
    conv => enter [1]; rw [l9 sK1 (sK3 ◇ sK0) sK3 sK0]
    conv => enter [1]; rw [← l38 X1 sK1 sK2 sK3 sK0]
  have l41 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK1]
    conv => enter [1]; rw [← l40 sK1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l41 x y z w]

theorem Equation43_4512_53864_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53864 : Equation53864 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53864 sK0 X0 X1]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ sK1) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l14 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1]; rw [← l14 sK0 X0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l17 x y]

theorem Equation43_4512_53864_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53864 : Equation53864 G) : Equation53867 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ X0) X1]
  have l2 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l3 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ X0)) = (((sK2 ◇ sK2) ◇ X0) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h53864 sK2 X0 X1]
    conv => enter [1]; rw [← l2 sK2 X0 X1]
  have l4 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l3 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [l4 sK2 X0 X1]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h43 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK2 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l8 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK2 X0]
    conv => enter [1]; rw [← l5 sK2 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
  have l10 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2 X0]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l7 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l10 sK0 sK2 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53864 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l12 sK0 sK2 (sK0 ◇ sK1)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l17 x y z]
  conv => enter [1]; rw [l11 x z]

theorem Equation43_4512_53863_implies_Equation54162 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53863 : Equation53863 G) : Equation54162 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 X0 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53863 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53863 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l19 sK1 X0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l38 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53863 X0 sK1]
    conv => enter [1]; rw [l0 X0 X0 (sK1 ◇ sK1)]
  have l42 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 X0]
    conv => enter [1]; rw [← l41 X0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l42 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l43 x y]
  conv => enter [1]; rw [l40 x y]

theorem Equation43_4512_53858_implies_Equation53821 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53821 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 sK0 sK3 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK3]
  have l1 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53858 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h53858 X0 X1 X1 X1 X1]
  have l3 : ∀ sK1 X1 X2 X3 X4 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK1 X1 X2 X3 X4]
  have l4 : ∀ sK1 X1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 X1 sK3 sK0 X0
    conv => enter [1]; rw [l3 sK1 X1 sK0 X0 sK3]
    conv => enter [1, 2]; rw [← l1 sK3 sK0 X0]
  have l5 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 X0 sK3 sK0 sK2]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x x y z w]

theorem Equation43_4512_53858_implies_Equation53811 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53811 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l2 : ∀ sK0 X1 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK0 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK0 X1 X2 X3 X4]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation43_4512_53858_implies_Equation53817 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53817 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l4 : ∀ sK0 X1 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK0 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK0 X1 X2 X3 X4]
  have l5 : ∀ sK0 X1 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 X1 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l1 sK1 X0 sK2]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X0 sK1 sK2]
    conv => enter [1]; rw [← l2 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x x y z]

theorem Equation43_4512_53858_implies_Equation53841 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53841 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l2 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 X0]
  have l3 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53858 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h53858 X0 X1 X1 X1 X1]
  have l5 : ∀ sK1 X1 X2 X3 X4 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK1 X1 X2 X3 X4]
  have l6 : ∀ sK1 X1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X1 X0 sK3 sK0
    conv => enter [1]; rw [l5 sK1 X1 sK0 X0 sK3]
    conv => enter [1, 2]; rw [l2 sK0 X0 sK3]
  have l7 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l3 sK2 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y y z w]

theorem Equation43_4512_53858_implies_Equation53810 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53810 G := by
  have l0 : ∀ X0 X1 X2 X3 X5 X6 X7 X8 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X5 ◇ (X6 ◇ (X7 ◇ X8))) := by
    intro X0 X1 X2 X3 X5 X6 X7 X8
    conv => enter [1]; rw [← h53858 X0 X0 X1 X2 X3]
    conv => enter [1]; rw [h53858 X0 X5 X6 X7 X8]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l2 : ∀ sK0 X1 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK0 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK0 X1 X2 X3 X4]
  have l3 : ∀ X0 X1 X2 X3 sK1 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK1 ◇ sK1) ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X3 sK1 X4 X5
    conv => enter [1]; rw [l0 X0 X1 X2 X3 sK1 sK1 X4 X5]
    conv => enter [1]; rw [h4512 sK1 sK1 (X4 ◇ X5)]
  have l4 : ∀ sK0 sK1 X4 X5 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (X4 ◇ X5)) := by
    intro sK0 sK1 X4 X5
    conv => enter [1]; rw [l2 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK1 X4 X5]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation43_4512_53858_implies_Equation53840 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53840 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 X3 X5 X6 X7 X8 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X5 ◇ (X6 ◇ (X7 ◇ X8))) := by
    intro X0 X1 X2 X3 X5 X6 X7 X8
    conv => enter [1]; rw [← h53858 X0 X0 X1 X2 X3]
    conv => enter [1]; rw [h53858 X0 X5 X6 X7 X8]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l3 : ∀ sK0 X1 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK0 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK0 X1 X2 X3 X4]
  have l4 : ∀ X1 X2 X3 X4 X5 sK2 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X4))) = (X5 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X1 X2 X3 X4 X5 sK2 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l5 : ∀ sK0 X5 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X5 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 X5 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK0 sK0 X5 sK2 X0]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) X0]
  intro x y z
  conv => enter [1]; rw [l6 x y y z]

theorem Equation43_4512_53858_implies_Equation53808 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53808 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53858 X0 sK0 X1 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53858 X0 sK0 X1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53858 X0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1, 2]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK0 X1]
  have l11 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK0 X1]
  have l12 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l10 sK0 sK1 X1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53858 sK0 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l17 sK0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l18 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l21 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1, 2]; rw [← l24 sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]

theorem Equation43_4512_53858_implies_Equation53816 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53816 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53858 X0 X1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK1 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l7 sK1 X1 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK0]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l13 y x]

theorem Equation43_4512_53858_implies_Equation53836 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53836 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK1 X0]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [← l5 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l7 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1]
  have l12 : ∀ sK1 X1 X2 X3 X4 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK1 X1 X2 X3 X4]
  have l13 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X0) X1]
  have l14 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l13 sK1 X1 X0]
    conv => enter [1]; rw [← l1 X0 X1 (X0 ◇ X0)]
  have l15 : ∀ sK1 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X1
    conv => enter [1]; rw [l12 sK1 sK1 X1 sK1 sK1]
    conv => enter [1]; rw [← l14 sK1 X1 sK1]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 X1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1, 1]; rw [l3 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation43_4512_53858_implies_Equation53837 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53837 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l4 : ∀ sK0 X1 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK0 X1 X2 X3 X4
    conv => enter [1]; rw [h53858 sK0 X1 X2 X3 X4]
  have l5 : ∀ sK0 X1 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 X1 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l1 sK1 X0 sK2]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X0 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y y z]

@[equational_result]
theorem Equation53858_implies_Equation4276 (G : Type*) [Magma G] (h53858 : Equation53858 G) : Equation4276 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation53858_implies_Equation53807 (G : Type*) [Magma G] (h53858 : Equation53858 G) : Equation53807 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53858 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h53858 X1 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53858 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 X1 sK0]
  intro x
  conv => enter [1]; rw [l2 x x]

theorem Equation43_4512_53841_implies_Equation53811 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53811 G := by
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
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h53841 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h53841 X1 X2 X2 X2]
    conv => enter [1, 2]; rw [h53841 X2 X0 sK0 sK0]
  have l6 : ∀ sK0 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← h53841 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X2 X0 sK0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l6 sK0 X2 sK0]
    conv => enter [1, 2]; rw [← h53841 sK0 sK0 sK0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53841 sK0 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53841 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h53841 sK0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l15 x x y z]

theorem Equation43_4512_53841_implies_Equation53817 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53817 G := by
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
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h53841 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h53841 X1 X2 X2 X2]
    conv => enter [1, 2]; rw [h53841 X2 X0 sK0 sK0]
  have l8 : ∀ sK0 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← h53841 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X2 X0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 X2 sK0]
    conv => enter [1, 2]; rw [← h53841 sK0 sK0 sK0 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 X0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53841 sK0 sK0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53841 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h53841 sK0 X1 X2 X3]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l17 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l4 sK1 X0 sK2]
  have l19 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l5 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x x y z]

theorem Equation43_4512_53841_implies_Equation53810 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53810 G := by
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
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53841 sK0 X0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h53841 sK0 X0 sK0 sK0]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53841 X0 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l7 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 X0 X0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← h53841 sK1 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h53841 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 sK0 X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation43_4512_53841_implies_Equation53840 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53840 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X2 X3 X4 X0 sK0 : G, (X2 ◇ (X2 ◇ (X3 ◇ X4))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X3 X4 X0 sK0
    conv => enter [1]; rw [← h53841 X2 X2 X3 X4]
    conv => enter [1]; rw [h53841 X2 X0 sK0 sK0]
  have l4 : ∀ X2 X0 sK0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X2 X0 sK0 X1
    conv => enter [1, 2]; rw [← h53841 X1 X0 sK0 sK0]
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1) X2]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53841 sK0 X0 sK0 sK0]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← h53841 sK2 sK0 sK0 sK0]
  have l7 : ∀ X2 X0 sK0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X2 X0 sK0 X1
    conv => enter [1]; rw [l4 X2 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ sK2 X2 X3 X4 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK2 X2 X3 X4
    conv => enter [1]; rw [h53841 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← l3 X2 X3 X4 sK2 sK2]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK2]
  have l10 : ∀ X2 sK2 X1 : G, (X2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X2 sK2 X1
    conv => enter [1, 2]; rw [h53841 sK2 X2 X2 X2]
    conv => enter [1]; rw [l7 X2 X2 X2 X1]
  have l11 : ∀ sK2 X2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X2
    conv => enter [1]; rw [l8 sK2 sK2 sK2 X2]
    conv => enter [1]; rw [← l10 X2 sK2 sK2]
  have l12 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l11 sK0 X2]
  have l13 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2) X0]
  have l14 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l2 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l9 sK2 sK0]
  have l15 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l14 sK2 X0 sK0]
  have l16 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l13 sK0 X0 sK2]
    conv => enter [1]; rw [← l1 sK2 X0 (sK2 ◇ sK2)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 X0 sK0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53841 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h53841 sK0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l19 x y z z]

theorem Equation43_4512_53841_implies_Equation53808 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53808 G := by
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
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h53841 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h53841 X1 X2 X2 X2]
    conv => enter [1, 2]; rw [h53841 X2 X0 sK0 sK0]
  have l7 : ∀ sK0 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← h53841 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X2 X0 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 X2 sK0]
    conv => enter [1, 2]; rw [← h53841 sK0 sK0 sK0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 X0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53841 sK0 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_53841_implies_Equation53816 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53816 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 X0 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h53841 (sK1 ◇ sK1) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h53841 X1 X2 X2 X2]
    conv => enter [1, 2]; rw [h53841 X2 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53841 sK0 X0 sK0 sK0]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53841 X0 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0]
  have l10 : ∀ sK0 sK1 X2 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X2 X0
    conv => enter [1]; rw [← l8 sK0 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 X2 X0 sK0]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← h53841 sK1 sK0 sK0 sK0]
  have l13 : ∀ sK0 sK1 X2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l10 sK0 sK1 X2 sK0]
    conv => enter [1, 2]; rw [← h53841 sK1 sK0 sK0 sK0]
  have l14 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l11 X0 sK0 sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h53841 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l14 sK1 sK1 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation43_4512_53841_implies_Equation53836 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53836 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h53841 X1 X2 X2 X2]
    conv => enter [1, 2]; rw [h53841 X2 X0 sK0 sK0]
  have l9 : ∀ X2 X3 X4 X0 sK0 : G, (X2 ◇ (X2 ◇ (X3 ◇ X4))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X3 X4 X0 sK0
    conv => enter [1]; rw [← h53841 X2 X2 X3 X4]
    conv => enter [1]; rw [h53841 X2 X0 sK0 sK0]
  have l10 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [← h53841 (X1 ◇ X2) X0 sK0 sK0]
    conv => enter [1]; rw [l0 X1 X2 ((X1 ◇ X2) ◇ (X1 ◇ X2))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53841 sK0 X0 sK0 sK0]
  have l12 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h53841 sK1 X0 sK0 sK0]
  have l13 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h53841 (sK1 ◇ sK1) X0 sK0 sK0]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53841 X0 (sK1 ◇ sK1) sK0 sK0]
    conv => enter [1]; rw [l7 sK1 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l13 sK1 sK1 sK1]
    conv => enter [1]; rw [← l12 sK1 sK1 sK1]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0]
  have l17 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l10 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [l5 X1 (X1 ◇ X2) X1 X2]
  have l18 : ∀ sK1 X2 X3 X4 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 X2 X3 X4
    conv => enter [1]; rw [l13 sK1 sK1 sK1]
    conv => enter [1]; rw [← l9 X2 X3 X4 sK1 sK1]
  have l19 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l8 X1 X2 X1 X1]
    conv => enter [1, 2]; rw [← l13 sK1 X1 X1]
  have l20 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← h53841 sK1 sK0 sK0 sK0]
  have l22 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l17 X0 sK0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [h43 (X1 ◇ X2) X2]
  have l23 : ∀ sK0 sK1 X2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [← l14 sK0 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 X2 sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l20 sK1]
  have l25 : ∀ X0 sK0 X2 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 X2 sK1
    conv => enter [1]; rw [l22 X0 sK0 X2 X0]
    conv => enter [1, 2]; rw [← l18 sK1 X0 X2 (X0 ◇ X2)]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 sK1]
  have l27 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l25 X0 sK0 X0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 X0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53841 sK1 sK1 sK0 sK0]
    conv => enter [1]; rw [l27 sK1 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l28 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l32 x y]

theorem Equation43_4512_53841_implies_Equation53837 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53837 G := by
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
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h53841 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h53841 X1 X2 X2 X2]
    conv => enter [1, 2]; rw [h53841 X2 X0 sK0 sK0]
  have l6 : ∀ sK0 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← h53841 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X2 X0 sK0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l6 sK0 X2 sK0]
    conv => enter [1, 2]; rw [← h53841 sK0 sK0 sK0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53841 sK0 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53841 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h53841 sK0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l15 x y y z]

@[equational_result]
theorem Equation53841_implies_Equation4276 (G : Type*) [Magma G] (h53841 : Equation53841 G) : Equation4276 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53841 sK1 sK1 sK0 sK0]
    conv => enter [1]; rw [← h53841 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4512_53841_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53807 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53841 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x x]

end CommutativeSemigroup5
