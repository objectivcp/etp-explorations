import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41750_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41750 : Equation41750 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h41750 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41750 X0 (X1 ◇ X1) X1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41750 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41750 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41750 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 (X0 ◇ X0)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41750 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X1))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK1) ◇ (X0 ◇ X0))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ sK1) sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41750 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l16 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l15 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [l14 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h41750 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l23 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41750 X0 sK0 sK0]
    conv => enter [1]; rw [← l24 X0 sK0]
  have l26 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [l25 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l27 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 sK0 X1]
    conv => enter [1]; rw [l26 X0 sK0 X1]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41750 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ (X1 ◇ X1))]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1]; rw [← l28 sK0 X0 sK0]
  have l30 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41750 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l18 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l30 X0 sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2]; rw [l31 X0 sK0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← l27 sK0 sK0 (X0 ◇ sK0)]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 (X0 ◇ sK0)]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41750 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1, 2]; rw [← l25 X0 sK0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← l38 sK0 X0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l40 x y]

@[equational_result]
theorem Equation38_implies_Equation41767 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41767 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation41767_implies_Equation38 (G : Type*) [Magma G] (h41767 : Equation41767 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41767 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41767 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41751 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41751 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41751_implies_Equation38 (G : Type*) [Magma G] (h41751 : Equation41751 G) : Equation38 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41751 X2 X0 X0 (X1 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41751 X0 X1 X2 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = (X2 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [l0 X2 X0 X2]
    conv => enter [1]; rw [← l1 X2 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation38_implies_Equation41759 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41759 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h38 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [← l1 x z y w]
  conv => enter [1]; rw [l0 x z y w]

theorem Equation4512_41759_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41759 : Equation41759 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h41759 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41759 sK0 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 sK1 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h41759 (sK0 ◇ sK0) X0 sK1 X1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 (X0 ◇ X1)]
  have l5 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41759 sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l6 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1 X2]
  have l7 : ∀ sK0 X0 sK1 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l4 sK0 X0 sK1 X1]
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK1) ◇ (X0 ◇ X1))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK1 (sK0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 sK1 X0 sK0 sK0]
  have l9 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK1) (X0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ X0) sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 sK0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41759 sK0 X0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 (X0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x x y]

@[equational_result]
theorem Equation38_implies_Equation41768 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41768 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1
    conv => enter [1]; rw [← h38 sK2 (sK3 ◇ (sK4 ◇ sK1))]
    conv => enter [1]; rw [h38 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 (sK3 ◇ (sK4 ◇ sK1))]
    conv => enter [1]; rw [h38 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l1 x z w u y]
  conv => enter [1]; rw [l0 x z w u]

@[equational_result]
theorem Equation41768_implies_Equation38 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation39_implies_Equation45 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation45 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation45_implies_Equation39 (G : Type*) [Magma G] (h45 : Equation45 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [h45 x x y]

theorem Equation39_4512_implies_Equation339 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation339_implies_Equation39 (G : Type*) [Magma G] (h339 : Equation339 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h339 sK1 sK0 sK0]
    conv => enter [1]; rw [← h339 X0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation347 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation347 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK1) sK2]
    conv => enter [1, 1]; rw [h39 sK1 sK0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation347_implies_Equation39 (G : Type*) [Magma G] (h347 : Equation347 G) : Equation39 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h347 sK0 sK0 sK0]
    conv => enter [1]; rw [← h347 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation355 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation355 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK2) sK3]
    conv => enter [1, 1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation355_implies_Equation39 (G : Type*) [Magma G] (h355 : Equation355 G) : Equation39 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h355 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h355 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation336 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation336 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation336_implies_Equation39 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h336 sK0 sK0]
    conv => enter [1]; rw [← h336 X0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation351 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation351 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0 sK2]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l3 z y z]

@[equational_result]
theorem Equation351_implies_Equation39 (G : Type*) [Magma G] (h351 : Equation351 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h351 sK1 sK0 sK0]
    conv => enter [1]; rw [← h351 X0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3349 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3349 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3349_4512_implies_Equation39 (G : Type*) [Magma G] (h3349 : Equation3349 G) (h4512 : Equation4512 G) : Equation39 G := by
  have l0 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 1]; rw [h3349 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK1 ◇ sK0)) X1]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h3349 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h3349 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
  have l4 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l0 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK0) X1]
  have l5 : ∀ X0 X3 X1 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X3 X1
    conv => enter [1]; rw [l1 X0 X3 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X3 X0]
  have l6 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← l4 X0 sK0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 X0 sK1 X1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 ((sK1 ◇ sK0) ◇ X1) X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 X1 (X0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l9 x x y]

theorem Equation39_4512_implies_Equation3367 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3367 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK1) sK2]
    conv => enter [1, 1]; rw [h39 sK1 sK0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation3367_implies_Equation39 (G : Type*) [Magma G] (h3367 : Equation3367 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3367 X0 X1 X0]
    conv => enter [1]; rw [← h3367 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3371 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3371 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK2 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation3371_implies_Equation39 (G : Type*) [Magma G] (h3371 : Equation3371 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3371 X0 X1 X0]
    conv => enter [1]; rw [← h3371 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3375 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3375 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK2) sK3]
    conv => enter [1, 1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l1 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK3 sK0 sK2 sK1]
  have l7 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK2 sK3]
    conv => enter [1, 2]; rw [l6 sK3 sK2 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l7 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

@[equational_result]
theorem Equation3375_implies_Equation39 (G : Type*) [Magma G] (h3375 : Equation3375 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3375 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3375 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3384 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3384 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3384_4512_implies_Equation39 (G : Type*) [Magma G] (h3384 : Equation3384 G) (h4512 : Equation4512 G) : Equation39 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3384 X1 (X0 ◇ X0) X2]
    conv => enter [1, 2]; rw [← h3384 (X0 ◇ X0) X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3384 X0 X0 X0]
    conv => enter [1]; rw [← l1 X1 X0 X0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3384 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation39_4512_implies_Equation3392 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3392 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK0]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK0 sK2 X0 : G, (sK0 ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l7 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l6 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK3 sK1 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation3392_implies_Equation39 (G : Type*) [Magma G] (h3392 : Equation3392 G) : Equation39 G := by
  have l0 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h3392 X1 (sK0 ◇ sK0) X2 X0]
    conv => enter [1, 2]; rw [← h3392 X0 sK0 X1 sK0]
  have l1 : ∀ X2 sK0 X3 X0 X1 : G, (X2 ◇ sK0) = (X3 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK0 X3 X0 X1
    conv => enter [1]; rw [h3392 X2 sK0 X3 sK0]
    conv => enter [1, 2]; rw [l0 X2 sK0 X0 X1]
  have l2 : ∀ X0 sK0 X2 : G, (X0 ◇ sK0) = (X2 ◇ sK0) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l1 X0 sK0 X0 X2 X0]
    conv => enter [1]; rw [← h3392 X2 sK0 X0 X0]
  intro x y
  conv => enter [1]; rw [l2 x x y]

theorem Equation39_4512_implies_Equation3401 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3401 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l6 sK2 sK1 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation3401_implies_Equation39 (G : Type*) [Magma G] (h3401 : Equation3401 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3401 X0 X1 X0]
    conv => enter [1]; rw [← h3401 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3405 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3405 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK2 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation3405_implies_Equation39 (G : Type*) [Magma G] (h3405 : Equation3405 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3405 X0 X1 X0]
    conv => enter [1]; rw [← h3405 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3409 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3409 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l6 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  have l8 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l3 sK2 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l7 sK3 sK2 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation3409_implies_Equation39 (G : Type*) [Magma G] (h3409 : Equation3409 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3409 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3409 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3436 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3436 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [h39 sK2 sK1]
    conv => enter [1, 2]; rw [h39 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  have l6 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK2 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l5 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l6 sK3 sK0 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

@[equational_result]
theorem Equation3436_implies_Equation39 (G : Type*) [Magma G] (h3436 : Equation3436 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3436 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3436 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3441 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3441 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK3]
  have l1 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [l0 sK3 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK0 sK3 sK2 X0 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 X0 sK1
    conv => enter [1]; rw [l1 sK0 sK3 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK0 sK3 sK2 sK1]
  have l7 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK2 sK0 sK3]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l7 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

@[equational_result]
theorem Equation3441_implies_Equation39 (G : Type*) [Magma G] (h3441 : Equation3441 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3441 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3441 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3446 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3446 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l6 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l5 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l6 sK3 sK0 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

@[equational_result]
theorem Equation3446_implies_Equation39 (G : Type*) [Magma G] (h3446 : Equation3446 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3446 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3446 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3451 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3451 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ sK3) sK1]
    conv => enter [1, 1]; rw [l0 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK1 sK0 sK3 X0 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [h39 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 sK2]
  have l6 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK1 sK0 sK3 sK2]
  have l7 : ∀ sK4 sK1 sK0 sK3 sK2 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ sK3)) sK4]
    conv => enter [1, 1]; rw [← l6 sK2 sK3 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK2 sK3 sK1 sK0]
  have l8 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l3 sK1 sK0 sK3 (sK1 ◇ sK3) sK1]
    conv => enter [1]; rw [← l7 sK4 sK1 sK0 sK3 sK1]
  have l9 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l9 x y z w u]

@[equational_result]
theorem Equation3451_implies_Equation39 (G : Type*) [Magma G] (h3451 : Equation3451 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3451 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3451 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3356 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3356 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l6 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation3356_implies_Equation39 (G : Type*) [Magma G] (h3356 : Equation3356 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3356 sK0 sK0]
    conv => enter [1]; rw [← h3356 X0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation3422 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3422 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0 sK2]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l4 z y]

@[equational_result]
theorem Equation3422_implies_Equation39 (G : Type*) [Magma G] (h3422 : Equation3422 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3422 X0 X1 X0]
    conv => enter [1]; rw [← h3422 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3359 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3359 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK0) sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l6 z y]

@[equational_result]
theorem Equation3359_implies_Equation39 (G : Type*) [Magma G] (h3359 : Equation3359 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3359 X0 X1 X0]
    conv => enter [1]; rw [← h3359 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation3418 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3418 G := by
  have l0 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h39 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← h39 y x]
  conv => enter [1]; rw [l2 y z]

@[equational_result]
theorem Equation3418_implies_Equation39 (G : Type*) [Magma G] (h3418 : Equation3418 G) : Equation39 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1]; rw [h3418 sK0 sK0 sK0]
    conv => enter [1]; rw [← h3418 X1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation3426 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3426 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0 sK2]
  have l4 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [l4 w y z]

@[equational_result]
theorem Equation3426_implies_Equation39 (G : Type*) [Magma G] (h3426 : Equation3426 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h3426 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3426 X4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41890 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41890 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0 sK2]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41890_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41890 : Equation41890 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41890 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41890 X1 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41890 X0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41890 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41890 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X1 ◇ sK0)))]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 X0 (X0 ◇ sK0)]
  have l8 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l3 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l8 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l2 X1 X0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l7 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41890 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l1 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41890 X0 (X1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 X1]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0]
    conv => enter [1]; rw [l9 (sK1 ◇ sK0) sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0]
  have l19 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l12 sK0 X0 X0]
    conv => enter [1]; rw [← l16 X0 X1 sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l17 sK1 sK0 X0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l19 X0 sK0 (sK1 ◇ sK0)]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l21 sK1 sK0 X0]
    conv => enter [1]; rw [← l19 X0 sK0 sK0]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41890 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 X0]
    conv => enter [1]; rw [← l23 X0 sK0]
  have l25 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41890 X1 sK0 (X1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l22 X1 sK0 X0]
  have l26 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l25 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l19 X0 sK0 X1]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l19 X0 sK0 X1]
    conv => enter [1]; rw [← l26 X1 sK0 X0]
  have l28 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l19 X0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l29 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 sK0 X1]
  intro x y
  conv => enter [1]; rw [l29 x y]

theorem Equation39_4512_implies_Equation41900 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41900 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41900_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41900 : Equation41900 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41900 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41900 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← h41900 (sK1 ◇ sK0) sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h41900 (sK0 ◇ sK0) sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation39_4512_implies_Equation41908 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41908 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK1) sK2]
    conv => enter [1, 1]; rw [h39 sK1 sK0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_41908_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41908 : Equation41908 G) : Equation39 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41908 X2 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h41908 (X0 ◇ (X1 ◇ X1)) X1 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41908 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41908 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l3 X3 X0 X1 X0]
    conv => enter [1]; rw [← l1 X0 X3 X1 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2]; rw [l5 X1 X1 (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1]; rw [l5 X0 X2 ((X0 ◇ (X1 ◇ X1)) ◇ X1)]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← l9 X2 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [l5 X2 X0 (X1 ◇ X1)]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X1]
  intro x y
  conv => enter [1]; rw [l12 x x y]

theorem Equation39_4512_implies_Equation41912 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41912 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK2 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK1 sK0]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41912_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41912 : Equation41912 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41912 X1 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41912 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41912 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41912 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ sK0))]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h41912 X0 sK0 X1]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l1 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l8 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l8 X1 sK0 X0]
    conv => enter [1, 2]; rw [l6 X0 X1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l0 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41912 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l15 sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l24 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41912 X0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l22 sK1 sK0]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l24 X0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0 (X0 ◇ sK0)]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41912 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l20 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l27 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41912 X1 ((sK0 ◇ sK0) ◇ X0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l20 sK0 X0]
  have l28 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l27 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) X0 sK0]
  have l30 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l28 X1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l20 sK0 X0]
  have l31 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l30 X1 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l32 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l31 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l2 X1 X0 sK0]
  have l33 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l32 X1 sK0 X0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l35 sK1 sK0]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l38 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l37 X0 X1 sK0]
    conv => enter [1]; rw [← l29 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41912 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l23 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1]; rw [← l38 X0 X0 sK0]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l41 sK0 X0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1, 2]; rw [l44 sK1 sK0]
  have l46 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41912 X0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l44 sK1 sK0]
  have l47 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l46 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l33 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l33 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
  have l49 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l47 X0 sK0 sK1]
    conv => enter [1]; rw [← l9 X0 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l50 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l49 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l48 sK0 X0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l51 sK1 sK0]
  have l53 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1, 2]; rw [← l50 X0 sK0]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l56 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41912 X0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l54 sK1 sK0]
  have l57 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l56 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l54 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1, 2]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l50 (sK1 ◇ sK0) sK0]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1, 2]; rw [l55 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← l57 (sK1 ◇ sK0) sK1 sK0]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l62 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l60 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l64 x y]

theorem Equation39_4512_implies_Equation41916 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41916 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ sK2) sK3]
    conv => enter [1, 1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l1 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK3 sK0 sK2 sK1]
  have l7 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l7 sK3 sK0 sK2 sK1]
  have l9 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK2 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

theorem Equation4512_41916_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41916 : Equation41916 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41916 X1 (sK0 ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [h41916 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l4 : ∀ sK1 X1 sK0 X0 : G, (sK1 ◇ X1) = (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 sK0 X0
    conv => enter [1]; rw [h41916 sK1 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l1 sK1 sK0 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [h41916 (X0 ◇ X1) X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l6 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ (X1 ◇ X4)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l5 X0 X1 X4 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l7 : ∀ sK1 X1 sK0 : G, (sK1 ◇ X1) = ((sK1 ◇ sK0) ◇ X1) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l4 sK1 X1 sK0 sK1]
    conv => enter [1]; rw [← h41916 (sK1 ◇ sK0) X1 sK0 sK1]
  have l8 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l2 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l9 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [← l6 X4 X0 X1 X0 X0]
    conv => enter [1]; rw [← l3 X0 X4 X1 X0 X0]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l8 X1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l3 X1 X0 X1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l9 sK0 X1 X0]
    conv => enter [1]; rw [l10 sK0 X1 X0]
  have l12 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l9 X1 sK0 X0]
    conv => enter [1]; rw [← l11 sK0 X0 X1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation39_4512_implies_Equation41962 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41962 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK0 sK1 X0 sK2]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 1]; rw [← l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l9 sK2 sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]
  conv => enter [1]; rw [l6 z x y y]

theorem Equation4512_41962_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41962 : Equation41962 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41962 X1 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h41962 (X0 ◇ X0) X0 X1]
  have l2 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41962 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (X0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41962 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X0 sK0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41962 X0 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41962 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← h41962 X1 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [l6 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1]
    conv => enter [1]; rw [← l3 sK0 (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l12 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h41962 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 X1]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X1]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41962 X0 sK0 X0]
    conv => enter [1]; rw [← l13 X0 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l15 X0 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation39_4512_implies_Equation41966 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41966 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41966_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41966 : Equation41966 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41966 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41966 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41966 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l13 X0 sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41966 (sK0 ◇ sK0) sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41966 (sK1 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l11 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41966 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK1 sK0]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [l26 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l26 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l31 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41966 X0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l33 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l32 sK0 X0 sK1]
  have l34 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l31 X0 sK1 sK0]
    conv => enter [1]; rw [l21 sK1 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l35 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l34 X0 sK1 sK0]
    conv => enter [1]; rw [← l33 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l36 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← l35 X0 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [← l36 (sK1 ◇ sK0) sK0 sK1]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l36 sK0 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1, 2]; rw [l19 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0 sK0]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [← l36 (sK0 ◇ sK0) sK0 sK1]
  have l45 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [← l43 sK0]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l38 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l46 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l47 x y]

theorem Equation39_4512_implies_Equation41970 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41970 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK1 sK0 sK2 X0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK3 sK1 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l3 sK3 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
  have l7 : ∀ sK3 sK1 sK0 sK2 X0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK2 X0 sK3]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l10 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l4 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l10 sK3 sK1 sK0 sK2]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]
  conv => enter [1]; rw [l7 z x w y y]

theorem Equation4512_41970_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41970 : Equation41970 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h41970 sK1 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0 X0]
  have l2 : ∀ X0 X1 X3 X4 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h41970 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41970 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ X0 X1 X3 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l2 X0 X1 X3 X0 X0]
    conv => enter [1]; rw [← l3 X1 X3 X0 X0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41970 (sK1 ◇ sK0) X0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 X0 sK1 sK0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1, 1]; rw [l5 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation39_4512_implies_Equation41979 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41979 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK1 X0 sK2]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 1]; rw [← l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l9 sK2 sK1 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]
  conv => enter [1]; rw [l6 z y y]

@[equational_result]
theorem Equation41979_implies_Equation39 (G : Type*) [Magma G] (h41979 : Equation41979 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41979 X0 X1 X0]
    conv => enter [1]; rw [← h41979 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41983 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41983 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK2 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation41983_implies_Equation39 (G : Type*) [Magma G] (h41983 : Equation41983 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41983 X0 X1 X0]
    conv => enter [1]; rw [← h41983 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41987 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41987 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK2 sK0 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK2 sK0 X0
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [h39 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l4 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK3 sK2 sK0 X0 X1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK2 sK0 X0 X1
    conv => enter [1]; rw [l3 sK3 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK2))]
  have l7 : ∀ sK3 sK2 sK0 X0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK3 sK2 sK0 X0 sK3]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l10 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0]
  have l11 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l4 sK2 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l10 sK3 sK2 sK0 sK2]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]
  conv => enter [1]; rw [l7 z y w y]

@[equational_result]
theorem Equation41987_implies_Equation39 (G : Type*) [Magma G] (h41987 : Equation41987 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41987 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41987 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41996 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41996 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l7 sK2 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation41996_implies_Equation39 (G : Type*) [Magma G] (h41996 : Equation41996 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41996 X0 X1 X0]
    conv => enter [1]; rw [← h41996 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42000 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42000 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK2 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK1]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l8 sK2 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation42000_implies_Equation39 (G : Type*) [Magma G] (h42000 : Equation42000 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42000 X0 X1 X0]
    conv => enter [1]; rw [← h42000 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42004 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42004 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK3 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK3 sK3]
    conv => enter [1, 2]; rw [l6 sK3 sK2 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l7 sK3 sK0 sK2]
  have l9 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK2 sK3]
    conv => enter [1, 2]; rw [l8 sK3 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42004_implies_Equation39 (G : Type*) [Magma G] (h42004 : Equation42004 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42004 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42004 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42014 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42014 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [h39 sK2 sK1]
    conv => enter [1, 2]; rw [h39 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK2 ◇ sK2)) sK3]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK3 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK3 sK0 sK2 X0 sK3]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  have l9 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK2 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l9 sK3 sK0 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]
  conv => enter [1]; rw [l6 z w y y]

@[equational_result]
theorem Equation42014_implies_Equation39 (G : Type*) [Magma G] (h42014 : Equation42014 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42014 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42014 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42019 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42019 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK3]
  have l1 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [l0 sK3 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK0 sK3 sK2 X0 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 X0 sK1
    conv => enter [1]; rw [l1 sK0 sK3 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK0 sK3 sK2 sK1]
  have l7 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK2 sK0 sK3]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l7 sK0 sK3 sK2]
  have l9 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK2 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l9 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42019_implies_Equation39 (G : Type*) [Magma G] (h42019 : Equation42019 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42019 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42019 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42024 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42024 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK0 ◇ sK2)) X0]
  have l4 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK3 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK2))]
  have l7 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l6 sK3 sK0 sK2 X0 sK3]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l10 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0]
  have l11 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l4 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l10 sK3 sK0 sK2 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]
  conv => enter [1]; rw [l7 z w y y]

@[equational_result]
theorem Equation42024_implies_Equation39 (G : Type*) [Magma G] (h42024 : Equation42024 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42024 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42024 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42029 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42029 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ sK3) sK1]
    conv => enter [1, 1]; rw [l0 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK1 sK0 sK3 X0 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [h39 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK4 sK1 sK0 sK3 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ sK3)) sK4]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK0 ◇ sK3)) X0]
  have l5 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l6 : ∀ sK4 sK1 sK0 sK3 X0 X1 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK3))]
  have l7 : ∀ sK4 sK1 sK0 sK3 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [l6 sK4 sK1 sK0 sK3 X0 sK4]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l5 sK2 sK3 X0 sK2]
  have l9 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK1 sK0 sK3 sK2]
  have l10 : ∀ sK4 sK1 sK0 sK3 sK2 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ sK3)) sK4]
    conv => enter [1, 1]; rw [← l9 sK2 sK3 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK2 sK3 sK1 sK0]
  have l11 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l3 sK1 sK0 sK3 (sK1 ◇ sK3) sK1]
    conv => enter [1]; rw [← l10 sK4 sK1 sK0 sK3 sK1]
  have l12 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]
  conv => enter [1]; rw [l7 z w u y y]

@[equational_result]
theorem Equation42029_implies_Equation39 (G : Type*) [Magma G] (h42029 : Equation42029 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42029 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42029 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42039 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42039 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h39 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1, 2]; rw [h39 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_42039_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42039 : Equation42039 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42039 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42039 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42039 X0 X1 X0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 (sK1 ◇ sK0) sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK0 sK1]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK0 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation39_4512_implies_Equation42043 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42043 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0 sK2]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_42043_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42043 : Equation42043 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42043 X1 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42043 X2 (X0 ◇ (X0 ◇ (X3 ◇ X1))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h42043 X0 X1 X3]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42043 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42043 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42043 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42043 X2 (X0 ◇ (X2 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h42043 X0 X1 X2]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42043 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42043 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X1)))]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l9 sK0 X0 (sK0 ◇ sK0)]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l2 X1 sK0 X0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l14 X1 sK0 X0]
    conv => enter [1]; rw [← l11 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42043 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l18 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l1 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l19 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0 X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l15 (sK0 ◇ sK0) sK0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l19 sK1 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l12 (sK0 ◇ sK0) sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [← l23 sK0]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42043 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42043 X0 sK0 sK0]
    conv => enter [1]; rw [← l26 X0 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l28 sK0 X0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l31 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42043 X1 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l20 sK0 X0]
  have l32 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK0 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42043 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l31 X1 sK0 X0]
  have l33 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h42043 (sK0 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l34 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l33 sK0 X0 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l35 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l34 sK0 X0 sK1]
    conv => enter [1]; rw [← l29 sK0 ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l36 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l35 sK0 X0 sK1]
    conv => enter [1]; rw [← l15 (sK1 ◇ sK0) sK0 X0]
  have l37 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l36 sK0 X0 sK1]
    conv => enter [1]; rw [← l32 (sK1 ◇ sK0) X0 sK0]
  have l38 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l37 sK0 X0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l39 x y]

theorem Equation39_4512_implies_Equation42047 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42047 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK0]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK0 sK2 X0 : G, (sK0 ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
  have l9 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK3 sK1 sK0 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_42047_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42047 : Equation42047 G) : Equation39 G := by
  have l0 : ∀ X1 sK0 X0 X2 sK1 : G, (X1 ◇ (sK0 ◇ X0)) = (X2 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0 X2 sK1
    conv => enter [1]; rw [h42047 X1 (sK0 ◇ X0) X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42047 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ (X4 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42047 X0 X1 X0 X0]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK0 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42047 X1 X0 X1 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l0 X1 sK0 X0 X1 X1]
  have l4 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l3 X1 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x x y]

theorem Equation39_4512_implies_Equation42056 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42056 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK2]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_42056_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42056 : Equation42056 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42056 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h42056 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42056 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42056 X0 X1 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h42056 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X0 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) (sK0 ◇ sK0) sK1]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42056 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h42056 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation39_4512_implies_Equation42060 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42060 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK2 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_42060_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42060 : Equation42060 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h42060 X2 (X0 ◇ (X1 ◇ (X3 ◇ X1))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h42060 X0 X1 X3]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42060 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42060 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42060 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42060 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l1 X2 X0 X1 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X3 ◇ X1)) (X0 ◇ X1)]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l8 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X3 ◇ X1) (X0 ◇ X1)]
  have l10 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 X1 (X0 ◇ X1)]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l10 X2 X0 X1 X3]
    conv => enter [1, 2, 2]; rw [← l6 X1 X3 X1 X0]
  have l12 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h42060 X2 X1 X3]
    conv => enter [1]; rw [← l11 X2 X0 X1 X3]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42060 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l16 X0 sK0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42060 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 sK0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l19 X0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← l17 (sK0 ◇ sK0) sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l23 sK0 (sK1 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation39_4512_implies_Equation42064 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42064 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 sK1]
  have l9 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l9 sK3 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK2 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_42064_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42064 : Equation42064 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ sK0) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h42064 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42064 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X4 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42064 X0 X1 X0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) (X0 ◇ sK0) sK1]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← l2 X0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x x y]

theorem Equation39_4512_implies_Equation42073 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42073 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_42073_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42073 : Equation42073 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h42073 sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (X0 ◇ X0)]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42073 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (X1 ◇ X1)))]
  have l3 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l1 sK1 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42073 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l3 sK1 (sK0 ◇ (X0 ◇ X0)) sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ X0)]
  have l6 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (X0 ◇ X0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42073 ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK0 ((sK1 ◇ sK0) ◇ (X0 ◇ X0))]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ X0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [← l6 sK1 sK0 X0]
    conv => enter [1, 1]; rw [← l5 sK1 sK0 X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) X0 X0]
    conv => enter [1]; rw [← l7 sK1 sK0 X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [l8 sK1 sK0 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l5 sK1 sK0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l13 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h42073 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l9 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h42073 X0 X1 (sK1 ◇ sK0)]
  have l14 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l13 X0 X0 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation39_4512_implies_Equation42081 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42081 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK0]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK3 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK0 sK2 X0 : G, (sK0 ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l7 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l7 sK3 sK0 sK2 sK1]
  have l9 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

end Semigroup5
