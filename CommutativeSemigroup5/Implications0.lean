import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

@[equational_result]
theorem Equation2_implies_Equation3 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation11 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation38 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation38 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation56 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation8 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation47 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation311 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation311 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation323 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation323 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation440 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation3414 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3414 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (z ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation411 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3267 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation2_implies_Equation3306 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3306 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4271 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4271 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation308 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation40 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation4268 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4268 G := by
  intro x y
  conv => enter [1, 2, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation307 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation307 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4270 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4270 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation3253 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4284 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4284 G := by
  intro x y
  conv => enter [1, 2, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4276 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation3_implies_Equation8 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

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

theorem Equation3_43_4512_implies_Equation323 (G : Type*) [Magma G] (h3 : Equation3 G) (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

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

@[equational_result]
theorem Equation8_implies_Equation411 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 2]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_43_4512_implies_Equation3306 (G : Type*) [Magma G] (h8 : Equation8 G) (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation3306 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h8 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h8 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h8 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation8_implies_Equation3253 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h8 x]

@[equational_result]
theorem Equation11_implies_Equation8 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h11 x x]

@[equational_result]
theorem Equation11_implies_Equation440 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation440 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h11 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation11_43_4512_implies_Equation3414 (G : Type*) [Magma G] (h11 : Equation11 G) (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation3414 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h11 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation11_43_implies_Equation40 (G : Type*) [Magma G] (h11 : Equation11 G) (h43 : Equation43 G) : Equation40 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← h11 X0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h11 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation11_implies_Equation4270 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h11 x x]
  conv => enter [1]; rw [h11 x y]

@[equational_result]
theorem Equation38_implies_Equation311 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ z)]

theorem Equation38_43_implies_Equation323 (G : Type*) [Magma G] (h38 : Equation38 G) (h43 : Equation43 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h38 (sK0 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h38 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [h43 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation38_43_implies_Equation3414 (G : Type*) [Magma G] (h38 : Equation38 G) (h43 : Equation43 G) : Equation3414 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h38 sK0 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 sK0 X0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation38_implies_Equation3267 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [h38 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation38_implies_Equation3306 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3306 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation4271 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ z)]

@[equational_result]
theorem Equation38_implies_Equation308 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ y)]

theorem Equation38_43_implies_Equation40 (G : Type*) [Magma G] (h38 : Equation38 G) (h43 : Equation43 G) : Equation40 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h38 sK0 X0]
    conv => enter [1]; rw [h43 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h38 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation38_implies_Equation4268 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation307 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation4270 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [h38 x (y ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation3253 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation38_implies_Equation4284 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation40_implies_Equation4270 (G : Type*) [Magma G] (h40 : Equation40 G) : Equation4270 G := by
  intro x y
  conv => enter [1, 2]; rw [h40 x y]

theorem Equation38_43_implies_Equation4276 (G : Type*) [Magma G] (h38 : Equation38 G) (h43 : Equation43 G) : Equation4276 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h38 sK0 X0]
    conv => enter [1]; rw [h43 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h38 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← h38 x (x ◇ x)]
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h38 y (y ◇ y)]

@[equational_result]
theorem Equation56_implies_Equation47 (G : Type*) [Magma G] (h56 : Equation56 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h56 x x]

@[equational_result]
theorem Equation307_implies_Equation3253 (G : Type*) [Magma G] (h307 : Equation307 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation43_308_4512_implies_Equation40 (G : Type*) [Magma G] (h43 : Equation43 G) (h308 : Equation308 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h308 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h308 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation308_implies_Equation4268 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h308 x x]
  conv => enter [1]; rw [h308 x y]

@[equational_result]
theorem Equation308_implies_Equation307 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h308 x x]

theorem Equation43_311_implies_Equation3267 (G : Type*) [Magma G] (h43 : Equation43 G) (h311 : Equation311 G) : Equation3267 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [h311 X0 (sK3 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) sK2]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation311_implies_Equation4271 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h311 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h311 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation311_implies_Equation308 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h311 x x y]

@[equational_result]
theorem Equation311_implies_Equation4284 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_311_4512_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h311 : Equation311 G) (h4512 : Equation4512 G) : Equation4276 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h311 X0 sK0 sK0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h311 X0 sK1 sK1]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l0 X0 sK0]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h311 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h311 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 1]; rw [← h311 sK0 sK0 sK0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [l2 sK1 X0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← h311 x x x]
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [h311 y y y]

theorem Equation43_308_4512_implies_Equation4284 (G : Type*) [Magma G] (h43 : Equation43 G) (h308 : Equation308 G) (h4512 : Equation4512 G) : Equation4284 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h308 X1 X0]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h308 sK0 sK1]
    conv => enter [1]; rw [h308 sK0 sK0]
    conv => enter [1, 2]; rw [h308 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← h308 sK0 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h308 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 (sK1 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h43 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h308 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h308 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
    conv => enter [1, 1]; rw [h308 sK0 sK1]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l0 (sK1 ◇ sK1) sK0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h308 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h308 sK0 X0]
    conv => enter [1]; rw [l14 sK0 X0 sK1]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h308 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l16 sK1 sK0 X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h308 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 sK0 X0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)]
    conv => enter [1]; rw [← l21 sK0 sK1 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l23 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation43_308_4512_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h308 : Equation308 G) (h4512 : Equation4512 G) : Equation4276 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h308 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h308 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [← h308 x x]
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h308 y y]

@[equational_result]
theorem Equation323_implies_Equation3306 (G : Type*) [Magma G] (h323 : Equation323 G) : Equation3306 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1, 2]; rw [h323 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation323_implies_Equation307 (G : Type*) [Magma G] (h323 : Equation323 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h323 x x]

theorem Equation43_323_4512_implies_Equation4284 (G : Type*) [Magma G] (h43 : Equation43 G) (h323 : Equation323 G) (h4512 : Equation4512 G) : Equation4284 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h323 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [h43 sK1 X0]
  intro x y
  conv => enter [1]; rw [← h323 x y]
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation440_implies_Equation411 (G : Type*) [Magma G] (h440 : Equation440 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h440 x x]

theorem Equation40_43_4512_implies_Equation3253 (G : Type*) [Magma G] (h40 : Equation40 G) (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h40 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h40 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation43_3267_4512_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h3267 : Equation3267 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3267 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3267 X0 X1 X1 X1]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3267 X1 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = ((X1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3267 X0 X1 sK0 sK0]
    conv => enter [1]; rw [h43 X0 (X1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X1]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l4 X1 sK0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0 X1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation3306_implies_Equation3253 (G : Type*) [Magma G] (h3306 : Equation3306 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3306 x x]

@[equational_result]
theorem Equation3414_implies_Equation3306 (G : Type*) [Magma G] (h3414 : Equation3414 G) : Equation3306 G := by
  intro x y
  conv => enter [1]; rw [h3414 x y x]

theorem Equation43_3414_4512_implies_Equation40 (G : Type*) [Magma G] (h43 : Equation43 G) (h3414 : Equation3414 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3414 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3414 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3414 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation4271_implies_Equation4268 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4268 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4271 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4271_implies_Equation4270 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4271 x y y]

@[equational_result]
theorem Equation4271_implies_Equation4284 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4284 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation43_4271_4512_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h4271 : Equation4271 G) (h4512 : Equation4512 G) : Equation4276 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h4271 X0 X1 X2]
    conv => enter [1]; rw [h4271 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK0]
    conv => enter [1]; rw [h4271 X0 sK1 sK1]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK1]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l3 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4271 (X0 ◇ X1) sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4271 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l3 X0 X1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [h43 (X0 ◇ X1) (sK0 ◇ sK0)]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 sK1 X0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) X0 X0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK0]
  have l12 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [← l2 X0 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation43_4268_4512_implies_Equation4270 (G : Type*) [Magma G] (h43 : Equation43 G) (h4268 : Equation4268 G) (h4512 : Equation4512 G) : Equation4270 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h4268 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4268 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l2 sK0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 X0]
  intro x y
  conv => enter [1]; rw [l7 x x y]

theorem Equation43_4268_4512_implies_Equation4284 (G : Type*) [Magma G] (h43 : Equation43 G) (h4268 : Equation4268 G) (h4512 : Equation4512 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4268 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 sK0 X0 sK1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4268 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l2 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l6 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l4 sK0 sK1 X1 sK0]
  have l7 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4268 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 X1]
  have l8 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l7 sK0 sK1 X1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK0 X0]
  intro x y
  conv => enter [1]; rw [l14 x y x]

theorem Equation43_4268_4512_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h4268 : Equation4268 G) (h4512 : Equation4512 G) : Equation4276 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h4268 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4268 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l2 sK0 X1 sK0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation43_4270_4284_4512_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4270 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4270 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4270 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0 X0]
    conv => enter [1]; rw [l10 X0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l17 (X0 ◇ X0) sK0]
    conv => enter [1, 2]; rw [← h4270 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1]; rw [← l17 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l20 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l21 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0)]
  have l23 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l22 X0 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l23 X0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [h43 (X0 ◇ X0) (sK0 ◇ sK0)]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0 sK0]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l26 sK0]
  have l28 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4270 sK0 X0]
    conv => enter [1]; rw [← h4284 sK0 X0]
  have l30 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h4284 X0 X1]
  have l31 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l30 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [← l2 X0 sK0 sK0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1]; rw [← l28 X0 sK0 sK1]
  have l34 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l31 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [l3 X0 X1 sK0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l27 sK0 sK0]
  have l36 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [l34 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l32 sK0 X0]
  have l37 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l36 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l27 X1 sK0]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l35 sK0 sK1 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0 sK0]
  have l40 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l38 sK0 sK1 X0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK0]
    conv => enter [1]; rw [← l40 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l41 x y]

theorem Equation43_4270_4276_4512_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4270 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4270 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0 X0]
    conv => enter [1]; rw [l9 X0 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4276 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4276 sK0 X0]
    conv => enter [1]; rw [l3 X0 X0 sK0]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l13 X0 sK0 sK1]
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l15 X0 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l16 X0 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l17 X0 sK0 sK1]
    conv => enter [1]; rw [l3 X0 X0 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation43_3253_4284_4512_implies_Equation307 (G : Type*) [Magma G] (h43 : Equation43 G) (h3253 : Equation3253 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4284 X0 X1]
    conv => enter [1]; rw [h4284 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3253 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1, 2]; rw [h43 X0 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4284 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l7 sK0]
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

theorem Equation43_3253_4276_4512_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h3253 : Equation3253 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h3253 X1]
    conv => enter [1, 2]; rw [h4276 X1 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2]; rw [h4276 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4276 X0 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h4276 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 X0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l11 X0 sK0]
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2, 2]; rw [l11 X0 sK0]
  have l15 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l15 X0 X1 sK0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l17 X0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation43_3253_4270_4512_implies_Equation40 (G : Type*) [Magma G] (h43 : Equation43 G) (h3253 : Equation3253 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4270 X0 sK1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3253 sK1]
    conv => enter [1, 2]; rw [h4270 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation40_43_3306_4512_implies_Equation3414 (G : Type*) [Magma G] (h40 : Equation40 G) (h43 : Equation43 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation3414 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h43 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h40 sK0 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3306 sK1 sK2]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) sK1 sK1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation43_411_4284_4512_implies_Equation3 (G : Type*) [Magma G] (h43 : Equation43 G) (h411 : Equation411 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4284 X0 X1]
    conv => enter [1]; rw [h4284 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1, 2]; rw [h43 X0 sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← h411 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l3 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h411 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1, 2]; rw [h4284 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h411 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l8 sK0]
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h411 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1, 2]; rw [h4284 (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l13 (sK0 ◇ sK0) sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK0]
  have l18 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l17 sK0]
  intro x
  conv => enter [1]; rw [l18 x]

theorem Equation43_411_4276_4512_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h411 : Equation411 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← h411 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ X2))) (X0 ◇ X1)]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2]; rw [l1 (X1 ◇ (X2 ◇ (X2 ◇ X2))) X0 X1]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X2)) X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X2 ◇ X2) X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X2 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1 X0]
    conv => enter [1, 2]; rw [← l8 X1 X0 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X0]
    conv => enter [1]; rw [h4276 X0 X1]
  have l15 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l12 X0 X0]
    conv => enter [1]; rw [← h411 X0]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l12 X0 X0]
    conv => enter [1]; rw [l15 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← l12 X1 X1]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l13 X0 X0]
    conv => enter [1]; rw [l16 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l18 X1]
  have l20 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X1 X0]
    conv => enter [1]; rw [l18 X1]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation43_411_4270_4512_implies_Equation11 (G : Type*) [Magma G] (h43 : Equation43 G) (h411 : Equation411 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4270 X0 sK1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [← h4270 X0 sK1]
    conv => enter [1]; rw [← h411 X0]
  have l4 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [l2 (X0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l3 X0 sK1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l4 X0 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l6 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation411_3253_implies_Equation8 (G : Type*) [Magma G] (h411 : Equation411 G) (h3253 : Equation3253 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h3253 X0]
    conv => enter [1]; rw [← h411 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation43_307_3306_4512_implies_Equation323 (G : Type*) [Magma G] (h43 : Equation43 G) (h307 : Equation307 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3306 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) sK0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h3306 X0 X1]
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h3306 X0 X1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h3306 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) X0 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation40_43_307_4512_implies_Equation308 (G : Type*) [Magma G] (h40 : Equation40 G) (h43 : Equation43 G) (h307 : Equation307 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h40 sK0 X0]
    conv => enter [1]; rw [h307 X0]
    conv => enter [1, 2]; rw [h40 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation308_323_implies_Equation38 (G : Type*) [Magma G] (h308 : Equation308 G) (h323 : Equation323 G) : Equation38 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h323 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h323 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation40_308_4271_implies_Equation311 (G : Type*) [Magma G] (h40 : Equation40 G) (h308 : Equation308 G) (h4271 : Equation4271 G) : Equation311 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [h4271 X0 sK1 sK2]
  have l1 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h40 sK0 X0]
    conv => enter [1]; rw [l0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

theorem Equation43_47_4284_4512_implies_Equation3 (G : Type*) [Magma G] (h43 : Equation43 G) (h47 : Equation47 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← h4284 X1 X0]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4284 X0 X1]
    conv => enter [1]; rw [h4284 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h47 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1, 2]; rw [h43 X0 sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h47 sK0]
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l13 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1, 2]; rw [← l12 sK0]
  intro x
  conv => enter [1]; rw [l13 x]

theorem Equation47_4276_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h4276 : Equation4276 G) : Equation56 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h4276 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_47_4270_4512_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h47 : Equation47 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h47 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [h4270 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [l3 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation47_3253_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h3253 : Equation3253 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1]; rw [← h3253 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation47_411_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h411 : Equation411 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← h411 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation43_56_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h56 : Equation56 G) : Equation4276 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← h56 X0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h56 (sK1 ◇ (sK1 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation440_3306_implies_Equation11 (G : Type*) [Magma G] (h440 : Equation440 G) (h3306 : Equation3306 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3306 X1 X1]
    conv => enter [1]; rw [← h440 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation42264_implies_Equation38 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_4512_42264_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ sK3) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l3 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← l2 sK4 sK4 sK4 sK1 sK0]
    conv => enter [1]; rw [l1 sK4 sK4 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l3 z w u x y]

theorem Equation43_42264_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK5 sK2 sK0 sK1 : G, (X0 ◇ X1) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  have l2 : ∀ sK5 sK2 sK0 sK1 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← l1 sK5 sK5 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK5 sK5 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]
  conv => enter [1]; rw [l2 z w u v x]

theorem Equation43_42264_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK4 sK5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  intro x y z w u v r
  conv => enter [1]; rw [l1 x y z w u v r]

theorem Equation4512_42264_implies_Equation41732 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_42264_implies_Equation42232 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation42264_implies_Equation41734 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation42264_implies_Equation42230 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_42264_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X1) = (sK3 ◇ sK0) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK3]
    conv => enter [1]; rw [h43 sK0 sK3]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 z w x y]

@[equational_result]
theorem Equation42264_implies_Equation41740 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 z x y]
  conv => enter [1]; rw [l1 z x]

@[equational_result]
theorem Equation42264_implies_Equation42222 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_42264_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X1) = (sK3 ◇ sK0) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK3]
    conv => enter [1]; rw [h43 sK0 sK3]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l3 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK2 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l3 w x y]
  conv => enter [1]; rw [l2 w z]

theorem Equation4512_42264_implies_Equation41737 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation42264_implies_Equation41741 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]
  conv => enter [1]; rw [l1 z w x]

@[equational_result]
theorem Equation42264_implies_Equation42225 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y x w]
  conv => enter [1]; rw [l1 x w z]

theorem Equation43_42264_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation42238 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (sK1 ◇ sK0) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 sK1]
  have l2 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l0 sK3 sK4 sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  intro x y z w u
  conv => enter [1]; rw [l1 x y w u]
  conv => enter [1]; rw [l2 w u z]

theorem Equation4512_42264_implies_Equation41747 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41747 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation42264_implies_Equation41761 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41761 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 z y x]
  conv => enter [1]; rw [l1 z y x]

@[equational_result]
theorem Equation42264_implies_Equation41763 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41763 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK3) sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z (z ◇ w)]
  conv => enter [1]; rw [l1 z w x]

@[equational_result]
theorem Equation42264_implies_Equation42254 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation42254 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l0 sK1 (sK2 ◇ (sK2 ◇ sK3)) sK2 sK3]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 z w x y]

theorem Equation43_42264_implies_Equation42258 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation42258 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (sK1 ◇ sK0) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 sK1]
  have l2 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK4) sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4)))]
  intro x y z w u
  conv => enter [1]; rw [l1 x y w (w ◇ u)]
  conv => enter [1]; rw [l2 w u z]

theorem Equation4512_42264_implies_Equation41751 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41751 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 sK3 sK0 : G, (X0 ◇ X1) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l1 sK1 sK1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l2 x y z w]

theorem Equation43_42264_implies_Equation41768 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation41768 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK4 sK1 : G, (X0 ◇ X1) = (sK3 ◇ (sK4 ◇ sK1)) := by
    intro X0 X1 sK3 sK4 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK4 ◇ sK1) sK3]
    conv => enter [1]; rw [h43 (sK4 ◇ sK1) sK3]
  have l2 : ∀ sK3 sK4 sK1 sK2 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK3 sK4 sK1 sK2
    conv => enter [1]; rw [← l1 sK3 sK3 sK3 sK4 sK1]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l3 : ∀ sK3 sK4 sK1 sK2 sK0 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ sK0) := by
    intro sK3 sK4 sK1 sK2 sK0
    conv => enter [1]; rw [← l1 sK3 sK3 sK3 sK4 sK1]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l3 z w u x y]
  conv => enter [1]; rw [l2 z w u x]

theorem Equation4512_42264_implies_Equation42195 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation42195 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ sK3) sK0]
    conv => enter [1]; rw [← h4512 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK2 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l1 sK2 sK2 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 sK2 sK2 sK2 sK3]
  have l3 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l1 sK2 sK2 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [← l2 x y w]
  conv => enter [1]; rw [l3 x y w z]

theorem Equation43_42264_implies_Equation42204 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation42204 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK4 sK1 : G, (X0 ◇ X1) = (sK4 ◇ sK1) := by
    intro X0 X1 sK4 sK1
    conv => enter [1]; rw [l0 X0 X1 sK1 sK4]
    conv => enter [1]; rw [h43 sK1 sK4]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1, 2]; rw [l1 sK2 (sK3 ◇ (sK4 ◇ sK1)) sK4 sK1]
    conv => enter [1]; rw [l0 sK2 (sK4 ◇ sK1) sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l2 z x w u y]

@[equational_result]
theorem Equation42264_implies_Equation41736 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41736 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y x (x ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation42264_implies_Equation42223 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation42223 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42264_implies_Equation54340 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54340 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK0]
  have l1 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l2 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l1 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 sK2 sK1 (sK2 ◇ sK3)]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3)) sK0]
    conv => enter [1]; rw [← l0 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 y z x]
  conv => enter [1]; rw [l3 y z x w]

@[equational_result]
theorem Equation42264_implies_Equation54345 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54345 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK3 (sK1 ◇ sK0) sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK3 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l0 sK3 sK4 sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK3 ◇ sK4)]
  intro x y z w u
  conv => enter [1]; rw [← l2 y z x]
  conv => enter [1]; rw [l0 y z y (w ◇ u)]
  conv => enter [1]; rw [l1 y w u x]

theorem Equation43_42264_implies_Equation54388 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54388 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ X1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK2]
  have l2 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← l1 sK2 sK2 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK2 sK2 sK3 (sK2 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK4 sK5 sK3 : G, (sK4 ◇ sK5) = (sK3 ◇ (sK4 ◇ sK5)) := by
    intro sK4 sK5 sK3
    conv => enter [1]; rw [l0 sK4 sK5 sK4 sK4]
    conv => enter [1]; rw [l0 sK4 sK4 sK3 (sK4 ◇ sK5)]
  have l4 : ∀ sK4 sK5 sK2 sK0 sK1 : G, (sK4 ◇ sK5) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK4 sK5 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK2]
  intro x y z w u v
  conv => enter [1]; rw [← l3 y z x]
  conv => enter [1]; rw [l4 y z w u v]
  conv => enter [1]; rw [l2 w u v x]

theorem Equation43_42264_implies_Equation54683 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54683 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK5 sK6 sK4 : G, (sK5 ◇ sK6) = (sK4 ◇ (sK5 ◇ sK6)) := by
    intro sK5 sK6 sK4
    conv => enter [1]; rw [l0 sK5 sK6 (sK5 ◇ sK6) sK4]
    conv => enter [1]; rw [h43 (sK5 ◇ sK6) sK4]
  have l2 : ∀ sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK5 ◇ sK6) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK5 sK6 (sK1 ◇ (sK2 ◇ sK0)) sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  intro x y z w u v r
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l2 y z w u v r]

theorem Equation4512_42264_implies_Equation54312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54312 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l2 y z x]

theorem Equation43_4512_42264_implies_Equation54639 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54639 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK1 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK2]
  intro x y z w
  conv => enter [1]; rw [← l2 w x y z]
  conv => enter [1]; rw [l1 w]

theorem Equation4512_42264_implies_Equation54313 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54313 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation42264_implies_Equation54315 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54315 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ z) x w]
  conv => enter [1]; rw [l0 x w x (x ◇ (x ◇ w))]

@[equational_result]
theorem Equation42264_implies_Equation54636 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54636 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ z) w x]
  conv => enter [1]; rw [l0 w x w (w ◇ (w ◇ x))]

theorem Equation43_42264_implies_Equation54640 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54640 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [← l1 w u x y z]
  conv => enter [1]; rw [l0 w u w (w ◇ (w ◇ u))]

@[equational_result]
theorem Equation42264_implies_Equation54317 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54317 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]
  conv => enter [1]; rw [l1 y z x]

@[equational_result]
theorem Equation42264_implies_Equation54327 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54327 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK3 ◇ sK0)]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  intro x y z w
  conv => enter [1]; rw [← l1 w x y z]
  conv => enter [1]; rw [l2 w x]

theorem Equation43_42264_implies_Equation54645 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54645 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK2 : G, (sK3 ◇ sK3) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK3 ◇ sK3))]
  have l2 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK3 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [← l2 u x y z]
  conv => enter [1]; rw [l1 u w]

@[equational_result]
theorem Equation42264_implies_Equation54319 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54319 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK2 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  intro x y z w
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l0 y z y w]
  conv => enter [1]; rw [l2 y w x]

@[equational_result]
theorem Equation42264_implies_Equation54328 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54328 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK4 sK2 sK1 sK0 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK3 sK4 sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK3 sK4 sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK1 ◇ sK0)]
  have l2 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l0 sK3 sK4 sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK3 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [← l1 w u x y z]
  conv => enter [1]; rw [l2 w u x]

theorem Equation4512_42264_implies_Equation54622 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54622 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 (sK2 ◇ sK3) sK0]
    conv => enter [1]; rw [← h4512 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x y z]
  conv => enter [1]; rw [l1 x y w]

@[equational_result]
theorem Equation42264_implies_Equation54625 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54625 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l0 sK3 sK4 sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK3 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ z) x u]
  conv => enter [1]; rw [l1 x u w]

theorem Equation43_42264_implies_Equation54646 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54646 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK4 sK5 sK3 : G, (sK4 ◇ sK5) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK5))) := by
    intro sK4 sK5 sK3
    conv => enter [1]; rw [l0 sK4 sK5 sK4 sK4]
    conv => enter [1]; rw [l0 sK4 sK4 sK3 (sK3 ◇ (sK4 ◇ sK5))]
  have l2 : ∀ sK4 sK5 sK2 sK0 sK1 : G, (sK4 ◇ sK5) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK4 sK5 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK2]
  intro x y z w u v
  conv => enter [1]; rw [← l2 u v x y z]
  conv => enter [1]; rw [l1 u v w]

@[equational_result]
theorem Equation42264_implies_Equation41733 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41733 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y x (x ◇ (x ◇ (x ◇ y)))]

theorem Equation43_42264_implies_Equation41580 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation41580 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK4 ◇ (sK1 ◇ sK0)) sK3]
    conv => enter [1]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) sK3]
  have l2 : ∀ sK3 sK4 sK1 sK0 sK2 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [← l1 sK3 sK3 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK2 (sK4 ◇ (sK1 ◇ sK0)) sK3]
    conv => enter [1]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) sK3]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]
  conv => enter [1]; rw [l2 y z w u x]

theorem Equation43_42264_implies_Equation41731 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation41731 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK3) = (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK4]
    conv => enter [1]; rw [h43 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK4]
  intro x y z w u v
  conv => enter [1]; rw [l1 x y z w u v]

theorem Equation4512_42264_implies_Equation53878 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53878 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation42264_implies_Equation53895 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53895 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y x (z ◇ (w ◇ u))]

@[equational_result]
theorem Equation42264_implies_Equation53932 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53932 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y y (z ◇ (w ◇ u))]

theorem Equation43_42264_implies_Equation54009 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54009 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l1 x y z w u v]

theorem Equation43_42264_implies_Equation54318 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation54318 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42264_implies_Equation41530 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_42264_implies_Equation41532 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_42264_implies_Equation41533 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42264_implies_Equation41539 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_4512_42264_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 sK3 sK0 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l2 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK2]
  have l3 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l2 sK2 sK2 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 sK2 sK2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK1 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK2]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l3 y z w x]

theorem Equation4512_42264_implies_Equation41558 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [l2 y x]

@[equational_result]
theorem Equation42264_implies_Equation41559 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41559 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x x y (y ◇ (y ◇ z))]
  conv => enter [1]; rw [l1 y z x]

@[equational_result]
theorem Equation42264_implies_Equation41562 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41562 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x x z z]
  conv => enter [1]; rw [l1 z x y]

@[equational_result]
theorem Equation42264_implies_Equation41563 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41563 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ sK0)) sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x x y (y ◇ (z ◇ w))]
  conv => enter [1]; rw [l1 y z w x]

theorem Equation4512_42264_implies_Equation41632 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41632 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation42264_implies_Equation41633 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41633 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y (y ◇ (y ◇ (y ◇ z)))]

@[equational_result]
theorem Equation42264_implies_Equation41636 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41636 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x x z z]
  conv => enter [1]; rw [l1 z y]

@[equational_result]
theorem Equation42264_implies_Equation41637 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41637 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x x y (y ◇ (y ◇ (z ◇ w)))]

@[equational_result]
theorem Equation42264_implies_Equation41649 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41649 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ sK0) sK3 sK3]
    conv => enter [1]; rw [l0 sK3 sK3 sK2 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x x z (z ◇ w)]
  conv => enter [1]; rw [l1 z w y]

theorem Equation43_42264_implies_Equation41654 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation41654 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l2 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← l1 sK4 sK4 sK4 sK1 sK0]
    conv => enter [1]; rw [l0 sK4 sK4 sK3 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK2 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [l3 x z w u]
  conv => enter [1]; rw [l2 z w u y]

theorem Equation4512_42264_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41538 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation42264_implies_Equation53821 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53821 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l0 x x x (y ◇ (z ◇ w))]

theorem Equation43_42264_implies_Equation53858 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation53858 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK2 (sK4 ◇ (sK1 ◇ sK0)) sK3]
    conv => enter [1]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) sK3]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l1 x y z w u]

theorem Equation4512_42264_implies_Equation53864 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53864 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK2]
  have l1 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x (x ◇ y) x y]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation42264_implies_Equation53867 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y x (x ◇ (z ◇ z))]

@[equational_result]
theorem Equation42264_implies_Equation53868 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53868 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y x (x ◇ (z ◇ w))]

theorem Equation4512_42264_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42264_implies_Equation53877 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation42264_implies_Equation53890 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y x (z ◇ (z ◇ w))]

theorem Equation43_42264_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation53914 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ sK1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK1 sK0]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l3 x y]
  conv => enter [1]; rw [l1 x y z z]
  conv => enter [1]; rw [l2 z y]

theorem Equation43_42264_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h42264 : Equation42264 G) : Equation53915 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK2 sK1]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK1 (sK1 ◇ sK2)]
  intro x y z w
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l1 x y y (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation42264_implies_Equation53927 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53927 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y y (z ◇ (z ◇ w))]

@[equational_result]
theorem Equation42264_implies_Equation53982 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53982 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y z (z ◇ (w ◇ w))]

@[equational_result]
theorem Equation42264_implies_Equation53983 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53983 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ y) x y]
  conv => enter [1]; rw [l0 x y z (z ◇ (w ◇ u))]

theorem Equation4512_42264_implies_Equation53859 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53859 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation4512_42264_implies_Equation54161 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54161 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation4512_42264_implies_Equation53977 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53977 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l2 z x y]

@[equational_result]
theorem Equation42264_implies_Equation53861 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53861 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ y) x z]
  conv => enter [1]; rw [l0 x z x (x ◇ (x ◇ z))]

@[equational_result]
theorem Equation42264_implies_Equation54163 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54163 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ y) x z]
  conv => enter [1]; rw [l0 x z x (x ◇ (x ◇ z))]

@[equational_result]
theorem Equation42264_implies_Equation53975 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53975 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ y) z x]
  conv => enter [1]; rw [l0 z x z (z ◇ (z ◇ x))]

@[equational_result]
theorem Equation42264_implies_Equation54277 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation54277 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ y) z x]
  conv => enter [1]; rw [l0 z x z (z ◇ (z ◇ x))]

@[equational_result]
theorem Equation42264_implies_Equation53978 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53978 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ y) z w]
  conv => enter [1]; rw [l0 z w z (z ◇ (z ◇ w))]

theorem Equation43_4512_42264_implies_Equation53863 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53863 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x (x ◇ y) x y]
  conv => enter [1]; rw [l3 x y]

theorem Equation43_4512_42264_implies_Equation54162 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation54162 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l1 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l1 x y x (x ◇ (x ◇ y))]

theorem Equation4512_42264_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation41529 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation4512_42264_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53811 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation42264_implies_Equation53817 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53817 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l0 x x x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation42264_implies_Equation53841 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53841 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l0 x x y (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation42264_implies_Equation53860 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53860 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y
  conv => enter [1, 2]; rw [l0 x y x (x ◇ y)]

theorem Equation4512_42264_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53810 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation42264_implies_Equation53840 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53840 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l0 x x y (y ◇ (z ◇ z))]

theorem Equation4512_42264_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53808 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l1 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x (x ◇ x) x x]
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation42264_implies_Equation53816 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53816 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l0 x x x (y ◇ (y ◇ y))]

theorem Equation4512_42264_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53836 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation42264_implies_Equation53837 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation53837 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ x) x x]
  conv => enter [1]; rw [l0 x x y (y ◇ (y ◇ z))]

theorem Equation4512_42264_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42264 : Equation42264 G) : Equation53807 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation42204_implies_Equation38 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation42204_implies_Equation41805 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation42204_implies_Equation41882 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_42204_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42204 : Equation42204 G) : Equation42405 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK2 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l6 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h43 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK2 X0]
  have l7 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [l5 sK2 X0 X1]
    conv => enter [1]; rw [l0 sK0 sK2 X1]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l5 (sK2 ◇ sK0) sK1 X0]
  have l9 : ∀ sK2 sK0 X0 sK1 X1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X0 sK1 X1
    conv => enter [1]; rw [l5 (sK2 ◇ sK0) X0 (X1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 X1]
  have l10 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
  have l11 : ∀ sK1 sK2 sK0 X0 sK3 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro sK1 sK2 sK0 X0 sK3 X1
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) X0 (X1 ◇ sK3)]
    conv => enter [1]; rw [← l4 sK3 sK1 sK2 sK0 X1]
  have l12 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
  have l13 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l12 sK6 sK3 sK1 sK2 sK0 sK6]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 X0 sK3 sK6]
  have l14 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l9 sK2 sK0 X0 sK1 sK3]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK2 X0 sK1]
  have l16 : ∀ sK3 sK1 sK2 sK0 sK6 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 sK6
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l13 sK6 sK3 sK1 sK2 sK0 sK3]
  have l17 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l14 sK3 sK1 sK2 sK0 sK1]
  have l18 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l15 sK1 sK2 sK0 sK2]
  have l19 : ∀ sK2 sK0 X0 X3 : G, (sK2 ◇ sK0) = (X0 ◇ X3) := by
    intro sK2 sK0 X0 X3
    conv => enter [1]; rw [l6 sK2 sK0 (sK0 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK2 sK2]
  have l20 : ∀ sK4 sK5 sK2 sK0 : G, (sK4 ◇ sK5) = (sK2 ◇ sK0) := by
    intro sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l5 sK4 sK5 sK4]
    conv => enter [1]; rw [l19 sK4 sK4 sK2 sK0]
  intro x y z w u v r
  conv => enter [1]; rw [l20 x y v r]
  conv => enter [1]; rw [l18 v r u]
  conv => enter [1]; rw [l17 u v r w]
  conv => enter [1]; rw [l16 w u v r z]

@[equational_result]
theorem Equation42204_implies_Equation41732 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_42204_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42204 : Equation42204 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42204_implies_Equation41734 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_42204_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42204 : Equation42204 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l1 sK0 X0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_42204_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h42204 : Equation42204 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l0 sK0 sK3 X0]
  have l2 : ∀ sK3 sK0 X0 X3 : G, (sK3 ◇ sK0) = (X0 ◇ X3) := by
    intro sK3 sK0 X0 X3
    conv => enter [1]; rw [l1 sK3 sK0 (sK0 ◇ (X0 ◇ (sK3 ◇ sK3)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK3 sK3]
  have l3 : ∀ sK1 sK2 X0 X3 : G, (sK1 ◇ sK2) = (X0 ◇ X3) := by
    intro sK1 sK2 X0 X3
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK1 sK1 sK1]
  have l4 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l3 sK3 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w (z ◇ (z ◇ (z ◇ w)))]

@[equational_result]
theorem Equation42204_implies_Equation41740 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_42204_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42204 : Equation42204 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l2 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l1 sK1 X0 (sK2 ◇ X1)]
    conv => enter [1]; rw [l0 sK1 sK2 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 X1 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l1 z (x ◇ x) (z ◇ (z ◇ (x ◇ x)))]

theorem Equation43_42204_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h42204 : Equation42204 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l0 sK0 sK3 X0]
  have l2 : ∀ sK3 sK0 X0 X3 : G, (sK3 ◇ sK0) = (X0 ◇ X3) := by
    intro sK3 sK0 X0 X3
    conv => enter [1]; rw [l1 sK3 sK0 (sK0 ◇ (X0 ◇ (sK3 ◇ sK3)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK3 sK3]
  have l3 : ∀ sK1 sK2 X0 X3 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ X3) := by
    intro sK1 sK2 X0 X3
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK1 sK1 sK1]
  have l4 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l3 sK1 sK2 sK3 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z (w ◇ w) (z ◇ (z ◇ (w ◇ w)))]

@[equational_result]
theorem Equation42204_implies_Equation41737 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation42204_implies_Equation41741 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (z ◇ w)))]

@[equational_result]
theorem Equation42204_implies_Equation42225 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 X0 X3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ X3) := by
    intro sK1 sK2 sK3 X0 X3
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK1 sK1 sK1]
  have l2 : ∀ sK2 sK0 X0 X3 : G, (sK2 ◇ sK0) = (X0 ◇ X3) := by
    intro sK2 sK0 X0 X3
    conv => enter [1]; rw [l0 sK2 sK0 (sK2 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK2 sK2 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK2 sK0]
  have l4 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [l4 x w z]
  conv => enter [1]; rw [l0 z (x ◇ w) (z ◇ (z ◇ (x ◇ w)))]

theorem Equation43_42204_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h42204 : Equation42204 G) : Equation42238 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X0 X3 : G, (sK1 ◇ sK0) = (X0 ◇ X3) := by
    intro sK1 sK0 X0 X3
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK1 sK1]
  have l3 : ∀ sK2 sK3 sK4 X0 X3 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ X3) := by
    intro sK2 sK3 sK4 X0 X3
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK4) (sK2 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK2 sK2 sK2]
  have l4 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l3 sK2 sK3 sK4 sK1 sK1]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z (w ◇ u) (z ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation42204_implies_Equation41747 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41747 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (y ◇ (y ◇ z)))]

@[equational_result]
theorem Equation42204_implies_Equation41761 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41761 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation42204_implies_Equation41763 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41763 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y (x ◇ (z ◇ (z ◇ w)))]

@[equational_result]
theorem Equation42204_implies_Equation42254 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation42254 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 X0 X3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ X3) := by
    intro sK1 sK2 sK3 X0 X3
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ (sK2 ◇ sK3)) (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK1 sK1 sK1]
  have l2 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK3 sK0 sK3]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK3 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1]; rw [l0 z (w ◇ (w ◇ x)) (z ◇ (w ◇ (w ◇ x)))]

theorem Equation43_42204_implies_Equation42258 (G : Type*) [Magma G] (h43 : Equation43 G) (h42204 : Equation42204 G) : Equation42258 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X0 X3 : G, (sK1 ◇ sK0) = (X0 ◇ X3) := by
    intro sK1 sK0 X0 X3
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK1 sK1]
  have l3 : ∀ sK2 sK3 sK4 X0 X3 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) = (X0 ◇ X3) := by
    intro sK2 sK3 sK4 X0 X3
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK3 ◇ sK4)) (sK2 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK2 sK2 sK2]
  have l4 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l3 sK2 sK3 sK4 sK1 sK1]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z (w ◇ (w ◇ u)) (z ◇ (w ◇ (w ◇ u)))]

@[equational_result]
theorem Equation42204_implies_Equation41751 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41751 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y (x ◇ (y ◇ (z ◇ w)))]

@[equational_result]
theorem Equation42204_implies_Equation41768 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41768 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l1 x z w u y]

theorem Equation43_4512_42204_implies_Equation42195 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42204 : Equation42204 G) : Equation42195 G := by
  have l0 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l2 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [l1 X0 sK3 X1]
  have l3 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = ((sK2 ◇ sK3) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 (sK2 ◇ sK3) sK0 X0]
  have l4 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = ((sK2 ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l1 sK2 sK3 (X0 ◇ sK2)]
    conv => enter [1]; rw [← l2 sK2 sK3 X0 sK2]
  have l5 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK2 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l4 sK2 sK3 sK2]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 X3 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ X3) := by
    intro sK1 sK2 sK3 sK0 X0 X3
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK1 sK1 sK1]
  have l7 : ∀ sK2 sK3 X0 X3 : G, (sK2 ◇ sK3) = (X0 ◇ X3) := by
    intro sK2 sK3 X0 X3
    conv => enter [1]; rw [l1 sK2 sK3 (sK2 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK2 sK2 sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 sK2 sK3]
  have l9 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK3 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l5 x y w]
  conv => enter [1]; rw [l9 x y w z]
  conv => enter [1]; rw [l1 z (x ◇ (y ◇ w)) (z ◇ (x ◇ (y ◇ w)))]

@[equational_result]
theorem Equation42204_implies_Equation42264 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation42264 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 X0 X3 : G, (sK0 ◇ sK1) = (X0 ◇ X3) := by
    intro sK0 sK1 X0 X3
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK0 sK0]
  have l2 : ∀ sK3 sK4 sK5 sK2 X0 X3 : G, (sK3 ◇ (sK4 ◇ (sK5 ◇ sK2))) = (X0 ◇ X3) := by
    intro sK3 sK4 sK5 sK2 X0 X3
    conv => enter [1]; rw [l0 sK3 (sK4 ◇ (sK5 ◇ sK2)) (sK3 ◇ (X0 ◇ (sK3 ◇ sK3)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK3 sK3 sK3]
  have l3 : ∀ sK0 sK1 sK3 sK4 sK5 sK2 : G, (sK0 ◇ sK1) = (sK3 ◇ (sK4 ◇ (sK5 ◇ sK2))) := by
    intro sK0 sK1 sK3 sK4 sK5 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK3 sK4 sK5 sK2 sK0 sK0]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]
  conv => enter [1]; rw [l0 z (w ◇ (u ◇ v)) (z ◇ (w ◇ (u ◇ v)))]

theorem Equation4512_42195_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation38 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42195 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X4)))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X4))]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l2 X2 X3 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation43_4512_42195_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation41805 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ X0) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l2 (sK2 ◇ sK3) (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X0 ◇ X0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [h43 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) sK4 X0]
  have l5 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [← l3 sK2 sK3 sK4 sK1 sK0 sK4]
  have l6 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK2]
    conv => enter [1]; rw [← l4 sK4 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]
  conv => enter [1]; rw [l5 z w u x y]

theorem Equation43_42195_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41882 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h42195 X0 X1 X2 X2]
    conv => enter [1]; rw [← h42195 X2 X0 X2 (X1 ◇ X2)]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ X0) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [h43 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l2 (sK2 ◇ (sK0 ◇ sK1)) sK5 X0]
  have l4 : ∀ sK5 sK2 sK0 sK1 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l3 sK5 sK2 sK0 sK1 sK5]
    conv => enter [1]; rw [← l2 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK5]
  have l5 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK4 sK3]
    conv => enter [1]; rw [← l3 sK5 sK2 sK0 sK1 sK3]
  intro x y z w u v
  conv => enter [1]; rw [l5 x y z w u v]
  conv => enter [1]; rw [l4 z w u v x]

theorem Equation43_4512_42195_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l0 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [l0 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l3 : ∀ sK3 sK1 sK2 sK0 sK6 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK6 ◇ X0)) = (X0 ◇ (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK1 sK2 sK0 sK6 X0
    conv => enter [1]; rw [l0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  have l4 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 X0]
  have l5 : ∀ sK1 sK2 sK0 X0 sK3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK3 X0]
  have l6 : ∀ sK3 sK1 sK2 sK0 X0 sK6 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ sK6)) = (X0 ◇ (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK1 sK2 sK0 X0 sK6
    conv => enter [1, 2]; rw [h43 X0 sK6]
    conv => enter [1]; rw [l3 sK3 sK1 sK2 sK0 sK6 X0]
  have l7 : ∀ X2 sK2 sK0 X1 X0 sK1 : G, (X2 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro X2 sK2 sK0 X1 X0 sK1
    conv => enter [1]; rw [h42195 X2 (sK2 ◇ sK0) X1 (X0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK2 sK0 X0 sK1]
  have l8 : ∀ X2 sK1 sK2 sK0 X1 X0 sK3 : G, (X2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))))) := by
    intro X2 sK1 sK2 sK0 X1 X0 sK3
    conv => enter [1]; rw [h42195 X2 (sK1 ◇ (sK2 ◇ sK0)) X1 (X0 ◇ sK3)]
    conv => enter [1, 2, 2, 2]; rw [l5 sK1 sK2 sK0 X0 sK3]
  have l9 : ∀ X2 sK3 sK1 sK2 sK0 X1 X0 sK6 : G, (X2 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))))))) := by
    intro X2 sK3 sK1 sK2 sK0 X1 X0 sK6
    conv => enter [1]; rw [h42195 X2 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1 (X0 ◇ sK6)]
    conv => enter [1, 2, 2, 2]; rw [l6 sK3 sK1 sK2 sK0 X0 sK6]
  have l10 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l12 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l10 X2 X0 X3 X2]
    conv => enter [1]; rw [← l11 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l13 : ∀ X2 X0 sK3 sK1 sK2 sK0 : G, (X2 ◇ X0) = (X2 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X2 X0 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h42195 X2 X0 X2 (X2 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [← l9 X2 sK3 sK1 sK2 sK0 X2 X0 X2]
  have l14 : ∀ X2 X0 sK1 sK2 sK0 : G, (X2 ◇ X0) = (X2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X2 X0 sK1 sK2 sK0
    conv => enter [1]; rw [h42195 X2 X0 X2 (X2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l8 X2 sK1 sK2 sK0 X2 X0 X2]
  have l15 : ∀ X2 X0 sK2 sK0 : G, (X2 ◇ X0) = (X2 ◇ (sK2 ◇ sK0)) := by
    intro X2 X0 sK2 sK0
    conv => enter [1]; rw [h42195 X2 X0 X2 (X2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l7 X2 sK2 sK0 X2 X0 X2]
  have l16 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l12 (sK2 ◇ sK0) sK1 X0]
  have l17 : ∀ X0 X1 sK4 sK5 : G, (X0 ◇ X1) = (sK4 ◇ sK5) := by
    intro X0 X1 sK4 sK5
    conv => enter [1]; rw [l12 X0 X1 X0]
    conv => enter [1]; rw [← l12 sK4 sK5 X0]
  have l18 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK4 sK5 sK4]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0 sK4]
  have l19 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ sK3) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 1]; rw [← l18 sK4 sK5 sK1 sK2 sK0]
  have l20 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l19 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l13 (sK4 ◇ sK5) sK3 sK3 sK1 sK2 sK0]
  have l21 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l20 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l14 (sK4 ◇ sK5) (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1 sK2 sK0]
  have l22 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ (sK2 ◇ sK0)) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l21 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l15 (sK4 ◇ sK5) (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l23 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK4 sK5 (sK4 ◇ sK5) (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK3 sK1 sK2 sK0 sK4 sK5]
  have l24 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ sK6) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 1]; rw [← l23 sK4 sK5 sK3 sK1 sK2 sK0]
  have l25 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l24 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l13 (sK4 ◇ sK5) sK6 sK3 sK1 sK2 sK0]
  have l26 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l25 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l14 (sK4 ◇ sK5) (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1 sK2 sK0]
  have l27 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ (sK2 ◇ sK0)) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l26 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l15 (sK4 ◇ sK5) (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l28 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK4 sK5 (sK4 ◇ sK5) (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l27 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
  intro x y z w u v r
  conv => enter [1]; rw [l28 x y z w u v r]

theorem Equation43_4512_42195_implies_Equation41732 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation41732 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1]; rw [l5 x]

theorem Equation43_4512_42195_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation42232 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]
  conv => enter [1]; rw [l5 z]

theorem Equation43_42195_implies_Equation41734 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41734 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l2 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 x z y]

theorem Equation43_42195_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42230 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation43_42195_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42233 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 X0]
  have l4 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK3]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_42195_implies_Equation41740 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41740 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 z x y]
  conv => enter [1]; rw [l3 z x]

theorem Equation43_42195_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42222 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation43_42195_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42237 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 X0]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l5 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK3]
    conv => enter [1]; rw [l2 sK3 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y w]
  conv => enter [1]; rw [l4 w z]

end CommutativeSemigroup5
