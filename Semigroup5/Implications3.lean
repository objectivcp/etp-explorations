import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation3323_implies_Equation3319 (G : Type*) [Magma G] (h3323 : Equation3323 G) : Equation3319 G := by
  intro x y
  conv => enter [1]; rw [h3323 x y y]

@[equational_result]
theorem Equation3323_implies_Equation3256 (G : Type*) [Magma G] (h3323 : Equation3323 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [h3323 x x y]

@[equational_result]
theorem Equation3414_implies_Equation3353 (G : Type*) [Magma G] (h3414 : Equation3414 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h3414 x y y]

@[equational_result]
theorem Equation3414_implies_Equation3306 (G : Type*) [Magma G] (h3414 : Equation3414 G) : Equation3306 G := by
  intro x y
  conv => enter [1]; rw [h3414 x y x]

@[equational_result]
theorem Equation3414_implies_Equation3278 (G : Type*) [Magma G] (h3414 : Equation3414 G) : Equation3278 G := by
  intro x y
  conv => enter [1]; rw [h3414 x x y]

@[equational_result]
theorem Equation3331_implies_Equation3308 (G : Type*) [Magma G] (h3331 : Equation3331 G) : Equation3308 G := by
  intro x y
  conv => enter [1]; rw [h3331 x y x]

@[equational_result]
theorem Equation3331_implies_Equation3319 (G : Type*) [Magma G] (h3331 : Equation3331 G) : Equation3319 G := by
  intro x y
  conv => enter [1]; rw [h3331 x y y]

@[equational_result]
theorem Equation3331_implies_Equation3259 (G : Type*) [Magma G] (h3331 : Equation3331 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h3331 x x y]

@[equational_result]
theorem Equation3388_implies_Equation3346 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3346 G := by
  intro x y
  conv => enter [1]; rw [h3388 x y y]

@[equational_result]
theorem Equation3388_implies_Equation3306 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3306 G := by
  intro x y
  conv => enter [1]; rw [h3388 x y x]

@[equational_result]
theorem Equation3388_implies_Equation3271 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3271 G := by
  intro x y
  conv => enter [1]; rw [h3388 x x y]

@[equational_result]
theorem Equation3334_implies_Equation3306 (G : Type*) [Magma G] (h3334 : Equation3334 G) : Equation3306 G := by
  intro x y
  conv => enter [1]; rw [h3334 x y x]

@[equational_result]
theorem Equation3334_implies_Equation3319 (G : Type*) [Magma G] (h3334 : Equation3334 G) : Equation3319 G := by
  intro x y
  conv => enter [1]; rw [h3334 x y y]

@[equational_result]
theorem Equation3334_implies_Equation3261 (G : Type*) [Magma G] (h3334 : Equation3334 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h3334 x x y]

@[equational_result]
theorem Equation3342_implies_Equation3253 (G : Type*) [Magma G] (h3342 : Equation3342 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3342 x x]

@[equational_result]
theorem Equation3370_implies_Equation3342 (G : Type*) [Magma G] (h3370 : Equation3370 G) : Equation3342 G := by
  intro x y
  conv => enter [1]; rw [h3370 x y x]

theorem Equation3370_4512_implies_Equation3323 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3323 G := by
  have l0 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK1 X0 sK0]
  have l1 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [← l0 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X1]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ (sK2 ◇ sK2)) sK0 sK0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK2 ◇ sK2)) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ sK2) sK1 sK1]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 sK2 sK2 sK2]
  have l5 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h3370 sK0 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 (sK2 ◇ sK2)]
  have l8 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l7 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l4 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK0]
  have l10 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l11 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = (((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro X1 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l8 sK1 X0 sK2]
    conv => enter [1]; rw [← h3370 ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) X1 X0]
  have l12 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l11 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2)) X1]
  have l13 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [← l1 X1 sK0 sK1 sK0]
    conv => enter [1]; rw [l12 X1 sK0 sK1 sK2]
  have l14 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l4 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l8 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 (sK0 ◇ sK1) sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l17 sK0 sK1]
  have l19 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l18 sK1 X0 sK0]
    conv => enter [1]; rw [l1 X0 (sK0 ◇ sK1) sK1 sK0]
  have l20 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ (sK2 ◇ sK2)) sK2 sK0]
  have l21 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h3370 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l22 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h3370 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l23 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l20 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK2]
  have l24 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l24 sK2 sK0 sK1]
    conv => enter [1]; rw [l14 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l26 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1 sK2 (sK2 ◇ sK2)]
  have l27 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l26 sK2 sK1 sK0]
    conv => enter [1]; rw [← l22 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l27 sK2 sK1 sK0]
  have l29 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l21 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK2 (sK2 ◇ sK2)]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l33 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l28 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1]; rw [← l33 sK2 sK1 X0 sK0]
  have l35 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l13 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2 X0]
  have l36 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l32 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l35 sK0 sK1 X0 sK2]
  have l37 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l19 sK1 X0 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 X0 sK1]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l39 x y z]

theorem Equation3370_4512_implies_Equation3346 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3346 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK1 sK1 sK1]
  have l2 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X1 X0]
    conv => enter [1, 2, 2]; rw [← l1 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK1)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK1) sK0 sK0]
  have l4 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro X1 X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [h3370 (sK1 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1 X0]
  have l5 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l4 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l7 : ∀ sK1 X1 sK0 : G, ((sK1 ◇ sK1) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l2 sK1 X1 sK1]
    conv => enter [1]; rw [l5 X1 sK1 sK1 sK0]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1 X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l10 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [h3370 (sK0 ◇ (sK1 ◇ sK1)) X0 sK1]
    conv => enter [1]; rw [← h3370 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1 X0]
  have l11 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l10 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK1]
  have l13 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l8 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [l11 X1 sK0 sK0 sK1]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  have l15 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 X0]
  have l16 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) = (sK1 ◇ (sK0 ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l15 sK1 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK0 X1]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3370 X0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3370 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK0]
  have l21 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro X0 sK1 sK0
    conv => enter [1, 2]; rw [h3370 sK1 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [l21 X0 sK1 sK0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [l12 sK1 sK0 X0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l24 sK1 sK0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 sK0 X0]
    conv => enter [1]; rw [l16 X0 (sK1 ◇ sK1) sK0 sK1]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [l26 sK1 sK0 X0]
  have l28 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3370 X0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l13 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l29 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l28 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l22 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l14 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK1 sK0]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 (sK0 ◇ sK1)]
  have l34 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 X0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l18 ((sK0 ◇ sK1) ◇ sK1) sK0 sK1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK1)]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [← l34 sK0 sK0 sK1]
  have l40 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← h3370 sK0 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l40 y x y]

theorem Equation3370_4512_implies_Equation43 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK0 sK1 sK1]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X3 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h3370 X3 (X0 ◇ X1) X2]
  have l3 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [h3370 X0 X1 X3]
    conv => enter [1]; rw [l2 X3 X1 X3 X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3370 sK1 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h3370 sK0 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l3 (sK1 ◇ sK0) sK0 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h3370 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation3370_4512_implies_Equation4270 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4270 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK0) sK0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK1)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK1) sK0 sK0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 sK0 X0 sK0]
    conv => enter [1]; rw [l7 X0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h3370 X1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [h3370 X1 sK0 X1]
    conv => enter [1]; rw [l9 sK0 X1 X1]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [l7 X0 sK0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l11 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l16 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ X0))) = (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l14 sK0 X0 sK1]
    conv => enter [1]; rw [← h3370 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) X1 X0]
  have l17 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l16 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l18 : ∀ sK0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X1 sK0]
    conv => enter [1]; rw [l17 X1 sK0 sK0 sK1]
  have l19 : ∀ sK0 X1 sK1 : G, (sK0 ◇ X1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l8 sK0 X1]
    conv => enter [1]; rw [l18 sK0 X1 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l11 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) sK1]
    conv => enter [1]; rw [← h3370 X0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ sK1) sK0]
  have l23 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l21 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 X0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3370 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l24 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK1 sK0]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2]; rw [l27 sK1 sK0]
  have l29 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l28 sK1 X0 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l29 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l30 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation3370_4512_implies_Equation3414 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3414 G := by
  have l0 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 (sK1 ◇ sK2) X0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK2 sK1 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK2) sK0 sK0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK2]
  have l5 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK2 ◇ sK1) ◇ X1) := by
    intro X1 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h3370 (sK2 ◇ sK1) X1 X0]
  have l6 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) = (sK2 ◇ (sK1 ◇ X1)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l5 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 X1]
  have l7 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (sK2 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [l6 X1 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X1 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h3370 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) X1 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK2 X0]
  have l9 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X1]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h3370 sK2 sK2 sK1]
  have l11 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h3370 X0 sK2 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK1 ◇ X0)]
  have l12 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 sK2 sK2]
  have l13 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l12 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l9 X0 sK2 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h3370 sK2 sK1 sK1]
    conv => enter [1]; rw [← l11 (sK1 ◇ (sK1 ◇ sK2)) sK2 sK0 sK1]
  have l15 : ∀ sK1 sK2 sK0 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 ((sK1 ◇ sK2) ◇ sK2) sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK1 sK2]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l15 sK1 sK2 sK1]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK1 sK1 sK2]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK2]
  have l21 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  have l22 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK2 sK0]
  have l24 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
  have l25 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2 sK1]
    conv => enter [1]; rw [← l24 (sK1 ◇ sK2) sK1 sK2 sK1]
  have l27 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l26 sK1 sK2]
  have l28 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h3370 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1]; rw [l27 sK1 sK2 X0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l27 sK1 sK2 sK0]
  have l30 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1 X0]
    conv => enter [1, 2, 2]; rw [l28 X0 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [← h3370 (sK1 ◇ sK2) X1 sK0]
  have l32 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l31 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l33 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3370 X0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l32 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l13 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [l29 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

@[equational_result]
theorem Equation3370_implies_Equation3308 (G : Type*) [Magma G] (h3370 : Equation3370 G) : Equation3308 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK0 sK1 sK1]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h3370 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [← l1 sK0 sK0 sK1]
    conv => enter [1]; rw [← h3370 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
  have l3 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 sK1 X0 sK0]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 sK1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3370_4512_implies_Equation4275 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4275 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h3370 sK0 X0 sK1]
    conv => enter [1]; rw [h3370 sK0 X0 sK0]
  have l1 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK1 ◇ sK0)) X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l1 sK1 sK0 X1 sK1]
    conv => enter [1]; rw [← h3370 (sK0 ◇ (sK0 ◇ sK0)) X1 sK1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK0) sK1 sK1]
  have l6 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 X0]
    conv => enter [1]; rw [l5 sK1 sK0 X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 sK0 X0 sK0]
    conv => enter [1]; rw [l7 X0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h3370 X1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [h3370 X1 sK0 X1]
    conv => enter [1]; rw [l9 sK0 X1 X1]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 sK0 X0 sK0]
    conv => enter [1]; rw [← l10 X0 sK0]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
    conv => enter [1, 1]; rw [← h3370 (sK0 ◇ sK0) X0 sK0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l12 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l14 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X1]
  have l17 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3370 X1 X0 sK0]
    conv => enter [1]; rw [← l16 sK0 X0 X1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK0 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l21 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

@[equational_result]
theorem Equation3370_implies_Equation3331 (G : Type*) [Magma G] (h3370 : Equation3370 G) : Equation3331 G := by
  have l0 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ (sK1 ◇ sK2)) sK0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK2 sK1 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK1 ◇ sK2)) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK2) sK2 sK2]
  have l3 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h3370 sK0 X0 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l0 sK0 sK2 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK2]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l4 sK1 X0 sK2]
    conv => enter [1]; rw [← l2 sK2 sK1 X0]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 (sK2 ◇ (sK1 ◇ sK2)) sK2 sK1]
    conv => enter [1]; rw [← l5 sK1 ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation3370_4512_implies_Equation3334 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK2 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK1 X0 sK2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK0]
  have l2 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X1 X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [h3370 sK1 X0 sK0]
    conv => enter [1]; rw [← h3370 (sK0 ◇ (sK0 ◇ sK1)) X1 X0]
  have l3 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l2 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X1]
  have l4 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h3370 sK1 sK0 sK2]
  have l5 : ∀ sK2 sK1 X1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK2 sK1 X1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 X1 sK2]
    conv => enter [1]; rw [l3 X1 sK2 sK1 sK0]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ (sK2 ◇ sK1)) sK0 sK0]
  have l7 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ sK0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h3370 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK2 sK1 ((sK0 ◇ sK1) ◇ X0) sK0]
  have l8 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h3370 sK0 X0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l9 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← h3370 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l7 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 (sK0 ◇ sK1) sK0 sK2 sK1]
    conv => enter [1]; rw [← l10 sK0 sK2 sK1]
  have l12 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0 sK1]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK2 sK1]
  have l15 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← h3370 (sK2 ◇ (sK2 ◇ sK1)) X0 sK0]
  have l16 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK1]
    conv => enter [1]; rw [l15 X0 sK1 sK1 sK2]
  have l17 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 (sK2 ◇ (sK2 ◇ sK1)) sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l17 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

theorem Equation3370_4512_implies_Equation3388 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3388 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK0]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ (sK2 ◇ sK1)) sK2 sK2]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  have l3 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [h3370 sK2 X0 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h3370 X0 sK0 sK1]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 sK1 sK1 X0]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l3 sK2 (sK2 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ (sK2 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
  have l10 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK1]
    conv => enter [1]; rw [← h3370 sK1 sK0 sK2]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l10 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation3370_4512_implies_Equation4305 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4305 G := by
  have l0 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK1 X0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK2 sK1 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK1 ◇ sK2)) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK2) sK2 sK2]
  have l3 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK2]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l3 sK1 X0 sK2]
    conv => enter [1]; rw [← l2 sK2 sK1 X0]
  have l5 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = (((sK1 ◇ sK2) ◇ sK2) ◇ X1) := by
    intro X1 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l3 sK1 X0 sK2]
    conv => enter [1]; rw [← h3370 ((sK1 ◇ sK2) ◇ sK2) X1 X0]
  have l6 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X1)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l5 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 X1]
  have l7 : ∀ sK0 sK1 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X1)) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [l6 X1 sK0 sK1 sK2]
  have l8 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l4 sK1 (X0 ◇ (X0 ◇ X1)) sK2]
    conv => enter [1]; rw [← h3370 X1 (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l9 : ∀ X1 sK1 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [h3370 X1 sK1 X1]
    conv => enter [1]; rw [l8 sK1 X1 X1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← h3370 sK1 sK2 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ sK2)]
  have l12 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h3370 X0 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK2 ◇ X0) sK2]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3370 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3370 sK1 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h3370 sK2 sK2 sK1]
  have l17 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 sK2]
  have l18 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l17 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l19 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l18 sK2 sK1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 sK2]
  have l20 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l19 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [← l15 sK1 sK2]
  have l21 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l20 sK2 sK1]
  have l22 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h3370 sK1 X0 sK0]
    conv => enter [1]; rw [l21 sK1 X0 sK2]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 X0 sK1]
    conv => enter [1]; rw [← l9 X0 sK1 sK1]
  have l24 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l22 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← l9 X0 sK1 X0]
  have l25 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l25 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK1) X1 sK0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [l24 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h3370 X0 sK0 sK1]
  have l29 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l26 sK0 sK1 sK1 X0]
    conv => enter [1]; rw [l28 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l23 (sK0 ◇ sK1) sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l29 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l32 sK1 sK0]
  have l34 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l20 sK2 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l27 sK0 sK1 sK0]
    conv => enter [1]; rw [← l34 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

theorem Equation3370_4512_implies_Equation4325 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4325 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK0) sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK0 sK1 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK2 ◇ sK2)) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ sK2) sK1 sK1]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 sK2 sK2 sK2]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 (sK1 ◇ sK0)]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ X0) := by
    intro X0 sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← h3370 sK1 X0 sK0]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l3 sK2 sK1]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 (sK2 ◇ sK2)]
  have l8 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l7 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l3 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [l5 X0 sK1 sK0]
  have l10 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← l9 sK0 sK1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h3370 X1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l11 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ sK1) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [← l10 sK1 X1 X1 sK0]
    conv => enter [1]; rw [← h3370 X1 sK1 X1]
  have l12 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l13 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l12 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l1 sK1 sK0 X1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3370 sK0 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0 sK1 (sK1 ◇ sK0)]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ sK2) (sK2 ◇ sK2) sK1]
  have l25 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l8 sK1 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l24 sK1 sK2]
  have l27 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l28 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1, 2]; rw [l25 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l28 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK2 (sK2 ◇ sK2)]
  have l31 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h3370 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l31 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK2 (sK2 ◇ sK2)]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

theorem Equation3370_4512_implies_Equation4364 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4364 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK2) sK0 sK0]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK2 ◇ sK0)) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ sK0) sK1 sK1]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h3370 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l3 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h3370 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK2) ◇ sK0)]
  have l5 : ∀ sK1 X0 X1 sK2 sK0 : G, (sK1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)))) := by
    intro sK1 X0 X1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 (X0 ◇ X1) sK2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))]
  have l6 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 X0 X1 sK1 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 X1 sK1 sK1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2 X1]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1]; rw [← h3370 X0 sK0 (sK1 ◇ sK2)]
  have l9 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 (sK1 ◇ sK2) X0]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l2 sK0 sK2 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK1 sK2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation3370_4512_implies_Equation4369 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4369 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK2) sK0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK2 sK1 sK1]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK0 sK1 sK1]
  have l3 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK1 ◇ sK0)) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK0) sK2 sK2]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h3370 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l5 : ∀ sK1 sK2 sK0 X1 X0 : G, (((sK1 ◇ sK2) ◇ sK0) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [h3370 ((sK1 ◇ sK2) ◇ sK0) X1 X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK2 X0]
  have l6 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK1 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X1]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK2]
  have l8 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK0]
  have l9 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [h3370 sK2 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK2 sK1 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK1)]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK2) ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2 X1]
  have l13 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 X1]
  have l14 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (X1 ◇ X0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h3370 X0 (sK1 ◇ sK2) X1]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3370 sK2 (sK1 ◇ sK2) sK1]
  have l16 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l17 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1]; rw [← h3370 X0 sK0 (sK1 ◇ sK2)]
  have l18 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 (sK1 ◇ sK2) X0]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 sK1 (sK1 ◇ sK2)]
  have l20 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h3370 X0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 sK2 sK1]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l20 sK0 sK2 sK1 sK2]
  have l23 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1, 1]; rw [l16 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l24 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l23 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 sK2 X0]
  have l25 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l22 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← l25 sK2 sK0 sK1 X0]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0 X0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1 X0 sK1]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK0 sK2 sK1 sK2]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l9 sK2 sK2 sK1 sK0]
  have l30 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  have l31 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 sK2]
    conv => enter [1]; rw [← l28 sK1 sK2 sK0]
  have l32 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l30 sK1 sK2 sK1]
    conv => enter [1]; rw [← l9 sK2 (sK1 ◇ sK2) sK1 sK1]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [← l31 sK1 sK0 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ sK0)]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l35 sK0 sK1 sK2]
  have l37 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l36 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l6 X0 (sK1 ◇ sK0) sK0 sK1 sK2]
  have l38 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l37 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [l13 sK1 sK2 sK0 X0]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l38 sK2 sK1 sK0 X0]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l32 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l41 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l16 sK1 sK0 sK2]
    conv => enter [1]; rw [← l40 sK0 sK2 sK1]
  have l42 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l41 sK1 sK0 sK2]
    conv => enter [1]; rw [l20 sK0 sK2 sK1 sK2]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 sK1]
  have l44 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l42 sK1 sK0 sK2]
  have l45 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l43 sK0 sK1]
  have l46 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
  have l48 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l45 sK1 sK0 sK2]
    conv => enter [1]; rw [l33 sK1 sK0 sK2]
  have l49 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK0]
  have l50 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [l39 sK2 sK1 sK0 sK0]
  have l51 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
    conv => enter [1]; rw [l44 sK0 sK1 sK2 sK0]
  have l52 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK0]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2]
  have l53 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← l52 sK1 sK2 sK1]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l53 sK1 sK2 sK0]
    conv => enter [1]; rw [← l48 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l54 x y z]

theorem Equation3370_4512_implies_Equation40 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK1 sK1 sK1]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X3 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h3370 X3 (X0 ◇ X1) X2]
  have l2 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [h3370 X0 X1 X3]
    conv => enter [1]; rw [l1 X3 X1 X3 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h3370 X0 sK0 X1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK1]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3370 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3370 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK1 (sK1 ◇ sK1)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3370 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK0 X0 X0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2]; rw [l11 sK1 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l12 sK1 X0 sK0]
  have l14 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3370 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ sK1) sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0) sK1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation3370_4512_implies_Equation4273 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4273 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK0) sK0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK0 ◇ sK1)) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK1) sK1 sK1]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 sK0 X0 sK0]
    conv => enter [1]; rw [l5 X0 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3370 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h3370 (sK0 ◇ sK1) sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h3370 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3370 sK0 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [l12 sK1 sK0]
  have l14 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ X0))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l13 sK0 X0 sK1]
    conv => enter [1]; rw [← h3370 (sK1 ◇ (sK0 ◇ sK1)) X1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK1]
  have l16 : ∀ sK0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X1 sK0]
    conv => enter [1]; rw [l14 X1 sK0 sK0 sK1]
  have l17 : ∀ sK0 X1 sK1 : G, (sK0 ◇ X1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l6 sK0 X1]
    conv => enter [1]; rw [l16 sK0 X1 sK1]
  have l18 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X1 X0]
    conv => enter [1, 2, 2]; rw [← l15 sK0 sK1 X0]
  have l19 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK0) ◇ X1) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h3370 (sK1 ◇ sK0) X1 X0]
  have l20 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) = (sK1 ◇ (sK0 ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l19 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 X1]
  have l21 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ sK1) ◇ X1) = (sK1 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l18 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [l20 X1 sK0 sK0 sK1]
  have l22 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 ((sK0 ◇ sK1) ◇ sK1) X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0 X0]
  have l23 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ X0))) = (((sK0 ◇ sK1) ◇ sK1) ◇ X1) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l17 sK0 X0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 X1 X0]
  have l24 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l23 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X1]
  have l25 : ∀ sK0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X1 sK0]
    conv => enter [1]; rw [l24 X1 sK0 sK0 sK1]
  have l26 : ∀ sK0 X1 sK1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l6 sK0 X1]
    conv => enter [1]; rw [l25 sK0 X1 sK1]
  have l27 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3370 X0 sK1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK0 ◇ X0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l27 (sK0 ◇ sK1) sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation3370_4512_implies_Equation4297 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4297 G := by
  have l0 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK1 X0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK2 ◇ sK2)) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ sK2) sK1 sK1]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 sK2 sK2 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3370 sK1 (sK2 ◇ sK2) sK0]
    conv => enter [1]; rw [l2 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [h3370 (sK2 ◇ sK2) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l6 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 (sK2 ◇ sK2)]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l6 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l8 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = (((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro X1 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l7 sK1 X0 sK2]
    conv => enter [1]; rw [← h3370 ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) X1 X0]
  have l9 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l8 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2)) X1]
  have l10 : ∀ sK0 sK1 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [l9 X1 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l5 sK1 sK2 X0]
  have l12 : ∀ sK2 X0 sK1 sK0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK2 X0 sK1 sK0 X1
    conv => enter [1, 2]; rw [h3370 X0 (sK1 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1]; rw [← l10 sK0 sK1 (X1 ◇ (X1 ◇ X0)) sK2]
  have l13 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h3370 X0 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l10 sK0 sK1 ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) sK2]
  have l14 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3370 X0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l12 sK2 X0 sK1 sK0 X0]
  have l15 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3370 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l13 ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) sK2 sK0 sK1]
  have l16 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l15 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) X0 (sK2 ◇ sK2)]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 X0 X0]
  have l18 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 sK1 X0 sK0]
    conv => enter [1]; rw [l17 X0 sK0 sK1]
  have l19 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l18 sK1 (X0 ◇ (X0 ◇ X1)) sK0]
    conv => enter [1]; rw [← h3370 X1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l20 : ∀ X1 sK1 sK0 : G, (X1 ◇ sK1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [h3370 X1 sK1 X1]
    conv => enter [1]; rw [l19 sK1 X1 X1 sK0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l23 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK1) X1 sK0]
  have l24 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l18 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← h3370 (sK2 ◇ sK2) sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h3370 X0 sK0 sK1]
  have l27 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l23 sK0 sK1 sK1 X0]
    conv => enter [1]; rw [l26 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK0]
  have l29 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l2 sK2 X0]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h3370 sK2 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ (sK2 ◇ sK2))]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [← l16 sK2 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2 sK1]
    conv => enter [1]; rw [← h3370 sK1 sK2 sK1]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l32 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK2]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l5 sK1 sK2 sK2]
    conv => enter [1]; rw [← l33 sK1 sK2]
  have l35 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ (sK2 ◇ sK2)) X0 sK2]
    conv => enter [1, 2, 2]; rw [l34 sK2 sK1]
  have l36 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l35 sK1 sK2 X0]
  have l37 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l18 sK1 X0 sK1]
    conv => enter [1]; rw [l36 sK1 sK1 X0 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l37 sK1 (sK0 ◇ sK1) sK2]
  have l39 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l39 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l41 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l40 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [l27 sK0 sK0 X0]
  have l42 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l41 sK0 sK2 X0]
  have l43 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [← l4 sK2 (sK0 ◇ sK1) sK0 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l42 sK0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l43 sK1 sK0 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK2 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 sK1]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK2 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l21 sK0 sK1 sK0]
    conv => enter [1]; rw [← l46 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

theorem Equation3370_4512_implies_Equation4290 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation4290 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation3388_implies_Equation3334 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3334 G := by
  have l0 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 sK1
    conv => enter [1, 2, 2]; rw [h3388 sK2 sK1 sK2]
    conv => enter [1]; rw [← h3388 X0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3388 X0 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3388_implies_Equation3414 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3414 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3388 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← h3388 X0 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3388 sK1 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3388_implies_Equation4362 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation4362 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3388 X0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1, 2, 2]; rw [← h3388 sK0 sK2 sK1]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h3388 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3388 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation3388_implies_Equation4275 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation4275 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3388 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h3388 X0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3388_implies_Equation4320 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation4320 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3388 X0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← h3388 sK0 sK0 sK1]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3388 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3388 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3331_4512_implies_Equation3323 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation3323 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h3331 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ sK2) sK2 sK2]
  have l1 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (X0 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h3331 X1 X0 ((sK2 ◇ sK2) ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l0 X0 sK2]
  have l2 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l1 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) sK2 (X0 ◇ sK2)]
  have l3 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l2 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ sK2) X0 sK2]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3331 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l3 X0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation3331_4512_implies_Equation3334 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3331 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ sK1) sK2 sK1]
  have l1 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3331 X0 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ (sK2 ◇ sK1)) sK2 (sK2 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h4512 X0 ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) X1]
    conv => enter [1, 1]; rw [← l1 X0 sK2 sK1]
  have l3 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [l2 X0 sK2 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK1) X1]
  have l4 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← l3 X0 sK2 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) sK2 X1]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3331 sK2 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3331 X0 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l5 sK2 sK1]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l4 X0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l6 X0 sK2 sK1]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3331_4512_implies_Equation4358 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4358 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3331 X0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3331 (sK1 ◇ sK2) sK1 sK2]
  have l1 : ∀ X0 sK2 X1 sK1 : G, ((X0 ◇ sK2) ◇ X1) = (X0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ X1)) := by
    intro X0 sK2 X1 sK1
    conv => enter [1, 1]; rw [l0 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ sK2) ◇ sK1) X1]
  have l2 : ∀ X0 sK2 X1 sK1 : G, ((X0 ◇ sK2) ◇ X1) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X1))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l1 X0 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK1 X1]
  have l3 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X1))) = (X0 ◇ (sK2 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l2 X0 sK2 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 sK2 X1]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h3331 sK1 sK1 sK2]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3331 X0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l4 sK1 sK2]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1]; rw [l3 X0 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation3331_4512_implies_Equation4270 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4270 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3331 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3331 X0 sK0 sK0]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3331 X1 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h3331 X0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l1 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0)]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l2 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l0 (sK0 ◇ sK0) X0 sK0]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3331 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l3 X0 X0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x x y]

theorem Equation3331_4512_implies_Equation4283 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4283 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3331 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3331 (sK0 ◇ sK1) sK0 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X1)) = ((X0 ◇ sK1) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK1) ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l0 X0 sK1 sK0]
  have l2 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l1 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 sK1 X1]
  have l3 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [← l2 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3331 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3331 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [← l3 X0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x x y]

@[equational_result]
theorem Equation4271_implies_Equation4339 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4339 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4360 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4360 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK3]
    conv => enter [1]; rw [h4271 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation4271_implies_Equation4286 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4286 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4318 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4318 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4271_implies_Equation4288 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4288 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4269 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4271 x y x]

@[equational_result]
theorem Equation4271_implies_Equation4358 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4358 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4314 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4314 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation4271_implies_Equation4270 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4271 x y y]

@[equational_result]
theorem Equation4271_implies_Equation4283 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4283 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation4271_implies_Equation4284 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4284 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x x y]

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
theorem Equation4278_implies_Equation4300 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4300 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4278_implies_Equation4360 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4360 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK1 sK0]
  have l2 : ∀ sK1 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z x w]

@[equational_result]
theorem Equation4278_implies_Equation4296 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4296 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4278 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y y z]

@[equational_result]
theorem Equation4278_implies_Equation4327 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4327 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4278 sK0 sK2 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK0]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x x y]

@[equational_result]
theorem Equation4278_implies_Equation4304 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4304 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK2 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4278 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4278_implies_Equation4269 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4278 x x y]

@[equational_result]
theorem Equation4278_implies_Equation4362 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4362 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4278 sK2 X0 sK1]
    conv => enter [1]; rw [h4278 sK2 X1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4278 sK2 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z y x]

@[equational_result]
theorem Equation4278_implies_Equation4291 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4291 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y y]

@[equational_result]
theorem Equation4278_implies_Equation4275 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [h4278 x y y]

@[equational_result]
theorem Equation4278_implies_Equation4284 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4284 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK1]
    conv => enter [1]; rw [h4278 sK1 X1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y x]

@[equational_result]
theorem Equation4278_implies_Equation4320 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4320 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x x]

@[equational_result]
theorem Equation4278_implies_Equation4272 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4278 x y x]

@[equational_result]
theorem Equation4274_implies_Equation4271 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 x y z x]

@[equational_result]
theorem Equation4274_implies_Equation4278 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4278 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x x]

@[equational_result]
theorem Equation4274_implies_Equation4301 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4301 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4274 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z z]

@[equational_result]
theorem Equation4274_implies_Equation4331 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4331 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4305 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4305 G := by
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
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 z y z x y]

@[equational_result]
theorem Equation4274_implies_Equation4325 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4325 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y x y z]

@[equational_result]
theorem Equation4274_implies_Equation4364 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4364 G := by
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
  have l4 : ∀ sK0 sK1 sK2 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X1 X2]
  have l5 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK0]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z y z x]

@[equational_result]
theorem Equation4274_implies_Equation4369 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4369 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z z x]

@[equational_result]
theorem Equation4274_implies_Equation4279 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z y x]

@[equational_result]
theorem Equation4274_implies_Equation4273 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [h4274 x y y]

@[equational_result]
theorem Equation4274_implies_Equation4299 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4299 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK2 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x x y]

@[equational_result]
theorem Equation4274_implies_Equation4297 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4297 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x x y y z]

@[equational_result]
theorem Equation4274_implies_Equation4277 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y y z x]

@[equational_result]
theorem Equation4274_implies_Equation4280 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4290 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4290 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x x]

@[equational_result]
theorem Equation4274_implies_Equation4321 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4321 G := by
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
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK0 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y x y x]

@[equational_result]
theorem Equation4274_implies_Equation4293 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4293 G := by
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
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x x y y x]

@[equational_result]
theorem Equation4274_implies_Equation4343 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4343 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4274 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4274 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK0) sK0 sK1]
  have l5 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [h4274 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 X0 sK0 X1 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK0 sK1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y y]

@[equational_result]
theorem Equation4274_implies_Equation4276 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4276 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4274 sK1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4274 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4274 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4277_implies_Equation4275 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4275 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h4277 X1 X1 X2]
    conv => enter [1]; rw [h4277 X1 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4277_implies_Equation4268 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4268 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4277 X1 X1 X2]
    conv => enter [1]; rw [h4277 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4277_implies_Equation4293 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4293 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4277 sK0 sK0 sK1]
    conv => enter [1]; rw [h4277 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4277_implies_Equation4276 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h4277 x y y]

@[equational_result]
theorem Equation4280_implies_Equation4270 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4280 x x y]

@[equational_result]
theorem Equation4280_implies_Equation4272 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4280 x y x]

@[equational_result]
theorem Equation4280_implies_Equation4343 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4343 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y y]

@[equational_result]
theorem Equation4280_implies_Equation4276 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h4280 x y y]

@[equational_result]
theorem Equation4279_implies_Equation4273 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4273 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4279_implies_Equation4269 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4269 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4279_implies_Equation4321 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4279_implies_Equation4276 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h4279 x y y]

@[equational_result]
theorem Equation4286_implies_Equation4269 (G : Type*) [Magma G] (h4286 : Equation4286 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4286 sK0 sK0 sK1]
    conv => enter [1]; rw [h4286 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4286_implies_Equation4283 (G : Type*) [Magma G] (h4286 : Equation4286 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4286 sK0 sK0 sK1]
    conv => enter [1]; rw [h4286 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4286 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4286_implies_Equation4268 (G : Type*) [Magma G] (h4286 : Equation4286 G) : Equation4268 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h4286 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4286 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4327_implies_Equation4269 (G : Type*) [Magma G] (h4327 : Equation4327 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4327 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4327_implies_Equation4320 (G : Type*) [Magma G] (h4327 : Equation4327 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [h4327 x y y]

@[equational_result]
theorem Equation4327_implies_Equation4272 (G : Type*) [Magma G] (h4327 : Equation4327 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4327 x x y]

@[equational_result]
theorem Equation4360_implies_Equation4269 (G : Type*) [Magma G] (h4360 : Equation4360 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4360 x x x y]

@[equational_result]
theorem Equation4360_implies_Equation4284 (G : Type*) [Magma G] (h4360 : Equation4360 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [h4360 x x y y]

@[equational_result]
theorem Equation4288_implies_Equation4270 (G : Type*) [Magma G] (h4288 : Equation4288 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4288 x x y]

@[equational_result]
theorem Equation4288_implies_Equation4284 (G : Type*) [Magma G] (h4288 : Equation4288 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [h4288 x y y]

@[equational_result]
theorem Equation4288_implies_Equation4268 (G : Type*) [Magma G] (h4288 : Equation4288 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h4288 x y x]

@[equational_result]
theorem Equation4304_implies_Equation4275 (G : Type*) [Magma G] (h4304 : Equation4304 G) : Equation4275 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4304 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4304_implies_Equation4284 (G : Type*) [Magma G] (h4304 : Equation4304 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [h4304 x y x]

@[equational_result]
theorem Equation4304_implies_Equation4272 (G : Type*) [Magma G] (h4304 : Equation4304 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4304 x x y]

@[equational_result]
theorem Equation4296_implies_Equation4269 (G : Type*) [Magma G] (h4296 : Equation4296 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4296 sK0 sK0 sK1]
    conv => enter [1]; rw [h4296 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4296_implies_Equation4291 (G : Type*) [Magma G] (h4296 : Equation4296 G) : Equation4291 G := by
  intro x y
  conv => enter [1]; rw [h4296 x y x]

@[equational_result]
theorem Equation4296_implies_Equation4275 (G : Type*) [Magma G] (h4296 : Equation4296 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h4296 y x x]

@[equational_result]
theorem Equation4318_implies_Equation4269 (G : Type*) [Magma G] (h4318 : Equation4318 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4318 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4318_implies_Equation4314 (G : Type*) [Magma G] (h4318 : Equation4318 G) : Equation4314 G := by
  intro x y
  conv => enter [1]; rw [h4318 x y y]

@[equational_result]
theorem Equation4318_implies_Equation4270 (G : Type*) [Magma G] (h4318 : Equation4318 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4318 x x y]

@[equational_result]
theorem Equation4297_implies_Equation4270 (G : Type*) [Magma G] (h4297 : Equation4297 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4297 x x y]

@[equational_result]
theorem Equation4297_implies_Equation4275 (G : Type*) [Magma G] (h4297 : Equation4297 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h4297 y x x]

@[equational_result]
theorem Equation4297_implies_Equation4290 (G : Type*) [Magma G] (h4297 : Equation4297 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [h4297 x y x]

theorem Equation4299_4512_implies_Equation4297 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4297 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4299 sK2 sK2 X0]
    conv => enter [1]; rw [h4299 sK2 sK2 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4299 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4299 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 (sK0 ◇ sK0)]
  have l3 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h4299 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 X0]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l4 X1 sK0 sK1 sK0]
  have l6 : ∀ X2 X1 X0 sK2 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 X0 sK2
    conv => enter [1]; rw [← h4299 X1 (sK2 ◇ sK2) X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 X0]
  have l7 : ∀ X2 X1 sK1 sK2 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 sK1 sK2
    conv => enter [1]; rw [l6 X2 X1 X2 sK2]
    conv => enter [1, 2]; rw [l0 X2 sK2 sK1]
  have l8 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l3 X1 X1 sK0 sK1]
    conv => enter [1]; rw [l7 X1 X1 sK1 sK2]
  have l9 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X1]
    conv => enter [1]; rw [l8 X1 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l7 X1 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y y z]

theorem Equation4299_4512_implies_Equation4288 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4288 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4299 sK2 sK2 X0]
    conv => enter [1]; rw [h4299 sK2 sK2 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4299 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4299 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 (sK0 ◇ sK0)]
  have l3 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h4299 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 X0]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l4 X1 sK0 sK1 sK0]
  have l6 : ∀ X2 X1 X0 sK2 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 X0 sK2
    conv => enter [1]; rw [← h4299 X1 (sK2 ◇ sK2) X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 X0]
  have l7 : ∀ X1 sK0 sK1 X0 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l3 X1 X1 sK0 sK1]
    conv => enter [1]; rw [l6 X1 X1 X0 sK2]
  have l8 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l7 X1 sK0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [l0 X1 sK2 sK0]
  have l9 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X1]
    conv => enter [1]; rw [l8 X1 sK0 sK1 sK2]
  have l10 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← h4299 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK0]
  have l11 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l10 X1 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y x z]

theorem Equation4299_4512_implies_Equation4304 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4304 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4299 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4299 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 (sK0 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK0]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4299 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l4 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4299_4512_implies_Equation4277 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4277 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h4299 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK0 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4299 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4299 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4299 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK1 sK2 (sK1 ◇ sK1)]
  have l3 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [← h4299 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 2]; rw [← h4299 sK1 sK2 X0]
  have l4 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l0 X0 X0 sK0]
    conv => enter [1]; rw [l3 X0 X0 sK1 sK2]
  have l5 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l6 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1]; rw [← l5 X1 sK1 sK2 sK1]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4299 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 X0 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation4299_implies_Equation4280 (G : Type*) [Magma G] (h4299 : Equation4299 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4299 sK2 sK2 sK1]
    conv => enter [1]; rw [h4299 sK2 sK2 X0]
  have l2 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h4299 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h4299 sK0 sK0 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l0 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 X0 X2]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h4299 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK0 X0]
  have l7 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l5 X1 sK0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation4300_implies_Equation4291 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4291 G := by
  intro x y
  conv => enter [1]; rw [h4300 x y y]

@[equational_result]
theorem Equation4300_implies_Equation4272 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4300 x x y]

@[equational_result]
theorem Equation4339_implies_Equation4314 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4314 G := by
  intro x y
  conv => enter [1]; rw [← h4339 x y x]

@[equational_result]
theorem Equation4339_implies_Equation4268 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [h4339 x x y]

@[equational_result]
theorem Equation4301_implies_Equation4305 (G : Type*) [Magma G] (h4301 : Equation4301 G) : Equation4305 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4301 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4301 sK1 X0 (sK0 ◇ sK1)]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4301 sK1 sK2 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4301 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4301_4512_implies_Equation4286 (G : Type*) [Magma G] (h4301 : Equation4301 G) (h4512 : Equation4512 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4301 sK0 X0 sK0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 X0]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4301 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 X0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l13 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0]
  have l14 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l13 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l14 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l16 : ∀ X2 X0 sK0 sK1 : G, (X2 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X2 X0 sK0 sK1
    conv => enter [1]; rw [← h4301 X0 X2 X2]
    conv => enter [1]; rw [l15 X0 X2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l16 x z x y]

theorem Equation4301_4512_implies_Equation4296 (G : Type*) [Magma G] (h4301 : Equation4301 G) (h4512 : Equation4512 G) : Equation4296 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4301 sK0 X0 sK0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 X0]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4301 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 X0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l13 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0]
  have l14 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l13 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ X2 X0 sK0 sK1 : G, (X2 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X2 X0 sK0 sK1
    conv => enter [1]; rw [← h4301 X0 X2 X2]
    conv => enter [1]; rw [l14 X0 X2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l15 y z x y]

theorem Equation4301_4512_implies_Equation4279 (G : Type*) [Magma G] (h4301 : Equation4301 G) (h4512 : Equation4512 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4301 sK0 X0 (sK0 ◇ X1)]
    conv => enter [1, 2]; rw [h4301 sK0 X1 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4301 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK0 X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← h4301 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X2 X0 sK0 : G, (X2 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X2 X0 sK0
    conv => enter [1]; rw [← h4301 X0 X2 X2]
    conv => enter [1]; rw [l6 X0 X2 sK0]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

theorem Equation4301_4512_implies_Equation4277 (G : Type*) [Magma G] (h4301 : Equation4301 G) (h4512 : Equation4512 G) : Equation4277 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4301 sK0 X0 (sK0 ◇ X1)]
    conv => enter [1, 2]; rw [h4301 sK0 X1 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4301 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4301 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK0 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4301 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation4331_implies_Equation4325 (G : Type*) [Magma G] (h4331 : Equation4331 G) : Equation4325 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4331 sK2 sK2 X0]
    conv => enter [1]; rw [h4331 sK2 sK2 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4331 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4331 X0 sK1 sK0]
  have l2 : ∀ X2 X1 sK2 X0 : G, (X2 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 sK2 X0
    conv => enter [1]; rw [← h4331 (sK2 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 X0]
  have l3 : ∀ X2 X1 sK2 sK1 : G, (X2 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 sK2 sK1
    conv => enter [1]; rw [l2 X2 X1 sK2 X2]
    conv => enter [1, 2]; rw [l0 X2 sK2 sK1]
  have l4 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [← h4331 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK2) sK1 sK0]
  have l5 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ sK2) sK2 sK1]
    conv => enter [1]; rw [l4 sK2 sK2 sK1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK2 sK1 sK0]
  have l7 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l3 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK2 sK1]
    conv => enter [1]; rw [l7 sK2 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l10 X0 sK0 sK1]
  have l12 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l12 X1 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l13 x y y z]

@[equational_result]
theorem Equation4331_implies_Equation4318 (G : Type*) [Magma G] (h4331 : Equation4331 G) : Equation4318 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4331 sK2 sK2 X0]
    conv => enter [1]; rw [h4331 sK2 sK2 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4331 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4331 X0 sK1 sK0]
  have l2 : ∀ X2 X1 sK2 X0 : G, (X2 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 sK2 X0
    conv => enter [1]; rw [← h4331 (sK2 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 X0]
  have l3 : ∀ X2 X1 sK2 sK0 : G, (X2 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 sK2 sK0
    conv => enter [1]; rw [l2 X2 X1 sK2 X2]
    conv => enter [1, 2]; rw [l0 X2 sK2 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l5 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ sK2) sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK2 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK0 sK1]
  have l8 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2]
  have l9 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l3 sK2 (sK0 ◇ (sK2 ◇ sK2)) sK2 sK0]
    conv => enter [1]; rw [l8 sK2 sK0 sK2 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK1]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l11 X0 sK0 sK1]
  have l13 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l13 X1 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l14 x y x z]

@[equational_result]
theorem Equation4331_implies_Equation4327 (G : Type*) [Magma G] (h4331 : Equation4331 G) : Equation4327 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h4331 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4331 sK0 sK0 X0]
  have l1 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1, 2]; rw [← h4331 sK0 sK0 sK2]
    conv => enter [1]; rw [← l0 X1 X0 sK0]
  have l2 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4331 sK0 sK0 sK2]
    conv => enter [1]; rw [h4331 sK0 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4331 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4331 X0 sK1 sK0]
  have l4 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X1]
    conv => enter [1, 2]; rw [h4331 (sK1 ◇ sK0) sK0 X0]
  have l5 : ∀ X1 sK1 sK0 sK2 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK1 sK0 sK2
    conv => enter [1]; rw [l4 X1 sK1 sK0 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0 sK2]
  have l6 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK2]
  have l8 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← h4331 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 sK0 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK2 sK1]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
  have l12 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 X0 sK2 sK0 sK1]
  have l14 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l13 sK0 sK1 sK0 sK2]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 sK1]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l16 X0 sK0 sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4331 (sK1 ◇ sK0) sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

@[equational_result]
theorem Equation4331_implies_Equation4279 (G : Type*) [Magma G] (h4331 : Equation4331 G) : Equation4279 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [h4331 sK0 sK0 X0]
    conv => enter [1]; rw [h4331 (sK0 ◇ sK0) X0 X1]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4331 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4331 X0 sK2 sK1]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4331 (sK0 ◇ sK0) sK0 sK0]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [h4331 (sK0 ◇ sK0) sK0 X0]
  have l4 : ∀ X1 sK0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l3 X1 sK0 X1]
    conv => enter [1, 2]; rw [← h4331 sK0 sK0 X1]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [h4331 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK0 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation4331_implies_Equation4280 (G : Type*) [Magma G] (h4331 : Equation4331 G) : Equation4280 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [h4331 sK0 sK0 X0]
    conv => enter [1]; rw [h4331 (sK0 ◇ sK0) X0 X1]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4331 (sK0 ◇ sK0) sK0 sK0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [h4331 (sK0 ◇ sK0) sK0 X0]
  have l3 : ∀ X1 sK0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l2 X1 sK0 X1]
    conv => enter [1, 2]; rw [← h4331 sK0 sK0 X1]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4331 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h4331 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 X1 X0 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK2 sK2]
    conv => enter [1]; rw [h4331 sK2 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation4305_implies_Equation4273 (G : Type*) [Magma G] (h4305 : Equation4305 G) : Equation4273 G := by
  have l0 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [← h4305 sK1 sK0 sK1]
    conv => enter [1]; rw [h4305 sK1 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4305_implies_Equation4275 (G : Type*) [Magma G] (h4305 : Equation4305 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h4305 y x x]

@[equational_result]
theorem Equation4305_implies_Equation4283 (G : Type*) [Magma G] (h4305 : Equation4305 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4305 sK0 sK1 sK0]
    conv => enter [1]; rw [h4305 sK0 sK1 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4305 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4325_implies_Equation4273 (G : Type*) [Magma G] (h4325 : Equation4325 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [← h4325 y x x]

@[equational_result]
theorem Equation4325_implies_Equation4270 (G : Type*) [Magma G] (h4325 : Equation4325 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4325 x x y]

@[equational_result]
theorem Equation4325_implies_Equation4320 (G : Type*) [Magma G] (h4325 : Equation4325 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [h4325 x y x]

@[equational_result]
theorem Equation4358_implies_Equation4283 (G : Type*) [Magma G] (h4358 : Equation4358 G) : Equation4283 G := by
  intro x y
  conv => enter [1]; rw [h4358 x x y]

@[equational_result]
theorem Equation4362_implies_Equation4320 (G : Type*) [Magma G] (h4362 : Equation4362 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [h4362 x y x]

@[equational_result]
theorem Equation4364_implies_Equation4283 (G : Type*) [Magma G] (h4364 : Equation4364 G) : Equation4283 G := by
  intro x y
  conv => enter [1]; rw [h4364 x x y]

@[equational_result]
theorem Equation4364_implies_Equation4320 (G : Type*) [Magma G] (h4364 : Equation4364 G) : Equation4320 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4364 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4364 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4364_implies_Equation4290 (G : Type*) [Magma G] (h4364 : Equation4364 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [← h4364 y x x]

@[equational_result]
theorem Equation4369_implies_Equation4290 (G : Type*) [Magma G] (h4369 : Equation4369 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [h4369 x x y]

theorem Equation4320_4343_implies_Equation4314 (G : Type*) [Magma G] (h4320 : Equation4320 G) (h4343 : Equation4343 G) : Equation4314 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h4343 X0 sK1]
    conv => enter [1]; rw [← h4320 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation4320_4343_4512_implies_Equation4321 (G : Type*) [Magma G] (h4320 : Equation4320 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4343 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4320 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4320 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4283_4293_implies_Equation4291 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4293 : Equation4293 G) : Equation4291 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h4293 X0 X1]
    conv => enter [1]; rw [h4283 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4283_4293_implies_Equation4321 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4293 : Equation4293 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4283 sK0 sK1]
    conv => enter [1]; rw [h4293 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4283 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4320_4321_implies_Equation4314 (G : Type*) [Magma G] (h4320 : Equation4320 G) (h4321 : Equation4321 G) : Equation4314 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [← h4320 sK1 X0]
    conv => enter [1]; rw [h4321 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation4320_4321_implies_Equation4343 (G : Type*) [Magma G] (h4320 : Equation4320 G) (h4321 : Equation4321 G) : Equation4343 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4320 sK0 X0]
    conv => enter [1]; rw [h4321 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4320 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4283_4321_implies_Equation4291 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4321 : Equation4321 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4283 sK0 sK1]
    conv => enter [1]; rw [h4321 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4283_4321_implies_Equation4293 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4321 : Equation4321 G) : Equation4293 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4283 sK1 sK0]
    conv => enter [1]; rw [h4321 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4283 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4314_4343_implies_Equation4320 (G : Type*) [Magma G] (h4314 : Equation4314 G) (h4343 : Equation4343 G) : Equation4320 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h4343 X0 sK0]
    conv => enter [1]; rw [← h4314 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation4291_4293_implies_Equation4283 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h4293 : Equation4293 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4293 sK0 sK1]
    conv => enter [1]; rw [h4291 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4314_4321_implies_Equation4320 (G : Type*) [Magma G] (h4314 : Equation4314 G) (h4321 : Equation4321 G) : Equation4320 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4314 X0 sK0]
    conv => enter [1]; rw [h4321 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation4291_4321_4512_implies_Equation4283 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4321 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4291 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4314_4320_implies_Equation4321 (G : Type*) [Magma G] (h4314 : Equation4314 G) (h4320 : Equation4320 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4320 sK0 sK1]
    conv => enter [1]; rw [← h4314 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4283_4291_implies_Equation4321 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4291 : Equation4291 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4283 sK0 sK1]
    conv => enter [1]; rw [h4291 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4291_4320_implies_Equation4284 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h4320 : Equation4320 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4291 sK0 sK1]
    conv => enter [1]; rw [h4320 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4283_4314_implies_Equation4284 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4314 : Equation4314 G) : Equation4284 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [← h4314 X0 sK1]
    conv => enter [1]; rw [← h4283 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation4291_4314_implies_Equation4290 (G : Type*) [Magma G] (h4291 : Equation4291 G) (h4314 : Equation4314 G) : Equation4290 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4291 sK0 sK1]
    conv => enter [1]; rw [h4314 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4290_4343_implies_Equation4284 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4343 : Equation4343 G) : Equation4284 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h4343 X0 sK1]
    conv => enter [1]; rw [← h4290 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation4290_4343_implies_Equation4293 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4343 : Equation4343 G) : Equation4293 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h4290 X0 X1]
    conv => enter [1]; rw [h4343 X1 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4290 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4290_4293_implies_Equation4284 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4293 : Equation4293 G) : Equation4284 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [← h4290 sK1 X0]
    conv => enter [1]; rw [h4293 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation4290_4293_implies_Equation4343 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4293 : Equation4293 G) : Equation4343 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4290 sK0 X0]
    conv => enter [1]; rw [h4293 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4290 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4290_4320_4512_implies_Equation4283 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4320 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4290 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4283_4290_implies_Equation4320 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4290 : Equation4290 G) : Equation4320 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4283 sK0 sK1]
    conv => enter [1]; rw [h4290 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4290_4314_implies_Equation4291 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4314 : Equation4314 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4290 sK0 sK1]
    conv => enter [1]; rw [← h4314 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4290_4291_implies_Equation4314 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4291 : Equation4291 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4291 sK1 sK0]
    conv => enter [1]; rw [h4290 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4284_4343_implies_Equation4290 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4343 : Equation4343 G) : Equation4290 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h4343 X0 sK0]
    conv => enter [1]; rw [← h4284 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation4284_4293_implies_Equation4290 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4293 : Equation4293 G) : Equation4290 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1]; rw [h4293 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation4284_4320_implies_Equation4291 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4320 : Equation4320 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4284 sK0 sK1]
    conv => enter [1]; rw [← h4320 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4283_4284_implies_Equation4314 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4284 : Equation4284 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4283 sK0 sK1]
    conv => enter [1]; rw [h4284 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4284_4314_4512_implies_Equation4283 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation4283 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4314 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation4284_4291_implies_Equation4320 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4291 : Equation4291 G) : Equation4320 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4291 sK1 sK0]
    conv => enter [1]; rw [h4284 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4284_4290_implies_Equation4293 (G : Type*) [Magma G] (h4284 : Equation4284 G) (h4290 : Equation4290 G) : Equation4293 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4290 sK0 sK1]
    conv => enter [1]; rw [← h4284 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4283_4320_implies_Equation4290 (G : Type*) [Magma G] (h4283 : Equation4283 G) (h4320 : Equation4320 G) : Equation4290 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4320 sK0 X0]
    conv => enter [1]; rw [← h4283 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation4364_4369_implies_Equation4358 (G : Type*) [Magma G] (h4364 : Equation4364 G) (h4369 : Equation4369 G) : Equation4358 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4364 sK2 X0 sK1]
    conv => enter [1]; rw [h4369 sK2 X0 sK1]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1]; rw [h4364 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4364_4369_implies_Equation4362 (G : Type*) [Magma G] (h4364 : Equation4364 G) (h4369 : Equation4369 G) : Equation4362 G := by
  have l0 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h4364 sK2 X0 sK0]
    conv => enter [1]; rw [h4369 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4362_4369_implies_Equation4364 (G : Type*) [Magma G] (h4362 : Equation4362 G) (h4369 : Equation4369 G) : Equation4364 G := by
  have l0 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h4362 X0 sK2 sK0]
    conv => enter [1]; rw [h4369 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation4358_4369_implies_Equation4364 (G : Type*) [Magma G] (h4358 : Equation4358 G) (h4369 : Equation4369 G) : Equation4364 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4369 X0 X1 X2]
    conv => enter [1]; rw [h4358 X2 X1 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4369 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 X0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4358 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4362_4364_implies_Equation4369 (G : Type*) [Magma G] (h4362 : Equation4362 G) (h4364 : Equation4364 G) : Equation4369 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4362 X0 sK1 sK0]
    conv => enter [1]; rw [← h4364 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4358_4364_implies_Equation4369 (G : Type*) [Magma G] (h4358 : Equation4358 G) (h4364 : Equation4364 G) : Equation4369 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4358 X0 sK1 sK0]
    conv => enter [1]; rw [h4364 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

end Semigroup5
