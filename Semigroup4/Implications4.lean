import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

@[equational_result]
theorem Equation3288_implies_Equation3258 (G : Type*) [Magma G] (h3288 : Equation3288 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [h3288 x x y]

@[equational_result]
theorem Equation3259_implies_Equation3253 (G : Type*) [Magma G] (h3259 : Equation3259 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3259 x x]

@[equational_result]
theorem Equation3271_implies_Equation3253 (G : Type*) [Magma G] (h3271 : Equation3271 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3271 x x]

@[equational_result]
theorem Equation3260_implies_Equation310 (G : Type*) [Magma G] (h3260 : Equation3260 G) : Equation310 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3260 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3260 sK1 X0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3260_implies_Equation3259 (G : Type*) [Magma G] (h3260 : Equation3260 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h3260 x y y]

@[equational_result]
theorem Equation3260_implies_Equation3254 (G : Type*) [Magma G] (h3260 : Equation3260 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h3260 x x y]

theorem Equation3274_4512_implies_Equation315 (G : Type*) [Magma G] (h3274 : Equation3274 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3274 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h3274 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X2 : G, (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [h3274 X0 X0 X0]
    conv => enter [1]; rw [← l1 X2 X0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3274 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3274 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3274 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3274 sK0 (sK1 ◇ sK0) sK1]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X1]
  have l6 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3274 sK0 X1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l11 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3274 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0 X0 X0]
  have l14 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l11 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ X1) X1]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l14 X1 X1 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ X1) X1]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 X0 sK0]
    conv => enter [1]; rw [← l10 sK0 X0 X0]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l16 X1 sK0]
    conv => enter [1]; rw [l15 X1 sK0 X0]
  have l18 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [l15 X1 sK0 X0]
  have l19 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l18 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
  have l20 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l17 sK0 X2 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l19 X1 X2 sK0 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation3274_implies_Equation3271 (G : Type*) [Magma G] (h3274 : Equation3274 G) : Equation3271 G := by
  intro x y
  conv => enter [1]; rw [h3274 x y y]

@[equational_result]
theorem Equation3274_implies_Equation3268 (G : Type*) [Magma G] (h3274 : Equation3274 G) : Equation3268 G := by
  intro x y
  conv => enter [1]; rw [h3274 x y x]

@[equational_result]
theorem Equation3261_implies_Equation3253 (G : Type*) [Magma G] (h3261 : Equation3261 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3261 x x]

@[equational_result]
theorem Equation3262_implies_Equation3253 (G : Type*) [Magma G] (h3262 : Equation3262 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3262 x x]

@[equational_result]
theorem Equation3281_implies_Equation3253 (G : Type*) [Magma G] (h3281 : Equation3281 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3281 x x]

@[equational_result]
theorem Equation3263_implies_Equation310 (G : Type*) [Magma G] (h3263 : Equation3263 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3263 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3263 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3263_implies_Equation3254 (G : Type*) [Magma G] (h3263 : Equation3263 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h3263 x x y]

theorem Equation3296_4512_implies_Equation315 (G : Type*) [Magma G] (h3296 : Equation3296 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h3296 (sK1 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h3296 sK0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3296 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 X0 X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2]; rw [h3296 sK0 X1 sK0]
    conv => enter [1]; rw [← h3296 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 X0 X1 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3296 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l7 : ∀ sK0 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0 sK1
    conv => enter [1, 1]; rw [h3296 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3296 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3296 X0 X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) X0 sK1]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0 (sK0 ◇ sK0) X0]
  have l12 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [← h3296 X0 X1 X2]
    conv => enter [1]; rw [l11 X0 sK0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3296 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0 (X0 ◇ X0) X0]
  have l14 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l16 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← l12 sK0 X0 X2 sK0]
    conv => enter [1]; rw [← l15 X0 X2 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l16 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation3296_implies_Equation3268 (G : Type*) [Magma G] (h3296 : Equation3296 G) : Equation3268 G := by
  intro x y
  conv => enter [1]; rw [h3296 x y x]

@[equational_result]
theorem Equation3264_implies_Equation3261 (G : Type*) [Magma G] (h3264 : Equation3264 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h3264 x y y]

@[equational_result]
theorem Equation3264_implies_Equation3255 (G : Type*) [Magma G] (h3264 : Equation3264 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h3264 x x y]

@[equational_result]
theorem Equation3264_implies_Equation3258 (G : Type*) [Magma G] (h3264 : Equation3264 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [h3264 x y x]

@[equational_result]
theorem Equation3265_implies_Equation3262 (G : Type*) [Magma G] (h3265 : Equation3265 G) : Equation3262 G := by
  intro x y
  conv => enter [1]; rw [h3265 x y y]

@[equational_result]
theorem Equation3265_implies_Equation3259 (G : Type*) [Magma G] (h3265 : Equation3265 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h3265 x y x]

@[equational_result]
theorem Equation3265_implies_Equation3255 (G : Type*) [Magma G] (h3265 : Equation3265 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h3265 x x y]

@[equational_result]
theorem Equation3292_implies_Equation3281 (G : Type*) [Magma G] (h3292 : Equation3292 G) : Equation3281 G := by
  intro x y
  conv => enter [1]; rw [h3292 x y y]

@[equational_result]
theorem Equation3292_implies_Equation3271 (G : Type*) [Magma G] (h3292 : Equation3292 G) : Equation3271 G := by
  intro x y
  conv => enter [1]; rw [h3292 x y x]

@[equational_result]
theorem Equation3292_implies_Equation3258 (G : Type*) [Magma G] (h3292 : Equation3292 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [h3292 x x y]

@[equational_result]
theorem Equation3266_implies_Equation310 (G : Type*) [Magma G] (h3266 : Equation3266 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3266 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3266 X0 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3284_4512_implies_Equation315 (G : Type*) [Magma G] (h3284 : Equation3284 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3284 sK0 X0 sK0]
    conv => enter [1]; rw [← h3284 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← l0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3284 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l0 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h3284 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1, 2]; rw [← h3284 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3284 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK0 X0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3284 X1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3284 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l11 X1 sK0]
    conv => enter [1]; rw [l9 X1 sK0 X0]
  have l13 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 X0 sK0 X1]
  have l14 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l13 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l15 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l12 sK0 X2 (sK0 ◇ X0)]
    conv => enter [1]; rw [l14 sK0 sK0 X0 X2]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation3267_implies_Equation3260 (G : Type*) [Magma G] (h3267 : Equation3267 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [h3267 x y x z]

@[equational_result]
theorem Equation3267_implies_Equation3265 (G : Type*) [Magma G] (h3267 : Equation3267 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [h3267 x y z y]

@[equational_result]
theorem Equation3267_implies_Equation3263 (G : Type*) [Magma G] (h3267 : Equation3267 G) : Equation3263 G := by
  intro x y z
  conv => enter [1]; rw [h3267 x y y z]

@[equational_result]
theorem Equation3267_implies_Equation3264 (G : Type*) [Magma G] (h3267 : Equation3267 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [h3267 x y z x]

@[equational_result]
theorem Equation3267_implies_Equation3257 (G : Type*) [Magma G] (h3267 : Equation3267 G) : Equation3257 G := by
  intro x y z
  conv => enter [1]; rw [h3267 x x y z]

@[equational_result]
theorem Equation3300_implies_Equation3274 (G : Type*) [Magma G] (h3300 : Equation3300 G) : Equation3274 G := by
  intro x y z
  conv => enter [1]; rw [h3300 x y x z]

@[equational_result]
theorem Equation3300_implies_Equation3292 (G : Type*) [Magma G] (h3300 : Equation3300 G) : Equation3292 G := by
  intro x y z
  conv => enter [1]; rw [h3300 x y z y]

@[equational_result]
theorem Equation3300_implies_Equation3296 (G : Type*) [Magma G] (h3300 : Equation3300 G) : Equation3296 G := by
  intro x y z
  conv => enter [1]; rw [h3300 x y z z]

@[equational_result]
theorem Equation3300_implies_Equation3264 (G : Type*) [Magma G] (h3300 : Equation3300 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [h3300 x x y z]

@[equational_result]
theorem Equation3300_implies_Equation3288 (G : Type*) [Magma G] (h3300 : Equation3300 G) : Equation3288 G := by
  intro x y z
  conv => enter [1]; rw [h3300 x y z x]

@[equational_result]
theorem Equation3269_implies_Equation3253 (G : Type*) [Magma G] (h3269 : Equation3269 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3269 x x]

@[equational_result]
theorem Equation3270_implies_Equation316 (G : Type*) [Magma G] (h3270 : Equation3270 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3270 X1 X2 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h3270 X0 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3270 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3270 X0 X0 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3270 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3270 sK0 sK0 sK0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3270 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3270 sK1 sK1 sK1]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3270 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [l4 y y]

@[equational_result]
theorem Equation3272_implies_Equation3253 (G : Type*) [Magma G] (h3272 : Equation3272 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3272 x x]

@[equational_result]
theorem Equation3279_implies_Equation3253 (G : Type*) [Magma G] (h3279 : Equation3279 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3279 x x]

theorem Equation3273_4512_implies_Equation316 (G : Type*) [Magma G] (h3273 : Equation3273 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h3273 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [h3273 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2]; rw [h3273 (X1 ◇ X2) X0 X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3273 X0 X1 (X2 ◇ (X0 ◇ X3))]
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3273 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [h3273 X0 sK0 sK0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [h3273 (X0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [l4 (X0 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3273_4512_implies_Equation3260 (G : Type*) [Magma G] (h3273 : Equation3273 G) (h4512 : Equation4512 G) : Equation3260 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h3273 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [h3273 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2]; rw [h3273 (X1 ◇ X2) X0 X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3273 X0 X1 (X2 ◇ (X0 ◇ X3))]
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3273 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [h3273 X0 sK0 sK0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h3273 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation3273_4512_implies_Equation3292 (G : Type*) [Magma G] (h3273 : Equation3273 G) (h4512 : Equation4512 G) : Equation3292 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h3273 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [h3273 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2]; rw [h3273 (X1 ◇ X2) X0 X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3273 X0 X1 (X2 ◇ (X0 ◇ X3))]
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3273 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [h3273 X0 sK0 sK0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h3273 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation3273_4512_implies_Equation3294 (G : Type*) [Magma G] (h3273 : Equation3273 G) (h4512 : Equation4512 G) : Equation3294 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h3273 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [h3273 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2]; rw [h3273 (X1 ◇ X2) X0 X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3273 X0 X1 (X2 ◇ (X0 ◇ X3))]
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3273 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [h3273 X0 sK0 sK0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h3273 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation3290_4512_implies_Equation316 (G : Type*) [Magma G] (h3290 : Equation3290 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3290 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3290 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h3290 X0 X1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← h3290 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l1 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h3290 (sK1 ◇ (sK1 ◇ sK1)) X0 (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← h3290 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [l0 y y]

theorem Equation3290_4512_implies_Equation3265 (G : Type*) [Magma G] (h3290 : Equation3290 G) (h4512 : Equation4512 G) : Equation3265 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3290 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3290 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [h3290 X0 X1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [← h3290 sK0 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l1 X0 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ sK0)]
  have l3 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l2 X0 X1 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 X0 X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h3290 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x x y z]

theorem Equation3290_4512_implies_Equation3274 (G : Type*) [Magma G] (h3290 : Equation3290 G) (h4512 : Equation4512 G) : Equation3274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3290 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3290 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h3290 X0 X1 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h3290 sK0 X0 (sK2 ◇ sK0)]
  have l2 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l1 X0 X1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK0)]
  have l3 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l2 X0 X1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ sK0)]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h3290 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation3290_implies_Equation3294 (G : Type*) [Magma G] (h3290 : Equation3290 G) : Equation3294 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3290 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3290 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3290 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3290 sK0 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h3290 sK1 sK1 sK2]
    conv => enter [1]; rw [h3290 sK1 X0 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h3290 sK1 sK1 sK2]
    conv => enter [1]; rw [h3290 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [h3290 sK1 sK1 sK2]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3290 sK1 X0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h3290 sK1 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 X0 sK2]
  have l6 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3290 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 (sK1 ◇ sK2)]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK2 sK1 sK1]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation3274_4512_implies_Equation3288 (G : Type*) [Magma G] (h3274 : Equation3274 G) (h4512 : Equation4512 G) : Equation3288 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h3274 X0 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h3274 (X1 ◇ X0) X2 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X2 : G, (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [h3274 X0 X0 X0]
    conv => enter [1]; rw [← l1 X2 X0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3274 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3274 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3274 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 X0]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l3 sK0 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l7 sK0 sK2]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [l9 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation3274_implies_Equation4272 (G : Type*) [Magma G] (h3274 : Equation3274 G) : Equation4272 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3274 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h3274 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3274 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3274 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 X0]
  intro x y
  conv => enter [1]; rw [l3 x x y]

theorem Equation3260_4512_implies_Equation3257 (G : Type*) [Magma G] (h3260 : Equation3260 G) (h4512 : Equation4512 G) : Equation3257 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h3260 X0 X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l4 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h3260 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l3 X0 X3 X0 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3260 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation3260_4512_implies_Equation4268 (G : Type*) [Magma G] (h3260 : Equation3260 G) (h4512 : Equation4512 G) : Equation4268 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3260 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3260 sK0 X0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h3260 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h3260 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l4 X0 X3 X0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3260 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x x]
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation3275_implies_Equation3289 (G : Type*) [Magma G] (h3275 : Equation3275 G) : Equation3289 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3275 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h3275 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h3275 (sK0 ◇ sK0) X0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3275 X0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [← h3275 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h3275 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation3275_implies_Equation316 (G : Type*) [Magma G] (h3275 : Equation3275 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3275 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h3275 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h3275 (sK0 ◇ sK0) X0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3275 X0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [← h3275 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation3275_implies_Equation3264 (G : Type*) [Magma G] (h3275 : Equation3275 G) : Equation3264 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3275 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h3275 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h3275 (sK0 ◇ sK0) X0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3275 X0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [← h3275 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h3275 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation3289_4512_implies_Equation3275 (G : Type*) [Magma G] (h3289 : Equation3289 G) (h4512 : Equation4512 G) : Equation3275 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3289 X1 (X0 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h3289 X0 X2 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X2 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← h3289 X1 X1 X0]
  have l3 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h3289 X0 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3289 sK0 (sK2 ◇ sK1) X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3289 X1 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [l2 (X1 ◇ X2) X0]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2 sK0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h3289 sK2 sK1 sK0]
    conv => enter [1]; rw [l3 sK2 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3276_4512_implies_Equation316 (G : Type*) [Magma G] (h3276 : Equation3276 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3276 X1 X2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3276 (X0 ◇ X0) X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1 X0]
    conv => enter [1]; rw [← h3276 (X0 ◇ X0) X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h3276 X1 X1 X1]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h3276 (sK0 ◇ sK0) X1 sK0]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation3280_implies_Equation316 (G : Type*) [Magma G] (h3280 : Equation3280 G) : Equation316 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3280 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3280 sK0 X0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3280 X0 X1 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3280 sK0 X0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 X0 sK0]
    conv => enter [1]; rw [← h3280 sK0 X0 sK0]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l3 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation3277_implies_Equation3291 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3291 G := by
  have l0 : ∀ X0 sK3 sK1 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK1 sK0 X1
    conv => enter [1]; rw [← h3277 sK3 X0 sK1 sK0]
    conv => enter [1]; rw [h3277 sK3 X1 sK1 sK0]
  have l1 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 sK0 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h3277 (sK3 ◇ (sK1 ◇ sK0)) X0 sK3 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK3 ◇ (sK1 ◇ sK0)) sK3 sK1 sK0 sK2]
  have l2 : ∀ X0 X1 sK3 sK1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK3 sK1 sK0 X2
    conv => enter [1]; rw [← h3277 X1 X0 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h3277 X1 X2 sK1 sK1]
  have l3 : ∀ X0 sK2 sK3 sK1 sK0 X2 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK3 sK1 sK0 X2 X1
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK1 sK0 X1]
    conv => enter [1]; rw [l2 X0 X1 sK3 sK1 sK0 X2]
  have l4 : ∀ sK2 sK3 sK1 sK0 X2 X1 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0 X2 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [l3 sK2 sK2 sK3 sK1 sK0 X2 X1]
  have l5 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h3277 X0 sK2 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [← l5 y z x w x]

@[equational_result]
theorem Equation3277_implies_Equation3267 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3267 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h3277 X0 X1 sK1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h3277 sK1 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3277 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h3277 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3277 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 sK1 sK1]
  have l3 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [h3277 sK2 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x x y z w]

@[equational_result]
theorem Equation3277_implies_Equation3300 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3300 G := by
  have l0 : ∀ X0 sK3 sK0 sK1 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK3 sK0 sK1 X1
    conv => enter [1]; rw [← h3277 sK3 X0 sK0 sK1]
    conv => enter [1]; rw [h3277 sK3 X1 sK0 sK1]
  have l1 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK0 sK1 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h3277 (sK3 ◇ (sK0 ◇ sK1)) X0 sK3 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK3 ◇ (sK0 ◇ sK1)) sK3 sK0 sK1 sK2]
  have l2 : ∀ X0 X1 sK3 sK0 sK1 X2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK3 sK0 sK1 X2
    conv => enter [1]; rw [← h3277 X1 X0 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h3277 X1 X2 sK1 sK1]
  have l3 : ∀ X0 sK2 sK3 sK0 sK1 X2 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK3 sK0 sK1 X2 X1
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK0 sK1 X1]
    conv => enter [1]; rw [l2 X0 X1 sK3 sK0 sK1 X2]
  have l4 : ∀ sK2 sK3 sK0 sK1 X2 X1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1 X2 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK2 sK3 sK0 sK1 X2 X1]
  have l5 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X0 ◇ X0) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h3277 X0 sK2 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [← l5 y z w x x]

@[equational_result]
theorem Equation3277_implies_Equation3273 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3273 G := by
  intro x y z
  conv => enter [1]; rw [h3277 x y y z]

@[equational_result]
theorem Equation3277_implies_Equation3290 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3290 G := by
  have l0 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h3277 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [h3277 sK2 X0 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h3277 (sK2 ◇ (sK0 ◇ sK2)) X0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK0 sK1]
  have l2 : ∀ X0 X1 sK2 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0 X2
    conv => enter [1]; rw [← h3277 X1 X0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h3277 X1 X2 sK0 sK0]
  have l3 : ∀ X0 sK1 sK2 sK0 X2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X2 X1
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [l2 X0 X1 sK2 sK0 X2]
  have l4 : ∀ sK1 sK2 sK0 X2 X1 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X2 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 sK2 sK0 X2 X1]
  have l5 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h3277 X0 X0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK1 sK2 sK0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l5 x y z x]

@[equational_result]
theorem Equation3277_implies_Equation3275 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3275 G := by
  intro x y z
  conv => enter [1]; rw [h3277 x y z y]

@[equational_result]
theorem Equation3291_implies_Equation3277 (G : Type*) [Magma G] (h3291 : Equation3291 G) : Equation3277 G := by
  have l0 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h3291 X0 X1 X2 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h3291 sK1 X0 X0 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h3291 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 sK1 sK1 sK1]
  have l2 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK3]
    conv => enter [1]; rw [h3291 sK3 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation3282_implies_Equation40 (G : Type*) [Magma G] (h3282 : Equation3282 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3282 X0 X0]
    conv => enter [1]; rw [← h3282 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3282_implies_Equation3256 (G : Type*) [Magma G] (h3282 : Equation3282 G) : Equation3256 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3282 X0 X0]
    conv => enter [1]; rw [← h3282 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h3282 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation3282_implies_Equation3278 (G : Type*) [Magma G] (h3282 : Equation3282 G) : Equation3278 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3282 X0 X0]
    conv => enter [1]; rw [← h3282 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h3282 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation3283_implies_Equation316 (G : Type*) [Magma G] (h3283 : Equation3283 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3283 X0 X0 X0]
    conv => enter [1]; rw [← h3283 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3283 X0 X1 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3283 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 X1]
  have l5 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l4 sK1 X1 sK0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 X1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation3298_implies_Equation316 (G : Type*) [Magma G] (h3298 : Equation3298 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3298 X0 X0 X0]
    conv => enter [1]; rw [← h3298 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X2))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h3298 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [l0 X2 sK1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation3284_implies_Equation3268 (G : Type*) [Magma G] (h3284 : Equation3284 G) : Equation3268 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3284 sK0 X0 sK0]
    conv => enter [1]; rw [← h3284 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← l0 X1 sK0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3284 sK0 X1 sK0]
    conv => enter [1, 2]; rw [l1 X1 sK0 X0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation3284_implies_Equation3288 (G : Type*) [Magma G] (h3284 : Equation3284 G) : Equation3288 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3284 sK0 X0 sK0]
    conv => enter [1]; rw [← h3284 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3284 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation3284_implies_Equation4272 (G : Type*) [Magma G] (h3284 : Equation3284 G) : Equation4272 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3284 sK0 X0 sK0]
    conv => enter [1]; rw [← h3284 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l0 X0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation3266_4512_implies_Equation3254 (G : Type*) [Magma G] (h3266 : Equation3266 G) (h4512 : Equation4512 G) : Equation3254 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3266 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3266 X0 (X1 ◇ X1) X1]
  have l1 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3266 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3266 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]
  conv => enter [1]; rw [l10 x y]

theorem Equation3266_4512_implies_Equation3257 (G : Type*) [Magma G] (h3266 : Equation3266 G) (h4512 : Equation4512 G) : Equation3257 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3266 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3266 X0 (X1 ◇ X1) X1]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3266 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3266_4512_implies_Equation4268 (G : Type*) [Magma G] (h3266 : Equation3266 G) (h4512 : Equation4512 G) : Equation4268 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3266 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3266 X0 (X1 ◇ X1) X1]
  have l1 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3266 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3266 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x x]
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation3285_implies_Equation3279 (G : Type*) [Magma G] (h3285 : Equation3285 G) : Equation3279 G := by
  intro x y
  conv => enter [1]; rw [h3285 x y x]

@[equational_result]
theorem Equation3285_implies_Equation40 (G : Type*) [Magma G] (h3285 : Equation3285 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3285 X0 X0 X0]
    conv => enter [1]; rw [← h3285 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3285_implies_Equation3282 (G : Type*) [Magma G] (h3285 : Equation3285 G) : Equation3282 G := by
  intro x y
  conv => enter [1]; rw [h3285 x y y]

@[equational_result]
theorem Equation3285_implies_Equation3255 (G : Type*) [Magma G] (h3285 : Equation3285 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h3285 x x y]

@[equational_result]
theorem Equation3293_implies_Equation3272 (G : Type*) [Magma G] (h3293 : Equation3293 G) : Equation3272 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3293 X0 X0 X0]
    conv => enter [1]; rw [← h3293 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3293 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation3293_implies_Equation40 (G : Type*) [Magma G] (h3293 : Equation3293 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3293 X0 X0 X0]
    conv => enter [1]; rw [← h3293 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3293_implies_Equation3282 (G : Type*) [Magma G] (h3293 : Equation3293 G) : Equation3282 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3293 X0 X0 X0]
    conv => enter [1]; rw [← h3293 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3293 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation3293_implies_Equation3258 (G : Type*) [Magma G] (h3293 : Equation3293 G) : Equation3258 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3293 X0 X0 X0]
    conv => enter [1]; rw [← h3293 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3293 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 X1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation3288_implies_Equation4272 (G : Type*) [Magma G] (h3288 : Equation3288 G) : Equation4272 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3288 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h3288 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l0 X0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation3257_4512_implies_Equation4268 (G : Type*) [Magma G] (h3257 : Equation3257 G) (h4512 : Equation4512 G) : Equation4268 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3257 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3257 sK0 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3257 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3257 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l7 x y]

theorem Equation3292_4512_implies_Equation3268 (G : Type*) [Magma G] (h3292 : Equation3292 G) (h4512 : Equation4512 G) : Equation3268 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3292 sK0 sK0 X0]
    conv => enter [1]; rw [← h3292 (sK0 ◇ sK0) X0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3292 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1, 2, 2]; rw [← h3292 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3292 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← h3292 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3292 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [l0 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3292_4512_implies_Equation3288 (G : Type*) [Magma G] (h3292 : Equation3292 G) (h4512 : Equation4512 G) : Equation3288 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3292 sK0 sK0 X0]
    conv => enter [1]; rw [← h3292 (sK0 ◇ sK0) X0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3292 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1, 2, 2]; rw [← h3292 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3292 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← h3292 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l0 X0 sK0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
    conv => enter [1]; rw [l0 sK1 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3265_4512_implies_Equation3254 (G : Type*) [Magma G] (h3265 : Equation3265 G) (h4512 : Equation4512 G) : Equation3254 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h3265 X2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h3265 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0
    conv => enter [1]; rw [l1 X2 X0 X2]
    conv => enter [1, 2]; rw [← h3265 X0 X2 X0]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 X0 sK0]
    conv => enter [1]; rw [l3 X0 X1 sK0]
  have l5 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l4 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l6 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l5 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l7 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l6 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3265 X1 (sK0 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK0 X0]
    conv => enter [1]; rw [l7 X1 (sK0 ◇ X0) sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation3265_4512_implies_Equation3257 (G : Type*) [Magma G] (h3265 : Equation3265 G) (h4512 : Equation4512 G) : Equation3257 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h3265 X2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h3265 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0
    conv => enter [1]; rw [l1 X2 X0 X2]
    conv => enter [1, 2]; rw [← h3265 X0 X2 X0]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 X0 sK0]
    conv => enter [1]; rw [l3 X0 X1 sK0]
  have l5 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l4 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l6 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l5 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l7 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l6 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3265 X1 (sK0 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK0 X0]
    conv => enter [1]; rw [l7 X1 (sK0 ◇ X0) sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation3293_implies_Equation316 (G : Type*) [Magma G] (h3293 : Equation3293 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3293 X0 X0 X0]
    conv => enter [1]; rw [← h3293 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3293 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3285_4512_implies_Equation316 (G : Type*) [Magma G] (h3285 : Equation3285 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3285 X0 X0 X0]
    conv => enter [1]; rw [← h3285 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h3285 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3285 X0 X1 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l2 sK1 X1 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3285 sK0 sK1 sK1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = ((X1 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3285 X0 (X1 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h3285 (sK0 ◇ sK0) sK1 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 X0]
  have l11 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l10 sK1 X1 sK0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 X1 sK0]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3285 X0 ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) X1]
    conv => enter [1, 2, 2]; rw [← l12 sK0 X1]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l14 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l15 X0 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l16 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [l1 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l17 sK1 sK0 X1]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 sK0 X1]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation3294_implies_Equation40 (G : Type*) [Magma G] (h3294 : Equation3294 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3294 X0 X0 X0]
    conv => enter [1]; rw [← h3294 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3294_implies_Equation3282 (G : Type*) [Magma G] (h3294 : Equation3294 G) : Equation3282 G := by
  intro x y
  conv => enter [1]; rw [h3294 x y y]

@[equational_result]
theorem Equation3294_implies_Equation3259 (G : Type*) [Magma G] (h3294 : Equation3294 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h3294 x x y]

@[equational_result]
theorem Equation3294_implies_Equation3271 (G : Type*) [Magma G] (h3294 : Equation3294 G) : Equation3271 G := by
  intro x y
  conv => enter [1]; rw [h3294 x y x]

@[equational_result]
theorem Equation3297_implies_Equation40 (G : Type*) [Magma G] (h3297 : Equation3297 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3297 X0 X0 X0]
    conv => enter [1]; rw [← h3297 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3297_implies_Equation3269 (G : Type*) [Magma G] (h3297 : Equation3297 G) : Equation3269 G := by
  intro x y
  conv => enter [1]; rw [h3297 x y x]

@[equational_result]
theorem Equation3297_implies_Equation3282 (G : Type*) [Magma G] (h3297 : Equation3297 G) : Equation3282 G := by
  intro x y
  conv => enter [1]; rw [h3297 x y y]

@[equational_result]
theorem Equation3297_implies_Equation3261 (G : Type*) [Magma G] (h3297 : Equation3297 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h3297 x x y]

@[equational_result]
theorem Equation3306_implies_Equation3253 (G : Type*) [Magma G] (h3306 : Equation3306 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3306 x x]

@[equational_result]
theorem Equation3319_implies_Equation3253 (G : Type*) [Magma G] (h3319 : Equation3319 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3319 x x]

@[equational_result]
theorem Equation3308_implies_Equation3253 (G : Type*) [Magma G] (h3308 : Equation3308 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3308 x x]

@[equational_result]
theorem Equation3346_implies_Equation3253 (G : Type*) [Magma G] (h3346 : Equation3346 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3346 x x]

@[equational_result]
theorem Equation3309_implies_Equation3253 (G : Type*) [Magma G] (h3309 : Equation3309 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3309 x x]

@[equational_result]
theorem Equation3312_implies_Equation3330 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3330 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3312 X0 (sK2 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 2, 2]; rw [← h3312 sK2 sK1 sK1]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3312 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3312_implies_Equation3334 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3334 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1, 2, 2]; rw [h3312 sK2 sK1 sK2]
    conv => enter [1]; rw [← h3312 X0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3312 X0 sK1 sK2]
    conv => enter [1]; rw [l0 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3312_implies_Equation3322 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3322 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3312 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← h3312 sK1 sK1 sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3312 X0 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3312_implies_Equation3326 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3326 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h3312 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h3312 sK2 sK1 sK0]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h3312 X0 (sK2 ◇ (sK0 ◇ sK1)) sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z x]

@[equational_result]
theorem Equation3312_implies_Equation3309 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3309 G := by
  intro x y
  conv => enter [1]; rw [h3312 x y y]

@[equational_result]
theorem Equation3312_implies_Equation4287 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation4287 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3312 sK0 (sK2 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h3312 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l0 x z y]

@[equational_result]
theorem Equation3312_implies_Equation4340 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation4340 G := by
  have l0 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h3312 X0 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← h3312 X0 (sK2 ◇ sK1) sK0]
  have l1 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ sK1) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [← h3312 X0 sK1 sK2]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3312 X0 (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l1 X0 X0 sK2 sK1]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3312 X0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← h3312 X0 (sK1 ◇ sK1) sK0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK1]
    conv => enter [1]; rw [← h3312 X0 sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3312 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l4 X0 X0 sK1]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l2 X0 sK2 sK1]
    conv => enter [1]; rw [← l5 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l6 x z y]

@[equational_result]
theorem Equation3312_implies_Equation3316 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3316 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3312 X0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← h3312 sK1 sK1 sK0]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3312 X0 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y x]

@[equational_result]
theorem Equation3312_implies_Equation3306 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3306 G := by
  intro x y
  conv => enter [1]; rw [h3312 x y x]

@[equational_result]
theorem Equation3312_implies_Equation3319 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3319 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [h3312 sK1 sK1 sK1]
    conv => enter [1]; rw [← h3312 X0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h3312 X0 sK1 sK1]
    conv => enter [1]; rw [l0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation3312_implies_Equation3264 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation3264 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h3312 X0 (sK1 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← h3312 sK1 sK0 sK2]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3312 X0 sK0 sK1]
    conv => enter [1]; rw [← l0 X0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation3312_implies_Equation4269 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation4269 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3312 X0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h3312 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3312 X0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← h3312 X0 (sK1 ◇ sK0) sK0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3312 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 X0 sK0 sK1]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3312 X0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l2 X0 sK0 sK1]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← l3 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x x y]

@[equational_result]
theorem Equation3312_implies_Equation4284 (G : Type*) [Magma G] (h3312 : Equation3312 G) : Equation4284 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3312 X0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h3312 X0 sK1 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3312 X0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← h3312 X0 (sK1 ◇ sK1) sK0]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3312 X0 sK1 sK1]
    conv => enter [1]; rw [← l1 X0 sK0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3312 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l2 X0 sK1 X0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK1]
    conv => enter [1]; rw [← l3 X0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x x y]

theorem Equation3330_4512_implies_Equation3312 (G : Type*) [Magma G] (h3330 : Equation3330 G) (h4512 : Equation4512 G) : Equation3312 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h3330 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X3 X2 X0 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ X2)) := by
    intro X3 X2 X0
    conv => enter [1]; rw [l0 X3 X2 X0 X3]
    conv => enter [1, 2]; rw [← h3330 X0 X2 X3]
  have l2 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3330 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X0)]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK2 ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 (sK2 ◇ sK1) X0 X0]
    conv => enter [1]; rw [← l2 sK2 X0 sK1]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l3 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l5 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h3330 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (X0 ◇ X0)]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ (sK2 ◇ sK1)) X0 X0]
    conv => enter [1]; rw [← l5 sK0 X0 sK2 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation3315_implies_Equation3253 (G : Type*) [Magma G] (h3315 : Equation3315 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3315 x x]

@[equational_result]
theorem Equation3353_implies_Equation3253 (G : Type*) [Magma G] (h3353 : Equation3353 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3353 x x]

@[equational_result]
theorem Equation3316_implies_Equation3253 (G : Type*) [Magma G] (h3316 : Equation3316 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3316 x x]

@[equational_result]
theorem Equation3317_implies_Equation325 (G : Type*) [Magma G] (h3317 : Equation3317 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3317 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3317 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3317_implies_Equation3254 (G : Type*) [Magma G] (h3317 : Equation3317 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h3317 x x y]

theorem Equation3397_4512_implies_Equation333 (G : Type*) [Magma G] (h3397 : Equation3397 G) (h4512 : Equation4512 G) : Equation333 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3397 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h3397 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X1
    conv => enter [1, 2]; rw [h3397 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h3397 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) X1]
    conv => enter [1, 2, 2, 2]; rw [← h3397 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l1 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l2 sK1 sK0 X1]
    conv => enter [1, 2, 2]; rw [← h3397 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l3 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3397 sK0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation3397_implies_Equation3268 (G : Type*) [Magma G] (h3397 : Equation3397 G) : Equation3268 G := by
  intro x y
  conv => enter [1]; rw [h3397 x x y]

@[equational_result]
theorem Equation3318_implies_Equation3253 (G : Type*) [Magma G] (h3318 : Equation3318 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3318 x x]

@[equational_result]
theorem Equation3343_implies_Equation3253 (G : Type*) [Magma G] (h3343 : Equation3343 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3343 x x]

@[equational_result]
theorem Equation3320_implies_Equation3318 (G : Type*) [Magma G] (h3320 : Equation3320 G) : Equation3318 G := by
  intro x y
  conv => enter [1]; rw [h3320 x y x]

@[equational_result]
theorem Equation3320_implies_Equation326 (G : Type*) [Magma G] (h3320 : Equation3320 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3320 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3320 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3320_implies_Equation3254 (G : Type*) [Magma G] (h3320 : Equation3320 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h3320 x x y]

@[equational_result]
theorem Equation3380_implies_Equation3343 (G : Type*) [Magma G] (h3380 : Equation3380 G) : Equation3343 G := by
  intro x y
  conv => enter [1]; rw [h3380 x y y]

theorem Equation3380_4512_implies_Equation323 (G : Type*) [Magma G] (h3380 : Equation3380 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ sK1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3380 sK0 sK1 X0]
    conv => enter [1]; rw [h3380 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1, 2, 2]; rw [← h3380 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3380 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h3380 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation3380_implies_Equation3268 (G : Type*) [Magma G] (h3380 : Equation3380 G) : Equation3268 G := by
  intro x y
  conv => enter [1]; rw [h3380 x x y]

@[equational_result]
theorem Equation3321_implies_Equation3318 (G : Type*) [Magma G] (h3321 : Equation3321 G) : Equation3318 G := by
  intro x y
  conv => enter [1]; rw [h3321 x y y]

@[equational_result]
theorem Equation3321_implies_Equation3315 (G : Type*) [Magma G] (h3321 : Equation3321 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [h3321 x y x]

@[equational_result]
theorem Equation3321_implies_Equation3255 (G : Type*) [Magma G] (h3321 : Equation3321 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h3321 x x y]

@[equational_result]
theorem Equation3363_implies_Equation3343 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3343 G := by
  intro x y
  conv => enter [1]; rw [h3363 x y x]

@[equational_result]
theorem Equation3363_implies_Equation3353 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h3363 x y y]

@[equational_result]
theorem Equation3363_implies_Equation3258 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [h3363 x x y]

@[equational_result]
theorem Equation3322_implies_Equation3316 (G : Type*) [Magma G] (h3322 : Equation3322 G) : Equation3316 G := by
  intro x y
  conv => enter [1]; rw [h3322 x y x]

@[equational_result]
theorem Equation3322_implies_Equation3319 (G : Type*) [Magma G] (h3322 : Equation3322 G) : Equation3319 G := by
  intro x y
  conv => enter [1]; rw [h3322 x y y]

@[equational_result]
theorem Equation3322_implies_Equation3255 (G : Type*) [Magma G] (h3322 : Equation3322 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [h3322 x x y]

@[equational_result]
theorem Equation3326_implies_Equation3316 (G : Type*) [Magma G] (h3326 : Equation3326 G) : Equation3316 G := by
  intro x y
  conv => enter [1]; rw [h3326 x y y]

@[equational_result]
theorem Equation3326_implies_Equation3306 (G : Type*) [Magma G] (h3326 : Equation3326 G) : Equation3306 G := by
  intro x y
  conv => enter [1]; rw [h3326 x y x]

@[equational_result]
theorem Equation3326_implies_Equation3258 (G : Type*) [Magma G] (h3326 : Equation3326 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [h3326 x x y]

@[equational_result]
theorem Equation3323_implies_Equation3315 (G : Type*) [Magma G] (h3323 : Equation3323 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [h3323 x y x]

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
theorem Equation3329_implies_Equation38 (G : Type*) [Magma G] (h3329 : Equation3329 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3329 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3329 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3329 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h3329 sK0 X0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

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
theorem Equation3355_implies_Equation3253 (G : Type*) [Magma G] (h3355 : Equation3355 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3355 x x]

@[equational_result]
theorem Equation3345_implies_Equation3253 (G : Type*) [Magma G] (h3345 : Equation3345 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3345 x x]

@[equational_result]
theorem Equation3350_implies_Equation3342 (G : Type*) [Magma G] (h3350 : Equation3350 G) : Equation3342 G := by
  intro x y
  conv => enter [1]; rw [h3350 x y x]

@[equational_result]
theorem Equation3350_implies_Equation3323 (G : Type*) [Magma G] (h3350 : Equation3350 G) : Equation3323 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h3350 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3350 (sK2 ◇ sK2) X0 sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [h3350 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ sK2)) X0 sK2]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3350 sK1 X0 sK2]
    conv => enter [1]; rw [l1 X0 sK1 sK2]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l2 sK1 ((sK2 ◇ sK2) ◇ X0) sK2]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 x y z]

@[equational_result]
theorem Equation3350_implies_Equation3346 (G : Type*) [Magma G] (h3350 : Equation3350 G) : Equation3346 G := by
  intro x y
  conv => enter [1]; rw [h3350 x y y]

theorem Equation3350_4512_implies_Equation43 (G : Type*) [Magma G] (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3350 X1 X2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3350 (X0 ◇ X0) X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3350 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3350 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h3350 (X0 ◇ X0) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 sK1 sK0 X0]
  have l6 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK0 ◇ sK1)]
  have l8 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l6 sK1 sK0 X1 sK1]
    conv => enter [1]; rw [← l1 X1 (sK0 ◇ sK1) sK1]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK1 sK0 X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3350 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 (sK1 ◇ sK0)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3350 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ X0)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [l11 sK1 sK0 (X0 ◇ X0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation3350_implies_Equation4270 (G : Type*) [Magma G] (h3350 : Equation3350 G) : Equation4270 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3350 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3350 (sK0 ◇ sK0) X0 sK0]
  have l1 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3350 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK1) X0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3350 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3350 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation3417_implies_Equation3355 (G : Type*) [Magma G] (h3417 : Equation3417 G) : Equation3355 G := by
  intro x y
  conv => enter [1]; rw [h3417 x y y]

@[equational_result]
theorem Equation3417_implies_Equation3308 (G : Type*) [Magma G] (h3417 : Equation3417 G) : Equation3308 G := by
  intro x y
  conv => enter [1]; rw [h3417 x y x]

theorem Equation3417_4512_implies_Equation3414 (G : Type*) [Magma G] (h3417 : Equation3417 G) (h4512 : Equation4512 G) : Equation3414 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X1 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h3417 (X0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h3417 sK1 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((X0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3417 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h3417 sK1 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h3417 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3417_implies_Equation43 (G : Type*) [Magma G] (h3417 : Equation3417 G) : Equation43 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [h3417 sK0 sK1 X0]
    conv => enter [1]; rw [← h3417 (sK1 ◇ sK0) X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3417 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 (sK1 ◇ sK0) sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h3417 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3417_4512_implies_Equation4275 (G : Type*) [Magma G] (h3417 : Equation3417 G) (h4512 : Equation4512 G) : Equation4275 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3417 sK0 sK0 X0]
    conv => enter [1]; rw [← h3417 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3417 (X0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h3417 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3417 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ X0) := by
    intro X1 sK0 X0
    conv => enter [1, 2, 2]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h3417 ((sK0 ◇ sK0) ◇ X0) X0 X1]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l4 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3417 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3417 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3417 X0 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l7 (X1 ◇ X0) sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [l9 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3417 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
    conv => enter [1, 2]; rw [← h3417 (sK0 ◇ sK0) sK0 X0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 X0 sK0]
    conv => enter [1]; rw [← l11 sK0 X0 sK0]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3417 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [l14 sK0 X0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0 X0]
    conv => enter [1]; rw [← h3417 X0 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3417 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [l16 X0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation3352_implies_Equation3253 (G : Type*) [Magma G] (h3352 : Equation3352 G) : Equation3253 G := by
  intro x
  conv => enter [1]; rw [h3352 x x]

@[equational_result]
theorem Equation3363_implies_Equation3380 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3380 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3363 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK0 (sK0 ◇ sK1) X0]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3363 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK0 (sK0 ◇ sK1) sK2]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3363 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 sK1]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l0 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3363_implies_Equation3397 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3397 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3363 X0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK1 (sK0 ◇ sK1) X0]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3363 sK2 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK1 (sK0 ◇ sK1) sK2]
  have l2 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l0 X0 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3363 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3363_implies_Equation3414 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3414 G := by
  have l0 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h3363 X0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK2 (sK0 ◇ sK1) X0]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3363 sK2 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK2 (sK0 ◇ sK1) sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3363 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK0 sK1]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l0 X0 sK2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3363_implies_Equation3326 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3326 G := by
  have l0 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h3363 X0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK2 (sK0 ◇ sK1) X0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3363 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3363 sK2 (sK0 ◇ sK1) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3363 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK0 sK1]
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l0 X0 sK2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 sK2 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3363_implies_Equation4300 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation4300 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3363 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3363 sK0 sK1 sK0]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3363 sK2 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3363 sK0 sK1 sK2]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l2 z x y]

@[equational_result]
theorem Equation3363_implies_Equation4330 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation4330 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3363 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h3363 sK1 sK0 sK0]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3363 sK2 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h3363 sK1 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation3363_implies_Equation3288 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation3288 G := by
  have l0 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h3363 X0 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3363 sK2 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3363 sK1 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3363 sK2 (sK0 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 X0 sK2 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3363 sK0 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3363_implies_Equation4291 (G : Type*) [Magma G] (h3363 : Equation3363 G) : Equation4291 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3363 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3363 sK0 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3363 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3363 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3321_4512_implies_Equation3317 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation3317 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X1 X2 X3 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l6 X0 X1 X3 X2]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l7 X0 X1 X0 X3]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3321 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) X0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation3321_4512_implies_Equation3320 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation3320 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3321 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 2]; rw [← h3321 sK1 X0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l2 X1 X2 X3 X0]
  have l7 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l7 X0 X1 X3 X2]
  have l9 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l8 X0 X1 X0 X3]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3321 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK1) X0 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation3321_4512_implies_Equation3323 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation3323 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3321 (sK2 ◇ sK2) sK2 X0]
    conv => enter [1, 2]; rw [← h3321 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h3321 X0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l0 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h3321 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l0 sK2 sK2]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 X0]
    conv => enter [1, 2]; rw [← l1 X0 sK2]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3321 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l3 sK2 X0]
  have l5 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 X0]
  have l6 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (((sK2 ◇ sK2) ◇ X0) ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h3321 ((sK2 ◇ sK2) ◇ X0) X1 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l5 sK2 X0]
  have l7 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l6 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 (X1 ◇ ((sK2 ◇ sK2) ◇ sK2))]
  have l8 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) = (((sK2 ◇ sK2) ◇ X0) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1, 2, 2]; rw [l1 X1 sK2]
    conv => enter [1]; rw [← l7 sK2 X0 X1]
  have l9 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l8 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l10 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h3321 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l9 sK2 X0 X1]
  have l11 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2 X0
    conv => enter [1, 2]; rw [l10 sK2 X0 X1]
    conv => enter [1]; rw [← h3321 X1 (sK2 ◇ sK2) X0]
  have l12 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X1 ◇ X0) := by
    intro X1 X0 sK2
    conv => enter [1, 2]; rw [← l11 X0 sK2 X1]
    conv => enter [1]; rw [← h3321 X1 X0 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l12 x y z]

theorem Equation3321_4512_implies_Equation3322 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation3322 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X1 X2 X3 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l6 X0 X1 X3 X2]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l7 X0 X1 X0 X3]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3321 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) X0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation3321_4512_implies_Equation4315 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation4315 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X1 X2 X3 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l6 X0 X1 X3 X2]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l7 X0 X1 X0 X3]
  have l9 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3321 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l8 X0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l9 X0 sK1 sK2]
  have l11 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3321 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l12 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l8 X0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l11 X0 sK1 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 x y z]

theorem Equation3321_4512_implies_Equation4339 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X1 X2 X3 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l6 X0 X1 X3 X2]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l7 X0 X1 X0 X3]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3321 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l9 X0 sK1]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3321 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l8 X0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l11 X0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l13 x y z]

theorem Equation3321_4512_implies_Equation3257 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation3257 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3321 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← h3321 sK0 X0 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3321 (sK1 ◇ sK2) sK2 X0]
    conv => enter [1, 2]; rw [← h3321 sK2 X0 sK1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3321 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3321 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← l2 X0 sK0]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3321 X0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3321 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3321 ((sK0 ◇ sK0) ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [l2 X1 sK0]
    conv => enter [1]; rw [← l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3321 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3321 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [h3321 sK0 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l13 X0 sK0 X1]
    conv => enter [1]; rw [← l15 sK0 X0 X1]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3321 sK0 X0 sK0]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ sK2) sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

theorem Equation3321_4512_implies_Equation4314 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation4314 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3321 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1, 2]; rw [← h3321 sK1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3321 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l3 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1 sK1
    conv => enter [1, 1]; rw [h3321 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK1 ◇ sK0)) X1]
  have l4 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK0) X1]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l4 X1 X2 X3 X0]
  have l10 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l7 sK0 X0 X1 sK1]
  have l11 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l8 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l12 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l9 sK0 X0 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [← l10 sK0 X0 X1 sK1]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l9 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l11 X0 X1 X3 X2]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3321 sK0 X0 sK0]
    conv => enter [1]; rw [l12 sK0 X0 sK0 X1]
  have l15 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l13 X0 X1 X0 X3]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3321 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l17 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l15 X0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l16 X0 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l20 x y]

@[equational_result]
theorem Equation3364_implies_Equation3342 (G : Type*) [Magma G] (h3364 : Equation3364 G) : Equation3342 G := by
  intro x y
  conv => enter [1]; rw [h3364 x y x]

@[equational_result]
theorem Equation3364_implies_Equation3355 (G : Type*) [Magma G] (h3364 : Equation3364 G) : Equation3355 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3364 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3364 sK1 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y y]

@[equational_result]
theorem Equation3364_implies_Equation3331 (G : Type*) [Magma G] (h3364 : Equation3364 G) : Equation3331 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3364 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3364 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK1 X1 X0 sK2 : G, (sK1 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 X1 X0 sK2
    conv => enter [1]; rw [h3364 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [h3364 sK1 X0 sK2]
  have l2 : ∀ sK1 X1 sK2 : G, (sK1 ◇ X1) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l1 sK1 X1 sK1 sK2]
    conv => enter [1]; rw [← l0 (sK2 ◇ (sK1 ◇ sK2)) X1 sK1]
  have l3 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l2 sK1 (X0 ◇ (X1 ◇ X0)) sK2]
    conv => enter [1]; rw [← h3364 X1 (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ X1 sK1 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [h3364 X1 sK1 X1]
    conv => enter [1]; rw [l3 sK1 X1 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3364_implies_Equation3334 (G : Type*) [Magma G] (h3364 : Equation3364 G) : Equation3334 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3364 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3364 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3364 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3364 sK2 (sK2 ◇ sK1) sK1]
  have l2 : ∀ sK1 X1 X0 sK2 : G, (sK1 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 X1 X0 sK2
    conv => enter [1]; rw [h3364 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 sK1 X0 sK2]
  have l3 : ∀ sK1 X1 sK2 : G, (sK1 ◇ X1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l2 sK1 X1 sK1 sK2]
    conv => enter [1]; rw [← l0 (sK2 ◇ (sK2 ◇ sK1)) X1 sK1]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3364 sK0 (sK2 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3364 sK0 sK1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation3364_implies_Equation3353 (G : Type*) [Magma G] (h3364 : Equation3364 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h3364 x y y]

theorem Equation3364_4512_implies_Equation43 (G : Type*) [Magma G] (h3364 : Equation3364 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3364 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3364 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3364 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3364 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3364 X3 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l3 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l2 X3 X0 X1 X3]
    conv => enter [1, 2]; rw [← h3364 X3 X1 X3]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK1 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3364 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3364 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l7 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h3364 sK0 X1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l7 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l10 : ∀ sK0 X1 sK1 : G, (sK0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l8 sK0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h3364 (sK0 ◇ sK1) sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [l3 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3364 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK0) X0 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK1]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l3 (sK1 ◇ sK0) sK0 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK1 sK0 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation3404_4512_implies_Equation3342 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3342 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h3404 (X1 ◇ (X2 ◇ X0)) X3 X2]
    conv => enter [1, 2, 2]; rw [← h3404 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK1 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3404 (X0 ◇ (sK0 ◇ sK0)) X1 sK0]
    conv => enter [1, 2, 2]; rw [← h3404 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3404 X0 X1 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h3404 sK0 sK0 sK0]
    conv => enter [1]; rw [← h3404 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3404 sK0 X0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3404 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l8 sK0 (sK0 ◇ sK1)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h3404 sK1 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 (sK0 ◇ sK0) X0 sK0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 X0 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3404 X0 X1 X0]
    conv => enter [1, 2, 2]; rw [l13 X0 sK0]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l13 sK0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h3404 X0 (X1 ◇ X0) X1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [l13 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3404 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 (sK0 ◇ sK1) sK0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 (sK0 ◇ sK1) sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK1) sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l24 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h3404 sK1 sK0 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l28 x y]

@[equational_result]
theorem Equation3404_implies_Equation3355 (G : Type*) [Magma G] (h3404 : Equation3404 G) : Equation3355 G := by
  intro x y
  conv => enter [1]; rw [h3404 x y y]

theorem Equation3404_4512_implies_Equation3388 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3388 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h3404 (X1 ◇ (X2 ◇ X0)) X3 X2]
    conv => enter [1, 2, 2]; rw [← h3404 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK1 X0 sK0]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [h3404 sK1 X0 sK2]
    conv => enter [1]; rw [← h3404 (sK2 ◇ sK1) sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h3404 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h3404 sK1 sK0 sK2]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = (X0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK2 ◇ sK1)) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 (sK2 ◇ sK1) X0 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h3404 (sK2 ◇ sK1) sK2 sK0]
  have l9 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2 X0]
    conv => enter [1, 2]; rw [← h3404 (sK0 ◇ (sK2 ◇ sK1)) X0 sK2]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3404 X0 X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l11 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l10 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 X0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 sK0 X0 X0]
  have l13 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3404 sK0 X1 sK0]
    conv => enter [1, 2, 2]; rw [l12 sK0 X0]
  have l14 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h3404 X0 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l7 sK0 sK2 sK1 X0]
  have l15 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = (((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK1 ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l16 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l15 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0)]
  have l17 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = (sK0 ◇ ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1)) sK0]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l13 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l17 sK2 sK0 sK1]
  have l19 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h3404 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l14 X0 sK2 sK1 sK0]
  have l20 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = ((X0 ◇ X0) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l9 sK2 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l19 sK0 sK2 sK1 X0]
  have l21 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l20 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK0 ◇ (sK2 ◇ sK1))]
  have l22 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [l21 sK2 sK0 sK1 X0]
  have l23 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h3404 (sK0 ◇ (sK2 ◇ sK1)) X0 X0]
  have l24 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l22 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 sK2]
  have l25 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK2 sK1 sK2]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h3404 sK1 (sK0 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l23 (sK0 ◇ sK1) sK0 sK2 sK1]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h3404 sK1 (sK0 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l23 (sK2 ◇ sK1) sK0 sK2 sK1]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK2 sK0 sK1 (sK2 ◇ sK1)]
  have l29 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
    conv => enter [1]; rw [← h3404 (sK2 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l30 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK0 ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l28 sK1 sK0 sK2]
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l24 sK1 sK0 sK2]
    conv => enter [1]; rw [l29 sK1 sK0 sK2]
  have l32 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l24 sK1 sK0 sK2]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) X0 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l31 sK0 sK2 sK1]
  have l34 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l33 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l2 (sK2 ◇ sK1) X0 sK0 sK2]
  have l35 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3404 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l32 sK0 sK2 sK1]
  have l36 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
  have l37 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3404 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l38 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK2 ◇ sK1) ◇ (X0 ◇ X1))]
  have l39 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK0 sK2 sK1]
    conv => enter [1]; rw [l38 sK0 sK2 sK1 X0 X1]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l36 X0 X1 sK0]
  have l41 : ∀ sK0 sK2 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1 X1
    conv => enter [1]; rw [l39 sK0 sK2 sK1 sK0 X1]
    conv => enter [1]; rw [← l37 X1 X1 (sK2 ◇ sK1) sK0]
  have l42 : ∀ sK2 sK1 X1 : G, (sK2 ◇ sK1) = (X1 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [l35 sK2 sK1 sK2]
    conv => enter [1]; rw [l41 sK2 sK2 sK1 X1]
  have l43 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ X0) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l42 sK2 sK1 X0]
    conv => enter [1]; rw [← h3404 (sK2 ◇ sK1) X0 X0]
  have l44 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l30 sK2 sK0 sK1]
    conv => enter [1]; rw [l43 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2 sK1]
  have l45 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l44 sK0 sK2 sK1]
  have l46 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l45 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l2 (sK2 ◇ sK1) X0 sK0 sK2]
  have l47 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l34 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l46 sK2 sK0 sK1 X0]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3404 sK1 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2]
    conv => enter [1, 2]; rw [← l47 sK0 sK1 (sK2 ◇ sK1) sK2]
  have l49 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h3404 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← l48 sK1 sK2 sK0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [← l49 sK1 sK0 sK0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l40 sK1 (sK0 ◇ sK1) sK0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h3404 sK1 sK0 sK0]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h3404 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l53 x y z]

theorem Equation3404_4512_implies_Equation3334 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ X0 sK2 sK1 X1 : G, ((X0 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK2 ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h3404 (X0 ◇ (sK2 ◇ sK1)) X1 sK2]
    conv => enter [1, 2, 2]; rw [← h3404 sK1 X0 sK2]
  have l1 : ∀ sK2 X1 sK1 X0 : G, (sK2 ◇ (X1 ◇ (sK1 ◇ X0))) = (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro sK2 X1 sK1 X0
    conv => enter [1]; rw [← l0 X0 sK2 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK1) X1]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK2 ◇ sK1)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h3404 sK1 sK2 sK2]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK1 X0]
    conv => enter [1]; rw [l1 sK2 X0 sK1 sK2]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3404 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l3 sK2 sK1 (sK2 ◇ sK1)]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3404 sK1 (sK2 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l4 sK1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3404 sK1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l7 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK2 ◇ sK1)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK2]
  have l8 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3404 sK1 X0 sK1]
    conv => enter [1]; rw [← l7 sK2 sK1 X0]
  have l9 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h3404 X1 (sK2 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l8 sK1 (X0 ◇ X1) sK2]
  have l10 : ∀ X1 sK2 sK1 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ sK1) := by
    intro X1 sK2 sK1
    conv => enter [1]; rw [l9 X1 sK2 sK1 X1]
    conv => enter [1]; rw [← h3404 X1 sK1 X1]
  intro x y z
  conv => enter [1]; rw [← l10 x z y]

@[equational_result]
theorem Equation3404_implies_Equation3315 (G : Type*) [Magma G] (h3404 : Equation3404 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [h3404 x y x]

theorem Equation3404_4512_implies_Equation43 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK1 X0 sK0]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3404 X0 X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 X0 sK1 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← h3404 X0 ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK0 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3404 sK1 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation3380_implies_Equation3363 (G : Type*) [Magma G] (h3380 : Equation3380 G) : Equation3363 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3380 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h3380 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h3380 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y y z]

theorem Equation3320_4512_implies_Equation3317 (G : Type*) [Magma G] (h3320 : Equation3320 G) (h4512 : Equation4512 G) : Equation3317 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3320 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3320 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3320 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation3320_4512_implies_Equation3321 (G : Type*) [Magma G] (h3320 : Equation3320 G) (h4512 : Equation4512 G) : Equation3321 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3320 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3320 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3320 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation3385_4512_implies_Equation3350 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3350 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3385 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 sK2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 X1]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l4 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ sK1)]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 X1]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 X1]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3385 (sK0 ◇ (sK2 ◇ sK2)) sK0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l8 sK0 (sK2 ◇ sK2) (sK0 ◇ sK1)]
  have l11 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK2]
    conv => enter [1]; rw [l8 sK2 sK2 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [← l11 sK2 sK0 sK0]
  have l13 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l9 X0 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK2 X0 X0]
  have l14 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l1 sK2 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2]
  have l15 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l14 sK2 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ (sK2 ◇ sK2)) sK0]
  have l16 : ∀ X0 sK0 sK2 : G, (X0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h3385 X0 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l15 sK2 sK0]
  have l17 : ∀ X0 sK0 sK2 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l16 X0 sK0 sK2]
    conv => enter [1]; rw [← l13 X0 (sK0 ◇ (sK2 ◇ sK2)) sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l17 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

theorem Equation3385_4512_implies_Equation3364 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3364 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK2 X0 sK0 : G, (sK2 ◇ X0) = ((sK0 ◇ sK2) ◇ (X0 ◇ sK0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h3385 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK2) X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK2 X0 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 X1]
  have l6 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l5 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l7 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ sK1)]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l10 sK1 X0]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ sK2) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [l10 sK2 X0]
  have l14 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l13 sK0 sK2 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK0]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l14 sK0 sK2 sK1]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l15 sK2 sK0 sK1]
    conv => enter [1]; rw [← h3385 sK1 sK0 sK1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation3385_4512_implies_Equation3398 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3398 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X1]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l3 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h3385 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

end Semigroup4
