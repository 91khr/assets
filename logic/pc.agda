module pc where

open import base
open import Data.Nat using (ℕ)

infix 15 _↝_
data _↝_ : Term → Term → Set where
  ↝var : ∀ {a} → ` a ↝ ` a
  ↝⊥ : t⊥ ↝ t⊥
  ↝∧ : ∀ {a b a′ b′} → a ↝ a′ → b ↝ b′ → (a ∧ b) ↝ (a′ ∧ b′)
  ↝∨ : ∀ {a b a′ b′} → a ↝ a′ → b ↝ b′ → (a ∨ b) ↝ (a′ ∨ b′)
  ↝¬ : ∀ {a a′} → a ↝ a′ → ¬ a ↝ ¬ a′
  ↝⇒ : ∀ {a b a′ b′} → a ↝ a′ → b ↝ b′ → (a ⇒ b) ↝ (a′ ⇒ b′)
  ↝⇔ : ∀ {a b a′ b′} → a ↝ a′ → b ↝ b′ → (a ⇔ b) ↝ (a′ ⇔ b′)
  Df1 : ∀ (a b : Term) → a ∧ b ↝ ¬ (¬ a ∨ ¬ b)
  Dr1 : ∀ (a b : Term) → ¬ (¬ a ∨ ¬ b) ↝ a ∧ b
  Df2 : ∀ (a b : Term) → a ⇒ b ↝ ¬ a ∨ b
  Dr2 : ∀ (a b : Term) → ¬ a ∨ b ↝ a ⇒ b
  Df3 : ∀ (a b : Term) → a ⇔ b ↝ (a ⇒ b) ∧ (b ⇒ a)
  Dr3 : ∀ (a b : Term) → (a ⇒ b) ∧ (b ⇒ a) ↝ a ⇔ b
↝refl : ∀ {x} → x ↝ x
↝refl {` x} = ↝var
↝refl {x ∧ x₁} = ↝∧ ↝refl ↝refl
↝refl {x ∨ x₁} = ↝∨ ↝refl ↝refl
↝refl {¬ x} = ↝¬ ↝refl
↝refl {x ⇒ x₁} = ↝⇒ ↝refl ↝refl
↝refl {x ⇔ x₁} = ↝⇔ ↝refl ↝refl
↝refl {t⊥} = ↝⊥

infixl 15 _,_
data Context : Set where
  ∅ : Context
  _,_ : Context → Term → Context

infix 14 _∋_
data _∋_ : Context → Term → Set where
  Z : ∀ {Γ x} → Γ , x ∋ x
  S_ : ∀ {Γ x y} → Γ ∋ y → Γ , x ∋ y

module lookup where
  open import Data.Nat using (suc; _≤_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary.Decidable using (True; toWitness)
  length : Context → ℕ
  length ∅ = 0
  length (Γ , x) = suc (length Γ)
  lookup : {Γ : Context} {n : ℕ} (p : suc n ≤ length Γ) → Term
  lookup {Γ , x} {0} p = x
  lookup {Γ , x} {suc n} (s≤s p) = lookup p
  count : ∀ {Γ} {n : ℕ} (p : suc n ≤ length Γ) → Γ ∋ lookup p
  count {Γ , x} {0} p = Z
  count {Γ , x} {suc n} (s≤s p) = S count p
  infix 18 #_
  #_ : ∀ {Γ} (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)} → Γ ∋ lookup (toWitness n∈Γ)
  #_ n {n∈Γ} = count (toWitness n∈Γ)
  infix 18 ##_
  ##_ : ∀ {Γ} (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)} → Term
  ##_ n {n∈Γ} = lookup (toWitness n∈Γ)
open lookup using (#_; ##_)

infix 14 _⊢_
infixr 16 ⟨_⟩→_
data _⊢_ : Context → Term → Set where
  ⟨_⟩→_ : ∀ {Γ imm res} → Γ ⊢ imm → Γ , imm ⊢ res → Γ ⊢ res
  ∎ : ∀ {Γ res} → Γ , res ⊢ res
  MP : ∀ {Γ a b} → Γ ∋ a ⇒ b → Γ ∋ a → Γ ⊢ b
  A1 : ∀ {Γ} (a) → Γ ⊢ a ∨ a ⇒ a
  A2 : ∀ {Γ} (a b : Term) → Γ ⊢ a ⇒ a ∨ b
  A3 : ∀ {Γ} (a b : Term) → Γ ⊢ a ∨ b ⇒ b ∨ a
  A4 : ∀ {Γ} (a b c : Term) → Γ ⊢ (b ⇒ c) ⇒ (a ∨ b ⇒ a ∨ c)
  ↝app : ∀ {Γ a a′} → Γ ∋ a → a ↝ a′ → Γ ⊢ a′

Ax1 : ∀ {Γ} (a b c : Term) → Γ ⊢ (b ⇒ c) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))
Ax1 a b c = ⟨ A4 (¬ a) b c ⟩→ ⟨ ↝app (# 0) (↝⇒ ↝refl (↝⇒ (Dr2 a b) (Dr2 a c))) ⟩→ ∎
Ax2 : ∀ {Γ} (a : Term) → Γ ⊢ a ⇒ a
Ax2 a = ⟨ A2 a a ⟩→ ⟨ A1 a ⟩→ ⟨ Ax1 a (a ∨ a) a ⟩→ ⟨ MP (# 0) (# 1) ⟩→ ⟨ MP (# 0) (# 3) ⟩→ ∎
Ax3 : ∀ {Γ} (a : Term) → Γ ⊢ ¬ a ∨ a
Ax3 a = ⟨ Ax2 a ⟩→ ⟨ ↝app (# 0) (Df2 a a) ⟩→ ∎
Ax4 : ∀ {Γ} (a : Term) → Γ ⊢ a ∨ ¬ a
Ax4 a = ⟨ Ax3 a ⟩→ ⟨ A3 (¬ a) a ⟩→ ⟨ MP (# 0) (# 1) ⟩→ ∎
Ax5 : ∀ {Γ} (a : Term) → Γ ⊢ a ⇒ ¬ ¬ a
Ax5 a = ⟨ Ax4 (¬ a) ⟩→ ⟨ ↝app (# 0) (Dr2 a (¬ ¬ a)) ⟩→ ∎
Ax6 : ∀ {Γ} (a : Term) → Γ ⊢ ¬ ¬ a ⇒ a
Ax6 a = ⟨ Ax5 (¬ a) ⟩→ ⟨ A4 a (¬ a) (¬ ¬ ¬ a) ⟩→ ⟨ MP (# 0) (# 1) ⟩→ ⟨ Ax4 a ⟩→ ⟨ MP (# 1) (# 0) ⟩→
        ⟨ A3 a (¬ ¬ ¬ a) ⟩→ ⟨ MP (# 0) (# 1) ⟩→ ⟨ ↝app (# 0) (Dr2 (¬ ¬ a) a) ⟩→ ∎
Ax7 : ∀ {Γ} (a b : Term) → Γ ⊢ (a ⇒ b) ⇒ (¬ b ⇒ ¬ a)
Ax7 a b = ⟨ Ax5 b ⟩→ ⟨ A4 (¬ a) b (¬ ¬ b) ⟩→ ⟨ MP (# 0) (# 1) ⟩→ ⟨ Ax1 (¬ a ∨ b) (¬ a ∨ ¬ ¬ b) (¬ ¬ b ∨ ¬ a) ⟩→
          ⟨ A3 (¬ a) (¬ ¬ b) ⟩→ ⟨ MP (# 1) (# 0) ⟩→ ⟨ MP (# 0) (# 3) ⟩→
          ⟨ ↝app (# 0) (↝⇒ (Dr2 a b) (Dr2 (¬ b) (¬ a))) ⟩→ ∎
Ax8 : ∀ {Γ} (a b : Term) → Γ ⊢ ¬ (a ∧ b) ⇒ ¬ a ∨ ¬ b
Ax8 a b = ⟨ Ax6 (¬ a ∨ ¬ b) ⟩→ ↝app (# 0) (↝⇒ (↝¬ (Dr1 a b)) ↝refl)
Ax9 : ∀ {Γ} (a b : Term) → Γ ⊢ ¬ a ∨ ¬ b ⇒ ¬ (a ∧ b)
Ax9 a b = ⟨ Ax5 (¬ a ∨ ¬ b) ⟩→ ↝app (# 0) (↝⇒ ↝refl (↝¬ (Dr1 a b)))
Ax10 : ∀ {Γ} (a b : Term) → Γ ⊢ a ⇒ b ∨ a
Ax10 a b = ⟨ A3 a b ⟩→ ⟨ Ax1 a (a ∨ b) (b ∨ a) ⟩→ ⟨ MP (# 0) (# 1) ⟩→ ⟨ A2 a b ⟩→ MP (# 1) (# 0)

