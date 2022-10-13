module fpc where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import base
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)

infixl 9 _::_
data Hyposis : Term → Set where
  [] : Hyposis t⊥
  [_] : (x : Term) → Hyposis x
  _::_ : ∀ {x} → Hyposis x → Term → Hyposis x
  _::[_] : ∀ {x y} → Hyposis x → Hyposis y → Hyposis x

data InHyp : ∀ {x} → Term → Hyposis x → Set where
  hyp : ∀ {x} {hyp : Hyposis x} → InHyp x hyp
  here : ∀ {x elem} {pre : Hyposis x} → InHyp elem (pre :: elem)
  there : ∀ {x elem tail} {pre : Hyposis x} → InHyp elem pre → InHyp elem (pre :: tail)
  inner : ∀ {x y elem} {pre : Hyposis x} {sub : Hyposis y} → InHyp elem sub → InHyp elem (pre ::[ sub ])
  outer : ∀ {x y elem} {pre : Hyposis x} {sub : Hyposis y} → InHyp elem pre → InHyp elem (pre ::[ sub ])

InHyp? : ∀ {x} (res : Term) (cur : Hyposis x) → Dec (InHyp res cur)
InHyp? res [] with res t≟ t⊥
...              | yes refl = yes hyp
...              | no r⊥ = no λ { hyp → r⊥ refl }
InHyp? res [ x ] with res t≟ x
...                 | yes refl = yes hyp
...                 | no r⊥ = no λ { hyp → r⊥ refl }
InHyp? res (cur :: x) with res t≟ x
...                      | yes refl = yes here
...                      | no res≢x with InHyp? res cur
...                                     | yes incur = yes (there incur)
...                                     | no ¬incur = no λ { hyp → ¬incur hyp ; here → res≢x refl ; (there y) → ¬incur y }
InHyp? res (cur ::[ sub ]) with InHyp? res sub
...                           | yes insub = yes (inner insub)
...                           | no ¬insub with InHyp? res cur
...                                          | yes incur = yes (outer incur)
...                                          | no ¬incur = no λ { hyp → ¬incur hyp ; (inner y) → ¬insub y ; (outer y) → ¬incur y }

module implication-impl where
  private variable
    x y a b : Term
    base : Hyposis x
    cur : Hyposis y
  private data ∋⊥ : Set where
  infixl 8 _∋_ _:>_⊢_ _:>′_⊢_
  data _∋_ : Hyposis x → Hyposis y → Set
  data _:>_⊢_ : Hyposis x → Hyposis y → Term → Set
  _:>′_⊢_ : Hyposis x → Hyposis y → Term → Set
  base :>′ cur ⊢ res = ∋⊥ → base :> cur ⊢ res
  
  data _∋_ where
    hyp⟨_⟩ : ∀ (y) → ∋⊥ → base ∋ [ y ]
    cont⟨_⟩ : ∀ {z res} {pre : Hyposis z} → base ::[ pre ] :>′ cur ⊢ res → base ∋ pre → base ∋ pre :: res
    rep⟨_⟩ : ∀ (res) {incur : True (InHyp? res cur)} → base ∋ cur → base ∋ cur :: res
    reit⟨_⟩ : ∀ (res) {inbase : True (InHyp? res base)} → base ∋ cur → base ∋ cur :: res
    ⇒⁻ :  base ∋ cur :: a ⇒ b :: a → base ∋ cur :: a ⇒ b :: a :: b
    ∨⁺ˡ :  base ∋ cur :: a → base ∋ cur :: a :: a ∨ b
    ∨⁺ʳ :  base ∋ cur :: a → base ∋ cur :: a :: b ∨ a
    ∨⁻ : ∀ {c} → base ∋ cur :: a ⇒ c :: b ⇒ c :: a ∨ b → base ∋ cur :: a ⇒ c :: b ⇒ c :: a ∨ b :: c
    ∧⁺ :  base ∋ cur :: a :: b → base ∋ cur :: a :: b :: a ∧ b
    ∧⁻ˡ :  base ∋ cur :: a ∧ b → base ∋ cur :: a ∧ b :: a
    ∧⁻ʳ :  base ∋ cur :: a ∧ b → base ∋ cur :: a ∧ b :: b
    ⇔⁺ :  base ∋ cur :: a ⇒ b :: b ⇒ a → base ∋ cur :: a ⇒ b :: b ⇒ a :: a ⇔ b
    ⇔⁻ˡ :  base ∋ cur :: a ⇔ b → base ∋ cur :: a ⇔ b :: a ⇒ b
    ⇔⁻ʳ :  base ∋ cur :: a ⇔ b → base ∋ cur :: a ⇔ b :: b ⇒ a
  
  data _:>_⊢_ where
    ⇒⁺ : ∀ {res} → base ∋ cur :: res → base :> cur :: res ⊢ y ⇒ res
    ¬elim : ∀ {cur : Hyposis (¬ y)} → base ∋ cur :: a :: ¬ a → base :> cur :: a :: ¬ a ⊢ y

  infix 8 _⊢_
  data _⊢_ : ∀ {x} → Hyposis x → Term → Set where
    imply_ : ∀ {res} → base :>′ cur ⊢ res → base ⊢ res

  infixl 1 _>>_
  _>>_ : ∀ {A B C : Set} → (A → B) → (B → C) → A → C
  g >> f = λ x → f (g x)
open implication-impl

_ : [] ⊢ ` 0 ⇒ ` 0
_ = imply do
  hyp⟨ ` 0 ⟩
  rep⟨ ` 0 ⟩
  ⇒⁺
_ : [] ⊢ ` 0 ∨ ` 0 ⇒ ` 0
_ = imply do
  hyp⟨ ` 0 ∨ ` 0 ⟩
  cont⟨(do
    hyp⟨ ` 0 ⟩
    rep⟨ ` 0 ⟩
    ⇒⁺
    )⟩
  rep⟨ ` 0 ⇒ ` 0 ⟩
  rep⟨ ` 0 ∨ ` 0 ⟩
  ∨⁻
  ⇒⁺
_ : [] ⊢ ¬ ¬ ` 0 ⇒ ` 0
_ = imply do
  hyp⟨ ¬ ¬ ` 0 ⟩
  cont⟨(do
    hyp⟨ ¬ ` 0 ⟩
    rep⟨ ¬ ` 0 ⟩
    reit⟨ ¬ ¬ ` 0 ⟩
    ¬elim
    )⟩
  ⇒⁺
_ : [] ⊢ ` 0 ⇒ ¬ ¬ ` 0
_ = imply do
  hyp⟨ ` 0 ⟩
  cont⟨(do
    hyp⟨ ¬ ¬ ¬ ` 0 ⟩
    cont⟨(do
      hyp⟨ ¬ ¬ ` 0 ⟩
      rep⟨ ¬ ¬ ` 0 ⟩
      reit⟨ ¬ ¬ ¬ ` 0 ⟩
      ¬elim
      )⟩
    reit⟨ ` 0 ⟩
    rep⟨ ¬ ` 0 ⟩
    ¬elim
    )⟩
  ⇒⁺

