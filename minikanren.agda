
open import Data.Bool using (Bool; true; false; T?; not; _xor_; if_then_else_) renaming (_∨_ to _or_)
open import Data.String using (_==_; String)
open import Data.Nat using (ℕ; _≡ᵇ_; _<ᵇ_; zero; suc; _+_; _∸_)
open import Function using (_∘_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)


data Term : Set where

    symbol : String → Term
    boolean : Bool → Term
    _,_ : Term → Term → Term
    
open Term

infixr 4 _,_

_==ᵗ_ : Term → Term → Bool
symbol x ==ᵗ symbol x₁ = x == x₁
boolean x ==ᵗ boolean x₁ = not (x xor x₁)
(a , a₁) ==ᵗ (b , b₁) with a ==ᵗ b
... | false = false
... | true = a₁ ==ᵗ b₁
_ ==ᵗ _ = false

infix 3 _==ᵗ_

data Kanren : Set where

    `_ : Term → Kanren
    _∧_ : Kanren → Kanren → Kanren
    _∨_ : Kanren → Kanren → Kanren
    ƛ_ : Kanren → Kanren
    μ_ : Kanren → Kanren
    #_ : ℕ → Kanren
    _·_ : Kanren → Kanren → Kanren
    _===_ : Kanren → Kanren → Kanren

open Kanren

infix 4 _===_
infixr 6 _∧_
infixr 5 _∨_
infix 5 ƛ_
infix 4 μ_
infix 9 `_
infix 9 #_
infixl 7 _·_

data Shift : Set where

    Upward : ℕ → Shift

    Downward : ℕ → Shift

_↑_<_ : Kanren → Shift → ℕ → Kanren
(` x) ↑ d < c = ` x
(k ∧ k₁) ↑ d < c = (k ↑ d < c) ∧ (k₁ ↑ d < c)
(k ∨ k₁) ↑ d < c = (k ↑ d < c) ∨ (k₁ ↑ d < c)
(ƛ k) ↑ d < c = ƛ (k ↑ d < suc c)
(μ k) ↑ d < c = μ (k ↑ d < suc c)
(# x) ↑ d < c with x <ᵇ c | d
... | false | Upward x₁ = # (x + x₁)
... | false | Downward x₁ = # (x ∸ x₁)
... | true | d' = # x
(k · k₁) ↑ d < c = (k ↑ d < c) · (k₁ ↑ d < c)
(a === b) ↑ d < c = (a ↑ d < c) === (b ↑ d < c)

_↑_ : Kanren → Shift → Kanren
x ↑ d = x ↑ d < 0

infix 3 _↑_

_ : (ƛ (# 1 · # 0 · # 2) ↑ Upward 1) ≡ ƛ # 2 · # 0 · # 3
_ = refl

_[_] : Kanren → Kanren → Kanren
_[_] a = (_↑ Downward 1) ∘ subst 0 a ∘ (_↑ Upward 1)
    where
        subst : ℕ → Kanren → Kanren → Kanren
        subst i (` x) b = ` x
        subst i (a ∧ a₁) b = subst i a b ∧ subst i a₁ b
        subst i (a ∨ a₁) b = subst i a b ∨ subst i a₁ b
        subst i (ƛ a) b = ƛ subst (suc i) a (b ↑ Upward 1)
        subst i (μ a) b = μ subst (suc i) a (b ↑ Upward 1)
        subst i (# x) b with x ≡ᵇ i
        ... | false = # x
        ... | true = b
        subst i (a · a₁) b = subst i a b · subst i a₁ b
        subst i (a === b) c = subst i a c === subst i b c

_ : (# 0) [ ƛ # 1 ] ≡ ƛ # 1
_ = refl

_ : (# 1 · # 0 · # 2) [ ƛ # 2 ] ≡ (# 0 · (ƛ # 2)) · # 1
_ = refl

data Value : Kanren → Set where

    V-ƛ : ∀ {K}
        -----------
      → Value (ƛ K)

    V-Term : ∀ {T}
      → Value (` T)

infix 4 _—→_

data _—→_ : Kanren → Kanren → Set where

    ξ-·₁ : ∀ {L L′ M}
      → L —→ L′
        ------------------
      → L · M —→ L′ · M

    ξ-·₂ : ∀ {V M M′}
      → Value V
      → M —→ M′
        ------------------
      → V · M —→ V · M′

    β-ƛ : ∀ {N M}
        ---------------------------------------------------
      → (ƛ N) · M —→ (N [ M ])

    β-μ : ∀ {N}
        -------------------
      → (μ N) —→ N [ μ N ]


data _—↠_ : Kanren → Kanren → Set where

    _↠∎ : ∀ L
         --------
      → L —↠ L

    _—→⟨_⟩_ : ∀ L {M N}
      → L —→ M
      → M —↠ N
         --------
      → L —↠ N

infix 2 _—↠_
infixr 2 _—→⟨_⟩_
infix 3 _↠∎

begin↠_ : ∀ {A B} → A —↠ B → A —↠ B
begin↠_ b = b

infix 1 begin↠_

_ : (ƛ # 0 · # 0) · (ƛ # 0) —↠ ƛ # 0
_ = begin↠
      (ƛ # zero · # zero) · (ƛ # zero)
    —→⟨ β-ƛ ⟩
      (ƛ # zero) · (ƛ # zero)
    —→⟨ β-ƛ ⟩
      (ƛ # zero) ↠∎

_ : (μ ƛ # 1) —→ (ƛ (μ ƛ # 1))
_ = β-μ

_ : (boolean true , boolean true , boolean true) ≡ (boolean true , (boolean true , boolean true))
_ = refl

_ : Kanren
_ = ƛ (ƛ (# 1 · # 0))

Subst : Set
Subst = List (ℕ × Kanren)

occurs? : ℕ → Kanren → Bool
occurs? n (` x) = false
occurs? n (k ∧ k₁) = occurs? n k or occurs? n k₁
occurs? n (k ∨ k₁) = occurs? n k or occurs? n k₁
occurs? n (ƛ k) = occurs? n k
occurs? n (μ k) = occurs? n k
occurs? n (# x) = n ≡ᵇ x
occurs? n (k · k₁) = occurs? n k or occurs? n k₁
occurs? n (k === k₁) = occurs? n k or occurs? n k₁

ext-s : ℕ → Kanren → Subst → Maybe Subst
ext-s n k s with occurs? n k
... | false = just (⟨ n , k ⟩ ∷ s)
... | true = nothing

unify-=== : Kanren → Subst → Maybe Subst
unify-=== (a === b) s = {!!}
unify-=== k s = just s

{-
Subst : Set
Subst = List (ℕ × Term)

State : Set
State = Subst × ℕ

data Stream : Set where
    [] : Stream
    _∷_ : State → Stream → Stream

Goal : Set
Goal = State → Stream

take : ℕ → Stream → Stream
take n [] = []
take zero (x ∷ s) = []
take (suc n) (x ∷ s) = x ∷ take n s

drop : ℕ → Stream → Stream
drop n [] = []
drop zero (x ∷ s) = x ∷ s
drop (suc n) (x ∷ s) = drop n s

append-stream : Stream → Stream → Stream
append-stream [] b = b
append-stream (x ∷ a) b = x ∷ append-stream a b

append-map : Goal → Stream → Stream
append-map g [] = []
append-map g (x ∷ s) = append-stream (g x) (append-map g s)

term-size : Term → ℕ
term-size (_ ∷ t) = suc (term-size t)
term-size _ = suc zero

var? : Term → Bool
var? (var _) = true
var? _ = false

pair? : Term → Bool
pair? (_ ∷ _) = true
pair? _ = false

eq? : Term → Term → Bool
eq? (symbol u) (symbol v) = u == v
eq? (boolean u) (boolean v) = not (u xor v)
eq? (u ∷ t₁) (v ∷ t₂) = eq? u v ∧ (eq? t₁ t₂)
eq? (var u) (var v) = u ≡ᵇ v
eq? _ _ = false

find : Term → Subst → Term
find (var x) [] = var x
find (var x) (( n , st ) ∷ s) with x ≡ᵇ n
... | false = find (var x) s
... | true = st
find x _ = x

occurs? : ℕ → Term → Subst → Bool
occurs? x (v ∷ v₁) s = go (term-size (v ∷ v₁)) (v ∷ v₁)
    where
        go : ℕ → Term → Bool
        go zero v = false
        go (suc size) (symbol x) = false
        go (suc size) (boolean x) = false
        go (suc size) (v ∷ v₁) = go size v ∨ go size v₁ 
        go (suc size) (var x₁)  = x ≡ᵇ x₁
occurs? x (var x₁) s = x ≡ᵇ x₁
occurs? _ _ _ = false

ext-s : ℕ → Term → Subst → Maybe Subst
ext-s x v s with occurs? x v s
... | false = just ((x , v) ∷ s)
... | true = nothing

unify : Term → Term → Subst → Maybe Subst
unify u v s with eq? u v
... | true = just s
... | false with u | v
... | var x | _ = ext-s x v s
... | _ | var _ = unify′ 1 v u s
  where
        unify′ : ℕ → Term → Term → Subst → Maybe Subst
        unify′ n u v s with eq? u v
        ... | true = just s
        ... | false with u | v | n
        ... | var x | _ | _ = ext-s x v s
        ... | symbol _ | _ | _ = nothing
        ... | boolean _ | _ | _ = nothing
        ... | _ | var _ | 0 = nothing
        ... | _ | var _ | suc y = unify′ y v u s
        ... | _ | symbol _ | _ = nothing
        ... | _ | boolean _ | _ = nothing
        ... | a0 ∷ a1 | b0 ∷ b1 | _ with unify a0 b0 s
        ...                        | nothing = nothing
        ...                        | just s′ = unify a1 b1 s′
... | symbol _ | _ = nothing
... | boolean _ | _ = nothing
... | _ | symbol _ = nothing
... | _ | boolean _ = nothing
... | a0 ∷ a1 | b0 ∷ b1 with unify a0 b0 s
...                        | nothing = nothing
...                        | just s′ = unify a1 b1 s′

_===_ : Term → Term → Goal
u === v = go
    where
        go : Goal
        go (s , counter) with unify (find u s) (find v s) s
        ... | nothing = []
        ... | just subst = (subst , counter) ∷ []

_ : (boolean true === boolean false) ([] , 0) ≡ []
_ = refl

_ : (boolean true === boolean true) ([] , 0) ≡ ([] , 0) ∷ []
_ = refl

_ : ((boolean true ∷ boolean false) === (boolean true ∷ boolean false)) ([] , 0) ≡ ([] , 0) ∷ []
_ = refl

call/fresh : (ℕ → Goal) → Goal
call/fresh f (subst , counter) = (f counter) (subst , (suc counter))

_ : call/fresh (λ x → var x === symbol "a") ([] , 0) ≡ ((0 , symbol "a") ∷ [] , 1) ∷ []
_ = refl

disj : Goal → Goal → Goal
disj g1 g2 state = append-stream (g1 state) (g2 state)

conj : Goal → Goal → Goal
conj g1 g2 state = append-map g2 (g1 state)

_ : disj (call/fresh λ x → var x === symbol "z") (call/fresh λ x → var x === (symbol "s" ∷ symbol "z")) ([] , 0) ≡ ((0 , symbol "z") ∷ [] , 1) ∷ (((0 , (symbol "s" ∷ symbol "z")) ∷ [] , 1) ∷ [])
_ = refl

_ : (call/fresh λ x → call/fresh λ y → conj (var y === var x) (symbol "z" === var x)) ([] , 0) ≡ ((0 , symbol "z") ∷ (1 , var 0) ∷ [] , 2) ∷ []
_ = refl

{-# NON_TERMINATING #-}
peano : ℕ → Goal
peano n = (disj
        (var n === symbol "z")
        (call/fresh (λ r → conj
            (var n === (symbol "s" ∷ var r))
            (peano r)
        ))
    )

pull : Stream → Stream
pull [] = []
pull (x ∷ s) = x ∷ s

call/initial-state : ℕ → Goal → Stream
call/initial-state 0 g = pull (g ([] , 0))
call/initial-state n g = take n (pull (g ([] , 0)))
-}
