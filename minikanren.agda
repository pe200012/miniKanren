
open import Data.Bool using (Bool; true; false; T?; _∧_; _∨_; not; _xor_; if_then_else_)
open import Data.String using (_==_; String)
open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)


data Term : Set where
    symbol : String → Term
    boolean : Bool → Term
    _∷_ : Term → Term → Term
    var : ℕ → Term

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
