{-# OPTIONS --no-positivity-check #-}
module Kiplingesque where

open import Data.Product
open import Data.Sum
open import Data.Unit

-- Normalised values
mutual
  data U : Set where
    `Π : (S : U) → (El S → U) → U
    _`∧_ : (S : U) → (T : U) → U
    _`∨_ : (S : U) → (T : U) → U
    `U : U -- optional but fun!
  El : U → Set
  El (`Π S T) = (s : El S) → El (T s)
  El `U = U
  El (S `∧ T) = El S × El T
  El (S `∨ T) = El S ⊎ El T

-- Subtyping
mutual
  data _⊑_ : U -> U -> Set where
    meetL1 : ∀ {S S' T} -> S ⊑ T -> (S `∧ S') ⊑ T
    meetL2 : ∀ {S S' T} -> S' ⊑ T -> (S `∧ S') ⊑ T
    meetR : ∀ {S T T'} -> S ⊑ T -> S ⊑ T' -> S ⊑ (T `∧ T')
    joinL : ∀ {S S' T} -> S ⊑ T -> S' ⊑ T -> (S `∨ S') ⊑ T
    joinR1 : ∀ {S T T'} -> S ⊑ T -> S ⊑ (T `∨ T')
    joinR2 : ∀ {S T T'} -> S ⊑ T' -> S ⊑ (T `∨ T')
    sub-> : ∀ {V W V' W'} -> (p : V' ⊑ V) -> (∀ x -> (W (convert p x) ⊑ W' x)) -> (`Π V W) ⊑ (`Π V' W')
    sub-refl : ∀ {V} -> V ⊑ V
    -- etc.

  convert : ∀ {A B} -> A ⊑ B -> El A -> El B
  convert (meetL1 p) (x , _) = convert p x
  convert (meetL2 p) (_ , x) = convert p x
  convert (meetR p q) x = (convert p x) , (convert q x)
  convert (joinL p q) (inj₁ x) = convert p x
  convert (joinL p q) (inj₂ y) = convert q y
  convert (joinR1 p) x = inj₁ (convert p x)
  convert (joinR2 p) x = inj₂ (convert p x)
  convert (sub-> p q) f = \x -> convert (q x) (f (convert p x ))
  convert (sub-refl) x = x

-- Contexts and environments
mutual
  data Cx : Set where
    — : Cx
    _,_ : (Γ : Cx) → (Env Γ -> U) → Cx

  Env : Cx -> Set
  Env — = ⊤
  Env (Γ , A) = Σ (Env Γ) (λ x → El (A x))

-- (Value for) a type in a given context
Typ : Cx -> Set
Typ Γ = (ρ : Env Γ) -> U

-- Variable: proof that a type is found in a given context
data _∋_ : (Γ : Cx) (T : Typ Γ) -> Set where
  here : ∀ {Γ T} -> (Γ , T) ∋ (λ x → T (proj₁ x))
  there : ∀ {Γ T S} -> Γ ∋ T -> (Γ , S) ∋ (λ x → T (proj₁ x))

-- Lookup a variable in an environment
lk : ∀ {Γ T} -> Γ ∋ T -> (ρ : Env Γ) -> El (T ρ)
lk here (_ , v) = v
lk (there i) (ρ , _) = lk i ρ

mutual
  -- Typing judgement
  data _⊢_ : (Γ : Cx) -> Typ Γ -> Set
  data _⊢Type : (Γ : Cx) -> Set
  eval : ∀ {Γ A} -> (ρ : Env Γ) -> Γ ⊢ A -> El (A ρ)
  evalTyp : ∀ {Γ} -> (ρ : Env Γ) -> Γ ⊢Type -> U


  data _⊢_  where
    var : ∀ {Γ T} -> Γ ∋ T -> Γ ⊢ T
    app : ∀ {Γ A} {B : Typ (Γ , A)} ->
          Γ ⊢ (λ ρ → `Π (A ρ) (λ x → B (ρ , x))) -> (u : Γ ⊢ A) ->
          Γ ⊢ (λ ρ → B ( ρ , eval ρ u ))
    lam : ∀ {Γ A} {B : Typ (Γ , A)} ->
          (Γ , A) ⊢ B ->
          Γ ⊢ (λ ρ → `Π (A ρ) (λ x → (B (ρ , x))))
    typ : ∀ {Γ} -> Γ ⊢Type -> Γ ⊢ (λ ρ → `U)
    conv : ∀ {Γ} {A B : Typ Γ} -> Γ ⊢ A -> ((ρ : Env Γ) -> A ρ ⊑ B ρ) -> Γ ⊢ B

  data _⊢Type where
    Pi : ∀ {Γ} -> (A : Γ ⊢Type) -> (Γ , (λ ρ → evalTyp ρ A)) ⊢Type
                   -> Γ ⊢Type
    Type : ∀ {Γ} -> Γ ⊢Type
    Elim : ∀ {Γ} -> (A : Γ ⊢ (λ ρ → `U)) -> Γ ⊢Type
    Meet : ∀ {Γ} -> Γ ⊢Type -> Γ ⊢Type -> Γ ⊢Type

  -- Evaluation of well-typed terms
  evalTyp ρ (Pi A B) = `Π (evalTyp ρ A) (λ x → evalTyp (ρ , x) B)
  evalTyp _ Type = `U
  evalTyp ρ (Meet A B) = evalTyp ρ A `∧ evalTyp ρ B
  evalTyp ρ (Elim A) = eval ρ A

  eval ρ (var x) = lk x ρ
  eval ρ (app t u) = eval ρ t (eval ρ u)
  eval ρ (lam t) = λ x → eval (ρ , x) t
  eval ρ (typ T) = evalTyp ρ T
  eval ρ (conv t s) = convert (s ρ) (eval ρ t)
