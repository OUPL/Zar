{-# OPTIONS --guardedness #-}

module ky where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Rational using (ℚ; _+_; _*_; _-_)
open import Data.Bool
open import Data.Bool.Properties
open import Data.Rational
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Empty
open import Relation.Nullary 
open import Relation.Nullary.Negation
open import Agda.Builtin.Size
open import Data.Product
open import Data.Unit
open import Data.Maybe
open import Data.String
open import Data.List

TyCon = List Set 

data Env : TyCon → Set₁ where
  nil : Env []
  cons : ∀{t Γ} →  t → Env Γ → Env (t ∷ Γ)

data Idx : Set → TyCon → Set₁ where
  fst : ∀{t Γ} → Idx t (t ∷ Γ)
  nxt : ∀{t t' Γ} → Idx t Γ → Idx t (t' ∷ Γ)

get : ∀{t Γ} → Idx t Γ → Env Γ → t
get fst       (cons v _)  = v
get (nxt idx) (cons _ vs) = get idx vs

upd : ∀{t Γ} → Idx t Γ → t -> Env Γ → Env Γ
upd fst       v' (cons _ vs) = cons v' vs
upd (nxt idx) v' (cons v vs) = cons v (upd idx v' vs)

data Exp : TyCon → Set → Set₁ where
  EVal : ∀{t Γ} → t → Exp Γ t
  EVar : ∀{t Γ} → Idx t Γ → Exp Γ t
  EPlus : ∀{Γ} → Exp Γ ℚ → Exp Γ ℚ → Exp Γ ℚ

data Com : TyCon → Set → Set₁ where
  CUpd : ∀{t Γ} → Idx t Γ → Exp Γ t → Com Γ t
  --CAlloc : ∀{t Γ} → Exp Γ t → Com (t ∷ Γ) ⊤ 
  CIte : ∀{t Γ} → Exp Γ Bool → Com Γ t → Com Γ t → Com Γ t
  CSeq : ∀{t Γ} → Com Γ ⊤ → Com Γ t → Com Γ t
  CWhile : ∀{t Γ} → Exp Γ Bool → Com Γ t → Com Γ ⊤

eval : ∀{t Γ} → Env Γ → Exp Γ t → t
eval ρ (EVal v) = v
eval ρ (EVar x) = get x ρ
eval ρ (EPlus e₁ e₂) = eval ρ e₁ + eval ρ e₂

-- Cf. Abel 2017
record Cotree (i : Size) (A : Set) (Γ : TyCon) : Set₁ where
  coinductive
  field
    ν : Env Γ -> Maybe (Env Γ)
    δ : ∀{j : Size< i} → Env Γ → A →  Cotree j A Γ 

open Cotree

∅ : ∀{i A Γ} → Cotree i A Γ
ν ∅ _   = nothing
δ ∅ _ _ = ∅

interp : ∀{i τ} → ∀(Γ) → Com Γ τ → Cotree i Bool Γ
interp Γ (CUpd x e) = t
  where t : ∀{j} → Cotree j Bool Γ
        ν t ρ   = just (upd x (eval ρ e) ρ)
        δ t ρ _ = ∅
interp Γ (CIte e c₁ c₂) = t
  where t : ∀{j : Size} → Cotree j Bool Γ 
        ν t ρ with eval ρ e
        ...      | true  = ν (interp Γ c₁) ρ 
        ...      | false = ν (interp Γ c₂) ρ 
        δ t ρ b with eval ρ e
        ...        | true  = δ (interp Γ c₁) ρ b
        ...        | false = δ (interp Γ c₂) ρ b
interp Γ (CSeq c₁ c₂) = t
  where t : ∀{j : Size} → Cotree j Bool Γ
        ν t ρ   = nothing
        δ t ρ b with ν (interp Γ c₁) ρ
        ...        | nothing = δ (interp Γ c₁) ρ  b
        ...        | just ρ' = δ (interp Γ c₂) ρ' b
{-        
interp (CWhile e c) = t
  where t : ∀{j : Size} → Cotree j Bool State
        ν t s with eval e s
        ...      | true  = ν (interp c) s
        ...      | false = true
        δ t s b with eval e s
        ...        | true  = δ (interp c) s b
        ...        | false = 
-}
