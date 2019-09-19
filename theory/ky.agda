{-# OPTIONS --guardedness --without-K #-}

module ky where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Rational using (ℚ; _+_; _*_; _-_)
open import Data.Bool
open import Data.Bool.Properties
open import Data.Rational
open import Data.Nat as ℕ using (ℕ; zero; suc; ⌊_/2⌋)
open import Data.Empty
open import Relation.Nullary 
open import Relation.Nullary.Negation
open import Agda.Builtin.Size
open import Data.Product
open import Data.Unit
open import Data.Maybe
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

record Cotree (i : Size) (A : Set) (Γ : TyCon) : Set₁

data Pattern : Size → TyCon → Set₁ where
  mkPattern : ∀{i Γ} →  --{j₁ j₂ : Size< i} → 
    (Cotree i Bool Γ → Cotree i Bool Γ → Cotree i Bool Γ) →
    Pattern i Γ

data Com : Size → TyCon → Set → Set₁ where
  CSkip : ∀{i Γ} → Com i Γ ⊤ 
  CPrim : ∀{i t Γ} → Pattern i Γ → Com i Γ t → Com i Γ t → Com i Γ t
  --CFlip : ∀{i t Γ} → Com i Γ t → Com i Γ t → Com i Γ t
  CUpd : ∀{i t Γ} → Idx t Γ → Exp Γ t → Com i Γ ⊤ 
  --CAlloc : ∀{t Γ} → Exp Γ t → Com (t ∷ Γ) ⊤ 
  CIte : ∀{i t Γ} → Exp Γ Bool → Com i Γ t → Com i Γ t → Com i Γ t
  CSeq : ∀{i t Γ} → Com i Γ ⊤ → Com i Γ t → Com i Γ t
  CWhile : ∀{i t Γ} → Exp Γ Bool → Com i Γ t → Com i Γ ⊤

eval : ∀{t Γ} → Env Γ → Exp Γ t → t
eval ρ (EVal v) = v
eval ρ (EVar x) = get x ρ
eval ρ (EPlus e₁ e₂) = eval ρ e₁ + eval ρ e₂

-- Cf. Abel 2017 (Equational Reasoning about Formal Languages in Coalgebraic Style)
record Cotree i A Γ where
  coinductive
  field
    ν : Env Γ -> Maybe (Env Γ)
    δ : ∀{j : Size< i} → Env Γ → A →  Cotree j A Γ 

open Cotree

∅ : ∀{i A Γ} → Cotree i A Γ
ν ∅ _   = nothing
δ ∅ _ _ = ∅

flip : ∀(i Γ) → Cotree i Bool Γ → Cotree i Bool Γ → Cotree i Bool Γ
flip i Γ t₁ t₂ = t
  where t : Cotree i Bool Γ
        ν t ρ       = nothing
        δ t ρ true  = t₁
        δ t ρ false = t₂
        
interp : ∀(i){τ} → ∀(Γ) → Com i Γ τ → Cotree i Bool Γ
interp i Γ CSkip = t
  where t : ∀{j} → Cotree j Bool Γ
        ν t ρ   = just ρ 
        δ t ρ _ = ∅
interp i Γ (CPrim (mkPattern f) c₁ c₂) = t
  where t : Cotree i Bool Γ
        ν t ρ   = nothing
        δ t ρ _ = f (interp i Γ c₁) (interp i Γ c₂)
{-interp i Γ (CFlip c₁ c₂) = t
  where t : Cotree i Bool Γ
        ν t ρ       = nothing
        δ t ρ true  = interp i Γ c₁
        δ t ρ false = interp i Γ c₂-}
interp i Γ (CUpd x e) = t
  where t : ∀{j} → Cotree j Bool Γ
        ν t ρ   = just (upd x (eval ρ e) ρ)
        δ t ρ _ = ∅
interp i Γ (CIte e c₁ c₂) = t
  where t : Cotree i Bool Γ 
        ν t ρ with eval ρ e
        ...      | true  = ν (interp i Γ c₁) ρ 
        ...      | false = ν (interp i Γ c₂) ρ 
        δ t ρ b with eval ρ e
        ...        | true  = δ (interp i Γ c₁) ρ b
        ...        | false = δ (interp i Γ c₂) ρ b
interp i Γ (CSeq c₁ c₂) = t
  where t : Cotree i Bool Γ
        ν t ρ   = nothing
        δ t ρ b with ν (interp i Γ c₁) ρ
        ...        | nothing = δ (interp i Γ c₁) ρ  b
        ...        | just ρ' = δ (interp i Γ c₂) ρ' b
interp i Γ (CWhile e c) = t
  where t : Cotree i Bool Γ 
        ν t ρ with eval ρ e
        ...      | true  = ν (interp i Γ c) ρ 
        ...      | false = just ρ 
        δ t ρ b with eval ρ e
        ...        | true  = δ (interp i Γ c) ρ b
        ...        | false = ∅ 

-- Flip as a derived command
cflip : ∀(i Γ){τ} → Com i Γ τ → Com i Γ τ → Com i Γ τ
cflip i Γ = CPrim (mkPattern (flip i Γ))
