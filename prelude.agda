module prelude where

open import Agda.Primitive

data _≡_ {i}{A : Set i} (x : A) : A → Set i where
  refl : x ≡ x

infix 4 _≡_


coe : ∀ {i}
        {A B : Set i}
        (p : A ≡ B)
        → -----------
        A → B
        
coe refl a = a


_≡[_]≡_ : ∀ {i} {A B : Set i} (a : A) → (p : A ≡ B) → (b : B) → Set i
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_


ap : ∀ {i j}
       {A : Set i}
       {B : Set j}
       (f : A → B)
       {a₀ a₁ : A}
       (p : a₀ ≡ a₁)
       → -----------
       f a₀ ≡ f a₁
ap f refl = refl


trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
