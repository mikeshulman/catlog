open import Data.Sum
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality

-- a directed graph to start with

postulate G₀ : Set

postulate G : G₀ → G₀ → Set

-- types

data ty : Set where
  base : G₀ → ty
  O : ty
  _+_ : ty → ty → ty

infix 30 _+_

-- canonical/molecular/atomic terms

data _↓_ : ty → ty → Set        -- atomic

data _↕_ : ty → ty → Set        -- molecular

data _↑_ : ty → ty → Set        -- canonical

data _↓_ where
  var : (A : ty) → (A ↓ A)

data _↕_ where
  ↓↕ : {A : ty} {B : G₀} → (A ↓ base B) → (A ↕ base B)
  ar : {X : ty} {A B : G₀} (f : G A B) → (X ↕ base A) → (X ↕ base B)
  inl : {X A B : ty} → (X ↕ A) → (X ↕ A + B)
  inr : {X A B : ty} → (X ↕ B) → (X ↕ A + B)

data _↑_ where
  ↕↑ : {A B : ty} → (A ↕ B) → (A ↑ B)
  abort : {X C : ty} → (X ↓ O) → (X ↑ C)
  case : {X A B C : ty} → (X ↓ A + B) → (A ↑ C) → (B ↑ C) → (X ↑ C)

-- Unrestricted versions are admissible (excluding case for now)

ar' : {X : ty} {A B : G₀} (f : G A B) → (X ↑ base A) → (X ↑ base B)
ar' f (↕↑ M) =  ↕↑ (ar f M)
ar' f (abort M) = abort M
ar' f (case x M₁ M₂) =  case x (ar' f M₁) (ar' f M₂)

inl' : {X A B : ty} → (X ↑ A) → (X ↑ A + B)
inl' (↕↑ M) = ↕↑ (inl M)
inl' (abort M) = abort M
inl' (case x M₁ M₂) = case x (inl' M₁) (inl' M₂)

inr' : {X A B : ty} → (X ↑ B) → (X ↑ A + B)
inr' (↕↑ M) = ↕↑ (inr M)
inr' (abort M) = abort M
inr' (case x M₁ M₂) = case x (inr' M₁) (inr' M₂)

abort' : {X C : ty} → (X ↑ O) → (X ↑ C)
abort' (↕↑ ())
abort' (abort M) = abort M
abort' (case x M₁ M₂) =  case x (abort' M₁) (abort' M₂)

-- Hereditary substitution (together with admissible unrestricted case)

_↓⟦_⟧ : {A B C : ty} → (B ↓ C) → (A ↑ B) → (A ↑ C)
var A ↓⟦ M ⟧ = M

_↕⟦_⟧ : {A B C : ty} → (B ↕ C) → (A ↑ B) → (A ↑ C)

_↑⟦_⟧ : {A B C : ty} → (B ↑ C) → (A ↑ B) → (A ↑ C)

case' : {X A B C : ty} → (X ↑ A + B) → (A ↑ C) → (B ↑ C) → (X ↑ C)

↓↕ N ↕⟦ M ⟧ = N ↓⟦ M ⟧
ar f N ↕⟦ M ⟧ = ar' f (N ↕⟦ M ⟧)
inl N ↕⟦ M ⟧ = inl' (N ↕⟦ M ⟧)
inr N ↕⟦ M ⟧ = inr' (N ↕⟦ M ⟧)

↕↑ N ↑⟦ M ⟧ = N ↕⟦ M ⟧
abort N ↑⟦ M ⟧ =  abort' (N ↓⟦ M ⟧)
case x N₁ N₂ ↑⟦ M ⟧ = case' (x ↓⟦ M ⟧) N₁ N₂

case' (↕↑ (inl M)) P Q = P ↑⟦ ↕↑ M ⟧
case' (↕↑ (inr M)) P Q = Q ↑⟦ ↕↑ M ⟧
case' (abort M) P Q = abort M
case' (case x M₁ M₂) P Q =  case x (case' M₁ P Q) (case' M₂ P Q)

-- identites

hid : (A : ty) → (A ↑ A)
hid (base A) = ↕↑ (↓↕ (var (base A)))
hid O = abort (var O)
hid (A + B) = case (var (A + B)) (inl' (hid A)) (inr' (hid B))

-- ar' commutes with substitution

ar-abort : ∀ {X} {C D : G₀} (f : G C D) (M : X ↑ O) → abort' M ≡ ar' f (abort' M)
ar-abort f (↕↑ ())
ar-abort f (abort x) = refl
ar-abort f (case x M₁ M₂) = cong₂ (case x) (ar-abort f M₁) (ar-abort f M₂) 

ar-case : ∀ {X A B} {C D : G₀} (f : G C D) (M : X ↑ A + B) (P : A ↑ base C) (Q : B ↑ base C) 
  → case' M (ar' f P) (ar' f Q) ≡ ar' f (case' M P Q)

ar↑ : {X A : ty} {B C : G₀} (f : G B C) (N : A ↑ base B) (M : X ↑ A) → ar' f N ↑⟦ M ⟧ ≡ ar' f (N ↑⟦ M ⟧)

ar-case f (↕↑ (inl x)) P Q = ar↑ f P (↕↑ x)
ar-case f (↕↑ (inr x)) P Q = ar↑ f Q (↕↑ x)
ar-case f (abort x) P Q = refl
ar-case f (case x M₁ M₂) P Q = cong₂ (case x) (ar-case f M₁ P Q) (ar-case f M₂ P Q) 

ar↑ f (↕↑ x) M = refl
ar↑ f (abort x) M = ar-abort f (x ↓⟦ M ⟧)
ar↑ f (case x N₁ N₂) M = ar-case f (x ↓⟦ M ⟧) N₁ N₂

ar↕ : {X Y : ty} {A B : G₀} (f : G A B) (N : Y ↕ base A) (M : X ↑ Y) → (ar' f (↕↑ N)) ↑⟦ M ⟧ ≡ ar' f (N ↕⟦ M ⟧)
ar↕ f (↓↕ (var ._)) M = refl
ar↕ f (ar g N) M = refl

-- inl' commutes with substitution

inl-abort : ∀ {X A B} (w : X ↑ O) → abort' w ≡ inl' {A = A} {B = B} (abort' w)
inl-abort (↕↑ ())
inl-abort (abort x) = refl
inl-abort (case x M₁ M₂) = cong₂ (case x) (inl-abort M₁) (inl-abort M₂) 

inl-case : ∀ {X A B C D} (M : X ↑ A + B) (P : A ↑ C) (Q : B ↑ C) 
  → case' M (inl' {B = D} P) (inl' {B = D} Q) ≡ inl' {B = D} (case' M P Q)

inl↑ : {X A B C : ty} (N : A ↑ B) (M : X ↑ A) → inl' N ↑⟦ M ⟧ ≡ inl' {B = C} (N ↑⟦ M ⟧)

inl-case (↕↑ (inl x)) P Q = inl↑ P (↕↑ x)
inl-case (↕↑ (inr x)) P Q = inl↑ Q (↕↑ x)
inl-case (abort x) P Q = refl
inl-case (case x M₁ M₂) P Q = cong₂ (case x) (inl-case M₁ P Q) (inl-case M₂ P Q) 

inl↑ (↕↑ x) M = refl
inl↑ (abort x) M = inl-abort (x ↓⟦ M ⟧)
inl↑ (case x N₁ N₂) M = inl-case (x ↓⟦ M ⟧) N₁ N₂

inl↕ : {X Y A B : ty} (N : Y ↕ A) (M : X ↑ Y) → (inl' {B = B} (↕↑ N)) ↑⟦ M ⟧ ≡ inl' {B = B} (N ↕⟦ M ⟧)
inl↕ (↓↕ x) M = refl
inl↕ (ar f N) M = refl
inl↕ (inl N) M = refl
inl↕ (inr N) M = refl

-- inr' commutes with substitution

inr-abort : ∀ {X A B} (w : X ↑ O) → abort' w ≡ inr' {A = A} {B = B} (abort' w)
inr-abort (↕↑ ())
inr-abort (abort x) = refl
inr-abort (case x M₁ M₂) = cong₂ (case x) (inr-abort M₁) (inr-abort M₂) 

inr-case : ∀ {X A B C D} (M : X ↑ A + B) (P : A ↑ C) (Q : B ↑ C) 
  → case' M (inr' {A = D} P) (inr' {A = D} Q) ≡ inr' {A = D} (case' M P Q)

inr↑ : {X A B C : ty} (N : A ↑ B) (M : X ↑ A) → inr' N ↑⟦ M ⟧ ≡ inr' {A = C} (N ↑⟦ M ⟧)

inr-case (↕↑ (inl x)) P Q = inr↑ P (↕↑ x)
inr-case (↕↑ (inr x)) P Q = inr↑ Q (↕↑ x)
inr-case (abort x) P Q = refl
inr-case (case x M₁ M₂) P Q = cong₂ (case x) (inr-case M₁ P Q) (inr-case M₂ P Q) 

inr↑ (↕↑ x) M = refl
inr↑ (abort x) M = inr-abort (x ↓⟦ M ⟧)
inr↑ (case x N₁ N₂) M = inr-case (x ↓⟦ M ⟧) N₁ N₂

inr↕ : {X Y A B : ty} (N : Y ↕ B) (M : X ↑ Y) → (inr' {A = A} (↕↑ N)) ↑⟦ M ⟧ ≡ inr' {A = A} (N ↕⟦ M ⟧)
inr↕ (↓↕ x) M = refl
inr↕ (ar f N) M = refl
inr↕ (inl N) M = refl
inr↕ (inr N) M = refl

-- abort' commutes with substitution

abort-abort : ∀ {A C} (w : A ↑ O) → abort' {C = C} w ≡ abort' (abort' w)
abort-abort (↕↑ ())
abort-abort (abort x) = refl
abort-abort (case x M₁ M₂) = cong₂ (case x) (abort-abort M₁) (abort-abort M₂)

abort-case : ∀ {A C A₁ B₁} (w : A ↑ A₁ + B₁) (N₁ : A₁ ↑ O) (N₂ : B₁ ↑ O)
  → case' w (abort' N₁) (abort' N₂) ≡ abort' {C = C} (case' w N₁ N₂)

abort↑ : {A B C : ty} (N : B ↑ O) (M : A ↑ B) → (abort' N) ↑⟦ M ⟧ ≡ abort' {C = C} (N ↑⟦ M ⟧)

abort-case (↕↑ (inl x)) P Q = abort↑ P (↕↑ x)
abort-case (↕↑ (inr x)) P Q = abort↑ Q (↕↑ x)
abort-case (abort x) P Q = refl
abort-case (case x M₁ M₂) P Q = cong₂ (case x) (abort-case M₁ P Q) (abort-case M₂ P Q)

abort↑ (↕↑ ()) M
abort↑ (abort x) M = abort-abort (x ↓⟦ M ⟧)
abort↑ (case x N₁ N₂) M = abort-case (x ↓⟦ M ⟧) N₁ N₂

-- some commuting conversions

κ↕-abort : {X C D : ty} (M : X ↓ O) (P : C ↕ D) → abort M ≡ P ↕⟦ abort M ⟧
κ↕-abort M (↓↕ (var ._)) = refl
κ↕-abort M (ar f P) = cong (ar' f) (κ↕-abort M P)
κ↕-abort M (inl P) = cong inl' (κ↕-abort M P)
κ↕-abort M (inr P) = cong inr' (κ↕-abort M P)

κ↑-abort : {X C D : ty} (M : X ↓ O) (P : C ↑ D) → abort M ≡ P ↑⟦ abort M ⟧
κ↑-abort M (↕↑ P) = κ↕-abort M P
κ↑-abort M (abort (var .O)) = refl
κ↑-abort M (case (var ._) P P₁) = refl

κ↕-case : {X A B C D : ty} (M : X ↓ A + B) (P : A ↑ C) (Q : B ↑ C) (R : C ↕ D) 
  → case M (R ↕⟦ P ⟧) (R ↕⟦ Q ⟧) ≡ R ↕⟦ case M P Q ⟧
κ↕-case M P Q (↓↕ (var ._)) = refl
κ↕-case M P Q (ar f R) = cong (ar' f) (κ↕-case M P Q R)
κ↕-case M P Q (inl R) = cong inl' (κ↕-case M P Q R)
κ↕-case M P Q (inr R) = cong inr' (κ↕-case M P Q R)

κ↑-case : {X A B C D : ty} (M : X ↓ A + B) (P : A ↑ C) (Q : B ↑ C) (R : C ↑ D) 
  → case M (R ↑⟦ P ⟧) (R ↑⟦ Q ⟧) ≡ R ↑⟦ case M P Q ⟧
κ↑-case M P Q (↕↑ R) = κ↕-case M P Q R
κ↑-case M P Q (abort (var .O)) = refl
κ↑-case M P Q (case (var ._) R R₁) = refl

κ↕-abort' : {X C D : ty} (M : X ↑ O) (P : C ↕ D) → abort' M ≡ P ↕⟦ abort' M ⟧
κ↕-abort' (↕↑ ()) P
κ↕-abort' (abort x) P = κ↕-abort x P
κ↕-abort' (case x M₁ M₂) P = trans (cong₂ (case x) (κ↕-abort' M₁ P) (κ↕-abort' M₂ P)) (κ↕-case x (abort' M₁) (abort' M₂) P)

κ↑-abort' : {X C D : ty} (M : X ↑ O) (P : C ↑ D) → abort' M ≡ P ↑⟦ abort' M ⟧
κ↑-abort' (↕↑ ()) P
κ↑-abort' (abort x) P = κ↑-abort x P
κ↑-abort' (case x M₁ M₂) P = trans (cong₂ (case x) (κ↑-abort' M₁ P) (κ↑-abort' M₂ P)) (κ↑-case x (abort' M₁) (abort' M₂) P)

-- β-reductions

β-inl : {X A B C : ty} (M : X ↑ A) (P : A ↑ C) (Q : B ↑ C) → case' (inl' M) P Q ≡ P ↑⟦ M ⟧
β-inl (↕↑ x) P Q = refl
β-inl (abort x) P Q = κ↑-abort x P
β-inl (case x M₁ M₂) P Q = trans (cong₂ (case x) (β-inl M₁ P Q) (β-inl M₂ P Q)) (κ↑-case x M₁ M₂ P)

β-inr : {X A B C : ty} (M : X ↑ B) (P : A ↑ C) (Q : B ↑ C) → case' (inr' M) P Q ≡ Q ↑⟦ M ⟧
β-inr (↕↑ x) P Q = refl
β-inr (abort x) P Q = κ↑-abort x Q
β-inr (case x M₁ M₂) P Q = trans (cong₂ (case x) (β-inr M₁ P Q) (β-inr M₂ P Q)) (κ↑-case x M₁ M₂ Q)

-- unitality

hid↕ : {A B : ty} (M : A ↕ B) → M ↕⟦ hid A ⟧ ≡ ↕↑ M
hid↕ (↓↕ (var ._)) = refl
hid↕ (ar f M) = cong (ar' f) (hid↕ M)
hid↕ (inl M) = cong inl' (hid↕ M)
hid↕ (inr M) = cong inr' (hid↕ M)

hid↑ : {A B : ty} (M : A ↑ B) → M ↑⟦ hid A ⟧ ≡ M
hid↑ (↕↑ M) = hid↕ M
hid↑ (abort (var .O)) = refl
hid↑ (case (var ._) M₁ M₂) = cong₂ (case _) (trans (β-inl (hid _) M₁ M₂) (hid↑ M₁)) (trans (β-inr (hid _) M₁ M₂) (hid↑ M₂))

↑hid : {A B : ty} (M : A ↑ B) → hid B ↑⟦ M ⟧ ≡ M

inl-hid : {X A B : ty} (M : X ↑ A) → inl' {B = B} (hid A) ↑⟦ M ⟧ ≡ inl' M -- not mutual, just auxiliary
inr-hid : {X A B : ty} (M : X ↑ B) → inr' {A = A} (hid B) ↑⟦ M ⟧ ≡ inr' M -- not mutual, just auxiliary

↑hid {B = base x} M = refl
↑hid {B = O} (↕↑ ())
↑hid {B = O} (abort x) = refl
↑hid {B = O} (case x M₁ M₂) = cong₂ (case x) (↑hid M₁) (↑hid M₂)
↑hid {B = B₁ + B₂} (↕↑ (inl x)) = inl-hid (↕↑ x)
↑hid {B = B₁ + B₂} (↕↑ (inr x)) = inr-hid (↕↑ x)
↑hid {B = B₁ + B₂} (abort x) = refl
↑hid {B = B₁ + B₂} (case x M₁ M₂) = cong₂ (case x) (↑hid M₁) (↑hid M₂)

inl-hid {X} {A} {B} M = trans (inl↑ (hid A) M) (cong inl' (↑hid M))

inr-hid {X} {A} {B} M = trans (inr↑ (hid B) M) (cong inr' (↑hid M))

-- case' commutes with substitution
-- AND
-- the last commuting conversion
-- AND
-- assocativity of substitution

case-abort : ∀ {Y A B C} (w : Y ↑ O) (P : A ↑ C) (Q : B ↑ C) →
             abort' w ≡ case' (abort' w) P Q

case-case : ∀ {Y A B C A₁ B₁} (w : Y ↑ A₁ + B₁) (N₁ : A₁ ↑ A + B)
              (N₂ : B₁ ↑ A + B) (P : A ↑ C) (Q : B ↑ C) →
            case' w (case' N₁ P Q) (case' N₂ P Q) ≡ case' (case' w N₁ N₂) P Q

case↑ : {X Y A B C : ty} (N : X ↑ A + B) (M : Y ↑ X) (P : A ↑ C) (Q : B ↑ C)
  → case' N P Q ↑⟦ M ⟧ ≡ case' (N ↑⟦ M ⟧) P Q

κ↕-case' : {X A B C D : ty} (M : X ↑ A + B) (P : A ↑ C) (Q : B ↑ C) (R : C ↕ D) 
  → case' M (R ↕⟦ P ⟧) (R ↕⟦ Q ⟧) ≡ R ↕⟦ case' M P Q ⟧

κ↑-case' : {X A B C D : ty} (M : X ↑ A + B) (P : A ↑ C) (Q : B ↑ C) (R : C ↑ D) 
  → case' M (R ↑⟦ P ⟧) (R ↑⟦ Q ⟧) ≡ R ↑⟦ case' M P Q ⟧

assoc↕↑ : {A B C D : ty} (P : C ↕ D) (N : B ↑ C) (M : A ↑ B)
  → (P ↕⟦ N ⟧) ↑⟦ M ⟧ ≡ P ↕⟦ (N ↑⟦ M ⟧) ⟧

assoc↑↑ : {A B C D : ty} (P : C ↑ D) (N : B ↑ C) (M : A ↑ B)
  → (P ↑⟦ N ⟧) ↑⟦ M ⟧ ≡ P ↑⟦ (N ↑⟦ M ⟧) ⟧

case-abort (↕↑ ()) P Q
case-abort (abort x) P Q = refl
case-abort (case x M₁ M₂) P Q = cong₂ (case x) (case-abort M₁ P Q) (case-abort M₂ P Q)

case-case (↕↑ (inl x)) N₁ N₂ P Q = case↑ N₁ (↕↑ x) P Q
case-case (↕↑ (inr x)) N₁ N₂ P Q = case↑ N₂ (↕↑ x) P Q
case-case (abort x) N₁ N₂ P Q = refl
case-case (case x M₁ M₂) N₁ N₂ P Q = cong₂ (case x) (case-case M₁ N₁ N₂ P Q) (case-case M₂ N₁ N₂ P Q)

case↑ (↕↑ (inl x)) M P Q = trans (assoc↑↑ P (↕↑ x) M) (sym (β-inl (x ↕⟦ M ⟧) P Q))
case↑ (↕↑ (inr x)) M P Q = trans (assoc↑↑ Q (↕↑ x) M) (sym (β-inr (x ↕⟦ M ⟧) P Q))
case↑ (abort x) M P Q = case-abort (x ↓⟦ M ⟧) P Q
case↑ (case x N₁ N₂) M P Q = case-case (x ↓⟦ M ⟧) N₁ N₂ P Q

κ↕-case' (↕↑ (inl x)) P Q R = assoc↕↑ R P (↕↑ x)
κ↕-case' (↕↑ (inr x)) P Q R = assoc↕↑ R Q (↕↑ x)
κ↕-case' (abort x) P Q R = κ↕-abort x R
κ↕-case' (case x M₁ M₂) P Q R = trans (cong₂ (case x) (κ↕-case' M₁ P Q R) (κ↕-case' M₂ P Q R)) (κ↕-case x (case' M₁ P Q) (case' M₂ P Q) R) 

κ↑-case' (↕↑ (inl x)) P Q R = assoc↑↑ R P (↕↑ x)
κ↑-case' (↕↑ (inr x)) P Q R = assoc↑↑ R Q (↕↑ x)
κ↑-case' (abort x) P Q R = κ↑-abort x R
κ↑-case' (case x M₁ M₂) P Q R = trans (cong₂ (case x) (κ↑-case' M₁ P Q R) (κ↑-case' M₂ P Q R)) (κ↑-case x (case' M₁ P Q) (case' M₂ P Q) R)

assoc↕↑ (↓↕ (var ._)) N M = refl
assoc↕↑ (ar f P) N M = trans (trans (ar↑ f (P ↕⟦ N ⟧) M) (cong (ar' f) (assoc↕↑ P N M))) (ar↕ f P (N ↑⟦ M ⟧))
assoc↕↑ (inl P)  N M = trans (trans (inl↑  (P ↕⟦ N ⟧) M) (cong inl'    (assoc↕↑ P N M))) (inl↕  P (N ↑⟦ M ⟧))
assoc↕↑ (inr P)  N M = trans (trans (inr↑  (P ↕⟦ N ⟧) M) (cong inr'    (assoc↕↑ P N M))) (inr↕  P (N ↑⟦ M ⟧))

assoc↑↑ (↕↑ P) N M = assoc↕↑ P N M
assoc↑↑ (abort (var .O)) N M = abort↑ N M
assoc↑↑ (case (var ._) P₁ P₂) N M = case↑ N M P₁ P₂

-- weak eta

wη-abort : {X : ty} (M : X ↑ O) → M ≡ abort' M
wη-abort (↕↑ ())
wη-abort (abort x) = refl
wη-abort (case x M₁ M₂) = cong₂ (case x) (wη-abort M₁) (wη-abort M₂)

wη-case : {X A B : ty} (M : X ↑ A + B) → M ≡ case' M (inl' (hid A)) (inr' (hid B))
wη-case (↕↑ (inl x)) = sym (trans (inl↑ (hid _) (↕↑ x)) (cong inl' (↑hid (↕↑ x))))
wη-case (↕↑ (inr x)) = sym (trans (inr↑ (hid _) (↕↑ x)) (cong inr' (↑hid (↕↑ x))))
wη-case (abort x) = refl
wη-case (case x M₁ M₂) = cong₂ (case x) (wη-case M₁) (wη-case M₂)

-- strong eta-expansions

η-abort : {X C : ty} (M : X ↑ O) (P : O ↑ C) → P ↑⟦ M ⟧ ≡ abort' M
η-abort (↕↑ ()) P
η-abort (abort M) P = sym (κ↑-abort M P)
η-abort (case x M₁ M₂) P = trans (sym (κ↑-case x M₁ M₂ P)) (cong₂ (case x) (η-abort M₁ P) (η-abort M₂ P))

η-case : {X A B C : ty} (M : X ↑ A + B) (P : A + B ↑ C)
  → P ↑⟦ M ⟧ ≡ case' M (P ↑⟦ inl' (hid A) ⟧) (P ↑⟦ inr' (hid B) ⟧)
η-case (↕↑ (inl x)) P = trans (cong (λ y → P ↑⟦ y ⟧) (sym (inl-hid (↕↑ x)))) (sym (assoc↑↑ P (inl' (hid _)) (↕↑ x)))
η-case (↕↑ (inr x)) P = trans (cong (λ y → P ↑⟦ y ⟧) (sym (inr-hid (↕↑ x)))) (sym (assoc↑↑ P (inr' (hid _)) (↕↑ x)))
η-case (abort M) P = sym (κ↑-abort M P)
η-case (case x M₁ M₂) P = trans (sym (κ↑-case x M₁ M₂ P)) (cong₂ (case x) (η-case M₁ P) (η-case M₂ P))

-- Universal properties

β-inl-ump : {A B C : ty} (P : A ↑ C) (Q : B ↑ C) → case' (hid (A + B)) P Q ↑⟦ inl' (hid A) ⟧ ≡ P
β-inl-ump {A} {B} P Q = trans (case↑ (hid (A + B)) (inl' (hid A)) P Q)
                       (trans (cong (λ y → case' y P Q) (↑hid (inl' (hid A))))
                       (trans (β-inl (hid A) P Q)
                              (hid↑ P)))

β-inr-ump : {A B C : ty} (P : A ↑ C) (Q : B ↑ C) → case' (hid (A + B)) P Q ↑⟦ inr' (hid B) ⟧ ≡ Q
β-inr-ump {A} {B} P Q = trans (case↑ (hid (A + B)) (inr' (hid B)) P Q)
                       (trans (cong (λ y → case' y P Q) (↑hid (inr' (hid B))))
                       (trans (β-inr (hid B) P Q)
                              (hid↑ Q)))

η-abort-ump : {C : ty} (P : O ↑ C) → P ≡ abort' (hid O)
η-abort-ump P = trans (sym (hid↑ P)) (η-abort (hid O) P)

η-case-ump : {A B C : ty} (P : A + B ↑ C) 
  → P ≡ case' (hid (A + B)) (P ↑⟦ inl' (hid A) ⟧) (P ↑⟦ inr' (hid B) ⟧)
η-case-ump {A} {B} {C} P = trans (sym (hid↑ P)) (η-case (hid (A + B)) P)
