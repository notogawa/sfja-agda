module Rel-J where

open import Level
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; sym; cong; trans)

open import Basics-J
open import Poly-J
open import Logic-J

relation : ∀ {a b} → Set a → Set (a ⊔ suc b)
relation {b = b} X = X → X → Set b

-- 関係の基本性質 -------------------------------------------------------------

partial-function : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
partial-function R = ∀ x y₁ y₂ → R x y₁ → R x y₂ → y₁ ≡ y₂

next-nat-partial-function : partial-function next-nat
next-nat-partial-function x .(S x) .(S x) nn nn = refl

le-not-a-partial-function : ~ (partial-function _≤_)
le-not-a-partial-function pf with pf 0 1 2 (le-S le-n) (le-S (le-S le-n))
le-not-a-partial-function pf | ()

{-
練習問題:★★, optional

Logic_J.v に定義された total_relation が部分関数ではないことを示しなさい。
-}
total-relation-not-a-partial-function : ~ (partial-function total-relation)
total-relation-not-a-partial-function pf with pf 0 1 2 (tot 0 1) (tot 0 2)
total-relation-not-a-partial-function pf | ()

{-
練習問題:★★, optional

Logic_J.v に定義された empty_relation が部分関数であることを示しなさい。
-}
empty-relation-not-a-partial-function : partial-function empty-relation
empty-relation-not-a-partial-function x y₁ y₂ () R₂


reflexive : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
reflexive R = ∀ a → R a a

le-reflexive : reflexive _≤_
le-reflexive = λ a → le-n

transitive : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
transitive R = ∀ a b c → R a b → R b c → R a c

le-trans : transitive _≤_
le-trans a .c c a≤b le-n = a≤b
le-trans a b .(S m) a≤b (le-S {m} b≤c) = le-S (le-trans a b m a≤b b≤c)

lt-trans : transitive _<_
lt-trans a b c a<b = le-trans (S a) (S b) c (le-S a<b)

{-
練習問題:★★, optional

lt_trans は、帰納法を使って手間をかければ、le_trans を使わずに証明することができます。 これをやってみなさい。
-}
lt-trans' : transitive _<_
lt-trans' a b .(S b) a<b le-n = le-S a<b
lt-trans' a b .(S m) a<b (le-S {m} b<c) = le-S (lt-trans a b m a<b b<c)

{-
練習問題:★★, optional

同じことを、oについての帰納法で証明しなさい。
-}
lt-trans'' : transitive _<_
lt-trans'' a b O a<b ()
lt-trans'' a b (S c) a<b b<c = le-trans (S a) (S b) (S c) (le-S a<b) b<c


le-Sn-le : ∀ n m → S n ≤ m → n ≤ m
le-Sn-le n m = le-trans n (S n) m (le-S le-n)

{-
練習問題:★, optional
-}
le-S-n : ∀ n m → S n ≤ S m → n ≤ m
le-S-n .m m le-n = le-n
le-S-n n m (le-S Sn≤Sm) = le-trans n (S n) m (le-S le-n) Sn≤Sm

{-
練習問題:★★, optional(le_Sn_n_inf)

以下の定理の非形式的な証明を示しなさい。

定理: すべてのnについて、~(S n <= n)
-}
-- 略
{-
形式的な証明は後のoptionalな練習問題ですが、 ここでは、形式的な証明を行わずに、まず非形式的な証明を示しなさい。
-}
{-
練習問題:★, optional
-}
le-Sn-n-inf : ∀ n → ~ (S n ≤ n)
le-Sn-n-inf O ()
le-Sn-n-inf (S n) Sn≤n = le-Sn-n-inf n (le-S-n (S n) n Sn≤n)


symmetric : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
symmetric R = ∀ a b → R a b → R b a

{-
練習問題:★★, optional
-}
le-not-symmetric : ~ (symmetric _≤_)
le-not-symmetric sym with sym 0 1 (le-S le-n)
le-not-symmetric sym | ()


antisymmetric : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
antisymmetric R = ∀ a b → R a b → R b a → a ≡ b

{-
練習問題:★★, optional
-}
le-antisymmetric : antisymmetric _≤_
le-antisymmetric .b b le-n R₂ = refl
le-antisymmetric .(S m) .(S m) (le-S {m} R₁) le-n = refl
le-antisymmetric .(S m₁) .(S m) (le-S {m} R₁) (le-S {m₁} R₂) = cong S (le-antisymmetric m₁ m (le-Sn-le m₁ m R₁) (le-Sn-le m m₁ R₂))

{-
練習問題:★★, optional
-}
le-step : ∀ n m p → n < m → m ≤ S p → n ≤ p
le-step n m p n<m m≤Sp = le-S-n n p (le-trans (S n) m (S p) n<m m≤Sp)

equivalence : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
equivalence R = reflexive R × symmetric R × transitive R

order : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
order R = reflexive R × antisymmetric R × transitive R

preorder : ∀ {a b} {X : Set a} (R : relation {b = b} X) → Set (a ⊔ b)
preorder R = reflexive R × transitive R

le-order : order _≤_
le-order = le-reflexive , le-antisymmetric , le-trans

-- 反射推移閉包 ---------------------------------------------------------------

data clos-refl-trans {a b} {X : Set a} (R : relation {b = b} X) : relation {b = a ⊔ b} X where
  rt-step : ∀ x y → R x y → clos-refl-trans R x y
  rt-refl : ∀ x → clos-refl-trans R x x
  rt-trans : ∀ x y z → clos-refl-trans R x y → clos-refl-trans R y z → clos-refl-trans R x z

next-nat-closure-is-le : ∀ n m → n ≤ m ↔ (clos-refl-trans next-nat) n m
next-nat-closure-is-le n m = left n m , right n m
  where
    left : ∀ n m → n ≤ m → clos-refl-trans next-nat n m
    left .m₁ m₁ le-n = rt-refl m₁
    left n₁ .(S m₁) (le-S {m₁} n≤m) = rt-trans n₁ m₁ (S m₁) (left n₁ m₁ n≤m) (rt-step m₁ (S m₁) nn)
    right : ∀ n m → clos-refl-trans next-nat n m → n ≤ m
    right n₁ .(S n₁) (rt-step .n₁ .(S n₁) nn) = le-S le-n
    right .m₁ m₁ (rt-refl .m₁) = le-n
    right n₁ m₁ (rt-trans .n₁ y .m₁ clos clos₁) = le-trans n₁ y m₁ (right n₁ y clos) (right y m₁ clos₁)


data refl-step-closure {a b} {X : Set a} (R : relation {b = b} X) : X → X → Set (a ⊔ b) where
  rsc-refl : ∀ x → refl-step-closure R x x
  rsc-step : ∀ x y z → R x y → refl-step-closure R y z → refl-step-closure R x z

rsc-R : ∀ {a b} {X : Set a} (R : relation {b = b} X) (x y : X) →
        R x y → refl-step-closure R x y
rsc-R = λ R x y z → rsc-step x y y z (rsc-refl y)

{-
練習問題:★★, optional(rsc_trans)
-}
rsc-trans : ∀ {a b} {X : Set a} (R : relation {b = b} X) (x y z : X) →
            refl-step-closure R x y → refl-step-closure R y z → refl-step-closure R x z
rsc-trans R .y y z (rsc-refl .y) rsc₂ = rsc₂
rsc-trans R x y z (rsc-step .x y₁ .y x₁ rsc₁) rsc₂ = rsc-step x y₁ z x₁ (rsc-trans R y₁ y z rsc₁ rsc₂)

{-
練習問題:★★★, optional (rtc_rsc_coincide)
-}
rtc-rsc-coincide : ∀ {a b} {X : Set a} (R : relation {b = b} X) (x y : X) →
                   clos-refl-trans R x y ↔ refl-step-closure R x y
rtc-rsc-coincide R x y = left x y , right x y
  where
    left : ∀ x y → clos-refl-trans R x y → refl-step-closure R x y
    left x₁ y₁ (rt-step .x₁ .y₁ x₂) = rsc-step x₁ y₁ y₁ x₂ (rsc-refl y₁)
    left .y₁ y₁ (rt-refl .y₁) = rsc-refl y₁
    left x₁ y₁ (rt-trans .x₁ y₂ .y₁ clos clos₁) = rsc-trans R x₁ y₂ y₁ (left x₁ y₂ clos) (left y₂ y₁ clos₁)
    right : ∀ x y → refl-step-closure R x y → clos-refl-trans R x y
    right .y₁ y₁ (rsc-refl .y₁) = rt-refl y₁
    right x₁ y₁ (rsc-step .x₁ y₂ .y₁ x₂ rsc) = rt-trans x₁ y₂ y₁ (rt-step x₁ y₂ x₂) (right y₂ y₁ rsc)
