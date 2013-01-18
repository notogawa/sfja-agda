module Lists where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 前章"Basics"の定義をimportしても良いが，
-- Bool/Natならagda標準ライブラリにあるので以後そっちを使う．
-- というかtactic無い上標準ライブラリ縛りはめんどいので

data ℕ-prod' : Set where
  pair : ℕ → ℕ → ℕ-prod'

fst' : ℕ-prod' → ℕ
fst' (pair a b) = a

snd' : ℕ-prod' → ℕ
snd' (pair a b) = b

--_,_ : ℕ → ℕ → ℕ-prod'
--_,_ = pair

{-
$ agda -I -i/usr/share/agda-stdlib -i. Lists.agda
Main> fst (3 , 4)
3
-}

-- Notationは無いのとこっちのがソレっぽいので
data ℕ-prod : Set where
  _,_ : ℕ → ℕ → ℕ-prod

fst : ℕ-prod → ℕ
fst (a , b) = a

snd : ℕ-prod → ℕ
snd (a , b) = b

swap-pair : ℕ-prod → ℕ-prod
swap-pair (a , b) = (b , a)

surjective-pairing' : {n m : ℕ} → (n , m) ≡ (fst (n , m) , snd (n , m))
surjective-pairing' = refl

surjective-pairing : {p : ℕ-prod} → p ≡ (fst p , snd p)
surjective-pairing {(n , m)} = refl
-- surjective-pairing {p} = refl -- こちらではダメ"p の構造を明らかにする必要があります"なので

{-
練習問題: ★ (snd_fst_is_swap)
-}
snd-fst-is-swap : {p : ℕ-prod} → (snd p , fst p) ≡ swap-pair p
snd-fst-is-swap {(n , m)}= refl

data ℕ-list : Set where
  [] : ℕ-list
  _∷_ : ℕ → ℕ-list → ℕ-list

infixr 5 _∷_

[_] : ℕ → ℕ-list
[ x ] = x ∷ []

l-123 : ℕ-list
l-123 = 1 ∷ 2 ∷ 3 ∷ []

l_123' = 1 ∷ (2 ∷ [ 3 ])
l_123'' = 1 ∷ 2 ∷ [ 3 ]
-- l_123''' = [ 1 , 2 , 3 ] -- これはできない

repeat : ℕ → ℕ → ℕ-list
repeat n 0 = []
repeat n (suc count) = n ∷ repeat n count

length : ℕ-list → ℕ
length [] = 0
length (_ ∷ ns) = 1 + length ns

app : ℕ-list → ℕ-list → ℕ-list
app [] ys = ys
app (x ∷ xs) ys = x ∷ app xs ys

_++_ : ℕ-list → ℕ-list → ℕ-list
_++_ = app

infixr 5 _++_

test-app1 : 1 ∷ 2 ∷ [ 3 ] ++ 4 ∷ [ 5 ] ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
test-app1 = refl
test-app2 : [] ++ 4 ∷ [ 5 ] ≡ 4 ∷ [ 5 ]
test-app2 = refl
test-app3 : 1 ∷ 2 ∷ [ 3 ] ++ [] ≡ 1 ∷ 2 ∷ [ 3 ]
test-app3 = refl

hd : ℕ → ℕ-list → ℕ
hd default [] = default
hd _ (x ∷ _) = x

tail : ℕ-list → ℕ-list
tail [] = []
tail (_ ∷ xs) = xs

test-hd1 : hd 0 (1 ∷ 2 ∷ [ 3 ]) ≡ 1
test-hd1 = refl
test-hd2 : hd 0 [] ≡ 0
test-hd2 = refl
test-tail : tail (1 ∷ 2 ∷ [ 3 ]) ≡ 2 ∷ [ 3 ]
test-tail = refl

{-
練習問題: ★★, recommended (list_funs)

以下の nonzeros、 oddmembers、 countoddmembers の定義を完成させなさい。
-}
nonzeros : ℕ-list → ℕ-list
nonzeros [] = []
nonzeros (0 ∷ xs) = nonzeros xs
nonzeros (x ∷ xs) = x ∷ nonzeros xs

test-nonzeros : nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ [ 0 ]) ≡ 1 ∷ 2 ∷ [ 3 ]
test-nonzeros = refl

even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)

odd : ℕ → Bool
odd n = not (even n)

oddmembers : ℕ-list → ℕ-list
oddmembers [] = []
oddmembers (x ∷ xs) = if odd x then x ∷ oddmembers xs else oddmembers xs

test-oddmembers : oddmembers (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ [ 0 ]) ≡ 1 ∷ [ 3 ]
test-oddmembers = refl

countoddmembers : ℕ-list → ℕ
countoddmembers xs = length (oddmembers xs)

test-countoddmembers1 : countoddmembers (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ [ 5 ]) ≡ 4
test-countoddmembers1 = refl
test-countoddmembers2 : countoddmembers (0 ∷ 2 ∷ [ 4 ]) ≡ 0
test-countoddmembers2 = refl
test-countoddmembers3 : countoddmembers [] ≡ 0
test-countoddmembers3 = refl

{-
練習問題: ★★ (alternate)

alternate の定義を完成させなさい。この関数は、ふたつのリストから交互に要素を取り出しひとつに「綴じ合わせる」関数です。具体的な例は下のテストを見てください。

注意: alternate の自然な定義のひとつは、 「Fixpoint による定義は『明らかに停止する』ものでなければならない」という Coq の要求を満たすことができません。このパターンにはまってしまったようであれば、両方のリストの要素を同時に見ていくような少し冗長な方法を探してみてください。
-}
alternate : ℕ-list → ℕ-list → ℕ-list
alternate [] ys = ys
alternate (x ∷ xs) ys = x ∷ alternate ys xs

test-alternate1 : alternate (1 ∷ 2 ∷ [ 3 ]) (4 ∷ 5 ∷ [ 6 ]) ≡ 1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ [ 6 ]
test-alternate1 = refl
test-alternate2 : alternate [ 1 ] (4 ∷ 5 ∷ [ 6 ]) ≡ 1 ∷ 4 ∷ 5 ∷ [ 6 ]
test-alternate2 = refl
test-alternate3 : alternate (1 ∷ 2 ∷ [ 3 ]) [ 4 ] ≡ 1 ∷ 4 ∷ 2 ∷ [ 3 ]
test-alternate3 = refl
test-alternate4 : alternate [] (20 ∷ [ 30 ]) ≡ 20 ∷ [ 30 ]
test-alternate4 = refl
