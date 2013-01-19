module Lists where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

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
nonzeros (suc x ∷ xs) = suc x ∷ nonzeros xs

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

ℕ-bag : Set
ℕ-bag = ℕ-list

{-
練習問題: ★★★ (ℕ-bag_functions)

バッグに対する count、 sum、 add、 member 関数の定義を完成させなさい。
-}
ℕ-eq : ℕ → ℕ → Bool
ℕ-eq zero zero = true
ℕ-eq zero (suc m) = false
ℕ-eq (suc n) zero = false
ℕ-eq (suc n) (suc m) = ℕ-eq n m

count : ℕ → ℕ-bag → ℕ
count n [] = 0
count n (x ∷ xs) = (if ℕ-eq n x then 1 else 0) + count n xs

test-count1 : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ 3
test-count1 = refl
test-count2 : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ 0
test-count2 = refl

sum : ℕ-bag → ℕ-bag → ℕ-bag
sum = app

test-sum1 : count 1 (sum (1 ∷ 2 ∷  [ 3 ]) (1 ∷ 4 ∷ [ 1 ])) ≡ 3
test-sum1 = refl

add : ℕ → ℕ-bag → ℕ-bag
add = _∷_

test-add1 : count 1 (add 1 (1 ∷ 4 ∷ [ 1 ])) ≡ 3
test-add1 = refl
test-add2 : count 5 (add 1 (1 ∷ 4 ∷ [ 1 ])) ≡ 0
test-add2 = refl

member : ℕ → ℕ-bag → Bool
member n [] = false
member n (x ∷ xs) = if ℕ-eq n x then true else member n xs

test-member1 : member 1 (1 ∷ 4 ∷ [ 1 ]) ≡ true
test-member1 = refl
test-member2 : member 2 (1 ∷ 4 ∷ [ 1 ]) ≡ false
test-member2 = refl

{-
練習問題: ★★★, optional (bag_more_functions)

練習として、さらにいくつかの関数を作成してください。
-}
remove-one : ℕ → ℕ-bag → ℕ-bag
remove-one n [] = []
remove-one n (x ∷ xs) = if ℕ-eq n x then xs else x ∷ remove-one n xs

test-remove-one1 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ [ 1 ])) ≡ 0
test-remove-one1 = refl
test-remove-one2 : count 5 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ [ 1 ])) ≡ 0
test-remove-one2 = refl
test-remove-one3 : count 4 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 2
test-remove-one3 = refl
test-remove-one4 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 1
test-remove-one4 = refl

remove-all : ℕ → ℕ-bag → ℕ-bag
remove-all n [] = []
remove-all n (x ∷ xs) = if ℕ-eq n x then remove-all n xs else x ∷ remove-all n xs

test-remove-all1 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷  [ 1 ])) ≡ 0
test-remove-all1 = refl
test-remove-all2 : count 5 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ [ 1 ])) ≡ 0
test-remove-all2 = refl
test-remove-all3 : count 4 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 2
test-remove-all3 = refl
test-remove-all4 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 0
test-remove-all4 = refl

subset : ℕ-bag → ℕ-bag → Bool
subset [] ys = true
subset (x ∷ xs) ys with count x ys
... | 0 = false
... | suc _ = subset xs (remove-one x ys)

test-subset1 : subset (1 ∷ [ 2 ]) (2 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ true
test-subset1 = refl
test-subset2 : subset (1 ∷ 2 ∷ [ 2 ]) (2 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ false
test-subset2 = refl

{-
練習問題: ★★★, recommended (bag_theorem)

count や add を使ったバッグに関する面白い定理書き、それを証明しなさい。この問題はいわゆる自由課題で、真になることがわかっていても、証明にはまだ習っていない技を使わなければならない定理を思いついてしまうこともあります。証明に行き詰まってしまったら気軽に質問してください。
-}
add-count-commute-count-inc : {n : ℕ} {xs : ℕ-bag} → count n (add n xs) ≡ 1 + count n xs
add-count-commute-count-inc {n} {xs} = cong (\eq → (if eq then 1 else 0) + count n xs) (ℕ-eq-refl {n})
  where
    ℕ-eq-refl : {n : ℕ} → ℕ-eq n n ≡ true
    ℕ-eq-refl {0} = refl
    ℕ-eq-refl {suc n} = ℕ-eq-refl {n}

[]-app : {l : ℕ-list} → [] ++ l ≡ l
[]-app = refl

tl-length-pred : {l : ℕ-list} → pred (length l) ≡ length (tail l)
tl-length-pred {[]} = refl
tl-length-pred {x ∷ xs} = refl

++-assoc : {l1 l2 l3 : ℕ-list} → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc {[]} {ys} {zs} = refl
++-assoc {x ∷ xs} {ys} {zs} = cong (\as → x ∷ as) (++-assoc {xs} {ys} {zs})

++-length : {l1 l2 : ℕ-list} → length (l1 ++ l2) ≡ (length l1) + (length l2)
++-length {[]} {ys} = refl
++-length {x ∷ xs} {ys} = cong (\a → 1 + a) (++-length {xs} {ys})

snoc : ℕ-list → ℕ → ℕ-list
snoc [] n = [ n ]
snoc (x ∷ xs) n = x ∷ snoc xs n

rev : ℕ-list → ℕ-list
rev [] = []
rev (x ∷ xs) = snoc (rev xs) x

test-rev1 : rev (1 ∷ 2 ∷ [ 3 ]) ≡ (3 ∷ 2 ∷ [ 1 ])
test-rev1 = refl
test-rev2 : rev [] ≡ []
test-rev2 = refl

{-
rev-length-firsttry : {l : ℕ-list} → length (rev l) ≡ length l
rev-length-firsttry {[]} = refl
rev-length-firsttry {x ∷ xs} = ?
-}

length-snoc : {n : ℕ} {l : ℕ-list} → length (snoc l n) ≡ 1 + length l
length-snoc {n} {[]} = refl
length-snoc {n} {x ∷ xs} = cong (\a → 1 + a) (length-snoc {n} {xs})

rev-length : {l : ℕ-list} → length (rev l) ≡ length l
rev-length {[]} = refl
rev-length {x ∷ xs} rewrite length-snoc {x} {rev xs} = cong (\a → 1 + a) (rev-length {xs})

{-
練習問題: ★★★, recommended (list_exercises)

リストについてさらに練習しましょう。
-}
app-[]-end : {l : ℕ-list} → l ++ [] ≡ l
app-[]-end {[]} = refl
app-[]-end {x ∷ xs} = cong (\as → x ∷ as) (app-[]-end {xs})

rev-snoc-commute-rev-cons : {n : ℕ} {ls : ℕ-list} → rev (snoc ls n) ≡ n ∷ rev ls
rev-snoc-commute-rev-cons {n} {[]} = refl
rev-snoc-commute-rev-cons {n} {x ∷ xs} = cong (\as → snoc as x) (rev-snoc-commute-rev-cons {n} {xs})

rev-involutive : {l : ℕ-list} → rev (rev l) ≡ l
rev-involutive {[]} = refl
rev-involutive {x ∷ xs} rewrite rev-snoc-commute-rev-cons {x} {rev xs} = cong (\as → x ∷ as) (rev-involutive {xs})

++-rev : {l1 l2 : ℕ-list} → rev (l1 ++ l2) ≡ rev l2 ++ rev l1
++-rev {[]} {ys} = sym (app-[]-end {rev ys})
++-rev {x ∷ xs} {ys} =
  begin
     rev (x ∷ xs ++ ys)
  ≡⟨ refl ⟩
     snoc (rev (xs ++ ys)) x
  ≡⟨ cong (\z → snoc z x) (++-rev {xs})⟩
     snoc (rev ys ++ rev xs) x
  ≡⟨ ++-snoc {x} {rev ys} {rev xs} ⟩
     rev ys ++ snoc (rev xs) x
  ≡⟨ refl ⟩
     rev ys ++ rev (x ∷ xs)
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    ++-snoc : {n : ℕ} {l1 l2 : ℕ-list} → snoc (l1 ++ l2) n ≡ l1 ++ snoc l2 n
    ++-snoc {n} {[]} {ys} = refl
    ++-snoc {n} {x ∷ xs} {ys} = cong (\as → x ∷ as) (++-snoc {n} {xs} {ys})

{-
次の問題には簡単な解法があります。こんがらがってしまったようであれば、少し戻って単純な方法を探してみましょう。
-}
app-ass4 : {l1 l2 l3 l4 : ℕ-list} → l1 ++ (l2 ++ (l3 ++ l4)) ≡ ((l1 ++ l2) ++ l3) ++ l4
app-ass4 {l1} {l2} {l3} {l4} = sym (trans (++-assoc {l1 ++ l2} {l3} {l4}) (++-assoc {l1} {l2} {l3 ++ l4}))

snoc-append : {l : ℕ-list} {n : ℕ} → snoc l n ≡ l ++ [ n ]
snoc-append {[]} = refl
snoc-append {x ∷ xs} = cong (\as → x ∷ as) (snoc-append {xs})

{-
前に書いた nonzeros 関数に関する練習問題です。
-}
nonzeros-length : {l1 l2 : ℕ-list} → nonzeros (l1 ++ l2) ≡ (nonzeros l1) ++ (nonzeros l2)
nonzeros-length {[]} {ys} = cong nonzeros ([]-app {ys})
nonzeros-length {0 ∷ xs} {ys} = nonzeros-length {xs} {ys}
nonzeros-length {suc x ∷ xs} {ys} = cong (\as → suc x ∷ as) (nonzeros-length {xs} {ys})

{-
練習問題: ★★, recommended (list_design)

自分で問題を考えましょう。
cons （::）、 snoc、 append （++） に関する、自明でない定理を考えて書きなさい。
それを証明しなさい。
-}
-- 略


{-
練習問題: ★★, optional (bag_proofs)

前のバッグについての optional な練習問題に挑戦したのであれば、その定義について、以下の定理を証明しなさい。
-}
count-member-nonzero : {s : ℕ-bag} → 1 ≤ count 1 (1 ∷ s)
count-member-nonzero {[]} = s≤s z≤n
count-member-nonzero {x ∷ xs} = s≤s z≤n

n≤Sn : {n : ℕ} → n ≤ suc n
n≤Sn {0} = z≤n
n≤Sn {suc n} = s≤s n≤Sn

remove-decreases-count : {s : ℕ-bag} → count 0 (remove-one 0 s) ≤ count 0 s
remove-decreases-count {[]} = z≤n
remove-decreases-count {0 ∷ xs} = n≤Sn {count 0 xs}
remove-decreases-count {suc n ∷ xs} = remove-decreases-count {xs}

{-
練習問題: ★★★★, optional (rev_injective)

rev 関数が単射である、すなわち

    ∀ X (l1 l2 : list X), rev l1 = rev l2 → l1 = l2

であることを証明しなさい。

この練習問題には簡単な解法と難しい解法があります。
-}
rev-injective : {l1 l2 : ℕ-list} → rev l1 ≡ rev l2 → l1 ≡ l2
rev-injective {xs} {ys} eq =
  begin
     xs
  ≡⟨ sym (rev-involutive {xs}) ⟩
     rev (rev xs)
  ≡⟨ cong rev eq ⟩
     rev (rev ys)
  ≡⟨ rev-involutive {ys} ⟩
     ys
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
-- 難しい解法ってなんだろう？
