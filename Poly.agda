module Poly where

import Level
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

data Bool-list : Set where
  Bool-nil : Bool-list
  Bool-cons : Bool → Bool-list → Bool-list

infixr 5 _∷_

data list {x} (X : Set x) : Set x where
  []  : list X
  _∷_ : X → list X → list X

{-# BUILTIN LIST list #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

[_] : ∀{x} {X : Set x} → X → list X
[ x ] = x ∷ []

{-
$ agda -I -i/usr/share/agda-stdlib -i. Poly.agda
Main> :typeOf []
list _A_24
Main> :typeOf _∷_
_A_32 → list _A_32 → list _A_32
Main> :typeOf 1 ∷ 2 ∷ []
list ℕ
-}

length' : ∀{x} (X : Set x) → list X → ℕ
length' X [] = 0
length' X (_ ∷ xs) = 1 + length' X xs

test-length'1 : length' ℕ (1 ∷ 2 ∷ []) ≡ 2
test-length'1 = refl

app' : ∀{x} (X : Set x) → list X → list X → list X
app' X [] ys = ys
app' X (x ∷ xs) ys = x ∷ app' X xs ys

snoc' : ∀{x} (X : Set x) → list X → X → list X
snoc' X [] n = [ n ]
snoc' X (x ∷ xs) n = x ∷ snoc' X xs n

rev' : ∀{x} (X : Set x) → list X → list X
rev' X [] = []
rev' X (x ∷ xs) = snoc' X (rev' X xs) x

test-rev'1 : rev' ℕ (1 ∷ 2 ∷ []) ≡ 2 ∷ 1 ∷ []
test-rev'1 = refl
test-rev'2 : rev' Bool [] ≡ []
test-rev'2 = refl

-- 型推論の項
-- 略


-- 引数の同化(相当)
length'' : ∀{x} (X : Set x) → list X → ℕ
length'' _ [] = 0
length'' _ (_ ∷ xs) = 1 + length'' _ xs

-- 暗黙の引数(…ってこれまでも使いまくってるけど)
length : ∀{x} {X : Set x} → list X → ℕ
length [] = 0
length (_ ∷ xs) = 1 + length xs

infixr 5 _++_

_++_ : ∀{x} {X : Set x} → list X → list X → list X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

snoc : ∀{x} {X : Set x} → list X → X → list X
snoc [] n = [ n ]
snoc (x ∷ xs) n = x ∷ snoc xs n

rev : ∀{x} {X : Set x} → list X → list X
rev [] = []
rev (x ∷ xs) = snoc (rev xs) x

{-
練習問題: ★★, optional (poly_exercises)

ここにあるいくつかの練習問題は、List_J.vにあったものと同じですが、多相性の練習になります。以下の定義を行い、証明を完成させなさい。
-}
repeat : ∀{x} {X : Set x} → X → ℕ → list X
repeat x 0 = []
repeat x (suc n) = x ∷ repeat x n

test-repeat1 : repeat true 2 ≡ true ∷ true ∷ []
test-repeat1 = refl

[]-++ : ∀{x} {X : Set x} →
        (l : list X) → [] ++ l ≡ l
[]-++ [] = refl
[]-++ (x ∷ xs) = cong (λ as → x ∷ as) ([]-++ xs)

rev-snoc : ∀{x} {X : Set x} →
           (v : X) → (s : list X) →
           rev (snoc s v) ≡ v ∷ rev s
rev-snoc v [] = refl
rev-snoc v (x ∷ xs) = cong (λ as → snoc as x) (rev-snoc v xs)

snoc-with-append : ∀{x} {X : Set x} →
                   (v : X) → (l1 : list X) → (l2 : list X) →
                   snoc (l1 ++ l2) v ≡ l1 ++ snoc l2 v
snoc-with-append v [] ys = refl
snoc-with-append v (x ∷ xs) ys = cong (λ as → x ∷ as) (snoc-with-append v xs ys)


infixr 2 _×_
infixr 4 _,_

data _×_ {x y} (X : Set x) (Y : Set y) : Set (Level._⊔_ x y) where
  _,_ : X → Y → X × Y

fst : ∀{x y} {X : Set x} {Y : Set y} → X × Y → X
fst (x , y) = x

snd : ∀{x y} {X : Set x} {Y : Set y} → X × Y → Y
snd (x , y) = y

combine : ∀{x y} {X : Set x} {Y : Set y} → list X → list Y → list (X × Y)
combine [] _ = []
combine _ [] = []
combine (x ∷ xs) (y ∷ ys) = (x , y) ∷ combine xs ys

{-
練習問題: ★ (combine_checks)

次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。

  関数combineの型は何でしょう (Check @combineの出力結果は？
-}
-- といってもシグネチャ通りですよね
{-
Main> :typeOf combine
{x y : Level.Level} {X : Set x} {Y : Set y} →
list X → list Y → list (X × Y)
-}
{-
  それでは
        Eval simpl in (combine [1,2] [false,false,true,true]).

  は何を出力する？
-}
-- [(1,false),(2,false)]
{-
Main> combine (1 ∷ 2 ∷ []) (false ∷ false ∷ true ∷ true ∷ [])
(1 , false) ∷ (2 , false) ∷ []
-}

{-
練習問題: ★★, recommended (split)

split関数はcombineと全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。多くの関数型言語とでunzipと呼ばれているものです。次の段落のコメントをはずし、split関数の定義を完成させなさい。続くテストを通過することも確認しなさい。
-}
-- 次の段落のコメント？
-- 続くテスト？
split : ∀{x y} {X : Set x} {Y : Set y} → list (X × Y) → list X × list Y
split [] = ([] , [])
split ((x , y) ∷ xys) with split xys
... | (xs , ys) = (x ∷ xs , y ∷ ys)


data option {x} (X : Set x) : Set x where
  Some : X → option X
  None : option X

ℕ-eq : ℕ → ℕ → Bool
ℕ-eq zero zero = true
ℕ-eq zero (suc m) = false
ℕ-eq (suc n) zero = false
ℕ-eq (suc n) (suc m) = ℕ-eq n m

index : ∀{x} {X : Set x} → ℕ → list X → option X
index n [] = None
index n (x ∷ xs) = if ℕ-eq 0 n then Some x else index (pred n) xs

test-index1 : index 0 (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) ≡ Some 4
test-index1 = refl
test-index2 : index 1 ([ 1 ] ∷ [ 2 ] ∷ []) ≡ Some [ 2 ]
test-index2 = refl
test-index3 : index 3 [ true ] ≡ None
test-index3 = refl

{-
練習問題: ★, optional (hd_opt_poly)

前の章に出てきたhd_opt関数の多相版を定義しなさい。。次の単体テストでの確認も忘れずに。
-}

hd-opt : ∀{x} {X : Set x} → list X → option X
hd-opt [] = None
hd-opt (x ∷ _) = Some x

test-hd-opt1 : hd-opt (1 ∷ 2 ∷ []) ≡ Some 1
test-hd-opt1 = refl
test-hd-opt2 : hd-opt ([ 1 ] ∷ [ 2 ] ∷ []) ≡ Some [ 1 ]
test-hd-opt2 = refl


doit3times : ∀{x} {X : Set x} → (X → X) → X → X
doit3times f n = f (f (f n))

test-doit3times : doit3times (λ a → a ∸ 2) 9 ≡ 3
test-doit3times = refl
test-doit3times' : doit3times not true ≡ false
test-doit3times' = refl

{-
Main> :typeOf _+_
ℕ → ℕ → ℕ
-}

plus3 = _+_ 3

{-
Main> :typeOf _+_ 3
ℕ → ℕ
-}

test-plus3 : plus3 4 ≡ 7
test-plus3 = refl
test-plus3' : doit3times plus3 0 ≡ 9
test-plus3' = refl
test-plus3'' : doit3times (_+_ 3) 0 ≡ 9
test-plus3'' = refl

{-
練習問題: ★★, optional (currying)

Coqでは、f : A → B → Cという型の関数はA → (B → C)型と同じです。このことは、もし上の関数fに値Aを与えると、f' : B → Cという型の関数が戻り値として返ってくるということです。これは部分適用のplus3でやりましたが、このように、複数の引数から戻り値の型のリストを、関数を返す関数として捉えなおすことを、論理学者ハスケル・カリーにちなんでカリー化、と呼んでいます。

逆に、A → B → C型の関数を(A * B) → C型の関数に変換することもできます。これをアンカリー化（非カリー化）といいます。アンカリー化された二項演算は、二つの引数を同時にペアの形で与える必要があり、部分適用はできません。

カリー化は以下のように定義できます。
-}
prod-curry : ∀{x y z} {X : Set x} {Y : Set y} {Z : Set z} →
             (X × Y → Z) → X → Y → Z
prod-curry f x y = f (x , y)
{-
練習問題として、その逆のprod_uncurryを定義し、二つの関数が互いに逆関数であることを証明しなさい。
-}
prod-uncurry : ∀{x y z} {X : Set x} {Y : Set y} {Z : Set z} → (X → Y → Z) → (X × Y) → Z
prod-uncurry f (x , y) = f x y

uncurry-curry : ∀{x y z} {X : Set x} {Y : Set y} {Z : Set z} →
                (f : X → Y → Z) → (x : X) → (y : Y) →
                prod-curry (prod-uncurry f) x y ≡ f x y
uncurry-curry f x y = refl

curry-uncurry : ∀{x y z} {X : Set x} {Y : Set y} {Z : Set z} →
                (f : X × Y → Z) → (p : X × Y) →
                prod-uncurry (prod-curry f) p ≡ f p
curry-uncurry f (x , y) = refl


filter : ∀{x} {X : Set x} → (X → Bool) → list X → list X
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

-- 再定義
even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)
odd : ℕ → Bool
odd n = not (even n)

test-filter1 : filter even (1 ∷ 2 ∷ 3 ∷ [ 4 ]) ≡ 2 ∷ [ 4 ]
test-filter1 = refl

length-is-1 : ∀{x} {X : Set x} → list X → Bool
length-is-1 ls = ℕ-eq (length ls) 1

test-filter2 : filter length-is-1 ((1 ∷ 2 ∷ []) ∷ [ 3 ] ∷ [ 4 ] ∷ (5 ∷ 6 ∷ []) ∷ [] ∷ [ 8 ] ∷ []) ≡ [ 3 ] ∷ [ 4 ] ∷ [ 8 ] ∷ []
test-filter2 = refl

countoddmembers' : list ℕ → ℕ
countoddmembers' ls = length (filter odd ls)

test-countoddmembers'1 : countoddmembers' (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
test-countoddmembers'1 = refl
test-countoddmembers'2 : countoddmembers' (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
test-countoddmembers'2 = refl
test-countoddmembers'3 : countoddmembers' [] ≡ 0
test-countoddmembers'3 = refl


test-anon-fun' : doit3times (λ n → n * n) 2 ≡ 256
test-anon-fun' = refl

test-filter2' : filter (λ ls → ℕ-eq (length ls) 1) ((1 ∷ 2 ∷ []) ∷ [ 3 ] ∷ [ 4 ] ∷ (5 ∷ 6 ∷ []) ∷ [] ∷ [ 8 ] ∷ []) ≡ [ 3 ] ∷ [ 4 ] ∷ [ 8 ] ∷ []
test-filter2' = refl

{-
練習問題: ★★, optional (filter_even_gt7)

filter関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出すfilter_even_gt7関数を書きなさい。
-}
filter-even-gt7 : list ℕ → list ℕ
filter-even-gt7 = filter (λ n → even n ∧ ℕ-< 7 n)
  where
    ℕ-< : ℕ → ℕ → Bool
    ℕ-< _ 0 = false
    ℕ-< 0 (suc _) = true
    ℕ-< (suc n) (suc m) = ℕ-< n m

test-filter-even-gt7-1 : filter-even-gt7 (1 ∷ 2 ∷ 6 ∷ 9 ∷ 10 ∷ 3 ∷ 12 ∷ 8 ∷ []) ≡ 10 ∷ 12 ∷ 8 ∷ []
test-filter-even-gt7-1 = refl
test-filter-even-gt7-2 : filter-even-gt7 (5 ∷ 2 ∷ 6 ∷ 19 ∷ 129 ∷ []) ≡ []
test-filter-even-gt7-2 = refl

{-
練習問題: ★★★, optional (partition)

filter関数を使って、partition関数を書きなさい。:
  partition : ∀ X : Type,
                (X → bool) → list X → list X * list X

型Xについて、X型の値がある条件を満たすかを調べる述語X → boolとXのリストlist Xを引数に与えると、partition関数はリストのペアを返します。ペアの最初の要素は、与えられたリストのうち、条件を満たす要素だけのリストで、二番目の要素は、条件を満たさないもののリストです。二つのリストの要素の順番は、元のリストの順と同じでなければなりません。
-}
partition : ∀{x} {X : Set x} → (X → Bool) → list X → list X × list X
partition p [] = ([] , [])
partition p (x ∷ xs) with p x | partition p xs
... | true  | (as , bs) = (x ∷ as , bs)
... | false | (as , bs) = (as , x ∷ bs)

test-partition1 : partition odd (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 3 ∷ 5 ∷ [] , 2 ∷ 4 ∷ [])
test-partition1 = refl
test-partition2 : partition (λ _ → false) (5 ∷ 9 ∷ 0 ∷ []) ≡ ([] , 5 ∷ 9 ∷ 0 ∷ [])
test-partition2 = refl

map : ∀{x y} {X : Set x} {Y : Set y} → (X → Y) → list X → list Y
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

test-map1 : map (_+_ 3) (2 ∷ 0 ∷ 2 ∷ []) ≡ 5 ∷ 3 ∷ 5 ∷ []
test-map1 = refl
test-map2 : map odd (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ false ∷ true ∷ false ∷ true ∷ []
test-map2 = refl
test-map3 : map (λ n → even n ∷ odd n ∷ []) (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ []
test-map3 = refl

{-
練習問題: ★★★, optional (map_rev)

mapとrevが可換であることを示しなさい。証明には補題をたてて証明する必要があるでしょう。
-}
++-map : ∀{x y} {X : Set x} {Y : Set y} →
         (f : X → Y) → (l1 : list X) → (l2 : list X) →
         map f (l1 ++ l2) ≡ map f l1 ++ map f l2
++-map f [] ys = refl
++-map f (x ∷ xs) ys = cong (_∷_ (f x)) (++-map f xs ys)

map-rev : ∀{x y} {X : Set x} {Y : Set y} →
          (f : X → Y) → (l : list X) →
          map f (rev l) ≡ rev (map f l)
map-rev f [] = refl
map-rev f (x ∷ xs) =
  begin
     map f (rev (x ∷ xs))
  ≡⟨ refl ⟩
     map f (snoc (rev xs) x)
  ≡⟨ cong (map f) (snoc-append (rev xs) x) ⟩
     map f (rev xs ++ [ x ])
  ≡⟨ ++-map f (rev xs) ([ x ]) ⟩
     map f (rev xs) ++ f x ∷ []
  ≡⟨ sym (snoc-append (map f (rev xs)) (f x)) ⟩
     snoc (map f (rev xs)) (f x)
  ≡⟨ cong (λ z → snoc z (f x)) (map-rev f xs) ⟩
     rev (map f (x ∷ xs))
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    snoc-append : ∀{x} {X : Set x} →
                  (l : list X) → (n : X) →
                  snoc l n ≡ l ++ [ n ]
    snoc-append [] n = refl
    snoc-append (x ∷ xs) n = cong (λ as → x ∷ as) (snoc-append xs n)

{-
練習問題: ★★, recommended (flat_map)

map関数は、list Xからlist Yへのマップを、型X → Yの関数を使って実現しています。同じような関数flat_mapを定義しましょう。これはlist Xからlist Yへのマップですが、X → list Yとなる関数fを使用できます。このため、次のように要素ごとの関数fの結果を平坦化してやる必要があります。
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12].
-}
flat-map : ∀{x y} {X : Set x} {Y : Set y} →
           (X → list Y) → list X → list Y
flat-map f [] = []
flat-map f (x ∷ xs) = f x ++ flat-map f xs

test-flat-map1 : flat-map (λ n → n ∷ n ∷ n ∷ []) (1 ∷ 5 ∷ 4 ∷ []) ≡ 1 ∷ 1 ∷ 1 ∷ 5 ∷ 5 ∷ 5 ∷ 4 ∷ 4 ∷ 4 ∷ []
test-flat-map1 = refl

option-map : ∀{x y} {X : Set x} {Y : Set y} →
             (X → Y) → option X → option Y
option-map f None = None
option-map f (Some x) = Some (f x)

{-
練習問題: ★★, optional (implicit_args)

filterやmap関数を定義したり使ったりするケースでは、多くの場合暗黙的な型引数が使われます。暗黙の型引数定義に使われている中括弧を普通の括弧に置き換え、必要なところに型引数を明示的に書くようにして、それが正しいかどうかをCoqでチェックしなさい。
-}
-- 略
