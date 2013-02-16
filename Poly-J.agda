module Poly-J where

import Level
open import Function -- 解禁
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong; sym; trans; subst₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Basics-J
open import Lists-J

-- ポリモルフィズム（多相性） -------------------------------------------------

---- 多相的なリスト -----------------------------------------------------------

data boollist : Set where
  bool-nil : boollist
  bool-cons : bool → boollist → boollist

infixr 5 _∷_

data list {x} (X : Set x) : Set x where
  []  : list X
  _∷_ : X → list X → list X

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
private
  length' : ∀{x} (X : Set x) → list X → nat
  length' X [] = 0
  length' X (_ ∷ xs) = 1 + length' X xs

  test-length'1 : length' nat (1 ∷ 2 ∷ []) ≡ 2
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

  test-rev'1 : rev' nat (1 ∷ 2 ∷ []) ≡ 2 ∷ 1 ∷ []
  test-rev'1 = refl
  test-rev'2 : rev' bool [] ≡ []
  test-rev'2 = refl

------ 型推論 -----------------------------------------------------------------
-- 略


------ 引数の同化（Synthesis） ------------------------------------------------
length'' : ∀{x} (X : Set x) → list X → nat
length'' _ [] = 0
length'' _ (_ ∷ xs) = 1 + length'' _ xs

------ 暗黙の引数 -------------------------------------------------------------
length : ∀{x} {X : Set x} → list X → nat
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

------ 練習問題:多相的なリスト ------------------------------------------------

{-
練習問題: ★★, optional (poly_exercises)

ここにあるいくつかの練習問題は、List_J.vにあったものと同じですが、多相性の練習になります。以下の定義を行い、証明を完成させなさい。
-}
repeat : ∀{x} {X : Set x} → X → nat → list X
repeat x 0 = []
repeat x (S n) = x ∷ repeat x n

test-repeat1 : repeat true 2 ≡ true ∷ true ∷ []
test-repeat1 = refl

nil-app : ∀{x} {X : Set x} →
        (l : list X) → [] ++ l ≡ l
nil-app xs = refl

rev-snoc : ∀{x} {X : Set x} →
           (v : X) → (s : list X) →
           rev (snoc s v) ≡ v ∷ rev s
rev-snoc v [] = refl
rev-snoc v (x ∷ xs)
  rewrite rev-snoc v xs
        = refl

snoc-with-append : ∀{x} {X : Set x} →
                   (v : X) → (l1 : list X) → (l2 : list X) →
                   snoc (l1 ++ l2) v ≡ l1 ++ snoc l2 v
snoc-with-append v [] ys = refl
snoc-with-append v (x ∷ xs) ys
  rewrite snoc-with-append v xs ys
        = refl

---- 多相的なペア -------------------------------------------------------------

infixr 2 _×_
infixr 4 _,_

data _×_ {x y} (X : Set x) (Y : Set y) : Set (Level._⊔_ x y) where
  _,_ : X → Y → X × Y

fst : ∀{x y} {X : Set x} {Y : Set y} → X × Y → X
fst (x , y) = x

snd : ∀{x y} {X : Set x} {Y : Set y} → X × Y → Y
snd (x , y) = y

combine : ∀{x y} {X : Set x} {Y : Set y} → list X × list Y → list (X × Y)
combine ([] , _) = []
combine (_ , []) = []
combine (x ∷ xs , y ∷ ys) = (x , y) ∷ combine (xs , ys)

{-
練習問題: ★ (combine_checks)

次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。

  関数combineの型は何でしょう (Check @combineの出力結果は？
-}
-- といってもシグネチャ通りですよね
{-
Main> :typeOf combine
{x y : Level.Level} {X : Set x} {Y : Set y} →
list X × list Y → list (X × Y)
-}
{-
  それでは
        Eval simpl in (combine [1,2] [false,false,true,true]).

  は何を出力する？
-}
-- [(1,false),(2,false)]
{-
Main> combine (1 ∷ 2 ∷ [] , false ∷ false ∷ true ∷ true ∷ [])
(1 , false) ∷ (2 , false) ∷ []
-}

{-
練習問題: ★★, recommended (split)

split関数はcombineと全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。多くの関数型言語とでunzipと呼ばれているものです。次の段落のコメントをはずし、split関数の定義を完成させなさい。続くテストを通過することも確認しなさい。
-}
-- 次の段落のコメント？
-- 続くテスト？
prod-map : ∀{x y} {X : Set x} {Y : Set y} →
           (list X → list X) → (list Y → list Y) → list X × list Y → list X × list Y
prod-map f g (xs , ys) = (f xs , g ys)

split : ∀{x y} {X : Set x} {Y : Set y} → list (X × Y) → list X × list Y
split [] = ([] , [])
split ((x , y) ∷ xys) = prod-map (_∷_ x) (_∷_ y) (split xys)

---- 多相的なオプション -------------------------------------------------------

data option {x} (X : Set x) : Set x where
  Some : X → option X
  None : option X

if_then_else_ : ∀ {x} {X : Set x} → bool → X → X → X
if true  then t else f = t
if false then t else f = f

index : ∀{x} {X : Set x} → nat → list X → option X
index n [] = None
index n (x ∷ xs) = if beq-nat 0 n then Some x else index (pred n) xs

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

-- データとしての関数 ---------------------------------------------------------

---- 高階関数 -----------------------------------------------------------------

doit3times : ∀{x} {X : Set x} → (X → X) → X → X
doit3times f = f ∘ f ∘ f

test-doit3times : doit3times (λ a → a - 2) 9 ≡ 3
test-doit3times = refl
test-doit3times' : doit3times negb true ≡ false
test-doit3times' = refl

---- 部分適用 ------------------------------------------------------------------

{-
Main> :typeOf _+_
nat → nat → nat
-}

plus3 = _+_ 3

{-
Main> :typeOf _+_ 3
nat → nat
-}

test-plus3 : plus3 4 ≡ 7
test-plus3 = refl
test-plus3' : doit3times plus3 0 ≡ 9
test-plus3' = refl
test-plus3'' : doit3times (_+_ 3) 0 ≡ 9
test-plus3'' = refl

---- 余談： カリー化 ----------------------------------------------------------

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

---- フィルター (Filter)関数 --------------------------------------------------

filter : ∀{x} {X : Set x} → (X → bool) → list X → list X
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

test-filter1 : filter evenb (1 ∷ 2 ∷ 3 ∷ [ 4 ]) ≡ 2 ∷ [ 4 ]
test-filter1 = refl

length-is-1 : ∀{x} {X : Set x} → list X → bool
length-is-1 ls = beq-nat (length ls) 1

test-filter2 : filter length-is-1 ((1 ∷ 2 ∷ []) ∷ [ 3 ] ∷ [ 4 ] ∷ (5 ∷ 6 ∷ []) ∷ [] ∷ [ 8 ] ∷ []) ≡ [ 3 ] ∷ [ 4 ] ∷ [ 8 ] ∷ []
test-filter2 = refl

countoddmembers' : list nat → nat
countoddmembers' = length ∘ filter oddb

test-countoddmembers'1 : countoddmembers' (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
test-countoddmembers'1 = refl
test-countoddmembers'2 : countoddmembers' (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
test-countoddmembers'2 = refl
test-countoddmembers'3 : countoddmembers' [] ≡ 0
test-countoddmembers'3 = refl

---- 無名（匿名）関数 ---------------------------------------------------------

test-anon-fun' : doit3times (λ n → n * n) 2 ≡ 256
test-anon-fun' = refl

test-filter2' : filter (λ ls → beq-nat (length ls) 1) ((1 ∷ 2 ∷ []) ∷ [ 3 ] ∷ [ 4 ] ∷ (5 ∷ 6 ∷ []) ∷ [] ∷ [ 8 ] ∷ []) ≡ [ 3 ] ∷ [ 4 ] ∷ [ 8 ] ∷ []
test-filter2' = refl

{-
練習問題: ★★, optional (filter_even_gt7)

filter関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出すfilter_even_gt7関数を書きなさい。
-}
filter-even-gt7 : list nat → list nat
filter-even-gt7 = filter (λ n → andb (evenb n) (andb (ble-nat 7 n) (negb (beq-nat 7 n))))

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
partition : ∀{x} {X : Set x} → (X → bool) → list X → list X × list X
partition p [] = ([] , [])
partition p (x ∷ xs) with partition p xs
... | (as , bs) = if p x then (x ∷ as , bs) else (as , x ∷ bs)

test-partition1 : partition oddb (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 3 ∷ 5 ∷ [] , 2 ∷ 4 ∷ [])
test-partition1 = refl
test-partition2 : partition (λ _ → false) (5 ∷ 9 ∷ 0 ∷ []) ≡ ([] , 5 ∷ 9 ∷ 0 ∷ [])
test-partition2 = refl

---- マップ（Map）関数 --------------------------------------------------------

map : ∀{x y} {X : Set x} {Y : Set y} → (X → Y) → list X → list Y
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

test-map1 : map (_+_ 3) (2 ∷ 0 ∷ 2 ∷ []) ≡ 5 ∷ 3 ∷ 5 ∷ []
test-map1 = refl
test-map2 : map oddb (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ false ∷ true ∷ false ∷ true ∷ []
test-map2 = refl
test-map3 : map (λ n → evenb n ∷ oddb n ∷ []) (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ []
test-map3 = refl

{-
練習問題: ★★★, optional (map_rev)

mapとrevが可換であることを示しなさい。証明には補題をたてて証明する必要があるでしょう。
-}
++-map : ∀{x y} {X : Set x} {Y : Set y} →
         (f : X → Y) → (l1 : list X) → (l2 : list X) →
         map f (l1 ++ l2) ≡ map f l1 ++ map f l2
++-map f [] ys = refl
++-map f (x ∷ xs) ys
  rewrite ++-map f xs ys
        = refl

snoc-append : ∀{x} {X : Set x} →
              (l : list X) → (n : X) →
              snoc l n ≡ l ++ [ n ]
snoc-append [] n = refl
snoc-append (x ∷ xs) n
  rewrite snoc-append xs n
        = refl

map-rev : ∀{x y} {X : Set x} {Y : Set y} →
          (f : X → Y) → (l : list X) →
          map f (rev l) ≡ rev (map f l)
map-rev f [] = refl
map-rev f (x ∷ xs)
  rewrite snoc-append (rev xs) x
        | ++-map f (rev xs) ([ x ])
        | sym (snoc-append (map f (rev xs)) (f x))
        | map-rev f xs
        = refl

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

---- 畳み込み（Fold）関数 -----------------------------------------------------

fold : ∀{x y} → {X : Set x} {Y : Set y} →
       (X → Y → Y) → list X → Y → Y
fold f [] e = e
fold f (x ∷ xs) e = f x (fold f xs e)

{-
Main> :typeOf fold (_+_)
list nat → nat → nat
-}

fold-example1 : fold (_*_) (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 1 ≡ 24
fold-example1 = refl
fold-example2 : fold andb (true ∷ true ∷ false ∷ true ∷ []) true ≡ false
fold-example2 = refl
fold-example3 : fold (_++_) ([ 1 ] ∷ [] ∷ (2 ∷ [ 3 ]) ∷ [ 4 ] ∷ []) [] ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
fold-example3 = refl

{-
練習問題: ★, optional (fold_types_different)

fold関数がXとY二つの型引数をとっていて、関数fが型Xを引数にとり型Yを返すようになっていることに注目してください。XとYが別々の型となっていることで、どのような場合に便利であるかを考えてください。
-}
-- 略

---- 関数を作成する関数 -------------------------------------------------------

constfun : ∀{x} {X : Set x} → X → nat → X
constfun x = λ _ → x

ftrue = constfun true

constfun-example1 : ftrue 0 ≡ true
constfun-example1 = refl
constfun-example2 : constfun 5 99 ≡ 5
constfun-example2 = refl

override : ∀{x} {X : Set x} → (nat → X) → nat → X → nat → X
override f k x k' = if beq-nat k k' then x else f k'

fmostlytrue = override (override ftrue 1 false) 3 false

override-example1 : fmostlytrue 0 ≡ true
override-example1 = refl
override-example2 : fmostlytrue 1 ≡ false
override-example2 = refl
override-example3 : fmostlytrue 2 ≡ true
override-example3 = refl
override-example4 : fmostlytrue 3 ≡ false
override-example4 = refl

{-
練習問題: ★ (override_example)

次の証明にとりかかる前に、あなたがこの証明の意味することを理解しているか確認するため、証明内容を別の言葉で言い換えてください。証明自体は単純なものです。
-}
-- "「3のときtrue，それ以外のときbとなる関数」に2を適用したらbになることを示せ"
override-example : (b : bool) → override (constfun b) 3 true 2 ≡ b
override-example false = refl
override-example true = refl

-- さらにCoqについて ----------------------------------------------------------

---- unfoldタクティック -------------------------------------------------------

-- unfoldなにそれおいしいの？
-- symでrewrite方向を弄る
unfold-example : {m n : nat} → 3 + n ≡ m → plus3 n + 1 ≡ m + 1
unfold-example eq
  rewrite sym eq
        = refl

-- tacticﾅｸﾃﾓｶﾃﾙｩｰ
override-eq : ∀{x} {X : Set x} →
              (x : X) → (k : nat) → (f : nat → X) →
              override f k x k ≡ x
override-eq x k f
  rewrite sym (beq-nat-refl k)
        = refl


{-
練習問題: ★★ (override_neq)
-}
override-neq : ∀{x} {X : Set x} →
               (x1 x2 : X) → (k1 k2 : nat) → (f : nat → X) →
               f k1 ≡ x1 → beq-nat k1 k2 ≡ false → override f k2 x2 k1 ≡ x1
override-neq x1 x2 k1 k2 f fk1≡x1 k1≠k2
  rewrite beq-nat-sym k2 k1
        | k1≠k2
        | fk1≡x1
        = refl

---- 反転（Inversion） --------------------------------------------------------

-- まぁ，仮定をバッファしておく所があるわけじゃないのでinversion的なものは無いよな…
-- てことはデストラクトに相当する操作でcongするのが定石？

-- というか… dot pattern でいいのか．
eq-add-S : {n m : nat} → S n ≡ S m → n ≡ m
eq-add-S {.m} {m} refl = refl

silly4 : {n m : nat} →  [ n ] ≡ [ m ] → n ≡ m
silly4 {.m} {m} refl = refl

silly5 : {n m o : nat} → n ∷ [ m ] ≡ o ∷ [ o ] → [ n ] ≡ [ m ]
silly5 {.o} {.o} {o} refl = refl

{-
練習問題: ★ (sillyex1)
-}
sillyex1 : ∀{x} {X : Set x} → (x y z : X) → (l j : list X) →
           x ∷ y ∷ l ≡ z ∷ j → y ∷ l ≡ x ∷ j → x ≡ y
sillyex1 x y z l j eq1 eq2 = sym (assert y x l j eq2)
  where
    assert : ∀{x} {X : Set x} → (x y : X) → (xs ys : list X) →
              x ∷ xs ≡ y ∷ ys → x ≡ y
    assert .y y .ys ys refl = refl

silly6 : (n : nat) → S n ≡ 0 → 2 + 2 ≡ 5
silly6 n ()

silly7 : (n m : nat) → false ≡ true → [ n ] ≡ [ m ]
silly7 n m ()

{-
練習問題: ★ (sillyex2)
-}
sillyex2 : ∀{x} {X : Set x} → (x y z : X) → (l j : list X) →
           x ∷ y ∷ l ≡ [] → y ∷ l ≡ z ∷ j → x ≡ z
sillyex2 _ _ _ _ _ ()

eq-remove-S : ∀{n m} → n ≡ m → S n ≡ S m
eq-remove-S {.m} {m} refl = refl

beq-nat-≡ : ∀{n m} → true ≡ beq-nat n m → n ≡ m
beq-nat-≡ {0} {0} refl = refl
beq-nat-≡ {0} {S _} ()
beq-nat-≡ {S _} {0} ()
beq-nat-≡ {S n} {S m} eq
  rewrite beq-nat-≡ {n} {m} eq
        = refl

{-
練習問題: ★★ (beq_nat_eq_informal)

beq_nat_eqの、非形式的な証明を示しなさい。
-}
-- 略


{-
練習問題: ★★★ (beq_nat_eq')

beq_nat_eqは、mについて帰納法をつかうことで証明することができました。しかし我々は、もう少し変数を導入する順序に注意を払うべきです。なぜなら、我々は一般に、十分な帰納法の仮定を得ているからです。このことを次に示します。次の証明を完成させなさい。この練習問題の効果を最大にするため、とりあえずは先にやった証明を見ないで取り組んでください。
-}
-- どういうことだってばよ？
beq-nat-≡' : ∀{m n} → beq-nat n m ≡ true → n ≡ m
beq-nat-≡' {0} {0} refl = refl
beq-nat-≡' {0} {S _} ()
beq-nat-≡' {S _} {0} ()
beq-nat-≡' {S m} {S n} eq
  rewrite beq-nat-≡' {m} {n} eq
        = refl

length-snoc' : ∀{x} {X : Set x} →
               (v : X) → (l : list X) (n : nat) →
               length l ≡ n → length (snoc l v) ≡ S n
length-snoc' v [] 0 eq = refl
length-snoc' v [] (S _) ()
length-snoc' v (x ∷ xs) 0 ()
length-snoc' v (x ∷ xs) (S n) eq
  rewrite length-snoc' v xs n (eq-add-S {length xs} {n} eq)
        = refl

------ 練習問題 ---------------------------------------------------------------

{-
練習問題: ★★, optional (practice)

同じところに分類され、相互に関連するような、自明でもないが複雑というほどでもない証明をいくつか練習問題としましょう。このうち、いくつかは過去のレクチャーや練習問題に出てきた補題を使用します。
-}
beq-nat-0-l : ∀{n} → true ≡ beq-nat 0 n → 0 ≡ n
beq-nat-0-l = beq-nat-≡ {0}

beq-nat-0-r : ∀{n} → true ≡ beq-nat n 0 → 0 ≡ n
beq-nat-0-r {n} eq = sym (beq-nat-≡ {n} {0} eq)

double-injective : ∀{n m} → double n ≡ double m → n ≡ m
double-injective {0} {0} refl = refl
double-injective {0} {S _} ()
double-injective {S _} {0} ()
double-injective {S n} {S m} eq = cong S $ ind $ drop-S2 $ drop-S1 eq
  where
    ind = double-injective {n} {m}
    drop-S1 = eq-add-S {S (double n)} {S (double m)}
    drop-S2 = eq-add-S {double n} {double m}


---- タクティックを仮定に使用する ---------------------------------------------

-- ?
S-inj : (n m : nat) → (b : bool) → beq-nat (S n) (S m) ≡ b → beq-nat n m ≡ b
S-inj n m b eq = eq

-- 何?
silly3' : (n : nat) → (beq-nat n 5 ≡ true → beq-nat (S (S n)) 7 ≡ true) →
          true ≡ beq-nat n 5 → true ≡ beq-nat (S (S n)) 7
silly3' n _ eq = eq

{-
練習問題: ★★★, recommended (plus_n_n_injective)

先に述べた"in"を使って次の証明をしなさい。
-}
Sn+Sn≡SSn+n : ∀{n} → S n + S n ≡ S (S (n + n))
Sn+Sn≡SSn+n {n}
  rewrite plus-assoc (S n) 1 n
        | plus-comm n 1
        = refl

n+n-injective : {n m : nat} → n + n ≡ m + m → n ≡ m
n+n-injective {0} {0} refl = refl
n+n-injective {0} {S _} ()
n+n-injective {S _} {0} ()
n+n-injective {S n} {S m} eq = cong S $ ind $ drop-S2 $ drop-S1 $ toSS eq
  where
    ind = n+n-injective {n} {m}
    drop-S1 = eq-add-S {S (n + n)} {S (m + m)}
    drop-S2 = eq-add-S {n + n} {m + m}
    toSS = subst₂ (_≡_) (Sn+Sn≡SSn+n {n}) (Sn+Sn≡SSn+n {m})

---- destructを複合式で使う ---------------------------------------------------

sillyfun : nat → bool
sillyfun n with beq-nat n 3
sillyfun n | true = false
sillyfun n | false with beq-nat n 5
sillyfun n | false | true = false
sillyfun n | false | false = false

sillyfun-false : ∀{n} → sillyfun n ≡ false
sillyfun-false {n} with beq-nat n 3
sillyfun-false {n} | true = refl
sillyfun-false {n} | false with beq-nat n 5
sillyfun-false {n} | false | true = refl
sillyfun-false {n} | false | false = refl

{-
練習問題: ★ (override_shadow)
-}
override-shadow : ∀{x} {X : Set x} → (x1 x2 : X) → (k1 k2 : nat) → (f : nat → X) →
                  (override (override f k1 x2) k1 x1) k2 ≡ (override f k1 x1) k2
override-shadow x1 x2 k1 k2 f with beq-nat k1 k2
override-shadow x1 x2 k1 k2 f | true = refl
override-shadow x1 x2 k1 k2 f | false = refl


{-
練習問題: ★★★, recommended (combine_split)
-}
combine-split : ∀{x y} {X : Set x} {Y : Set y} → (xys : list (X × Y)) →
                combine (split xys) ≡ xys
combine-split [] = refl
combine-split ((x , y) ∷ xys) =
  begin
     combine (split ((x , y) ∷ xys))
  ≡⟨ refl ⟩
     combine (prod-map (_∷_ x) (_∷_ y) (split xys))
  ≡⟨ combine-prod-map x y (split xys) ⟩
     (x , y) ∷ combine (split xys)
  ≡⟨ cong (_∷_ (x , y)) (combine-split xys) ⟩
     (x , y) ∷ xys
  ∎
  where
    open PropEq.≡-Reasoning
    combine-prod-map : ∀{x y} {X : Set x} {Y : Set y} →
                       (x : X) → (y : Y) → (xsys : list X × list Y) →
                       combine (prod-map (_∷_ x) (_∷_ y) xsys) ≡ (x , y) ∷ combine xsys
    combine-prod-map x y (xs , ys) = refl

{-
練習問題: ★★★, optional (split_combine)

思考練習: 我々はすでに、全ての型のリストのペアでcombineがsplitの逆関数であることを証明しました。ではその逆の「splitはcombineの逆関数である」を示すことはできるでしょうか？

ヒント: split combine l1 l2 = (l1,l2)がtrueとなるl1、l2の条件は何でしょう？
-}
-- 長さの同じリストのときのみ可能

{-
この定理をCoqで証明しなさい（なるべくintrosを使うタイミングを遅らせ、帰納法の仮定を一般化させておくといいでしょう。
-}
split-combine : ∀{x y} {X : Set x} {Y : Set y} → (xsys : list X × list Y) →
                length (fst xsys) ≡ length (snd xsys) → split (combine xsys) ≡ xsys
split-combine ([] , []) refl = refl
split-combine ([] , y ∷ ys) ()
split-combine (x ∷ xs , []) ()
split-combine (x ∷ xs , y ∷ ys) eq = cong pm (split-combine (xs , ys) (tail-length-equiv eq))
  where
    ∷→S : ∀{x} {X : Set x} → (x : X) → (xs : list X) → length (x ∷ xs) ≡ S (length xs)
    ∷→S x xs = refl
    ∷≡∷→S≡S = subst₂ (_≡_) (∷→S x xs) (∷→S y ys)
    tail-length-equiv : length (x ∷ xs) ≡ length (y ∷ ys) → length xs ≡ length ys
    tail-length-equiv eq = eq-add-S {length xs} {length ys} (∷≡∷→S≡S eq)
    pm = prod-map (_∷_ x) (_∷_ y)

---- rememberタクティック -----------------------------------------------------

sillyfun1 : nat → bool
sillyfun1 n with beq-nat n 3
sillyfun1 n | true = true
sillyfun1 n | false with beq-nat n 5
sillyfun1 n | false | true = true
sillyfun1 n | false | false = false

-- うーん remember がマップできてるかよくわからないな．これ対応してるかなぁ？
sillyfun1-odd : ∀{n} → sillyfun1 n ≡ true → oddb n ≡ true
sillyfun1-odd {n} = 3-5-is-odd ∘ n-is-3-or-5
  where
    n-is-3-or-5 : sillyfun1 n ≡ true → true ≡ beq-nat n 3 ⊎ true ≡ beq-nat n 5
    n-is-3-or-5 eq with beq-nat n 3
    n-is-3-or-5 refl | true = inj₁ refl -- remember as e3
    n-is-3-or-5 eq   | false with beq-nat n 5 -- ここで分岐に使うと同時に以下で結果を保存
    n-is-3-or-5 refl | false | true = inj₂ refl -- remember as e5
    n-is-3-or-5 () | false | false
    3-5-is-odd : true ≡ beq-nat n 3 ⊎ true ≡ beq-nat n 5 → oddb n ≡ true
    3-5-is-odd (inj₁ eq) = cong oddb (beq-nat-≡ {n} {3} eq) -- use e3
    3-5-is-odd (inj₂ eq) = cong oddb (beq-nat-≡ {n} {5} eq) -- use e5

{-
練習問題: ★★ (override_same)
-}
t≡B∨f≡B : ∀{b} → true ≡ b ⊎ false ≡ b
t≡B∨f≡B {true} = inj₁ refl
t≡B∨f≡B {false} = inj₂ refl

override-same : ∀{x} {X : Set x} →
                (x1 : X) → (k1 k2 : nat) → (f : nat → X) →
                f k1 ≡ x1 → (override f k1 x1) k2 ≡ f k2
override-same x1 k1 k2 f eq = override-same' $ assert' $ t≡B∨f≡B {beq-nat k1 k2}
  where
    override-same' : (true ≡ beq-nat k1 k2 × x1 ≡ f k2) ⊎ (false ≡ beq-nat k1 k2 × f k2 ≡ f k2) →
                     (override f k1 x1) k2 ≡ f k2
    override-same' eq with beq-nat k1 k2
    override-same' (inj₁ (refl , eq))| true = eq
    override-same' (inj₁ (() , _))| false
    override-same' (inj₂ (() , _))| true
    override-same' (inj₂ (refl , refl))| false = refl
    assert' : true ≡ beq-nat k1 k2 ⊎ false ≡ beq-nat k1 k2 →
              (true ≡ beq-nat k1 k2 × x1 ≡ f k2) ⊎ (false ≡ beq-nat k1 k2 × f k2 ≡ f k2)
    assert' (inj₁ eq') = inj₁ (eq' , (sym eq ⟨ trans ⟩ cong f (beq-nat-≡ {k1} {k2} eq')) )
    assert' (inj₂ eq') = inj₂ (eq' , refl)

{-
練習問題: ★★★, optional (filter_exercise)

この問題はやや難しいかもしれません。最初にintrosを使うと、帰納法を適用するための変数まで上に上げてしまうので気をつけてください。
-}

filter-exercise : ∀{x} {X : Set x} →
                  (test : X → bool) → (x : X) → (l lf : list X) →
                  filter test l ≡ x ∷ lf → test x ≡ true
filter-exercise test x [] lf ()
filter-exercise test x (y ∷ ys) lf eq = assert2 $ assert1 eq
  where
    head-inversion : ∀{x} {X : Set x} →
                     (a b : X) → (as bs : list X) →
                     a ∷ as ≡ b ∷ bs → a ≡ b
    head-inversion .b b .bs bs refl = refl
    assert1 : filter test (y ∷ ys) ≡ x ∷ lf →
              (true ≡ test y × y ∷ filter test ys ≡ x ∷ lf) ⊎
              (false ≡ test y × filter test ys ≡ x ∷ lf)
    assert1 eq with test y
    assert1 eq | true = inj₁ (refl , eq)
    assert1 eq | false = inj₂ (refl , eq)
    assert2 : (true ≡ test y × y ∷ filter test ys ≡ x ∷ lf) ⊎
              (false ≡ test y × filter test ys ≡ x ∷ lf) ->
              test x ≡ true
    assert2 (inj₂ (eq1 , eq2)) = filter-exercise test x ys lf eq2
    assert2 (inj₁ (eq1 , eq2)) = sym (eq1 ⟨ trans ⟩ cong test (head-inversion y x (filter test ys) lf eq2))

---- apply ... with ...タクティック -------------------------------------------

trans-eq-example : {a b c d e f : nat} →
                   a ∷ [ b ] ≡ c ∷ [ d ] → c ∷ [ d ] ≡ e ∷ [ f ] → a ∷ [ b ] ≡ e ∷ [ f ]
trans-eq-example eq1 eq2
  rewrite eq1
        | eq2
        = refl
-- trans-eq-example = trans でいいけど

trans-≡ : ∀{x} {X : Set x} {n m o : X} → n ≡ m → m ≡ o → n ≡ o
trans-≡ eq1 eq2
  rewrite eq1
        | eq2
        = refl

{-
練習問題: ★★★, recommended (apply_exercises)
-}
trans-≡-exercise : {n m o p : nat} →
                   m ≡ minustwo o → n + p ≡ m → n + p ≡ minustwo o
trans-≡-exercise eq1 eq2 = trans eq2 eq1

nat-≡-eq : ∀{n m} → n ≡ m → true ≡ beq-nat n m
nat-≡-eq {0} {0} refl = refl
nat-≡-eq {0} {S _} ()
nat-≡-eq {S _} {0} ()
nat-≡-eq {S n} {S m} eq = nat-≡-eq {n} {m} (eq-add-S eq)

beq-nat-trans : ∀{n m p} → true ≡ beq-nat n m → true ≡ beq-nat m p → true ≡ beq-nat n p
beq-nat-trans {n} {m} {p} eq1 eq2
  rewrite beq-nat-≡ {n} {m} eq1
        | beq-nat-≡ {m} {p} eq2
        = beq-nat-refl p

override-permute : ∀{x} {X : Set x} →
                   (x1 x2 : X) → (k1 k2 k3 : nat) → (f : nat → X) →
                   false ≡ beq-nat k2 k1 →
                   (override (override f k2 x2) k1 x1) k3 ≡ (override (override f k1 x1) k2 x2) k3
override-permute x1 x2 k1 k2 k3 f eq = assert2 $ assert1
  where
    assert1 : ((false ≡ beq-nat k1 k3 × false ≡ beq-nat k2 k3) ⊎
               (false ≡ beq-nat k1 k3 × true ≡ beq-nat k2 k3)) ⊎
              ((true ≡ beq-nat k1 k3 × false ≡ beq-nat k2 k3) ⊎
               (true ≡ beq-nat k1 k3 × true ≡ beq-nat k2 k3))
    assert1 with beq-nat k1 k3 | beq-nat k2 k3
    ... | false | false = inj₁ (inj₁ (refl , refl))
    ... | false | true = inj₁ (inj₂ (refl , refl))
    ... | true | false = inj₂ (inj₁ (refl , refl))
    ... | true | true = inj₂ (inj₂ (refl , refl))
    assert2 : ((false ≡ beq-nat k1 k3 × false ≡ beq-nat k2 k3) ⊎
               (false ≡ beq-nat k1 k3 × true ≡ beq-nat k2 k3)) ⊎
              ((true ≡ beq-nat k1 k3 × false ≡ beq-nat k2 k3) ⊎
               (true ≡ beq-nat k1 k3 × true ≡ beq-nat k2 k3)) →
              (override (override f k2 x2) k1 x1) k3 ≡ (override (override f k1 x1) k2 x2) k3
    assert2 (inj₁ (inj₁ (eq1 , eq2))) with beq-nat k1 k3 | beq-nat k2 k3
    assert2 (inj₁ (inj₁ (eq1 , eq2))) | false | false = refl
    assert2 (inj₁ (inj₁ (eq1 , ()))) | false | true
    assert2 (inj₁ (inj₁ (() , eq2))) | true | false
    assert2 (inj₁ (inj₁ (() , eq2))) | true | true
    assert2 (inj₁ (inj₂ (eq1 , eq2))) with beq-nat k1 k3 | beq-nat k2 k3
    assert2 (inj₁ (inj₂ (eq1 , ()))) | false | false
    assert2 (inj₁ (inj₂ (eq1 , eq2))) | false | true = refl
    assert2 (inj₁ (inj₂ (eq1 , ()))) | true | false
    assert2 (inj₁ (inj₂ (() , eq2))) | true | true
    assert2 (inj₂ (inj₁ (eq1 , eq2))) with beq-nat k1 k3 | beq-nat k2 k3
    assert2 (inj₂ (inj₁ (() , eq2))) | false | false
    assert2 (inj₂ (inj₁ (() , eq2))) | false | true
    assert2 (inj₂ (inj₁ (eq1 , eq2))) | true | false = refl
    assert2 (inj₂ (inj₁ (eq1 , ()))) | true | true
    assert2 (inj₂ (inj₂ (eq1 , eq2))) with trans eq
                                             (sym
                                              (beq-nat-trans {k2} {k3} {k1} eq2
                                               (eq1 ⟨ trans ⟩ beq-nat-sym k1 k3)))
    assert2 (inj₂ (inj₂ (eq1 , eq2))) | ()


-- まとめ ---------------------------------------------------------------------

-- さらなる練習問題 -----------------------------------------------------------

{-
練習問題: ★★, optional (fold_length)

リストに関する多くの一般的な関数はfoldを使って書きなおすることができます。例えば、次に示すのはlengthの別な実装です。
-}
fold-length : ∀{x} {X : Set x} (ls : list X) → nat
fold-length ls = fold (λ _ n → S n) ls 0

test-fold-length1 : fold-length (4 ∷ 7 ∷ [ 0 ]) ≡ 3
test-fold-length1 = refl

fold-length-correct : ∀{x} {X : Set x} (ls : list X) → fold-length ls ≡ length ls
fold-length-correct [] = refl
fold-length-correct (x ∷ xs)
  rewrite fold-length-correct xs
        = refl

{-
練習問題: ★★★, recommended (fold_map)

map関数もfoldを使って書くことができます。以下のfold_mapを完成させなさい。
-}
fold-map : ∀{x y} {X : Set x} {Y : Set y} → (X → Y) → list X → list Y
fold-map f ls = fold (λ x ys → f x ∷ ys) ls []


fold-map-correct : ∀{x y} {X : Set x} {Y : Set y} → (f : X → Y) → (xs : list X) →
                   fold-map f xs ≡ map f xs
fold-map-correct f [] = refl
fold-map-correct f (x ∷ xs)
  rewrite fold-map-correct f xs
        = refl

{-
練習問題: ★★, optional (mumble_grumble)

つぎの、機能的に定義された二つの型をよく観察してください。

data mumble : Set where
  a : mumble
  b : mumble → nat → mumble
  c : mumble

data grumble {x} (X : Set x) : Set x where
  d : mumble → grumble X
  e : X → grumble X

次の式のうち、ある型Xについてgrumble Xの要素として正しく定義されているものはどれでしょうか。
d (b a 5)
d mumble (b a 5)
d bool (b a 5)
e bool true
e mumble (b c 0)
e bool (b c 0)
c
-}
-- d (b a 5) のみ

{-
練習問題: ★★, optional (baz_num_elts)

次の、機能的に定義された型をよく観察してください。

data baz : Set where
  x : baz → baz
  y : baz → bool → baz

型bazはいくつの要素を持つことができるでしょうか？
-}
-- ひとつも持てない

{-
練習問題: ★★★★, recommended (forall_exists_challenge)

チャレンジ問題: 二つの再帰関数forallb、existsbを定義しなさい。forallbは、リストの全ての要素が与えられた条件を満たしているかどうかを返します。
-}
forallb : ∀{x} {X : Set x} → (X → bool) → list X → bool
forallb p xs = fold (λ x b → andb (p x) b) xs true

existsb : ∀{x} {X : Set x} → (X → bool) → list X → bool
existsb p xs = fold (λ x b → orb (p x) b) xs false

existsb' : ∀{x} {X : Set x} → (X → bool) → list X → bool
existsb' p = negb ∘ forallb (negb ∘ p)

existb≡existsb' : ∀{x} {X : Set x} →
                  (p : X → bool) → (xs : list X) →
                  existsb p xs ≡ existsb' p xs
existb≡existsb' p [] = refl
existb≡existsb' p (x ∷ xs) =
  begin
     existsb p (x ∷ xs)
  ≡⟨ refl ⟩
     orb (p x) (existsb p xs)
  ≡⟨ cong (orb (p x)) (existb≡existsb' p xs) ⟩
     orb (p x) (existsb' p xs)
  ≡⟨ refl ⟩
     orb (p x) (negb (forallb (negb ∘ p) xs))
  ≡⟨ sym (not-not-P≡P) ⟩
     negb (negb (orb (p x) (negb (forallb (negb ∘ p) xs))))
  ≡⟨ cong negb (not-P∨Q≡not-P∧not-Q {p x}) ⟩
     negb (andb (negb (p x)) (negb (negb (forallb (negb ∘ p) xs))))
  ≡⟨ cong (λ a → negb (andb (negb (p x)) a)) not-not-P≡P ⟩
     negb (andb (negb (p x)) (forallb (negb ∘ p) xs))
  ≡⟨ refl ⟩
     existsb' p (x ∷ xs)
  ∎
  where
    open PropEq.≡-Reasoning
    not-not-P≡P : ∀{x} → negb (negb x) ≡ x
    not-not-P≡P {false} = refl
    not-not-P≡P {true} = refl
    not-P∨Q≡not-P∧not-Q : ∀{x y} → negb (orb x y) ≡ andb (negb x) (negb y)
    not-P∨Q≡not-P∧not-Q {false} {false} = refl
    not-P∨Q≡not-P∧not-Q {false} {true} = refl
    not-P∨Q≡not-P∧not-Q {true} {false} = refl
    not-P∨Q≡not-P∧not-Q {true} {true} = refl

{-
練習問題: ★★, optional (index_informal)

index関数の定義を思い出してください。

次の定理の、非形式的な証明を書きなさい。
   ∀ X n l, length l = n → @index X (S n) l = None.
-}
-- ニポンゴ書くのめんどくさいので形式的な証明でカンベン
out-of-bounds : ∀{x} {X : Set x} → (n : nat) → (xs : list X) →
                length xs ≡ n → index (S n) xs ≡ None
out-of-bounds n [] eq = refl
out-of-bounds 0 (x ∷ xs) ()
out-of-bounds (S n) (x ∷ xs) eq = out-of-bounds n xs $ eq-add-S eq
