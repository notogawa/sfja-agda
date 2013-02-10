module Lists-J where

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; sym; cong)

open import Basics-J


-- 数のペア -------------------------------------------------------------------

module NatList where
  data natprod' : Set where
    pair : nat → nat → natprod'

  fst' : natprod' → nat
  fst' (pair a b) = a

  snd' : natprod' → nat
  snd' (pair a b) = b

  --_,_ : ℕ → ℕ → ℕ-prod'
  --_,_ = pair

  {-
  $ agda -I -i/usr/share/agda-stdlib -i. Lists.agda
  Main> fst (3 , 4)
  3
  -}

  -- Notationは無いのとこっちのがソレっぽいので
  data natprod : Set where
    _,_ : nat → nat → natprod

  fst : natprod → nat
  fst (a , b) = a

  snd : natprod → nat
  snd (a , b) = b

  swap-pair : natprod → natprod
  swap-pair (a , b) = (b , a)

  surjective-pairing' : (n m : nat) → (n , m) ≡ (fst (n , m) , snd (n , m))
  surjective-pairing' n m  = refl

  surjective-pairing : (p : natprod) → p ≡ (fst p , snd p)
  surjective-pairing (n , m) = refl
  -- surjective-pairing p = refl
  -- こちらではダメ，"p の構造を明らかにする必要があります"なので

  {-
  練習問題: ★ (snd_fst_is_swap)
  -}
  snd-fst-is-swap : (p : natprod) → (snd p , fst p) ≡ swap-pair p
  snd-fst-is-swap (n , m) = refl

-- 数のリスト -----------------------------------------------------------------

  data natlist : Set where
    [] : natlist
    _∷_ : nat → natlist → natlist

  infixr 5 _∷_

  [_] : nat → natlist
  [ x ] = x ∷ []

  l-123 : natlist
  l-123 = 1 ∷ 2 ∷ 3 ∷ []

  l_123' = 1 ∷ (2 ∷ [ 3 ])
  l_123'' = 1 ∷ 2 ∷ [ 3 ]
  -- l_123''' = [ 1 , 2 , 3 ] -- これはできない

  repeat : nat → nat → natlist
  repeat n 0 = []
  repeat n (S count) = n ∷ repeat n count

  length : natlist → nat
  length [] = 0
  length (_ ∷ ns) = S (length ns)

  app : natlist → natlist → natlist
  app [] ys = ys
  app (x ∷ xs) ys = x ∷ app xs ys

  _++_ : natlist → natlist → natlist
  _++_ = app

  infixr 5 _++_

  test-app1 : 1 ∷ 2 ∷ [ 3 ] ++ 4 ∷ [ 5 ] ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
  test-app1 = refl
  test-app2 : [] ++ 4 ∷ [ 5 ] ≡ 4 ∷ [ 5 ]
  test-app2 = refl
  test-app3 : 1 ∷ 2 ∷ [ 3 ] ++ [] ≡ 1 ∷ 2 ∷ [ 3 ]
  test-app3 = refl

  hd : nat → natlist → nat
  hd default [] = default
  hd _ (x ∷ _) = x

  tail : natlist → natlist
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
  nonzeros : natlist → natlist
  nonzeros [] = []
  nonzeros (0 ∷ xs) = nonzeros xs
  nonzeros (S x ∷ xs) = S x ∷ nonzeros xs

  test-nonzeros : nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ [ 0 ]) ≡ 1 ∷ 2 ∷ [ 3 ]
  test-nonzeros = refl

  oddmembers : natlist → natlist
  oddmembers [] = []
  oddmembers (x ∷ xs) with oddb x
  ... | true = x ∷ oddmembers xs
  ... | false = oddmembers xs

  test-oddmembers : oddmembers (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ [ 0 ]) ≡ 1 ∷ [ 3 ]
  test-oddmembers = refl

  countoddmembers : natlist → nat
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
  alternate : natlist → natlist → natlist
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

---- リストを使ったバッグ -----------------------------------------------------

  bag : Set
  bag = natlist

  {-
  練習問題: ★★★ (bag_functions)

  バッグに対する count、 sum、 add、 member 関数の定義を完成させなさい。
  -}
  count : nat → bag → nat
  count n [] = 0
  count n (x ∷ xs) with beq-nat n x
  ... | true = S (count n xs)
  ... | false = count n xs

  test-count1 : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ 3
  test-count1 = refl
  test-count2 : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ 0
  test-count2 = refl

  sum : bag → bag → bag
  sum = app

  test-sum1 : count 1 (sum (1 ∷ 2 ∷  [ 3 ]) (1 ∷ 4 ∷ [ 1 ])) ≡ 3
  test-sum1 = refl

  add : nat → bag → bag
  add = _∷_

  test-add1 : count 1 (add 1 (1 ∷ 4 ∷ [ 1 ])) ≡ 3
  test-add1 = refl
  test-add2 : count 5 (add 1 (1 ∷ 4 ∷ [ 1 ])) ≡ 0
  test-add2 = refl

  member : nat → bag → bool
  member n [] = false
  member n (x ∷ xs) with beq-nat n x
  ... | true = true
  ... | false = member n xs

  test-member1 : member 1 (1 ∷ 4 ∷ [ 1 ]) ≡ true
  test-member1 = refl
  test-member2 : member 2 (1 ∷ 4 ∷ [ 1 ]) ≡ false
  test-member2 = refl

  {-
  練習問題: ★★★, optional (bag_more_functions)

  練習として、さらにいくつかの関数を作成してください。
  -}
  remove-one : nat → bag → bag
  remove-one n [] = []
  remove-one n (x ∷ xs) with beq-nat n x
  ... | true = xs
  ... | false = x ∷ remove-one n xs

  test-remove-one1 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ [ 1 ])) ≡ 0
  test-remove-one1 = refl
  test-remove-one2 : count 5 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ [ 1 ])) ≡ 0
  test-remove-one2 = refl
  test-remove-one3 : count 4 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 2
  test-remove-one3 = refl
  test-remove-one4 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 1
  test-remove-one4 = refl

  remove-all : nat → bag → bag
  remove-all n [] = []
  remove-all n (x ∷ xs) with beq-nat n x
  ... | true = remove-all n xs
  ... | false = x ∷ remove-all n xs

  test-remove-all1 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷  [ 1 ])) ≡ 0
  test-remove-all1 = refl
  test-remove-all2 : count 5 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ [ 1 ])) ≡ 0
  test-remove-all2 = refl
  test-remove-all3 : count 4 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 2
  test-remove-all3 = refl
  test-remove-all4 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ [ 4 ])) ≡ 0
  test-remove-all4 = refl

  subset : bag → bag → bool
  subset [] ys = true
  subset (x ∷ xs) ys with count x ys
  ... | 0 = false
  ... | S _ = subset xs (remove-one x ys)

  test-subset1 : subset (1 ∷ [ 2 ]) (2 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ true
  test-subset1 = refl
  test-subset2 : subset (1 ∷ 2 ∷ [ 2 ]) (2 ∷ 1 ∷ 4 ∷ [ 1 ]) ≡ false
  test-subset2 = refl

  {-
  練習問題: ★★★, recommended (bag_theorem)

  count や add を使ったバッグに関する面白い定理書き、それを証明しなさい。この問題はいわゆる自由課題で、真になることがわかっていても、証明にはまだ習っていない技を使わなければならない定理を思いついてしまうこともあります。証明に行き詰まってしまったら気軽に質問してください。
  -}
  add-count-commute-count-inc : (n : nat) (xs : bag) → count n (add n xs) ≡ 1 + count n xs
  add-count-commute-count-inc n xs with beq-nat n n | beq-nat-refl n
  ... | true | refl = refl
  ... | false | ()

-- リストに関する推論 ---------------------------------------------------------

  nil-app : (l : natlist) → [] ++ l ≡ l
  nil-app l = refl

  tl-length-pred : (l : natlist) → pred (length l) ≡ length (tail l)
  tl-length-pred [] = refl
  tl-length-pred (x ∷ xs) = refl

---- お小言 -------------------------------------------------------------------
-- Coqしたくないでござる！絶対にCoqしたくないでござる！

---- リスト上の帰納法 ---------------------------------------------------------

  app-ass : (l1 l2 l3 : natlist) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
  app-ass [] ys zs = refl
  app-ass (x ∷ xs) ys zs = cong (λ as → x ∷ as) (app-ass xs ys zs)

  app-length : (l1 l2 : natlist) → length (l1 ++ l2) ≡ (length l1) + (length l2)
  app-length [] ys = refl
  app-length (x ∷ xs) ys = cong (λ a → 1 + a) (app-length xs ys)

  snoc : natlist → nat → natlist
  snoc [] n = [ n ]
  snoc (x ∷ xs) n = x ∷ snoc xs n

  rev : natlist → natlist
  rev [] = []
  rev (x ∷ xs) = snoc (rev xs) x

  test-rev1 : rev (1 ∷ 2 ∷ [ 3 ]) ≡ (3 ∷ 2 ∷ [ 1 ])
  test-rev1 = refl
  test-rev2 : rev [] ≡ []
  test-rev2 = refl

  {-
  rev-length-firsttry : (l : natlist) → length (rev l) ≡ length l
  rev-length-firsttry [] = refl
  rev-length-firsttry (x ∷ xs) = ?
  -}

  length-snoc : (n : nat) (l : natlist) → length (snoc l n) ≡ 1 + length l
  length-snoc n [] = refl
  length-snoc n (x ∷ xs)
    rewrite length-snoc n xs
          = refl

  rev-length : (l : natlist) → length (rev l) ≡ length l
  rev-length [] = refl
  rev-length (x ∷ xs)
    rewrite length-snoc x (rev xs)
          | rev-length xs
          = refl

---- SearchAbout --------------------------------------------------------------
--- ...

---- リストについての練習問題 (1) ---------------------------------------------
  {-
  練習問題: ★★★, recommended (list_exercises)

  リストについてさらに練習しましょう。
  -}
  app-nil-end : (l : natlist) → l ++ [] ≡ l
  app-nil-end [] = refl
  app-nil-end (x ∷ xs)
    rewrite app-nil-end xs
          = refl

  rev-snoc-commute-rev-cons : (n : nat) (ls : natlist) → rev (snoc ls n) ≡ n ∷ rev ls
  rev-snoc-commute-rev-cons n [] = refl
  rev-snoc-commute-rev-cons n (x ∷ xs) = cong (λ as → snoc as x) (rev-snoc-commute-rev-cons n xs)

  rev-involutive : (l : natlist) → rev (rev l) ≡ l
  rev-involutive [] = refl
  rev-involutive (x ∷ xs)
    rewrite rev-snoc-commute-rev-cons x (rev xs)
          | rev-involutive xs
          = refl

  distr-rev : (l1 l2 : natlist) → rev (l1 ++ l2) ≡ rev l2 ++ rev l1
  distr-rev [] ys
    rewrite app-nil-end (rev ys)
          = refl
  distr-rev (x ∷ xs) ys
    rewrite distr-rev xs ys
          = ++-snoc x (rev ys) (rev xs)
    where
      ++-snoc : (n : nat) (l1 l2 : natlist) → snoc (l1 ++ l2) n ≡ l1 ++ snoc l2 n
      ++-snoc n [] ys = refl
      ++-snoc n (x ∷ xs) ys
        rewrite ++-snoc n xs ys
              = refl

  {-
  次の問題には簡単な解法があります。こんがらがってしまったようであれば、少し戻って単純な方法を探してみましょう。
  -}
  app-ass4 : (l1 l2 l3 l4 : natlist) → l1 ++ (l2 ++ (l3 ++ l4)) ≡ ((l1 ++ l2) ++ l3) ++ l4
  app-ass4 l1 l2 l3 l4
    rewrite app-ass (l1 ++ l2) l3 l4
          | app-ass l1 l2 (l3 ++ l4)
          = refl

  snoc-append : (l : natlist) (n : nat) → snoc l n ≡ l ++ [ n ]
  snoc-append [] n = refl
  snoc-append (x ∷ xs) n
    rewrite snoc-append xs n
          = refl

  {-
  前に書いた nonzeros 関数に関する練習問題です。
  -}
  nonzeros-length : (l1 l2 : natlist) → nonzeros (l1 ++ l2) ≡ (nonzeros l1) ++ (nonzeros l2)
  nonzeros-length [] ys = cong nonzeros (nil-app ys)
  nonzeros-length (0 ∷ xs) ys = nonzeros-length xs ys
  nonzeros-length (S x ∷ xs) ys = cong (λ as → S x ∷ as) (nonzeros-length xs ys)

---- リストについての練習問題 (2) ---------------------------------------------

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

  count-member-nonzero : (s : bag) → ble-nat 1 (count 1 (1 ∷ s)) ≡ true
  count-member-nonzero xs = cong (ble-nat 1) (add-count-commute-count-inc 1 xs)

  ble-n-Sn : (n : nat) → ble-nat n (S n) ≡ true
  ble-n-Sn 0 = refl
  ble-n-Sn (S n) = ble-n-Sn n

  remove-decreases-count : (s : bag) → ble-nat (count 0 (remove-one 0 s)) (count 0 s) ≡ true
  remove-decreases-count [] = refl
  remove-decreases-count (0 ∷ xs) = ble-n-Sn (count 0 xs)
  remove-decreases-count (S n ∷ xs) = remove-decreases-count xs

  {-
  練習問題: ★★★★, optional (rev_injective)

  rev 関数が単射である、すなわち

      ∀ X (l1 l2 : list X), rev l1 = rev l2 → l1 = l2

  であることを証明しなさい。

  この練習問題には簡単な解法と難しい解法があります。
  -}
  rev-injective : (l1 l2 : natlist) → rev l1 ≡ rev l2 → l1 ≡ l2
  rev-injective xs ys eq = rev-injective' (cong rev eq)
    where
      rev-injective' : rev (rev xs) ≡ rev (rev ys) → xs ≡ ys
      rev-injective' eq
        rewrite rev-involutive xs
              | rev-involutive ys
              = eq
  -- 難しい解法ってなんだろう？

-- オプション -----------------------------------------------------------------

  data natoption : Set where
    Some : nat → natoption
    None : natoption

  index-bad : nat → natlist → nat
  index-bad n [] = 42
  index-bad 0 (x ∷ _) = x
  index-bad (S n) (_ ∷ xs) = index-bad n xs

  index : nat → natlist → natoption
  index n [] = None
  index 0 (x ∷ _) = Some x
  index (S n) (_ ∷ xs) = index n xs

  test-index1 : index 0 (4 ∷ 5 ∷ 6 ∷ [ 7 ]) ≡ Some 4
  test-index1 = refl
  test-index2 : index 3 (4 ∷ 5 ∷ 6 ∷ [ 7 ]) ≡ Some 7
  test-index2 = refl
  test-index3 : index 10 (4 ∷ 5 ∷ 6 ∷ [ 7 ]) ≡ None
  test-index3 = refl

  index' : nat → natlist → natoption
  index' n [] = None
  index' n (x ∷ xs) with beq-nat 0 n
  ... | true = Some x
  ... | false = index' (pred n) xs

  option-elim : natoption → nat → nat
  option-elim None default = default
  option-elim (Some n) _ = n

  {-
  練習問題: ★★ (hd_opt)

  同じ考え方を使って、以前定義した hd 関数を修正し、 nil の場合に返す値を渡さなくて済むようにしなさい。
  -}

  hd-opt : natlist → natoption
  hd-opt [] = None
  hd-opt (x ∷ _) = Some x

  test-hd-opt1 : hd-opt [] ≡ None
  test-hd-opt1 = refl
  test-hd-opt2 : hd-opt [ 1 ] ≡ Some 1
  test-hd-opt2 = refl
  test-hd-opt3 : hd-opt (5 ∷ [ 6 ]) ≡ Some 5
  test-hd-opt3 = refl

  {-
  練習問題: ★★, optional (option_elim_hd)

  新しい hd_opt と古い hd の関係についての練習問題です。
  -}

  option-elim-hd : (l : natlist) (default : nat) → hd default l ≡ option-elim (hd-opt l) default
  option-elim-hd [] default = refl
  option-elim-hd (x ∷ xs) default = refl

  {-
  練習問題: ★★, recommended (beq_natlist)

  数のリストふたつを比較し等価性を判定する関数 beq_natlist の定義を完成させなさい。そして、 beq_natlist l l が任意のリスト l で true となることを証明しなさい。
  -}
  beq-natlist : natlist → natlist → bool
  beq-natlist [] [] = true
  beq-natlist [] (y ∷ ys) = false
  beq-natlist (x ∷ xs) [] = false
  beq-natlist (x ∷ xs) (y ∷ ys) = andb (beq-nat x y) (beq-natlist xs ys)

  test-beq-natlist1 : beq-natlist [] [] ≡ true
  test-beq-natlist1 = refl
  test-beq-natlist2 : beq-natlist (1 ∷ 2 ∷ [ 3 ]) (1 ∷ 2 ∷ [ 3 ]) ≡ true
  test-beq-natlist2 = refl
  test-beq-natlist3 : beq-natlist (1 ∷ 2 ∷ [ 3 ]) (1 ∷ 2 ∷ [ 4 ]) ≡ false
  test-beq-natlist3 = refl

  beq-natlist-refl : (l : natlist) → true ≡ beq-natlist l l
  beq-natlist-refl [] = refl
  beq-natlist-refl (x ∷ xs)
    rewrite sym (beq-nat-refl x)
          | sym (beq-natlist-refl xs)
          = refl

-- apply タクティック ---------------------------------------------------------

  silly1 : (n m o p : nat) → n ≡ m → n ∷ [ o ] ≡ n ∷ [ p ] → n ∷ [ o ] ≡ m ∷ [ p ]
  silly1 n m o p eq1 eq2
    rewrite eq1
          = eq2

  silly2 : (n m o p : nat) → n ≡ m → ((q r : nat) → q ≡ r → q ∷ [ o ] ≡ r ∷ [ p ]) → n ∷ [ o ] ≡ m ∷ [ p ]
  silly2 n m o p eq1 eq2 = eq2 n m eq1

  silly2a : (n m : nat) → (n , n) ≡ (m , m) → ((q r : nat) → (q , q) ≡ (r , r) → [ q ] ≡ [ r ]) → [ n ] ≡ [ m ]
  silly2a n m eq1 eq2 = eq2 n m eq1

  {-
  練習問題: ★★, optional (silly_ex)

  次の証明を simpl を使わずに完成させなさい。
  -}
  -- simpl...
  silly-ex : ((n : nat) → evenb n ≡ true → oddb (S n) ≡ true) → evenb 3 ≡ true → oddb 4 ≡ true
  silly-ex eq = eq 3

  {-
  silly3-firsttry : (n : nat) → true ≡ beq-nat n 5 → beq-nat (S (S n)) 7 ≡ true
  silly3-firsttry = ?
  -}

  silly3 : (n : nat) → true ≡ beq-nat n 5 → beq-nat (S (S n)) 7 ≡ true
  silly3 n = sym

  {-
  練習問題: ★★★, recommended (apply_exercise1)
  -}

  rev-exercise1 : (l l' : natlist) → l ≡ rev l' → l' ≡ rev l
  rev-exercise1 l l' eq
    rewrite eq
          | rev-involutive l'
          = refl

  {-
  練習問題: ★ (apply_rewrite)

  apply と rewrite の違いを簡単に説明しなさい。どちらもうまく使えるような場面はありますか？
  -}
  -- 略

-- 帰納法の仮定を変更する -----------------------------------------------------

  {-
  練習問題: ★★, optional (app_ass')

  ++ の結合則をより一般的な仮定のもとで証明しなさい。（最初の行を変更せずに）次の証明を完成させること。
  -}
  -- 略

  {-
  練習問題: ★★★ (apply_exercise2)

  induction の前に m を intros していないことに注意してください。これによって仮定が一般化され、帰納法の仮定が特定の m に縛られることがなくなり、より使いやすくなりました。
  -}
  -- うわーtactic無いとこのへんの文面全然意味無いなー
  beq-nat-sym : (n m : nat) → beq-nat n m ≡ beq-nat m n
  beq-nat-sym 0 0 = refl
  beq-nat-sym 0 (S m) = refl
  beq-nat-sym (S n) 0 = refl
  beq-nat-sym (S n) (S m) = beq-nat-sym n m

  {-
  練習問題: ★★★, recommended (beq_nat_sym_informal)

  以下の補題について上の証明と対応する非形式的な証明を書きなさい。

  定理: 任意の nat n m について、 beq_nat n m = beq_nat m n。
  -}
  -- 略

-- 練習問題: 辞書 -------------------------------------------------------------

module Dictionary where
  open NatList

  data dictionary : Set where
    nat-empty : dictionary
    nat-record : nat → nat → dictionary → dictionary

  insert : (key value : nat) → (d : dictionary) → dictionary
  insert = nat-record

  find : (key : nat) (d : dictionary) → natoption
  find key nat-empty = None
  find key (nat-record k v d) with beq-nat key k
  ... | true = Some v
  ... | false = find key d

  {-
  練習問題: ★ (dictionary_invariant1)
  -}

  dictionary-invariant1 : (d : dictionary) (k v : nat) → find k (insert k v d) ≡ Some v
  dictionary-invariant1 d k v with beq-nat k k | beq-nat-refl k
  ... | true | refl = refl
  ... | false | ()

  {-
  練習問題: ★ (dictionary_invariant2)
  -}

  dictionary-invariant2 : (d : dictionary) (m n o : nat) → beq-nat m n ≡ false → find m d ≡ find m (insert n o d)
  dictionary-invariant2 d m n o eq with beq-nat m n
  dictionary-invariant2 d m n o () | true
  dictionary-invariant2 d m n o eq | false = refl

beq-nat-sym = NatList.beq-nat-sym
