module Basics where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Day : Set where
  Monday : Day
  Tuesday : Day
  Wednesday : Day
  Thursday : Day
  Friday : Day
  Saturday : Day
  Sunday : Day

nextWeekday : Day -> Day
nextWeekday Monday = Tuesday
nextWeekday Tuesday = Wednesday
nextWeekday Wednesday = Thursday
nextWeekday Thursday = Friday
nextWeekday Friday = Monday
nextWeekday Saturday = Monday
nextWeekday Sunday = Monday

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> nextWeekday Friday
Monday
Main> nextWeekday (nextWeekday Saturday)
Tuesday
-}

test_nextWeekday : nextWeekday (nextWeekday Saturday) ≡ Tuesday
test_nextWeekday = refl

data Bool : Set where
  True : Bool
  False : Bool

negb : Bool -> Bool
negb True = False
negb False = True

andb : Bool -> Bool -> Bool
andb True b = b
andb False _ = False

orb : Bool -> Bool -> Bool
orb True _ = True
orb False b = b

test_orb1 : orb True False ≡ True
test_orb1 = refl
test_orb2 : orb False False ≡ False
test_orb2 = refl
test_orb3 : orb False True ≡ True
test_orb3 = refl
test_orb4 : orb True True ≡ True
test_orb4 = refl

admit = {!!}

{-
練習問題: ★ (nandb)

次の定義を完成させ、Exampleで記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。

この関数はどちらか、もしくは両方がfalseになったときにtrueを返すものである。
-}
nandb : Bool -> Bool -> Bool
nandb True b = negb b
nandb False _ = True

{-
下の定義からAdmitted.を取り去り、代わりに"Proof. simpl. reflexivity. Qed."で検証できるようなコードを記述しなさい。
-}
test_nandb1 : nandb True False ≡ True
test_nandb1 = refl
test_nandb2 : nandb False False ≡ True
test_nandb2 = refl
test_nandb3 : nandb False True ≡ True
test_nandb3 = refl
test_nandb4 : nandb True True ≡ False
test_nandb4 = refl

{-
練習問題: ★ (andb3)
-}
andb3 : Bool -> Bool -> Bool -> Bool
andb3 a b c = andb a (andb b c)

test_andb31 : andb3 True True True ≡ True
test_andb31 = refl
test_andb32 : andb3 False True True ≡ False
test_andb32 = refl
test_andb33 : andb3 True False True ≡ False
test_andb33 = refl
test_andb34 : andb3 True True False ≡ False
test_andb34 = refl
