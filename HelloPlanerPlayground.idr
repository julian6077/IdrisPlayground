import Data.Vect
import Data.Fin
{-
import Data.List
import Data.String
import Decidable.Equality
import Data.List.Elem



data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) ->
                 SplitList (lefts ++ rights)

total
splitList : (xs : List a) ->  SplitList xs
splitList xs = splitListHelp xs xs
  where
    splitListHelp : (counter : List a) -> (xs : List a) -> SplitList xs
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: ys) (x :: xs)
       = case splitListHelp ys xs of
              SplitNil => SplitOne
              SplitOne {x=y} => SplitPair [x] [y]
              SplitPair lefts rights => SplitPair (x :: lefts) rights
    splitListHelp _ xs = SplitPair [] xs

mergeSort : Ord a => List a -> List a
mergeSort input with (splitList input)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights)
         = merge (mergeSort lefts) (mergeSort rights)

groupSizes : List Nat 
groupSizes = [3,4,5]

-- Main> :t SplitPair [1,2] [3,4]
-- SplitPair [1, 2] [3, 4] : SplitList [1, 2, 3, 4]

-- goal: 
-- Main> :t OneGroup [[1,2,3]] : FairGroup [1,2,3]
-- Main> :t OneGroup [[1,2,3,5,6]] : Compile Error

-- Main> :t SameSize [[1,2,3], [4,5,6]] : FairGroup [1,2,3,4,5,6]
-- Main> :t SameSize [[1,2,3], [4,5,6]] : FairGroup [1,2,3,4,5,6]


chunks : Nat -> List a -> List (List a)
chunks 0 _    = []   
chunks _ []   = []
chunks n xs   = take n xs :: chunks n (drop n xs)

data AllLT : List (List a) -> Type where
  ALNil  : AllLT []
  ALCons : {xs : List a} -> {rest : List (List a)} ->
           (prf : LT (length xs) 6) -> AllLT rest -> AllLT (xs :: rest)


data AllSameLen : List (List a) -> Nat -> Type where
  ASNil  : AllSameLen [] n
  ASCons : {xs : List a} -> {rest : List (List a)} ->
           (prf : length xs = n) -> AllSameLen rest n -> AllSameLen (xs :: rest) n

data FairGroup : List a -> Type where
  Empty    : FairGroup []
  OneGroup : (group : List (List a)) -> {auto prf : AllLT group} -> FairGroup (concat group)
  SameSize : (group : List (List a)) -> (n : Nat) -> {auto prf : AllSameLen group n} -> {auto prfElem : Elem n groupSizes} -> FairGroup (concat group)

 -}
data Diff : Nat -> Nat -> Type where
  Same : Diff n n
  PlusOne : Diff n (S n)
  MinusOne : Diff (S n) n 

data Elem : a -> List a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

groupSizes : List Nat 
groupSizes = [3,4,5]

maxGroupSize : Nat
maxGroupSize = foldr max 0 groupSizes


-- namespace Test

-- TODO: translate Planer.hs in Planer.idr literally without improving it, to check if it's total


-- groupsLists: [1,2,3,4,5,6] -> [[1,2,3],[4,5,6]]
-- idris2:                   ^^^
-- data FairSizes 
-- covering fairSizes

-- why is there no compile error in Two or Cons when typing FairSizes : Vect n a, in Two the size of resulting vect is n + k
-- can remove need for adding groupSizes when giving [3,4,5] as an explicit List in Elem prf
data FairSizes : Vect n a -> Type where 
  Empty : FairSizes []
  Single : (n : Fin (S maxGroupSize)) -> (ls : Vect (finToNat n) a) -> FairSizes ls
  Two    : (l1 : Vect n a) -> (l2 : Vect k a) -> (validGrps : List Nat) -> {auto validPrfL1 : Elem n validGrps} -> 
    {auto validPrfL2 : Elem k validGrps} -> {auto diffPrf : Diff n k} -> FairSizes (l1 ++ l2 ++ [])
  Cons   : (l1 : Vect n a) -> (l2 : Vect n a) -> FairSizes (l2 ++ ls) -> FairSizes (l1 ++ l2 ++ ls)
  -- Error : (prfs = 26 or 38 ) -> Void

-- Elem (length x) ys cant be automatically solved

-- t : SplitList [1,2,3,4]
-- t = SplitPair [1,2] [3,4]

five : Fin 6
five = 5
four : Fin 6
four = 4
three : Fin 6
three = 3


-- question: weird idris2 compiler code suggestion for ok : FairSizes [1,2,3,4,5] (might need to remove Fin constraint on Single)
-- why cant Fin proof be given implicit and why cant groupSizes in validPrf be given directly in the type

ok1 : FairSizes [1,2,3,4,5]
ok1 = Single five [1,2,3,4,5]

ok2 : FairSizes [1,2,3,4,5,6]
ok2 = Two [1,2,3] [4,5,6] groupSizes


ok3 : FairSizes [1,2,3,4,5,6,7,8,9,10]
ok3 = Cons [1,2,3] [4,5,6] (Two [4,5,6] [7,8,9,10] groupSizes )

-- how can I achieve that the compiler is able to give me one of the correct solution?
bad4 : FairSizes [1,2,3,4,5,6,7,8,9,10]
bad4 = ?hole

ok4 : FairSizes [1,2,3,4,5,6,7,8,9,10]
ok4 = Two [1,2,3,4,5] [6,7,8,9,10] groupSizes
 

-- 0..25 and 39..60 repeats, not total for 26 and 38
fairSizes : (xs : Vect n a) ->  Either (FairSizes xs -> Void) (FairSizes xs)

groupFair : (xs : Vect n a) -> (prf : FairSizes xs) -> (Vect l (Vect k a), Vect z a)



-- for the return type, is it useful to reflect the rules of FairSIzes?, for example that all the inner lists are of same length except for the last which could be one less or one more?
-- return List of Vects and not Vect of Vects because there exist multiple fair ways in how to group a list, so you can't have information on how many groups there will be or smth else
-- groupFair : (xs : List a) -> (List (Vect z a) ++ Vect k a)
-- groupFair : Vect n a -> (List (Vect z a), (k ** Vect k a))


test : List (Vect 2 Nat)
test = [[1,2],[3,4]]




{-
bad : List (Vect n Nat)
bad = [ [1], [2] ]

would also have to work then, but is wrong
useBad : List (Vect 7 Nat)
useBad = bad


good : (n ** List (Vect n Nat))
good = (1 ** [ [1], [2] ])



  data FairGroup : List (List a) -> Type where
      Empty    : FairGroup []
      OneGroup : (xs : List a) -> {auto prfLT : LT (length xs) 6} -> FairGroup [xs]
      SameSize : (xs : List a) -> (n : Nat) -> {auto prfElem : Elem n Group.groupSizes} ->
                 {auto prfDIV : mod (length xs) n = 0} ->
                 FairGroup (chunks n xs) 

    -- examples
    testEmpty : FairGroup []
    testEmpty = Empty

    testOne : FairGroup [[1,2,3,4,5]]
    testOne = OneGroup [1,2,3,4,5]

    t : FairGroup [[1,2,3],[4,5,6]]
  
 -}