import Data.Vect
import Data.Fin
import Data.List.Elem
import Decidable.Equality

-- %default total
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
  DPlusOne : Diff n (S n)
  DMinusOne : Diff (S n) n 



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

-- TODO: schreibe Programm Model auf Zettel, schaue properties, proofs, etc.


more : Integer -> Integer
more x = if (x <= 0) then 1 else more (x-2) + 3

prf1 : (x : Integer) -> ((x < (more x)) = True)
prf1 x = if (x <= 0) then ?hole_01 else ?hole_02

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
-- ok3 = Two [1,2,3,4,5] [6,7,8,9,10]
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

-- WRITE :ti for more information



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




-- rules

modNat : Nat -> Nat -> Nat
modNat n d = case d of
  Z => n
  S k => if n < d then n else Main.modNat (minus n d) d

-- allowed group sizes
grp : List Nat
grp = [3, 4, 5]

maxGroup : Nat
maxGroup = foldr max 0 grp

minGroup : Nat
minGroup = foldr min maxGroup grp

-- need to do it like this to fix compile errors
ValidSize : Nat -> Type
ValidSize x = Elem x grp

threee : Nat 
threee = 3

-- n: projects
-- x: group size
-- to fix compile errors probably need to give minGroup and maxGroup explictly in the type here maybe?
data Fair : (n : Nat) -> (x : Nat) -> Type where

  -- n mod x = 0
  Perfect : (prf_valid : ValidSize x)
              -> (prf_gt  : GT n 5)   -- TODO: cant make code work with maxGroup instead of 5
              -> (prf_mod : Main.modNat n x = 0)
              -> Fair n x

  -- n mod x = 1
  -- not allowed if x = 5
  PlusOne : (prf_valid : ValidSize x)
              -> (prf_gt  : GT n 5)   -- TODO: as above
              -> (prf_mod : Main.modNat n x = 1) 
              -> (prf_ex  : Not (x = 5)) -- TODO: cant make code work with maxGroup instead of 5
              -> Fair n x

  -- x - (n mod x) = 1
  -- = n mod x = x - 1 = pred x
  -- not allowed if x = 3
  MinusOne : (prf_valid : ValidSize x)
               -> (prf_gt  : GT n 5)   -- TODO: as above 
               -> (prf_mod : Main.modNat n x = (pred x))
               -> (prf_ex  : Not (x = Main.threee)) -- TODO: cant make code work with minGroup instead of 3
               -> Fair n x



-- "proof" that n projects can be fairly grouped for some x
-- dependancy on grp
data FairGrouping : (n : Nat) -> Type where
  IsFair : (x : Nat) -> Fair n x -> FairGrouping n

-- functional part
getGroupSize : FairGrouping n -> Nat
getGroupSize (IsFair x _) = x


t1 : GT 7 5 -- automatically found by expression search
t1 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))

hole_04 : 3 = 5 -> Void
hole_04 prf impossible

-- here show expression search
fair7 : FairGrouping 7
--fair7 = IsFair 3 (PlusOne Here t1 Refl (\arg => hole_04 arg) ) -- 3 = 5 -> Void)


-- fair11_rhs_7 : 4 = 3 -> Void

-- hole_56 : (x : Nat ) -> (4 = x) -> Void 

fair111 : FairGrouping 11
fair111 {} = IsFair 4 (MinusOne (There Here) (LTESucc ?fair11_rhs_6) Refl (absurd))

t : 4 = 4
t = Refl {x=4}

t11 : 5 = 5 
t11 = Refl {x=5}


{- idris compiler
While processing right hand side of fair7. When unifying:
    3 = 5
and:
    3 = 5
Mismatch between: 5 and 5.

solution: use absurd or \_ impossible

 -}

fair8 : FairGrouping 8
fair8 = IsFair 4 (Perfect (There Here) (LTESucc ?fair8_rhs_5) Refl)

t2 : GT 11 5 -- automatically found by expression search
t2 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))

fair11 : FairGrouping 11
fair11 = IsFair 4 (MinusOne 
                       (There Here) 
                       t2 -- 11 > 5
                       Refl 
                       (\_ impossible) -- 4 = 3 -> Void
                    )

-- x = 1 arbitary num from grp
--  n = amount of projects
-- case checks like p.232+ and p.247+
checkRule : (n : Nat) -> (x : Nat) -> Dec (Fair n x)
checkRule n x = 
  -- 1. Check if n > 5
  case isGT n maxGroup of
    No notGt => No (notGtLemma notGt) -- hole here gives me a LTE 6 n -> Void instead of GT 6 n -> VOid but is the same thing
    Yes prfGt => 
      -- 2. Check if x is in grp
      case isElem x grp of
        No notElem => No (notElemLemma notElem)
        Yes valid =>
          -- 3. Check Modulo Rules
          case decEq (Main.modNat n x) 0 of
            Yes prfZero => Yes (Perfect valid prfGt prfZero) -- nice
            No notZero =>
              case decEq (Main.modNat n x) 1 of
                Yes prfPlusOne => 
                  -- check constraint
                  case decEq x maxGroup of
                    Yes prfMax => No (isMaxExceptionLemma prfPlusOne prfMax)
                    No notMax => Yes (PlusOne valid prfGt prfPlusOne notMax)
                
                No notPlusOne =>
                  case decEq (Main.modNat n x) (pred x) of
                    Yes prfMinusOne =>
                       -- check constraint
                       case decEq x minGroup of
                         Yes prfMin => No (isMinExceptionLemma prfMinusOne prfMin)
                         No notMin => Yes (MinusOne valid prfGt prfMinusOne notMin)
                  
                    -- no other valid cases left, cant construct Fair in any other way now
                    No notMinusOne => No (failAll notZero notPlusOne notMinusOne)

  where
    -- 1. lemma
    notGtLemma : (GT n 5 -> Void) -> Fair n x -> Void
    notGtLemma notGt (Perfect _ p _)    = notGt p -- can these identical cases be simplified?
    notGtLemma notGt (PlusOne _ p _ _)  = notGt p
    notGtLemma notGt (MinusOne _ p _ _) = notGt p

    -- type checker would fill hole like this:
    -- hole_05 : LTE 6 n -> (Elem x [3, 4, 5] -> Void) -> Fair n x -> Void 
    -- but I already know that n > 5 must be true at this stage, Elem x ... must be simplified to ValidSize to be variable in the future
    -- 2. lemma
    notElemLemma : (ValidSize x -> Void) -> Fair n x -> Void
    notElemLemma notElem (Perfect v _ _)    = notElem v
    notElemLemma notElem (PlusOne v _ _ _)  = notElem v
    notElemLemma notElem (MinusOne v _ _ _) = notElem v


    -- hole type would be hole_06 : LTE 6 n -> Elem x [3, 4, 5] -> (case x of { 0 => n ; S k => let d = S k in if n < d then n else modNat (assert_smaller n (minus n d)) d } = 0 -> Void) -> case x of { 0 => n ; S k => let d = S k in if n < d then n else modNat (assert_smaller n (minus n d)) d } = 1 -> x = 5 -> Fair n x -> Void
    -- 3. lemma when mod=1 but x=5
    isMaxExceptionLemma : (Main.modNat n x = 1) -> (x = Main.maxGroup) -> Fair n x -> Void
    isMaxExceptionLemma prfPlusOne isMax fair = case fair of
        -- perfect wants mod=0 but we have mod=1 -> contradiction, how can I tell this idris?
        (Perfect _ _ p) => ?hole_07
        -- plusOne wants x cant be 5 but we have 5 -> contradiction
        (PlusOne _ _ _ notMax) => notMax isMax
        -- minusOne wants mod=x-1 but we have mod=1 -> contradiction
        (MinusOne _ _ p _) => ?hole_09

    -- almost same as isMaxException
    isMinExceptionLemma : (Main.modNat n x = pred x) -> (x = Main.minGroup) -> Fair n x -> Void
    isMinExceptionLemma prfMinusOne isMin fair = case fair of
        -- perfect wants mod=0 but we have mod=2 -> contradiction, how can I tell this idris?
        (Perfect _ _ p) => ?hole_10
        -- plusOne wants mod=1, we have mod=2 -> contradiction
        (PlusOne _ _ p _) => ?hole_11
        -- minusOne says x cannot be 3 but we have 3 -> contradiction
        (MinusOne _ _ _ notMin) => notMin isMin

    -- no other cases left
    failAll : (Main.modNat n x = 0 -> Void) -> (Main.modNat n x = 1 -> Void) -> (Main.modNat n x = pred x -> Void) -> Fair n x -> Void
    failAll notZero _ _ (Perfect _ _ p) = notZero p
    failAll _ notOne _ (PlusOne _ _ p _) = notOne p
    failAll _ _ notMinusOne (MinusOne _ _ p _) = notMinusOne p



-- A solution for the amount of projects n is the grouping number x AND the proof it works
Solution : Nat -> Type
Solution n = (x : Nat ** Fair n x)

findAllSolutions : (n : Nat) -> List (Solution n)
findAllSolutions n = 
  let
    try : (x : Nat) -> List (Solution n)
    try x = case checkRule n x of
              Yes prf => [(x ** prf)]
              No _    => []
  in
    try 3 ++ try 4 ++ try 5


isFair' : Nat -> Nat -> Bool
isFair' n x = case checkRule n x of
    Yes _ => True
    No  _ => False

isFair : Nat -> Bool
isFair n = any (isFair' n) grp

unfairNumbers : List Nat
unfairNumbers = filter (not . isFair) [0..60]




