import Data.List
import Data.String
import Debug.Trace
import System.File.ReadWrite

Room : Type
Room = String

Project : Type
Project = String

Day : Type
Day = Nat

partial
error : String -> a
error msg = idris_crash msg

even : (n : Nat) -> Bool 
even 0 = True
even (S k) = not (even k)

odd : (n : Nat) -> Bool 
odd n = not (even n)

-- use :exec main or latex

partial
unsafeTail : List a -> List a
unsafeTail [] = error "empty list"
unsafeTail (x::xs) = xs


record Professor where
  constructor MkProf
  profName : String
  unavailableDays : List Day
  availableDays : List Day
  projects : List Project

Eq Professor where
  (MkProf n1 u1 a1 p1) == (MkProf n2 u2 a2 p2) =
    n1 == n2 && u1 == u2 && a1 == a2 && p1 == p2

Ord Professor where
  compare (MkProf n1 u1 a1 p1) (MkProf n2 u2 a2 p2) =
    compare n1 n2

Show Professor where
  show p = profName p

record Presentation where
  constructor MkPres
  room : Room
  day : Day
  project : Project
  professor : Professor

Eq Presentation where
  (MkPres r1 d1 p1 prof1) == (MkPres r2 d2 p2 prof2) =
    r1 == r2 && d1 == d2 && p1 == p2 && prof1 == prof2

prettyPrint : Presentation -> String
prettyPrint p = "Presentation:\n" ++
                "  Room: " ++ room p ++
                "  Day: " ++ show (day p) ++
                "  Project: " ++ project p ++
                "  Professor: " ++ profName (professor p) ++ "\n"

detailedPrint : Presentation -> String
detailedPrint p = "Presentation {room = " ++ show (room p) ++
                  ", day = " ++ show (day p) ++
                  ", project = " ++ show (project p) ++
                  ", professor = " ++ show (professor p) ++ "}"

Show Presentation where
  show = prettyPrint

Ord Presentation where
  compare p1 p2 =
       compare (day p1, room p1, professor p1, project p1)
               (day p2, room p2, professor p2, project p2)


{-
Prelude.take : Nat -> Stream a -> List a
take 0 xs = []
take (S k) (x :: xs) = x :: take k (Force xs)

partial
(!!) : List a -> Nat -> a
(!!) xs i = 
  case integerToFin (cast i) (length xs) of
    Nothing => error "index too large"
    Just id => Data.List.index (finToNat id) xs
 -}

partial
unsafeHead : List a -> a
unsafeHead [] = error "Prelude.head: empty list"
unsafeHead (x::xs) = x

{-
using Maybe is prob better

headMaybe : List a -> Maybe a
headMaybe []      = Nothing
headMaybe (x :: _) = Just x

tailMaybe : List a -> Maybe (List a)
tailMaybe []       = Nothing
tailMaybe (x :: xs) = Just xs

lastMaybe : List a -> Maybe a
lastMaybe []        = Nothing
lastMaybe (x :: []) = Just x
lastMaybe (_ :: xs)  = lastMaybe xs

initMaybe : List a -> Maybe (List a)
initMaybe [] = Nothing
initMaybe (x :: xs) = case initMaybe xs of
    Nothing => Just []
    Just ys => Just (x :: ys)
 -}





notElem : Eq a => a -> List a -> Bool
notElem x xs = not (elem x xs)


-- ( n, x, n%x, x - (n%x) )
fairRestDebug : Int -> List (Int, Int, Int, Int)
fairRestDebug n = modResults
  where
    modResult x = (n, x, n `mod` x, x - (n `mod` x))
    modResults = map modResult [5,4,3]

unfairNumbers : List Int
unfairNumbers = [n | n <- [0..60], isUnfair (fairRestDebug n)]
  where
    isUnfair : List (Int, Int, Int, Int) -> Bool
    isUnfair rests =  
      -- compiler wants added brackets around notElem expressions to resolve non-associativity?
      (any (\(_, x, _, rDiff) => x == 3 && rDiff == 1) rests &&
       any (\(_, x, r, rDiff) => x == 4 && (r `notElem` [0, 1]) && (rDiff `notElem` [0, 1])) rests &&
       any (\(_, x, r, rDiff) => x == 5 && (r `notElem` [0, 1]) && (rDiff `notElem` [0, 1])) rests)
      || 
      (any (\(_, x, r, _) => x == 5 && r == 1) rests && 
       any (\(_, x, r, rDiff) => x == 4 && (r `notElem` [0, 1]) && (rDiff `notElem` [0, 1])) rests &&
       any (\(_, x, r, rDiff) => x == 3 && (r `notElem` [0, 1]) && (rDiff `notElem` [0, 1])) rests)
      || 
      (any (\(_, x, diff, _) => x == 5 && diff == 1) rests && 
       any (\(_, x, _, rDiff) => x == 3 && rDiff == 1) rests &&
       any (\(_, x, r, rDiff) => x == 4 && (r `notElem` [0, 1]) && (rDiff `notElem` [0, 1])) rests)

-- amount of presentations -> fair grouping

-- 3. rules
-- n mod 
partial
fairRest : Int -> Int
fairRest n =
  if n < 6 then n
  else if n `elem` unfairNumbers then 3
  else if not (null zeroRest)    then unsafeHead zeroRest
  else if not (null oneRest)     then findFair 5 oneRest    oneRestDif
  else if not (null oneRestDif)  then findFair 3 oneRestDif oneRest
  else error "critical math error in fairRest"
  where
    modResult x = (x, n `mod` x, x - (n `mod` x))
    modResults  = map modResult [5,4,3] 

    -- idris needs this type declaration?
    first,second,third : (Int, Int, Int) -> Int
    first  (x, _, _) = x    
    second (_, x, _) = x
    third  (_, _, x) = x
    
    zeroRest   = [first x | x <- modResults, second x == 0]
    oneRest    = [x       | x <- modResults, second x == 1]    
    oneRestDif = [x       | x <- modResults, third  x == 1]
    
    -- finds fairest grouping value
    -- rewritten from haskell logic so (!!) is not needed
    -- idris has index, its called index
    findFair : Int -> List (Int, Int, Int) -> List (Int, Int, Int) -> Int
    findFair grp (val1 :: rest) y =
      if first val1 == grp 
         then case rest of
                (val2 :: _) => first val2
                []          => first (unsafeHead y)
         else first val1

-- split a list into n groups
partial
splitIntoGroups : Int -> List a -> List (List a)
splitIntoGroups _ [] = []
splitIntoGroups n xs =
  if (cast (length xs)) == n+1 then [xs]
  else if n > 0 then take (cast n) xs :: splitIntoGroups n (drop (cast n) xs)
  else []

-- choose n from [a] without repeats
combinations : Eq a => Int -> List a -> List (List a)
combinations 0 _  = [[]]
combinations _ [] = []
combinations n (x::xs) = [x::ys | ys <- combinations (n-1) (filter (/= x) xs)] ++ combinations n xs

-- Rules for filtering when combining
filterPresentations : Presentation -> List Presentation -> List Presentation
filterPresentations x = filter (\p => (professor p, project p) /= (professor x, project x)
                                    && (room p, day p) /= (room x, day x)
                                    && (professor p, day p) /= (professor x, day x))

combinationsP : Int -> List Presentation -> List (List Presentation)
combinationsP 0 _  = [[]]
combinationsP _ [] = []
combinationsP n (x::xs) = [x::ys | ys <- combinationsP (n-1) (filterPresentations x xs)] ++ combinationsP n xs


-- stub
-- TODO: Day 1: "01", Day 2: "02"
uniHolidays : Day -> Day -> List Day
uniHolidays start end = [4,29]

data DayOfWeek = Thursday | AddRest

Eq DayOfWeek where 
  (==) Thursday Thursday = True
  (==) _ _               = False 

dayOfWeek : Day -> DayOfWeek
dayOfWeek _ = Thursday

-- TODO: date range [start..end]
dateRange : Day -> Day -> List Day
dateRange start end = [day | day <- [start..end]] 

comparePresentationsByRoom : Presentation -> Presentation -> Ordering
comparePresentationsByRoom p1 p2 =
  compare  (room p1, day p1, professor p1, project p1)
           (room p2, day p2, professor p2, project p2)


sortByRoom : List Presentation -> List Presentation
sortByRoom = sortBy comparePresentationsByRoom


partial
generateSchedules : List Room -> Nat -> Nat -> List Professor -> List (List (List Presentation))
generateSchedules rooms startDay endDay professors = groups
  where
    projectsLen : Int
    projectsLen = cast (sum (map (length . projects) professors))

    days = [d | d <- dateRange startDay endDay, 
                dayOfWeek d == Thursday, 
                notElem d (uniHolidays startDay endDay)]
    
    -- generate all possible presentations
    presentations = [MkPres room day proj prof | day <- days,
                                                       room <- rooms,
                                                       prof <- professors,
                                                       (null (availableDays prof) && notElem day (unavailableDays prof)) ||
                                                       (null (unavailableDays prof) && elem day (availableDays prof)),
                                                       proj <- projects prof]

    groups : List (List (List Presentation))
    groups =
      if cast (length days) * cast (length rooms) < projectsLen 
      then error "not enough possible dates or rooms for scheduling"
      else map (\g => splitIntoGroups (fairRest projectsLen) (sortByRoom g)) (combinationsP projectsLen presentations)


{- readDay : Nat -> Day
readDay s = s 

readDays: List Nat -> List Day
readDays []      = []
readDays (x::xs) = readDay x :: readDays xs -}



hasUniqueProjectProf : List Presentation -> Bool
hasUniqueProjectProf presList = length (nub $ map (\p => (professor p, project p)) presList) == length presList

hasUniqueDaysRooms : List Presentation -> Bool
hasUniqueDaysRooms presList = length (nub $ map (\p => (day p, room p)) presList) == length presList

hasUniqueDaysProf : List Presentation -> Bool
hasUniqueDaysProf presList = length (nub $ map (\p => (professor p, day p)) presList) == length presList

partial
addProfessor : Professor -> List Room -> Nat -> Nat -> List (List Presentation) -> List (List (List Presentation))
addProfessor prof rooms startDay endDay oldPresentations =
  if null newGroups
  then error "Cannot add a new professor with the existing presentation list."
  else map (\grp => splitIntoGroups (fairRest projectsLen) (sortByRoom grp)) newGroups
  where
    oldPresentationsFlat = concat oldPresentations
    
    projectsLen : Int
    projectsLen = cast (length oldPresentationsFlat) + cast (length (projects prof))
    
    days = [d | d <- dateRange startDay endDay, 
                dayOfWeek d == Thursday, 
                notElem d (uniHolidays ( startDay) ( endDay))]
    
    newPresentations = [MkPres room day proj prof
                         | day <- days,
                           (null (availableDays prof) && notElem day (unavailableDays prof)) ||
                           (null (unavailableDays prof) && elem day (availableDays prof)),
                           room <- rooms,
                           proj <- projects prof]

    newGroups = [oldPresentationsFlat ++ newPres
                         | newPres <- combinationsP (cast (length (projects prof))) newPresentations,
                           hasUniqueDaysRooms (oldPresentationsFlat ++ newPres),
                           hasUniqueDaysProf  (oldPresentationsFlat ++ newPres),
                           hasUniqueProjectProf (oldPresentationsFlat ++ newPres)]

partial
addProfUnavailability : Professor -> List Nat -> List Room -> Nat -> Nat -> List (List Presentation) -> List (List (List Presentation))
addProfUnavailability prof unavailables rooms startDay endDay oldPresentations =
  if null newGroups
  then error "Cannot add new unavailability for professor."
  else newGroups
  where
    oldPresentationsFlat = concat oldPresentations
    
    updatedProf : Professor
    updatedProf = record { unavailableDays = unavailables ++ unavailableDays prof } prof
    
    updatedPresentations = filter (\pres => professor pres /= prof) oldPresentationsFlat
    
    newGroups = addProfessor updatedProf rooms startDay endDay [updatedPresentations]

countRoom : List Presentation -> Room -> Int
countRoom presentations r = cast $ length $ filter (\p => room p == r) presentations

-- Filters according to the rules above findEven
partial
checkEven : List (List Presentation) -> List Room -> Bool
checkEven presentations rooms =
  if even (cast (length presentations)) then all (\group => length (nub (map room group)) == 1) presentations
  else if even projectsLen              then all (== unsafeHead countRooms) (unsafeTail countRooms)
  else if odd projectsLen               then all (\x => all (\y => abs (x - y) <= 1) countRooms) countRooms
  else error "unaccounted for amount of rooms and or presenations"
  where
    projectsLen = length $ concat presentations    
    countRooms  = map (countRoom (concat presentations)) rooms 

partial
findEven : List (List (List Presentation)) -> List Room -> List (List (List Presentation))
findEven presentations rooms =
  if projectsLen <= 5 then filter (\group => length (nub (map room (concat group))) == 1) presentations 
  else filter (`checkEven` rooms) presentations
  where
    projectsLen = length (concat $ unsafeHead presentations)


-- stub
formatDay : Day -> String
formatDay d = show d

formatPresentation : Presentation -> String
formatPresentation p =
  "\t" ++ formatDay (day p) ++ " & " ++ project p ++ " & " ++ profName (professor p) ++ " & " ++ room p ++ "\\\\" ++ "\n"

formatGroup : Int -> List Presentation -> String
formatGroup _ [] = ""
formatGroup i ps =
  "\\begin{minipage}{\\textwidth}\\noindent \\textbf{Vortragsgruppe S" ++ show i ++ "}" ++ "\\\\" ++ "\n" ++
  "Beginn: " ++ "14:00" ++ "\\\\" ++ "\n" ++
  "\\begin{tabular}{@{}p{2cm}p{3cm}p{5cm}p{1cm}}" ++ "\n" ++ "\t" ++
  "Datum & Projektgruppe & Dozent/in & Raum\\\\" ++ "\n" ++
  concatMap formatPresentation ps ++
  "\\end{tabular}" ++ "\n" ++ "\\end{minipage}" ++ "\n" ++ "\\\\\\\\"

-- Literal conversion of generateLaTeX
generateLaTeX : List (List Presentation) -> String
generateLaTeX presentations = 
  unlines (header ++ zipWith formatGroup [1..(cast (length presentations))] presentations ++ footer)
  where
    header : List String
    header =
      ["\\documentclass[a4paper]{article}",
       "\\usepackage{geometry}",
       "\\geometry{a4paper, margin=1in}",
       "\\usepackage[ngerman]{babel}",
       "\\usepackage{titling}",
       "\\usepackage{fancyhdr}",
       "\\pagestyle{fancy}",
       "\\fancyhf{}",
       "\\renewcommand{\\headrulewidth}{0pt}",
       "\\rhead{Stand: \\today}",
       "\\lhead{\\thetitle}",
       "\\title{IT-Projekte XxXx 20YY}",
       "\\begin{document}"
      ]
    footer : List String
    footer = ["\\end{document}"]


partial
unsafeLast : List a -> a
unsafeLast [] = error "Prelude.last: empty list"
unsafeLast [x] = x
unsafeLast (x::xs) = unsafeLast xs


partial
unsafeInit : List a -> List a
unsafeInit [] = error "Prelude.init: empty list"
unsafeInit [x] = []
unsafeInit (x::xs) = x :: unsafeInit xs


partial -- needs partial or woudlnt compile since not covering
groupLengths : List (List Int) -> (Int, Int)
groupLengths groups = 
  (cast (length (unsafeLast (unsafeInit groups))), cast (length (unsafeLast groups)))

partial
splitIntoFairGroups : Int -> List (List Int)
splitIntoFairGroups m = splitIntoGroups (fairRest m) [1..m]

partial
checkFairRest : List (Int, Int)
checkFairRest = map (groupLengths . splitIntoFairGroups) [6..60]



calculateFairRests : Int -> List (Int, Int, Int)
calculateFairRests n = [(x, n `mod` x, x - n `mod` x) | x <- [3..5]]

plotFairRest : List (Int, List (Int, Int, Int))
plotFairRest = [(n, calculateFairRests n) | n <- [1..60]]


p1 : Professor
p1 = MkProf 
  "Professor 1" 
  [ 1, 4,  11,  25] 
  [] 
  ["Project 1"]

p2 : Professor
p2 = MkProf 
  "Professor 2" 
  [2, 28] 
  [] 
  ["Project 2"]

p3 : Professor
p3 = MkProf 
  "Professor 3" 
  [ 11,  25] 
  [] 
  ["Project 3"]

p4 : Professor
p4 = MkProf 
  "Professor 4" 
  [ 4,  18,  25] 
  [] 
  ["Project 4"]

p5 : Professor
p5 = MkProf 
  "Professor 5" 
  [ 18] 
  [] 
  ["Project 5"]


partial
main : IO ()
main = do 
       the (IO ()) (traverse_ (putStrLn . show) ((generateSchedules ["H","Q"] 1 2 [p1,p2])))


partial
latex : IO ()
latex = do
  let schedule = unsafeHead $ take 1 $ generateSchedules ["H","Q"] 1 2 [p1,p2]
  let content = generateLaTeX schedule
  result <- writeFile "presentations.tex" content
  case result of
       Left err => putStrLn "Error: Could not write file."
       Right _  => putStrLn "Success: presentations.tex written."