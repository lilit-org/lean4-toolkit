import src.definitions.TypeClasses

/-!
##
## this file demonstrates various examples of using the doublable type class
##
-/

-- basic list doubling
#eval Doublable.double [1, 2, 3]  -- should output [2, 4, 6]

-- empty list
#eval Doublable.double ([] : List Nat)  -- empty list

-- single element list
#eval Doublable.double [5]  -- single element list

-- nested lists
#eval Doublable.double [[1, 2], [3, 4]]  -- nested lists

-- list with repeated elements
#eval Doublable.double [0, 0, 0]  -- list with repeated elements

-- larger numbers
#eval Doublable.double [1000, 2000, 3000]  -- larger numbers

-- map and append examples
#eval List.map (· + 1) ([1, 2] ++ [3, 4])  -- [2, 3, 4, 5]
#eval List.map (· + 1) [1, 2] ++ List.map (· + 1) [3, 4]  -- [2, 3, 4, 5]
#eval List.map (· * 2) ([1, 2] ++ [3, 4])  -- [2, 4, 6, 8]
#eval List.map (· * 2) [1, 2] ++ List.map (· * 2) [3, 4]  -- [2, 4, 6, 8]

-- double vs map examples
#eval Doublable.double [1, 2, 3]  -- [2, 4, 6]
#eval List.map Doublable.double [1, 2, 3]  -- [2, 4, 6]
#eval Doublable.double [[1, 2], [3, 4]]  -- [[2, 4], [6, 8]]
#eval List.map Doublable.double [[1, 2], [3, 4]]  -- [[2, 4], [6, 8]]
