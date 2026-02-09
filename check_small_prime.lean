import Erdos.KGe29
import Erdos.KLe28

open Erdos1094

def checkRange : IO Unit := do
  let mut foundException := false
  for k in [2:29] do
    -- We want to check if there exists n > 284 such that smallPrimeDivCheck n k = false.
    -- We'll check a range, say up to 10000.
    for n in [285:2000] do
      if !smallPrimeDivCheck n k then
        IO.println s!"Counterexample found: k={k}, n={n}"
        foundException := true
  if !foundException then
    IO.println "No counterexamples found in range [285, 2000] for k in [2, 28]."

#eval checkRange
