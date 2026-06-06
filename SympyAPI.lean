import Lean

open Lean Elab Command Term Meta

/-- Run a python script and return its stdout -/
def runPython (script : String) : IO String := do
  let out ← IO.Process.output {
    cmd := "python3"
    args := #["-c", script]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"Python script failed: {out.stderr}"
  
  let stdout := out.stdout
  if stdout.endsWith "\n" then
    return stdout.dropRight 1
  else
    return stdout

/-- 
  A command macro that runs SymPy live during Lean's compilation.
  It takes a python script string and an expected output string.
  If SymPy returns the expected string, compilation proceeds.
  If not, compilation fails.
-/
elab "verify_sympy_limit " script:str expected:str : command => do
  let scriptStr := script.getString
  let expectedStr := expected.getString
  let pyResult ← IO.ofExcept <| ← (runPython scriptStr).toBaseIO
  
  if pyResult != expectedStr then
    throwError m!"SymPy verification failed.\nExpected: {expectedStr}\nGot: {pyResult}"
  
  logInfo m!"SymPy live verification successful: {pyResult}"
