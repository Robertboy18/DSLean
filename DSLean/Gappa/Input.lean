/- The input language of Gappa: the `Gappa_input` grammar, from Lean propositions and real
expressions to Gappa's syntax. The `gappa` tactic (`DSLean.Gappa`) uses it; it lives in a module of
its own so that it can be used without the tactic. -/
import DSLean.Command
import Mathlib.Analysis.Real.Sqrt

set_option linter.unusedVariables false

external Gappa_input where
  "(" x "+" y ")" <== x + y
  "(" x "-" y ")" <== x - y
  "(" x "*" y ")" <== x * y
  "(" x "/" y ")" <== x / y
  "sqrt(" x ")" <== Real.sqrt x
  "-" x <== - (x:Real)
  "|" x "|" <== abs x

  "(" x "->" y ")" <== x → y
  "(" x "/\\" y ")" <== x ∧ y
  "(" x "\\/" y ")" <== x ∨ y
  "not" x <== ¬ x

  "[" x "," y "]" <== Set.Icc x y
  x "in" y <== x ∈ y
  x "=" y <== x = y
