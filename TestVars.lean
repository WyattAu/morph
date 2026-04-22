import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem

namespace Test

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Step
open Morph.Specs.TypeSystem
open HasType

-- Test: how many vars does cases introduce for each constructor?
theorem test : forall {e : Expr} {tau : Typ} {Gamma : TypEnv},
    HasType Gamma e tau -> True := by
  intro e tau Gamma hType
  cases hType with
  | var_type =>
    rename_i h
    trivial
  | lit_int => trivial
  | lit_bool => trivial
  | lit_string => trivial
  | lit_unit => trivial
  | lit_pointer => trivial
  | unop_not =>
    rename_i h
    trivial
  | unop_notb =>
    rename_i h
    trivial
  | binop_arith =>
    rename_i h1 h2 h3
    trivial
  | binop_comp =>
    rename_i h1 h2 h3
    trivial
  | binop_logic =>
    rename_i h1 h2 h3
    trivial
  | binop_bitwise =>
    rename_i h1 h2 h3
    trivial
  | lam_type =>
    rename_i h
    trivial
  | app_type =>
    rename_i h1 h2
    trivial
  | let_type =>
    rename_i h1 h2
    trivial
  | if_type =>
    rename_i h1 h2 h3
    trivial
  | for_type =>
    rename_i h1 h2 h3
    trivial
  | block_type =>
    rename_i h
    trivial

end Test
