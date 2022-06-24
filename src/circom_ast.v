Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.
(* From LF Require Import Maps.
Import ListNotations. *)


(* 
Circom is a novel domain-specific language for defining arithmetic circuits that can be  be used to generate zero-knowledge proof.

template Multipier() {
  signal private input a;
  signal private input b;
  signal output c;
  c <== a * b;
}

component main = Mutipier();
 *)
(*
Inductive TypeReduction :=
| CVariable | Component | Signal.

Class TypeKnowledge := 
{ 
  reducesto: option TypeReduction
}.
*)

Inductive AssignOp :=
| AssignVar | AssignSignal | AssignConstraintSignal.

Inductive ExpressionInfixOpcode :=
| Mul | Div | Add | Sub
| Pow | IntDiv | Mod | ShiftL
| ShiftR | LesserEq | GreaterEq
| Lesser | Greater | Eq
| NotEq | BoolOr | BoolAnd | BitOr
| BitAnd | BitXor.

Inductive ExpressionPrefixOpcode :=
| PreSub | BoolNot | Complement.

Inductive Access :=
| PRIVATE | PUBLIC.

Inductive Expression :=
| InfixOp (lhe: Expression) (infix_op: ExpressionInfixOpcode) (rhe: Expression)
| PrefixOp (prefix_op: ExpressionPrefixOpcode) (rhe: Expression)
| InlineSwitchOp (cond: Expression) (if_true: Expression) (if_false: Expression)
| Variable_ (name: string) (access: Access)
| Number (num: Z)
| Call (id: string) (args: list Expression)
| ArrayInLine (values: list Expression).

Notation "x + y" := (InfixOp x Add y) (at level 50, left associativity).
Notation "x - y" := (InfixOp x Sub y) (at level 50, left associativity).
Notation "x * y" := (InfixOp x Mul y) (at level 40, left associativity).
Notation "x ** y" := (InfixOp x Pow y) (at level 40, left associativity).
Notation "x / y" := (InfixOp x Div y)  (at level 40, left associativity).
Notation "x <= y" := (InfixOp x LesserEq y) (at level 70, no associativity).
Notation "x >= y" := (InfixOp x GreaterEq y) (at level 70, no associativity).
Notation "x < y" := (InfixOp x Lesser y) (at level 70, no associativity).
Notation "x > y" := (InfixOp x Greater y) (at level 70, no associativity).
Notation "x == y" := (InfixOp x Eq y) (at level 70, no associativity).
Notation "x != y" := (InfixOp x NotEq y) (at level 70, no associativity).


Inductive SignalElementType :=
| Empty | Binary | FieldElement.

Inductive SignalType :=
| Output | Input | Intermediate.

Inductive SignalTyp :=
| signal_ele_t: SignalElementType -> SignalTyp
| signal_t : SignalType -> SignalTyp.

Inductive VariableType :=
| Var | Component | Signal (signal_typ: SignalTyp).

Inductive Statement:=
| IfThenElse (cond: Expression) (if_case: Statement) (else_case: option Statement)
| While (cond: Expression) (stmt: Statement)
| Return (value: Expression)
| InitializationBlock (xtype: VariableType) (Initialization: list Statement)
| Declaration (xtype: VariableType) (name: string) (dimensions: list Expression) (is_constant: bool)
| Substitution  (var: string) (access: list Access) (op: AssignOp) (rhe: Expression)
| ConstraintEquality (lhe: Expression) (rhe: Expression)
| LogCall (arg: Expression)
| Block (stmts: list Statement)
| Assert (arg: Expression).

Notation "x <== y" := (ConstraintEquality x y) (at level 60).
Notation "{| stmts |}" := (Block stmts) (at level 100).
(* Notation "'declare' ty name dim constant" := (Declaration ty name dim constant) (at level 100). *)
Notation "'#Signal' 'Input' s" := (Declaration (Signal (signal_t Input)) s [] false) (at level 100).
Notation "'#Signal' 'Output' s" := (Declaration (Signal (signal_t Output)) s [] false) (at level 100).

Inductive CircomDef :=
| Temp (name: string) (args: list string) (body: Statement) (parallel: bool)
| Func (name: string) (args: list string)  (body: Statement).

Module Example.

  (* Signal Input a[N] *)
  Definition st1: Statement := #Signal Input "a".
  Definition st2: Statement := #Signal Input "b".
  Definition st3: Statement := #Signal Output "c".
  Definition st4: Statement :=
     (Variable_ "c" PUBLIC) <== (Variable_ "a" PRIVATE) * (Variable_ "b" PRIVATE).

  Definition b1: Statement := {| [st1; st2; st3; st4] |}.
  
  Definition d1: CircomDef := Temp "Multipier" [] b1 false.

  Definition d2 :=
    Temp
      "Multipier" []
      ({|
        [
          Declaration (Signal (signal_t Input)) "a" [] false;
          Declaration (Signal (signal_t Input)) "b" [] false;
          Declaration (Signal (signal_t Output)) "c" [] false;
          (Variable_ "c" PUBLIC) <== (Variable_ "a" PRIVATE) * (Variable_ "b" PRIVATE)
        ]
      |})
      false.
End Example.