Require Import Arith.
Require Import List.
Require Import ZArith.
Import ListNotations.

Inductive InputVar: Set :=
| input: nat -> InputVar.

Inductive WitnessVar: Set :=
| witness: nat -> WitnessVar.

Inductive ConstantVar: Set :=
| constrant: nat -> nat -> ConstantVar.

Definition Inputs := list InputVar.

Definition Witness := list WitnessVar.

Definition Constants := list ConstantVar.

(*
 * For a simple circuit:
 *     a + b - c = 0    
 *     c * d - e = 0 
 * we can build the following gates:
 *  ----------------------------------------------------------------
 *  |  advise  | advise  | advise  | selector(add) |  selector(mul) |
 *  ----------------------------------------------------------------
 *  |   a      |    b    |   c     |   1           |                |
 *  -----------------------------------------------------------------
 *  |   c      |    d    |   e     |   0           |   1            |
 *  ----------------------------------------------------------------
 *  with a implicit constraints:  
 *         column[2][0] = column[0][1]
 *
 *)

Inductive Column :=
| INSTANCE: Inputs -> Column
| ADVISE: Witness -> Column
| FIXED: Constants -> Column.

Local Open Scope Z_scope.

Inductive Rotation :=
| CUR | NEXT | PREV.

Inductive ColumnCursor :=
| COLUMN_CURSOR: Column -> nat -> Rotation -> ColumnCursor.

Inductive Constraints :=
| APlus: Constraints -> Constraints -> Constraints
| AMinus:  Constraints -> Constraints -> Constraints
| AMul: Constraints -> Constraints -> Constraints
| CTOM: ColumnCursor  -> Constraints
| FTOM: ConstantVar -> Constraints.


Definition Lookup := list (InputVar * Z).


Inductive Assignment :=
| ASSIGNMENT: InputVar -> Z -> option Lookup -> Assignment.

Class Gate { T: Type} { F: Type} :=
  {
    col: list Column;
    cons: Constraints;
    ass: list Assignment
  }.