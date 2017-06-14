(************************************************************************************)
(* Copyright (c) 2009 Santosh Nagarakatte, Milo M. K. Martin. All rights reserved.  *)
(*                                                                                  *)
(* Developed by: Santosh Nagarakatte, Milo M.K. Martin,                             *)
(*               Jianzhou Zhao, Steve Zdancewic                                     *)
(*               Department of Computer and Information Sciences,                   *)
(*               University of Pennsylvania                                         *)
(*               http://www.cis.upenn.edu/acg/softbound/                            *)
(*                                                                                  *)
(* Permission is hereby granted, free of charge, to any person obtaining a copy     *)
(* of this software and associated documentation files (the "Software"), to         *)
(* deal with the Software without restriction, including without limitation the     *)
(* rights to use, copy, modify, merge, publish, distribute, sublicense, and/or      *)
(* sell copies of the Software, and to permit persons to whom the Software is       *)
(* furnished to do so, subject to the following conditions:                         *)
(*                                                                                  *)
(*   1. Redistributions of source code must retain the above copyright notice,      *)
(*      this list of conditions and the following disclaimers.                      *)
(*                                                                                  *)
(*   2. Redistributions in binary form must reproduce the above copyright           *)
(*      notice, this list of conditions and the following disclaimers in the        *)
(*      documentation and/or other materials provided with the distribution.        *)
(*                                                                                  *)
(*   3. Neither the names of Santosh Nagarakatte, Milo M. K. Martin,                *)
(*      Jianzhou Zhao, Steve Zdancewic, University of Pennsylvania, nor             *)
(*     the names of its contributors may be used to endorse or promote              *)
(*     products derived from this Software without specific prior                   *)
(*     written permission.                                                          *)
(*                                                                                  *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR       *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,         *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE     *)
(* CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER      *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING          *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS     *)
(* WITH THE SOFTWARE.                                                               *)
(************************************************************************************)

Require Import List.
Require Import EqNat.
Require Import Zdiv.
Require Import Compare_dec.
Require Import Types.

Set Implicit Arguments.

(******************************************************************)
(*                          Value                                 *)
(******************************************************************)
(* Value is the type of contents stored in Mem, 
   and addresses in Mem. *)
Definition Value := nat.

(******************************************************************)
(*                          Arch                                  *)
(******************************************************************)

(*
Memory is devided into three equivalent parts with size 'maxAddress'.
The 1st part is the common mem
The 2nd part is the mem storing the corresponding meta-data 'base'
The 3rd part is the mem storing the corresponding meta-data 'bound'
The offSet between each memory is 'maxAddress'
i.e.
Value = M(loc)
Base = M(loc+offSet)
Bound = M(loc+2*offSet)  where 0 <= loc < maxAddress
*)

Definition Loc := Value. (* the address of Mem *)
Parameter baseAddress : nat.    
Parameter maxAddress: nat.

(******************************************************************)
(*                          Heap                                  *)
(******************************************************************)
(* 
  We do not define Heap explictly. Insteadly, the abstract
  interfaces of memory management and the corresponding
  axioms are defined. Any implemenatation satisfying these
  properties are good design.
*)

(******************************************************************)
(*                          Stack                                 *)
(******************************************************************)
Definition Var := c_ident.                       (* named variables *)
Record Stack : Set := MkStack
  {  data : Var -> option (nat*AType) ;
      top : nat }.

Definition lookUpStack (S: Stack) (v: Var) : option (nat*AType) :=
  S.(data) v.

(* 
  assume no duplicated vars are in Stack,
  duplication should be handled by the concrete implemenation of
  Stack.(data).

  We do not check whether the data in stack are stored
  continuously. In the other words, it is OK if there are any
  padding between data.

  In our system, stack is kept unchanged during evaluation.
  So the wfStack property can hold as long as it is given
  in the beginning.

  It does not matter if any malicious codes overwrite the
  data in stack, because the information of Stack, such 
  as the top of stack, is stored in some register, which can
  not be touched by any bad codes.
*)
Definition wfStack (S: Stack) :Prop := 
  baseAddress <= S.(top) <= maxAddress /\ 
  (forall v loc t,                                                    (* any loc is within [top, maxAddress) *)
     lookUpStack S v = Some (loc, t) -> 
     S.(top) <= loc /\ loc + sizeOfAType t < maxAddress
  ) /\ 
  (forall v loc t,                                                    (* no vars are overlapped *)
     lookUpStack S v = Some (loc, t) -> 
     (forall v' loc' t', 
       lookUpStack S v' = Some (loc', t') ->
       loc' > loc + sizeOfAType t \/ loc > loc' + sizeOfAType t')
  ).

(******************************************************************)
(*                          Mem                                   *)
(******************************************************************)
Definition Mem := Loc -> Value.
Definition Base := Loc.
Definition Bound := Loc.
Definition Meta := (Base * Bound)%type.

(******************************************************************)
(*                          TypeInfo                              *)
(******************************************************************)
Definition TypeInfo := Loc -> AType.

(******************************************************************)
(*                          Env                                   *)
(******************************************************************)
Record Env : Set := MkEnv {  
  mem : Mem; 
  mem_unsafe : Mem;
  stack : Stack;
  typeInfo : TypeInfo }.

(******************************************************************)
(*                          Opt                                   *)
(******************************************************************)
Parameter newEnv : Env.
(*
  Runtime Data are data managed by the runtime system,
    such as the pre-loaded runtime library,
                  memo have not been allocated to users yet,
                  codes segment, system core, other system-protected data...
    which can not be read and written by user-program.
*)
(* reading Runtime Data can lead to bug *)
Parameter accessMemMeta : Mem -> Loc-> option (Value * Meta)%type.
Parameter accessMem : Mem -> Loc-> option Value.
(* writing Runtime Data can lead to bug *)
Parameter storeMemMeta : Mem -> Loc -> (Value * Meta)%type -> option Mem.
Parameter storeMem : Mem -> Loc -> Value -> option Mem.
(* e:Env->size:nat -> e':Env*addr:nat *)
Parameter malloc : Env -> Value -> option (Env*Base).
Definition copyMemMeta (mem:Mem) (src:Loc) (des:Loc) : option Mem :=
  match accessMemMeta mem src with 
  | Some vs => storeMemMeta mem des vs
  | None => None
  end.
Definition copyMem (mem:Mem) (src:Loc) (des:Loc) : option Mem :=
  match accessMemMeta mem src with 
  | Some (v, meta) => storeMem mem des v
  | None => None
  end.
(*  read the mem block [l ~ l+size-1]
     reading Runtime Data can lead to bug *)
Fixpoint accessMemMetaBlock (m:Mem) (l:Loc) (size:nat) :option (list (Value*Meta)) :=
  match size with 
  | O => Some nil
  | S size' => 
    match accessMemMeta m l with
    | Some v =>
      match accessMemMetaBlock m (S l) size' with
      | Some vs => Some (v::vs)
      | None => None
      end
    | None => None
    end
  end.
Fixpoint accessMemBlock (m:Mem) (l:Loc) (size:nat) :option (list Value) :=
  match size with 
  | O => Some nil
  | S size' => 
    match accessMem m l with
    | Some v =>
      match accessMemBlock m (S l) size' with
      | Some vs => Some (v::vs)
      | None => None
      end
    | None => None
    end
  end.
Fixpoint accessTypeInfoBlock (ti:TypeInfo) (l:Loc) (size:nat) :(list AType) :=
  match size with 
  | O => nil
  | S size' =>  (ti l)::(accessTypeInfoBlock ti (S l) size')
  end.
(*  write location [l ~ l+size-1] if it is defined
    writing Runtime Data can lead to bug *)
Fixpoint storeMemMetaBlock (m:Mem) (l:Loc) (vs: list (Value*Meta)) :(option Mem) :=
  match vs with 
  | nil => Some m
  | v::vs' => 
    match storeMemMeta m l v with
    | Some m' => storeMemMetaBlock m' (S l) vs'
    | None => None
    end
  end.
Fixpoint storeMemBlock (m:Mem) (l:Loc) (vs: list Value) :(option Mem) :=
  match vs with 
  | nil => Some m
  | v::vs' => 
    match storeMem m l v with
    | Some m' => storeMemBlock m' (S l) vs'
    | None => None
    end
  end.
Definition copyMemMetaBlock (mem:Mem) (src:Loc) (des:Loc) (size:nat) : option Mem :=
  match accessMemMetaBlock mem src size with 
  | Some vs => storeMemMetaBlock mem des vs
  | None => None
  end.
Definition copyMemBlock (mem:Mem) (src:Loc) (des:Loc) (size:nat) : option Mem :=
  match accessMemBlock mem src size with 
  | Some vs => storeMemBlock mem des vs
  | None => None
  end.

Parameter updateTypeInfo : TypeInfo -> Loc -> PType -> Value -> TypeInfo.


Definition validAddress (m:Mem) (l:Loc) :=
  (exists v, accessMemMeta m l = Some v) /\
  (forall v, exists m', storeMemMeta m l v = Some m').
Definition validAddresses (m:Mem) (l:Loc) (n:nat) : Prop :=
  (validAddress m l) /\
  (exists vs, accessMemMetaBlock m l n = Some vs) /\
  (forall (vs:list (Value*Meta)%type), length vs = n -> exists m', storeMemMetaBlock m l vs = Some m')
  .

Fixpoint equalTypeBlock (ti : TypeInfo) (l:Loc) (ts: list AType) : Prop :=
  match ts with 
  | nil => True
  | t::ts' => atypeEqual t (ti l) /\ equalTypeBlock ti (l+1) ts'
  end.
(*
  assume no duplicated locs are in Mem,
  even if any loc were duplicated, the first one works.

  if data in the common Mem are valid,
  then meta data are also valid.
*)
(* 
  tame and void ptr is untyped, it is ok not to check
*)
Definition wfData (M: Mem) (TI : TypeInfo) (d:Value*Meta) (t: AType): Prop :=
  match d with
  | (v, (b, e)) =>
    match t with 
    | A_Pointer p Tame =>
         (*
            in the case b=0, it doesnot need to check TI. Because the meta data
            implies this is not ptr type pointed to any valid location. At runtime,
            any deference on this value will be prevented by the runtime assertion
            that fails immdietely if b = 0.

            in the case b<>0, for any data with the in-bounds address (i.e., i \in
            [b, e)), the data the ptr points to, its type info can only be q* tame.
              it cannot be any q* safe/seq, because tame can not specify a safe or
              seq ptr, if wf_AType t.

              it cannot be int either. This follows by
              1) we assume the meta data of an int value that hasnt been casted into
                 any other type is (0,0). In the other words, in the very beginning
                 (before the program starts to run), the shadow space sets zeros for
                 all meta data of int. So if no cast occurs, b=0 which is not this case.
                 t cannot be any type rather than int, either.
              2) when casting int to any ptr types, the meta data is also set as zero,
                 although it might already be (0,0). When casting that ptr back to int,
                 its meta data isnt changed. So if any such casting chain occurs, b is
                 also 0 which is not this case.

              NOTE: casting does only change the type in the user-level, no changes
              occur on TI at all. There are only two possiblity to modify TI, malloc,
              and address-of, but what they changed are the unallocated mem. The TI
              of allocated mem is stable. Therefore, any casting chain from int to ptr
              has been disccussed in the above.
         *)
         (
           b <> 0 /\ b >= baseAddress /\ b <= e < maxAddress /\
           (forall i : nat, b <= i < e -> validAddress M i /\ exists q, atypeEqual (TI i) (A_Pointer q Tame))
         ) \/
         (b = 0) 
    | A_Pointer p Safe =>
         match p with 
         | P_AType t =>
           (
             (sizeOfAType t > 0) /\
             v >= baseAddress /\ v +sizeOfAType t < maxAddress /\
             (forall i : nat, 0 <= i < sizeOfAType t -> validAddress M (v+i) /\ atypeEqual (TI (v+i)) t)
            ) \/
            (v = 0)
         | P_Struct s => 
           (
             (sizeOfStruct s > 0) /\
             v >= baseAddress /\ v +sizeOfStruct s < maxAddress /\
             (forall i : nat, 0 <= i < sizeOfStruct s -> 
                     validAddress M (v+i) /\ optionAtypeEqual (Some (TI (v+i))) (getStructNthType s i)
             )
            ) \/
            (v = 0)
         | P_Name n =>
           (
             exists s, typeTable n = Some s /\
             (sizeOfStruct s > 0) /\
             v >= baseAddress /\ v +sizeOfStruct s < maxAddress /\
             (forall i : nat, 0 <= i < sizeOfStruct s -> 
                    validAddress M (v+i) /\ optionAtypeEqual (Some (TI (v+i))) (getStructNthType s i)
             )
            ) \/
            (v = 0)
         | P_Func => (* TODO *)
           (
            v >= baseAddress /\ v +1 < maxAddress 
           ) \/
           (v = 0)
         | P_VoidPtr => False (* because void* can only be Tame *)
         end
    | A_Pointer p Seq =>
         (
           b <> 0 /\ b >= baseAddress /\ b <= e < maxAddress /\ 
           (exists s, sizeOfPType p = Some s /\ s > 0 /\
           (forall i : nat, 
                    b <= i < e -> 
                    validAddress M i /\ 
                    (exists j, mmod i v s = Some j /\ optionAtypeEqual (Some (TI i)) (getNthPType p j))
           ))
         ) \/
         (b = 0) 
    | _ => True
    end
  end.

Fixpoint wfDatas (M: Mem) (TI : TypeInfo) (ds: list (Value*Meta)) (ts : list AType) {struct ds} : Prop :=
  match (ds, ts) with
  | (nil, nil) => True
  | (d::ds', t::ts') =>  wfData M TI d t /\ wfDatas M TI ds' ts'
  | _ => False
  end.

Definition wfMem (M: Mem) (TI : TypeInfo) :Prop := 
  (forall l, 
    match (accessMemMeta M l) with 
    | Some d => wfData M TI d (TI l)
    | _ => True
    end
   ).

Definition wfEnv (E:Env) : Prop := 
  wfMem E.(mem) E.(typeInfo) /\ 
  wfMem E.(mem_unsafe) E.(typeInfo) /\
  wfStack E.(stack) /\
  (forall v loc t,                                           (* data in Stack exists in Mem *)
    lookUpStack E.(stack) v = Some (loc, t) -> 
    validAddresses E.(mem) loc (sizeOfAType t) /\
    (forall i : nat, 0 <= i < sizeOfAType t -> atypeEqual (E.(typeInfo) (loc+i)) t)
  ).
