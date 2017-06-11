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
Require Import Compare_dec.
Require Import Omega.
Require Import Types.
Require Import Envs.

Axiom validAddressRange : 0 < baseAddress <= maxAddress.

Axiom validAccessMemMeta__validStoreMemMeta : forall m l v,
  (exists v, accessMemMeta m l = Some v) <-> (exists m', storeMemMeta m l v = Some m').

Axiom validAccessMemMeta__validAccessMem : forall m l,
  (exists v, accessMemMeta m l = Some v) <-> (exists v, accessMem m l= Some v).

Axiom validStoreMemMeta__validStoreMem : forall m l v1 v2,
  (exists m', storeMemMeta m l v1 = Some m') <-> (exists m', storeMem m l v2= Some m').

Axiom validAccessMemMeta__validStoreMem : forall m l v,
  (exists v, accessMemMeta m l = Some v) <-> (exists m', storeMem m l v= Some m').

Axiom validStoreMemMeta__validAccessMem : forall m l v,
  (exists m', storeMemMeta m l v = Some m') <-> (exists v, accessMem m l = Some v).

Axiom accessMemMeta_uniqBehavior : forall v m l v',
  (accessMemMeta m l = Some v -> accessMemMeta m l = Some v' -> v = v') /\
  (accessMemMeta m l = None -> accessMemMeta m l = None).

Axiom accessMem_uniqBehavior : forall v m l v',
  (accessMem m l = Some v -> accessMem m l = Some v' -> v = v') /\
  (accessMem m l = None -> accessMem m l = None).

Axiom storeMemMeta_uniqBehavior : forall v m l v',
  ((exists m', storeMemMeta m l v = Some m') -> (exists m', storeMemMeta m l v' = Some m')) /\
  (storeMemMeta m l v = None -> storeMemMeta m l v' = None).

Axiom storeMem_uniqBehavior : forall v m l v',
  ((exists m', storeMem m l v = Some m') -> (exists m', storeMem m l v' = Some m')) /\
  (storeMem m l v = None -> storeMem m l v' = None).

Axiom updateNonTameTypeInfo_inversion : forall TI loc p size n TI' q,
  wf_AType (A_Pointer p q) ->
  sizeOfPType p = Some size -> 
  size > 0 ->
  updateTypeInfo TI loc p n = TI' ->
  q <> Tame ->
  (forall l, 
    l < loc \/ l >= loc + n -> TI l = TI' l
  ) /\
  (forall l, 
    loc <= l < loc + n -> 
    (exists j, mmod l loc size = Some j /\ optionAtypeEqual (Some (TI' l)) (getNthPType p j))
  ).

Axiom updateTameTypeInfo_inversion : forall TI loc p n TI',
  wf_AType (A_Pointer p Tame) ->
  updateTypeInfo TI loc p n = TI' ->
  (forall l, 
    l < loc \/ l >= loc + n -> TI l = TI' l
  ) /\
  (forall l, 
    loc <= l < loc + n -> atypeEqual (TI' l) (A_Pointer P_VoidPtr Tame)
  ).

Axiom malloc__inversion : forall E n M' S' TI' loc,
  malloc E n = Some ((MkEnv M' S' TI'), loc) ->
  exists M, exists TI, E = MkEnv M S' TI /\                                                                         (*stack is unchanged*)   
  (baseAddress<=loc /\ loc+ n < maxAddress /\ n > 0) /\
  (forall l v, 
    accessMemMeta M l = Some v -> accessMemMeta M' l = Some v
  ) /\                                                                                                              (*existed valid data in mem are still valid*)
  (forall l, 
    l < loc \/ l >= loc + n -> 
    accessMemMeta M l = None -> accessMemMeta M' l = None
    ) /\                                                                                                            (*existed unvalid data in mem are still unvalid if it is not allocated*)
  (forall l, 
    loc <= l < loc + n -> accessMemMeta M l = None
  ) /\                                                                                                              (*allocated data are valid*)
  (forall l, 
    loc <= l < loc + n -> 
    accessMemMeta M' l = Some (0, (0, 0))
  ) /\                                                                                                              (*allocated data are valid*)
  (forall l, 
    l < loc \/ l >= loc + n -> atypeEqual (TI' l) (TI l)
    ) /\                                                                                                            (*type info is unchanged if it is not allocated*)
  (forall l, 
    loc <= l < loc + n -> atypeEqual (TI' l) A_Int
  ).                                                                                                                (*type info is INT if it is allocated*)

Axiom storeMemMeta__inversion : forall M loc d M',
  storeMemMeta M loc d = Some M' ->
  accessMemMeta M' loc = Some d /\
  (forall l v, 
    l <> loc ->
    accessMemMeta M l = Some v -> 
    accessMemMeta M' l = Some v
  ) /\                                                                                                              (*existed valid data in mem are still valid*)
  (forall l, 
    accessMemMeta M l = None -> 
    accessMemMeta M' l = None
  )                                                                                                                 (*existed unvalid data in mem are still unvalid if it is not allocated*)
  .
Axiom storeMem__inversion : forall M loc d v be M',
  storeMem M loc d = Some M' ->
  accessMemMeta M loc = Some (v, be) ->
  accessMemMeta M' loc = Some (d, be) /\
  (forall l v, 
    l <> loc ->
    accessMemMeta M l = Some v -> 
    accessMemMeta M' l = Some v
  ) /\                                                                                                              (*existed valid data in mem are still valid*)
  (forall l, 
    accessMemMeta M l = None -> 
    accessMemMeta M' l = None
  )                                                                                                                 (*existed unvalid data in mem are still unvalid if it is not allocated*)
  .

