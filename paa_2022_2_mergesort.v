(* Projeto e Análise de Algoritmos 2022/2 - comentários *)

(** * Formalização da correção e complexidade do algoritmo [mergesort]  *)

(** Neste trabalho construiremos ... *)

(** ** O algoritmo mergesort *)
(* begin hide *)
Require Import List Arith Permutation. 
Require Import Recdef.
(* end hide *)

Definition len (p:list nat * list nat) := length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p} :=
  match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
  if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
  else hd2 :: merge (l1, tl2)
 end.
Proof.
  Admitted.
  
Function mergesort (l: list nat) {measure length l} :=
  match l with
  | nil => nil
  | h::nil => l
  | h::tl =>
    let n := length(l) / 2 in
     let l1 := firstn n l in
     let l2 := skipn n l in
     let sorted_l1 := mergesort(l1) in
     let sorted_l2 := mergesort(l2) in
     merge (sorted_l1, sorted_l2)
  end.
Proof.
  Admitted. (* Defined *)

(** * A correção de [mergesort] *)

Inductive sorted :list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x::nil)
| sorted_many: forall x y l, x <=y -> sorted (y::l) -> sorted (x::y::l).

Theorem mergesort_correct: forall l, sorted (mergesort l) /\ Permutation l (mergesort l).
Proof.
 Admitted.  

(** * A complexidade do pior caso de [mergesort] *)

 Function T_merge (p: list nat * list nat) {measure len p} : nat :=
  match p with
  | (nil, l2) => 0
  | (l1, nil) => 0
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
    if hd1 <=? hd2 then S(T_merge (tl1, l2))
    else S(T_merge (l1, tl2))
  end.
 Proof.
 Admitted.

  Function T_mergesort (l: list nat) {measure length l} : nat :=
  match l with
  | nil => 0
  | hd :: nil => 0
  | hd :: tl =>
    let n := length(l) / 2 in
    let l1 := firstn n l in
    let l2 := skipn n l in
    T_mergesort(l1) + T_mergesort(l2) + T_merge (mergesort l1, mergesort l2)
  end.
  Proof.
Admitted.  

Theorem T_mergesort_complexity_wc: forall l k, length l = 2^k -> T_mergesort l <= k * 2^k.
Proof.
  Admitted.
