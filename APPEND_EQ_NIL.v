Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_EQ_NIL_term_abbrevs.
Require Import ADD_EQ_0_spec.
Require Import LENGTH_APPEND_spec.
Require Import LENGTH_EQ_NIL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1187296 {A : Type'} (l : list A) (h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (h1). Qed.
Lemma lem1187297 {A : Type'} (l : list A) (h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (SYM (@lem1187296 A l h1)). Qed.
Lemma lem1187298 {A : Type'} (l : list A) (h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (h1). Qed.
Lemma lem1187299 {A : Type'} (l : list A) (h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (SYM (@lem1187298 A l h1)). Qed.
Lemma lem1187300 {A : Type'} (l : list A) : (((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) = ((l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))).
Proof. exact (prop_ext (fun h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)) => @lem1187297 A l h1) (fun h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)) => @lem1187299 A l h1)). Qed.
Lemma lem1187301 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (fun_ext (fun l : list A => @lem1187300 A l)). Qed.
Lemma lem1187302 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187303 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (MK_COMB (@lem1187302 A) (@lem1187301 A)). Qed.
Lemma lem1187304 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem1187303 A) (@lem1117066 A)). Qed.
Lemma lem1187305 (m : nat) : term4 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem1187306 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1187307 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1187306 m) (@lem1187305 m)). Qed.
Lemma lem1187308 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1187307 m n). Qed.
Lemma lem1187309 (m : nat) (n : nat) : (term6 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term7 m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1187311 {A : Type'} (l : list A) : term8 A l.
Proof. exact (@lem1116558 A l). Qed.
Lemma lem1187312 {A : Type'} (l : list A) : (term8 A l) = (term9 A l).
Proof. exact (eq_refl (term8 A l)). Qed.
Lemma lem1187313 {A : Type'} (l : list A) : term9 A l.
Proof. exact (EQ_MP (@lem1187312 A l) (@lem1187311 A l)). Qed.
Lemma lem1187314 {A : Type'} (l : list A) (m : list A) : term10 A l m.
Proof. exact (@lem1187313 A l m). Qed.
Lemma lem1187315 {A : Type'} (l : list A) (m : list A) : (term10 A l m) = ((term11 A l m) = (term12 A l m)).
Proof. exact (eq_refl (term10 A l m)). Qed.
Lemma lem1187317 {A : Type'} (l : list A) : term13 A l.
Proof. exact (@lem1187304 A l). Qed.
Lemma lem1187318 {A : Type'} (l : list A) : (term13 A l) = ((l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))).
Proof. exact (eq_refl (term13 A l)). Qed.
Lemma lem1187331 {A : Type'} (l : list A) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1187318 A l) (@lem1187317 A l)). Qed.
Lemma lem1187332 {_27653 : Type'} (l : list _27653) : (l = (@nil _27653)) = ((@List.length _27653 l) = (NUMERAL 0)).
Proof. exact (@lem1187331 _27653 l). Qed.
Lemma lem1187333 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((@List.app _27653 l m) = (@nil _27653)) = ((term11 _27653 l m) = (NUMERAL 0)).
Proof. exact (@lem1187332 _27653 (@List.app _27653 l m)). Qed.
Lemma lem1187337 {A : Type'} (l : list A) (m : list A) : (term11 A l m) = (term12 A l m).
Proof. exact (EQ_MP (@lem1187315 A l m) (@lem1187314 A l m)). Qed.
Lemma lem1187338 {_27653 : Type'} (l : list _27653) (m : list _27653) : (term11 _27653 l m) = (term12 _27653 l m).
Proof. exact (@lem1187337 _27653 l m). Qed.
Lemma lem1187339 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1187340 {_27653 : Type'} (l : list _27653) (m : list _27653) : (term14 _27653 l m) = (term15 _27653 l m).
Proof. exact (MK_COMB (@lem1187339) (@lem1187338 _27653 l m)). Qed.
Lemma lem1187341 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1187342 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((term11 _27653 l m) = (NUMERAL 0)) = ((term12 _27653 l m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1187340 _27653 l m) (@lem1187341)). Qed.
Lemma lem1187344 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term7 m n).
Proof. exact (EQ_MP (@lem1187309 m n) (@lem1187308 m n)). Qed.
Lemma lem1187345 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((term12 _27653 l m) = (NUMERAL 0)) = (term16 _27653 l m).
Proof. exact (@lem1187344 (@List.length _27653 l) (@List.length _27653 m)). Qed.
Lemma lem1187352 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((term11 _27653 l m) = (NUMERAL 0)) = (term16 _27653 l m).
Proof. exact (TRANS (@lem1187342 _27653 l m) (@lem1187345 _27653 l m)). Qed.
Lemma lem1187353 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((@List.app _27653 l m) = (@nil _27653)) = (term16 _27653 l m).
Proof. exact (TRANS (@lem1187333 _27653 l m) (@lem1187352 _27653 l m)). Qed.
Lemma lem1187354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187355 {_27653 : Type'} (l : list _27653) (m : list _27653) : (term17 _27653 l m) = (term18 _27653 l m).
Proof. exact (MK_COMB (@lem1187354) (@lem1187353 _27653 l m)). Qed.
Lemma lem1187359 {A : Type'} (l : list A) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1187318 A l) (@lem1187317 A l)). Qed.
Lemma lem1187360 {_27653 : Type'} (l : list _27653) : (l = (@nil _27653)) = ((@List.length _27653 l) = (NUMERAL 0)).
Proof. exact (@lem1187359 _27653 l). Qed.
Lemma lem1187363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187364 {_27653 : Type'} (l : list _27653) : (term19 _27653 l) = (term20 _27653 l).
Proof. exact (MK_COMB (@lem1187363) (@lem1187360 _27653 l)). Qed.
Lemma lem1187366 {A : Type'} (l : list A) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1187318 A l) (@lem1187317 A l)). Qed.
Lemma lem1187367 {_27653 : Type'} (l : list _27653) : (l = (@nil _27653)) = ((@List.length _27653 l) = (NUMERAL 0)).
Proof. exact (@lem1187366 _27653 l). Qed.
Lemma lem1187368 {_27653 : Type'} (m : list _27653) : (m = (@nil _27653)) = ((@List.length _27653 m) = (NUMERAL 0)).
Proof. exact (@lem1187367 _27653 m). Qed.
Lemma lem1187371 {_27653 : Type'} (l : list _27653) (m : list _27653) : (term21 _27653 l m) = (term16 _27653 l m).
Proof. exact (MK_COMB (@lem1187364 _27653 l) (@lem1187368 _27653 m)). Qed.
Lemma lem1187374 {_27653 : Type'} (l : list _27653) (m : list _27653) : (((@List.app _27653 l m) = (@nil _27653)) = (term21 _27653 l m)) = ((term16 _27653 l m) = (term16 _27653 l m)).
Proof. exact (MK_COMB (@lem1187355 _27653 l m) (@lem1187371 _27653 l m)). Qed.
Lemma lem1187376 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1187377 (x : Prop) : (x = x) = True.
Proof. exact (@lem1187376 Prop x). Qed.
Lemma lem1187378 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((term16 _27653 l m) = (term16 _27653 l m)) = True.
Proof. exact (@lem1187377 (term16 _27653 l m)). Qed.
Lemma lem1187379 {_27653 : Type'} (l : list _27653) (m : list _27653) : (((@List.app _27653 l m) = (@nil _27653)) = (term21 _27653 l m)) = True.
Proof. exact (TRANS (@lem1187374 _27653 l m) (@lem1187378 _27653 l m)). Qed.
Lemma lem1187380 {_27653 : Type'} (l : list _27653) : (term22 _27653 l) = (term23 _27653).
Proof. exact (fun_ext (fun m : list _27653 => @lem1187379 _27653 l m)). Qed.
Lemma lem1187381 {_27653 : Type'} : (@all (list _27653)) = (@all (list _27653)).
Proof. exact (eq_refl (@all (list _27653))). Qed.
Lemma lem1187382 {_27653 : Type'} (l : list _27653) : (term24 _27653 l) = (term25 _27653).
Proof. exact (MK_COMB (@lem1187381 _27653) (@lem1187380 _27653 l)). Qed.
Lemma lem1187384 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1187385 {_27653 : Type'} (t : Prop) : (term27 _27653 t) = t.
Proof. exact (@lem1187384 (list _27653) t). Qed.
Lemma lem1187386 {_27653 : Type'} : (term25 _27653) = True.
Proof. exact (@lem1187385 _27653 True). Qed.
Lemma lem1187387 {_27653 : Type'} (l : list _27653) : (term24 _27653 l) = True.
Proof. exact (TRANS (@lem1187382 _27653 l) (@lem1187386 _27653)). Qed.
Lemma lem1187388 {_27653 : Type'} : (term28 _27653) = (term23 _27653).
Proof. exact (fun_ext (fun l : list _27653 => @lem1187387 _27653 l)). Qed.
Lemma lem1187389 {_27653 : Type'} : (@all (list _27653)) = (@all (list _27653)).
Proof. exact (eq_refl (@all (list _27653))). Qed.
Lemma lem1187390 {_27653 : Type'} : (term29 _27653) = (term25 _27653).
Proof. exact (MK_COMB (@lem1187389 _27653) (@lem1187388 _27653)). Qed.
Lemma lem1187392 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1187393 {_27653 : Type'} (t : Prop) : (term27 _27653 t) = t.
Proof. exact (@lem1187392 (list _27653) t). Qed.
Lemma lem1187394 {_27653 : Type'} : (term25 _27653) = True.
Proof. exact (@lem1187393 _27653 True). Qed.
Lemma lem1187395 {_27653 : Type'} : (term29 _27653) = True.
Proof. exact (TRANS (@lem1187390 _27653) (@lem1187394 _27653)). Qed.
Lemma lem1187396 {_27653 : Type'} : True = (term29 _27653).
Proof. exact (SYM (@lem1187395 _27653)). Qed.
Lemma lem1187397 {_27653 : Type'} : term29 _27653.
Proof. exact (EQ_MP (@lem1187396 _27653) (@lem0)). Qed.
