Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_AND_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Lemma lem4798414 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4798415 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4798416 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4798415 t1) (@lem4798414 t1)). Qed.
Lemma lem4798417 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4798416 t1 t2). Qed.
Lemma lem4798418 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4798419 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4798418 t1 t2) (@lem4798417 t1 t2)). Qed.
Lemma lem4798420 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4798419 t1 t2 t3). Qed.
Lemma lem4798421 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4798422 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4798421 t1 t2 t3) (@lem4798420 t1 t2 t3)). Qed.
Lemma lem4798423 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4798422 t1 t2 t3)). Qed.
Lemma lem4798424 {_110510 : Type'} (s : _110510 -> Prop) : term7 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4798425 {_110510 : Type'} (s : _110510 -> Prop) : (term7 _110510 s) = (term8 _110510 s).
Proof. exact (eq_refl (term7 _110510 s)). Qed.
Lemma lem4798426 {_110510 : Type'} (s : _110510 -> Prop) : term8 _110510 s.
Proof. exact (EQ_MP (@lem4798425 _110510 s) (@lem4798424 _110510 s)). Qed.
Lemma lem4798427 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term9 _110510 s r.
Proof. exact (@lem4798426 _110510 s r). Qed.
Lemma lem4798428 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term9 _110510 s r) = ((@pairwise _110510 r s) = (term10 _110510 s r)).
Proof. exact (eq_refl (term9 _110510 s r)). Qed.
Lemma lem4798447 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4798428 _110510 s r) (@lem4798427 _110510 s r)). Qed.
Lemma lem4798448 {_110654 : Type'} (s : _110654 -> Prop) (r : type1402 _110654) : (@pairwise _110654 r s) = (term10 _110654 s r).
Proof. exact (@lem4798447 _110654 s r). Qed.
Lemma lem4798449 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (@pairwise _110654 R s) = (term10 _110654 s R).
Proof. exact (@lem4798448 _110654 s R). Qed.
Lemma lem4798466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798467 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term11 _110654 R s) = (term12 _110654 s R).
Proof. exact (MK_COMB (@lem4798466) (@lem4798449 _110654 s R)). Qed.
Lemma lem4798469 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4798428 _110510 s r) (@lem4798427 _110510 s r)). Qed.
Lemma lem4798470 {_110654 : Type'} (s : _110654 -> Prop) (r : type1402 _110654) : (@pairwise _110654 r s) = (term10 _110654 s r).
Proof. exact (@lem4798469 _110654 s r). Qed.
Lemma lem4798471 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (@pairwise _110654 R' s) = (term10 _110654 s R').
Proof. exact (@lem4798470 _110654 s R'). Qed.
Lemma lem4798488 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term13 _110654 R R' s) = (term14 _110654 R s R').
Proof. exact (MK_COMB (@lem4798467 _110654 s R) (@lem4798471 _110654 s R')). Qed.
Lemma lem4798491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4798492 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term15 _110654 R R' s) = (term16 _110654 R s R').
Proof. exact (MK_COMB (@lem4798491) (@lem4798488 _110654 R s R')). Qed.
Lemma lem4798494 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4798428 _110510 s r) (@lem4798427 _110510 s r)). Qed.
Lemma lem4798495 {_110654 : Type'} (s : _110654 -> Prop) (r : type1402 _110654) : (@pairwise _110654 r s) = (term10 _110654 s r).
Proof. exact (@lem4798494 _110654 s r). Qed.
Lemma lem4798496 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term17 _110654 R R' s) = (term18 _110654 s R R').
Proof. exact (@lem4798495 _110654 s (term19 _110654 R R')). Qed.
Lemma lem4798514 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4798515 {_110654 : Type'} (f : type1402 _110654) (y : _110654) : (term21 _110654 f y) = (f y).
Proof. exact (@lem4798514 _110654 (_110654 -> Prop) f y). Qed.
Lemma lem4798516 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term22 _110654 R R' x) = (term23 _110654 R R' x).
Proof. exact (@lem4798515 _110654 (term19 _110654 R R') x). Qed.
Lemma lem4798517 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term23 _110654 R R' x) = (term24 _110654 R R' x).
Proof. exact (eq_refl (term23 _110654 R R' x)). Qed.
Lemma lem4798518 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term25 _110654 R R') = (term19 _110654 R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4798517 _110654 R R' x)). Qed.
Lemma lem4798519 {_110654 : Type'} (x : _110654) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4798520 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term22 _110654 R R' x) = (term23 _110654 R R' x).
Proof. exact (MK_COMB (@lem4798518 _110654 R R') (@lem4798519 _110654 x)). Qed.
Lemma lem4798521 {_110654 : Type'} : (@eq (_110654 -> Prop)) = (@eq (_110654 -> Prop)).
Proof. exact (eq_refl (@eq (_110654 -> Prop))). Qed.
Lemma lem4798522 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term26 _110654 R R' x) = (term27 _110654 R R' x).
Proof. exact (MK_COMB (@lem4798521 _110654) (@lem4798520 _110654 R R' x)). Qed.
Lemma lem4798523 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term23 _110654 R R' x) = (term24 _110654 R R' x).
Proof. exact (eq_refl (term23 _110654 R R' x)). Qed.
Lemma lem4798524 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : ((term22 _110654 R R' x) = (term23 _110654 R R' x)) = ((term23 _110654 R R' x) = (term24 _110654 R R' x)).
Proof. exact (MK_COMB (@lem4798522 _110654 R R' x) (@lem4798523 _110654 R R' x)). Qed.
Lemma lem4798525 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term23 _110654 R R' x) = (term24 _110654 R R' x).
Proof. exact (EQ_MP (@lem4798524 _110654 R R' x) (@lem4798516 _110654 R R' x)). Qed.
Lemma lem4798528 {_110654 : Type'} (y : _110654) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4798529 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term28 _110654 R R' x y) = (term29 _110654 R R' x y).
Proof. exact (MK_COMB (@lem4798525 _110654 R R' x) (@lem4798528 _110654 y)). Qed.
Lemma lem4798531 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4798532 {_110654 : Type'} (f : _110654 -> Prop) (y : _110654) : (term30 _110654 f y) = (f y).
Proof. exact (@lem4798531 _110654 Prop f y). Qed.
Lemma lem4798533 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term31 _110654 R R' x y) = (term29 _110654 R R' x y).
Proof. exact (@lem4798532 _110654 (term24 _110654 R R' x) y). Qed.
Lemma lem4798534 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term29 _110654 R R' x y) = (term32 _110654 R R' x y).
Proof. exact (eq_refl (term29 _110654 R R' x y)). Qed.
Lemma lem4798535 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term33 _110654 R R' x) = (term24 _110654 R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4798534 _110654 R R' x y)). Qed.
Lemma lem4798536 {_110654 : Type'} (y : _110654) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4798537 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term31 _110654 R R' x y) = (term29 _110654 R R' x y).
Proof. exact (MK_COMB (@lem4798535 _110654 R R' x) (@lem4798536 _110654 y)). Qed.
Lemma lem4798538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4798539 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term34 _110654 R R' x y) = (term35 _110654 R R' x y).
Proof. exact (MK_COMB (@lem4798538) (@lem4798537 _110654 R R' x y)). Qed.
Lemma lem4798540 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term29 _110654 R R' x y) = (term32 _110654 R R' x y).
Proof. exact (eq_refl (term29 _110654 R R' x y)). Qed.
Lemma lem4798541 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : ((term31 _110654 R R' x y) = (term29 _110654 R R' x y)) = ((term29 _110654 R R' x y) = (term32 _110654 R R' x y)).
Proof. exact (MK_COMB (@lem4798539 _110654 R R' x y) (@lem4798540 _110654 R R' x y)). Qed.
Lemma lem4798542 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term29 _110654 R R' x y) = (term32 _110654 R R' x y).
Proof. exact (EQ_MP (@lem4798541 _110654 R R' x y) (@lem4798533 _110654 R R' x y)). Qed.
Lemma lem4798545 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term28 _110654 R R' x y) = (term32 _110654 R R' x y).
Proof. exact (TRANS (@lem4798529 _110654 R R' x y) (@lem4798542 _110654 R R' x y)). Qed.
Lemma lem4798546 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term36 _110654 s x y) = (term36 _110654 s x y).
Proof. exact (eq_refl (term36 _110654 s x y)). Qed.
Lemma lem4798547 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term37 _110654 s R R' x y) = (term38 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4798546 _110654 s x y) (@lem4798545 _110654 R R' x y)). Qed.
Lemma lem4798550 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term39 _110654 s R R' x) = (term40 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4798547 _110654 s R R' x y)). Qed.
Lemma lem4798551 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798552 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term41 _110654 s R R' x) = (term42 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4798551 _110654) (@lem4798550 _110654 s R R' x)). Qed.
Lemma lem4798557 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term43 _110654 s R R') = (term44 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4798552 _110654 s R R' x)). Qed.
Lemma lem4798558 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798559 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term18 _110654 s R R') = (term45 _110654 s R R').
Proof. exact (MK_COMB (@lem4798558 _110654) (@lem4798557 _110654 s R R')). Qed.
Lemma lem4798564 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term17 _110654 R R' s) = (term45 _110654 s R R').
Proof. exact (TRANS (@lem4798496 _110654 s R R') (@lem4798559 _110654 s R R')). Qed.
Lemma lem4798565 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term13 _110654 R R' s) = (term17 _110654 R R' s)) = ((term14 _110654 R s R') = (term45 _110654 s R R')).
Proof. exact (MK_COMB (@lem4798492 _110654 R s R') (@lem4798564 _110654 s R R')). Qed.
Lemma lem4798568 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term46 _110654 R R') = (term47 _110654 R R').
Proof. exact (fun_ext (fun s : _110654 -> Prop => @lem4798565 _110654 s R R')). Qed.
Lemma lem4798569 {_110654 : Type'} : (@all (_110654 -> Prop)) = (@all (_110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> Prop))). Qed.
Lemma lem4798570 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term48 _110654 R R') = (term49 _110654 R R').
Proof. exact (MK_COMB (@lem4798569 _110654) (@lem4798568 _110654 R R')). Qed.
Lemma lem4798575 {_110654 : Type'} (R : type1402 _110654) : (term50 _110654 R) = (term51 _110654 R).
Proof. exact (fun_ext (fun R' : type1402 _110654 => @lem4798570 _110654 R R')). Qed.
Lemma lem4798576 {_110654 : Type'} : (@all (_110654 -> _110654 -> Prop)) = (@all (_110654 -> _110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> _110654 -> Prop))). Qed.
Lemma lem4798577 {_110654 : Type'} (R : type1402 _110654) : (term52 _110654 R) = (term53 _110654 R).
Proof. exact (MK_COMB (@lem4798576 _110654) (@lem4798575 _110654 R)). Qed.
Lemma lem4798582 {_110654 : Type'} : (term54 _110654) = (term55 _110654).
Proof. exact (fun_ext (fun R : type1402 _110654 => @lem4798577 _110654 R)). Qed.
Lemma lem4798583 {_110654 : Type'} : (@all (_110654 -> _110654 -> Prop)) = (@all (_110654 -> _110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> _110654 -> Prop))). Qed.
Lemma lem4798584 {_110654 : Type'} : (term56 _110654) = (term57 _110654).
Proof. exact (MK_COMB (@lem4798583 _110654) (@lem4798582 _110654)). Qed.
Lemma lem4798589 {_110654 : Type'} : (term57 _110654) = (term56 _110654).
Proof. exact (SYM (@lem4798584 _110654)). Qed.
Lemma lem4798695 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4798696 {_110654 : Type'} (P : _110654 -> Prop) (x : _110654) : (@IN _110654 x P) = (P x).
Proof. exact (@lem4798695 _110654 P x). Qed.
Lemma lem4798697 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (@IN _110654 x s) = (s x).
Proof. exact (@lem4798696 _110654 s x). Qed.
Lemma lem4798698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798699 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term58 _110654 x s) = (term59 _110654 s x).
Proof. exact (MK_COMB (@lem4798698) (@lem4798697 _110654 s x)). Qed.
Lemma lem4798703 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4798704 {_110654 : Type'} (P : _110654 -> Prop) (x : _110654) : (@IN _110654 x P) = (P x).
Proof. exact (@lem4798703 _110654 P x). Qed.
Lemma lem4798705 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (@IN _110654 y s) = (s y).
Proof. exact (@lem4798704 _110654 s y). Qed.
Lemma lem4798706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798707 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term58 _110654 y s) = (term59 _110654 s y).
Proof. exact (MK_COMB (@lem4798706) (@lem4798705 _110654 s y)). Qed.
Lemma lem4798710 {_110654 : Type'} (x : _110654) (y : _110654) : (term60 _110654 x y) = (term60 _110654 x y).
Proof. exact (eq_refl (term60 _110654 x y)). Qed.
Lemma lem4798711 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term61 _110654 s x y) = (term62 _110654 s x y).
Proof. exact (MK_COMB (@lem4798707 _110654 s y) (@lem4798710 _110654 x y)). Qed.
Lemma lem4798714 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term63 _110654 s x y) = (term64 _110654 s x y).
Proof. exact (MK_COMB (@lem4798699 _110654 s x) (@lem4798711 _110654 s x y)). Qed.
Lemma lem4798717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4798718 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term36 _110654 s x y) = (term65 _110654 s x y).
Proof. exact (MK_COMB (@lem4798717) (@lem4798714 _110654 s x y)). Qed.
Lemma lem4798719 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4798720 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term66 _110654 s R x y) = (term67 _110654 s R x y).
Proof. exact (MK_COMB (@lem4798718 _110654 s x y) (@lem4798719 _110654 R x y)). Qed.
Lemma lem4798723 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term68 _110654 s R x) = (term69 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4798720 _110654 s R x y)). Qed.
Lemma lem4798724 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798725 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term70 _110654 s R x) = (term71 _110654 s R x).
Proof. exact (MK_COMB (@lem4798724 _110654) (@lem4798723 _110654 s R x)). Qed.
Lemma lem4798730 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term72 _110654 s R) = (term73 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4798725 _110654 s R x)). Qed.
Lemma lem4798731 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798732 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term10 _110654 s R) = (term74 _110654 s R).
Proof. exact (MK_COMB (@lem4798731 _110654) (@lem4798730 _110654 s R)). Qed.
Lemma lem4798737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798738 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term12 _110654 s R) = (term75 _110654 s R).
Proof. exact (MK_COMB (@lem4798737) (@lem4798732 _110654 s R)). Qed.
Lemma lem4798752 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4798753 {_110654 : Type'} (P : _110654 -> Prop) (x : _110654) : (@IN _110654 x P) = (P x).
Proof. exact (@lem4798752 _110654 P x). Qed.
Lemma lem4798754 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (@IN _110654 x s) = (s x).
Proof. exact (@lem4798753 _110654 s x). Qed.
Lemma lem4798755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798756 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term58 _110654 x s) = (term59 _110654 s x).
Proof. exact (MK_COMB (@lem4798755) (@lem4798754 _110654 s x)). Qed.
Lemma lem4798760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4798761 {_110654 : Type'} (P : _110654 -> Prop) (x : _110654) : (@IN _110654 x P) = (P x).
Proof. exact (@lem4798760 _110654 P x). Qed.
Lemma lem4798762 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (@IN _110654 y s) = (s y).
Proof. exact (@lem4798761 _110654 s y). Qed.
Lemma lem4798763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798764 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term58 _110654 y s) = (term59 _110654 s y).
Proof. exact (MK_COMB (@lem4798763) (@lem4798762 _110654 s y)). Qed.
Lemma lem4798767 {_110654 : Type'} (x : _110654) (y : _110654) : (term60 _110654 x y) = (term60 _110654 x y).
Proof. exact (eq_refl (term60 _110654 x y)). Qed.
Lemma lem4798768 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term61 _110654 s x y) = (term62 _110654 s x y).
Proof. exact (MK_COMB (@lem4798764 _110654 s y) (@lem4798767 _110654 x y)). Qed.
Lemma lem4798771 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term63 _110654 s x y) = (term64 _110654 s x y).
Proof. exact (MK_COMB (@lem4798756 _110654 s x) (@lem4798768 _110654 s x y)). Qed.
Lemma lem4798774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4798775 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term36 _110654 s x y) = (term65 _110654 s x y).
Proof. exact (MK_COMB (@lem4798774) (@lem4798771 _110654 s x y)). Qed.
Lemma lem4798776 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) : (R' x y) = (R' x y).
Proof. exact (eq_refl (R' x y)). Qed.
Lemma lem4798777 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term66 _110654 s R' x y) = (term67 _110654 s R' x y).
Proof. exact (MK_COMB (@lem4798775 _110654 s x y) (@lem4798776 _110654 R' x y)). Qed.
Lemma lem4798780 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term68 _110654 s R' x) = (term69 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4798777 _110654 s R' x y)). Qed.
Lemma lem4798781 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798782 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term70 _110654 s R' x) = (term71 _110654 s R' x).
Proof. exact (MK_COMB (@lem4798781 _110654) (@lem4798780 _110654 s R' x)). Qed.
Lemma lem4798787 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term72 _110654 s R') = (term73 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4798782 _110654 s R' x)). Qed.
Lemma lem4798788 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798789 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term10 _110654 s R') = (term74 _110654 s R').
Proof. exact (MK_COMB (@lem4798788 _110654) (@lem4798787 _110654 s R')). Qed.
Lemma lem4798794 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term14 _110654 R s R') = (term76 _110654 R s R').
Proof. exact (MK_COMB (@lem4798738 _110654 s R) (@lem4798789 _110654 s R')). Qed.
Lemma lem4798797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4798798 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term16 _110654 R s R') = (term77 _110654 R s R').
Proof. exact (MK_COMB (@lem4798797) (@lem4798794 _110654 R s R')). Qed.
Lemma lem4798812 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4798813 {_110654 : Type'} (P : _110654 -> Prop) (x : _110654) : (@IN _110654 x P) = (P x).
Proof. exact (@lem4798812 _110654 P x). Qed.
Lemma lem4798814 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (@IN _110654 x s) = (s x).
Proof. exact (@lem4798813 _110654 s x). Qed.
Lemma lem4798815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798816 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term58 _110654 x s) = (term59 _110654 s x).
Proof. exact (MK_COMB (@lem4798815) (@lem4798814 _110654 s x)). Qed.
Lemma lem4798820 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4798821 {_110654 : Type'} (P : _110654 -> Prop) (x : _110654) : (@IN _110654 x P) = (P x).
Proof. exact (@lem4798820 _110654 P x). Qed.
Lemma lem4798822 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (@IN _110654 y s) = (s y).
Proof. exact (@lem4798821 _110654 s y). Qed.
Lemma lem4798823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798824 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term58 _110654 y s) = (term59 _110654 s y).
Proof. exact (MK_COMB (@lem4798823) (@lem4798822 _110654 s y)). Qed.
Lemma lem4798827 {_110654 : Type'} (x : _110654) (y : _110654) : (term60 _110654 x y) = (term60 _110654 x y).
Proof. exact (eq_refl (term60 _110654 x y)). Qed.
Lemma lem4798828 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term61 _110654 s x y) = (term62 _110654 s x y).
Proof. exact (MK_COMB (@lem4798824 _110654 s y) (@lem4798827 _110654 x y)). Qed.
Lemma lem4798831 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term63 _110654 s x y) = (term64 _110654 s x y).
Proof. exact (MK_COMB (@lem4798816 _110654 s x) (@lem4798828 _110654 s x y)). Qed.
Lemma lem4798834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4798835 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term36 _110654 s x y) = (term65 _110654 s x y).
Proof. exact (MK_COMB (@lem4798834) (@lem4798831 _110654 s x y)). Qed.
Lemma lem4798838 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term32 _110654 R R' x y) = (term32 _110654 R R' x y).
Proof. exact (eq_refl (term32 _110654 R R' x y)). Qed.
Lemma lem4798839 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term38 _110654 s R R' x y) = (term78 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4798835 _110654 s x y) (@lem4798838 _110654 R R' x y)). Qed.
Lemma lem4798842 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term40 _110654 s R R' x) = (term79 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4798839 _110654 s R R' x y)). Qed.
Lemma lem4798843 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798844 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term42 _110654 s R R' x) = (term80 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4798843 _110654) (@lem4798842 _110654 s R R' x)). Qed.
Lemma lem4798849 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term44 _110654 s R R') = (term81 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4798844 _110654 s R R' x)). Qed.
Lemma lem4798850 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798851 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term45 _110654 s R R') = (term82 _110654 s R R').
Proof. exact (MK_COMB (@lem4798850 _110654) (@lem4798849 _110654 s R R')). Qed.
Lemma lem4798856 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term14 _110654 R s R') = (term45 _110654 s R R')) = ((term76 _110654 R s R') = (term82 _110654 s R R')).
Proof. exact (MK_COMB (@lem4798798 _110654 R s R') (@lem4798851 _110654 s R R')). Qed.
Lemma lem4798859 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term47 _110654 R R') = (term83 _110654 R R').
Proof. exact (fun_ext (fun s : _110654 -> Prop => @lem4798856 _110654 s R R')). Qed.
Lemma lem4798860 {_110654 : Type'} : (@all (_110654 -> Prop)) = (@all (_110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> Prop))). Qed.
Lemma lem4798861 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term49 _110654 R R') = (term84 _110654 R R').
Proof. exact (MK_COMB (@lem4798860 _110654) (@lem4798859 _110654 R R')). Qed.
Lemma lem4798866 {_110654 : Type'} (R : type1402 _110654) : (term51 _110654 R) = (term85 _110654 R).
Proof. exact (fun_ext (fun R' : type1402 _110654 => @lem4798861 _110654 R R')). Qed.
Lemma lem4798867 {_110654 : Type'} : (@all (_110654 -> _110654 -> Prop)) = (@all (_110654 -> _110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> _110654 -> Prop))). Qed.
Lemma lem4798868 {_110654 : Type'} (R : type1402 _110654) : (term53 _110654 R) = (term86 _110654 R).
Proof. exact (MK_COMB (@lem4798867 _110654) (@lem4798866 _110654 R)). Qed.
Lemma lem4798873 {_110654 : Type'} : (term55 _110654) = (term87 _110654).
Proof. exact (fun_ext (fun R : type1402 _110654 => @lem4798868 _110654 R)). Qed.
Lemma lem4798874 {_110654 : Type'} : (@all (_110654 -> _110654 -> Prop)) = (@all (_110654 -> _110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> _110654 -> Prop))). Qed.
Lemma lem4798875 {_110654 : Type'} : (term57 _110654) = (term88 _110654).
Proof. exact (MK_COMB (@lem4798874 _110654) (@lem4798873 _110654)). Qed.
Lemma lem4798880 {_110654 : Type'} : (term88 _110654) = (term57 _110654).
Proof. exact (SYM (@lem4798875 _110654)). Qed.
Lemma lem4798882 (p : Prop) : p = (term89 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4798883 {_110654 : Type'} : (term88 _110654) = (term90 _110654).
Proof. exact (@lem4798882 (term88 _110654)). Qed.
Lemma lem4798884 {_110654 : Type'} : (term90 _110654) = (term88 _110654).
Proof. exact (SYM (@lem4798883 _110654)). Qed.
Lemma lem4798885 {_110654 : Type'} (h1 : term91 _110654) : term91 _110654.
Proof. exact (h1). Qed.
Lemma lem4798888 {_110654 : Type'} (h1 : term90 _110654) : term90 _110654.
Proof. exact (h1). Qed.
Lemma lem4798889 {_110654 : Type'} : term92 _110654.
Proof. exact (fun h0 : term90 _110654 => @lem4798888 _110654 h0). Qed.
Lemma lem4798890 {_110654 : Type'} (h1 : term92 _110654) : term92 _110654.
Proof. exact (h1). Qed.
Lemma lem4798891 {_110654 : Type'} (h1 : term90 _110654) : term90 _110654.
Proof. exact (h1). Qed.
Lemma lem4798892 {_110654 : Type'} (h1 : term90 _110654) (h2 : term92 _110654) : term90 _110654.
Proof. exact (@lem4798890 _110654 h2 (@lem4798891 _110654 h1)). Qed.
Lemma lem4798893 {_110654 : Type'} (h1 : term90 _110654) : term93 _110654.
Proof. exact (fun h0 : term92 _110654 => @lem4798892 _110654 h1 h0). Qed.
Lemma lem4798894 {_110654 : Type'} (h1 : term92 _110654) : term92 _110654.
Proof. exact (h1). Qed.
Lemma lem4798895 {_110654 : Type'} (h1 : term90 _110654) (h2 : term92 _110654) : term90 _110654.
Proof. exact (@lem4798893 _110654 h1 (@lem4798894 _110654 h2)). Qed.
Lemma lem4798896 {_110654 : Type'} (h1 : term92 _110654) : term92 _110654.
Proof. exact (fun h0 : term90 _110654 => @lem4798895 _110654 h0 h1). Qed.
Lemma lem4798897 {_110654 : Type'} : term94 _110654.
Proof. exact (fun h0 : term92 _110654 => @lem4798896 _110654 h0). Qed.
Lemma lem4798900 {_110654 : Type'} : term92 _110654.
Proof. exact (@lem4798897 _110654 (@lem4798889 _110654)). Qed.
Lemma lem4798901 {_110654 : Type'} : term92 _110654.
Proof. exact (@lem4798900 _110654). Qed.
Lemma lem4798903 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4798904 {_110654 : Type'} : (term90 _110654) = (term95 _110654).
Proof. exact (@lem4798903 (term91 _110654)). Qed.
Lemma lem4798906 (t : Prop) : (term96 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4798907 {_110654 : Type'} : (term95 _110654) = (term88 _110654).
Proof. exact (@lem4798906 (term88 _110654)). Qed.
Lemma lem4798970 {_110654 : Type'} : (term90 _110654) = (term88 _110654).
Proof. exact (TRANS (@lem4798904 _110654) (@lem4798907 _110654)). Qed.
Lemma lem4798989 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term78 _110654 s R R' x y) = (term78 _110654 s R R' x y).
Proof. exact (eq_refl (term78 _110654 s R R' x y)). Qed.
Lemma lem4798990 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term79 _110654 s R R' x) = (term79 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4798989 _110654 s R R' x y)). Qed.
Lemma lem4798991 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798992 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term80 _110654 s R R' x) = (term80 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4798991 _110654) (@lem4798990 _110654 s R R' x)). Qed.
Lemma lem4798993 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term81 _110654 s R R') = (term81 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4798992 _110654 s R R' x)). Qed.
Lemma lem4798994 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4798995 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term82 _110654 s R R') = (term82 _110654 s R R').
Proof. exact (MK_COMB (@lem4798994 _110654) (@lem4798993 _110654 s R R')). Qed.
Lemma lem4799010 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term67 _110654 s R' x y) = (term67 _110654 s R' x y).
Proof. exact (eq_refl (term67 _110654 s R' x y)). Qed.
Lemma lem4799011 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term69 _110654 s R' x) = (term69 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799010 _110654 s R' x y)). Qed.
Lemma lem4799012 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799013 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term71 _110654 s R' x) = (term71 _110654 s R' x).
Proof. exact (MK_COMB (@lem4799012 _110654) (@lem4799011 _110654 s R' x)). Qed.
Lemma lem4799014 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term73 _110654 s R') = (term73 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799013 _110654 s R' x)). Qed.
Lemma lem4799015 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799016 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term74 _110654 s R') = (term74 _110654 s R').
Proof. exact (MK_COMB (@lem4799015 _110654) (@lem4799014 _110654 s R')). Qed.
Lemma lem4799031 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term67 _110654 s R x y) = (term67 _110654 s R x y).
Proof. exact (eq_refl (term67 _110654 s R x y)). Qed.
Lemma lem4799032 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term69 _110654 s R x) = (term69 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799031 _110654 s R x y)). Qed.
Lemma lem4799033 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799034 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term71 _110654 s R x) = (term71 _110654 s R x).
Proof. exact (MK_COMB (@lem4799033 _110654) (@lem4799032 _110654 s R x)). Qed.
Lemma lem4799035 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term73 _110654 s R) = (term73 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4799034 _110654 s R x)). Qed.
Lemma lem4799036 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799037 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term74 _110654 s R) = (term74 _110654 s R).
Proof. exact (MK_COMB (@lem4799036 _110654) (@lem4799035 _110654 s R)). Qed.
Lemma lem4799038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799039 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term75 _110654 s R) = (term75 _110654 s R).
Proof. exact (MK_COMB (@lem4799038) (@lem4799037 _110654 s R)). Qed.
Lemma lem4799040 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term76 _110654 R s R') = (term76 _110654 R s R').
Proof. exact (MK_COMB (@lem4799039 _110654 s R) (@lem4799016 _110654 s R')). Qed.
Lemma lem4799041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799042 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term77 _110654 R s R') = (term77 _110654 R s R').
Proof. exact (MK_COMB (@lem4799041) (@lem4799040 _110654 R s R')). Qed.
Lemma lem4799043 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term76 _110654 R s R') = (term82 _110654 s R R')) = ((term76 _110654 R s R') = (term82 _110654 s R R')).
Proof. exact (MK_COMB (@lem4799042 _110654 R s R') (@lem4798995 _110654 s R R')). Qed.
Lemma lem4799044 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term83 _110654 R R') = (term83 _110654 R R').
Proof. exact (fun_ext (fun s : _110654 -> Prop => @lem4799043 _110654 s R R')). Qed.
Lemma lem4799045 {_110654 : Type'} : (@all (_110654 -> Prop)) = (@all (_110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> Prop))). Qed.
Lemma lem4799046 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : (term84 _110654 R R') = (term84 _110654 R R').
Proof. exact (MK_COMB (@lem4799045 _110654) (@lem4799044 _110654 R R')). Qed.
Lemma lem4799047 {_110654 : Type'} (R : type1402 _110654) : (term85 _110654 R) = (term85 _110654 R).
Proof. exact (fun_ext (fun R' : type1402 _110654 => @lem4799046 _110654 R R')). Qed.
Lemma lem4799048 {_110654 : Type'} : (@all (_110654 -> _110654 -> Prop)) = (@all (_110654 -> _110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> _110654 -> Prop))). Qed.
Lemma lem4799049 {_110654 : Type'} (R : type1402 _110654) : (term86 _110654 R) = (term86 _110654 R).
Proof. exact (MK_COMB (@lem4799048 _110654) (@lem4799047 _110654 R)). Qed.
Lemma lem4799050 {_110654 : Type'} : (term87 _110654) = (term87 _110654).
Proof. exact (fun_ext (fun R : type1402 _110654 => @lem4799049 _110654 R)). Qed.
Lemma lem4799051 {_110654 : Type'} : (@all (_110654 -> _110654 -> Prop)) = (@all (_110654 -> _110654 -> Prop)).
Proof. exact (eq_refl (@all (_110654 -> _110654 -> Prop))). Qed.
Lemma lem4799052 {_110654 : Type'} : (term88 _110654) = (term88 _110654).
Proof. exact (MK_COMB (@lem4799051 _110654) (@lem4799050 _110654)). Qed.
Lemma lem4799131 {_110654 : Type'} : (term90 _110654) = (term88 _110654).
Proof. exact (TRANS (@lem4798970 _110654) (@lem4799052 _110654)). Qed.
Lemma lem4799132 {_110654 : Type'} : (term88 _110654) = (term90 _110654).
Proof. exact (SYM (@lem4799131 _110654)). Qed.
Lemma lem4799134 (p : Prop) : p = (term89 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4799135 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term76 _110654 R s R') = (term82 _110654 s R R')) = (term97 _110654 s R R').
Proof. exact (@lem4799134 ((term76 _110654 R s R') = (term82 _110654 s R R'))). Qed.
Lemma lem4799136 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term97 _110654 s R R') = ((term76 _110654 R s R') = (term82 _110654 s R R')).
Proof. exact (SYM (@lem4799135 _110654 s R R')). Qed.
Lemma lem4799137 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term98 _110654 s R R') : term98 _110654 s R R'.
Proof. exact (h1). Qed.
Lemma lem4799145 {_110654 : Type'} (x : _110654) (y : _110654) : (term99 _110654 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4799147 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term100 _110654 s y) = (term100 _110654 s y).
Proof. exact (eq_refl (term100 _110654 s y)). Qed.
Lemma lem4799148 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term101 _110654 s x y) = (term102 _110654 s x y).
Proof. exact (MK_COMB (@lem4799147 _110654 s y) (@lem4799145 _110654 x y)). Qed.
Lemma lem4799149 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term103 _110654 s x y) = (term101 _110654 s x y).
Proof. exact (@lem17045 (s y) (term60 _110654 x y)). Qed.
Lemma lem4799150 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term103 _110654 s x y) = (term102 _110654 s x y).
Proof. exact (TRANS (@lem4799149 _110654 s x y) (@lem4799148 _110654 s x y)). Qed.
Lemma lem4799155 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term100 _110654 s x) = (term100 _110654 s x).
Proof. exact (eq_refl (term100 _110654 s x)). Qed.
Lemma lem4799156 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term104 _110654 s x y) = (term105 _110654 s x y).
Proof. exact (MK_COMB (@lem4799155 _110654 s x) (@lem4799150 _110654 s x y)). Qed.
Lemma lem4799157 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term106 _110654 s x y) = (term104 _110654 s x y).
Proof. exact (@lem17045 (s x) (term62 _110654 s x y)). Qed.
Lemma lem4799158 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term106 _110654 s x y) = (term105 _110654 s x y).
Proof. exact (TRANS (@lem4799157 _110654 s x y) (@lem4799156 _110654 s x y)). Qed.
Lemma lem4799163 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4799168 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term107 _110654 s R x y) = (term108 _110654 s R x y).
Proof. exact (@lem17362 (term64 _110654 s x y) (R x y)). Qed.
Lemma lem4799169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799170 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term109 _110654 s x y) = (term110 _110654 s x y).
Proof. exact (MK_COMB (@lem4799169) (@lem4799158 _110654 s x y)). Qed.
Lemma lem4799171 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term111 _110654 s R x y) = (term112 _110654 s R x y).
Proof. exact (MK_COMB (@lem4799170 _110654 s x y) (@lem4799163 _110654 R x y)). Qed.
Lemma lem4799172 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term67 _110654 s R x y) = (term111 _110654 s R x y).
Proof. exact (@lem17265 (term64 _110654 s x y) (R x y)). Qed.
Lemma lem4799173 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term67 _110654 s R x y) = (term112 _110654 s R x y).
Proof. exact (TRANS (@lem4799172 _110654 s R x y) (@lem4799171 _110654 s R x y)). Qed.
Lemma lem4799174 {_110654 : Type'} (P : _110654 -> Prop) : (term113 _110654 P) = (term114 _110654 P).
Proof. exact (@lem18392 _110654 P). Qed.
Lemma lem4799175 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term115 _110654 s R x) = (term116 _110654 s R x).
Proof. exact (@lem4799174 _110654 (term69 _110654 s R x)). Qed.
Lemma lem4799176 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term117 _110654 s R x y) = (term67 _110654 s R x y).
Proof. exact (eq_refl (term117 _110654 s R x y)). Qed.
Lemma lem4799177 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4799178 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term118 _110654 s R x y) = (term107 _110654 s R x y).
Proof. exact (MK_COMB (@lem4799177) (@lem4799176 _110654 s R x y)). Qed.
Lemma lem4799179 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term118 _110654 s R x y) = (term108 _110654 s R x y).
Proof. exact (TRANS (@lem4799178 _110654 s R x y) (@lem4799168 _110654 s R x y)). Qed.
Lemma lem4799180 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term119 _110654 s R x) = (term120 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799179 _110654 s R x y)). Qed.
Lemma lem4799181 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799182 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term116 _110654 s R x) = (term121 _110654 s R x).
Proof. exact (MK_COMB (@lem4799181 _110654) (@lem4799180 _110654 s R x)). Qed.
Lemma lem4799183 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term115 _110654 s R x) = (term121 _110654 s R x).
Proof. exact (TRANS (@lem4799175 _110654 s R x) (@lem4799182 _110654 s R x)). Qed.
Lemma lem4799184 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term69 _110654 s R x) = (term122 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799173 _110654 s R x y)). Qed.
Lemma lem4799185 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799186 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term71 _110654 s R x) = (term123 _110654 s R x).
Proof. exact (MK_COMB (@lem4799185 _110654) (@lem4799184 _110654 s R x)). Qed.
Lemma lem4799187 {_110654 : Type'} (P : _110654 -> Prop) : (term113 _110654 P) = (term114 _110654 P).
Proof. exact (@lem18392 _110654 P). Qed.
Lemma lem4799188 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term124 _110654 s R) = (term125 _110654 s R).
Proof. exact (@lem4799187 _110654 (term73 _110654 s R)). Qed.
Lemma lem4799189 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term126 _110654 s R x) = (term71 _110654 s R x).
Proof. exact (eq_refl (term126 _110654 s R x)). Qed.
Lemma lem4799190 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4799191 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term127 _110654 s R x) = (term115 _110654 s R x).
Proof. exact (MK_COMB (@lem4799190) (@lem4799189 _110654 s R x)). Qed.
Lemma lem4799192 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term127 _110654 s R x) = (term121 _110654 s R x).
Proof. exact (TRANS (@lem4799191 _110654 s R x) (@lem4799183 _110654 s R x)). Qed.
Lemma lem4799193 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term128 _110654 s R) = (term129 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4799192 _110654 s R x)). Qed.
Lemma lem4799194 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799195 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term125 _110654 s R) = (term130 _110654 s R).
Proof. exact (MK_COMB (@lem4799194 _110654) (@lem4799193 _110654 s R)). Qed.
Lemma lem4799196 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term124 _110654 s R) = (term130 _110654 s R).
Proof. exact (TRANS (@lem4799188 _110654 s R) (@lem4799195 _110654 s R)). Qed.
Lemma lem4799197 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term73 _110654 s R) = (term131 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4799186 _110654 s R x)). Qed.
Lemma lem4799198 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799199 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term74 _110654 s R) = (term132 _110654 s R).
Proof. exact (MK_COMB (@lem4799198 _110654) (@lem4799197 _110654 s R)). Qed.
Lemma lem4799207 {_110654 : Type'} (x : _110654) (y : _110654) : (term99 _110654 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4799209 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term100 _110654 s y) = (term100 _110654 s y).
Proof. exact (eq_refl (term100 _110654 s y)). Qed.
Lemma lem4799210 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term101 _110654 s x y) = (term102 _110654 s x y).
Proof. exact (MK_COMB (@lem4799209 _110654 s y) (@lem4799207 _110654 x y)). Qed.
Lemma lem4799211 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term103 _110654 s x y) = (term101 _110654 s x y).
Proof. exact (@lem17045 (s y) (term60 _110654 x y)). Qed.
Lemma lem4799212 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term103 _110654 s x y) = (term102 _110654 s x y).
Proof. exact (TRANS (@lem4799211 _110654 s x y) (@lem4799210 _110654 s x y)). Qed.
Lemma lem4799217 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term100 _110654 s x) = (term100 _110654 s x).
Proof. exact (eq_refl (term100 _110654 s x)). Qed.
Lemma lem4799218 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term104 _110654 s x y) = (term105 _110654 s x y).
Proof. exact (MK_COMB (@lem4799217 _110654 s x) (@lem4799212 _110654 s x y)). Qed.
Lemma lem4799219 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term106 _110654 s x y) = (term104 _110654 s x y).
Proof. exact (@lem17045 (s x) (term62 _110654 s x y)). Qed.
Lemma lem4799220 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term106 _110654 s x y) = (term105 _110654 s x y).
Proof. exact (TRANS (@lem4799219 _110654 s x y) (@lem4799218 _110654 s x y)). Qed.
Lemma lem4799225 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) : (R' x y) = (R' x y).
Proof. exact (eq_refl (R' x y)). Qed.
Lemma lem4799230 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term107 _110654 s R' x y) = (term108 _110654 s R' x y).
Proof. exact (@lem17362 (term64 _110654 s x y) (R' x y)). Qed.
Lemma lem4799231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799232 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term109 _110654 s x y) = (term110 _110654 s x y).
Proof. exact (MK_COMB (@lem4799231) (@lem4799220 _110654 s x y)). Qed.
Lemma lem4799233 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term111 _110654 s R' x y) = (term112 _110654 s R' x y).
Proof. exact (MK_COMB (@lem4799232 _110654 s x y) (@lem4799225 _110654 R' x y)). Qed.
Lemma lem4799234 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term67 _110654 s R' x y) = (term111 _110654 s R' x y).
Proof. exact (@lem17265 (term64 _110654 s x y) (R' x y)). Qed.
Lemma lem4799235 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term67 _110654 s R' x y) = (term112 _110654 s R' x y).
Proof. exact (TRANS (@lem4799234 _110654 s R' x y) (@lem4799233 _110654 s R' x y)). Qed.
Lemma lem4799236 {_110654 : Type'} (P : _110654 -> Prop) : (term113 _110654 P) = (term114 _110654 P).
Proof. exact (@lem18392 _110654 P). Qed.
Lemma lem4799237 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term115 _110654 s R' x) = (term116 _110654 s R' x).
Proof. exact (@lem4799236 _110654 (term69 _110654 s R' x)). Qed.
Lemma lem4799238 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term117 _110654 s R' x y) = (term67 _110654 s R' x y).
Proof. exact (eq_refl (term117 _110654 s R' x y)). Qed.
Lemma lem4799239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4799240 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term118 _110654 s R' x y) = (term107 _110654 s R' x y).
Proof. exact (MK_COMB (@lem4799239) (@lem4799238 _110654 s R' x y)). Qed.
Lemma lem4799241 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term118 _110654 s R' x y) = (term108 _110654 s R' x y).
Proof. exact (TRANS (@lem4799240 _110654 s R' x y) (@lem4799230 _110654 s R' x y)). Qed.
Lemma lem4799242 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term119 _110654 s R' x) = (term120 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799241 _110654 s R' x y)). Qed.
Lemma lem4799243 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799244 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term116 _110654 s R' x) = (term121 _110654 s R' x).
Proof. exact (MK_COMB (@lem4799243 _110654) (@lem4799242 _110654 s R' x)). Qed.
Lemma lem4799245 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term115 _110654 s R' x) = (term121 _110654 s R' x).
Proof. exact (TRANS (@lem4799237 _110654 s R' x) (@lem4799244 _110654 s R' x)). Qed.
Lemma lem4799246 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term69 _110654 s R' x) = (term122 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799235 _110654 s R' x y)). Qed.
Lemma lem4799247 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799248 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term71 _110654 s R' x) = (term123 _110654 s R' x).
Proof. exact (MK_COMB (@lem4799247 _110654) (@lem4799246 _110654 s R' x)). Qed.
Lemma lem4799249 {_110654 : Type'} (P : _110654 -> Prop) : (term113 _110654 P) = (term114 _110654 P).
Proof. exact (@lem18392 _110654 P). Qed.
Lemma lem4799250 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term124 _110654 s R') = (term125 _110654 s R').
Proof. exact (@lem4799249 _110654 (term73 _110654 s R')). Qed.
Lemma lem4799251 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term126 _110654 s R' x) = (term71 _110654 s R' x).
Proof. exact (eq_refl (term126 _110654 s R' x)). Qed.
Lemma lem4799252 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4799253 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term127 _110654 s R' x) = (term115 _110654 s R' x).
Proof. exact (MK_COMB (@lem4799252) (@lem4799251 _110654 s R' x)). Qed.
Lemma lem4799254 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term127 _110654 s R' x) = (term121 _110654 s R' x).
Proof. exact (TRANS (@lem4799253 _110654 s R' x) (@lem4799245 _110654 s R' x)). Qed.
Lemma lem4799255 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term128 _110654 s R') = (term129 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799254 _110654 s R' x)). Qed.
Lemma lem4799256 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799257 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term125 _110654 s R') = (term130 _110654 s R').
Proof. exact (MK_COMB (@lem4799256 _110654) (@lem4799255 _110654 s R')). Qed.
Lemma lem4799258 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term124 _110654 s R') = (term130 _110654 s R').
Proof. exact (TRANS (@lem4799250 _110654 s R') (@lem4799257 _110654 s R')). Qed.
Lemma lem4799259 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term73 _110654 s R') = (term131 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799248 _110654 s R' x)). Qed.
Lemma lem4799260 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799261 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term74 _110654 s R') = (term132 _110654 s R').
Proof. exact (MK_COMB (@lem4799260 _110654) (@lem4799259 _110654 s R')). Qed.
Lemma lem4799262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799263 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term133 _110654 s R) = (term134 _110654 s R).
Proof. exact (MK_COMB (@lem4799262) (@lem4799196 _110654 s R)). Qed.
Lemma lem4799264 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term135 _110654 R s R') = (term136 _110654 R s R').
Proof. exact (MK_COMB (@lem4799263 _110654 s R) (@lem4799258 _110654 s R')). Qed.
Lemma lem4799265 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term137 _110654 R s R') = (term135 _110654 R s R').
Proof. exact (@lem17045 (term74 _110654 s R) (term74 _110654 s R')). Qed.
Lemma lem4799266 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term137 _110654 R s R') = (term136 _110654 R s R').
Proof. exact (TRANS (@lem4799265 _110654 R s R') (@lem4799264 _110654 R s R')). Qed.
Lemma lem4799267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799268 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term75 _110654 s R) = (term138 _110654 s R).
Proof. exact (MK_COMB (@lem4799267) (@lem4799199 _110654 s R)). Qed.
Lemma lem4799269 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term76 _110654 R s R') = (term139 _110654 R s R').
Proof. exact (MK_COMB (@lem4799268 _110654 s R) (@lem4799261 _110654 s R')). Qed.
Lemma lem4799277 {_110654 : Type'} (x : _110654) (y : _110654) : (term99 _110654 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4799279 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term100 _110654 s y) = (term100 _110654 s y).
Proof. exact (eq_refl (term100 _110654 s y)). Qed.
Lemma lem4799280 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term101 _110654 s x y) = (term102 _110654 s x y).
Proof. exact (MK_COMB (@lem4799279 _110654 s y) (@lem4799277 _110654 x y)). Qed.
Lemma lem4799281 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term103 _110654 s x y) = (term101 _110654 s x y).
Proof. exact (@lem17045 (s y) (term60 _110654 x y)). Qed.
Lemma lem4799282 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term103 _110654 s x y) = (term102 _110654 s x y).
Proof. exact (TRANS (@lem4799281 _110654 s x y) (@lem4799280 _110654 s x y)). Qed.
Lemma lem4799287 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term100 _110654 s x) = (term100 _110654 s x).
Proof. exact (eq_refl (term100 _110654 s x)). Qed.
Lemma lem4799288 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term104 _110654 s x y) = (term105 _110654 s x y).
Proof. exact (MK_COMB (@lem4799287 _110654 s x) (@lem4799282 _110654 s x y)). Qed.
Lemma lem4799289 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term106 _110654 s x y) = (term104 _110654 s x y).
Proof. exact (@lem17045 (s x) (term62 _110654 s x y)). Qed.
Lemma lem4799290 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term106 _110654 s x y) = (term105 _110654 s x y).
Proof. exact (TRANS (@lem4799289 _110654 s x y) (@lem4799288 _110654 s x y)). Qed.
Lemma lem4799302 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term140 _110654 R R' x y) = (term141 _110654 R R' x y).
Proof. exact (@lem17045 (R x y) (R' x y)). Qed.
Lemma lem4799305 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term32 _110654 R R' x y) = (term32 _110654 R R' x y).
Proof. exact (eq_refl (term32 _110654 R R' x y)). Qed.
Lemma lem4799307 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term142 _110654 s x y) = (term142 _110654 s x y).
Proof. exact (eq_refl (term142 _110654 s x y)). Qed.
Lemma lem4799308 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term143 _110654 s R R' x y) = (term144 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4799307 _110654 s x y) (@lem4799302 _110654 R R' x y)). Qed.
Lemma lem4799309 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term145 _110654 s R R' x y) = (term143 _110654 s R R' x y).
Proof. exact (@lem17362 (term64 _110654 s x y) (term32 _110654 R R' x y)). Qed.
Lemma lem4799310 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term145 _110654 s R R' x y) = (term144 _110654 s R R' x y).
Proof. exact (TRANS (@lem4799309 _110654 s R R' x y) (@lem4799308 _110654 s R R' x y)). Qed.
Lemma lem4799311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799312 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) (y : _110654) : (term109 _110654 s x y) = (term110 _110654 s x y).
Proof. exact (MK_COMB (@lem4799311) (@lem4799290 _110654 s x y)). Qed.
Lemma lem4799313 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term146 _110654 s R R' x y) = (term147 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4799312 _110654 s x y) (@lem4799305 _110654 R R' x y)). Qed.
Lemma lem4799314 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term78 _110654 s R R' x y) = (term146 _110654 s R R' x y).
Proof. exact (@lem17265 (term64 _110654 s x y) (term32 _110654 R R' x y)). Qed.
Lemma lem4799315 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term78 _110654 s R R' x y) = (term147 _110654 s R R' x y).
Proof. exact (TRANS (@lem4799314 _110654 s R R' x y) (@lem4799313 _110654 s R R' x y)). Qed.
Lemma lem4799316 {_110654 : Type'} (P : _110654 -> Prop) : (term113 _110654 P) = (term114 _110654 P).
Proof. exact (@lem18392 _110654 P). Qed.
Lemma lem4799317 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term148 _110654 s R R' x) = (term149 _110654 s R R' x).
Proof. exact (@lem4799316 _110654 (term79 _110654 s R R' x)). Qed.
Lemma lem4799318 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term150 _110654 s R R' x y) = (term78 _110654 s R R' x y).
Proof. exact (eq_refl (term150 _110654 s R R' x y)). Qed.
Lemma lem4799319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4799320 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term151 _110654 s R R' x y) = (term145 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4799319) (@lem4799318 _110654 s R R' x y)). Qed.
Lemma lem4799321 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term151 _110654 s R R' x y) = (term144 _110654 s R R' x y).
Proof. exact (TRANS (@lem4799320 _110654 s R R' x y) (@lem4799310 _110654 s R R' x y)). Qed.
Lemma lem4799322 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term152 _110654 s R R' x) = (term153 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799321 _110654 s R R' x y)). Qed.
Lemma lem4799323 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799324 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term149 _110654 s R R' x) = (term154 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799323 _110654) (@lem4799322 _110654 s R R' x)). Qed.
Lemma lem4799325 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term148 _110654 s R R' x) = (term154 _110654 s R R' x).
Proof. exact (TRANS (@lem4799317 _110654 s R R' x) (@lem4799324 _110654 s R R' x)). Qed.
Lemma lem4799326 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term79 _110654 s R R' x) = (term155 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799315 _110654 s R R' x y)). Qed.
Lemma lem4799327 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799328 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term80 _110654 s R R' x) = (term156 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799327 _110654) (@lem4799326 _110654 s R R' x)). Qed.
Lemma lem4799329 {_110654 : Type'} (P : _110654 -> Prop) : (term113 _110654 P) = (term114 _110654 P).
Proof. exact (@lem18392 _110654 P). Qed.
Lemma lem4799330 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term157 _110654 s R R') = (term158 _110654 s R R').
Proof. exact (@lem4799329 _110654 (term81 _110654 s R R')). Qed.
Lemma lem4799331 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term159 _110654 s R R' x) = (term80 _110654 s R R' x).
Proof. exact (eq_refl (term159 _110654 s R R' x)). Qed.
Lemma lem4799332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4799333 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term160 _110654 s R R' x) = (term148 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799332) (@lem4799331 _110654 s R R' x)). Qed.
Lemma lem4799334 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term160 _110654 s R R' x) = (term154 _110654 s R R' x).
Proof. exact (TRANS (@lem4799333 _110654 s R R' x) (@lem4799325 _110654 s R R' x)). Qed.
Lemma lem4799335 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term161 _110654 s R R') = (term162 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799334 _110654 s R R' x)). Qed.
Lemma lem4799336 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799337 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term158 _110654 s R R') = (term163 _110654 s R R').
Proof. exact (MK_COMB (@lem4799336 _110654) (@lem4799335 _110654 s R R')). Qed.
Lemma lem4799338 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term157 _110654 s R R') = (term163 _110654 s R R').
Proof. exact (TRANS (@lem4799330 _110654 s R R') (@lem4799337 _110654 s R R')). Qed.
Lemma lem4799339 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term81 _110654 s R R') = (term164 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799328 _110654 s R R' x)). Qed.
Lemma lem4799340 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799341 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term82 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (MK_COMB (@lem4799340 _110654) (@lem4799339 _110654 s R R')). Qed.
Lemma lem4799342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799343 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term166 _110654 R s R') = (term167 _110654 R s R').
Proof. exact (MK_COMB (@lem4799342) (@lem4799266 _110654 R s R')). Qed.
Lemma lem4799344 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term168 _110654 s R R') = (term169 _110654 s R R').
Proof. exact (MK_COMB (@lem4799343 _110654 R s R') (@lem4799341 _110654 s R R')). Qed.
Lemma lem4799345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799346 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term170 _110654 R s R') = (term171 _110654 R s R').
Proof. exact (MK_COMB (@lem4799345) (@lem4799269 _110654 R s R')). Qed.
Lemma lem4799347 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term172 _110654 s R R') = (term173 _110654 s R R').
Proof. exact (MK_COMB (@lem4799346 _110654 R s R') (@lem4799338 _110654 s R R')). Qed.
Lemma lem4799348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799349 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term174 _110654 s R R') = (term175 _110654 s R R').
Proof. exact (MK_COMB (@lem4799348) (@lem4799347 _110654 s R R')). Qed.
Lemma lem4799350 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term176 _110654 s R R') = (term177 _110654 s R R').
Proof. exact (MK_COMB (@lem4799349 _110654 s R R') (@lem4799344 _110654 s R R')). Qed.
Lemma lem4799351 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term98 _110654 s R R') = (term176 _110654 s R R').
Proof. exact (@lem17646 (term76 _110654 R s R') (term82 _110654 s R R')). Qed.
Lemma lem4799352 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term98 _110654 s R R') = (term177 _110654 s R R').
Proof. exact (TRANS (@lem4799351 _110654 s R R') (@lem4799350 _110654 s R R')). Qed.
Lemma lem4799667 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4799668 {_110654 : Type'} (P : Prop) (Q : _110654 -> Prop) : (term178 _110654 P Q) = (term179 _110654 P Q).
Proof. exact (@lem4799667 _110654 P Q). Qed.
Lemma lem4799669 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term180 _110654 s R R') = (term181 _110654 s R R').
Proof. exact (@lem4799668 _110654 (term139 _110654 R s R') (term162 _110654 s R R')). Qed.
Lemma lem4799670 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term182 _110654 s R R' x) = (term154 _110654 s R R' x).
Proof. exact (eq_refl (term182 _110654 s R R' x)). Qed.
Lemma lem4799671 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term183 _110654 s R R') = (term162 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799670 _110654 s R R' x)). Qed.
Lemma lem4799672 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799673 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term184 _110654 s R R') = (term163 _110654 s R R').
Proof. exact (MK_COMB (@lem4799672 _110654) (@lem4799671 _110654 s R R')). Qed.
Lemma lem4799674 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term171 _110654 R s R') = (term171 _110654 R s R').
Proof. exact (eq_refl (term171 _110654 R s R')). Qed.
Lemma lem4799675 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term180 _110654 s R R') = (term173 _110654 s R R').
Proof. exact (MK_COMB (@lem4799674 _110654 R s R') (@lem4799673 _110654 s R R')). Qed.
Lemma lem4799676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799677 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term185 _110654 s R R') = (term186 _110654 s R R').
Proof. exact (MK_COMB (@lem4799676) (@lem4799675 _110654 s R R')). Qed.
Lemma lem4799678 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term182 _110654 s R R' x) = (term154 _110654 s R R' x).
Proof. exact (eq_refl (term182 _110654 s R R' x)). Qed.
Lemma lem4799679 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term171 _110654 R s R') = (term171 _110654 R s R').
Proof. exact (eq_refl (term171 _110654 R s R')). Qed.
Lemma lem4799680 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term187 _110654 s R R' x) = (term188 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799679 _110654 R s R') (@lem4799678 _110654 s R R' x)). Qed.
Lemma lem4799681 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term189 _110654 s R R') = (term190 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799680 _110654 s R R' x)). Qed.
Lemma lem4799682 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799683 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term181 _110654 s R R') = (term191 _110654 s R R').
Proof. exact (MK_COMB (@lem4799682 _110654) (@lem4799681 _110654 s R R')). Qed.
Lemma lem4799684 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term180 _110654 s R R') = (term181 _110654 s R R')) = ((term173 _110654 s R R') = (term191 _110654 s R R')).
Proof. exact (MK_COMB (@lem4799677 _110654 s R R') (@lem4799683 _110654 s R R')). Qed.
Lemma lem4799685 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term173 _110654 s R R') = (term191 _110654 s R R').
Proof. exact (EQ_MP (@lem4799684 _110654 s R R') (@lem4799669 _110654 s R R')). Qed.
Lemma lem4799687 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4799688 {_110654 : Type'} (P : Prop) (Q : _110654 -> Prop) : (term178 _110654 P Q) = (term179 _110654 P Q).
Proof. exact (@lem4799687 _110654 P Q). Qed.
Lemma lem4799689 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term192 _110654 s R R' x) = (term193 _110654 s R R' x).
Proof. exact (@lem4799688 _110654 (term139 _110654 R s R') (term153 _110654 s R R' x)). Qed.
Lemma lem4799690 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term194 _110654 s R R' x y) = (term144 _110654 s R R' x y).
Proof. exact (eq_refl (term194 _110654 s R R' x y)). Qed.
Lemma lem4799691 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term195 _110654 s R R' x) = (term153 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799690 _110654 s R R' x y)). Qed.
Lemma lem4799692 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799693 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term196 _110654 s R R' x) = (term154 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799692 _110654) (@lem4799691 _110654 s R R' x)). Qed.
Lemma lem4799694 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term171 _110654 R s R') = (term171 _110654 R s R').
Proof. exact (eq_refl (term171 _110654 R s R')). Qed.
Lemma lem4799695 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term192 _110654 s R R' x) = (term188 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799694 _110654 R s R') (@lem4799693 _110654 s R R' x)). Qed.
Lemma lem4799696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799697 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term197 _110654 s R R' x) = (term198 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799696) (@lem4799695 _110654 s R R' x)). Qed.
Lemma lem4799698 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term194 _110654 s R R' x y) = (term144 _110654 s R R' x y).
Proof. exact (eq_refl (term194 _110654 s R R' x y)). Qed.
Lemma lem4799699 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term171 _110654 R s R') = (term171 _110654 R s R').
Proof. exact (eq_refl (term171 _110654 R s R')). Qed.
Lemma lem4799700 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term199 _110654 s R R' x y) = (term200 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4799699 _110654 R s R') (@lem4799698 _110654 s R R' x y)). Qed.
Lemma lem4799701 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term201 _110654 s R R' x) = (term202 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799700 _110654 s R R' x y)). Qed.
Lemma lem4799702 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799703 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term193 _110654 s R R' x) = (term203 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799702 _110654) (@lem4799701 _110654 s R R' x)). Qed.
Lemma lem4799704 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : ((term192 _110654 s R R' x) = (term193 _110654 s R R' x)) = ((term188 _110654 s R R' x) = (term203 _110654 s R R' x)).
Proof. exact (MK_COMB (@lem4799697 _110654 s R R' x) (@lem4799703 _110654 s R R' x)). Qed.
Lemma lem4799705 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term188 _110654 s R R' x) = (term203 _110654 s R R' x).
Proof. exact (EQ_MP (@lem4799704 _110654 s R R' x) (@lem4799689 _110654 s R R' x)). Qed.
Lemma lem4799706 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term190 _110654 s R R') = (term204 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799705 _110654 s R R' x)). Qed.
Lemma lem4799707 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799708 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term191 _110654 s R R') = (term205 _110654 s R R').
Proof. exact (MK_COMB (@lem4799707 _110654) (@lem4799706 _110654 s R R')). Qed.
Lemma lem4799709 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term173 _110654 s R R') = (term205 _110654 s R R').
Proof. exact (TRANS (@lem4799685 _110654 s R R') (@lem4799708 _110654 s R R')). Qed.
Lemma lem4799710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799711 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term175 _110654 s R R') = (term206 _110654 s R R').
Proof. exact (MK_COMB (@lem4799710) (@lem4799709 _110654 s R R')). Qed.
Lemma lem4799713 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4799714 {_110654 : Type'} (P : _110654 -> Prop) (Q : _110654 -> Prop) : (term207 _110654 P Q) = (term208 _110654 P Q).
Proof. exact (@lem4799713 _110654 P Q). Qed.
Lemma lem4799715 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term209 _110654 R s R') = (term210 _110654 R s R').
Proof. exact (@lem4799714 _110654 (term129 _110654 s R) (term129 _110654 s R')). Qed.
Lemma lem4799716 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term211 _110654 s R x) = (term121 _110654 s R x).
Proof. exact (eq_refl (term211 _110654 s R x)). Qed.
Lemma lem4799717 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term212 _110654 s R) = (term129 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4799716 _110654 s R x)). Qed.
Lemma lem4799718 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799719 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term213 _110654 s R) = (term130 _110654 s R).
Proof. exact (MK_COMB (@lem4799718 _110654) (@lem4799717 _110654 s R)). Qed.
Lemma lem4799720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799721 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term214 _110654 s R) = (term134 _110654 s R).
Proof. exact (MK_COMB (@lem4799720) (@lem4799719 _110654 s R)). Qed.
Lemma lem4799722 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term211 _110654 s R' x) = (term121 _110654 s R' x).
Proof. exact (eq_refl (term211 _110654 s R' x)). Qed.
Lemma lem4799723 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term212 _110654 s R') = (term129 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799722 _110654 s R' x)). Qed.
Lemma lem4799724 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799725 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term213 _110654 s R') = (term130 _110654 s R').
Proof. exact (MK_COMB (@lem4799724 _110654) (@lem4799723 _110654 s R')). Qed.
Lemma lem4799726 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term209 _110654 R s R') = (term136 _110654 R s R').
Proof. exact (MK_COMB (@lem4799721 _110654 s R) (@lem4799725 _110654 s R')). Qed.
Lemma lem4799727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799728 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term215 _110654 R s R') = (term216 _110654 R s R').
Proof. exact (MK_COMB (@lem4799727) (@lem4799726 _110654 R s R')). Qed.
Lemma lem4799729 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term211 _110654 s R x) = (term121 _110654 s R x).
Proof. exact (eq_refl (term211 _110654 s R x)). Qed.
Lemma lem4799730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799731 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term217 _110654 s R x) = (term218 _110654 s R x).
Proof. exact (MK_COMB (@lem4799730) (@lem4799729 _110654 s R x)). Qed.
Lemma lem4799732 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term211 _110654 s R' x) = (term121 _110654 s R' x).
Proof. exact (eq_refl (term211 _110654 s R' x)). Qed.
Lemma lem4799733 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term219 _110654 R s R' x) = (term220 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799731 _110654 s R x) (@lem4799732 _110654 s R' x)). Qed.
Lemma lem4799734 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term221 _110654 R s R') = (term222 _110654 R s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799733 _110654 R s R' x)). Qed.
Lemma lem4799735 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799736 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term210 _110654 R s R') = (term223 _110654 R s R').
Proof. exact (MK_COMB (@lem4799735 _110654) (@lem4799734 _110654 R s R')). Qed.
Lemma lem4799737 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : ((term209 _110654 R s R') = (term210 _110654 R s R')) = ((term136 _110654 R s R') = (term223 _110654 R s R')).
Proof. exact (MK_COMB (@lem4799728 _110654 R s R') (@lem4799736 _110654 R s R')). Qed.
Lemma lem4799738 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term136 _110654 R s R') = (term223 _110654 R s R').
Proof. exact (EQ_MP (@lem4799737 _110654 R s R') (@lem4799715 _110654 R s R')). Qed.
Lemma lem4799740 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4799741 {_110654 : Type'} (P : _110654 -> Prop) (Q : _110654 -> Prop) : (term207 _110654 P Q) = (term208 _110654 P Q).
Proof. exact (@lem4799740 _110654 P Q). Qed.
Lemma lem4799742 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term224 _110654 R s R' x) = (term225 _110654 R s R' x).
Proof. exact (@lem4799741 _110654 (term120 _110654 s R x) (term120 _110654 s R' x)). Qed.
Lemma lem4799743 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term226 _110654 s R x y) = (term108 _110654 s R x y).
Proof. exact (eq_refl (term226 _110654 s R x y)). Qed.
Lemma lem4799744 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term227 _110654 s R x) = (term120 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799743 _110654 s R x y)). Qed.
Lemma lem4799745 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799746 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term228 _110654 s R x) = (term121 _110654 s R x).
Proof. exact (MK_COMB (@lem4799745 _110654) (@lem4799744 _110654 s R x)). Qed.
Lemma lem4799747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799748 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term229 _110654 s R x) = (term218 _110654 s R x).
Proof. exact (MK_COMB (@lem4799747) (@lem4799746 _110654 s R x)). Qed.
Lemma lem4799749 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term226 _110654 s R' x y) = (term108 _110654 s R' x y).
Proof. exact (eq_refl (term226 _110654 s R' x y)). Qed.
Lemma lem4799750 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term227 _110654 s R' x) = (term120 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799749 _110654 s R' x y)). Qed.
Lemma lem4799751 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799752 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term228 _110654 s R' x) = (term121 _110654 s R' x).
Proof. exact (MK_COMB (@lem4799751 _110654) (@lem4799750 _110654 s R' x)). Qed.
Lemma lem4799753 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term224 _110654 R s R' x) = (term220 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799748 _110654 s R x) (@lem4799752 _110654 s R' x)). Qed.
Lemma lem4799754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799755 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term230 _110654 R s R' x) = (term231 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799754) (@lem4799753 _110654 R s R' x)). Qed.
Lemma lem4799756 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term226 _110654 s R x y) = (term108 _110654 s R x y).
Proof. exact (eq_refl (term226 _110654 s R x y)). Qed.
Lemma lem4799757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799758 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term232 _110654 s R x y) = (term233 _110654 s R x y).
Proof. exact (MK_COMB (@lem4799757) (@lem4799756 _110654 s R x y)). Qed.
Lemma lem4799759 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term226 _110654 s R' x y) = (term108 _110654 s R' x y).
Proof. exact (eq_refl (term226 _110654 s R' x y)). Qed.
Lemma lem4799760 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term234 _110654 R s R' x y) = (term235 _110654 R s R' x y).
Proof. exact (MK_COMB (@lem4799758 _110654 s R x y) (@lem4799759 _110654 s R' x y)). Qed.
Lemma lem4799761 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term236 _110654 R s R' x) = (term237 _110654 R s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799760 _110654 R s R' x y)). Qed.
Lemma lem4799762 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799763 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term225 _110654 R s R' x) = (term238 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799762 _110654) (@lem4799761 _110654 R s R' x)). Qed.
Lemma lem4799764 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : ((term224 _110654 R s R' x) = (term225 _110654 R s R' x)) = ((term220 _110654 R s R' x) = (term238 _110654 R s R' x)).
Proof. exact (MK_COMB (@lem4799755 _110654 R s R' x) (@lem4799763 _110654 R s R' x)). Qed.
Lemma lem4799765 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term220 _110654 R s R' x) = (term238 _110654 R s R' x).
Proof. exact (EQ_MP (@lem4799764 _110654 R s R' x) (@lem4799742 _110654 R s R' x)). Qed.
Lemma lem4799766 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term222 _110654 R s R') = (term239 _110654 R s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799765 _110654 R s R' x)). Qed.
Lemma lem4799767 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799768 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term223 _110654 R s R') = (term240 _110654 R s R').
Proof. exact (MK_COMB (@lem4799767 _110654) (@lem4799766 _110654 R s R')). Qed.
Lemma lem4799769 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term136 _110654 R s R') = (term240 _110654 R s R').
Proof. exact (TRANS (@lem4799738 _110654 R s R') (@lem4799768 _110654 R s R')). Qed.
Lemma lem4799770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799771 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term167 _110654 R s R') = (term241 _110654 R s R').
Proof. exact (MK_COMB (@lem4799770) (@lem4799769 _110654 R s R')). Qed.
Lemma lem4799772 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term165 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (eq_refl (term165 _110654 s R R')). Qed.
Lemma lem4799773 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term169 _110654 s R R') = (term242 _110654 s R R').
Proof. exact (MK_COMB (@lem4799771 _110654 R s R') (@lem4799772 _110654 s R R')). Qed.
Lemma lem4799775 {A : Type'} (P : A -> Prop) (Q : Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4799776 {_110654 : Type'} (P : _110654 -> Prop) (Q : Prop) : (term243 _110654 P Q) = (term244 _110654 P Q).
Proof. exact (@lem4799775 _110654 P Q). Qed.
Lemma lem4799777 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term245 _110654 s R R') = (term246 _110654 s R R').
Proof. exact (@lem4799776 _110654 (term239 _110654 R s R') (term165 _110654 s R R')). Qed.
Lemma lem4799778 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term247 _110654 R s R' x) = (term238 _110654 R s R' x).
Proof. exact (eq_refl (term247 _110654 R s R' x)). Qed.
Lemma lem4799779 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term248 _110654 R s R') = (term239 _110654 R s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799778 _110654 R s R' x)). Qed.
Lemma lem4799780 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799781 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term249 _110654 R s R') = (term240 _110654 R s R').
Proof. exact (MK_COMB (@lem4799780 _110654) (@lem4799779 _110654 R s R')). Qed.
Lemma lem4799782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799783 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term250 _110654 R s R') = (term241 _110654 R s R').
Proof. exact (MK_COMB (@lem4799782) (@lem4799781 _110654 R s R')). Qed.
Lemma lem4799784 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term165 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (eq_refl (term165 _110654 s R R')). Qed.
Lemma lem4799785 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term245 _110654 s R R') = (term242 _110654 s R R').
Proof. exact (MK_COMB (@lem4799783 _110654 R s R') (@lem4799784 _110654 s R R')). Qed.
Lemma lem4799786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799787 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term251 _110654 s R R') = (term252 _110654 s R R').
Proof. exact (MK_COMB (@lem4799786) (@lem4799785 _110654 s R R')). Qed.
Lemma lem4799788 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term247 _110654 R s R' x) = (term238 _110654 R s R' x).
Proof. exact (eq_refl (term247 _110654 R s R' x)). Qed.
Lemma lem4799789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799790 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term253 _110654 R s R' x) = (term254 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799789) (@lem4799788 _110654 R s R' x)). Qed.
Lemma lem4799791 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term165 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (eq_refl (term165 _110654 s R R')). Qed.
Lemma lem4799792 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term255 _110654 x s R R') = (term256 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799790 _110654 R s R' x) (@lem4799791 _110654 s R R')). Qed.
Lemma lem4799793 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term257 _110654 s R R') = (term258 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799792 _110654 x s R R')). Qed.
Lemma lem4799794 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799795 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term246 _110654 s R R') = (term259 _110654 s R R').
Proof. exact (MK_COMB (@lem4799794 _110654) (@lem4799793 _110654 s R R')). Qed.
Lemma lem4799796 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term245 _110654 s R R') = (term246 _110654 s R R')) = ((term242 _110654 s R R') = (term259 _110654 s R R')).
Proof. exact (MK_COMB (@lem4799787 _110654 s R R') (@lem4799795 _110654 s R R')). Qed.
Lemma lem4799797 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term242 _110654 s R R') = (term259 _110654 s R R').
Proof. exact (EQ_MP (@lem4799796 _110654 s R R') (@lem4799777 _110654 s R R')). Qed.
Lemma lem4799799 {A : Type'} (P : A -> Prop) (Q : Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4799800 {_110654 : Type'} (P : _110654 -> Prop) (Q : Prop) : (term243 _110654 P Q) = (term244 _110654 P Q).
Proof. exact (@lem4799799 _110654 P Q). Qed.
Lemma lem4799801 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term260 _110654 x s R R') = (term261 _110654 x s R R').
Proof. exact (@lem4799800 _110654 (term237 _110654 R s R' x) (term165 _110654 s R R')). Qed.
Lemma lem4799802 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term262 _110654 R s R' x y) = (term235 _110654 R s R' x y).
Proof. exact (eq_refl (term262 _110654 R s R' x y)). Qed.
Lemma lem4799803 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term263 _110654 R s R' x) = (term237 _110654 R s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799802 _110654 R s R' x y)). Qed.
Lemma lem4799804 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799805 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term264 _110654 R s R' x) = (term238 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799804 _110654) (@lem4799803 _110654 R s R' x)). Qed.
Lemma lem4799806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799807 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term265 _110654 R s R' x) = (term254 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4799806) (@lem4799805 _110654 R s R' x)). Qed.
Lemma lem4799808 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term165 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (eq_refl (term165 _110654 s R R')). Qed.
Lemma lem4799809 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term260 _110654 x s R R') = (term256 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799807 _110654 R s R' x) (@lem4799808 _110654 s R R')). Qed.
Lemma lem4799810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799811 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term266 _110654 x s R R') = (term267 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799810) (@lem4799809 _110654 x s R R')). Qed.
Lemma lem4799812 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term262 _110654 R s R' x y) = (term235 _110654 R s R' x y).
Proof. exact (eq_refl (term262 _110654 R s R' x y)). Qed.
Lemma lem4799813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4799814 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term268 _110654 R s R' x y) = (term269 _110654 R s R' x y).
Proof. exact (MK_COMB (@lem4799813) (@lem4799812 _110654 R s R' x y)). Qed.
Lemma lem4799815 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term165 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (eq_refl (term165 _110654 s R R')). Qed.
Lemma lem4799816 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term270 _110654 x y s R R') = (term271 _110654 x y s R R').
Proof. exact (MK_COMB (@lem4799814 _110654 R s R' x y) (@lem4799815 _110654 s R R')). Qed.
Lemma lem4799817 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term272 _110654 x s R R') = (term273 _110654 x s R R').
Proof. exact (fun_ext (fun y : _110654 => @lem4799816 _110654 x y s R R')). Qed.
Lemma lem4799818 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799819 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term261 _110654 x s R R') = (term274 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799818 _110654) (@lem4799817 _110654 x s R R')). Qed.
Lemma lem4799820 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term260 _110654 x s R R') = (term261 _110654 x s R R')) = ((term256 _110654 x s R R') = (term274 _110654 x s R R')).
Proof. exact (MK_COMB (@lem4799811 _110654 x s R R') (@lem4799819 _110654 x s R R')). Qed.
Lemma lem4799821 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term256 _110654 x s R R') = (term274 _110654 x s R R').
Proof. exact (EQ_MP (@lem4799820 _110654 x s R R') (@lem4799801 _110654 x s R R')). Qed.
Lemma lem4799822 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term258 _110654 s R R') = (term275 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799821 _110654 x s R R')). Qed.
Lemma lem4799823 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799824 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term259 _110654 s R R') = (term276 _110654 s R R').
Proof. exact (MK_COMB (@lem4799823 _110654) (@lem4799822 _110654 s R R')). Qed.
Lemma lem4799825 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term242 _110654 s R R') = (term276 _110654 s R R').
Proof. exact (TRANS (@lem4799797 _110654 s R R') (@lem4799824 _110654 s R R')). Qed.
Lemma lem4799826 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term169 _110654 s R R') = (term276 _110654 s R R').
Proof. exact (TRANS (@lem4799773 _110654 s R R') (@lem4799825 _110654 s R R')). Qed.
Lemma lem4799827 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term177 _110654 s R R') = (term277 _110654 s R R').
Proof. exact (MK_COMB (@lem4799711 _110654 s R R') (@lem4799826 _110654 s R R')). Qed.
Lemma lem4799829 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4799830 {_110654 : Type'} (P : _110654 -> Prop) (Q : _110654 -> Prop) : (term207 _110654 P Q) = (term208 _110654 P Q).
Proof. exact (@lem4799829 _110654 P Q). Qed.
Lemma lem4799831 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term278 _110654 s R R') = (term279 _110654 s R R').
Proof. exact (@lem4799830 _110654 (term204 _110654 s R R') (term275 _110654 s R R')). Qed.
Lemma lem4799832 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term280 _110654 s R R' x) = (term203 _110654 s R R' x).
Proof. exact (eq_refl (term280 _110654 s R R' x)). Qed.
Lemma lem4799833 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term281 _110654 s R R') = (term204 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799832 _110654 s R R' x)). Qed.
Lemma lem4799834 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799835 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term282 _110654 s R R') = (term205 _110654 s R R').
Proof. exact (MK_COMB (@lem4799834 _110654) (@lem4799833 _110654 s R R')). Qed.
Lemma lem4799836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799837 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term283 _110654 s R R') = (term206 _110654 s R R').
Proof. exact (MK_COMB (@lem4799836) (@lem4799835 _110654 s R R')). Qed.
Lemma lem4799838 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term284 _110654 s R R' x) = (term274 _110654 x s R R').
Proof. exact (eq_refl (term284 _110654 s R R' x)). Qed.
Lemma lem4799839 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term285 _110654 s R R') = (term275 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799838 _110654 x s R R')). Qed.
Lemma lem4799840 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799841 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term286 _110654 s R R') = (term276 _110654 s R R').
Proof. exact (MK_COMB (@lem4799840 _110654) (@lem4799839 _110654 s R R')). Qed.
Lemma lem4799842 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term278 _110654 s R R') = (term277 _110654 s R R').
Proof. exact (MK_COMB (@lem4799837 _110654 s R R') (@lem4799841 _110654 s R R')). Qed.
Lemma lem4799843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799844 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term287 _110654 s R R') = (term288 _110654 s R R').
Proof. exact (MK_COMB (@lem4799843) (@lem4799842 _110654 s R R')). Qed.
Lemma lem4799845 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term280 _110654 s R R' x) = (term203 _110654 s R R' x).
Proof. exact (eq_refl (term280 _110654 s R R' x)). Qed.
Lemma lem4799846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799847 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term289 _110654 s R R' x) = (term290 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799846) (@lem4799845 _110654 s R R' x)). Qed.
Lemma lem4799848 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term284 _110654 s R R' x) = (term274 _110654 x s R R').
Proof. exact (eq_refl (term284 _110654 s R R' x)). Qed.
Lemma lem4799849 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term291 _110654 s R R' x) = (term292 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799847 _110654 s R R' x) (@lem4799848 _110654 x s R R')). Qed.
Lemma lem4799850 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term293 _110654 s R R') = (term294 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799849 _110654 x s R R')). Qed.
Lemma lem4799851 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799852 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term279 _110654 s R R') = (term295 _110654 s R R').
Proof. exact (MK_COMB (@lem4799851 _110654) (@lem4799850 _110654 s R R')). Qed.
Lemma lem4799853 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term278 _110654 s R R') = (term279 _110654 s R R')) = ((term277 _110654 s R R') = (term295 _110654 s R R')).
Proof. exact (MK_COMB (@lem4799844 _110654 s R R') (@lem4799852 _110654 s R R')). Qed.
Lemma lem4799854 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term277 _110654 s R R') = (term295 _110654 s R R').
Proof. exact (EQ_MP (@lem4799853 _110654 s R R') (@lem4799831 _110654 s R R')). Qed.
Lemma lem4799856 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4799857 {_110654 : Type'} (P : _110654 -> Prop) (Q : _110654 -> Prop) : (term207 _110654 P Q) = (term208 _110654 P Q).
Proof. exact (@lem4799856 _110654 P Q). Qed.
Lemma lem4799858 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term296 _110654 x s R R') = (term297 _110654 x s R R').
Proof. exact (@lem4799857 _110654 (term202 _110654 s R R' x) (term273 _110654 x s R R')). Qed.
Lemma lem4799859 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term298 _110654 s R R' x y) = (term200 _110654 s R R' x y).
Proof. exact (eq_refl (term298 _110654 s R R' x y)). Qed.
Lemma lem4799860 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term299 _110654 s R R' x) = (term202 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799859 _110654 s R R' x y)). Qed.
Lemma lem4799861 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799862 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term300 _110654 s R R' x) = (term203 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799861 _110654) (@lem4799860 _110654 s R R' x)). Qed.
Lemma lem4799863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799864 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term301 _110654 s R R' x) = (term290 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799863) (@lem4799862 _110654 s R R' x)). Qed.
Lemma lem4799865 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term302 _110654 x s R R' y) = (term271 _110654 x y s R R').
Proof. exact (eq_refl (term302 _110654 x s R R' y)). Qed.
Lemma lem4799866 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term303 _110654 x s R R') = (term273 _110654 x s R R').
Proof. exact (fun_ext (fun y : _110654 => @lem4799865 _110654 x y s R R')). Qed.
Lemma lem4799867 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799868 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term304 _110654 x s R R') = (term274 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799867 _110654) (@lem4799866 _110654 x s R R')). Qed.
Lemma lem4799869 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term296 _110654 x s R R') = (term292 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799864 _110654 s R R' x) (@lem4799868 _110654 x s R R')). Qed.
Lemma lem4799870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4799871 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term305 _110654 x s R R') = (term306 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799870) (@lem4799869 _110654 x s R R')). Qed.
Lemma lem4799872 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term298 _110654 s R R' x y) = (term200 _110654 s R R' x y).
Proof. exact (eq_refl (term298 _110654 s R R' x y)). Qed.
Lemma lem4799873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4799874 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term307 _110654 s R R' x y) = (term308 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4799873) (@lem4799872 _110654 s R R' x y)). Qed.
Lemma lem4799875 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term302 _110654 x s R R' y) = (term271 _110654 x y s R R').
Proof. exact (eq_refl (term302 _110654 x s R R' y)). Qed.
Lemma lem4799876 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term309 _110654 x s R R' y) = (term310 _110654 x y s R R').
Proof. exact (MK_COMB (@lem4799874 _110654 s R R' x y) (@lem4799875 _110654 x y s R R')). Qed.
Lemma lem4799877 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term311 _110654 x s R R') = (term312 _110654 x s R R').
Proof. exact (fun_ext (fun y : _110654 => @lem4799876 _110654 x y s R R')). Qed.
Lemma lem4799878 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799879 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term297 _110654 x s R R') = (term313 _110654 x s R R').
Proof. exact (MK_COMB (@lem4799878 _110654) (@lem4799877 _110654 x s R R')). Qed.
Lemma lem4799880 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : ((term296 _110654 x s R R') = (term297 _110654 x s R R')) = ((term292 _110654 x s R R') = (term313 _110654 x s R R')).
Proof. exact (MK_COMB (@lem4799871 _110654 x s R R') (@lem4799879 _110654 x s R R')). Qed.
Lemma lem4799881 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term292 _110654 x s R R') = (term313 _110654 x s R R').
Proof. exact (EQ_MP (@lem4799880 _110654 x s R R') (@lem4799858 _110654 x s R R')). Qed.
Lemma lem4799882 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term294 _110654 s R R') = (term314 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799881 _110654 x s R R')). Qed.
Lemma lem4799883 {_110654 : Type'} : (@ex _110654) = (@ex _110654).
Proof. exact (eq_refl (@ex _110654)). Qed.
Lemma lem4799884 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term295 _110654 s R R') = (term315 _110654 s R R').
Proof. exact (MK_COMB (@lem4799883 _110654) (@lem4799882 _110654 s R R')). Qed.
Lemma lem4799885 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term277 _110654 s R R') = (term315 _110654 s R R').
Proof. exact (TRANS (@lem4799854 _110654 s R R') (@lem4799884 _110654 s R R')). Qed.
Lemma lem4799887 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term177 _110654 s R R') = (term315 _110654 s R R').
Proof. exact (TRANS (@lem4799827 _110654 s R R') (@lem4799885 _110654 s R R')). Qed.
Lemma lem4799888 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term98 _110654 s R R') = (term315 _110654 s R R').
Proof. exact (TRANS (@lem4799352 _110654 s R R') (@lem4799887 _110654 s R R')). Qed.
Lemma lem4799889 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term98 _110654 s R R') : term315 _110654 s R R'.
Proof. exact (EQ_MP (@lem4799888 _110654 s R R') (@lem4799137 _110654 s R R' h1)). Qed.
Lemma lem4799890 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term313 _110654 x s R R') : term313 _110654 x s R R'.
Proof. exact (h1). Qed.
Lemma lem4799891 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term310 _110654 x y s R R') : term310 _110654 x y s R R'.
Proof. exact (h1). Qed.
Lemma lem4799928 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term147 _110654 s R R' x y) = (term147 _110654 s R R' x y).
Proof. exact (eq_refl (term147 _110654 s R R' x y)). Qed.
Lemma lem4799929 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term155 _110654 s R R' x) = (term155 _110654 s R R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4799928 _110654 s R R' x y)). Qed.
Lemma lem4799930 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799931 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) : (term156 _110654 s R R' x) = (term156 _110654 s R R' x).
Proof. exact (MK_COMB (@lem4799930 _110654) (@lem4799929 _110654 s R R' x)). Qed.
Lemma lem4799932 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term164 _110654 s R R') = (term164 _110654 s R R').
Proof. exact (fun_ext (fun x : _110654 => @lem4799931 _110654 s R R' x)). Qed.
Lemma lem4799933 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4799934 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term165 _110654 s R R') = (term165 _110654 s R R').
Proof. exact (MK_COMB (@lem4799933 _110654) (@lem4799932 _110654 s R R')). Qed.
Lemma lem4799997 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term269 _110654 R s R' x y) = (term269 _110654 R s R' x y).
Proof. exact (eq_refl (term269 _110654 R s R' x y)). Qed.
Lemma lem4799998 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term271 _110654 x y s R R') = (term271 _110654 x y s R R').
Proof. exact (MK_COMB (@lem4799997 _110654 R s R' x y) (@lem4799934 _110654 s R R')). Qed.
Lemma lem4800037 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term144 _110654 s R R' x y) = (term144 _110654 s R R' x y).
Proof. exact (eq_refl (term144 _110654 s R R' x y)). Qed.
Lemma lem4800066 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term112 _110654 s R' x y) = (term112 _110654 s R' x y).
Proof. exact (eq_refl (term112 _110654 s R' x y)). Qed.
Lemma lem4800067 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term122 _110654 s R' x) = (term122 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4800066 _110654 s R' x y)). Qed.
Lemma lem4800068 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800069 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term123 _110654 s R' x) = (term123 _110654 s R' x).
Proof. exact (MK_COMB (@lem4800068 _110654) (@lem4800067 _110654 s R' x)). Qed.
Lemma lem4800070 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term131 _110654 s R') = (term131 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4800069 _110654 s R' x)). Qed.
Lemma lem4800071 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800072 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term132 _110654 s R') = (term132 _110654 s R').
Proof. exact (MK_COMB (@lem4800071 _110654) (@lem4800070 _110654 s R')). Qed.
Lemma lem4800101 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term112 _110654 s R x y) = (term112 _110654 s R x y).
Proof. exact (eq_refl (term112 _110654 s R x y)). Qed.
Lemma lem4800102 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term122 _110654 s R x) = (term122 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4800101 _110654 s R x y)). Qed.
Lemma lem4800103 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800104 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term123 _110654 s R x) = (term123 _110654 s R x).
Proof. exact (MK_COMB (@lem4800103 _110654) (@lem4800102 _110654 s R x)). Qed.
Lemma lem4800105 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term131 _110654 s R) = (term131 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4800104 _110654 s R x)). Qed.
Lemma lem4800106 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800107 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term132 _110654 s R) = (term132 _110654 s R).
Proof. exact (MK_COMB (@lem4800106 _110654) (@lem4800105 _110654 s R)). Qed.
Lemma lem4800108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4800109 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term138 _110654 s R) = (term138 _110654 s R).
Proof. exact (MK_COMB (@lem4800108) (@lem4800107 _110654 s R)). Qed.
Lemma lem4800110 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term139 _110654 R s R') = (term139 _110654 R s R').
Proof. exact (MK_COMB (@lem4800109 _110654 s R) (@lem4800072 _110654 s R')). Qed.
Lemma lem4800111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4800112 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term171 _110654 R s R') = (term171 _110654 R s R').
Proof. exact (MK_COMB (@lem4800111) (@lem4800110 _110654 R s R')). Qed.
Lemma lem4800113 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term200 _110654 s R R' x y) = (term200 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4800112 _110654 R s R') (@lem4800037 _110654 s R R' x y)). Qed.
Lemma lem4800114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4800115 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term308 _110654 s R R' x y) = (term308 _110654 s R R' x y).
Proof. exact (MK_COMB (@lem4800114) (@lem4800113 _110654 s R R' x y)). Qed.
Lemma lem4800116 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term310 _110654 x y s R R') = (term310 _110654 x y s R R').
Proof. exact (MK_COMB (@lem4800115 _110654 s R R' x y) (@lem4799998 _110654 x y s R R')). Qed.
Lemma lem4800117 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term310 _110654 x y s R R') : term310 _110654 x y s R R'.
Proof. exact (EQ_MP (@lem4800116 _110654 x y s R R') (@lem4799891 _110654 x y s R R' h1)). Qed.
Lemma lem4800118 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term200 _110654 s R R' x y.
Proof. exact (h1). Qed.
Lemma lem4800119 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term271 _110654 x y s R R'.
Proof. exact (h1). Qed.
Lemma lem4800120 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term144 _110654 s R R' x y.
Proof. exact (proj2 (@lem4800118 _110654 s R R' x y h1)). Qed.
Lemma lem4800121 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term139 _110654 R s R'.
Proof. exact (proj1 (@lem4800118 _110654 s R R' x y h1)). Qed.
Lemma lem4800122 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term141 _110654 R R' x y.
Proof. exact (proj2 (@lem4800120 _110654 s R R' x y h1)). Qed.
Lemma lem4800123 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term64 _110654 s x y.
Proof. exact (proj1 (@lem4800120 _110654 s R R' x y h1)). Qed.
Lemma lem4800124 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term62 _110654 s x y.
Proof. exact (proj2 (@lem4800123 _110654 s R R' x y h1)). Qed.
Lemma lem4800128 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term132 _110654 s R'.
Proof. exact (proj2 (@lem4800121 _110654 s R R' x y h1)). Qed.
Lemma lem4800129 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term132 _110654 s R.
Proof. exact (proj1 (@lem4800121 _110654 s R R' x y h1)). Qed.
Lemma lem4800132 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term165 _110654 s R R'.
Proof. exact (proj2 (@lem4800119 _110654 x y s R R' h1)). Qed.
Lemma lem4800133 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term235 _110654 R s R' x y.
Proof. exact (proj1 (@lem4800119 _110654 x y s R R' h1)). Qed.
Lemma lem4800134 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term108 _110654 s R x y.
Proof. exact (h1). Qed.
Lemma lem4800135 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term108 _110654 s R' x y.
Proof. exact (h1). Qed.
Lemma lem4800137 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term64 _110654 s x y.
Proof. exact (proj1 (@lem4800134 _110654 s R x y h1)). Qed.
Lemma lem4800138 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term62 _110654 s x y.
Proof. exact (proj2 (@lem4800137 _110654 s R x y h1)). Qed.
Lemma lem4800143 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term64 _110654 s x y.
Proof. exact (proj1 (@lem4800135 _110654 s R' x y h1)). Qed.
Lemma lem4800144 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term62 _110654 s x y.
Proof. exact (proj2 (@lem4800143 _110654 s R' x y h1)). Qed.
Lemma lem4800179 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) : (term112 _110654 s R x y) = (term112 _110654 s R x y).
Proof. exact (eq_refl (term112 _110654 s R x y)). Qed.
Lemma lem4800180 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term122 _110654 s R x) = (term122 _110654 s R x).
Proof. exact (fun_ext (fun y : _110654 => @lem4800179 _110654 s R x y)). Qed.
Lemma lem4800181 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800182 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) : (term123 _110654 s R x) = (term123 _110654 s R x).
Proof. exact (MK_COMB (@lem4800181 _110654) (@lem4800180 _110654 s R x)). Qed.
Lemma lem4800183 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term131 _110654 s R) = (term131 _110654 s R).
Proof. exact (fun_ext (fun x : _110654 => @lem4800182 _110654 s R x)). Qed.
Lemma lem4800184 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800186 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) : (term132 _110654 s R) = (term132 _110654 s R).
Proof. exact (MK_COMB (@lem4800184 _110654) (@lem4800183 _110654 s R)). Qed.
Lemma lem4800187 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term132 _110654 s R.
Proof. exact (EQ_MP (@lem4800186 _110654 s R) (@lem4800129 _110654 s R R' x y h1)). Qed.
Lemma lem4800219 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) : term316 _110654 R x y.
Proof. exact (h1). Qed.
Lemma lem4800279 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term112 _110654 s R' x y) = (term112 _110654 s R' x y).
Proof. exact (eq_refl (term112 _110654 s R' x y)). Qed.
Lemma lem4800280 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term122 _110654 s R' x) = (term122 _110654 s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4800279 _110654 s R' x y)). Qed.
Lemma lem4800281 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800282 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term123 _110654 s R' x) = (term123 _110654 s R' x).
Proof. exact (MK_COMB (@lem4800281 _110654) (@lem4800280 _110654 s R' x)). Qed.
Lemma lem4800283 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term131 _110654 s R') = (term131 _110654 s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4800282 _110654 s R' x)). Qed.
Lemma lem4800284 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800286 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) : (term132 _110654 s R') = (term132 _110654 s R').
Proof. exact (MK_COMB (@lem4800284 _110654) (@lem4800283 _110654 s R')). Qed.
Lemma lem4800287 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term132 _110654 s R'.
Proof. exact (EQ_MP (@lem4800286 _110654 s R') (@lem4800128 _110654 s R R' x y h1)). Qed.
Lemma lem4800291 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) : term316 _110654 R' x y.
Proof. exact (h1). Qed.
Lemma lem4800321 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term147 _110654 s R R' x y) = (term317 _110654 R s R' x y).
Proof. exact (@lem19490 (R x y) (term105 _110654 s x y) (R' x y)). Qed.
Lemma lem4800322 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term155 _110654 s R R' x) = (term318 _110654 R s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4800321 _110654 R s R' x y)). Qed.
Lemma lem4800323 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800324 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term156 _110654 s R R' x) = (term319 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4800323 _110654) (@lem4800322 _110654 R s R' x)). Qed.
Lemma lem4800325 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term164 _110654 s R R') = (term320 _110654 R s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4800324 _110654 R s R' x)). Qed.
Lemma lem4800326 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800328 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term165 _110654 s R R') = (term321 _110654 R s R').
Proof. exact (MK_COMB (@lem4800326 _110654) (@lem4800325 _110654 R s R')). Qed.
Lemma lem4800329 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term321 _110654 R s R'.
Proof. exact (EQ_MP (@lem4800328 _110654 R s R') (@lem4800132 _110654 x y s R R' h1)). Qed.
Lemma lem4800375 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) : (term147 _110654 s R R' x y) = (term317 _110654 R s R' x y).
Proof. exact (@lem19490 (R x y) (term105 _110654 s x y) (R' x y)). Qed.
Lemma lem4800376 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term155 _110654 s R R' x) = (term318 _110654 R s R' x).
Proof. exact (fun_ext (fun y : _110654 => @lem4800375 _110654 R s R' x y)). Qed.
Lemma lem4800377 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800378 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) : (term156 _110654 s R R' x) = (term319 _110654 R s R' x).
Proof. exact (MK_COMB (@lem4800377 _110654) (@lem4800376 _110654 R s R' x)). Qed.
Lemma lem4800379 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term164 _110654 s R R') = (term320 _110654 R s R').
Proof. exact (fun_ext (fun x : _110654 => @lem4800378 _110654 R s R' x)). Qed.
Lemma lem4800380 {_110654 : Type'} : (@all _110654) = (@all _110654).
Proof. exact (eq_refl (@all _110654)). Qed.
Lemma lem4800382 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) : (term165 _110654 s R R') = (term321 _110654 R s R').
Proof. exact (MK_COMB (@lem4800380 _110654) (@lem4800379 _110654 R s R')). Qed.
Lemma lem4800383 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term321 _110654 R s R'.
Proof. exact (EQ_MP (@lem4800382 _110654 R s R') (@lem4800132 _110654 x y s R R' h1)). Qed.
Lemma lem4800400 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term322 _110654 s R _59374.
Proof. exact (@lem4800187 _110654 s R R' x y h1 _59374). Qed.
Lemma lem4800401 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) : (term322 _110654 s R _59374) = (term123 _110654 s R _59374).
Proof. exact (eq_refl (term322 _110654 s R _59374)). Qed.
Lemma lem4800402 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term123 _110654 s R _59374.
Proof. exact (EQ_MP (@lem4800401 _110654 s R _59374) (@lem4800400 _110654 _59374 s R R' x y h1)). Qed.
Lemma lem4800403 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term323 _110654 s R _59374 _59375.
Proof. exact (@lem4800402 _110654 _59374 s R R' x y h1 _59375). Qed.
Lemma lem4800404 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term323 _110654 s R _59374 _59375) = (term112 _110654 s R _59374 _59375).
Proof. exact (eq_refl (term323 _110654 s R _59374 _59375)). Qed.
Lemma lem4800405 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term112 _110654 s R _59374 _59375.
Proof. exact (EQ_MP (@lem4800404 _110654 s R _59374 _59375) (@lem4800403 _110654 _59374 _59375 s R R' x y h1)). Qed.
Lemma lem4800418 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term322 _110654 s R' _59380.
Proof. exact (@lem4800287 _110654 s R R' x y h1 _59380). Qed.
Lemma lem4800419 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) : (term322 _110654 s R' _59380) = (term123 _110654 s R' _59380).
Proof. exact (eq_refl (term322 _110654 s R' _59380)). Qed.
Lemma lem4800420 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term123 _110654 s R' _59380.
Proof. exact (EQ_MP (@lem4800419 _110654 s R' _59380) (@lem4800418 _110654 _59380 s R R' x y h1)). Qed.
Lemma lem4800421 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term323 _110654 s R' _59380 _59381.
Proof. exact (@lem4800420 _110654 _59380 s R R' x y h1 _59381). Qed.
Lemma lem4800422 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term323 _110654 s R' _59380 _59381) = (term112 _110654 s R' _59380 _59381).
Proof. exact (eq_refl (term323 _110654 s R' _59380 _59381)). Qed.
Lemma lem4800423 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term112 _110654 s R' _59380 _59381.
Proof. exact (EQ_MP (@lem4800422 _110654 s R' _59380 _59381) (@lem4800421 _110654 _59380 _59381 s R R' x y h1)). Qed.
Lemma lem4800424 {_110654 : Type'} (_59382 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term324 _110654 R s R' _59382.
Proof. exact (@lem4800329 _110654 x y s R R' h1 _59382). Qed.
Lemma lem4800425 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (_59382 : _110654) : (term324 _110654 R s R' _59382) = (term319 _110654 R s R' _59382).
Proof. exact (eq_refl (term324 _110654 R s R' _59382)). Qed.
Lemma lem4800426 {_110654 : Type'} (_59382 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term319 _110654 R s R' _59382.
Proof. exact (EQ_MP (@lem4800425 _110654 R s R' _59382) (@lem4800424 _110654 _59382 x y s R R' h1)). Qed.
Lemma lem4800427 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term325 _110654 R s R' _59382 _59383.
Proof. exact (@lem4800426 _110654 _59382 x y s R R' h1 _59383). Qed.
Lemma lem4800428 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term325 _110654 R s R' _59382 _59383) = (term317 _110654 R s R' _59382 _59383).
Proof. exact (eq_refl (term325 _110654 R s R' _59382 _59383)). Qed.
Lemma lem4800429 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term317 _110654 R s R' _59382 _59383.
Proof. exact (EQ_MP (@lem4800428 _110654 R s R' _59382 _59383) (@lem4800427 _110654 _59382 _59383 x y s R R' h1)). Qed.
Lemma lem4800430 {_110654 : Type'} (_59384 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term324 _110654 R s R' _59384.
Proof. exact (@lem4800383 _110654 x y s R R' h1 _59384). Qed.
Lemma lem4800431 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) : (term324 _110654 R s R' _59384) = (term319 _110654 R s R' _59384).
Proof. exact (eq_refl (term324 _110654 R s R' _59384)). Qed.
Lemma lem4800432 {_110654 : Type'} (_59384 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term319 _110654 R s R' _59384.
Proof. exact (EQ_MP (@lem4800431 _110654 R s R' _59384) (@lem4800430 _110654 _59384 x y s R R' h1)). Qed.
Lemma lem4800433 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term325 _110654 R s R' _59384 _59385.
Proof. exact (@lem4800432 _110654 _59384 x y s R R' h1 _59385). Qed.
Lemma lem4800434 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term325 _110654 R s R' _59384 _59385) = (term317 _110654 R s R' _59384 _59385).
Proof. exact (eq_refl (term325 _110654 R s R' _59384 _59385)). Qed.
Lemma lem4800435 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term317 _110654 R s R' _59384 _59385.
Proof. exact (EQ_MP (@lem4800434 _110654 R s R' _59384 _59385) (@lem4800433 _110654 _59384 _59385 x y s R R' h1)). Qed.
Lemma lem4800437 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term112 _110654 s R _59382 _59383.
Proof. exact (proj1 (@lem4800429 _110654 _59382 _59383 x y s R R' h1)). Qed.
Lemma lem4800438 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term112 _110654 s R' _59384 _59385.
Proof. exact (proj2 (@lem4800435 _110654 _59384 _59385 x y s R R' h1)). Qed.
Lemma lem4800449 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term112 _110654 s R _59374 _59375) = (term326 _110654 s R _59374 _59375).
Proof. exact (@lem4798423 (term327 _110654 s _59374) (term102 _110654 s _59374 _59375) (R _59374 _59375)). Qed.
Lemma lem4800456 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term328 _110654 s R _59374 _59375) = (term329 _110654 s R _59374 _59375).
Proof. exact (@lem4798423 (term327 _110654 s _59375) (_59374 = _59375) (R _59374 _59375)). Qed.
Lemma lem4800457 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) : (term100 _110654 s _59374) = (term100 _110654 s _59374).
Proof. exact (eq_refl (term100 _110654 s _59374)). Qed.
Lemma lem4800460 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term326 _110654 s R _59374 _59375) = (term330 _110654 s R _59374 _59375).
Proof. exact (MK_COMB (@lem4800457 _110654 s _59374) (@lem4800456 _110654 s R _59374 _59375)). Qed.
Lemma lem4800462 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term112 _110654 s R _59374 _59375) = (term330 _110654 s R _59374 _59375).
Proof. exact (TRANS (@lem4800449 _110654 s R _59374 _59375) (@lem4800460 _110654 s R _59374 _59375)). Qed.
Lemma lem4800463 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term330 _110654 s R _59374 _59375.
Proof. exact (EQ_MP (@lem4800462 _110654 s R _59374 _59375) (@lem4800405 _110654 _59374 _59375 s R R' x y h1)). Qed.
Lemma lem4800483 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) : term316 _110654 R x y.
Proof. exact (h1). Qed.
Lemma lem4800511 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term112 _110654 s R' _59380 _59381) = (term326 _110654 s R' _59380 _59381).
Proof. exact (@lem4798423 (term327 _110654 s _59380) (term102 _110654 s _59380 _59381) (R' _59380 _59381)). Qed.
Lemma lem4800518 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term328 _110654 s R' _59380 _59381) = (term329 _110654 s R' _59380 _59381).
Proof. exact (@lem4798423 (term327 _110654 s _59381) (_59380 = _59381) (R' _59380 _59381)). Qed.
Lemma lem4800519 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) : (term100 _110654 s _59380) = (term100 _110654 s _59380).
Proof. exact (eq_refl (term100 _110654 s _59380)). Qed.
Lemma lem4800522 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term326 _110654 s R' _59380 _59381) = (term330 _110654 s R' _59380 _59381).
Proof. exact (MK_COMB (@lem4800519 _110654 s _59380) (@lem4800518 _110654 s R' _59380 _59381)). Qed.
Lemma lem4800524 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term112 _110654 s R' _59380 _59381) = (term330 _110654 s R' _59380 _59381).
Proof. exact (TRANS (@lem4800511 _110654 s R' _59380 _59381) (@lem4800522 _110654 s R' _59380 _59381)). Qed.
Lemma lem4800525 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term330 _110654 s R' _59380 _59381.
Proof. exact (EQ_MP (@lem4800524 _110654 s R' _59380 _59381) (@lem4800423 _110654 _59380 _59381 s R R' x y h1)). Qed.
Lemma lem4800527 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) : term316 _110654 R' x y.
Proof. exact (h1). Qed.
Lemma lem4800535 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term60 _110654 x y.
Proof. exact (proj2 (@lem4800138 _110654 s R x y h1)). Qed.
Lemma lem4800539 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term112 _110654 s R _59382 _59383) = (term326 _110654 s R _59382 _59383).
Proof. exact (@lem4798423 (term327 _110654 s _59382) (term102 _110654 s _59382 _59383) (R _59382 _59383)). Qed.
Lemma lem4800546 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term328 _110654 s R _59382 _59383) = (term329 _110654 s R _59382 _59383).
Proof. exact (@lem4798423 (term327 _110654 s _59383) (_59382 = _59383) (R _59382 _59383)). Qed.
Lemma lem4800547 {_110654 : Type'} (s : _110654 -> Prop) (_59382 : _110654) : (term100 _110654 s _59382) = (term100 _110654 s _59382).
Proof. exact (eq_refl (term100 _110654 s _59382)). Qed.
Lemma lem4800550 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term326 _110654 s R _59382 _59383) = (term330 _110654 s R _59382 _59383).
Proof. exact (MK_COMB (@lem4800547 _110654 s _59382) (@lem4800546 _110654 s R _59382 _59383)). Qed.
Lemma lem4800552 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term112 _110654 s R _59382 _59383) = (term330 _110654 s R _59382 _59383).
Proof. exact (TRANS (@lem4800539 _110654 s R _59382 _59383) (@lem4800550 _110654 s R _59382 _59383)). Qed.
Lemma lem4800553 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term330 _110654 s R _59382 _59383.
Proof. exact (EQ_MP (@lem4800552 _110654 s R _59382 _59383) (@lem4800437 _110654 _59382 _59383 x y s R R' h1)). Qed.
Lemma lem4800579 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term60 _110654 x y.
Proof. exact (proj2 (@lem4800144 _110654 s R' x y h1)). Qed.
Lemma lem4800601 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term112 _110654 s R' _59384 _59385) = (term326 _110654 s R' _59384 _59385).
Proof. exact (@lem4798423 (term327 _110654 s _59384) (term102 _110654 s _59384 _59385) (R' _59384 _59385)). Qed.
Lemma lem4800608 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term328 _110654 s R' _59384 _59385) = (term329 _110654 s R' _59384 _59385).
Proof. exact (@lem4798423 (term327 _110654 s _59385) (_59384 = _59385) (R' _59384 _59385)). Qed.
Lemma lem4800609 {_110654 : Type'} (s : _110654 -> Prop) (_59384 : _110654) : (term100 _110654 s _59384) = (term100 _110654 s _59384).
Proof. exact (eq_refl (term100 _110654 s _59384)). Qed.
Lemma lem4800612 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term326 _110654 s R' _59384 _59385) = (term330 _110654 s R' _59384 _59385).
Proof. exact (MK_COMB (@lem4800609 _110654 s _59384) (@lem4800608 _110654 s R' _59384 _59385)). Qed.
Lemma lem4800614 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term112 _110654 s R' _59384 _59385) = (term330 _110654 s R' _59384 _59385).
Proof. exact (TRANS (@lem4800601 _110654 s R' _59384 _59385) (@lem4800612 _110654 s R' _59384 _59385)). Qed.
Lemma lem4800615 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term330 _110654 s R' _59384 _59385.
Proof. exact (EQ_MP (@lem4800614 _110654 s R' _59384 _59385) (@lem4800438 _110654 _59384 _59385 x y s R R' h1)). Qed.
Lemma lem4800669 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s x.
Proof. exact (proj1 (@lem4800123 _110654 s R R' x y h1)). Qed.
Lemma lem4800670 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term331 _110654 s x.
Proof. exact (fun h0 : term327 _110654 s x => @lem4800669 _110654 s R R' x y h1). Qed.
Lemma lem4800672 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4800673 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term331 _110654 s x) = (s x).
Proof. exact (@lem4800672 (s x)). Qed.
Lemma lem4800674 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s x.
Proof. exact (EQ_MP (@lem4800673 _110654 s x) (@lem4800670 _110654 s R R' x y h1)). Qed.
Lemma lem4800676 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s y.
Proof. exact (proj1 (@lem4800124 _110654 s R R' x y h1)). Qed.
Lemma lem4800677 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term331 _110654 s y.
Proof. exact (fun h0 : term327 _110654 s y => @lem4800676 _110654 s R R' x y h1). Qed.
Lemma lem4800679 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4800680 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term331 _110654 s y) = (s y).
Proof. exact (@lem4800679 (s y)). Qed.
Lemma lem4800681 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s y.
Proof. exact (EQ_MP (@lem4800680 _110654 s y) (@lem4800677 _110654 s R R' x y h1)). Qed.
Lemma lem4800683 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term60 _110654 x y.
Proof. exact (proj2 (@lem4800124 _110654 s R R' x y h1)). Qed.
Lemma lem4800684 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term333 _110654 x y.
Proof. exact (fun h0 : x = y => @lem4800683 _110654 s R R' x y h1). Qed.
Lemma lem4800686 (p : Prop) : (term334 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4800687 {_110654 : Type'} (x : _110654) (y : _110654) : (term333 _110654 x y) = (term60 _110654 x y).
Proof. exact (@lem4800686 (x = y)). Qed.
Lemma lem4800688 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term60 _110654 x y.
Proof. exact (EQ_MP (@lem4800687 _110654 x y) (@lem4800684 _110654 s R R' x y h1)). Qed.
Lemma lem4800704 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4800705 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term329 _110654 s R _59374 _59375) = (term335 _110654 s R _59374 _59375).
Proof. exact (@lem4800704 (_59374 = _59375) (term327 _110654 s _59375) (R _59374 _59375)). Qed.
Lemma lem4800721 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4800722 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term336 _110654 s R _59374 _59375) = (term337 _110654 R _59374 s _59375).
Proof. exact (@lem4800721 (R _59374 _59375) (term327 _110654 s _59375)). Qed.
Lemma lem4800728 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) : (term338 _110654 _59374 _59375) = (term338 _110654 _59374 _59375).
Proof. exact (eq_refl (term338 _110654 _59374 _59375)). Qed.
Lemma lem4800729 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term335 _110654 s R _59374 _59375) = (term339 _110654 R _59374 s _59375).
Proof. exact (MK_COMB (@lem4800728 _110654 _59374 _59375) (@lem4800722 _110654 R _59374 s _59375)). Qed.
Lemma lem4800733 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4800734 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term339 _110654 R _59374 s _59375) = (term340 _110654 R _59374 s _59375).
Proof. exact (@lem4800733 (R _59374 _59375) (_59374 = _59375) (term327 _110654 s _59375)). Qed.
Lemma lem4800752 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term335 _110654 s R _59374 _59375) = (term340 _110654 R _59374 s _59375).
Proof. exact (TRANS (@lem4800729 _110654 R _59374 s _59375) (@lem4800734 _110654 R _59374 s _59375)). Qed.
Lemma lem4800753 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term329 _110654 s R _59374 _59375) = (term340 _110654 R _59374 s _59375).
Proof. exact (TRANS (@lem4800705 _110654 s R _59374 _59375) (@lem4800752 _110654 R _59374 s _59375)). Qed.
Lemma lem4800754 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) : (term100 _110654 s _59374) = (term100 _110654 s _59374).
Proof. exact (eq_refl (term100 _110654 s _59374)). Qed.
Lemma lem4800755 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term330 _110654 s R _59374 _59375) = (term341 _110654 R _59374 s _59375).
Proof. exact (MK_COMB (@lem4800754 _110654 s _59374) (@lem4800753 _110654 R _59374 s _59375)). Qed.
Lemma lem4800759 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4800760 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term341 _110654 R _59374 s _59375) = (term342 _110654 R _59374 s _59375).
Proof. exact (@lem4800759 (R _59374 _59375) (term327 _110654 s _59374) (term343 _110654 _59374 s _59375)). Qed.
Lemma lem4800774 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4800775 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term344 _110654 _59374 s _59375) = (term345 _110654 _59374 s _59375).
Proof. exact (@lem4800774 (_59374 = _59375) (term327 _110654 s _59374) (term327 _110654 s _59375)). Qed.
Lemma lem4800793 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term346 _110654 R _59374 _59375) = (term346 _110654 R _59374 _59375).
Proof. exact (eq_refl (term346 _110654 R _59374 _59375)). Qed.
Lemma lem4800794 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term342 _110654 R _59374 s _59375) = (term347 _110654 R _59374 s _59375).
Proof. exact (MK_COMB (@lem4800793 _110654 R _59374 _59375) (@lem4800775 _110654 _59374 s _59375)). Qed.
Lemma lem4800805 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term341 _110654 R _59374 s _59375) = (term347 _110654 R _59374 s _59375).
Proof. exact (TRANS (@lem4800760 _110654 R _59374 s _59375) (@lem4800794 _110654 R _59374 s _59375)). Qed.
Lemma lem4800806 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term330 _110654 s R _59374 _59375) = (term347 _110654 R _59374 s _59375).
Proof. exact (TRANS (@lem4800755 _110654 R _59374 s _59375) (@lem4800805 _110654 R _59374 s _59375)). Qed.
Lemma lem4800807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4800808 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term348 _110654 s R _59374 _59375) = (term349 _110654 R _59374 s _59375).
Proof. exact (MK_COMB (@lem4800807) (@lem4800806 _110654 R _59374 s _59375)). Qed.
Lemma lem4800832 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4800833 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term102 _110654 s _59374 _59375) = (term343 _110654 _59374 s _59375).
Proof. exact (@lem4800832 (_59374 = _59375) (term327 _110654 s _59375)). Qed.
Lemma lem4800841 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) : (term100 _110654 s _59374) = (term100 _110654 s _59374).
Proof. exact (eq_refl (term100 _110654 s _59374)). Qed.
Lemma lem4800842 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term105 _110654 s _59374 _59375) = (term344 _110654 _59374 s _59375).
Proof. exact (MK_COMB (@lem4800841 _110654 s _59374) (@lem4800833 _110654 _59374 s _59375)). Qed.
Lemma lem4800846 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4800847 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term344 _110654 _59374 s _59375) = (term345 _110654 _59374 s _59375).
Proof. exact (@lem4800846 (_59374 = _59375) (term327 _110654 s _59374) (term327 _110654 s _59375)). Qed.
Lemma lem4800865 {_110654 : Type'} (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term105 _110654 s _59374 _59375) = (term345 _110654 _59374 s _59375).
Proof. exact (TRANS (@lem4800842 _110654 _59374 s _59375) (@lem4800847 _110654 _59374 s _59375)). Qed.
Lemma lem4800866 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term346 _110654 R _59374 _59375) = (term346 _110654 R _59374 _59375).
Proof. exact (eq_refl (term346 _110654 R _59374 _59375)). Qed.
Lemma lem4800867 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : (term350 _110654 R s _59374 _59375) = (term347 _110654 R _59374 s _59375).
Proof. exact (MK_COMB (@lem4800866 _110654 R _59374 _59375) (@lem4800865 _110654 _59374 s _59375)). Qed.
Lemma lem4800878 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : ((term330 _110654 s R _59374 _59375) = (term350 _110654 R s _59374 _59375)) = ((term347 _110654 R _59374 s _59375) = (term347 _110654 R _59374 s _59375)).
Proof. exact (MK_COMB (@lem4800808 _110654 R _59374 s _59375) (@lem4800867 _110654 R _59374 s _59375)). Qed.
Lemma lem4800880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4800881 (x : Prop) : (x = x) = True.
Proof. exact (@lem4800880 Prop x). Qed.
Lemma lem4800882 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (s : _110654 -> Prop) (_59375 : _110654) : ((term347 _110654 R _59374 s _59375) = (term347 _110654 R _59374 s _59375)) = True.
Proof. exact (@lem4800881 (term347 _110654 R _59374 s _59375)). Qed.
Lemma lem4800883 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : ((term330 _110654 s R _59374 _59375) = (term350 _110654 R s _59374 _59375)) = True.
Proof. exact (TRANS (@lem4800878 _110654 R _59374 s _59375) (@lem4800882 _110654 R _59374 s _59375)). Qed.
Lemma lem4800884 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : True = ((term330 _110654 s R _59374 _59375) = (term350 _110654 R s _59374 _59375)).
Proof. exact (SYM (@lem4800883 _110654 R s _59374 _59375)). Qed.
Lemma lem4800885 {_110654 : Type'} (R : type1402 _110654) (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term330 _110654 s R _59374 _59375) = (term350 _110654 R s _59374 _59375).
Proof. exact (EQ_MP (@lem4800884 _110654 R s _59374 _59375) (@lem0)). Qed.
Lemma lem4800886 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term350 _110654 R s _59374 _59375.
Proof. exact (EQ_MP (@lem4800885 _110654 R s _59374 _59375) (@lem4800463 _110654 _59374 _59375 s R R' x y h1)). Qed.
Lemma lem4800888 (b : Prop) (a : Prop) : (a \/ b) = (term351 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4800889 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term350 _110654 R s _59374 _59375) = (term352 _110654 s R _59374 _59375).
Proof. exact (@lem4800888 (term105 _110654 s _59374 _59375) (R _59374 _59375)). Qed.
Lemma lem4800891 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4800892 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term355 _110654 s _59374 _59375) = (term356 _110654 s _59374 _59375).
Proof. exact (@lem4800891 (term327 _110654 s _59374) (term102 _110654 s _59374 _59375)). Qed.
Lemma lem4800894 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4800895 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) : (term357 _110654 s _59374) = (s _59374).
Proof. exact (@lem4800894 (s _59374)). Qed.
Lemma lem4800896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4800897 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) : (term358 _110654 s _59374) = (term59 _110654 s _59374).
Proof. exact (MK_COMB (@lem4800896) (@lem4800895 _110654 s _59374)). Qed.
Lemma lem4800899 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4800900 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term359 _110654 s _59374 _59375) = (term360 _110654 s _59374 _59375).
Proof. exact (@lem4800899 (term327 _110654 s _59375) (_59374 = _59375)). Qed.
Lemma lem4800902 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4800903 {_110654 : Type'} (s : _110654 -> Prop) (_59375 : _110654) : (term357 _110654 s _59375) = (s _59375).
Proof. exact (@lem4800902 (s _59375)). Qed.
Lemma lem4800904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4800905 {_110654 : Type'} (s : _110654 -> Prop) (_59375 : _110654) : (term358 _110654 s _59375) = (term59 _110654 s _59375).
Proof. exact (MK_COMB (@lem4800904) (@lem4800903 _110654 s _59375)). Qed.
Lemma lem4800906 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) : (term60 _110654 _59374 _59375) = (term60 _110654 _59374 _59375).
Proof. exact (eq_refl (term60 _110654 _59374 _59375)). Qed.
Lemma lem4800907 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term360 _110654 s _59374 _59375) = (term62 _110654 s _59374 _59375).
Proof. exact (MK_COMB (@lem4800905 _110654 s _59375) (@lem4800906 _110654 _59374 _59375)). Qed.
Lemma lem4800908 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term359 _110654 s _59374 _59375) = (term62 _110654 s _59374 _59375).
Proof. exact (TRANS (@lem4800900 _110654 s _59374 _59375) (@lem4800907 _110654 s _59374 _59375)). Qed.
Lemma lem4800909 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term356 _110654 s _59374 _59375) = (term64 _110654 s _59374 _59375).
Proof. exact (MK_COMB (@lem4800897 _110654 s _59374) (@lem4800908 _110654 s _59374 _59375)). Qed.
Lemma lem4800910 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term355 _110654 s _59374 _59375) = (term64 _110654 s _59374 _59375).
Proof. exact (TRANS (@lem4800892 _110654 s _59374 _59375) (@lem4800909 _110654 s _59374 _59375)). Qed.
Lemma lem4800911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4800912 {_110654 : Type'} (s : _110654 -> Prop) (_59374 : _110654) (_59375 : _110654) : (term361 _110654 s _59374 _59375) = (term65 _110654 s _59374 _59375).
Proof. exact (MK_COMB (@lem4800911) (@lem4800910 _110654 s _59374 _59375)). Qed.
Lemma lem4800913 {_110654 : Type'} (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (R _59374 _59375) = (R _59374 _59375).
Proof. exact (eq_refl (R _59374 _59375)). Qed.
Lemma lem4800914 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term352 _110654 s R _59374 _59375) = (term67 _110654 s R _59374 _59375).
Proof. exact (MK_COMB (@lem4800912 _110654 s _59374 _59375) (@lem4800913 _110654 R _59374 _59375)). Qed.
Lemma lem4800915 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59374 : _110654) (_59375 : _110654) : (term350 _110654 R s _59374 _59375) = (term67 _110654 s R _59374 _59375).
Proof. exact (TRANS (@lem4800889 _110654 s R _59374 _59375) (@lem4800914 _110654 s R _59374 _59375)). Qed.
Lemma lem4800917 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term62 _110654 s x y.
Proof. exact (conj (@lem4800681 _110654 s R R' x y h1) (@lem4800688 _110654 s R R' x y h1)). Qed.
Lemma lem4800918 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term64 _110654 s x y.
Proof. exact (conj (@lem4800674 _110654 s R R' x y h1) (@lem4800917 _110654 s R R' x y h1)). Qed.
Lemma lem4800920 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term67 _110654 s R _59374 _59375.
Proof. exact (EQ_MP (@lem4800915 _110654 s R _59374 _59375) (@lem4800886 _110654 _59374 _59375 s R R' x y h1)). Qed.
Lemma lem4800921 {_110654 : Type'} (_59374 : _110654) (_59375 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term67 _110654 s R _59374 _59375.
Proof. exact (@lem4800920 _110654 _59374 _59375 s R R' x y h1). Qed.
Lemma lem4800922 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term67 _110654 s R x y.
Proof. exact (@lem4800921 _110654 x y s R R' x y h1). Qed.
Lemma lem4800925 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : R x y.
Proof. exact (@lem4800922 _110654 s R R' x y h1 (@lem4800918 _110654 s R R' x y h1)). Qed.
Lemma lem4800926 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term362 _110654 R x y.
Proof. exact (fun h0 : term316 _110654 R x y => @lem4800925 _110654 s R R' x y h1). Qed.
Lemma lem4800928 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4800929 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) : (term362 _110654 R x y) = (R x y).
Proof. exact (@lem4800928 (R x y)). Qed.
Lemma lem4800930 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : R x y.
Proof. exact (EQ_MP (@lem4800929 _110654 R x y) (@lem4800926 _110654 s R R' x y h1)). Qed.
Lemma lem4800933 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4800935 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) : (term316 _110654 R x y) = (term363 _110654 R x y).
Proof. exact (@lem4800933 (R x y)). Qed.
Lemma lem4800938 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) : term363 _110654 R x y.
Proof. exact (EQ_MP (@lem4800935 _110654 R x y) (@lem4800483 _110654 R x y h1)). Qed.
Lemma lem4800941 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (@lem4800938 _110654 R x y h1 (@lem4800930 _110654 s R R' x y h2)). Qed.
Lemma lem4800942 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : term364.
Proof. exact (fun h0 : ~ False => @lem4800941 _110654 s R R' x y h1 h2). Qed.
Lemma lem4800944 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4800945 : term364 = False.
Proof. exact (@lem4800944 False). Qed.
Lemma lem4800946 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4800945) (@lem4800942 _110654 s R R' x y h1 h2)). Qed.
Lemma lem4801000 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s x.
Proof. exact (proj1 (@lem4800123 _110654 s R R' x y h1)). Qed.
Lemma lem4801001 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term331 _110654 s x.
Proof. exact (fun h0 : term327 _110654 s x => @lem4801000 _110654 s R R' x y h1). Qed.
Lemma lem4801003 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801004 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term331 _110654 s x) = (s x).
Proof. exact (@lem4801003 (s x)). Qed.
Lemma lem4801005 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s x.
Proof. exact (EQ_MP (@lem4801004 _110654 s x) (@lem4801001 _110654 s R R' x y h1)). Qed.
Lemma lem4801007 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s y.
Proof. exact (proj1 (@lem4800124 _110654 s R R' x y h1)). Qed.
Lemma lem4801008 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term331 _110654 s y.
Proof. exact (fun h0 : term327 _110654 s y => @lem4801007 _110654 s R R' x y h1). Qed.
Lemma lem4801010 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801011 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term331 _110654 s y) = (s y).
Proof. exact (@lem4801010 (s y)). Qed.
Lemma lem4801012 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : s y.
Proof. exact (EQ_MP (@lem4801011 _110654 s y) (@lem4801008 _110654 s R R' x y h1)). Qed.
Lemma lem4801014 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term60 _110654 x y.
Proof. exact (proj2 (@lem4800124 _110654 s R R' x y h1)). Qed.
Lemma lem4801015 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term333 _110654 x y.
Proof. exact (fun h0 : x = y => @lem4801014 _110654 s R R' x y h1). Qed.
Lemma lem4801017 (p : Prop) : (term334 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4801018 {_110654 : Type'} (x : _110654) (y : _110654) : (term333 _110654 x y) = (term60 _110654 x y).
Proof. exact (@lem4801017 (x = y)). Qed.
Lemma lem4801019 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term60 _110654 x y.
Proof. exact (EQ_MP (@lem4801018 _110654 x y) (@lem4801015 _110654 s R R' x y h1)). Qed.
Lemma lem4801035 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801036 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term329 _110654 s R' _59380 _59381) = (term335 _110654 s R' _59380 _59381).
Proof. exact (@lem4801035 (_59380 = _59381) (term327 _110654 s _59381) (R' _59380 _59381)). Qed.
Lemma lem4801052 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4801053 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term336 _110654 s R' _59380 _59381) = (term337 _110654 R' _59380 s _59381).
Proof. exact (@lem4801052 (R' _59380 _59381) (term327 _110654 s _59381)). Qed.
Lemma lem4801059 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) : (term338 _110654 _59380 _59381) = (term338 _110654 _59380 _59381).
Proof. exact (eq_refl (term338 _110654 _59380 _59381)). Qed.
Lemma lem4801060 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term335 _110654 s R' _59380 _59381) = (term339 _110654 R' _59380 s _59381).
Proof. exact (MK_COMB (@lem4801059 _110654 _59380 _59381) (@lem4801053 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801064 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801065 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term339 _110654 R' _59380 s _59381) = (term340 _110654 R' _59380 s _59381).
Proof. exact (@lem4801064 (R' _59380 _59381) (_59380 = _59381) (term327 _110654 s _59381)). Qed.
Lemma lem4801083 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term335 _110654 s R' _59380 _59381) = (term340 _110654 R' _59380 s _59381).
Proof. exact (TRANS (@lem4801060 _110654 R' _59380 s _59381) (@lem4801065 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801084 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term329 _110654 s R' _59380 _59381) = (term340 _110654 R' _59380 s _59381).
Proof. exact (TRANS (@lem4801036 _110654 s R' _59380 _59381) (@lem4801083 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801085 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) : (term100 _110654 s _59380) = (term100 _110654 s _59380).
Proof. exact (eq_refl (term100 _110654 s _59380)). Qed.
Lemma lem4801086 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term330 _110654 s R' _59380 _59381) = (term341 _110654 R' _59380 s _59381).
Proof. exact (MK_COMB (@lem4801085 _110654 s _59380) (@lem4801084 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801090 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801091 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term341 _110654 R' _59380 s _59381) = (term342 _110654 R' _59380 s _59381).
Proof. exact (@lem4801090 (R' _59380 _59381) (term327 _110654 s _59380) (term343 _110654 _59380 s _59381)). Qed.
Lemma lem4801105 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801106 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term344 _110654 _59380 s _59381) = (term345 _110654 _59380 s _59381).
Proof. exact (@lem4801105 (_59380 = _59381) (term327 _110654 s _59380) (term327 _110654 s _59381)). Qed.
Lemma lem4801124 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term346 _110654 R' _59380 _59381) = (term346 _110654 R' _59380 _59381).
Proof. exact (eq_refl (term346 _110654 R' _59380 _59381)). Qed.
Lemma lem4801125 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term342 _110654 R' _59380 s _59381) = (term347 _110654 R' _59380 s _59381).
Proof. exact (MK_COMB (@lem4801124 _110654 R' _59380 _59381) (@lem4801106 _110654 _59380 s _59381)). Qed.
Lemma lem4801136 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term341 _110654 R' _59380 s _59381) = (term347 _110654 R' _59380 s _59381).
Proof. exact (TRANS (@lem4801091 _110654 R' _59380 s _59381) (@lem4801125 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801137 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term330 _110654 s R' _59380 _59381) = (term347 _110654 R' _59380 s _59381).
Proof. exact (TRANS (@lem4801086 _110654 R' _59380 s _59381) (@lem4801136 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4801139 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term348 _110654 s R' _59380 _59381) = (term349 _110654 R' _59380 s _59381).
Proof. exact (MK_COMB (@lem4801138) (@lem4801137 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801163 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4801164 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term102 _110654 s _59380 _59381) = (term343 _110654 _59380 s _59381).
Proof. exact (@lem4801163 (_59380 = _59381) (term327 _110654 s _59381)). Qed.
Lemma lem4801172 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) : (term100 _110654 s _59380) = (term100 _110654 s _59380).
Proof. exact (eq_refl (term100 _110654 s _59380)). Qed.
Lemma lem4801173 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term105 _110654 s _59380 _59381) = (term344 _110654 _59380 s _59381).
Proof. exact (MK_COMB (@lem4801172 _110654 s _59380) (@lem4801164 _110654 _59380 s _59381)). Qed.
Lemma lem4801177 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801178 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term344 _110654 _59380 s _59381) = (term345 _110654 _59380 s _59381).
Proof. exact (@lem4801177 (_59380 = _59381) (term327 _110654 s _59380) (term327 _110654 s _59381)). Qed.
Lemma lem4801196 {_110654 : Type'} (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term105 _110654 s _59380 _59381) = (term345 _110654 _59380 s _59381).
Proof. exact (TRANS (@lem4801173 _110654 _59380 s _59381) (@lem4801178 _110654 _59380 s _59381)). Qed.
Lemma lem4801197 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term346 _110654 R' _59380 _59381) = (term346 _110654 R' _59380 _59381).
Proof. exact (eq_refl (term346 _110654 R' _59380 _59381)). Qed.
Lemma lem4801198 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : (term350 _110654 R' s _59380 _59381) = (term347 _110654 R' _59380 s _59381).
Proof. exact (MK_COMB (@lem4801197 _110654 R' _59380 _59381) (@lem4801196 _110654 _59380 s _59381)). Qed.
Lemma lem4801209 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : ((term330 _110654 s R' _59380 _59381) = (term350 _110654 R' s _59380 _59381)) = ((term347 _110654 R' _59380 s _59381) = (term347 _110654 R' _59380 s _59381)).
Proof. exact (MK_COMB (@lem4801139 _110654 R' _59380 s _59381) (@lem4801198 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4801212 (x : Prop) : (x = x) = True.
Proof. exact (@lem4801211 Prop x). Qed.
Lemma lem4801213 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (s : _110654 -> Prop) (_59381 : _110654) : ((term347 _110654 R' _59380 s _59381) = (term347 _110654 R' _59380 s _59381)) = True.
Proof. exact (@lem4801212 (term347 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801214 {_110654 : Type'} (R' : type1402 _110654) (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : ((term330 _110654 s R' _59380 _59381) = (term350 _110654 R' s _59380 _59381)) = True.
Proof. exact (TRANS (@lem4801209 _110654 R' _59380 s _59381) (@lem4801213 _110654 R' _59380 s _59381)). Qed.
Lemma lem4801215 {_110654 : Type'} (R' : type1402 _110654) (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : True = ((term330 _110654 s R' _59380 _59381) = (term350 _110654 R' s _59380 _59381)).
Proof. exact (SYM (@lem4801214 _110654 R' s _59380 _59381)). Qed.
Lemma lem4801216 {_110654 : Type'} (R' : type1402 _110654) (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term330 _110654 s R' _59380 _59381) = (term350 _110654 R' s _59380 _59381).
Proof. exact (EQ_MP (@lem4801215 _110654 R' s _59380 _59381) (@lem0)). Qed.
Lemma lem4801217 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term350 _110654 R' s _59380 _59381.
Proof. exact (EQ_MP (@lem4801216 _110654 R' s _59380 _59381) (@lem4800525 _110654 _59380 _59381 s R R' x y h1)). Qed.
Lemma lem4801219 (b : Prop) (a : Prop) : (a \/ b) = (term351 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4801220 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term350 _110654 R' s _59380 _59381) = (term352 _110654 s R' _59380 _59381).
Proof. exact (@lem4801219 (term105 _110654 s _59380 _59381) (R' _59380 _59381)). Qed.
Lemma lem4801222 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4801223 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term355 _110654 s _59380 _59381) = (term356 _110654 s _59380 _59381).
Proof. exact (@lem4801222 (term327 _110654 s _59380) (term102 _110654 s _59380 _59381)). Qed.
Lemma lem4801225 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4801226 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) : (term357 _110654 s _59380) = (s _59380).
Proof. exact (@lem4801225 (s _59380)). Qed.
Lemma lem4801227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4801228 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) : (term358 _110654 s _59380) = (term59 _110654 s _59380).
Proof. exact (MK_COMB (@lem4801227) (@lem4801226 _110654 s _59380)). Qed.
Lemma lem4801230 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4801231 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term359 _110654 s _59380 _59381) = (term360 _110654 s _59380 _59381).
Proof. exact (@lem4801230 (term327 _110654 s _59381) (_59380 = _59381)). Qed.
Lemma lem4801233 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4801234 {_110654 : Type'} (s : _110654 -> Prop) (_59381 : _110654) : (term357 _110654 s _59381) = (s _59381).
Proof. exact (@lem4801233 (s _59381)). Qed.
Lemma lem4801235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4801236 {_110654 : Type'} (s : _110654 -> Prop) (_59381 : _110654) : (term358 _110654 s _59381) = (term59 _110654 s _59381).
Proof. exact (MK_COMB (@lem4801235) (@lem4801234 _110654 s _59381)). Qed.
Lemma lem4801237 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) : (term60 _110654 _59380 _59381) = (term60 _110654 _59380 _59381).
Proof. exact (eq_refl (term60 _110654 _59380 _59381)). Qed.
Lemma lem4801238 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term360 _110654 s _59380 _59381) = (term62 _110654 s _59380 _59381).
Proof. exact (MK_COMB (@lem4801236 _110654 s _59381) (@lem4801237 _110654 _59380 _59381)). Qed.
Lemma lem4801239 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term359 _110654 s _59380 _59381) = (term62 _110654 s _59380 _59381).
Proof. exact (TRANS (@lem4801231 _110654 s _59380 _59381) (@lem4801238 _110654 s _59380 _59381)). Qed.
Lemma lem4801240 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term356 _110654 s _59380 _59381) = (term64 _110654 s _59380 _59381).
Proof. exact (MK_COMB (@lem4801228 _110654 s _59380) (@lem4801239 _110654 s _59380 _59381)). Qed.
Lemma lem4801241 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term355 _110654 s _59380 _59381) = (term64 _110654 s _59380 _59381).
Proof. exact (TRANS (@lem4801223 _110654 s _59380 _59381) (@lem4801240 _110654 s _59380 _59381)). Qed.
Lemma lem4801242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4801243 {_110654 : Type'} (s : _110654 -> Prop) (_59380 : _110654) (_59381 : _110654) : (term361 _110654 s _59380 _59381) = (term65 _110654 s _59380 _59381).
Proof. exact (MK_COMB (@lem4801242) (@lem4801241 _110654 s _59380 _59381)). Qed.
Lemma lem4801244 {_110654 : Type'} (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (R' _59380 _59381) = (R' _59380 _59381).
Proof. exact (eq_refl (R' _59380 _59381)). Qed.
Lemma lem4801245 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term352 _110654 s R' _59380 _59381) = (term67 _110654 s R' _59380 _59381).
Proof. exact (MK_COMB (@lem4801243 _110654 s _59380 _59381) (@lem4801244 _110654 R' _59380 _59381)). Qed.
Lemma lem4801246 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59380 : _110654) (_59381 : _110654) : (term350 _110654 R' s _59380 _59381) = (term67 _110654 s R' _59380 _59381).
Proof. exact (TRANS (@lem4801220 _110654 s R' _59380 _59381) (@lem4801245 _110654 s R' _59380 _59381)). Qed.
Lemma lem4801248 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term62 _110654 s x y.
Proof. exact (conj (@lem4801012 _110654 s R R' x y h1) (@lem4801019 _110654 s R R' x y h1)). Qed.
Lemma lem4801249 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term64 _110654 s x y.
Proof. exact (conj (@lem4801005 _110654 s R R' x y h1) (@lem4801248 _110654 s R R' x y h1)). Qed.
Lemma lem4801251 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term67 _110654 s R' _59380 _59381.
Proof. exact (EQ_MP (@lem4801246 _110654 s R' _59380 _59381) (@lem4801217 _110654 _59380 _59381 s R R' x y h1)). Qed.
Lemma lem4801252 {_110654 : Type'} (_59380 : _110654) (_59381 : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term67 _110654 s R' _59380 _59381.
Proof. exact (@lem4801251 _110654 _59380 _59381 s R R' x y h1). Qed.
Lemma lem4801253 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term67 _110654 s R' x y.
Proof. exact (@lem4801252 _110654 x y s R R' x y h1). Qed.
Lemma lem4801256 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : R' x y.
Proof. exact (@lem4801253 _110654 s R R' x y h1 (@lem4801249 _110654 s R R' x y h1)). Qed.
Lemma lem4801257 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : term362 _110654 R' x y.
Proof. exact (fun h0 : term316 _110654 R' x y => @lem4801256 _110654 s R R' x y h1). Qed.
Lemma lem4801259 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801260 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) : (term362 _110654 R' x y) = (R' x y).
Proof. exact (@lem4801259 (R' x y)). Qed.
Lemma lem4801261 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : R' x y.
Proof. exact (EQ_MP (@lem4801260 _110654 R' x y) (@lem4801257 _110654 s R R' x y h1)). Qed.
Lemma lem4801264 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4801266 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) : (term316 _110654 R' x y) = (term363 _110654 R' x y).
Proof. exact (@lem4801264 (R' x y)). Qed.
Lemma lem4801269 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) : term363 _110654 R' x y.
Proof. exact (EQ_MP (@lem4801266 _110654 R' x y) (@lem4800527 _110654 R' x y h1)). Qed.
Lemma lem4801272 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (@lem4801269 _110654 R' x y h1 (@lem4801261 _110654 s R R' x y h2)). Qed.
Lemma lem4801273 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : term364.
Proof. exact (fun h0 : ~ False => @lem4801272 _110654 s R R' x y h1 h2). Qed.
Lemma lem4801275 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801276 : term364 = False.
Proof. exact (@lem4801275 False). Qed.
Lemma lem4801277 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801276) (@lem4801273 _110654 s R R' x y h1 h2)). Qed.
Lemma lem4801331 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : s x.
Proof. exact (proj1 (@lem4800137 _110654 s R x y h1)). Qed.
Lemma lem4801332 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term331 _110654 s x.
Proof. exact (fun h0 : term327 _110654 s x => @lem4801331 _110654 s R x y h1). Qed.
Lemma lem4801334 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801335 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term331 _110654 s x) = (s x).
Proof. exact (@lem4801334 (s x)). Qed.
Lemma lem4801336 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : s x.
Proof. exact (EQ_MP (@lem4801335 _110654 s x) (@lem4801332 _110654 s R x y h1)). Qed.
Lemma lem4801338 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : s y.
Proof. exact (proj1 (@lem4800138 _110654 s R x y h1)). Qed.
Lemma lem4801339 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term331 _110654 s y.
Proof. exact (fun h0 : term327 _110654 s y => @lem4801338 _110654 s R x y h1). Qed.
Lemma lem4801341 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801342 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term331 _110654 s y) = (s y).
Proof. exact (@lem4801341 (s y)). Qed.
Lemma lem4801343 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : s y.
Proof. exact (EQ_MP (@lem4801342 _110654 s y) (@lem4801339 _110654 s R x y h1)). Qed.
Lemma lem4801345 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term316 _110654 R x y.
Proof. exact (proj2 (@lem4800134 _110654 s R x y h1)). Qed.
Lemma lem4801346 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term365 _110654 R x y.
Proof. exact (fun h0 : R x y => @lem4801345 _110654 s R x y h1). Qed.
Lemma lem4801348 (p : Prop) : (term334 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4801349 {_110654 : Type'} (R : type1402 _110654) (x : _110654) (y : _110654) : (term365 _110654 R x y) = (term316 _110654 R x y).
Proof. exact (@lem4801348 (R x y)). Qed.
Lemma lem4801350 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term316 _110654 R x y.
Proof. exact (EQ_MP (@lem4801349 _110654 R x y) (@lem4801346 _110654 s R x y h1)). Qed.
Lemma lem4801366 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801367 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term329 _110654 s R _59382 _59383) = (term335 _110654 s R _59382 _59383).
Proof. exact (@lem4801366 (_59382 = _59383) (term327 _110654 s _59383) (R _59382 _59383)). Qed.
Lemma lem4801383 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4801384 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term336 _110654 s R _59382 _59383) = (term337 _110654 R _59382 s _59383).
Proof. exact (@lem4801383 (R _59382 _59383) (term327 _110654 s _59383)). Qed.
Lemma lem4801390 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) : (term338 _110654 _59382 _59383) = (term338 _110654 _59382 _59383).
Proof. exact (eq_refl (term338 _110654 _59382 _59383)). Qed.
Lemma lem4801391 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term335 _110654 s R _59382 _59383) = (term339 _110654 R _59382 s _59383).
Proof. exact (MK_COMB (@lem4801390 _110654 _59382 _59383) (@lem4801384 _110654 R _59382 s _59383)). Qed.
Lemma lem4801395 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801396 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term339 _110654 R _59382 s _59383) = (term340 _110654 R _59382 s _59383).
Proof. exact (@lem4801395 (R _59382 _59383) (_59382 = _59383) (term327 _110654 s _59383)). Qed.
Lemma lem4801414 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term335 _110654 s R _59382 _59383) = (term340 _110654 R _59382 s _59383).
Proof. exact (TRANS (@lem4801391 _110654 R _59382 s _59383) (@lem4801396 _110654 R _59382 s _59383)). Qed.
Lemma lem4801415 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term329 _110654 s R _59382 _59383) = (term340 _110654 R _59382 s _59383).
Proof. exact (TRANS (@lem4801367 _110654 s R _59382 _59383) (@lem4801414 _110654 R _59382 s _59383)). Qed.
Lemma lem4801416 {_110654 : Type'} (s : _110654 -> Prop) (_59382 : _110654) : (term100 _110654 s _59382) = (term100 _110654 s _59382).
Proof. exact (eq_refl (term100 _110654 s _59382)). Qed.
Lemma lem4801417 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term330 _110654 s R _59382 _59383) = (term341 _110654 R _59382 s _59383).
Proof. exact (MK_COMB (@lem4801416 _110654 s _59382) (@lem4801415 _110654 R _59382 s _59383)). Qed.
Lemma lem4801421 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801422 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term341 _110654 R _59382 s _59383) = (term342 _110654 R _59382 s _59383).
Proof. exact (@lem4801421 (R _59382 _59383) (term327 _110654 s _59382) (term343 _110654 _59382 s _59383)). Qed.
Lemma lem4801436 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801437 {_110654 : Type'} (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term344 _110654 _59382 s _59383) = (term345 _110654 _59382 s _59383).
Proof. exact (@lem4801436 (_59382 = _59383) (term327 _110654 s _59382) (term327 _110654 s _59383)). Qed.
Lemma lem4801455 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term346 _110654 R _59382 _59383) = (term346 _110654 R _59382 _59383).
Proof. exact (eq_refl (term346 _110654 R _59382 _59383)). Qed.
Lemma lem4801456 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term342 _110654 R _59382 s _59383) = (term347 _110654 R _59382 s _59383).
Proof. exact (MK_COMB (@lem4801455 _110654 R _59382 _59383) (@lem4801437 _110654 _59382 s _59383)). Qed.
Lemma lem4801467 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term341 _110654 R _59382 s _59383) = (term347 _110654 R _59382 s _59383).
Proof. exact (TRANS (@lem4801422 _110654 R _59382 s _59383) (@lem4801456 _110654 R _59382 s _59383)). Qed.
Lemma lem4801468 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term330 _110654 s R _59382 _59383) = (term347 _110654 R _59382 s _59383).
Proof. exact (TRANS (@lem4801417 _110654 R _59382 s _59383) (@lem4801467 _110654 R _59382 s _59383)). Qed.
Lemma lem4801469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4801470 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term348 _110654 s R _59382 _59383) = (term349 _110654 R _59382 s _59383).
Proof. exact (MK_COMB (@lem4801469) (@lem4801468 _110654 R _59382 s _59383)). Qed.
Lemma lem4801496 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4801497 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term336 _110654 s R _59382 _59383) = (term337 _110654 R _59382 s _59383).
Proof. exact (@lem4801496 (R _59382 _59383) (term327 _110654 s _59383)). Qed.
Lemma lem4801503 {_110654 : Type'} (s : _110654 -> Prop) (_59382 : _110654) : (term100 _110654 s _59382) = (term100 _110654 s _59382).
Proof. exact (eq_refl (term100 _110654 s _59382)). Qed.
Lemma lem4801504 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term366 _110654 s R _59382 _59383) = (term367 _110654 R _59382 s _59383).
Proof. exact (MK_COMB (@lem4801503 _110654 s _59382) (@lem4801497 _110654 R _59382 s _59383)). Qed.
Lemma lem4801508 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801509 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term367 _110654 R _59382 s _59383) = (term368 _110654 R _59382 s _59383).
Proof. exact (@lem4801508 (R _59382 _59383) (term327 _110654 s _59382) (term327 _110654 s _59383)). Qed.
Lemma lem4801525 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term366 _110654 s R _59382 _59383) = (term368 _110654 R _59382 s _59383).
Proof. exact (TRANS (@lem4801504 _110654 R _59382 s _59383) (@lem4801509 _110654 R _59382 s _59383)). Qed.
Lemma lem4801526 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) : (term338 _110654 _59382 _59383) = (term338 _110654 _59382 _59383).
Proof. exact (eq_refl (term338 _110654 _59382 _59383)). Qed.
Lemma lem4801527 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term369 _110654 s R _59382 _59383) = (term370 _110654 R _59382 s _59383).
Proof. exact (MK_COMB (@lem4801526 _110654 _59382 _59383) (@lem4801525 _110654 R _59382 s _59383)). Qed.
Lemma lem4801531 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801532 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term370 _110654 R _59382 s _59383) = (term347 _110654 R _59382 s _59383).
Proof. exact (@lem4801531 (R _59382 _59383) (_59382 = _59383) (term371 _110654 _59382 s _59383)). Qed.
Lemma lem4801560 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : (term369 _110654 s R _59382 _59383) = (term347 _110654 R _59382 s _59383).
Proof. exact (TRANS (@lem4801527 _110654 R _59382 s _59383) (@lem4801532 _110654 R _59382 s _59383)). Qed.
Lemma lem4801561 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : ((term330 _110654 s R _59382 _59383) = (term369 _110654 s R _59382 _59383)) = ((term347 _110654 R _59382 s _59383) = (term347 _110654 R _59382 s _59383)).
Proof. exact (MK_COMB (@lem4801470 _110654 R _59382 s _59383) (@lem4801560 _110654 R _59382 s _59383)). Qed.
Lemma lem4801563 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4801564 (x : Prop) : (x = x) = True.
Proof. exact (@lem4801563 Prop x). Qed.
Lemma lem4801565 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (s : _110654 -> Prop) (_59383 : _110654) : ((term347 _110654 R _59382 s _59383) = (term347 _110654 R _59382 s _59383)) = True.
Proof. exact (@lem4801564 (term347 _110654 R _59382 s _59383)). Qed.
Lemma lem4801566 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : ((term330 _110654 s R _59382 _59383) = (term369 _110654 s R _59382 _59383)) = True.
Proof. exact (TRANS (@lem4801561 _110654 R _59382 s _59383) (@lem4801565 _110654 R _59382 s _59383)). Qed.
Lemma lem4801567 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : True = ((term330 _110654 s R _59382 _59383) = (term369 _110654 s R _59382 _59383)).
Proof. exact (SYM (@lem4801566 _110654 s R _59382 _59383)). Qed.
Lemma lem4801568 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term330 _110654 s R _59382 _59383) = (term369 _110654 s R _59382 _59383).
Proof. exact (EQ_MP (@lem4801567 _110654 s R _59382 _59383) (@lem0)). Qed.
Lemma lem4801569 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term369 _110654 s R _59382 _59383.
Proof. exact (EQ_MP (@lem4801568 _110654 s R _59382 _59383) (@lem4800553 _110654 _59382 _59383 x y s R R' h1)). Qed.
Lemma lem4801571 (b : Prop) (a : Prop) : (a \/ b) = (term351 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4801572 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term369 _110654 s R _59382 _59383) = (term372 _110654 s R _59382 _59383).
Proof. exact (@lem4801571 (term366 _110654 s R _59382 _59383) (_59382 = _59383)). Qed.
Lemma lem4801574 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4801575 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term373 _110654 s R _59382 _59383) = (term374 _110654 s R _59382 _59383).
Proof. exact (@lem4801574 (term327 _110654 s _59382) (term336 _110654 s R _59382 _59383)). Qed.
Lemma lem4801577 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4801578 {_110654 : Type'} (s : _110654 -> Prop) (_59382 : _110654) : (term357 _110654 s _59382) = (s _59382).
Proof. exact (@lem4801577 (s _59382)). Qed.
Lemma lem4801579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4801580 {_110654 : Type'} (s : _110654 -> Prop) (_59382 : _110654) : (term358 _110654 s _59382) = (term59 _110654 s _59382).
Proof. exact (MK_COMB (@lem4801579) (@lem4801578 _110654 s _59382)). Qed.
Lemma lem4801582 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4801583 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term375 _110654 s R _59382 _59383) = (term376 _110654 s R _59382 _59383).
Proof. exact (@lem4801582 (term327 _110654 s _59383) (R _59382 _59383)). Qed.
Lemma lem4801585 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4801586 {_110654 : Type'} (s : _110654 -> Prop) (_59383 : _110654) : (term357 _110654 s _59383) = (s _59383).
Proof. exact (@lem4801585 (s _59383)). Qed.
Lemma lem4801587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4801588 {_110654 : Type'} (s : _110654 -> Prop) (_59383 : _110654) : (term358 _110654 s _59383) = (term59 _110654 s _59383).
Proof. exact (MK_COMB (@lem4801587) (@lem4801586 _110654 s _59383)). Qed.
Lemma lem4801589 {_110654 : Type'} (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term316 _110654 R _59382 _59383) = (term316 _110654 R _59382 _59383).
Proof. exact (eq_refl (term316 _110654 R _59382 _59383)). Qed.
Lemma lem4801590 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term376 _110654 s R _59382 _59383) = (term377 _110654 s R _59382 _59383).
Proof. exact (MK_COMB (@lem4801588 _110654 s _59383) (@lem4801589 _110654 R _59382 _59383)). Qed.
Lemma lem4801591 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term375 _110654 s R _59382 _59383) = (term377 _110654 s R _59382 _59383).
Proof. exact (TRANS (@lem4801583 _110654 s R _59382 _59383) (@lem4801590 _110654 s R _59382 _59383)). Qed.
Lemma lem4801592 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term374 _110654 s R _59382 _59383) = (term378 _110654 s R _59382 _59383).
Proof. exact (MK_COMB (@lem4801580 _110654 s _59382) (@lem4801591 _110654 s R _59382 _59383)). Qed.
Lemma lem4801593 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term373 _110654 s R _59382 _59383) = (term378 _110654 s R _59382 _59383).
Proof. exact (TRANS (@lem4801575 _110654 s R _59382 _59383) (@lem4801592 _110654 s R _59382 _59383)). Qed.
Lemma lem4801594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4801595 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term379 _110654 s R _59382 _59383) = (term380 _110654 s R _59382 _59383).
Proof. exact (MK_COMB (@lem4801594) (@lem4801593 _110654 s R _59382 _59383)). Qed.
Lemma lem4801596 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) : (_59382 = _59383) = (_59382 = _59383).
Proof. exact (eq_refl (_59382 = _59383)). Qed.
Lemma lem4801597 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term372 _110654 s R _59382 _59383) = (term381 _110654 s R _59382 _59383).
Proof. exact (MK_COMB (@lem4801595 _110654 s R _59382 _59383) (@lem4801596 _110654 _59382 _59383)). Qed.
Lemma lem4801598 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (_59382 : _110654) (_59383 : _110654) : (term369 _110654 s R _59382 _59383) = (term381 _110654 s R _59382 _59383).
Proof. exact (TRANS (@lem4801572 _110654 s R _59382 _59383) (@lem4801597 _110654 s R _59382 _59383)). Qed.
Lemma lem4801600 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term377 _110654 s R x y.
Proof. exact (conj (@lem4801343 _110654 s R x y h1) (@lem4801350 _110654 s R x y h1)). Qed.
Lemma lem4801601 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term378 _110654 s R x y.
Proof. exact (conj (@lem4801336 _110654 s R x y h1) (@lem4801600 _110654 s R x y h1)). Qed.
Lemma lem4801603 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term381 _110654 s R _59382 _59383.
Proof. exact (EQ_MP (@lem4801598 _110654 s R _59382 _59383) (@lem4801569 _110654 _59382 _59383 x y s R R' h1)). Qed.
Lemma lem4801604 {_110654 : Type'} (_59382 : _110654) (_59383 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term381 _110654 s R _59382 _59383.
Proof. exact (@lem4801603 _110654 _59382 _59383 x y s R R' h1). Qed.
Lemma lem4801605 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term381 _110654 s R x y.
Proof. exact (@lem4801604 _110654 x y x y s R R' h1). Qed.
Lemma lem4801608 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R x y) (h2 : term271 _110654 x y s R R') : x = y.
Proof. exact (@lem4801605 _110654 x y s R R' h2 (@lem4801601 _110654 s R x y h1)). Qed.
Lemma lem4801609 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R x y) (h2 : term271 _110654 x y s R R') : term382 _110654 x y.
Proof. exact (fun h0 : term60 _110654 x y => @lem4801608 _110654 x y s R R' h1 h2). Qed.
Lemma lem4801611 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801612 {_110654 : Type'} (x : _110654) (y : _110654) : (term382 _110654 x y) = (x = y).
Proof. exact (@lem4801611 (x = y)). Qed.
Lemma lem4801613 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R x y) (h2 : term271 _110654 x y s R R') : x = y.
Proof. exact (EQ_MP (@lem4801612 _110654 x y) (@lem4801609 _110654 x y s R R' h1 h2)). Qed.
Lemma lem4801616 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4801618 {_110654 : Type'} (x : _110654) (y : _110654) : (term60 _110654 x y) = (term383 _110654 x y).
Proof. exact (@lem4801616 (x = y)). Qed.
Lemma lem4801621 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R x y) : term383 _110654 x y.
Proof. exact (EQ_MP (@lem4801618 _110654 x y) (@lem4800535 _110654 s R x y h1)). Qed.
Lemma lem4801624 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R x y) (h2 : term271 _110654 x y s R R') : False.
Proof. exact (@lem4801621 _110654 s R x y h1 (@lem4801613 _110654 x y s R R' h1 h2)). Qed.
Lemma lem4801625 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R x y) (h2 : term271 _110654 x y s R R') : term364.
Proof. exact (fun h0 : ~ False => @lem4801624 _110654 x y s R R' h1 h2). Qed.
Lemma lem4801627 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801628 : term364 = False.
Proof. exact (@lem4801627 False). Qed.
Lemma lem4801629 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R x y) (h2 : term271 _110654 x y s R R') : False.
Proof. exact (EQ_MP (@lem4801628) (@lem4801625 _110654 x y s R R' h1 h2)). Qed.
Lemma lem4801683 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : s x.
Proof. exact (proj1 (@lem4800143 _110654 s R' x y h1)). Qed.
Lemma lem4801684 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term331 _110654 s x.
Proof. exact (fun h0 : term327 _110654 s x => @lem4801683 _110654 s R' x y h1). Qed.
Lemma lem4801686 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801687 {_110654 : Type'} (s : _110654 -> Prop) (x : _110654) : (term331 _110654 s x) = (s x).
Proof. exact (@lem4801686 (s x)). Qed.
Lemma lem4801688 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : s x.
Proof. exact (EQ_MP (@lem4801687 _110654 s x) (@lem4801684 _110654 s R' x y h1)). Qed.
Lemma lem4801690 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : s y.
Proof. exact (proj1 (@lem4800144 _110654 s R' x y h1)). Qed.
Lemma lem4801691 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term331 _110654 s y.
Proof. exact (fun h0 : term327 _110654 s y => @lem4801690 _110654 s R' x y h1). Qed.
Lemma lem4801693 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801694 {_110654 : Type'} (s : _110654 -> Prop) (y : _110654) : (term331 _110654 s y) = (s y).
Proof. exact (@lem4801693 (s y)). Qed.
Lemma lem4801695 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : s y.
Proof. exact (EQ_MP (@lem4801694 _110654 s y) (@lem4801691 _110654 s R' x y h1)). Qed.
Lemma lem4801697 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term316 _110654 R' x y.
Proof. exact (proj2 (@lem4800135 _110654 s R' x y h1)). Qed.
Lemma lem4801698 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term365 _110654 R' x y.
Proof. exact (fun h0 : R' x y => @lem4801697 _110654 s R' x y h1). Qed.
Lemma lem4801700 (p : Prop) : (term334 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4801701 {_110654 : Type'} (R' : type1402 _110654) (x : _110654) (y : _110654) : (term365 _110654 R' x y) = (term316 _110654 R' x y).
Proof. exact (@lem4801700 (R' x y)). Qed.
Lemma lem4801702 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term316 _110654 R' x y.
Proof. exact (EQ_MP (@lem4801701 _110654 R' x y) (@lem4801698 _110654 s R' x y h1)). Qed.
Lemma lem4801718 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801719 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term329 _110654 s R' _59384 _59385) = (term335 _110654 s R' _59384 _59385).
Proof. exact (@lem4801718 (_59384 = _59385) (term327 _110654 s _59385) (R' _59384 _59385)). Qed.
Lemma lem4801735 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4801736 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term336 _110654 s R' _59384 _59385) = (term337 _110654 R' _59384 s _59385).
Proof. exact (@lem4801735 (R' _59384 _59385) (term327 _110654 s _59385)). Qed.
Lemma lem4801742 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) : (term338 _110654 _59384 _59385) = (term338 _110654 _59384 _59385).
Proof. exact (eq_refl (term338 _110654 _59384 _59385)). Qed.
Lemma lem4801743 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term335 _110654 s R' _59384 _59385) = (term339 _110654 R' _59384 s _59385).
Proof. exact (MK_COMB (@lem4801742 _110654 _59384 _59385) (@lem4801736 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801747 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801748 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term339 _110654 R' _59384 s _59385) = (term340 _110654 R' _59384 s _59385).
Proof. exact (@lem4801747 (R' _59384 _59385) (_59384 = _59385) (term327 _110654 s _59385)). Qed.
Lemma lem4801766 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term335 _110654 s R' _59384 _59385) = (term340 _110654 R' _59384 s _59385).
Proof. exact (TRANS (@lem4801743 _110654 R' _59384 s _59385) (@lem4801748 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801767 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term329 _110654 s R' _59384 _59385) = (term340 _110654 R' _59384 s _59385).
Proof. exact (TRANS (@lem4801719 _110654 s R' _59384 _59385) (@lem4801766 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801768 {_110654 : Type'} (s : _110654 -> Prop) (_59384 : _110654) : (term100 _110654 s _59384) = (term100 _110654 s _59384).
Proof. exact (eq_refl (term100 _110654 s _59384)). Qed.
Lemma lem4801769 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term330 _110654 s R' _59384 _59385) = (term341 _110654 R' _59384 s _59385).
Proof. exact (MK_COMB (@lem4801768 _110654 s _59384) (@lem4801767 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801773 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801774 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term341 _110654 R' _59384 s _59385) = (term342 _110654 R' _59384 s _59385).
Proof. exact (@lem4801773 (R' _59384 _59385) (term327 _110654 s _59384) (term343 _110654 _59384 s _59385)). Qed.
Lemma lem4801788 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801789 {_110654 : Type'} (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term344 _110654 _59384 s _59385) = (term345 _110654 _59384 s _59385).
Proof. exact (@lem4801788 (_59384 = _59385) (term327 _110654 s _59384) (term327 _110654 s _59385)). Qed.
Lemma lem4801807 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term346 _110654 R' _59384 _59385) = (term346 _110654 R' _59384 _59385).
Proof. exact (eq_refl (term346 _110654 R' _59384 _59385)). Qed.
Lemma lem4801808 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term342 _110654 R' _59384 s _59385) = (term347 _110654 R' _59384 s _59385).
Proof. exact (MK_COMB (@lem4801807 _110654 R' _59384 _59385) (@lem4801789 _110654 _59384 s _59385)). Qed.
Lemma lem4801819 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term341 _110654 R' _59384 s _59385) = (term347 _110654 R' _59384 s _59385).
Proof. exact (TRANS (@lem4801774 _110654 R' _59384 s _59385) (@lem4801808 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801820 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term330 _110654 s R' _59384 _59385) = (term347 _110654 R' _59384 s _59385).
Proof. exact (TRANS (@lem4801769 _110654 R' _59384 s _59385) (@lem4801819 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4801822 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term348 _110654 s R' _59384 _59385) = (term349 _110654 R' _59384 s _59385).
Proof. exact (MK_COMB (@lem4801821) (@lem4801820 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801848 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4801849 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term336 _110654 s R' _59384 _59385) = (term337 _110654 R' _59384 s _59385).
Proof. exact (@lem4801848 (R' _59384 _59385) (term327 _110654 s _59385)). Qed.
Lemma lem4801855 {_110654 : Type'} (s : _110654 -> Prop) (_59384 : _110654) : (term100 _110654 s _59384) = (term100 _110654 s _59384).
Proof. exact (eq_refl (term100 _110654 s _59384)). Qed.
Lemma lem4801856 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term366 _110654 s R' _59384 _59385) = (term367 _110654 R' _59384 s _59385).
Proof. exact (MK_COMB (@lem4801855 _110654 s _59384) (@lem4801849 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801860 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801861 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term367 _110654 R' _59384 s _59385) = (term368 _110654 R' _59384 s _59385).
Proof. exact (@lem4801860 (R' _59384 _59385) (term327 _110654 s _59384) (term327 _110654 s _59385)). Qed.
Lemma lem4801877 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term366 _110654 s R' _59384 _59385) = (term368 _110654 R' _59384 s _59385).
Proof. exact (TRANS (@lem4801856 _110654 R' _59384 s _59385) (@lem4801861 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801878 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) : (term338 _110654 _59384 _59385) = (term338 _110654 _59384 _59385).
Proof. exact (eq_refl (term338 _110654 _59384 _59385)). Qed.
Lemma lem4801879 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term369 _110654 s R' _59384 _59385) = (term370 _110654 R' _59384 s _59385).
Proof. exact (MK_COMB (@lem4801878 _110654 _59384 _59385) (@lem4801877 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801883 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4801884 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term370 _110654 R' _59384 s _59385) = (term347 _110654 R' _59384 s _59385).
Proof. exact (@lem4801883 (R' _59384 _59385) (_59384 = _59385) (term371 _110654 _59384 s _59385)). Qed.
Lemma lem4801912 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : (term369 _110654 s R' _59384 _59385) = (term347 _110654 R' _59384 s _59385).
Proof. exact (TRANS (@lem4801879 _110654 R' _59384 s _59385) (@lem4801884 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801913 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : ((term330 _110654 s R' _59384 _59385) = (term369 _110654 s R' _59384 _59385)) = ((term347 _110654 R' _59384 s _59385) = (term347 _110654 R' _59384 s _59385)).
Proof. exact (MK_COMB (@lem4801822 _110654 R' _59384 s _59385) (@lem4801912 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801915 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4801916 (x : Prop) : (x = x) = True.
Proof. exact (@lem4801915 Prop x). Qed.
Lemma lem4801917 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (s : _110654 -> Prop) (_59385 : _110654) : ((term347 _110654 R' _59384 s _59385) = (term347 _110654 R' _59384 s _59385)) = True.
Proof. exact (@lem4801916 (term347 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801918 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : ((term330 _110654 s R' _59384 _59385) = (term369 _110654 s R' _59384 _59385)) = True.
Proof. exact (TRANS (@lem4801913 _110654 R' _59384 s _59385) (@lem4801917 _110654 R' _59384 s _59385)). Qed.
Lemma lem4801919 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : True = ((term330 _110654 s R' _59384 _59385) = (term369 _110654 s R' _59384 _59385)).
Proof. exact (SYM (@lem4801918 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801920 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term330 _110654 s R' _59384 _59385) = (term369 _110654 s R' _59384 _59385).
Proof. exact (EQ_MP (@lem4801919 _110654 s R' _59384 _59385) (@lem0)). Qed.
Lemma lem4801921 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term369 _110654 s R' _59384 _59385.
Proof. exact (EQ_MP (@lem4801920 _110654 s R' _59384 _59385) (@lem4800615 _110654 _59384 _59385 x y s R R' h1)). Qed.
Lemma lem4801923 (b : Prop) (a : Prop) : (a \/ b) = (term351 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4801924 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term369 _110654 s R' _59384 _59385) = (term372 _110654 s R' _59384 _59385).
Proof. exact (@lem4801923 (term366 _110654 s R' _59384 _59385) (_59384 = _59385)). Qed.
Lemma lem4801926 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4801927 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term373 _110654 s R' _59384 _59385) = (term374 _110654 s R' _59384 _59385).
Proof. exact (@lem4801926 (term327 _110654 s _59384) (term336 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801929 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4801930 {_110654 : Type'} (s : _110654 -> Prop) (_59384 : _110654) : (term357 _110654 s _59384) = (s _59384).
Proof. exact (@lem4801929 (s _59384)). Qed.
Lemma lem4801931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4801932 {_110654 : Type'} (s : _110654 -> Prop) (_59384 : _110654) : (term358 _110654 s _59384) = (term59 _110654 s _59384).
Proof. exact (MK_COMB (@lem4801931) (@lem4801930 _110654 s _59384)). Qed.
Lemma lem4801934 (a : Prop) (b : Prop) : (term353 a b) = (term354 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4801935 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term375 _110654 s R' _59384 _59385) = (term376 _110654 s R' _59384 _59385).
Proof. exact (@lem4801934 (term327 _110654 s _59385) (R' _59384 _59385)). Qed.
Lemma lem4801937 (a : Prop) : (term96 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4801938 {_110654 : Type'} (s : _110654 -> Prop) (_59385 : _110654) : (term357 _110654 s _59385) = (s _59385).
Proof. exact (@lem4801937 (s _59385)). Qed.
Lemma lem4801939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4801940 {_110654 : Type'} (s : _110654 -> Prop) (_59385 : _110654) : (term358 _110654 s _59385) = (term59 _110654 s _59385).
Proof. exact (MK_COMB (@lem4801939) (@lem4801938 _110654 s _59385)). Qed.
Lemma lem4801941 {_110654 : Type'} (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term316 _110654 R' _59384 _59385) = (term316 _110654 R' _59384 _59385).
Proof. exact (eq_refl (term316 _110654 R' _59384 _59385)). Qed.
Lemma lem4801942 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term376 _110654 s R' _59384 _59385) = (term377 _110654 s R' _59384 _59385).
Proof. exact (MK_COMB (@lem4801940 _110654 s _59385) (@lem4801941 _110654 R' _59384 _59385)). Qed.
Lemma lem4801943 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term375 _110654 s R' _59384 _59385) = (term377 _110654 s R' _59384 _59385).
Proof. exact (TRANS (@lem4801935 _110654 s R' _59384 _59385) (@lem4801942 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801944 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term374 _110654 s R' _59384 _59385) = (term378 _110654 s R' _59384 _59385).
Proof. exact (MK_COMB (@lem4801932 _110654 s _59384) (@lem4801943 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801945 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term373 _110654 s R' _59384 _59385) = (term378 _110654 s R' _59384 _59385).
Proof. exact (TRANS (@lem4801927 _110654 s R' _59384 _59385) (@lem4801944 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4801947 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term379 _110654 s R' _59384 _59385) = (term380 _110654 s R' _59384 _59385).
Proof. exact (MK_COMB (@lem4801946) (@lem4801945 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801948 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) : (_59384 = _59385) = (_59384 = _59385).
Proof. exact (eq_refl (_59384 = _59385)). Qed.
Lemma lem4801949 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term372 _110654 s R' _59384 _59385) = (term381 _110654 s R' _59384 _59385).
Proof. exact (MK_COMB (@lem4801947 _110654 s R' _59384 _59385) (@lem4801948 _110654 _59384 _59385)). Qed.
Lemma lem4801950 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (_59384 : _110654) (_59385 : _110654) : (term369 _110654 s R' _59384 _59385) = (term381 _110654 s R' _59384 _59385).
Proof. exact (TRANS (@lem4801924 _110654 s R' _59384 _59385) (@lem4801949 _110654 s R' _59384 _59385)). Qed.
Lemma lem4801952 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term377 _110654 s R' x y.
Proof. exact (conj (@lem4801695 _110654 s R' x y h1) (@lem4801702 _110654 s R' x y h1)). Qed.
Lemma lem4801953 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term378 _110654 s R' x y.
Proof. exact (conj (@lem4801688 _110654 s R' x y h1) (@lem4801952 _110654 s R' x y h1)). Qed.
Lemma lem4801955 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term381 _110654 s R' _59384 _59385.
Proof. exact (EQ_MP (@lem4801950 _110654 s R' _59384 _59385) (@lem4801921 _110654 _59384 _59385 x y s R R' h1)). Qed.
Lemma lem4801956 {_110654 : Type'} (_59384 : _110654) (_59385 : _110654) (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term381 _110654 s R' _59384 _59385.
Proof. exact (@lem4801955 _110654 _59384 _59385 x y s R R' h1). Qed.
Lemma lem4801957 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : term381 _110654 s R' x y.
Proof. exact (@lem4801956 _110654 x y x y s R R' h1). Qed.
Lemma lem4801960 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R' x y) (h2 : term271 _110654 x y s R R') : x = y.
Proof. exact (@lem4801957 _110654 x y s R R' h2 (@lem4801953 _110654 s R' x y h1)). Qed.
Lemma lem4801961 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R' x y) (h2 : term271 _110654 x y s R R') : term382 _110654 x y.
Proof. exact (fun h0 : term60 _110654 x y => @lem4801960 _110654 x y s R R' h1 h2). Qed.
Lemma lem4801963 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801964 {_110654 : Type'} (x : _110654) (y : _110654) : (term382 _110654 x y) = (x = y).
Proof. exact (@lem4801963 (x = y)). Qed.
Lemma lem4801965 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R' x y) (h2 : term271 _110654 x y s R R') : x = y.
Proof. exact (EQ_MP (@lem4801964 _110654 x y) (@lem4801961 _110654 x y s R R' h1 h2)). Qed.
Lemma lem4801968 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4801970 {_110654 : Type'} (x : _110654) (y : _110654) : (term60 _110654 x y) = (term383 _110654 x y).
Proof. exact (@lem4801968 (x = y)). Qed.
Lemma lem4801973 {_110654 : Type'} (s : _110654 -> Prop) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term108 _110654 s R' x y) : term383 _110654 x y.
Proof. exact (EQ_MP (@lem4801970 _110654 x y) (@lem4800579 _110654 s R' x y h1)). Qed.
Lemma lem4801976 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R' x y) (h2 : term271 _110654 x y s R R') : False.
Proof. exact (@lem4801973 _110654 s R' x y h1 (@lem4801965 _110654 x y s R R' h1 h2)). Qed.
Lemma lem4801977 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R' x y) (h2 : term271 _110654 x y s R R') : term364.
Proof. exact (fun h0 : ~ False => @lem4801976 _110654 x y s R R' h1 h2). Qed.
Lemma lem4801979 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4801980 : term364 = False.
Proof. exact (@lem4801979 False). Qed.
Lemma lem4801981 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term108 _110654 s R' x y) (h2 : term271 _110654 x y s R R') : False.
Proof. exact (EQ_MP (@lem4801980) (@lem4801977 _110654 x y s R R' h1 h2)). Qed.
Lemma lem4801982 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : (term316 _110654 R' x y) = False.
Proof. exact (prop_ext (fun h3 : term316 _110654 R' x y => @lem4801277 _110654 s R R' x y h1 h2) (fun h3 : False => @lem4800527 _110654 R' x y h1)). Qed.
Lemma lem4801983 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801982 _110654 s R R' x y h1 h2) (@lem4800527 _110654 R' x y h1)). Qed.
Lemma lem4801984 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : (term316 _110654 R x y) = False.
Proof. exact (prop_ext (fun h3 : term316 _110654 R x y => @lem4800946 _110654 s R R' x y h1 h2) (fun h3 : False => @lem4800483 _110654 R x y h1)). Qed.
Lemma lem4801985 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801984 _110654 s R R' x y h1 h2) (@lem4800483 _110654 R x y h1)). Qed.
Lemma lem4801986 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : (term316 _110654 R' x y) = False.
Proof. exact (prop_ext (fun h3 : term316 _110654 R' x y => @lem4801983 _110654 s R R' x y h1 h2) (fun h3 : False => @lem4800291 _110654 R' x y h1)). Qed.
Lemma lem4801987 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801986 _110654 s R R' x y h1 h2) (@lem4800291 _110654 R' x y h1)). Qed.
Lemma lem4801988 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : (term316 _110654 R x y) = False.
Proof. exact (prop_ext (fun h3 : term316 _110654 R x y => @lem4801985 _110654 s R R' x y h1 h2) (fun h3 : False => @lem4800219 _110654 R x y h1)). Qed.
Lemma lem4801989 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801988 _110654 s R R' x y h1 h2) (@lem4800219 _110654 R x y h1)). Qed.
Lemma lem4801990 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : (term316 _110654 R' x y) = False.
Proof. exact (prop_ext (fun h3 : term316 _110654 R' x y => @lem4801987 _110654 s R R' x y h1 h2) (fun h3 : False => @lem4800291 _110654 R' x y h1)). Qed.
Lemma lem4801991 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R' x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801990 _110654 s R R' x y h1 h2) (@lem4800291 _110654 R' x y h1)). Qed.
Lemma lem4801992 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : (term316 _110654 R x y) = False.
Proof. exact (prop_ext (fun h3 : term316 _110654 R x y => @lem4801989 _110654 s R R' x y h1 h2) (fun h3 : False => @lem4800219 _110654 R x y h1)). Qed.
Lemma lem4801993 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term316 _110654 R x y) (h2 : term200 _110654 s R R' x y) : False.
Proof. exact (EQ_MP (@lem4801992 _110654 s R R' x y h1 h2) (@lem4800219 _110654 R x y h1)). Qed.
Lemma lem4801994 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term271 _110654 x y s R R') : False.
Proof. exact (or_elim (@lem4800133 _110654 x y s R R' h1) (fun h0 : term108 _110654 s R x y => @lem4801629 _110654 x y s R R' h0 h1) (fun h0 : term108 _110654 s R' x y => @lem4801981 _110654 x y s R R' h0 h1)). Qed.
Lemma lem4801995 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (x : _110654) (y : _110654) (h1 : term200 _110654 s R R' x y) : False.
Proof. exact (or_elim (@lem4800122 _110654 s R R' x y h1) (fun h0 : term316 _110654 R x y => @lem4801993 _110654 s R R' x y h0 h1) (fun h0 : term316 _110654 R' x y => @lem4801991 _110654 s R R' x y h0 h1)). Qed.
Lemma lem4801996 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term310 _110654 x y s R R') : False.
Proof. exact (or_elim (@lem4800117 _110654 x y s R R' h1) (fun h0 : term200 _110654 s R R' x y => @lem4801995 _110654 s R R' x y h0) (fun h0 : term271 _110654 x y s R R' => @lem4801994 _110654 x y s R R' h0)). Qed.
Lemma lem4801997 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term310 _110654 x y s R R') : (term310 _110654 x y s R R') = False.
Proof. exact (prop_ext (fun h2 : term310 _110654 x y s R R' => @lem4801996 _110654 x y s R R' h1) (fun h2 : False => @lem4800117 _110654 x y s R R' h1)). Qed.
Lemma lem4801998 {_110654 : Type'} (x : _110654) (y : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term310 _110654 x y s R R') : False.
Proof. exact (EQ_MP (@lem4801997 _110654 x y s R R' h1) (@lem4800117 _110654 x y s R R' h1)). Qed.
Lemma lem4801999 {_110654 : Type'} (x : _110654) (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term313 _110654 x s R R') : False.
Proof. exact (ex_elim (@lem4799890 _110654 x s R R' h1) (fun y : _110654 => fun h0 : term312 _110654 x s R R' y => @lem4801998 _110654 x y s R R' h0)). Qed.
Lemma lem4802000 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term98 _110654 s R R') : False.
Proof. exact (ex_elim (@lem4799889 _110654 s R R' h1) (fun x : _110654 => fun h0 : term314 _110654 s R R' x => @lem4801999 _110654 x s R R' h0)). Qed.
Lemma lem4802001 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term98 _110654 s R R') : (term98 _110654 s R R') = False.
Proof. exact (prop_ext (fun h2 : term98 _110654 s R R' => @lem4802000 _110654 s R R' h1) (fun h2 : False => @lem4799137 _110654 s R R' h1)). Qed.
Lemma lem4802002 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) (h1 : term98 _110654 s R R') : False.
Proof. exact (EQ_MP (@lem4802001 _110654 s R R' h1) (@lem4799137 _110654 s R R' h1)). Qed.
Lemma lem4802003 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : term97 _110654 s R R'.
Proof. exact (fun h0 : term98 _110654 s R R' => @lem4802002 _110654 s R R' h0). Qed.
Lemma lem4802004 {_110654 : Type'} (s : _110654 -> Prop) (R : type1402 _110654) (R' : type1402 _110654) : (term76 _110654 R s R') = (term82 _110654 s R R').
Proof. exact (EQ_MP (@lem4799136 _110654 s R R') (@lem4802003 _110654 s R R')). Qed.
Lemma lem4802009 {_110654 : Type'} (R : type1402 _110654) (R' : type1402 _110654) : term84 _110654 R R'.
Proof. exact (fun s : _110654 -> Prop => @lem4802004 _110654 s R R'). Qed.
Lemma lem4802014 {_110654 : Type'} (R : type1402 _110654) : term86 _110654 R.
Proof. exact (fun R' : type1402 _110654 => @lem4802009 _110654 R R'). Qed.
Lemma lem4802019 {_110654 : Type'} : term88 _110654.
Proof. exact (fun R : type1402 _110654 => @lem4802014 _110654 R). Qed.
Lemma lem4802020 {_110654 : Type'} : term90 _110654.
Proof. exact (EQ_MP (@lem4799132 _110654) (@lem4802019 _110654)). Qed.
Lemma lem4802022 {_110654 : Type'} : term90 _110654.
Proof. exact (@lem4798901 _110654 (@lem4802020 _110654)). Qed.
Lemma lem4802023 {_110654 : Type'} (h1 : term91 _110654) : False.
Proof. exact (@lem4802022 _110654 (@lem4798885 _110654 h1)). Qed.
Lemma lem4802024 {_110654 : Type'} (h1 : term91 _110654) : (term91 _110654) = False.
Proof. exact (prop_ext (fun h2 : term91 _110654 => @lem4802023 _110654 h1) (fun h2 : False => @lem4798885 _110654 h1)). Qed.
Lemma lem4802025 {_110654 : Type'} (h1 : term91 _110654) : False.
Proof. exact (EQ_MP (@lem4802024 _110654 h1) (@lem4798885 _110654 h1)). Qed.
Lemma lem4802026 {_110654 : Type'} : term90 _110654.
Proof. exact (fun h0 : term91 _110654 => @lem4802025 _110654 h0). Qed.
Lemma lem4802027 {_110654 : Type'} : term88 _110654.
Proof. exact (EQ_MP (@lem4798884 _110654) (@lem4802026 _110654)). Qed.
Lemma lem4802029 {_110654 : Type'} : term57 _110654.
Proof. exact (EQ_MP (@lem4798880 _110654) (@lem4802027 _110654)). Qed.
Lemma lem4802030 {_110654 : Type'} : term56 _110654.
Proof. exact (EQ_MP (@lem4798589 _110654) (@lem4802029 _110654)). Qed.
