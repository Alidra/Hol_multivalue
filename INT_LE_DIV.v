Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_DIV_term_abbrevs.
Require Import INT_FORALL_POS_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_POS_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem2651483 (n : nat) : term0 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem2651484 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2651485 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2651484 n) (@lem2651483 n)). Qed.
Lemma lem2651486 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem2651488 (m : nat) : term2 m.
Proof. exact (@lem2538105 m). Qed.
Lemma lem2651489 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem2651490 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem2651489 m) (@lem2651488 m)). Qed.
Lemma lem2651491 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem2651490 m n). Qed.
Lemma lem2651492 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2651495 (P : int -> Prop) (h1 : (term7 P) = (term8 P)) : (term7 P) = (term8 P).
Proof. exact (h1). Qed.
Lemma lem2651496 (P : int -> Prop) (h1 : (term7 P) = (term8 P)) : (term8 P) = (term7 P).
Proof. exact (SYM (@lem2651495 P h1)). Qed.
Lemma lem2651497 (P : int -> Prop) (h1 : (term8 P) = (term7 P)) : (term8 P) = (term7 P).
Proof. exact (h1). Qed.
Lemma lem2651498 (P : int -> Prop) (h1 : (term8 P) = (term7 P)) : (term7 P) = (term8 P).
Proof. exact (SYM (@lem2651497 P h1)). Qed.
Lemma lem2651499 (P : int -> Prop) : ((term7 P) = (term8 P)) = ((term8 P) = (term7 P)).
Proof. exact (prop_ext (fun h1 : (term7 P) = (term8 P) => @lem2651496 P h1) (fun h1 : (term8 P) = (term7 P) => @lem2651498 P h1)). Qed.
Lemma lem2651500 : term9 = term10.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2651499 P)). Qed.
Lemma lem2651501 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2651502 : term11 = term12.
Proof. exact (MK_COMB (@lem2651501) (@lem2651500)). Qed.
Lemma lem2651503 : term12.
Proof. exact (EQ_MP (@lem2651502) (@lem2315380)). Qed.
Lemma lem2651504 {A : Type'} (P : Prop) : term13 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem2651505 {A : Type'} (P : Prop) : (term13 A P) = (term14 A P).
Proof. exact (eq_refl (term13 A P)). Qed.
Lemma lem2651506 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (EQ_MP (@lem2651505 A P) (@lem2651504 A P)). Qed.
Lemma lem2651507 {A : Type'} (P : Prop) (Q : A -> Prop) : term15 A P Q.
Proof. exact (@lem2651506 A P Q). Qed.
Lemma lem2651508 {A : Type'} (P : Prop) (Q : A -> Prop) : (term15 A P Q) = ((term16 A P Q) = (term17 A P Q)).
Proof. exact (eq_refl (term15 A P Q)). Qed.
Lemma lem2651510 (P : int -> Prop) : term18 P.
Proof. exact (@lem2651503 P). Qed.
Lemma lem2651511 (P : int -> Prop) : (term18 P) = ((term8 P) = (term7 P)).
Proof. exact (eq_refl (term18 P)). Qed.
Lemma lem2651542 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem2651543 (m : int) (n : int) : (term21 m n) = (term22 m n).
Proof. exact (@lem2651542 (term23 m) (term23 n) (term24 m n)). Qed.
Lemma lem2651548 (m : int) : (term25 m) = (term26 m).
Proof. exact (fun_ext (fun n : int => @lem2651543 m n)). Qed.
Lemma lem2651549 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2651550 (m : int) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem2651549) (@lem2651548 m)). Qed.
Lemma lem2651554 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = (term17 A P Q).
Proof. exact (EQ_MP (@lem2651508 A P Q) (@lem2651507 A P Q)). Qed.
Lemma lem2651555 (P : Prop) (Q : int -> Prop) : (term29 P Q) = (term30 P Q).
Proof. exact (@lem2651554 int P Q). Qed.
Lemma lem2651556 (m : int) : (term31 m) = (term32 m).
Proof. exact (@lem2651555 (term23 m) (term33 m)). Qed.
Lemma lem2651557 (m : int) (n : int) : (term34 m n) = (term35 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem2651558 (m : int) : (term36 m) = (term36 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem2651559 (m : int) (n : int) : (term37 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem2651558 m) (@lem2651557 m n)). Qed.
Lemma lem2651560 (m : int) : (term38 m) = (term26 m).
Proof. exact (fun_ext (fun n : int => @lem2651559 m n)). Qed.
Lemma lem2651561 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2651562 (m : int) : (term31 m) = (term28 m).
Proof. exact (MK_COMB (@lem2651561) (@lem2651560 m)). Qed.
Lemma lem2651563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2651564 (m : int) : (term39 m) = (term40 m).
Proof. exact (MK_COMB (@lem2651563) (@lem2651562 m)). Qed.
Lemma lem2651565 (m : int) (n : int) : (term34 m n) = (term35 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem2651566 (m : int) : (term41 m) = (term33 m).
Proof. exact (fun_ext (fun n : int => @lem2651565 m n)). Qed.
Lemma lem2651567 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2651568 (m : int) : (term42 m) = (term43 m).
Proof. exact (MK_COMB (@lem2651567) (@lem2651566 m)). Qed.
Lemma lem2651569 (m : int) : (term36 m) = (term36 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem2651570 (m : int) : (term32 m) = (term44 m).
Proof. exact (MK_COMB (@lem2651569 m) (@lem2651568 m)). Qed.
Lemma lem2651571 (m : int) : ((term31 m) = (term32 m)) = ((term28 m) = (term44 m)).
Proof. exact (MK_COMB (@lem2651564 m) (@lem2651570 m)). Qed.
Lemma lem2651572 (m : int) : (term28 m) = (term44 m).
Proof. exact (EQ_MP (@lem2651571 m) (@lem2651556 m)). Qed.
Lemma lem2651576 (P : int -> Prop) : (term8 P) = (term7 P).
Proof. exact (EQ_MP (@lem2651511 P) (@lem2651510 P)). Qed.
Lemma lem2651577 (m : int) : (term45 m) = (term46 m).
Proof. exact (@lem2651576 (term47 m)). Qed.
Lemma lem2651578 (m : int) (n : int) : (term48 m n) = (term24 m n).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem2651579 (n : int) : (term36 n) = (term36 n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem2651580 (m : int) (n : int) : (term49 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2651579 n) (@lem2651578 m n)). Qed.
Lemma lem2651581 (m : int) : (term50 m) = (term33 m).
Proof. exact (fun_ext (fun n : int => @lem2651580 m n)). Qed.
Lemma lem2651582 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2651583 (m : int) : (term45 m) = (term43 m).
Proof. exact (MK_COMB (@lem2651582) (@lem2651581 m)). Qed.
Lemma lem2651584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2651585 (m : int) : (term51 m) = (term52 m).
Proof. exact (MK_COMB (@lem2651584) (@lem2651583 m)). Qed.
Lemma lem2651586 (m : int) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem2651587 (m : int) : (term55 m) = (term56 m).
Proof. exact (fun_ext (fun n : nat => @lem2651586 m n)). Qed.
Lemma lem2651588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2651589 (m : int) : (term46 m) = (term57 m).
Proof. exact (MK_COMB (@lem2651588) (@lem2651587 m)). Qed.
Lemma lem2651590 (m : int) : ((term45 m) = (term46 m)) = ((term43 m) = (term57 m)).
Proof. exact (MK_COMB (@lem2651585 m) (@lem2651589 m)). Qed.
Lemma lem2651591 (m : int) : (term43 m) = (term57 m).
Proof. exact (EQ_MP (@lem2651590 m) (@lem2651577 m)). Qed.
Lemma lem2651596 (m : int) : (term36 m) = (term36 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem2651597 (m : int) : (term44 m) = (term58 m).
Proof. exact (MK_COMB (@lem2651596 m) (@lem2651591 m)). Qed.
Lemma lem2651600 (m : int) : (term28 m) = (term58 m).
Proof. exact (TRANS (@lem2651572 m) (@lem2651597 m)). Qed.
Lemma lem2651601 (m : int) : (term27 m) = (term58 m).
Proof. exact (TRANS (@lem2651550 m) (@lem2651600 m)). Qed.
Lemma lem2651602 : term59 = term60.
Proof. exact (fun_ext (fun m : int => @lem2651601 m)). Qed.
Lemma lem2651603 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2651604 : term61 = term62.
Proof. exact (MK_COMB (@lem2651603) (@lem2651602)). Qed.
Lemma lem2651606 (P : int -> Prop) : (term8 P) = (term7 P).
Proof. exact (EQ_MP (@lem2651511 P) (@lem2651510 P)). Qed.
Lemma lem2651607 : term63 = term64.
Proof. exact (@lem2651606 term65). Qed.
Lemma lem2651608 (m : int) : (term66 m) = (term57 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem2651609 (m : int) : (term36 m) = (term36 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem2651610 (m : int) : (term67 m) = (term58 m).
Proof. exact (MK_COMB (@lem2651609 m) (@lem2651608 m)). Qed.
Lemma lem2651611 : term68 = term60.
Proof. exact (fun_ext (fun m : int => @lem2651610 m)). Qed.
Lemma lem2651612 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2651613 : term63 = term62.
Proof. exact (MK_COMB (@lem2651612) (@lem2651611)). Qed.
Lemma lem2651614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2651615 : term69 = term70.
Proof. exact (MK_COMB (@lem2651614) (@lem2651613)). Qed.
Lemma lem2651616 (n : nat) : (term71 n) = (term72 n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem2651617 : term73 = term74.
Proof. exact (fun_ext (fun n : nat => @lem2651616 n)). Qed.
Lemma lem2651618 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2651619 : term64 = term75.
Proof. exact (MK_COMB (@lem2651618) (@lem2651617)). Qed.
Lemma lem2651620 : (term63 = term64) = (term62 = term75).
Proof. exact (MK_COMB (@lem2651615) (@lem2651619)). Qed.
Lemma lem2651621 : term62 = term75.
Proof. exact (EQ_MP (@lem2651620) (@lem2651607)). Qed.
Lemma lem2651630 : term61 = term75.
Proof. exact (TRANS (@lem2651604) (@lem2651621)). Qed.
Lemma lem2651631 : term75 = term61.
Proof. exact (SYM (@lem2651630)). Qed.
Lemma lem2651641 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem2651492 m n) (@lem2651491 m n)). Qed.
Lemma lem2651642 (n : nat) (n' : nat) : (term5 n n') = (term6 n n').
Proof. exact (@lem2651641 n n'). Qed.
Lemma lem2651643 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem2651644 (n : nat) (n' : nat) : (term77 n n') = (term78 n n').
Proof. exact (MK_COMB (@lem2651643) (@lem2651642 n n')). Qed.
Lemma lem2651646 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem2651486 n) (@lem2651485 n)). Qed.
Lemma lem2651647 (n : nat) (n' : nat) : (term78 n n') = True.
Proof. exact (@lem2651646 (Nat.div n n')). Qed.
Lemma lem2651648 (n : nat) (n' : nat) : (term77 n n') = True.
Proof. exact (TRANS (@lem2651644 n n') (@lem2651647 n n')). Qed.
Lemma lem2651649 (n : nat) : (term79 n) = term80.
Proof. exact (fun_ext (fun n' : nat => @lem2651648 n n')). Qed.
Lemma lem2651650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2651651 (n : nat) : (term72 n) = term81.
Proof. exact (MK_COMB (@lem2651650) (@lem2651649 n)). Qed.
Lemma lem2651653 {A : Type'} (t : Prop) : (term82 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2651654 (t : Prop) : (term83 t) = t.
Proof. exact (@lem2651653 nat t). Qed.
Lemma lem2651655 : term81 = True.
Proof. exact (@lem2651654 True). Qed.
Lemma lem2651656 (n : nat) : (term72 n) = True.
Proof. exact (TRANS (@lem2651651 n) (@lem2651655)). Qed.
Lemma lem2651657 : term74 = term80.
Proof. exact (fun_ext (fun n : nat => @lem2651656 n)). Qed.
Lemma lem2651658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2651659 : term75 = term81.
Proof. exact (MK_COMB (@lem2651658) (@lem2651657)). Qed.
Lemma lem2651661 {A : Type'} (t : Prop) : (term82 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2651662 (t : Prop) : (term83 t) = t.
Proof. exact (@lem2651661 nat t). Qed.
Lemma lem2651663 : term81 = True.
Proof. exact (@lem2651662 True). Qed.
Lemma lem2651664 : term75 = True.
Proof. exact (TRANS (@lem2651659) (@lem2651663)). Qed.
Lemma lem2651665 : True = term75.
Proof. exact (SYM (@lem2651664)). Qed.
Lemma lem2651666 : term75.
Proof. exact (EQ_MP (@lem2651665) (@lem0)). Qed.
Lemma lem2651667 : term61.
Proof. exact (EQ_MP (@lem2651631) (@lem2651666)). Qed.
