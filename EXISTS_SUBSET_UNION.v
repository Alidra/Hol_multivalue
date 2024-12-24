Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SUBSET_UNION_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_SUBSET_UNION_spec.
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
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3245542 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3245543 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3245544 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3245543 t1) (@lem3245542 t1)). Qed.
Lemma lem3245545 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3245544 t1 t2). Qed.
Lemma lem3245546 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3245547 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3245546 t1 t2) (@lem3245545 t1 t2)). Qed.
Lemma lem3245548 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3245547 t1 t2 t3). Qed.
Lemma lem3245549 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3245550 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3245549 t1 t2 t3) (@lem3245548 t1 t2 t3)). Qed.
Lemma lem3245551 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3245550 t1 t2 t3)). Qed.
Lemma lem3245552 {A : Type'} (P : type686 A) (t : A -> Prop) : term7 A P t.
Proof. exact (@lem3245541 A P t). Qed.
Lemma lem3245553 {A : Type'} (t : A -> Prop) (P : type686 A) : (term7 A P t) = (term8 A t P).
Proof. exact (eq_refl (term7 A P t)). Qed.
Lemma lem3245554 {A : Type'} (t : A -> Prop) (P : type686 A) : term8 A t P.
Proof. exact (EQ_MP (@lem3245553 A t P) (@lem3245552 A P t)). Qed.
Lemma lem3245555 {A : Type'} (t : A -> Prop) (P : type686 A) (u : A -> Prop) : term9 A t P u.
Proof. exact (@lem3245554 A t P u). Qed.
Lemma lem3245556 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term9 A t P u) = ((term10 A t u P) = (term11 A t u P)).
Proof. exact (eq_refl (term9 A t P u)). Qed.
Lemma lem3245569 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3245570 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : ((term13 _85001 P Q) = (term14 _85001 P Q)) = (term15 _85001 P Q).
Proof. exact (@lem3245569 ((term13 _85001 P Q) = (term14 _85001 P Q))). Qed.
Lemma lem3245571 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term15 _85001 P Q) = ((term13 _85001 P Q) = (term14 _85001 P Q)).
Proof. exact (SYM (@lem3245570 _85001 P Q)). Qed.
Lemma lem3245572 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : term16 _85001 P Q.
Proof. exact (h1). Qed.
Lemma lem3245575 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term15 _85001 P Q) : term15 _85001 P Q.
Proof. exact (h1). Qed.
Lemma lem3245576 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term17 _85001 P Q.
Proof. exact (fun h0 : term15 _85001 P Q => @lem3245575 _85001 P Q h0). Qed.
Lemma lem3245577 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term17 _85001 P Q) : term17 _85001 P Q.
Proof. exact (h1). Qed.
Lemma lem3245578 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term15 _85001 P Q) : term15 _85001 P Q.
Proof. exact (h1). Qed.
Lemma lem3245579 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term15 _85001 P Q) (h2 : term17 _85001 P Q) : term15 _85001 P Q.
Proof. exact (@lem3245577 _85001 P Q h2 (@lem3245578 _85001 P Q h1)). Qed.
Lemma lem3245580 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term15 _85001 P Q) : term18 _85001 P Q.
Proof. exact (fun h0 : term17 _85001 P Q => @lem3245579 _85001 P Q h1 h0). Qed.
Lemma lem3245581 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term17 _85001 P Q) : term17 _85001 P Q.
Proof. exact (h1). Qed.
Lemma lem3245582 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term15 _85001 P Q) (h2 : term17 _85001 P Q) : term15 _85001 P Q.
Proof. exact (@lem3245580 _85001 P Q h1 (@lem3245581 _85001 P Q h2)). Qed.
Lemma lem3245583 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term17 _85001 P Q) : term17 _85001 P Q.
Proof. exact (fun h0 : term15 _85001 P Q => @lem3245582 _85001 P Q h0 h1). Qed.
Lemma lem3245584 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term19 _85001 P Q.
Proof. exact (fun h0 : term17 _85001 P Q => @lem3245583 _85001 P Q h0). Qed.
Lemma lem3245587 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term17 _85001 P Q.
Proof. exact (@lem3245584 _85001 P Q (@lem3245576 _85001 P Q)). Qed.
Lemma lem3245588 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term17 _85001 P Q.
Proof. exact (@lem3245587 _85001 P Q). Qed.
Lemma lem3245598 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3245599 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term15 _85001 P Q) = (term20 _85001 P Q).
Proof. exact (@lem3245598 (term16 _85001 P Q)). Qed.
Lemma lem3245601 (t : Prop) : (term21 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3245602 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term20 _85001 P Q) = ((term13 _85001 P Q) = (term14 _85001 P Q)).
Proof. exact (@lem3245601 ((term13 _85001 P Q) = (term14 _85001 P Q))). Qed.
Lemma lem3245603 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term15 _85001 P Q) = ((term13 _85001 P Q) = (term14 _85001 P Q)).
Proof. exact (TRANS (@lem3245599 _85001 P Q) (@lem3245602 _85001 P Q)). Qed.
Lemma lem3245624 {_85001 : Type'} (Q : _85001 -> Prop) : (term22 _85001 Q) = (term23 _85001 Q).
Proof. exact (fun_ext (fun P : _85001 -> Prop => @lem3245603 _85001 P Q)). Qed.
Lemma lem3245625 {_85001 : Type'} : (@all (_85001 -> Prop)) = (@all (_85001 -> Prop)).
Proof. exact (eq_refl (@all (_85001 -> Prop))). Qed.
Lemma lem3245626 {_85001 : Type'} (Q : _85001 -> Prop) : (term24 _85001 Q) = (term25 _85001 Q).
Proof. exact (MK_COMB (@lem3245625 _85001) (@lem3245624 _85001 Q)). Qed.
Lemma lem3245631 {_85001 : Type'} : (term26 _85001) = (term27 _85001).
Proof. exact (fun_ext (fun Q : _85001 -> Prop => @lem3245626 _85001 Q)). Qed.
Lemma lem3245632 {_85001 : Type'} : (@all (_85001 -> Prop)) = (@all (_85001 -> Prop)).
Proof. exact (eq_refl (@all (_85001 -> Prop))). Qed.
Lemma lem3245641 {_85001 : Type'} : (term28 _85001) = (term29 _85001).
Proof. exact (MK_COMB (@lem3245632 _85001) (@lem3245631 _85001)). Qed.
Lemma lem3245648 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term30 _85001 P Q x) = (term30 _85001 P Q x).
Proof. exact (eq_refl (term30 _85001 P Q x)). Qed.
Lemma lem3245649 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term31 _85001 P Q) = (term31 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245648 _85001 P Q x)). Qed.
Lemma lem3245650 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3245651 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term32 _85001 P Q) = (term32 _85001 P Q).
Proof. exact (MK_COMB (@lem3245650 _85001) (@lem3245649 _85001 P Q)). Qed.
Lemma lem3245652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3245653 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term14 _85001 P Q) = (term14 _85001 P Q).
Proof. exact (MK_COMB (@lem3245652) (@lem3245651 _85001 P Q)). Qed.
Lemma lem3245658 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term33 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term33 _85001 P Q x)). Qed.
Lemma lem3245659 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term34 _85001 P Q) = (term34 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245658 _85001 P Q x)). Qed.
Lemma lem3245660 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245661 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term13 _85001 P Q) = (term13 _85001 P Q).
Proof. exact (MK_COMB (@lem3245660 _85001) (@lem3245659 _85001 P Q)). Qed.
Lemma lem3245662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3245663 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term35 _85001 P Q) = (term35 _85001 P Q).
Proof. exact (MK_COMB (@lem3245662) (@lem3245661 _85001 P Q)). Qed.
Lemma lem3245664 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : ((term13 _85001 P Q) = (term14 _85001 P Q)) = ((term13 _85001 P Q) = (term14 _85001 P Q)).
Proof. exact (MK_COMB (@lem3245663 _85001 P Q) (@lem3245653 _85001 P Q)). Qed.
Lemma lem3245665 {_85001 : Type'} (Q : _85001 -> Prop) : (term23 _85001 Q) = (term23 _85001 Q).
Proof. exact (fun_ext (fun P : _85001 -> Prop => @lem3245664 _85001 P Q)). Qed.
Lemma lem3245666 {_85001 : Type'} : (@all (_85001 -> Prop)) = (@all (_85001 -> Prop)).
Proof. exact (eq_refl (@all (_85001 -> Prop))). Qed.
Lemma lem3245667 {_85001 : Type'} (Q : _85001 -> Prop) : (term25 _85001 Q) = (term25 _85001 Q).
Proof. exact (MK_COMB (@lem3245666 _85001) (@lem3245665 _85001 Q)). Qed.
Lemma lem3245668 {_85001 : Type'} : (term27 _85001) = (term27 _85001).
Proof. exact (fun_ext (fun Q : _85001 -> Prop => @lem3245667 _85001 Q)). Qed.
Lemma lem3245669 {_85001 : Type'} : (@all (_85001 -> Prop)) = (@all (_85001 -> Prop)).
Proof. exact (eq_refl (@all (_85001 -> Prop))). Qed.
Lemma lem3245670 {_85001 : Type'} : (term29 _85001) = (term29 _85001).
Proof. exact (MK_COMB (@lem3245669 _85001) (@lem3245668 _85001)). Qed.
Lemma lem3245701 {_85001 : Type'} : (term28 _85001) = (term29 _85001).
Proof. exact (TRANS (@lem3245641 _85001) (@lem3245670 _85001)). Qed.
Lemma lem3245702 {_85001 : Type'} : (term29 _85001) = (term28 _85001).
Proof. exact (SYM (@lem3245701 _85001)). Qed.
Lemma lem3245704 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3245705 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : ((term13 _85001 P Q) = (term14 _85001 P Q)) = (term15 _85001 P Q).
Proof. exact (@lem3245704 ((term13 _85001 P Q) = (term14 _85001 P Q))). Qed.
Lemma lem3245706 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term15 _85001 P Q) = ((term13 _85001 P Q) = (term14 _85001 P Q)).
Proof. exact (SYM (@lem3245705 _85001 P Q)). Qed.
Lemma lem3245707 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : term16 _85001 P Q.
Proof. exact (h1). Qed.
Lemma lem3245716 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term36 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (@lem17045 (P x) (Q x)). Qed.
Lemma lem3245719 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term33 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term33 _85001 P Q x)). Qed.
Lemma lem3245720 {_85001 : Type'} (P : _85001 -> Prop) : (term38 _85001 P) = (term39 _85001 P).
Proof. exact (@lem18394 _85001 P). Qed.
Lemma lem3245721 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term40 _85001 P Q) = (term41 _85001 P Q).
Proof. exact (@lem3245720 _85001 (term34 _85001 P Q)). Qed.
Lemma lem3245722 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term42 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term42 _85001 P Q x)). Qed.
Lemma lem3245723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3245724 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term43 _85001 P Q x) = (term36 _85001 P Q x).
Proof. exact (MK_COMB (@lem3245723) (@lem3245722 _85001 P Q x)). Qed.
Lemma lem3245725 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term43 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (TRANS (@lem3245724 _85001 P Q x) (@lem3245716 _85001 P Q x)). Qed.
Lemma lem3245726 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term44 _85001 P Q) = (term45 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245725 _85001 P Q x)). Qed.
Lemma lem3245727 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3245728 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term41 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (MK_COMB (@lem3245727 _85001) (@lem3245726 _85001 P Q)). Qed.
Lemma lem3245729 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term40 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (TRANS (@lem3245721 _85001 P Q) (@lem3245728 _85001 P Q)). Qed.
Lemma lem3245730 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term34 _85001 P Q) = (term34 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245719 _85001 P Q x)). Qed.
Lemma lem3245731 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245732 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term13 _85001 P Q) = (term13 _85001 P Q).
Proof. exact (MK_COMB (@lem3245731 _85001) (@lem3245730 _85001 P Q)). Qed.
Lemma lem3245738 {_85001 : Type'} (Q : _85001 -> Prop) (x : _85001) : (term47 _85001 Q x) = (Q x).
Proof. exact (@lem16933 (Q x)). Qed.
Lemma lem3245740 {_85001 : Type'} (P : _85001 -> Prop) (x : _85001) : (term48 _85001 P x) = (term48 _85001 P x).
Proof. exact (eq_refl (term48 _85001 P x)). Qed.
Lemma lem3245741 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term49 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (MK_COMB (@lem3245740 _85001 P x) (@lem3245738 _85001 Q x)). Qed.
Lemma lem3245742 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term50 _85001 P Q x) = (term49 _85001 P Q x).
Proof. exact (@lem17362 (P x) (term51 _85001 Q x)). Qed.
Lemma lem3245743 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term50 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (TRANS (@lem3245742 _85001 P Q x) (@lem3245741 _85001 P Q x)). Qed.
Lemma lem3245748 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term30 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (@lem17265 (P x) (term51 _85001 Q x)). Qed.
Lemma lem3245749 {_85001 : Type'} (P : _85001 -> Prop) : (term52 _85001 P) = (term53 _85001 P).
Proof. exact (@lem18392 _85001 P). Qed.
Lemma lem3245750 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term14 _85001 P Q) = (term54 _85001 P Q).
Proof. exact (@lem3245749 _85001 (term31 _85001 P Q)). Qed.
Lemma lem3245751 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term55 _85001 P Q x) = (term30 _85001 P Q x).
Proof. exact (eq_refl (term55 _85001 P Q x)). Qed.
Lemma lem3245752 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3245753 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term56 _85001 P Q x) = (term50 _85001 P Q x).
Proof. exact (MK_COMB (@lem3245752) (@lem3245751 _85001 P Q x)). Qed.
Lemma lem3245754 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term56 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (TRANS (@lem3245753 _85001 P Q x) (@lem3245743 _85001 P Q x)). Qed.
Lemma lem3245755 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term57 _85001 P Q) = (term34 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245754 _85001 P Q x)). Qed.
Lemma lem3245756 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245757 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term54 _85001 P Q) = (term13 _85001 P Q).
Proof. exact (MK_COMB (@lem3245756 _85001) (@lem3245755 _85001 P Q)). Qed.
Lemma lem3245758 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term14 _85001 P Q) = (term13 _85001 P Q).
Proof. exact (TRANS (@lem3245750 _85001 P Q) (@lem3245757 _85001 P Q)). Qed.
Lemma lem3245759 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term31 _85001 P Q) = (term45 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245748 _85001 P Q x)). Qed.
Lemma lem3245760 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3245761 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term32 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (MK_COMB (@lem3245760 _85001) (@lem3245759 _85001 P Q)). Qed.
Lemma lem3245762 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term58 _85001 P Q) = (term32 _85001 P Q).
Proof. exact (@lem16933 (term32 _85001 P Q)). Qed.
Lemma lem3245763 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term58 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (TRANS (@lem3245762 _85001 P Q) (@lem3245761 _85001 P Q)). Qed.
Lemma lem3245764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3245765 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term59 _85001 P Q) = (term60 _85001 P Q).
Proof. exact (MK_COMB (@lem3245764) (@lem3245729 _85001 P Q)). Qed.
Lemma lem3245766 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term61 _85001 P Q) = (term62 _85001 P Q).
Proof. exact (MK_COMB (@lem3245765 _85001 P Q) (@lem3245758 _85001 P Q)). Qed.
Lemma lem3245767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3245768 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term63 _85001 P Q) = (term63 _85001 P Q).
Proof. exact (MK_COMB (@lem3245767) (@lem3245732 _85001 P Q)). Qed.
Lemma lem3245769 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term64 _85001 P Q) = (term65 _85001 P Q).
Proof. exact (MK_COMB (@lem3245768 _85001 P Q) (@lem3245763 _85001 P Q)). Qed.
Lemma lem3245770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3245771 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term66 _85001 P Q) = (term67 _85001 P Q).
Proof. exact (MK_COMB (@lem3245770) (@lem3245769 _85001 P Q)). Qed.
Lemma lem3245772 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term68 _85001 P Q) = (term69 _85001 P Q).
Proof. exact (MK_COMB (@lem3245771 _85001 P Q) (@lem3245766 _85001 P Q)). Qed.
Lemma lem3245773 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term16 _85001 P Q) = (term68 _85001 P Q).
Proof. exact (@lem17646 (term13 _85001 P Q) (term14 _85001 P Q)). Qed.
Lemma lem3245774 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term16 _85001 P Q) = (term69 _85001 P Q).
Proof. exact (TRANS (@lem3245773 _85001 P Q) (@lem3245772 _85001 P Q)). Qed.
Lemma lem3245897 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3245898 {_85001 : Type'} (P : _85001 -> Prop) (Q : Prop) : (term70 _85001 P Q) = (term71 _85001 P Q).
Proof. exact (@lem3245897 _85001 P Q). Qed.
Lemma lem3245899 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term72 _85001 P Q) = (term73 _85001 P Q).
Proof. exact (@lem3245898 _85001 (term34 _85001 P Q) (term46 _85001 P Q)). Qed.
Lemma lem3245900 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term42 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term42 _85001 P Q x)). Qed.
Lemma lem3245901 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term74 _85001 P Q) = (term34 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245900 _85001 P Q x)). Qed.
Lemma lem3245902 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245903 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term75 _85001 P Q) = (term13 _85001 P Q).
Proof. exact (MK_COMB (@lem3245902 _85001) (@lem3245901 _85001 P Q)). Qed.
Lemma lem3245904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3245905 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term76 _85001 P Q) = (term63 _85001 P Q).
Proof. exact (MK_COMB (@lem3245904) (@lem3245903 _85001 P Q)). Qed.
Lemma lem3245906 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term46 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (eq_refl (term46 _85001 P Q)). Qed.
Lemma lem3245907 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term72 _85001 P Q) = (term65 _85001 P Q).
Proof. exact (MK_COMB (@lem3245905 _85001 P Q) (@lem3245906 _85001 P Q)). Qed.
Lemma lem3245908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3245909 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term77 _85001 P Q) = (term78 _85001 P Q).
Proof. exact (MK_COMB (@lem3245908) (@lem3245907 _85001 P Q)). Qed.
Lemma lem3245910 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term42 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term42 _85001 P Q x)). Qed.
Lemma lem3245911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3245912 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term79 _85001 P Q x) = (term80 _85001 P Q x).
Proof. exact (MK_COMB (@lem3245911) (@lem3245910 _85001 P Q x)). Qed.
Lemma lem3245913 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term46 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (eq_refl (term46 _85001 P Q)). Qed.
Lemma lem3245914 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term81 _85001 x P Q) = (term82 _85001 x P Q).
Proof. exact (MK_COMB (@lem3245912 _85001 P Q x) (@lem3245913 _85001 P Q)). Qed.
Lemma lem3245915 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term83 _85001 P Q) = (term84 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245914 _85001 x P Q)). Qed.
Lemma lem3245916 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245917 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term73 _85001 P Q) = (term85 _85001 P Q).
Proof. exact (MK_COMB (@lem3245916 _85001) (@lem3245915 _85001 P Q)). Qed.
Lemma lem3245918 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : ((term72 _85001 P Q) = (term73 _85001 P Q)) = ((term65 _85001 P Q) = (term85 _85001 P Q)).
Proof. exact (MK_COMB (@lem3245909 _85001 P Q) (@lem3245917 _85001 P Q)). Qed.
Lemma lem3245919 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term65 _85001 P Q) = (term85 _85001 P Q).
Proof. exact (EQ_MP (@lem3245918 _85001 P Q) (@lem3245899 _85001 P Q)). Qed.
Lemma lem3245920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3245921 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term67 _85001 P Q) = (term86 _85001 P Q).
Proof. exact (MK_COMB (@lem3245920) (@lem3245919 _85001 P Q)). Qed.
Lemma lem3245923 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3245924 {_85001 : Type'} (P : Prop) (Q : _85001 -> Prop) : (term87 _85001 P Q) = (term88 _85001 P Q).
Proof. exact (@lem3245923 _85001 P Q). Qed.
Lemma lem3245925 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term89 _85001 P Q) = (term90 _85001 P Q).
Proof. exact (@lem3245924 _85001 (term46 _85001 P Q) (term34 _85001 P Q)). Qed.
Lemma lem3245926 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term42 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term42 _85001 P Q x)). Qed.
Lemma lem3245927 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term74 _85001 P Q) = (term34 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245926 _85001 P Q x)). Qed.
Lemma lem3245928 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245929 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term75 _85001 P Q) = (term13 _85001 P Q).
Proof. exact (MK_COMB (@lem3245928 _85001) (@lem3245927 _85001 P Q)). Qed.
Lemma lem3245930 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term60 _85001 P Q) = (term60 _85001 P Q).
Proof. exact (eq_refl (term60 _85001 P Q)). Qed.
Lemma lem3245931 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term89 _85001 P Q) = (term62 _85001 P Q).
Proof. exact (MK_COMB (@lem3245930 _85001 P Q) (@lem3245929 _85001 P Q)). Qed.
Lemma lem3245932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3245933 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term91 _85001 P Q) = (term92 _85001 P Q).
Proof. exact (MK_COMB (@lem3245932) (@lem3245931 _85001 P Q)). Qed.
Lemma lem3245934 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term42 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term42 _85001 P Q x)). Qed.
Lemma lem3245935 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term60 _85001 P Q) = (term60 _85001 P Q).
Proof. exact (eq_refl (term60 _85001 P Q)). Qed.
Lemma lem3245936 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term93 _85001 P Q x) = (term94 _85001 P Q x).
Proof. exact (MK_COMB (@lem3245935 _85001 P Q) (@lem3245934 _85001 P Q x)). Qed.
Lemma lem3245937 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term95 _85001 P Q) = (term96 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245936 _85001 P Q x)). Qed.
Lemma lem3245938 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245939 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term90 _85001 P Q) = (term97 _85001 P Q).
Proof. exact (MK_COMB (@lem3245938 _85001) (@lem3245937 _85001 P Q)). Qed.
Lemma lem3245940 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : ((term89 _85001 P Q) = (term90 _85001 P Q)) = ((term62 _85001 P Q) = (term97 _85001 P Q)).
Proof. exact (MK_COMB (@lem3245933 _85001 P Q) (@lem3245939 _85001 P Q)). Qed.
Lemma lem3245941 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term62 _85001 P Q) = (term97 _85001 P Q).
Proof. exact (EQ_MP (@lem3245940 _85001 P Q) (@lem3245925 _85001 P Q)). Qed.
Lemma lem3245942 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term69 _85001 P Q) = (term98 _85001 P Q).
Proof. exact (MK_COMB (@lem3245921 _85001 P Q) (@lem3245941 _85001 P Q)). Qed.
Lemma lem3245944 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3245945 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term99 _85001 P Q) = (term100 _85001 P Q).
Proof. exact (@lem3245944 _85001 P Q). Qed.
Lemma lem3245946 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term101 _85001 P Q) = (term102 _85001 P Q).
Proof. exact (@lem3245945 _85001 (term84 _85001 P Q) (term96 _85001 P Q)). Qed.
Lemma lem3245947 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term103 _85001 P Q x) = (term82 _85001 x P Q).
Proof. exact (eq_refl (term103 _85001 P Q x)). Qed.
Lemma lem3245948 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term104 _85001 P Q) = (term84 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245947 _85001 x P Q)). Qed.
Lemma lem3245949 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245950 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term105 _85001 P Q) = (term85 _85001 P Q).
Proof. exact (MK_COMB (@lem3245949 _85001) (@lem3245948 _85001 P Q)). Qed.
Lemma lem3245951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3245952 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term106 _85001 P Q) = (term86 _85001 P Q).
Proof. exact (MK_COMB (@lem3245951) (@lem3245950 _85001 P Q)). Qed.
Lemma lem3245953 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term107 _85001 P Q x) = (term94 _85001 P Q x).
Proof. exact (eq_refl (term107 _85001 P Q x)). Qed.
Lemma lem3245954 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term108 _85001 P Q) = (term96 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245953 _85001 P Q x)). Qed.
Lemma lem3245955 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245956 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term109 _85001 P Q) = (term97 _85001 P Q).
Proof. exact (MK_COMB (@lem3245955 _85001) (@lem3245954 _85001 P Q)). Qed.
Lemma lem3245957 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term101 _85001 P Q) = (term98 _85001 P Q).
Proof. exact (MK_COMB (@lem3245952 _85001 P Q) (@lem3245956 _85001 P Q)). Qed.
Lemma lem3245958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3245959 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term110 _85001 P Q) = (term111 _85001 P Q).
Proof. exact (MK_COMB (@lem3245958) (@lem3245957 _85001 P Q)). Qed.
Lemma lem3245960 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term103 _85001 P Q x) = (term82 _85001 x P Q).
Proof. exact (eq_refl (term103 _85001 P Q x)). Qed.
Lemma lem3245961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3245962 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term112 _85001 P Q x) = (term113 _85001 x P Q).
Proof. exact (MK_COMB (@lem3245961) (@lem3245960 _85001 x P Q)). Qed.
Lemma lem3245963 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term107 _85001 P Q x) = (term94 _85001 P Q x).
Proof. exact (eq_refl (term107 _85001 P Q x)). Qed.
Lemma lem3245964 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term114 _85001 P Q x) = (term115 _85001 P Q x).
Proof. exact (MK_COMB (@lem3245962 _85001 x P Q) (@lem3245963 _85001 P Q x)). Qed.
Lemma lem3245965 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term116 _85001 P Q) = (term117 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245964 _85001 P Q x)). Qed.
Lemma lem3245966 {_85001 : Type'} : (@ex _85001) = (@ex _85001).
Proof. exact (eq_refl (@ex _85001)). Qed.
Lemma lem3245967 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term102 _85001 P Q) = (term118 _85001 P Q).
Proof. exact (MK_COMB (@lem3245966 _85001) (@lem3245965 _85001 P Q)). Qed.
Lemma lem3245968 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : ((term101 _85001 P Q) = (term102 _85001 P Q)) = ((term98 _85001 P Q) = (term118 _85001 P Q)).
Proof. exact (MK_COMB (@lem3245959 _85001 P Q) (@lem3245967 _85001 P Q)). Qed.
Lemma lem3245969 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term98 _85001 P Q) = (term118 _85001 P Q).
Proof. exact (EQ_MP (@lem3245968 _85001 P Q) (@lem3245946 _85001 P Q)). Qed.
Lemma lem3245971 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term69 _85001 P Q) = (term118 _85001 P Q).
Proof. exact (TRANS (@lem3245942 _85001 P Q) (@lem3245969 _85001 P Q)). Qed.
Lemma lem3245972 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term16 _85001 P Q) = (term118 _85001 P Q).
Proof. exact (TRANS (@lem3245774 _85001 P Q) (@lem3245971 _85001 P Q)). Qed.
Lemma lem3245973 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : term118 _85001 P Q.
Proof. exact (EQ_MP (@lem3245972 _85001 P Q) (@lem3245707 _85001 P Q h1)). Qed.
Lemma lem3245974 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term115 _85001 P Q x) : term115 _85001 P Q x.
Proof. exact (h1). Qed.
Lemma lem3245983 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term33 _85001 P Q x) = (term33 _85001 P Q x).
Proof. exact (eq_refl (term33 _85001 P Q x)). Qed.
Lemma lem3245996 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term37 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (eq_refl (term37 _85001 P Q x)). Qed.
Lemma lem3245997 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term45 _85001 P Q) = (term45 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3245996 _85001 P Q x)). Qed.
Lemma lem3245998 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3245999 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term46 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (MK_COMB (@lem3245998 _85001) (@lem3245997 _85001 P Q)). Qed.
Lemma lem3246000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3246001 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term60 _85001 P Q) = (term60 _85001 P Q).
Proof. exact (MK_COMB (@lem3246000) (@lem3245999 _85001 P Q)). Qed.
Lemma lem3246002 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term94 _85001 P Q x) = (term94 _85001 P Q x).
Proof. exact (MK_COMB (@lem3246001 _85001 P Q) (@lem3245983 _85001 P Q x)). Qed.
Lemma lem3246015 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term37 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (eq_refl (term37 _85001 P Q x)). Qed.
Lemma lem3246016 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term45 _85001 P Q) = (term45 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3246015 _85001 P Q x)). Qed.
Lemma lem3246017 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3246018 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term46 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (MK_COMB (@lem3246017 _85001) (@lem3246016 _85001 P Q)). Qed.
Lemma lem3246029 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term80 _85001 P Q x) = (term80 _85001 P Q x).
Proof. exact (eq_refl (term80 _85001 P Q x)). Qed.
Lemma lem3246030 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term82 _85001 x P Q) = (term82 _85001 x P Q).
Proof. exact (MK_COMB (@lem3246029 _85001 P Q x) (@lem3246018 _85001 P Q)). Qed.
Lemma lem3246031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3246032 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term113 _85001 x P Q) = (term113 _85001 x P Q).
Proof. exact (MK_COMB (@lem3246031) (@lem3246030 _85001 x P Q)). Qed.
Lemma lem3246033 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term115 _85001 P Q x) = (term115 _85001 P Q x).
Proof. exact (MK_COMB (@lem3246032 _85001 x P Q) (@lem3246002 _85001 P Q x)). Qed.
Lemma lem3246034 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term115 _85001 P Q x) : term115 _85001 P Q x.
Proof. exact (EQ_MP (@lem3246033 _85001 P Q x) (@lem3245974 _85001 P Q x h1)). Qed.
Lemma lem3246035 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term82 _85001 x P Q.
Proof. exact (h1). Qed.
Lemma lem3246036 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term94 _85001 P Q x.
Proof. exact (h1). Qed.
Lemma lem3246037 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term46 _85001 P Q.
Proof. exact (proj2 (@lem3246035 _85001 x P Q h1)). Qed.
Lemma lem3246038 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term33 _85001 P Q x.
Proof. exact (proj1 (@lem3246035 _85001 x P Q h1)). Qed.
Lemma lem3246041 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term33 _85001 P Q x.
Proof. exact (proj2 (@lem3246036 _85001 P Q x h1)). Qed.
Lemma lem3246042 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term46 _85001 P Q.
Proof. exact (proj1 (@lem3246036 _85001 P Q x h1)). Qed.
Lemma lem3246052 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term37 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (eq_refl (term37 _85001 P Q x)). Qed.
Lemma lem3246053 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term45 _85001 P Q) = (term45 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3246052 _85001 P Q x)). Qed.
Lemma lem3246054 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3246056 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term46 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (MK_COMB (@lem3246054 _85001) (@lem3246053 _85001 P Q)). Qed.
Lemma lem3246057 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term46 _85001 P Q.
Proof. exact (EQ_MP (@lem3246056 _85001 P Q) (@lem3246037 _85001 x P Q h1)). Qed.
Lemma lem3246073 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) : (term37 _85001 P Q x) = (term37 _85001 P Q x).
Proof. exact (eq_refl (term37 _85001 P Q x)). Qed.
Lemma lem3246074 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term45 _85001 P Q) = (term45 _85001 P Q).
Proof. exact (fun_ext (fun x : _85001 => @lem3246073 _85001 P Q x)). Qed.
Lemma lem3246075 {_85001 : Type'} : (@all _85001) = (@all _85001).
Proof. exact (eq_refl (@all _85001)). Qed.
Lemma lem3246077 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term46 _85001 P Q) = (term46 _85001 P Q).
Proof. exact (MK_COMB (@lem3246075 _85001) (@lem3246074 _85001 P Q)). Qed.
Lemma lem3246078 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term46 _85001 P Q.
Proof. exact (EQ_MP (@lem3246077 _85001 P Q) (@lem3246042 _85001 P Q x h1)). Qed.
Lemma lem3246087 {_85001 : Type'} (_33247 : _85001) (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term119 _85001 P Q _33247.
Proof. exact (@lem3246057 _85001 x P Q h1 _33247). Qed.
Lemma lem3246088 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33247 : _85001) : (term119 _85001 P Q _33247) = (term37 _85001 P Q _33247).
Proof. exact (eq_refl (term119 _85001 P Q _33247)). Qed.
Lemma lem3246090 {_85001 : Type'} (_33248 : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term119 _85001 P Q _33248.
Proof. exact (@lem3246078 _85001 P Q x h1 _33248). Qed.
Lemma lem3246091 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33248 : _85001) : (term119 _85001 P Q _33248) = (term37 _85001 P Q _33248).
Proof. exact (eq_refl (term119 _85001 P Q _33248)). Qed.
Lemma lem3246098 {_85001 : Type'} (_33247 : _85001) (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term37 _85001 P Q _33247.
Proof. exact (EQ_MP (@lem3246088 _85001 P Q _33247) (@lem3246087 _85001 _33247 x P Q h1)). Qed.
Lemma lem3246108 {_85001 : Type'} (_33248 : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term37 _85001 P Q _33248.
Proof. exact (EQ_MP (@lem3246091 _85001 P Q _33248) (@lem3246090 _85001 _33248 P Q x h1)). Qed.
Lemma lem3246114 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : P x.
Proof. exact (proj1 (@lem3246038 _85001 x P Q h1)). Qed.
Lemma lem3246115 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term120 _85001 P x.
Proof. exact (fun h0 : term51 _85001 P x => @lem3246114 _85001 x P Q h1). Qed.
Lemma lem3246117 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3246118 {_85001 : Type'} (P : _85001 -> Prop) (x : _85001) : (term120 _85001 P x) = (P x).
Proof. exact (@lem3246117 (P x)). Qed.
Lemma lem3246119 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : P x.
Proof. exact (EQ_MP (@lem3246118 _85001 P x) (@lem3246115 _85001 x P Q h1)). Qed.
Lemma lem3246121 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : Q x.
Proof. exact (proj2 (@lem3246038 _85001 x P Q h1)). Qed.
Lemma lem3246122 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term120 _85001 Q x.
Proof. exact (fun h0 : term51 _85001 Q x => @lem3246121 _85001 x P Q h1). Qed.
Lemma lem3246124 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3246125 {_85001 : Type'} (Q : _85001 -> Prop) (x : _85001) : (term120 _85001 Q x) = (Q x).
Proof. exact (@lem3246124 (Q x)). Qed.
Lemma lem3246126 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : Q x.
Proof. exact (EQ_MP (@lem3246125 _85001 Q x) (@lem3246122 _85001 x P Q h1)). Qed.
Lemma lem3246128 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3246129 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33247 : _85001) : (term37 _85001 P Q _33247) = (term36 _85001 P Q _33247).
Proof. exact (@lem3246128 (P _33247) (Q _33247)). Qed.
Lemma lem3246131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3246132 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33247 : _85001) : (term36 _85001 P Q _33247) = (term124 _85001 P Q _33247).
Proof. exact (@lem3246131 (term33 _85001 P Q _33247)). Qed.
Lemma lem3246133 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33247 : _85001) : (term37 _85001 P Q _33247) = (term124 _85001 P Q _33247).
Proof. exact (TRANS (@lem3246129 _85001 P Q _33247) (@lem3246132 _85001 P Q _33247)). Qed.
Lemma lem3246135 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term33 _85001 P Q x.
Proof. exact (conj (@lem3246119 _85001 x P Q h1) (@lem3246126 _85001 x P Q h1)). Qed.
Lemma lem3246137 {_85001 : Type'} (_33247 : _85001) (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term124 _85001 P Q _33247.
Proof. exact (EQ_MP (@lem3246133 _85001 P Q _33247) (@lem3246098 _85001 _33247 x P Q h1)). Qed.
Lemma lem3246138 {_85001 : Type'} (_33247 : _85001) (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term124 _85001 P Q _33247.
Proof. exact (@lem3246137 _85001 _33247 x P Q h1). Qed.
Lemma lem3246139 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term124 _85001 P Q x.
Proof. exact (@lem3246138 _85001 x x P Q h1). Qed.
Lemma lem3246142 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : False.
Proof. exact (@lem3246139 _85001 x P Q h1 (@lem3246135 _85001 x P Q h1)). Qed.
Lemma lem3246143 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : term125.
Proof. exact (fun h0 : ~ False => @lem3246142 _85001 x P Q h1). Qed.
Lemma lem3246145 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3246146 : term125 = False.
Proof. exact (@lem3246145 False). Qed.
Lemma lem3246147 {_85001 : Type'} (x : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term82 _85001 x P Q) : False.
Proof. exact (EQ_MP (@lem3246146) (@lem3246143 _85001 x P Q h1)). Qed.
Lemma lem3246149 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : P x.
Proof. exact (proj1 (@lem3246041 _85001 P Q x h1)). Qed.
Lemma lem3246150 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term120 _85001 P x.
Proof. exact (fun h0 : term51 _85001 P x => @lem3246149 _85001 P Q x h1). Qed.
Lemma lem3246152 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3246153 {_85001 : Type'} (P : _85001 -> Prop) (x : _85001) : (term120 _85001 P x) = (P x).
Proof. exact (@lem3246152 (P x)). Qed.
Lemma lem3246154 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : P x.
Proof. exact (EQ_MP (@lem3246153 _85001 P x) (@lem3246150 _85001 P Q x h1)). Qed.
Lemma lem3246156 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : Q x.
Proof. exact (proj2 (@lem3246041 _85001 P Q x h1)). Qed.
Lemma lem3246157 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term120 _85001 Q x.
Proof. exact (fun h0 : term51 _85001 Q x => @lem3246156 _85001 P Q x h1). Qed.
Lemma lem3246159 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3246160 {_85001 : Type'} (Q : _85001 -> Prop) (x : _85001) : (term120 _85001 Q x) = (Q x).
Proof. exact (@lem3246159 (Q x)). Qed.
Lemma lem3246161 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : Q x.
Proof. exact (EQ_MP (@lem3246160 _85001 Q x) (@lem3246157 _85001 P Q x h1)). Qed.
Lemma lem3246163 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3246164 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33248 : _85001) : (term37 _85001 P Q _33248) = (term36 _85001 P Q _33248).
Proof. exact (@lem3246163 (P _33248) (Q _33248)). Qed.
Lemma lem3246166 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3246167 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33248 : _85001) : (term36 _85001 P Q _33248) = (term124 _85001 P Q _33248).
Proof. exact (@lem3246166 (term33 _85001 P Q _33248)). Qed.
Lemma lem3246168 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (_33248 : _85001) : (term37 _85001 P Q _33248) = (term124 _85001 P Q _33248).
Proof. exact (TRANS (@lem3246164 _85001 P Q _33248) (@lem3246167 _85001 P Q _33248)). Qed.
Lemma lem3246170 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term33 _85001 P Q x.
Proof. exact (conj (@lem3246154 _85001 P Q x h1) (@lem3246161 _85001 P Q x h1)). Qed.
Lemma lem3246172 {_85001 : Type'} (_33248 : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term124 _85001 P Q _33248.
Proof. exact (EQ_MP (@lem3246168 _85001 P Q _33248) (@lem3246108 _85001 _33248 P Q x h1)). Qed.
Lemma lem3246173 {_85001 : Type'} (_33248 : _85001) (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term124 _85001 P Q _33248.
Proof. exact (@lem3246172 _85001 _33248 P Q x h1). Qed.
Lemma lem3246174 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term124 _85001 P Q x.
Proof. exact (@lem3246173 _85001 x P Q x h1). Qed.
Lemma lem3246177 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : False.
Proof. exact (@lem3246174 _85001 P Q x h1 (@lem3246170 _85001 P Q x h1)). Qed.
Lemma lem3246178 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : term125.
Proof. exact (fun h0 : ~ False => @lem3246177 _85001 P Q x h1). Qed.
Lemma lem3246180 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3246181 : term125 = False.
Proof. exact (@lem3246180 False). Qed.
Lemma lem3246182 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term94 _85001 P Q x) : False.
Proof. exact (EQ_MP (@lem3246181) (@lem3246178 _85001 P Q x h1)). Qed.
Lemma lem3246183 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term115 _85001 P Q x) : False.
Proof. exact (or_elim (@lem3246034 _85001 P Q x h1) (fun h0 : term82 _85001 x P Q => @lem3246147 _85001 x P Q h0) (fun h0 : term94 _85001 P Q x => @lem3246182 _85001 P Q x h0)). Qed.
Lemma lem3246184 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term115 _85001 P Q x) : (term115 _85001 P Q x) = False.
Proof. exact (prop_ext (fun h2 : term115 _85001 P Q x => @lem3246183 _85001 P Q x h1) (fun h2 : False => @lem3246034 _85001 P Q x h1)). Qed.
Lemma lem3246185 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (x : _85001) (h1 : term115 _85001 P Q x) : False.
Proof. exact (EQ_MP (@lem3246184 _85001 P Q x h1) (@lem3246034 _85001 P Q x h1)). Qed.
Lemma lem3246186 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : False.
Proof. exact (ex_elim (@lem3245973 _85001 P Q h1) (fun x : _85001 => fun h0 : term117 _85001 P Q x => @lem3246185 _85001 P Q x h0)). Qed.
Lemma lem3246187 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : (term16 _85001 P Q) = False.
Proof. exact (prop_ext (fun h2 : term16 _85001 P Q => @lem3246186 _85001 P Q h1) (fun h2 : False => @lem3245707 _85001 P Q h1)). Qed.
Lemma lem3246188 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : False.
Proof. exact (EQ_MP (@lem3246187 _85001 P Q h1) (@lem3245707 _85001 P Q h1)). Qed.
Lemma lem3246189 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term15 _85001 P Q.
Proof. exact (fun h0 : term16 _85001 P Q => @lem3246188 _85001 P Q h0). Qed.
Lemma lem3246190 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term13 _85001 P Q) = (term14 _85001 P Q).
Proof. exact (EQ_MP (@lem3245706 _85001 P Q) (@lem3246189 _85001 P Q)). Qed.
Lemma lem3246195 {_85001 : Type'} (Q : _85001 -> Prop) : term25 _85001 Q.
Proof. exact (fun P : _85001 -> Prop => @lem3246190 _85001 P Q). Qed.
Lemma lem3246200 {_85001 : Type'} : term29 _85001.
Proof. exact (fun Q : _85001 -> Prop => @lem3246195 _85001 Q). Qed.
Lemma lem3246201 {_85001 : Type'} : term28 _85001.
Proof. exact (EQ_MP (@lem3245702 _85001) (@lem3246200 _85001)). Qed.
Lemma lem3246202 {_85001 : Type'} (Q : _85001 -> Prop) : term126 _85001 Q.
Proof. exact (@lem3246201 _85001 Q). Qed.
Lemma lem3246203 {_85001 : Type'} (Q : _85001 -> Prop) : (term126 _85001 Q) = (term24 _85001 Q).
Proof. exact (eq_refl (term126 _85001 Q)). Qed.
Lemma lem3246204 {_85001 : Type'} (Q : _85001 -> Prop) : term24 _85001 Q.
Proof. exact (EQ_MP (@lem3246203 _85001 Q) (@lem3246202 _85001 Q)). Qed.
Lemma lem3246205 {_85001 : Type'} (Q : _85001 -> Prop) (P : _85001 -> Prop) : term127 _85001 Q P.
Proof. exact (@lem3246204 _85001 Q P). Qed.
Lemma lem3246206 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term127 _85001 Q P) = (term15 _85001 P Q).
Proof. exact (eq_refl (term127 _85001 Q P)). Qed.
Lemma lem3246207 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term15 _85001 P Q.
Proof. exact (EQ_MP (@lem3246206 _85001 P Q) (@lem3246205 _85001 Q P)). Qed.
Lemma lem3246209 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term15 _85001 P Q.
Proof. exact (@lem3245588 _85001 P Q (@lem3246207 _85001 P Q)). Qed.
Lemma lem3246210 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : False.
Proof. exact (@lem3246209 _85001 P Q (@lem3245572 _85001 P Q h1)). Qed.
Lemma lem3246211 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : (term16 _85001 P Q) = False.
Proof. exact (prop_ext (fun h2 : term16 _85001 P Q => @lem3246210 _85001 P Q h1) (fun h2 : False => @lem3245572 _85001 P Q h1)). Qed.
Lemma lem3246212 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) (h1 : term16 _85001 P Q) : False.
Proof. exact (EQ_MP (@lem3246211 _85001 P Q h1) (@lem3245572 _85001 P Q h1)). Qed.
Lemma lem3246213 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : term15 _85001 P Q.
Proof. exact (fun h0 : term16 _85001 P Q => @lem3246212 _85001 P Q h0). Qed.
Lemma lem3246226 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term13 _85001 P Q) = (term14 _85001 P Q).
Proof. exact (EQ_MP (@lem3245571 _85001 P Q) (@lem3246213 _85001 P Q)). Qed.
Lemma lem3246227 {A : Type'} (P : type686 A) (Q : type686 A) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem3246226 (A -> Prop) P Q). Qed.
Lemma lem3246228 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term130 A t u P) = (term131 A t u P).
Proof. exact (@lem3246227 A (term132 A t u) P). Qed.
Lemma lem3246229 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term133 A t u s) = (term134 A s t u).
Proof. exact (eq_refl (term133 A t u s)). Qed.
Lemma lem3246230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3246231 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term135 A t u s) = (term136 A s t u).
Proof. exact (MK_COMB (@lem3246230) (@lem3246229 A s t u)). Qed.
Lemma lem3246232 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3246233 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : (term137 A t u P s) = (term138 A t u P s).
Proof. exact (MK_COMB (@lem3246231 A s t u) (@lem3246232 A P s)). Qed.
Lemma lem3246234 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A t u P) = (term140 A t u P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3246233 A t u P s)). Qed.
Lemma lem3246235 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246236 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term130 A t u P) = (term141 A t u P).
Proof. exact (MK_COMB (@lem3246235 A) (@lem3246234 A t u P)). Qed.
Lemma lem3246237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246238 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term142 A t u P) = (term143 A t u P).
Proof. exact (MK_COMB (@lem3246237) (@lem3246236 A t u P)). Qed.
Lemma lem3246239 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term133 A t u s) = (term134 A s t u).
Proof. exact (eq_refl (term133 A t u s)). Qed.
Lemma lem3246240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3246241 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term144 A t u s) = (term145 A s t u).
Proof. exact (MK_COMB (@lem3246240) (@lem3246239 A s t u)). Qed.
Lemma lem3246242 {A : Type'} (P : type686 A) (s : A -> Prop) : (term146 A P s) = (term146 A P s).
Proof. exact (eq_refl (term146 A P s)). Qed.
Lemma lem3246243 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : (term147 A t u P s) = (term148 A t u P s).
Proof. exact (MK_COMB (@lem3246241 A s t u) (@lem3246242 A P s)). Qed.
Lemma lem3246244 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term149 A t u P) = (term150 A t u P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3246243 A t u P s)). Qed.
Lemma lem3246245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246246 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term151 A t u P) = (term152 A t u P).
Proof. exact (MK_COMB (@lem3246245 A) (@lem3246244 A t u P)). Qed.
Lemma lem3246247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246248 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term131 A t u P) = (term153 A t u P).
Proof. exact (MK_COMB (@lem3246247) (@lem3246246 A t u P)). Qed.
Lemma lem3246249 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term130 A t u P) = (term131 A t u P)) = ((term141 A t u P) = (term153 A t u P)).
Proof. exact (MK_COMB (@lem3246238 A t u P) (@lem3246248 A t u P)). Qed.
Lemma lem3246250 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term141 A t u P) = (term153 A t u P).
Proof. exact (EQ_MP (@lem3246249 A t u P) (@lem3246228 A t u P)). Qed.
Lemma lem3246257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246258 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term143 A t u P) = (term154 A t u P).
Proof. exact (MK_COMB (@lem3246257) (@lem3246250 A t u P)). Qed.
Lemma lem3246264 {_85001 : Type'} (P : _85001 -> Prop) (Q : _85001 -> Prop) : (term13 _85001 P Q) = (term14 _85001 P Q).
Proof. exact (EQ_MP (@lem3245571 _85001 P Q) (@lem3246213 _85001 P Q)). Qed.
Lemma lem3246265 {A : Type'} (P : type686 A) (Q : type686 A) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem3246264 (A -> Prop) P Q). Qed.
Lemma lem3246266 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term155 A t u P t') = (term156 A t u P t').
Proof. exact (@lem3246265 A (term157 A t' t) (term158 A u P t')). Qed.
Lemma lem3246267 {A : Type'} (u' : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term159 A t' t u') = (@SUBSET A t' t).
Proof. exact (eq_refl (term159 A t' t u')). Qed.
Lemma lem3246268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3246269 {A : Type'} (u' : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term160 A t' t u') = (term161 A t' t).
Proof. exact (MK_COMB (@lem3246268) (@lem3246267 A u' t' t)). Qed.
Lemma lem3246270 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term162 A u P t' u') = (term163 A u P t' u').
Proof. exact (eq_refl (term162 A u P t' u')). Qed.
Lemma lem3246271 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term164 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (MK_COMB (@lem3246269 A u' t' t) (@lem3246270 A u P t' u')). Qed.
Lemma lem3246272 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term166 A t u P t') = (term167 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246271 A t u P t' u')). Qed.
Lemma lem3246273 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246274 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term155 A t u P t') = (term168 A t u P t').
Proof. exact (MK_COMB (@lem3246273 A) (@lem3246272 A t u P t')). Qed.
Lemma lem3246275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246276 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term169 A t u P t') = (term170 A t u P t').
Proof. exact (MK_COMB (@lem3246275) (@lem3246274 A t u P t')). Qed.
Lemma lem3246277 {A : Type'} (u' : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term159 A t' t u') = (@SUBSET A t' t).
Proof. exact (eq_refl (term159 A t' t u')). Qed.
Lemma lem3246278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3246279 {A : Type'} (u' : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term171 A t' t u') = (term172 A t' t).
Proof. exact (MK_COMB (@lem3246278) (@lem3246277 A u' t' t)). Qed.
Lemma lem3246280 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term162 A u P t' u') = (term163 A u P t' u').
Proof. exact (eq_refl (term162 A u P t' u')). Qed.
Lemma lem3246281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246282 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term173 A u P t' u') = (term174 A u P t' u').
Proof. exact (MK_COMB (@lem3246281) (@lem3246280 A u P t' u')). Qed.
Lemma lem3246283 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term175 A t u P t' u') = (term176 A t u P t' u').
Proof. exact (MK_COMB (@lem3246279 A u' t' t) (@lem3246282 A u P t' u')). Qed.
Lemma lem3246284 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term177 A t u P t') = (term178 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246283 A t u P t' u')). Qed.
Lemma lem3246285 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246286 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term179 A t u P t') = (term180 A t u P t').
Proof. exact (MK_COMB (@lem3246285 A) (@lem3246284 A t u P t')). Qed.
Lemma lem3246287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246288 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term156 A t u P t') = (term181 A t u P t').
Proof. exact (MK_COMB (@lem3246287) (@lem3246286 A t u P t')). Qed.
Lemma lem3246289 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term155 A t u P t') = (term156 A t u P t')) = ((term168 A t u P t') = (term181 A t u P t')).
Proof. exact (MK_COMB (@lem3246276 A t u P t') (@lem3246288 A t u P t')). Qed.
Lemma lem3246290 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term168 A t u P t') = (term181 A t u P t').
Proof. exact (EQ_MP (@lem3246289 A t u P t') (@lem3246266 A t u P t')). Qed.
Lemma lem3246299 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term182 A t u P) = (term183 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246290 A t u P t')). Qed.
Lemma lem3246300 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246301 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term184 A t u P) = (term185 A t u P).
Proof. exact (MK_COMB (@lem3246300 A) (@lem3246299 A t u P)). Qed.
Lemma lem3246306 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term141 A t u P) = (term184 A t u P)) = ((term153 A t u P) = (term185 A t u P)).
Proof. exact (MK_COMB (@lem3246258 A t u P) (@lem3246301 A t u P)). Qed.
Lemma lem3246309 {A : Type'} (t : A -> Prop) (P : type686 A) : (term186 A t P) = (term187 A t P).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3246306 A t u P)). Qed.
Lemma lem3246310 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246311 {A : Type'} (t : A -> Prop) (P : type686 A) : (term188 A t P) = (term189 A t P).
Proof. exact (MK_COMB (@lem3246310 A) (@lem3246309 A t P)). Qed.
Lemma lem3246316 {A : Type'} (P : type686 A) : (term190 A P) = (term191 A P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3246311 A t P)). Qed.
Lemma lem3246317 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246318 {A : Type'} (P : type686 A) : (term192 A P) = (term193 A P).
Proof. exact (MK_COMB (@lem3246317 A) (@lem3246316 A P)). Qed.
Lemma lem3246323 {A : Type'} (P : type686 A) : (term193 A P) = (term192 A P).
Proof. exact (SYM (@lem3246318 A P)). Qed.
Lemma lem3246335 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term10 A t u P) = (term11 A t u P).
Proof. exact (EQ_MP (@lem3245556 A t u P) (@lem3245555 A t P u)). Qed.
Lemma lem3246336 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term10 A t u P) = (term11 A t u P).
Proof. exact (@lem3246335 A t u P). Qed.
Lemma lem3246337 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term194 A t u P) = (term195 A t u P).
Proof. exact (@lem3246336 A t u (term196 A P)). Qed.
Lemma lem3246338 {A : Type'} (P : type686 A) (s : A -> Prop) : (term197 A P s) = (term146 A P s).
Proof. exact (eq_refl (term197 A P s)). Qed.
Lemma lem3246339 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term145 A s t u) = (term145 A s t u).
Proof. exact (eq_refl (term145 A s t u)). Qed.
Lemma lem3246340 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : (term198 A t u P s) = (term148 A t u P s).
Proof. exact (MK_COMB (@lem3246339 A s t u) (@lem3246338 A P s)). Qed.
Lemma lem3246341 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term199 A t u P) = (term150 A t u P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3246340 A t u P s)). Qed.
Lemma lem3246342 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246343 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term194 A t u P) = (term152 A t u P).
Proof. exact (MK_COMB (@lem3246342 A) (@lem3246341 A t u P)). Qed.
Lemma lem3246344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246345 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term200 A t u P) = (term201 A t u P).
Proof. exact (MK_COMB (@lem3246344) (@lem3246343 A t u P)). Qed.
Lemma lem3246346 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term202 A P t' u') = (term203 A P t' u').
Proof. exact (eq_refl (term202 A P t' u')). Qed.
Lemma lem3246347 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term204 A t' t u' u) = (term204 A t' t u' u).
Proof. exact (eq_refl (term204 A t' t u' u)). Qed.
Lemma lem3246348 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term205 A t u P t' u') = (term206 A t u P t' u').
Proof. exact (MK_COMB (@lem3246347 A t' t u' u) (@lem3246346 A P t' u')). Qed.
Lemma lem3246349 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term207 A t u P t') = (term208 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246348 A t u P t' u')). Qed.
Lemma lem3246350 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246351 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term209 A t u P t') = (term210 A t u P t').
Proof. exact (MK_COMB (@lem3246350 A) (@lem3246349 A t u P t')). Qed.
Lemma lem3246352 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term211 A t u P) = (term212 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246351 A t u P t')). Qed.
Lemma lem3246353 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246354 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term195 A t u P) = (term213 A t u P).
Proof. exact (MK_COMB (@lem3246353 A) (@lem3246352 A t u P)). Qed.
Lemma lem3246355 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term194 A t u P) = (term195 A t u P)) = ((term152 A t u P) = (term213 A t u P)).
Proof. exact (MK_COMB (@lem3246345 A t u P) (@lem3246354 A t u P)). Qed.
Lemma lem3246356 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term152 A t u P) = (term213 A t u P).
Proof. exact (EQ_MP (@lem3246355 A t u P) (@lem3246337 A t u P)). Qed.
Lemma lem3246369 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246370 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term153 A t u P) = (term214 A t u P).
Proof. exact (MK_COMB (@lem3246369) (@lem3246356 A t u P)). Qed.
Lemma lem3246371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246372 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term154 A t u P) = (term215 A t u P).
Proof. exact (MK_COMB (@lem3246371) (@lem3246370 A t u P)). Qed.
Lemma lem3246385 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term185 A t u P) = (term185 A t u P).
Proof. exact (eq_refl (term185 A t u P)). Qed.
Lemma lem3246386 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term153 A t u P) = (term185 A t u P)) = ((term214 A t u P) = (term185 A t u P)).
Proof. exact (MK_COMB (@lem3246372 A t u P) (@lem3246385 A t u P)). Qed.
Lemma lem3246389 {A : Type'} (t : A -> Prop) (P : type686 A) : (term187 A t P) = (term216 A t P).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3246386 A t u P)). Qed.
Lemma lem3246390 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246391 {A : Type'} (t : A -> Prop) (P : type686 A) : (term189 A t P) = (term217 A t P).
Proof. exact (MK_COMB (@lem3246390 A) (@lem3246389 A t P)). Qed.
Lemma lem3246396 {A : Type'} (P : type686 A) : (term191 A P) = (term218 A P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3246391 A t P)). Qed.
Lemma lem3246397 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246398 {A : Type'} (P : type686 A) : (term193 A P) = (term219 A P).
Proof. exact (MK_COMB (@lem3246397 A) (@lem3246396 A P)). Qed.
Lemma lem3246403 {A : Type'} (P : type686 A) : (term219 A P) = (term193 A P).
Proof. exact (SYM (@lem3246398 A P)). Qed.
Lemma lem3246405 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3246406 {A : Type'} (P : type686 A) : (term219 A P) = (term220 A P).
Proof. exact (@lem3246405 (term219 A P)). Qed.
Lemma lem3246407 {A : Type'} (P : type686 A) : (term220 A P) = (term219 A P).
Proof. exact (SYM (@lem3246406 A P)). Qed.
Lemma lem3246408 {A : Type'} (P : type686 A) (h1 : term221 A P) : term221 A P.
Proof. exact (h1). Qed.
Lemma lem3246411 {A : Type'} (P : type686 A) (h1 : term220 A P) : term220 A P.
Proof. exact (h1). Qed.
Lemma lem3246412 {A : Type'} (P : type686 A) : term222 A P.
Proof. exact (fun h0 : term220 A P => @lem3246411 A P h0). Qed.
Lemma lem3246413 {A : Type'} (P : type686 A) (h1 : term222 A P) : term222 A P.
Proof. exact (h1). Qed.
Lemma lem3246414 {A : Type'} (P : type686 A) (h1 : term220 A P) : term220 A P.
Proof. exact (h1). Qed.
Lemma lem3246415 {A : Type'} (P : type686 A) (h1 : term220 A P) (h2 : term222 A P) : term220 A P.
Proof. exact (@lem3246413 A P h2 (@lem3246414 A P h1)). Qed.
Lemma lem3246416 {A : Type'} (P : type686 A) (h1 : term220 A P) : term223 A P.
Proof. exact (fun h0 : term222 A P => @lem3246415 A P h1 h0). Qed.
Lemma lem3246417 {A : Type'} (P : type686 A) (h1 : term222 A P) : term222 A P.
Proof. exact (h1). Qed.
Lemma lem3246418 {A : Type'} (P : type686 A) (h1 : term220 A P) (h2 : term222 A P) : term220 A P.
Proof. exact (@lem3246416 A P h1 (@lem3246417 A P h2)). Qed.
Lemma lem3246419 {A : Type'} (P : type686 A) (h1 : term222 A P) : term222 A P.
Proof. exact (fun h0 : term220 A P => @lem3246418 A P h0 h1). Qed.
Lemma lem3246420 {A : Type'} (P : type686 A) : term224 A P.
Proof. exact (fun h0 : term222 A P => @lem3246419 A P h0). Qed.
Lemma lem3246423 {A : Type'} (P : type686 A) : term222 A P.
Proof. exact (@lem3246420 A P (@lem3246412 A P)). Qed.
Lemma lem3246424 {A : Type'} (P : type686 A) : term222 A P.
Proof. exact (@lem3246423 A P). Qed.
Lemma lem3246430 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3246431 {A : Type'} (P : type686 A) : (term220 A P) = (term225 A P).
Proof. exact (@lem3246430 (term221 A P)). Qed.
Lemma lem3246433 (t : Prop) : (term21 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3246434 {A : Type'} (P : type686 A) : (term225 A P) = (term219 A P).
Proof. exact (@lem3246433 (term219 A P)). Qed.
Lemma lem3246439 {A : Type'} (P : type686 A) : (term220 A P) = (term219 A P).
Proof. exact (TRANS (@lem3246431 A P) (@lem3246434 A P)). Qed.
Lemma lem3246468 {A : Type'} : (term226 A) = (term227 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3246439 A P)). Qed.
Lemma lem3246469 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3246478 {A : Type'} : (term228 A) = (term229 A).
Proof. exact (MK_COMB (@lem3246469 A) (@lem3246468 A)). Qed.
Lemma lem3246489 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term176 A t u P t' u') = (term176 A t u P t' u').
Proof. exact (eq_refl (term176 A t u P t' u')). Qed.
Lemma lem3246490 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term178 A t u P t') = (term178 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246489 A t u P t' u')). Qed.
Lemma lem3246491 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246492 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term180 A t u P t') = (term180 A t u P t').
Proof. exact (MK_COMB (@lem3246491 A) (@lem3246490 A t u P t')). Qed.
Lemma lem3246493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246494 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term181 A t u P t') = (term181 A t u P t').
Proof. exact (MK_COMB (@lem3246493) (@lem3246492 A t u P t')). Qed.
Lemma lem3246495 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term183 A t u P) = (term183 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246494 A t u P t')). Qed.
Lemma lem3246496 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246497 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term185 A t u P) = (term185 A t u P).
Proof. exact (MK_COMB (@lem3246496 A) (@lem3246495 A t u P)). Qed.
Lemma lem3246508 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term206 A t u P t' u') = (term206 A t u P t' u').
Proof. exact (eq_refl (term206 A t u P t' u')). Qed.
Lemma lem3246509 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term208 A t u P t') = (term208 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246508 A t u P t' u')). Qed.
Lemma lem3246510 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246511 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term210 A t u P t') = (term210 A t u P t').
Proof. exact (MK_COMB (@lem3246510 A) (@lem3246509 A t u P t')). Qed.
Lemma lem3246512 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term212 A t u P) = (term212 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246511 A t u P t')). Qed.
Lemma lem3246513 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246514 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term213 A t u P) = (term213 A t u P).
Proof. exact (MK_COMB (@lem3246513 A) (@lem3246512 A t u P)). Qed.
Lemma lem3246515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246516 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term214 A t u P) = (term214 A t u P).
Proof. exact (MK_COMB (@lem3246515) (@lem3246514 A t u P)). Qed.
Lemma lem3246517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246518 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term215 A t u P) = (term215 A t u P).
Proof. exact (MK_COMB (@lem3246517) (@lem3246516 A t u P)). Qed.
Lemma lem3246519 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term214 A t u P) = (term185 A t u P)) = ((term214 A t u P) = (term185 A t u P)).
Proof. exact (MK_COMB (@lem3246518 A t u P) (@lem3246497 A t u P)). Qed.
Lemma lem3246520 {A : Type'} (t : A -> Prop) (P : type686 A) : (term216 A t P) = (term216 A t P).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3246519 A t u P)). Qed.
Lemma lem3246521 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246522 {A : Type'} (t : A -> Prop) (P : type686 A) : (term217 A t P) = (term217 A t P).
Proof. exact (MK_COMB (@lem3246521 A) (@lem3246520 A t P)). Qed.
Lemma lem3246523 {A : Type'} (P : type686 A) : (term218 A P) = (term218 A P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3246522 A t P)). Qed.
Lemma lem3246524 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246525 {A : Type'} (P : type686 A) : (term219 A P) = (term219 A P).
Proof. exact (MK_COMB (@lem3246524 A) (@lem3246523 A P)). Qed.
Lemma lem3246526 {A : Type'} : (term227 A) = (term227 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3246525 A P)). Qed.
Lemma lem3246527 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3246528 {A : Type'} : (term229 A) = (term229 A).
Proof. exact (MK_COMB (@lem3246527 A) (@lem3246526 A)). Qed.
Lemma lem3246581 {A : Type'} : (term228 A) = (term229 A).
Proof. exact (TRANS (@lem3246478 A) (@lem3246528 A)). Qed.
Lemma lem3246582 {A : Type'} : (term229 A) = (term228 A).
Proof. exact (SYM (@lem3246581 A)). Qed.
Lemma lem3246584 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3246585 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term214 A t u P) = (term185 A t u P)) = (term230 A t u P).
Proof. exact (@lem3246584 ((term214 A t u P) = (term185 A t u P))). Qed.
Lemma lem3246586 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term230 A t u P) = ((term214 A t u P) = (term185 A t u P)).
Proof. exact (SYM (@lem3246585 A t u P)). Qed.
Lemma lem3246587 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term231 A t u P) : term231 A t u P.
Proof. exact (h1). Qed.
Lemma lem3246596 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term232 A t' t u' u) = (term233 A t' t u' u).
Proof. exact (@lem17045 (@SUBSET A t' t) (@SUBSET A u' u)). Qed.
Lemma lem3246600 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term203 A P t' u') = (term203 A P t' u').
Proof. exact (eq_refl (term203 A P t' u')). Qed.
Lemma lem3246603 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term234 A P t' u') = (term235 A P t' u').
Proof. exact (@lem16933 (term235 A P t' u')). Qed.
Lemma lem3246605 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term236 A t' t u' u) = (term236 A t' t u' u).
Proof. exact (eq_refl (term236 A t' t u' u)). Qed.
Lemma lem3246606 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term237 A t u P t' u') = (term238 A t u P t' u').
Proof. exact (MK_COMB (@lem3246605 A t' t u' u) (@lem3246603 A P t' u')). Qed.
Lemma lem3246607 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term239 A t u P t' u') = (term237 A t u P t' u').
Proof. exact (@lem17362 (term240 A t' t u' u) (term203 A P t' u')). Qed.
Lemma lem3246608 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term239 A t u P t' u') = (term238 A t u P t' u').
Proof. exact (TRANS (@lem3246607 A t u P t' u') (@lem3246606 A t u P t' u')). Qed.
Lemma lem3246609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3246610 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term241 A t' t u' u) = (term242 A t' t u' u).
Proof. exact (MK_COMB (@lem3246609) (@lem3246596 A t' t u' u)). Qed.
Lemma lem3246611 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term243 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (MK_COMB (@lem3246610 A t' t u' u) (@lem3246600 A P t' u')). Qed.
Lemma lem3246612 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term206 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (@lem17265 (term240 A t' t u' u) (term203 A P t' u')). Qed.
Lemma lem3246613 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term206 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (TRANS (@lem3246612 A t u P t' u') (@lem3246611 A t u P t' u')). Qed.
Lemma lem3246614 {A : Type'} (P : type686 A) : (term245 A P) = (term246 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3246615 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term247 A t u P t') = (term248 A t u P t').
Proof. exact (@lem3246614 A (term208 A t u P t')). Qed.
Lemma lem3246616 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term249 A t u P t' u') = (term206 A t u P t' u').
Proof. exact (eq_refl (term249 A t u P t' u')). Qed.
Lemma lem3246617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246618 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term250 A t u P t' u') = (term239 A t u P t' u').
Proof. exact (MK_COMB (@lem3246617) (@lem3246616 A t u P t' u')). Qed.
Lemma lem3246619 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term250 A t u P t' u') = (term238 A t u P t' u').
Proof. exact (TRANS (@lem3246618 A t u P t' u') (@lem3246608 A t u P t' u')). Qed.
Lemma lem3246620 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term251 A t u P t') = (term252 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246619 A t u P t' u')). Qed.
Lemma lem3246621 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246622 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term248 A t u P t') = (term253 A t u P t').
Proof. exact (MK_COMB (@lem3246621 A) (@lem3246620 A t u P t')). Qed.
Lemma lem3246623 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term247 A t u P t') = (term253 A t u P t').
Proof. exact (TRANS (@lem3246615 A t u P t') (@lem3246622 A t u P t')). Qed.
Lemma lem3246624 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term208 A t u P t') = (term254 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246613 A t u P t' u')). Qed.
Lemma lem3246625 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246626 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term210 A t u P t') = (term255 A t u P t').
Proof. exact (MK_COMB (@lem3246625 A) (@lem3246624 A t u P t')). Qed.
Lemma lem3246627 {A : Type'} (P : type686 A) : (term245 A P) = (term246 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3246628 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term214 A t u P) = (term256 A t u P).
Proof. exact (@lem3246627 A (term212 A t u P)). Qed.
Lemma lem3246629 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term257 A t u P t') = (term210 A t u P t').
Proof. exact (eq_refl (term257 A t u P t')). Qed.
Lemma lem3246630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246631 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term258 A t u P t') = (term247 A t u P t').
Proof. exact (MK_COMB (@lem3246630) (@lem3246629 A t u P t')). Qed.
Lemma lem3246632 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term258 A t u P t') = (term253 A t u P t').
Proof. exact (TRANS (@lem3246631 A t u P t') (@lem3246623 A t u P t')). Qed.
Lemma lem3246633 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term259 A t u P) = (term260 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246632 A t u P t')). Qed.
Lemma lem3246634 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246635 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term256 A t u P) = (term261 A t u P).
Proof. exact (MK_COMB (@lem3246634 A) (@lem3246633 A t u P)). Qed.
Lemma lem3246636 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term214 A t u P) = (term261 A t u P).
Proof. exact (TRANS (@lem3246628 A t u P) (@lem3246635 A t u P)). Qed.
Lemma lem3246637 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term212 A t u P) = (term262 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246626 A t u P t')). Qed.
Lemma lem3246638 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246639 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term213 A t u P) = (term263 A t u P).
Proof. exact (MK_COMB (@lem3246638 A) (@lem3246637 A t u P)). Qed.
Lemma lem3246640 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term264 A t u P) = (term213 A t u P).
Proof. exact (@lem16933 (term213 A t u P)). Qed.
Lemma lem3246641 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term264 A t u P) = (term263 A t u P).
Proof. exact (TRANS (@lem3246640 A t u P) (@lem3246639 A t u P)). Qed.
Lemma lem3246652 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term174 A u P t' u') = (term265 A u P t' u').
Proof. exact (@lem17045 (@SUBSET A u' u) (term235 A P t' u')). Qed.
Lemma lem3246657 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term266 A u P t' u') = (term163 A u P t' u').
Proof. exact (@lem16933 (term163 A u P t' u')). Qed.
Lemma lem3246659 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term161 A t' t) = (term161 A t' t).
Proof. exact (eq_refl (term161 A t' t)). Qed.
Lemma lem3246660 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term267 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (MK_COMB (@lem3246659 A t' t) (@lem3246657 A u P t' u')). Qed.
Lemma lem3246661 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term268 A t u P t' u') = (term267 A t u P t' u').
Proof. exact (@lem17362 (@SUBSET A t' t) (term174 A u P t' u')). Qed.
Lemma lem3246662 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term268 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (TRANS (@lem3246661 A t u P t' u') (@lem3246660 A t u P t' u')). Qed.
Lemma lem3246664 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term269 A t' t) = (term269 A t' t).
Proof. exact (eq_refl (term269 A t' t)). Qed.
Lemma lem3246665 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term270 A t u P t' u') = (term271 A t u P t' u').
Proof. exact (MK_COMB (@lem3246664 A t' t) (@lem3246652 A u P t' u')). Qed.
Lemma lem3246666 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term176 A t u P t' u') = (term270 A t u P t' u').
Proof. exact (@lem17265 (@SUBSET A t' t) (term174 A u P t' u')). Qed.
Lemma lem3246667 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term176 A t u P t' u') = (term271 A t u P t' u').
Proof. exact (TRANS (@lem3246666 A t u P t' u') (@lem3246665 A t u P t' u')). Qed.
Lemma lem3246668 {A : Type'} (P : type686 A) : (term245 A P) = (term246 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3246669 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term181 A t u P t') = (term272 A t u P t').
Proof. exact (@lem3246668 A (term178 A t u P t')). Qed.
Lemma lem3246670 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term273 A t u P t' u') = (term176 A t u P t' u').
Proof. exact (eq_refl (term273 A t u P t' u')). Qed.
Lemma lem3246671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246672 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term274 A t u P t' u') = (term268 A t u P t' u').
Proof. exact (MK_COMB (@lem3246671) (@lem3246670 A t u P t' u')). Qed.
Lemma lem3246673 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term274 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (TRANS (@lem3246672 A t u P t' u') (@lem3246662 A t u P t' u')). Qed.
Lemma lem3246674 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term275 A t u P t') = (term167 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246673 A t u P t' u')). Qed.
Lemma lem3246675 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246676 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term272 A t u P t') = (term168 A t u P t').
Proof. exact (MK_COMB (@lem3246675 A) (@lem3246674 A t u P t')). Qed.
Lemma lem3246677 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term181 A t u P t') = (term168 A t u P t').
Proof. exact (TRANS (@lem3246669 A t u P t') (@lem3246676 A t u P t')). Qed.
Lemma lem3246678 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term178 A t u P t') = (term276 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246667 A t u P t' u')). Qed.
Lemma lem3246679 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246680 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term180 A t u P t') = (term277 A t u P t').
Proof. exact (MK_COMB (@lem3246679 A) (@lem3246678 A t u P t')). Qed.
Lemma lem3246681 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term278 A t u P t') = (term180 A t u P t').
Proof. exact (@lem16933 (term180 A t u P t')). Qed.
Lemma lem3246682 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term278 A t u P t') = (term277 A t u P t').
Proof. exact (TRANS (@lem3246681 A t u P t') (@lem3246680 A t u P t')). Qed.
Lemma lem3246683 {A : Type'} (P : type686 A) : (term279 A P) = (term280 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3246684 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term281 A t u P) = (term282 A t u P).
Proof. exact (@lem3246683 A (term183 A t u P)). Qed.
Lemma lem3246685 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term283 A t u P t') = (term181 A t u P t').
Proof. exact (eq_refl (term283 A t u P t')). Qed.
Lemma lem3246686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3246687 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term284 A t u P t') = (term278 A t u P t').
Proof. exact (MK_COMB (@lem3246686) (@lem3246685 A t u P t')). Qed.
Lemma lem3246688 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term284 A t u P t') = (term277 A t u P t').
Proof. exact (TRANS (@lem3246687 A t u P t') (@lem3246682 A t u P t')). Qed.
Lemma lem3246689 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term285 A t u P) = (term286 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246688 A t u P t')). Qed.
Lemma lem3246690 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246691 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term282 A t u P) = (term287 A t u P).
Proof. exact (MK_COMB (@lem3246690 A) (@lem3246689 A t u P)). Qed.
Lemma lem3246692 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term281 A t u P) = (term287 A t u P).
Proof. exact (TRANS (@lem3246684 A t u P) (@lem3246691 A t u P)). Qed.
Lemma lem3246693 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term183 A t u P) = (term182 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246677 A t u P t')). Qed.
Lemma lem3246694 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246695 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term185 A t u P) = (term184 A t u P).
Proof. exact (MK_COMB (@lem3246694 A) (@lem3246693 A t u P)). Qed.
Lemma lem3246696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3246697 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term288 A t u P) = (term289 A t u P).
Proof. exact (MK_COMB (@lem3246696) (@lem3246641 A t u P)). Qed.
Lemma lem3246698 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term290 A t u P) = (term291 A t u P).
Proof. exact (MK_COMB (@lem3246697 A t u P) (@lem3246695 A t u P)). Qed.
Lemma lem3246699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3246700 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term292 A t u P) = (term293 A t u P).
Proof. exact (MK_COMB (@lem3246699) (@lem3246636 A t u P)). Qed.
Lemma lem3246701 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term294 A t u P) = (term295 A t u P).
Proof. exact (MK_COMB (@lem3246700 A t u P) (@lem3246692 A t u P)). Qed.
Lemma lem3246702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3246703 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term296 A t u P) = (term297 A t u P).
Proof. exact (MK_COMB (@lem3246702) (@lem3246701 A t u P)). Qed.
Lemma lem3246704 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term298 A t u P) = (term299 A t u P).
Proof. exact (MK_COMB (@lem3246703 A t u P) (@lem3246698 A t u P)). Qed.
Lemma lem3246705 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term231 A t u P) = (term298 A t u P).
Proof. exact (@lem17646 (term214 A t u P) (term185 A t u P)). Qed.
Lemma lem3246706 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term231 A t u P) = (term299 A t u P).
Proof. exact (TRANS (@lem3246705 A t u P) (@lem3246704 A t u P)). Qed.
Lemma lem3246764 {A : Type'} (P : Prop) (Q : A -> Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem3246765 {A : Type'} (P : Prop) (Q : type686 A) : (term302 A P Q) = (term303 A P Q).
Proof. exact (@lem3246764 (A -> Prop) P Q). Qed.
Lemma lem3246766 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term304 A t u P t') = (term305 A t u P t').
Proof. exact (@lem3246765 A (term306 A t' t) (term307 A u P t')). Qed.
Lemma lem3246767 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term308 A u P t' u') = (term265 A u P t' u').
Proof. exact (eq_refl (term308 A u P t' u')). Qed.
Lemma lem3246768 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term269 A t' t) = (term269 A t' t).
Proof. exact (eq_refl (term269 A t' t)). Qed.
Lemma lem3246769 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term309 A t u P t' u') = (term271 A t u P t' u').
Proof. exact (MK_COMB (@lem3246768 A t' t) (@lem3246767 A u P t' u')). Qed.
Lemma lem3246770 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term310 A t u P t') = (term276 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246769 A t u P t' u')). Qed.
Lemma lem3246771 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246772 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term304 A t u P t') = (term277 A t u P t').
Proof. exact (MK_COMB (@lem3246771 A) (@lem3246770 A t u P t')). Qed.
Lemma lem3246773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246774 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term311 A t u P t') = (term312 A t u P t').
Proof. exact (MK_COMB (@lem3246773) (@lem3246772 A t u P t')). Qed.
Lemma lem3246775 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term308 A u P t' u') = (term265 A u P t' u').
Proof. exact (eq_refl (term308 A u P t' u')). Qed.
Lemma lem3246776 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term313 A u P t') = (term307 A u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246775 A u P t' u')). Qed.
Lemma lem3246777 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246778 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term314 A u P t') = (term315 A u P t').
Proof. exact (MK_COMB (@lem3246777 A) (@lem3246776 A u P t')). Qed.
Lemma lem3246779 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term269 A t' t) = (term269 A t' t).
Proof. exact (eq_refl (term269 A t' t)). Qed.
Lemma lem3246780 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term305 A t u P t') = (term316 A t u P t').
Proof. exact (MK_COMB (@lem3246779 A t' t) (@lem3246778 A u P t')). Qed.
Lemma lem3246781 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term304 A t u P t') = (term305 A t u P t')) = ((term277 A t u P t') = (term316 A t u P t')).
Proof. exact (MK_COMB (@lem3246774 A t u P t') (@lem3246780 A t u P t')). Qed.
Lemma lem3246782 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term277 A t u P t') = (term316 A t u P t').
Proof. exact (EQ_MP (@lem3246781 A t u P t') (@lem3246766 A t u P t')). Qed.
Lemma lem3246831 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term286 A t u P) = (term317 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246782 A t u P t')). Qed.
Lemma lem3246832 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3246833 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term287 A t u P) = (term318 A t u P).
Proof. exact (MK_COMB (@lem3246832 A) (@lem3246831 A t u P)). Qed.
Lemma lem3246882 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term293 A t u P) = (term293 A t u P).
Proof. exact (eq_refl (term293 A t u P)). Qed.
Lemma lem3246883 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term295 A t u P) = (term319 A t u P).
Proof. exact (MK_COMB (@lem3246882 A t u P) (@lem3246833 A t u P)). Qed.
Lemma lem3246884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3246885 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term297 A t u P) = (term320 A t u P).
Proof. exact (MK_COMB (@lem3246884) (@lem3246883 A t u P)). Qed.
Lemma lem3246943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem3246944 {A : Type'} (P : Prop) (Q : type686 A) : (term321 A P Q) = (term322 A P Q).
Proof. exact (@lem3246943 (A -> Prop) P Q). Qed.
Lemma lem3246945 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term323 A t u P t') = (term324 A t u P t').
Proof. exact (@lem3246944 A (@SUBSET A t' t) (term158 A u P t')). Qed.
Lemma lem3246946 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term162 A u P t' u') = (term163 A u P t' u').
Proof. exact (eq_refl (term162 A u P t' u')). Qed.
Lemma lem3246947 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term161 A t' t) = (term161 A t' t).
Proof. exact (eq_refl (term161 A t' t)). Qed.
Lemma lem3246948 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term325 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (MK_COMB (@lem3246947 A t' t) (@lem3246946 A u P t' u')). Qed.
Lemma lem3246949 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term326 A t u P t') = (term167 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246948 A t u P t' u')). Qed.
Lemma lem3246950 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246951 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term323 A t u P t') = (term168 A t u P t').
Proof. exact (MK_COMB (@lem3246950 A) (@lem3246949 A t u P t')). Qed.
Lemma lem3246952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3246953 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term327 A t u P t') = (term170 A t u P t').
Proof. exact (MK_COMB (@lem3246952) (@lem3246951 A t u P t')). Qed.
Lemma lem3246954 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term162 A u P t' u') = (term163 A u P t' u').
Proof. exact (eq_refl (term162 A u P t' u')). Qed.
Lemma lem3246955 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term328 A u P t') = (term158 A u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3246954 A u P t' u')). Qed.
Lemma lem3246956 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3246957 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term329 A u P t') = (term330 A u P t').
Proof. exact (MK_COMB (@lem3246956 A) (@lem3246955 A u P t')). Qed.
Lemma lem3246958 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term161 A t' t) = (term161 A t' t).
Proof. exact (eq_refl (term161 A t' t)). Qed.
Lemma lem3246959 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term324 A t u P t') = (term331 A t u P t').
Proof. exact (MK_COMB (@lem3246958 A t' t) (@lem3246957 A u P t')). Qed.
Lemma lem3246960 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term323 A t u P t') = (term324 A t u P t')) = ((term168 A t u P t') = (term331 A t u P t')).
Proof. exact (MK_COMB (@lem3246953 A t u P t') (@lem3246959 A t u P t')). Qed.
Lemma lem3246961 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term168 A t u P t') = (term331 A t u P t').
Proof. exact (EQ_MP (@lem3246960 A t u P t') (@lem3246945 A t u P t')). Qed.
Lemma lem3247010 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term182 A t u P) = (term332 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3246961 A t u P t')). Qed.
Lemma lem3247011 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247012 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term184 A t u P) = (term333 A t u P).
Proof. exact (MK_COMB (@lem3247011 A) (@lem3247010 A t u P)). Qed.
Lemma lem3247061 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (eq_refl (term289 A t u P)). Qed.
Lemma lem3247062 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term291 A t u P) = (term334 A t u P).
Proof. exact (MK_COMB (@lem3247061 A t u P) (@lem3247012 A t u P)). Qed.
Lemma lem3247063 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term299 A t u P) = (term335 A t u P).
Proof. exact (MK_COMB (@lem3246885 A t u P) (@lem3247062 A t u P)). Qed.
Lemma lem3247065 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3247066 {A : Type'} (P : type686 A) (Q : Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (@lem3247065 (A -> Prop) P Q). Qed.
Lemma lem3247067 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term338 A t u P) = (term339 A t u P).
Proof. exact (@lem3247066 A (term260 A t u P) (term318 A t u P)). Qed.
Lemma lem3247068 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term340 A t u P t') = (term253 A t u P t').
Proof. exact (eq_refl (term340 A t u P t')). Qed.
Lemma lem3247069 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term341 A t u P) = (term260 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247068 A t u P t')). Qed.
Lemma lem3247070 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247071 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term342 A t u P) = (term261 A t u P).
Proof. exact (MK_COMB (@lem3247070 A) (@lem3247069 A t u P)). Qed.
Lemma lem3247072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3247073 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term343 A t u P) = (term293 A t u P).
Proof. exact (MK_COMB (@lem3247072) (@lem3247071 A t u P)). Qed.
Lemma lem3247074 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term318 A t u P).
Proof. exact (eq_refl (term318 A t u P)). Qed.
Lemma lem3247075 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term338 A t u P) = (term319 A t u P).
Proof. exact (MK_COMB (@lem3247073 A t u P) (@lem3247074 A t u P)). Qed.
Lemma lem3247076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247077 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term344 A t u P) = (term345 A t u P).
Proof. exact (MK_COMB (@lem3247076) (@lem3247075 A t u P)). Qed.
Lemma lem3247078 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term340 A t u P t') = (term253 A t u P t').
Proof. exact (eq_refl (term340 A t u P t')). Qed.
Lemma lem3247079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3247080 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term346 A t u P t') = (term347 A t u P t').
Proof. exact (MK_COMB (@lem3247079) (@lem3247078 A t u P t')). Qed.
Lemma lem3247081 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term318 A t u P).
Proof. exact (eq_refl (term318 A t u P)). Qed.
Lemma lem3247082 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term348 A t' t u P) = (term349 A t' t u P).
Proof. exact (MK_COMB (@lem3247080 A t u P t') (@lem3247081 A t u P)). Qed.
Lemma lem3247083 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term350 A t u P) = (term351 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247082 A t' t u P)). Qed.
Lemma lem3247084 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247085 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term339 A t u P) = (term352 A t u P).
Proof. exact (MK_COMB (@lem3247084 A) (@lem3247083 A t u P)). Qed.
Lemma lem3247086 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term338 A t u P) = (term339 A t u P)) = ((term319 A t u P) = (term352 A t u P)).
Proof. exact (MK_COMB (@lem3247077 A t u P) (@lem3247085 A t u P)). Qed.
Lemma lem3247087 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term319 A t u P) = (term352 A t u P).
Proof. exact (EQ_MP (@lem3247086 A t u P) (@lem3247067 A t u P)). Qed.
Lemma lem3247089 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3247090 {A : Type'} (P : type686 A) (Q : Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (@lem3247089 (A -> Prop) P Q). Qed.
Lemma lem3247091 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term353 A t' t u P) = (term354 A t' t u P).
Proof. exact (@lem3247090 A (term252 A t u P t') (term318 A t u P)). Qed.
Lemma lem3247092 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term355 A t u P t' u') = (term238 A t u P t' u').
Proof. exact (eq_refl (term355 A t u P t' u')). Qed.
Lemma lem3247093 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term356 A t u P t') = (term252 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247092 A t u P t' u')). Qed.
Lemma lem3247094 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247095 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term357 A t u P t') = (term253 A t u P t').
Proof. exact (MK_COMB (@lem3247094 A) (@lem3247093 A t u P t')). Qed.
Lemma lem3247096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3247097 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term358 A t u P t') = (term347 A t u P t').
Proof. exact (MK_COMB (@lem3247096) (@lem3247095 A t u P t')). Qed.
Lemma lem3247098 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term318 A t u P).
Proof. exact (eq_refl (term318 A t u P)). Qed.
Lemma lem3247099 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term353 A t' t u P) = (term349 A t' t u P).
Proof. exact (MK_COMB (@lem3247097 A t u P t') (@lem3247098 A t u P)). Qed.
Lemma lem3247100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247101 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term359 A t' t u P) = (term360 A t' t u P).
Proof. exact (MK_COMB (@lem3247100) (@lem3247099 A t' t u P)). Qed.
Lemma lem3247102 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term355 A t u P t' u') = (term238 A t u P t' u').
Proof. exact (eq_refl (term355 A t u P t' u')). Qed.
Lemma lem3247103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3247104 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term361 A t u P t' u') = (term362 A t u P t' u').
Proof. exact (MK_COMB (@lem3247103) (@lem3247102 A t u P t' u')). Qed.
Lemma lem3247105 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term318 A t u P).
Proof. exact (eq_refl (term318 A t u P)). Qed.
Lemma lem3247106 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term363 A t' u' t u P) = (term364 A t' u' t u P).
Proof. exact (MK_COMB (@lem3247104 A t u P t' u') (@lem3247105 A t u P)). Qed.
Lemma lem3247107 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term365 A t' t u P) = (term366 A t' t u P).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247106 A t' u' t u P)). Qed.
Lemma lem3247108 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247109 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term354 A t' t u P) = (term367 A t' t u P).
Proof. exact (MK_COMB (@lem3247108 A) (@lem3247107 A t' t u P)). Qed.
Lemma lem3247110 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term353 A t' t u P) = (term354 A t' t u P)) = ((term349 A t' t u P) = (term367 A t' t u P)).
Proof. exact (MK_COMB (@lem3247101 A t' t u P) (@lem3247109 A t' t u P)). Qed.
Lemma lem3247111 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term349 A t' t u P) = (term367 A t' t u P).
Proof. exact (EQ_MP (@lem3247110 A t' t u P) (@lem3247091 A t' t u P)). Qed.
Lemma lem3247112 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term351 A t u P) = (term368 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247111 A t' t u P)). Qed.
Lemma lem3247113 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247114 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term352 A t u P) = (term369 A t u P).
Proof. exact (MK_COMB (@lem3247113 A) (@lem3247112 A t u P)). Qed.
Lemma lem3247115 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term319 A t u P) = (term369 A t u P).
Proof. exact (TRANS (@lem3247087 A t u P) (@lem3247114 A t u P)). Qed.
Lemma lem3247116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247117 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term320 A t u P) = (term370 A t u P).
Proof. exact (MK_COMB (@lem3247116) (@lem3247115 A t u P)). Qed.
Lemma lem3247119 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3247120 {A : Type'} (P : Prop) (Q : type686 A) : (term322 A P Q) = (term321 A P Q).
Proof. exact (@lem3247119 (A -> Prop) P Q). Qed.
Lemma lem3247121 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term324 A t u P t') = (term323 A t u P t').
Proof. exact (@lem3247120 A (@SUBSET A t' t) (term158 A u P t')). Qed.
Lemma lem3247122 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term162 A u P t' u') = (term163 A u P t' u').
Proof. exact (eq_refl (term162 A u P t' u')). Qed.
Lemma lem3247123 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term328 A u P t') = (term158 A u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247122 A u P t' u')). Qed.
Lemma lem3247124 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247125 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term329 A u P t') = (term330 A u P t').
Proof. exact (MK_COMB (@lem3247124 A) (@lem3247123 A u P t')). Qed.
Lemma lem3247126 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term161 A t' t) = (term161 A t' t).
Proof. exact (eq_refl (term161 A t' t)). Qed.
Lemma lem3247127 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term324 A t u P t') = (term331 A t u P t').
Proof. exact (MK_COMB (@lem3247126 A t' t) (@lem3247125 A u P t')). Qed.
Lemma lem3247128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247129 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term371 A t u P t') = (term372 A t u P t').
Proof. exact (MK_COMB (@lem3247128) (@lem3247127 A t u P t')). Qed.
Lemma lem3247130 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term162 A u P t' u') = (term163 A u P t' u').
Proof. exact (eq_refl (term162 A u P t' u')). Qed.
Lemma lem3247131 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term161 A t' t) = (term161 A t' t).
Proof. exact (eq_refl (term161 A t' t)). Qed.
Lemma lem3247132 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term325 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (MK_COMB (@lem3247131 A t' t) (@lem3247130 A u P t' u')). Qed.
Lemma lem3247133 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term326 A t u P t') = (term167 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247132 A t u P t' u')). Qed.
Lemma lem3247134 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247135 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term323 A t u P t') = (term168 A t u P t').
Proof. exact (MK_COMB (@lem3247134 A) (@lem3247133 A t u P t')). Qed.
Lemma lem3247136 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term324 A t u P t') = (term323 A t u P t')) = ((term331 A t u P t') = (term168 A t u P t')).
Proof. exact (MK_COMB (@lem3247129 A t u P t') (@lem3247135 A t u P t')). Qed.
Lemma lem3247137 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term331 A t u P t') = (term168 A t u P t').
Proof. exact (EQ_MP (@lem3247136 A t u P t') (@lem3247121 A t u P t')). Qed.
Lemma lem3247138 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term332 A t u P) = (term182 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247137 A t u P t')). Qed.
Lemma lem3247139 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247140 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term333 A t u P) = (term184 A t u P).
Proof. exact (MK_COMB (@lem3247139 A) (@lem3247138 A t u P)). Qed.
Lemma lem3247141 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (eq_refl (term289 A t u P)). Qed.
Lemma lem3247142 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term334 A t u P) = (term291 A t u P).
Proof. exact (MK_COMB (@lem3247141 A t u P) (@lem3247140 A t u P)). Qed.
Lemma lem3247144 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3247145 {A : Type'} (P : Prop) (Q : type686 A) : (term322 A P Q) = (term321 A P Q).
Proof. exact (@lem3247144 (A -> Prop) P Q). Qed.
Lemma lem3247146 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term373 A t u P) = (term374 A t u P).
Proof. exact (@lem3247145 A (term263 A t u P) (term182 A t u P)). Qed.
Lemma lem3247147 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term375 A t u P t') = (term168 A t u P t').
Proof. exact (eq_refl (term375 A t u P t')). Qed.
Lemma lem3247148 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term376 A t u P) = (term182 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247147 A t u P t')). Qed.
Lemma lem3247149 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247150 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term377 A t u P) = (term184 A t u P).
Proof. exact (MK_COMB (@lem3247149 A) (@lem3247148 A t u P)). Qed.
Lemma lem3247151 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (eq_refl (term289 A t u P)). Qed.
Lemma lem3247152 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term373 A t u P) = (term291 A t u P).
Proof. exact (MK_COMB (@lem3247151 A t u P) (@lem3247150 A t u P)). Qed.
Lemma lem3247153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247154 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term378 A t u P) = (term379 A t u P).
Proof. exact (MK_COMB (@lem3247153) (@lem3247152 A t u P)). Qed.
Lemma lem3247155 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term375 A t u P t') = (term168 A t u P t').
Proof. exact (eq_refl (term375 A t u P t')). Qed.
Lemma lem3247156 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (eq_refl (term289 A t u P)). Qed.
Lemma lem3247157 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term380 A t u P t') = (term381 A t u P t').
Proof. exact (MK_COMB (@lem3247156 A t u P) (@lem3247155 A t u P t')). Qed.
Lemma lem3247158 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term382 A t u P) = (term383 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247157 A t u P t')). Qed.
Lemma lem3247159 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247160 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term374 A t u P) = (term384 A t u P).
Proof. exact (MK_COMB (@lem3247159 A) (@lem3247158 A t u P)). Qed.
Lemma lem3247161 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term373 A t u P) = (term374 A t u P)) = ((term291 A t u P) = (term384 A t u P)).
Proof. exact (MK_COMB (@lem3247154 A t u P) (@lem3247160 A t u P)). Qed.
Lemma lem3247162 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term291 A t u P) = (term384 A t u P).
Proof. exact (EQ_MP (@lem3247161 A t u P) (@lem3247146 A t u P)). Qed.
Lemma lem3247164 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3247165 {A : Type'} (P : Prop) (Q : type686 A) : (term322 A P Q) = (term321 A P Q).
Proof. exact (@lem3247164 (A -> Prop) P Q). Qed.
Lemma lem3247166 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term385 A t u P t') = (term386 A t u P t').
Proof. exact (@lem3247165 A (term263 A t u P) (term167 A t u P t')). Qed.
Lemma lem3247167 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term387 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (eq_refl (term387 A t u P t' u')). Qed.
Lemma lem3247168 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term388 A t u P t') = (term167 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247167 A t u P t' u')). Qed.
Lemma lem3247169 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247170 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term389 A t u P t') = (term168 A t u P t').
Proof. exact (MK_COMB (@lem3247169 A) (@lem3247168 A t u P t')). Qed.
Lemma lem3247171 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (eq_refl (term289 A t u P)). Qed.
Lemma lem3247172 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term385 A t u P t') = (term381 A t u P t').
Proof. exact (MK_COMB (@lem3247171 A t u P) (@lem3247170 A t u P t')). Qed.
Lemma lem3247173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247174 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term390 A t u P t') = (term391 A t u P t').
Proof. exact (MK_COMB (@lem3247173) (@lem3247172 A t u P t')). Qed.
Lemma lem3247175 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term387 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (eq_refl (term387 A t u P t' u')). Qed.
Lemma lem3247176 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (eq_refl (term289 A t u P)). Qed.
Lemma lem3247177 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term392 A t u P t' u') = (term393 A t u P t' u').
Proof. exact (MK_COMB (@lem3247176 A t u P) (@lem3247175 A t u P t' u')). Qed.
Lemma lem3247178 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term394 A t u P t') = (term395 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247177 A t u P t' u')). Qed.
Lemma lem3247179 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247180 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term386 A t u P t') = (term396 A t u P t').
Proof. exact (MK_COMB (@lem3247179 A) (@lem3247178 A t u P t')). Qed.
Lemma lem3247181 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term385 A t u P t') = (term386 A t u P t')) = ((term381 A t u P t') = (term396 A t u P t')).
Proof. exact (MK_COMB (@lem3247174 A t u P t') (@lem3247180 A t u P t')). Qed.
Lemma lem3247182 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term381 A t u P t') = (term396 A t u P t').
Proof. exact (EQ_MP (@lem3247181 A t u P t') (@lem3247166 A t u P t')). Qed.
Lemma lem3247183 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term383 A t u P) = (term397 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247182 A t u P t')). Qed.
Lemma lem3247184 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247185 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term384 A t u P) = (term398 A t u P).
Proof. exact (MK_COMB (@lem3247184 A) (@lem3247183 A t u P)). Qed.
Lemma lem3247186 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term291 A t u P) = (term398 A t u P).
Proof. exact (TRANS (@lem3247162 A t u P) (@lem3247185 A t u P)). Qed.
Lemma lem3247187 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term334 A t u P) = (term398 A t u P).
Proof. exact (TRANS (@lem3247142 A t u P) (@lem3247186 A t u P)). Qed.
Lemma lem3247188 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term335 A t u P) = (term399 A t u P).
Proof. exact (MK_COMB (@lem3247117 A t u P) (@lem3247187 A t u P)). Qed.
Lemma lem3247190 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3247191 {A : Type'} (P : type686 A) (Q : type686 A) : (term400 A P Q) = (term401 A P Q).
Proof. exact (@lem3247190 (A -> Prop) P Q). Qed.
Lemma lem3247192 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term402 A t u P) = (term403 A t u P).
Proof. exact (@lem3247191 A (term368 A t u P) (term397 A t u P)). Qed.
Lemma lem3247193 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term404 A t u P t') = (term367 A t' t u P).
Proof. exact (eq_refl (term404 A t u P t')). Qed.
Lemma lem3247194 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term405 A t u P) = (term368 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247193 A t' t u P)). Qed.
Lemma lem3247195 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247196 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term406 A t u P) = (term369 A t u P).
Proof. exact (MK_COMB (@lem3247195 A) (@lem3247194 A t u P)). Qed.
Lemma lem3247197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247198 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term407 A t u P) = (term370 A t u P).
Proof. exact (MK_COMB (@lem3247197) (@lem3247196 A t u P)). Qed.
Lemma lem3247199 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term408 A t u P t') = (term396 A t u P t').
Proof. exact (eq_refl (term408 A t u P t')). Qed.
Lemma lem3247200 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term409 A t u P) = (term397 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247199 A t u P t')). Qed.
Lemma lem3247201 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247202 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term410 A t u P) = (term398 A t u P).
Proof. exact (MK_COMB (@lem3247201 A) (@lem3247200 A t u P)). Qed.
Lemma lem3247203 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term402 A t u P) = (term399 A t u P).
Proof. exact (MK_COMB (@lem3247198 A t u P) (@lem3247202 A t u P)). Qed.
Lemma lem3247204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247205 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term411 A t u P) = (term412 A t u P).
Proof. exact (MK_COMB (@lem3247204) (@lem3247203 A t u P)). Qed.
Lemma lem3247206 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term404 A t u P t') = (term367 A t' t u P).
Proof. exact (eq_refl (term404 A t u P t')). Qed.
Lemma lem3247207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247208 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term413 A t u P t') = (term414 A t' t u P).
Proof. exact (MK_COMB (@lem3247207) (@lem3247206 A t' t u P)). Qed.
Lemma lem3247209 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term408 A t u P t') = (term396 A t u P t').
Proof. exact (eq_refl (term408 A t u P t')). Qed.
Lemma lem3247210 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term415 A t u P t') = (term416 A t u P t').
Proof. exact (MK_COMB (@lem3247208 A t' t u P) (@lem3247209 A t u P t')). Qed.
Lemma lem3247211 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term417 A t u P) = (term418 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247210 A t u P t')). Qed.
Lemma lem3247212 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247213 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term403 A t u P) = (term419 A t u P).
Proof. exact (MK_COMB (@lem3247212 A) (@lem3247211 A t u P)). Qed.
Lemma lem3247214 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term402 A t u P) = (term403 A t u P)) = ((term399 A t u P) = (term419 A t u P)).
Proof. exact (MK_COMB (@lem3247205 A t u P) (@lem3247213 A t u P)). Qed.
Lemma lem3247215 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term399 A t u P) = (term419 A t u P).
Proof. exact (EQ_MP (@lem3247214 A t u P) (@lem3247192 A t u P)). Qed.
Lemma lem3247217 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3247218 {A : Type'} (P : type686 A) (Q : type686 A) : (term400 A P Q) = (term401 A P Q).
Proof. exact (@lem3247217 (A -> Prop) P Q). Qed.
Lemma lem3247219 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term420 A t u P t') = (term421 A t u P t').
Proof. exact (@lem3247218 A (term366 A t' t u P) (term395 A t u P t')). Qed.
Lemma lem3247220 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term422 A t' t u P u') = (term364 A t' u' t u P).
Proof. exact (eq_refl (term422 A t' t u P u')). Qed.
Lemma lem3247221 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term423 A t' t u P) = (term366 A t' t u P).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247220 A t' u' t u P)). Qed.
Lemma lem3247222 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247223 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term424 A t' t u P) = (term367 A t' t u P).
Proof. exact (MK_COMB (@lem3247222 A) (@lem3247221 A t' t u P)). Qed.
Lemma lem3247224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247225 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term425 A t' t u P) = (term414 A t' t u P).
Proof. exact (MK_COMB (@lem3247224) (@lem3247223 A t' t u P)). Qed.
Lemma lem3247226 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term426 A t u P t' u') = (term393 A t u P t' u').
Proof. exact (eq_refl (term426 A t u P t' u')). Qed.
Lemma lem3247227 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term427 A t u P t') = (term395 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247226 A t u P t' u')). Qed.
Lemma lem3247228 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247229 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term428 A t u P t') = (term396 A t u P t').
Proof. exact (MK_COMB (@lem3247228 A) (@lem3247227 A t u P t')). Qed.
Lemma lem3247230 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term420 A t u P t') = (term416 A t u P t').
Proof. exact (MK_COMB (@lem3247225 A t' t u P) (@lem3247229 A t u P t')). Qed.
Lemma lem3247231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247232 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term429 A t u P t') = (term430 A t u P t').
Proof. exact (MK_COMB (@lem3247231) (@lem3247230 A t u P t')). Qed.
Lemma lem3247233 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term422 A t' t u P u') = (term364 A t' u' t u P).
Proof. exact (eq_refl (term422 A t' t u P u')). Qed.
Lemma lem3247234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247235 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term431 A t' t u P u') = (term432 A t' u' t u P).
Proof. exact (MK_COMB (@lem3247234) (@lem3247233 A t' u' t u P)). Qed.
Lemma lem3247236 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term426 A t u P t' u') = (term393 A t u P t' u').
Proof. exact (eq_refl (term426 A t u P t' u')). Qed.
Lemma lem3247237 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term433 A t u P t' u') = (term434 A t u P t' u').
Proof. exact (MK_COMB (@lem3247235 A t' u' t u P) (@lem3247236 A t u P t' u')). Qed.
Lemma lem3247238 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term435 A t u P t') = (term436 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247237 A t u P t' u')). Qed.
Lemma lem3247239 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247240 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term421 A t u P t') = (term437 A t u P t').
Proof. exact (MK_COMB (@lem3247239 A) (@lem3247238 A t u P t')). Qed.
Lemma lem3247241 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term420 A t u P t') = (term421 A t u P t')) = ((term416 A t u P t') = (term437 A t u P t')).
Proof. exact (MK_COMB (@lem3247232 A t u P t') (@lem3247240 A t u P t')). Qed.
Lemma lem3247242 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term416 A t u P t') = (term437 A t u P t').
Proof. exact (EQ_MP (@lem3247241 A t u P t') (@lem3247219 A t u P t')). Qed.
Lemma lem3247243 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term418 A t u P) = (term438 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247242 A t u P t')). Qed.
Lemma lem3247244 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3247245 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term419 A t u P) = (term439 A t u P).
Proof. exact (MK_COMB (@lem3247244 A) (@lem3247243 A t u P)). Qed.
Lemma lem3247246 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term399 A t u P) = (term439 A t u P).
Proof. exact (TRANS (@lem3247215 A t u P) (@lem3247245 A t u P)). Qed.
Lemma lem3247247 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term335 A t u P) = (term439 A t u P).
Proof. exact (TRANS (@lem3247188 A t u P) (@lem3247246 A t u P)). Qed.
Lemma lem3247248 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term299 A t u P) = (term439 A t u P).
Proof. exact (TRANS (@lem3247063 A t u P) (@lem3247247 A t u P)). Qed.
Lemma lem3247249 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term231 A t u P) = (term439 A t u P).
Proof. exact (TRANS (@lem3246706 A t u P) (@lem3247248 A t u P)). Qed.
Lemma lem3247250 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term231 A t u P) : term439 A t u P.
Proof. exact (EQ_MP (@lem3247249 A t u P) (@lem3246587 A t u P h1)). Qed.
Lemma lem3247251 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (h1 : term437 A t u P t') : term437 A t u P t'.
Proof. exact (h1). Qed.
Lemma lem3247252 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term434 A t u P t' u') : term434 A t u P t' u'.
Proof. exact (h1). Qed.
Lemma lem3247275 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term165 A t u P t' u') = (term165 A t u P t' u').
Proof. exact (eq_refl (term165 A t u P t' u')). Qed.
Lemma lem3247304 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term244 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (eq_refl (term244 A t u P t' u')). Qed.
Lemma lem3247305 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term254 A t u P t') = (term254 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247304 A t u P t' u')). Qed.
Lemma lem3247306 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247307 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term255 A t u P t') = (term255 A t u P t').
Proof. exact (MK_COMB (@lem3247306 A) (@lem3247305 A t u P t')). Qed.
Lemma lem3247308 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term262 A t u P) = (term262 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247307 A t u P t')). Qed.
Lemma lem3247309 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247310 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term263 A t u P) = (term263 A t u P).
Proof. exact (MK_COMB (@lem3247309 A) (@lem3247308 A t u P)). Qed.
Lemma lem3247311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3247312 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term289 A t u P) = (term289 A t u P).
Proof. exact (MK_COMB (@lem3247311) (@lem3247310 A t u P)). Qed.
Lemma lem3247313 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term393 A t u P t' u') = (term393 A t u P t' u').
Proof. exact (MK_COMB (@lem3247312 A t u P) (@lem3247275 A t u P t' u')). Qed.
Lemma lem3247332 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term265 A u P t' u') = (term265 A u P t' u').
Proof. exact (eq_refl (term265 A u P t' u')). Qed.
Lemma lem3247333 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term307 A u P t') = (term307 A u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247332 A u P t' u')). Qed.
Lemma lem3247334 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247335 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term315 A u P t') = (term315 A u P t').
Proof. exact (MK_COMB (@lem3247334 A) (@lem3247333 A u P t')). Qed.
Lemma lem3247344 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term269 A t' t) = (term269 A t' t).
Proof. exact (eq_refl (term269 A t' t)). Qed.
Lemma lem3247345 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term316 A t u P t') = (term316 A t u P t').
Proof. exact (MK_COMB (@lem3247344 A t' t) (@lem3247335 A u P t')). Qed.
Lemma lem3247346 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term317 A t u P) = (term317 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247345 A t u P t')). Qed.
Lemma lem3247347 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247348 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term318 A t u P).
Proof. exact (MK_COMB (@lem3247347 A) (@lem3247346 A t u P)). Qed.
Lemma lem3247373 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term362 A t u P t' u') = (term362 A t u P t' u').
Proof. exact (eq_refl (term362 A t u P t' u')). Qed.
Lemma lem3247374 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term364 A t' u' t u P) = (term364 A t' u' t u P).
Proof. exact (MK_COMB (@lem3247373 A t u P t' u') (@lem3247348 A t u P)). Qed.
Lemma lem3247375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247376 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term432 A t' u' t u P) = (term432 A t' u' t u P).
Proof. exact (MK_COMB (@lem3247375) (@lem3247374 A t' u' t u P)). Qed.
Lemma lem3247377 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term434 A t u P t' u') = (term434 A t u P t' u').
Proof. exact (MK_COMB (@lem3247376 A t' u' t u P) (@lem3247313 A t u P t' u')). Qed.
Lemma lem3247378 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term434 A t u P t' u') : term434 A t u P t' u'.
Proof. exact (EQ_MP (@lem3247377 A t u P t' u') (@lem3247252 A t u P t' u' h1)). Qed.
Lemma lem3247379 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term364 A t' u' t u P.
Proof. exact (h1). Qed.
Lemma lem3247380 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term393 A t u P t' u'.
Proof. exact (h1). Qed.
Lemma lem3247381 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term318 A t u P.
Proof. exact (proj2 (@lem3247379 A t' u' t u P h1)). Qed.
Lemma lem3247382 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term238 A t u P t' u'.
Proof. exact (proj1 (@lem3247379 A t' u' t u P h1)). Qed.
Lemma lem3247384 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term240 A t' t u' u.
Proof. exact (proj1 (@lem3247382 A t' u' t u P h1)). Qed.
Lemma lem3247387 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term165 A t u P t' u'.
Proof. exact (proj2 (@lem3247380 A t u P t' u' h1)). Qed.
Lemma lem3247388 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term263 A t u P.
Proof. exact (proj1 (@lem3247380 A t u P t' u' h1)). Qed.
Lemma lem3247389 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term163 A u P t' u'.
Proof. exact (proj2 (@lem3247387 A t u P t' u' h1)). Qed.
Lemma lem3247394 {A : Type'} (P : Prop) (Q : A -> Prop) : (term301 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3247395 {A : Type'} (P : Prop) (Q : type686 A) : (term303 A P Q) = (term302 A P Q).
Proof. exact (@lem3247394 (A -> Prop) P Q). Qed.
Lemma lem3247396 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term305 A t u P t') = (term304 A t u P t').
Proof. exact (@lem3247395 A (term306 A t' t) (term307 A u P t')). Qed.
Lemma lem3247397 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term308 A u P t' u') = (term265 A u P t' u').
Proof. exact (eq_refl (term308 A u P t' u')). Qed.
Lemma lem3247398 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term313 A u P t') = (term307 A u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247397 A u P t' u')). Qed.
Lemma lem3247399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247400 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term314 A u P t') = (term315 A u P t').
Proof. exact (MK_COMB (@lem3247399 A) (@lem3247398 A u P t')). Qed.
Lemma lem3247401 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term269 A t' t) = (term269 A t' t).
Proof. exact (eq_refl (term269 A t' t)). Qed.
Lemma lem3247402 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term305 A t u P t') = (term316 A t u P t').
Proof. exact (MK_COMB (@lem3247401 A t' t) (@lem3247400 A u P t')). Qed.
Lemma lem3247403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247404 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term440 A t u P t') = (term441 A t u P t').
Proof. exact (MK_COMB (@lem3247403) (@lem3247402 A t u P t')). Qed.
Lemma lem3247405 {A : Type'} (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term308 A u P t' u') = (term265 A u P t' u').
Proof. exact (eq_refl (term308 A u P t' u')). Qed.
Lemma lem3247406 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term269 A t' t) = (term269 A t' t).
Proof. exact (eq_refl (term269 A t' t)). Qed.
Lemma lem3247407 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term309 A t u P t' u') = (term271 A t u P t' u').
Proof. exact (MK_COMB (@lem3247406 A t' t) (@lem3247405 A u P t' u')). Qed.
Lemma lem3247408 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term310 A t u P t') = (term276 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247407 A t u P t' u')). Qed.
Lemma lem3247409 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247410 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term304 A t u P t') = (term277 A t u P t').
Proof. exact (MK_COMB (@lem3247409 A) (@lem3247408 A t u P t')). Qed.
Lemma lem3247411 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term305 A t u P t') = (term304 A t u P t')) = ((term316 A t u P t') = (term277 A t u P t')).
Proof. exact (MK_COMB (@lem3247404 A t u P t') (@lem3247410 A t u P t')). Qed.
Lemma lem3247412 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term316 A t u P t') = (term277 A t u P t').
Proof. exact (EQ_MP (@lem3247411 A t u P t') (@lem3247396 A t u P t')). Qed.
Lemma lem3247413 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term317 A t u P) = (term286 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247412 A t u P t')). Qed.
Lemma lem3247414 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247415 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term287 A t u P).
Proof. exact (MK_COMB (@lem3247414 A) (@lem3247413 A t u P)). Qed.
Lemma lem3247428 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term271 A t u P t' u') = (term271 A t u P t' u').
Proof. exact (eq_refl (term271 A t u P t' u')). Qed.
Lemma lem3247429 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term276 A t u P t') = (term276 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247428 A t u P t' u')). Qed.
Lemma lem3247430 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247431 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term277 A t u P t') = (term277 A t u P t').
Proof. exact (MK_COMB (@lem3247430 A) (@lem3247429 A t u P t')). Qed.
Lemma lem3247432 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term286 A t u P) = (term286 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247431 A t u P t')). Qed.
Lemma lem3247433 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247434 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term287 A t u P) = (term287 A t u P).
Proof. exact (MK_COMB (@lem3247433 A) (@lem3247432 A t u P)). Qed.
Lemma lem3247435 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term318 A t u P) = (term287 A t u P).
Proof. exact (TRANS (@lem3247415 A t u P) (@lem3247434 A t u P)). Qed.
Lemma lem3247436 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term287 A t u P.
Proof. exact (EQ_MP (@lem3247435 A t u P) (@lem3247381 A t' u' t u P h1)). Qed.
Lemma lem3247462 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term244 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (eq_refl (term244 A t u P t' u')). Qed.
Lemma lem3247463 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term254 A t u P t') = (term254 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3247462 A t u P t' u')). Qed.
Lemma lem3247464 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247465 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term255 A t u P t') = (term255 A t u P t').
Proof. exact (MK_COMB (@lem3247464 A) (@lem3247463 A t u P t')). Qed.
Lemma lem3247466 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term262 A t u P) = (term262 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3247465 A t u P t')). Qed.
Lemma lem3247467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3247469 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term263 A t u P) = (term263 A t u P).
Proof. exact (MK_COMB (@lem3247467 A) (@lem3247466 A t u P)). Qed.
Lemma lem3247470 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term263 A t u P.
Proof. exact (EQ_MP (@lem3247469 A t u P) (@lem3247388 A t u P t' u' h1)). Qed.
Lemma lem3247483 {A : Type'} (_33249 : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term442 A t u P _33249.
Proof. exact (@lem3247436 A t' u' t u P h1 _33249). Qed.
Lemma lem3247484 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) : (term442 A t u P _33249) = (term277 A t u P _33249).
Proof. exact (eq_refl (term442 A t u P _33249)). Qed.
Lemma lem3247485 {A : Type'} (_33249 : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term277 A t u P _33249.
Proof. exact (EQ_MP (@lem3247484 A t u P _33249) (@lem3247483 A _33249 t' u' t u P h1)). Qed.
Lemma lem3247486 {A : Type'} (_33249 : A -> Prop) (_33250 : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term443 A t u P _33249 _33250.
Proof. exact (@lem3247485 A _33249 t' u' t u P h1 _33250). Qed.
Lemma lem3247487 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term443 A t u P _33249 _33250) = (term271 A t u P _33249 _33250).
Proof. exact (eq_refl (term443 A t u P _33249 _33250)). Qed.
Lemma lem3247489 {A : Type'} (_33251 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term444 A t u P _33251.
Proof. exact (@lem3247470 A t u P t' u' h1 _33251). Qed.
Lemma lem3247490 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) : (term444 A t u P _33251) = (term255 A t u P _33251).
Proof. exact (eq_refl (term444 A t u P _33251)). Qed.
Lemma lem3247491 {A : Type'} (_33251 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term255 A t u P _33251.
Proof. exact (EQ_MP (@lem3247490 A t u P _33251) (@lem3247489 A _33251 t u P t' u' h1)). Qed.
Lemma lem3247492 {A : Type'} (_33251 : A -> Prop) (_33252 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term445 A t u P _33251 _33252.
Proof. exact (@lem3247491 A _33251 t u P t' u' h1 _33252). Qed.
Lemma lem3247493 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term445 A t u P _33251 _33252) = (term244 A t u P _33251 _33252).
Proof. exact (eq_refl (term445 A t u P _33251 _33252)). Qed.
Lemma lem3247494 {A : Type'} (_33251 : A -> Prop) (_33252 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term244 A t u P _33251 _33252.
Proof. exact (EQ_MP (@lem3247493 A t u P _33251 _33252) (@lem3247492 A _33251 _33252 t u P t' u' h1)). Qed.
Lemma lem3247504 {A : Type'} (_33249 : A -> Prop) (_33250 : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term271 A t u P _33249 _33250.
Proof. exact (EQ_MP (@lem3247487 A t u P _33249 _33250) (@lem3247486 A _33249 _33250 t' u' t u P h1)). Qed.
Lemma lem3247521 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term244 A t u P _33251 _33252) = (term271 A t u P _33251 _33252).
Proof. exact (@lem3245551 (term306 A _33251 t) (term306 A _33252 u) (term203 A P _33251 _33252)). Qed.
Lemma lem3247522 {A : Type'} (_33251 : A -> Prop) (_33252 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term271 A t u P _33251 _33252.
Proof. exact (EQ_MP (@lem3247521 A t u P _33251 _33252) (@lem3247494 A _33251 _33252 t u P t' u' h1)). Qed.
Lemma lem3247530 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : @SUBSET A t' t.
Proof. exact (proj1 (@lem3247384 A t' u' t u P h1)). Qed.
Lemma lem3247531 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term446 A t' t.
Proof. exact (fun h0 : term306 A t' t => @lem3247530 A t' u' t u P h1). Qed.
Lemma lem3247533 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247534 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term446 A t' t) = (@SUBSET A t' t).
Proof. exact (@lem3247533 (@SUBSET A t' t)). Qed.
Lemma lem3247535 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : @SUBSET A t' t.
Proof. exact (EQ_MP (@lem3247534 A t' t) (@lem3247531 A t' u' t u P h1)). Qed.
Lemma lem3247537 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : @SUBSET A u' u.
Proof. exact (proj2 (@lem3247384 A t' u' t u P h1)). Qed.
Lemma lem3247538 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term446 A u' u.
Proof. exact (fun h0 : term306 A u' u => @lem3247537 A t' u' t u P h1). Qed.
Lemma lem3247540 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247541 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term446 A u' u) = (@SUBSET A u' u).
Proof. exact (@lem3247540 (@SUBSET A u' u)). Qed.
Lemma lem3247542 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : @SUBSET A u' u.
Proof. exact (EQ_MP (@lem3247541 A u' u) (@lem3247538 A t' u' t u P h1)). Qed.
Lemma lem3247544 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term235 A P t' u'.
Proof. exact (proj2 (@lem3247382 A t' u' t u P h1)). Qed.
Lemma lem3247545 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term447 A P t' u'.
Proof. exact (fun h0 : term203 A P t' u' => @lem3247544 A t' u' t u P h1). Qed.
Lemma lem3247547 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247548 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term447 A P t' u') = (term235 A P t' u').
Proof. exact (@lem3247547 (term235 A P t' u')). Qed.
Lemma lem3247549 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term235 A P t' u'.
Proof. exact (EQ_MP (@lem3247548 A P t' u') (@lem3247545 A t' u' t u P h1)). Qed.
Lemma lem3247551 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3247552 {A : Type'} (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term265 A u P _33249 _33250) = (term174 A u P _33249 _33250).
Proof. exact (@lem3247551 (@SUBSET A _33250 u) (term235 A P _33249 _33250)). Qed.
Lemma lem3247553 {A : Type'} (_33249 : A -> Prop) (t : A -> Prop) : (term269 A _33249 t) = (term269 A _33249 t).
Proof. exact (eq_refl (term269 A _33249 t)). Qed.
Lemma lem3247554 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term271 A t u P _33249 _33250) = (term270 A t u P _33249 _33250).
Proof. exact (MK_COMB (@lem3247553 A _33249 t) (@lem3247552 A u P _33249 _33250)). Qed.
Lemma lem3247556 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3247557 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term270 A t u P _33249 _33250) = (term448 A t u P _33249 _33250).
Proof. exact (@lem3247556 (@SUBSET A _33249 t) (term163 A u P _33249 _33250)). Qed.
Lemma lem3247558 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term271 A t u P _33249 _33250) = (term448 A t u P _33249 _33250).
Proof. exact (TRANS (@lem3247554 A t u P _33249 _33250) (@lem3247557 A t u P _33249 _33250)). Qed.
Lemma lem3247560 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3247561 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term448 A t u P _33249 _33250) = (term449 A t u P _33249 _33250).
Proof. exact (@lem3247560 (term165 A t u P _33249 _33250)). Qed.
Lemma lem3247562 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33249 : A -> Prop) (_33250 : A -> Prop) : (term271 A t u P _33249 _33250) = (term449 A t u P _33249 _33250).
Proof. exact (TRANS (@lem3247558 A t u P _33249 _33250) (@lem3247561 A t u P _33249 _33250)). Qed.
Lemma lem3247564 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term163 A u P t' u'.
Proof. exact (conj (@lem3247542 A t' u' t u P h1) (@lem3247549 A t' u' t u P h1)). Qed.
Lemma lem3247565 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term165 A t u P t' u'.
Proof. exact (conj (@lem3247535 A t' u' t u P h1) (@lem3247564 A t' u' t u P h1)). Qed.
Lemma lem3247567 {A : Type'} (_33249 : A -> Prop) (_33250 : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term449 A t u P _33249 _33250.
Proof. exact (EQ_MP (@lem3247562 A t u P _33249 _33250) (@lem3247504 A _33249 _33250 t' u' t u P h1)). Qed.
Lemma lem3247568 {A : Type'} (_33249 : A -> Prop) (_33250 : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term449 A t u P _33249 _33250.
Proof. exact (@lem3247567 A _33249 _33250 t' u' t u P h1). Qed.
Lemma lem3247569 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term449 A t u P t' u'.
Proof. exact (@lem3247568 A t' u' t' u' t u P h1). Qed.
Lemma lem3247572 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : False.
Proof. exact (@lem3247569 A t' u' t u P h1 (@lem3247565 A t' u' t u P h1)). Qed.
Lemma lem3247573 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : term125.
Proof. exact (fun h0 : ~ False => @lem3247572 A t' u' t u P h1). Qed.
Lemma lem3247575 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247576 : term125 = False.
Proof. exact (@lem3247575 False). Qed.
Lemma lem3247577 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term364 A t' u' t u P) : False.
Proof. exact (EQ_MP (@lem3247576) (@lem3247573 A t' u' t u P h1)). Qed.
Lemma lem3247579 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : @SUBSET A t' t.
Proof. exact (proj1 (@lem3247387 A t u P t' u' h1)). Qed.
Lemma lem3247580 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term446 A t' t.
Proof. exact (fun h0 : term306 A t' t => @lem3247579 A t u P t' u' h1). Qed.
Lemma lem3247582 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247583 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term446 A t' t) = (@SUBSET A t' t).
Proof. exact (@lem3247582 (@SUBSET A t' t)). Qed.
Lemma lem3247584 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : @SUBSET A t' t.
Proof. exact (EQ_MP (@lem3247583 A t' t) (@lem3247580 A t u P t' u' h1)). Qed.
Lemma lem3247586 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : @SUBSET A u' u.
Proof. exact (proj1 (@lem3247389 A t u P t' u' h1)). Qed.
Lemma lem3247587 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term446 A u' u.
Proof. exact (fun h0 : term306 A u' u => @lem3247586 A t u P t' u' h1). Qed.
Lemma lem3247589 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247590 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term446 A u' u) = (@SUBSET A u' u).
Proof. exact (@lem3247589 (@SUBSET A u' u)). Qed.
Lemma lem3247591 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : @SUBSET A u' u.
Proof. exact (EQ_MP (@lem3247590 A u' u) (@lem3247587 A t u P t' u' h1)). Qed.
Lemma lem3247593 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term235 A P t' u'.
Proof. exact (proj2 (@lem3247389 A t u P t' u' h1)). Qed.
Lemma lem3247594 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term447 A P t' u'.
Proof. exact (fun h0 : term203 A P t' u' => @lem3247593 A t u P t' u' h1). Qed.
Lemma lem3247596 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247597 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term447 A P t' u') = (term235 A P t' u').
Proof. exact (@lem3247596 (term235 A P t' u')). Qed.
Lemma lem3247598 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term235 A P t' u'.
Proof. exact (EQ_MP (@lem3247597 A P t' u') (@lem3247594 A t u P t' u' h1)). Qed.
Lemma lem3247600 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3247601 {A : Type'} (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term265 A u P _33251 _33252) = (term174 A u P _33251 _33252).
Proof. exact (@lem3247600 (@SUBSET A _33252 u) (term235 A P _33251 _33252)). Qed.
Lemma lem3247602 {A : Type'} (_33251 : A -> Prop) (t : A -> Prop) : (term269 A _33251 t) = (term269 A _33251 t).
Proof. exact (eq_refl (term269 A _33251 t)). Qed.
Lemma lem3247603 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term271 A t u P _33251 _33252) = (term270 A t u P _33251 _33252).
Proof. exact (MK_COMB (@lem3247602 A _33251 t) (@lem3247601 A u P _33251 _33252)). Qed.
Lemma lem3247605 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3247606 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term270 A t u P _33251 _33252) = (term448 A t u P _33251 _33252).
Proof. exact (@lem3247605 (@SUBSET A _33251 t) (term163 A u P _33251 _33252)). Qed.
Lemma lem3247607 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term271 A t u P _33251 _33252) = (term448 A t u P _33251 _33252).
Proof. exact (TRANS (@lem3247603 A t u P _33251 _33252) (@lem3247606 A t u P _33251 _33252)). Qed.
Lemma lem3247609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3247610 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term448 A t u P _33251 _33252) = (term449 A t u P _33251 _33252).
Proof. exact (@lem3247609 (term165 A t u P _33251 _33252)). Qed.
Lemma lem3247611 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (_33251 : A -> Prop) (_33252 : A -> Prop) : (term271 A t u P _33251 _33252) = (term449 A t u P _33251 _33252).
Proof. exact (TRANS (@lem3247607 A t u P _33251 _33252) (@lem3247610 A t u P _33251 _33252)). Qed.
Lemma lem3247613 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term163 A u P t' u'.
Proof. exact (conj (@lem3247591 A t u P t' u' h1) (@lem3247598 A t u P t' u' h1)). Qed.
Lemma lem3247614 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term165 A t u P t' u'.
Proof. exact (conj (@lem3247584 A t u P t' u' h1) (@lem3247613 A t u P t' u' h1)). Qed.
Lemma lem3247616 {A : Type'} (_33251 : A -> Prop) (_33252 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term449 A t u P _33251 _33252.
Proof. exact (EQ_MP (@lem3247611 A t u P _33251 _33252) (@lem3247522 A _33251 _33252 t u P t' u' h1)). Qed.
Lemma lem3247617 {A : Type'} (_33251 : A -> Prop) (_33252 : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term449 A t u P _33251 _33252.
Proof. exact (@lem3247616 A _33251 _33252 t u P t' u' h1). Qed.
Lemma lem3247618 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term449 A t u P t' u'.
Proof. exact (@lem3247617 A t' u' t u P t' u' h1). Qed.
Lemma lem3247621 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : False.
Proof. exact (@lem3247618 A t u P t' u' h1 (@lem3247614 A t u P t' u' h1)). Qed.
Lemma lem3247622 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : term125.
Proof. exact (fun h0 : ~ False => @lem3247621 A t u P t' u' h1). Qed.
Lemma lem3247624 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3247625 : term125 = False.
Proof. exact (@lem3247624 False). Qed.
Lemma lem3247626 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term393 A t u P t' u') : False.
Proof. exact (EQ_MP (@lem3247625) (@lem3247622 A t u P t' u' h1)). Qed.
Lemma lem3247627 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term434 A t u P t' u') : False.
Proof. exact (or_elim (@lem3247378 A t u P t' u' h1) (fun h0 : term364 A t' u' t u P => @lem3247577 A t' u' t u P h0) (fun h0 : term393 A t u P t' u' => @lem3247626 A t u P t' u' h0)). Qed.
Lemma lem3247628 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term434 A t u P t' u') : (term434 A t u P t' u') = False.
Proof. exact (prop_ext (fun h2 : term434 A t u P t' u' => @lem3247627 A t u P t' u' h1) (fun h2 : False => @lem3247378 A t u P t' u' h1)). Qed.
Lemma lem3247629 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (h1 : term434 A t u P t' u') : False.
Proof. exact (EQ_MP (@lem3247628 A t u P t' u' h1) (@lem3247378 A t u P t' u' h1)). Qed.
Lemma lem3247630 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (h1 : term437 A t u P t') : False.
Proof. exact (ex_elim (@lem3247251 A t u P t' h1) (fun u' : A -> Prop => fun h0 : term436 A t u P t' u' => @lem3247629 A t u P t' u' h0)). Qed.
Lemma lem3247631 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term231 A t u P) : False.
Proof. exact (ex_elim (@lem3247250 A t u P h1) (fun t' : A -> Prop => fun h0 : term438 A t u P t' => @lem3247630 A t u P t' h0)). Qed.
Lemma lem3247632 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term231 A t u P) : (term231 A t u P) = False.
Proof. exact (prop_ext (fun h2 : term231 A t u P => @lem3247631 A t u P h1) (fun h2 : False => @lem3246587 A t u P h1)). Qed.
Lemma lem3247633 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term231 A t u P) : False.
Proof. exact (EQ_MP (@lem3247632 A t u P h1) (@lem3246587 A t u P h1)). Qed.
Lemma lem3247634 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : term230 A t u P.
Proof. exact (fun h0 : term231 A t u P => @lem3247633 A t u P h0). Qed.
Lemma lem3247635 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term214 A t u P) = (term185 A t u P).
Proof. exact (EQ_MP (@lem3246586 A t u P) (@lem3247634 A t u P)). Qed.
Lemma lem3247640 {A : Type'} (t : A -> Prop) (P : type686 A) : term217 A t P.
Proof. exact (fun u : A -> Prop => @lem3247635 A t u P). Qed.
Lemma lem3247645 {A : Type'} (P : type686 A) : term219 A P.
Proof. exact (fun t : A -> Prop => @lem3247640 A t P). Qed.
Lemma lem3247650 {A : Type'} : term229 A.
Proof. exact (fun P : type686 A => @lem3247645 A P). Qed.
Lemma lem3247651 {A : Type'} : term228 A.
Proof. exact (EQ_MP (@lem3246582 A) (@lem3247650 A)). Qed.
Lemma lem3247652 {A : Type'} (P : type686 A) : term450 A P.
Proof. exact (@lem3247651 A P). Qed.
Lemma lem3247653 {A : Type'} (P : type686 A) : (term450 A P) = (term220 A P).
Proof. exact (eq_refl (term450 A P)). Qed.
Lemma lem3247654 {A : Type'} (P : type686 A) : term220 A P.
Proof. exact (EQ_MP (@lem3247653 A P) (@lem3247652 A P)). Qed.
Lemma lem3247656 {A : Type'} (P : type686 A) : term220 A P.
Proof. exact (@lem3246424 A P (@lem3247654 A P)). Qed.
Lemma lem3247657 {A : Type'} (P : type686 A) (h1 : term221 A P) : False.
Proof. exact (@lem3247656 A P (@lem3246408 A P h1)). Qed.
Lemma lem3247658 {A : Type'} (P : type686 A) (h1 : term221 A P) : (term221 A P) = False.
Proof. exact (prop_ext (fun h2 : term221 A P => @lem3247657 A P h1) (fun h2 : False => @lem3246408 A P h1)). Qed.
Lemma lem3247659 {A : Type'} (P : type686 A) (h1 : term221 A P) : False.
Proof. exact (EQ_MP (@lem3247658 A P h1) (@lem3246408 A P h1)). Qed.
Lemma lem3247660 {A : Type'} (P : type686 A) : term220 A P.
Proof. exact (fun h0 : term221 A P => @lem3247659 A P h0). Qed.
Lemma lem3247661 {A : Type'} (P : type686 A) : term219 A P.
Proof. exact (EQ_MP (@lem3246407 A P) (@lem3247660 A P)). Qed.
Lemma lem3247662 {A : Type'} (P : type686 A) : term193 A P.
Proof. exact (EQ_MP (@lem3246403 A P) (@lem3247661 A P)). Qed.
Lemma lem3247663 {A : Type'} (P : type686 A) : term192 A P.
Proof. exact (EQ_MP (@lem3246323 A P) (@lem3247662 A P)). Qed.
