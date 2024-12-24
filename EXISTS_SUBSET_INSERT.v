Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SUBSET_INSERT_term_abbrevs.
Require Import FORALL_SUBSET_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
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
Require Import thm19490_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3252527 {A : Type'} (P : type686 A) (a : A) : term0 A P a.
Proof. exact (@lem3252516 A P a). Qed.
Lemma lem3252528 {A : Type'} (P : type686 A) (a : A) : (term0 A P a) = (term1 A P a).
Proof. exact (eq_refl (term0 A P a)). Qed.
Lemma lem3252529 {A : Type'} (P : type686 A) (a : A) : term1 A P a.
Proof. exact (EQ_MP (@lem3252528 A P a) (@lem3252527 A P a)). Qed.
Lemma lem3252530 {A : Type'} (P : type686 A) (a : A) (t : A -> Prop) : term2 A P a t.
Proof. exact (@lem3252529 A P a t). Qed.
Lemma lem3252531 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term2 A P a t) = ((term3 A a t P) = (term4 A t P a)).
Proof. exact (eq_refl (term2 A P a t)). Qed.
Lemma lem3252544 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3252545 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : ((term6 _85145 P Q) = (term7 _85145 P Q)) = (term8 _85145 P Q).
Proof. exact (@lem3252544 ((term6 _85145 P Q) = (term7 _85145 P Q))). Qed.
Lemma lem3252546 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term8 _85145 P Q) = ((term6 _85145 P Q) = (term7 _85145 P Q)).
Proof. exact (SYM (@lem3252545 _85145 P Q)). Qed.
Lemma lem3252547 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : term9 _85145 P Q.
Proof. exact (h1). Qed.
Lemma lem3252550 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term8 _85145 P Q) : term8 _85145 P Q.
Proof. exact (h1). Qed.
Lemma lem3252551 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term10 _85145 P Q.
Proof. exact (fun h0 : term8 _85145 P Q => @lem3252550 _85145 P Q h0). Qed.
Lemma lem3252552 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term10 _85145 P Q) : term10 _85145 P Q.
Proof. exact (h1). Qed.
Lemma lem3252553 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term8 _85145 P Q) : term8 _85145 P Q.
Proof. exact (h1). Qed.
Lemma lem3252554 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term8 _85145 P Q) (h2 : term10 _85145 P Q) : term8 _85145 P Q.
Proof. exact (@lem3252552 _85145 P Q h2 (@lem3252553 _85145 P Q h1)). Qed.
Lemma lem3252555 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term8 _85145 P Q) : term11 _85145 P Q.
Proof. exact (fun h0 : term10 _85145 P Q => @lem3252554 _85145 P Q h1 h0). Qed.
Lemma lem3252556 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term10 _85145 P Q) : term10 _85145 P Q.
Proof. exact (h1). Qed.
Lemma lem3252557 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term8 _85145 P Q) (h2 : term10 _85145 P Q) : term8 _85145 P Q.
Proof. exact (@lem3252555 _85145 P Q h1 (@lem3252556 _85145 P Q h2)). Qed.
Lemma lem3252558 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term10 _85145 P Q) : term10 _85145 P Q.
Proof. exact (fun h0 : term8 _85145 P Q => @lem3252557 _85145 P Q h0 h1). Qed.
Lemma lem3252559 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term12 _85145 P Q.
Proof. exact (fun h0 : term10 _85145 P Q => @lem3252558 _85145 P Q h0). Qed.
Lemma lem3252562 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term10 _85145 P Q.
Proof. exact (@lem3252559 _85145 P Q (@lem3252551 _85145 P Q)). Qed.
Lemma lem3252563 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term10 _85145 P Q.
Proof. exact (@lem3252562 _85145 P Q). Qed.
Lemma lem3252573 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3252574 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term8 _85145 P Q) = (term13 _85145 P Q).
Proof. exact (@lem3252573 (term9 _85145 P Q)). Qed.
Lemma lem3252576 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3252577 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term13 _85145 P Q) = ((term6 _85145 P Q) = (term7 _85145 P Q)).
Proof. exact (@lem3252576 ((term6 _85145 P Q) = (term7 _85145 P Q))). Qed.
Lemma lem3252578 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term8 _85145 P Q) = ((term6 _85145 P Q) = (term7 _85145 P Q)).
Proof. exact (TRANS (@lem3252574 _85145 P Q) (@lem3252577 _85145 P Q)). Qed.
Lemma lem3252599 {_85145 : Type'} (Q : _85145 -> Prop) : (term15 _85145 Q) = (term16 _85145 Q).
Proof. exact (fun_ext (fun P : _85145 -> Prop => @lem3252578 _85145 P Q)). Qed.
Lemma lem3252600 {_85145 : Type'} : (@all (_85145 -> Prop)) = (@all (_85145 -> Prop)).
Proof. exact (eq_refl (@all (_85145 -> Prop))). Qed.
Lemma lem3252601 {_85145 : Type'} (Q : _85145 -> Prop) : (term17 _85145 Q) = (term18 _85145 Q).
Proof. exact (MK_COMB (@lem3252600 _85145) (@lem3252599 _85145 Q)). Qed.
Lemma lem3252606 {_85145 : Type'} : (term19 _85145) = (term20 _85145).
Proof. exact (fun_ext (fun Q : _85145 -> Prop => @lem3252601 _85145 Q)). Qed.
Lemma lem3252607 {_85145 : Type'} : (@all (_85145 -> Prop)) = (@all (_85145 -> Prop)).
Proof. exact (eq_refl (@all (_85145 -> Prop))). Qed.
Lemma lem3252616 {_85145 : Type'} : (term21 _85145) = (term22 _85145).
Proof. exact (MK_COMB (@lem3252607 _85145) (@lem3252606 _85145)). Qed.
Lemma lem3252623 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term23 _85145 P Q x) = (term23 _85145 P Q x).
Proof. exact (eq_refl (term23 _85145 P Q x)). Qed.
Lemma lem3252624 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term24 _85145 P Q) = (term24 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252623 _85145 P Q x)). Qed.
Lemma lem3252625 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3252626 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term25 _85145 P Q) = (term25 _85145 P Q).
Proof. exact (MK_COMB (@lem3252625 _85145) (@lem3252624 _85145 P Q)). Qed.
Lemma lem3252627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3252628 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term7 _85145 P Q) = (term7 _85145 P Q).
Proof. exact (MK_COMB (@lem3252627) (@lem3252626 _85145 P Q)). Qed.
Lemma lem3252633 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term26 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term26 _85145 P Q x)). Qed.
Lemma lem3252634 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term27 _85145 P Q) = (term27 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252633 _85145 P Q x)). Qed.
Lemma lem3252635 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252636 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term6 _85145 P Q) = (term6 _85145 P Q).
Proof. exact (MK_COMB (@lem3252635 _85145) (@lem3252634 _85145 P Q)). Qed.
Lemma lem3252637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252638 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term28 _85145 P Q) = (term28 _85145 P Q).
Proof. exact (MK_COMB (@lem3252637) (@lem3252636 _85145 P Q)). Qed.
Lemma lem3252639 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : ((term6 _85145 P Q) = (term7 _85145 P Q)) = ((term6 _85145 P Q) = (term7 _85145 P Q)).
Proof. exact (MK_COMB (@lem3252638 _85145 P Q) (@lem3252628 _85145 P Q)). Qed.
Lemma lem3252640 {_85145 : Type'} (Q : _85145 -> Prop) : (term16 _85145 Q) = (term16 _85145 Q).
Proof. exact (fun_ext (fun P : _85145 -> Prop => @lem3252639 _85145 P Q)). Qed.
Lemma lem3252641 {_85145 : Type'} : (@all (_85145 -> Prop)) = (@all (_85145 -> Prop)).
Proof. exact (eq_refl (@all (_85145 -> Prop))). Qed.
Lemma lem3252642 {_85145 : Type'} (Q : _85145 -> Prop) : (term18 _85145 Q) = (term18 _85145 Q).
Proof. exact (MK_COMB (@lem3252641 _85145) (@lem3252640 _85145 Q)). Qed.
Lemma lem3252643 {_85145 : Type'} : (term20 _85145) = (term20 _85145).
Proof. exact (fun_ext (fun Q : _85145 -> Prop => @lem3252642 _85145 Q)). Qed.
Lemma lem3252644 {_85145 : Type'} : (@all (_85145 -> Prop)) = (@all (_85145 -> Prop)).
Proof. exact (eq_refl (@all (_85145 -> Prop))). Qed.
Lemma lem3252645 {_85145 : Type'} : (term22 _85145) = (term22 _85145).
Proof. exact (MK_COMB (@lem3252644 _85145) (@lem3252643 _85145)). Qed.
Lemma lem3252676 {_85145 : Type'} : (term21 _85145) = (term22 _85145).
Proof. exact (TRANS (@lem3252616 _85145) (@lem3252645 _85145)). Qed.
Lemma lem3252677 {_85145 : Type'} : (term22 _85145) = (term21 _85145).
Proof. exact (SYM (@lem3252676 _85145)). Qed.
Lemma lem3252679 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3252680 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : ((term6 _85145 P Q) = (term7 _85145 P Q)) = (term8 _85145 P Q).
Proof. exact (@lem3252679 ((term6 _85145 P Q) = (term7 _85145 P Q))). Qed.
Lemma lem3252681 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term8 _85145 P Q) = ((term6 _85145 P Q) = (term7 _85145 P Q)).
Proof. exact (SYM (@lem3252680 _85145 P Q)). Qed.
Lemma lem3252682 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : term9 _85145 P Q.
Proof. exact (h1). Qed.
Lemma lem3252691 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term29 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (@lem17045 (P x) (Q x)). Qed.
Lemma lem3252694 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term26 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term26 _85145 P Q x)). Qed.
Lemma lem3252695 {_85145 : Type'} (P : _85145 -> Prop) : (term31 _85145 P) = (term32 _85145 P).
Proof. exact (@lem18394 _85145 P). Qed.
Lemma lem3252696 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term33 _85145 P Q) = (term34 _85145 P Q).
Proof. exact (@lem3252695 _85145 (term27 _85145 P Q)). Qed.
Lemma lem3252697 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term35 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term35 _85145 P Q x)). Qed.
Lemma lem3252698 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3252699 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term36 _85145 P Q x) = (term29 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252698) (@lem3252697 _85145 P Q x)). Qed.
Lemma lem3252700 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term36 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (TRANS (@lem3252699 _85145 P Q x) (@lem3252691 _85145 P Q x)). Qed.
Lemma lem3252701 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term37 _85145 P Q) = (term38 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252700 _85145 P Q x)). Qed.
Lemma lem3252702 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3252703 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term34 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (MK_COMB (@lem3252702 _85145) (@lem3252701 _85145 P Q)). Qed.
Lemma lem3252704 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term33 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (TRANS (@lem3252696 _85145 P Q) (@lem3252703 _85145 P Q)). Qed.
Lemma lem3252705 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term27 _85145 P Q) = (term27 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252694 _85145 P Q x)). Qed.
Lemma lem3252706 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252707 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term6 _85145 P Q) = (term6 _85145 P Q).
Proof. exact (MK_COMB (@lem3252706 _85145) (@lem3252705 _85145 P Q)). Qed.
Lemma lem3252713 {_85145 : Type'} (Q : _85145 -> Prop) (x : _85145) : (term40 _85145 Q x) = (Q x).
Proof. exact (@lem16933 (Q x)). Qed.
Lemma lem3252715 {_85145 : Type'} (P : _85145 -> Prop) (x : _85145) : (term41 _85145 P x) = (term41 _85145 P x).
Proof. exact (eq_refl (term41 _85145 P x)). Qed.
Lemma lem3252716 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term42 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252715 _85145 P x) (@lem3252713 _85145 Q x)). Qed.
Lemma lem3252717 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term43 _85145 P Q x) = (term42 _85145 P Q x).
Proof. exact (@lem17362 (P x) (term44 _85145 Q x)). Qed.
Lemma lem3252718 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term43 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (TRANS (@lem3252717 _85145 P Q x) (@lem3252716 _85145 P Q x)). Qed.
Lemma lem3252723 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term23 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (@lem17265 (P x) (term44 _85145 Q x)). Qed.
Lemma lem3252724 {_85145 : Type'} (P : _85145 -> Prop) : (term45 _85145 P) = (term46 _85145 P).
Proof. exact (@lem18392 _85145 P). Qed.
Lemma lem3252725 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term7 _85145 P Q) = (term47 _85145 P Q).
Proof. exact (@lem3252724 _85145 (term24 _85145 P Q)). Qed.
Lemma lem3252726 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term48 _85145 P Q x) = (term23 _85145 P Q x).
Proof. exact (eq_refl (term48 _85145 P Q x)). Qed.
Lemma lem3252727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3252728 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term49 _85145 P Q x) = (term43 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252727) (@lem3252726 _85145 P Q x)). Qed.
Lemma lem3252729 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term49 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (TRANS (@lem3252728 _85145 P Q x) (@lem3252718 _85145 P Q x)). Qed.
Lemma lem3252730 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term50 _85145 P Q) = (term27 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252729 _85145 P Q x)). Qed.
Lemma lem3252731 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252732 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term47 _85145 P Q) = (term6 _85145 P Q).
Proof. exact (MK_COMB (@lem3252731 _85145) (@lem3252730 _85145 P Q)). Qed.
Lemma lem3252733 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term7 _85145 P Q) = (term6 _85145 P Q).
Proof. exact (TRANS (@lem3252725 _85145 P Q) (@lem3252732 _85145 P Q)). Qed.
Lemma lem3252734 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term24 _85145 P Q) = (term38 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252723 _85145 P Q x)). Qed.
Lemma lem3252735 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3252736 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term25 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (MK_COMB (@lem3252735 _85145) (@lem3252734 _85145 P Q)). Qed.
Lemma lem3252737 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term51 _85145 P Q) = (term25 _85145 P Q).
Proof. exact (@lem16933 (term25 _85145 P Q)). Qed.
Lemma lem3252738 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term51 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (TRANS (@lem3252737 _85145 P Q) (@lem3252736 _85145 P Q)). Qed.
Lemma lem3252739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252740 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term52 _85145 P Q) = (term53 _85145 P Q).
Proof. exact (MK_COMB (@lem3252739) (@lem3252704 _85145 P Q)). Qed.
Lemma lem3252741 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term54 _85145 P Q) = (term55 _85145 P Q).
Proof. exact (MK_COMB (@lem3252740 _85145 P Q) (@lem3252733 _85145 P Q)). Qed.
Lemma lem3252742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252743 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term56 _85145 P Q) = (term56 _85145 P Q).
Proof. exact (MK_COMB (@lem3252742) (@lem3252707 _85145 P Q)). Qed.
Lemma lem3252744 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term57 _85145 P Q) = (term58 _85145 P Q).
Proof. exact (MK_COMB (@lem3252743 _85145 P Q) (@lem3252738 _85145 P Q)). Qed.
Lemma lem3252745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3252746 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term59 _85145 P Q) = (term60 _85145 P Q).
Proof. exact (MK_COMB (@lem3252745) (@lem3252744 _85145 P Q)). Qed.
Lemma lem3252747 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term61 _85145 P Q) = (term62 _85145 P Q).
Proof. exact (MK_COMB (@lem3252746 _85145 P Q) (@lem3252741 _85145 P Q)). Qed.
Lemma lem3252748 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term9 _85145 P Q) = (term61 _85145 P Q).
Proof. exact (@lem17646 (term6 _85145 P Q) (term7 _85145 P Q)). Qed.
Lemma lem3252749 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term9 _85145 P Q) = (term62 _85145 P Q).
Proof. exact (TRANS (@lem3252748 _85145 P Q) (@lem3252747 _85145 P Q)). Qed.
Lemma lem3252872 {A : Type'} (P : A -> Prop) (Q : Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3252873 {_85145 : Type'} (P : _85145 -> Prop) (Q : Prop) : (term63 _85145 P Q) = (term64 _85145 P Q).
Proof. exact (@lem3252872 _85145 P Q). Qed.
Lemma lem3252874 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term65 _85145 P Q) = (term66 _85145 P Q).
Proof. exact (@lem3252873 _85145 (term27 _85145 P Q) (term39 _85145 P Q)). Qed.
Lemma lem3252875 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term35 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term35 _85145 P Q x)). Qed.
Lemma lem3252876 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term67 _85145 P Q) = (term27 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252875 _85145 P Q x)). Qed.
Lemma lem3252877 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252878 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term68 _85145 P Q) = (term6 _85145 P Q).
Proof. exact (MK_COMB (@lem3252877 _85145) (@lem3252876 _85145 P Q)). Qed.
Lemma lem3252879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252880 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term69 _85145 P Q) = (term56 _85145 P Q).
Proof. exact (MK_COMB (@lem3252879) (@lem3252878 _85145 P Q)). Qed.
Lemma lem3252881 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term39 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (eq_refl (term39 _85145 P Q)). Qed.
Lemma lem3252882 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term65 _85145 P Q) = (term58 _85145 P Q).
Proof. exact (MK_COMB (@lem3252880 _85145 P Q) (@lem3252881 _85145 P Q)). Qed.
Lemma lem3252883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252884 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term70 _85145 P Q) = (term71 _85145 P Q).
Proof. exact (MK_COMB (@lem3252883) (@lem3252882 _85145 P Q)). Qed.
Lemma lem3252885 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term35 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term35 _85145 P Q x)). Qed.
Lemma lem3252886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252887 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term72 _85145 P Q x) = (term73 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252886) (@lem3252885 _85145 P Q x)). Qed.
Lemma lem3252888 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term39 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (eq_refl (term39 _85145 P Q)). Qed.
Lemma lem3252889 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term74 _85145 x P Q) = (term75 _85145 x P Q).
Proof. exact (MK_COMB (@lem3252887 _85145 P Q x) (@lem3252888 _85145 P Q)). Qed.
Lemma lem3252890 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term76 _85145 P Q) = (term77 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252889 _85145 x P Q)). Qed.
Lemma lem3252891 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252892 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term66 _85145 P Q) = (term78 _85145 P Q).
Proof. exact (MK_COMB (@lem3252891 _85145) (@lem3252890 _85145 P Q)). Qed.
Lemma lem3252893 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : ((term65 _85145 P Q) = (term66 _85145 P Q)) = ((term58 _85145 P Q) = (term78 _85145 P Q)).
Proof. exact (MK_COMB (@lem3252884 _85145 P Q) (@lem3252892 _85145 P Q)). Qed.
Lemma lem3252894 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term58 _85145 P Q) = (term78 _85145 P Q).
Proof. exact (EQ_MP (@lem3252893 _85145 P Q) (@lem3252874 _85145 P Q)). Qed.
Lemma lem3252895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3252896 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term60 _85145 P Q) = (term79 _85145 P Q).
Proof. exact (MK_COMB (@lem3252895) (@lem3252894 _85145 P Q)). Qed.
Lemma lem3252898 {A : Type'} (P : Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3252899 {_85145 : Type'} (P : Prop) (Q : _85145 -> Prop) : (term80 _85145 P Q) = (term81 _85145 P Q).
Proof. exact (@lem3252898 _85145 P Q). Qed.
Lemma lem3252900 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term82 _85145 P Q) = (term83 _85145 P Q).
Proof. exact (@lem3252899 _85145 (term39 _85145 P Q) (term27 _85145 P Q)). Qed.
Lemma lem3252901 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term35 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term35 _85145 P Q x)). Qed.
Lemma lem3252902 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term67 _85145 P Q) = (term27 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252901 _85145 P Q x)). Qed.
Lemma lem3252903 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252904 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term68 _85145 P Q) = (term6 _85145 P Q).
Proof. exact (MK_COMB (@lem3252903 _85145) (@lem3252902 _85145 P Q)). Qed.
Lemma lem3252905 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term53 _85145 P Q) = (term53 _85145 P Q).
Proof. exact (eq_refl (term53 _85145 P Q)). Qed.
Lemma lem3252906 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term82 _85145 P Q) = (term55 _85145 P Q).
Proof. exact (MK_COMB (@lem3252905 _85145 P Q) (@lem3252904 _85145 P Q)). Qed.
Lemma lem3252907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252908 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term84 _85145 P Q) = (term85 _85145 P Q).
Proof. exact (MK_COMB (@lem3252907) (@lem3252906 _85145 P Q)). Qed.
Lemma lem3252909 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term35 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term35 _85145 P Q x)). Qed.
Lemma lem3252910 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term53 _85145 P Q) = (term53 _85145 P Q).
Proof. exact (eq_refl (term53 _85145 P Q)). Qed.
Lemma lem3252911 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term86 _85145 P Q x) = (term87 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252910 _85145 P Q) (@lem3252909 _85145 P Q x)). Qed.
Lemma lem3252912 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term88 _85145 P Q) = (term89 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252911 _85145 P Q x)). Qed.
Lemma lem3252913 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252914 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term83 _85145 P Q) = (term90 _85145 P Q).
Proof. exact (MK_COMB (@lem3252913 _85145) (@lem3252912 _85145 P Q)). Qed.
Lemma lem3252915 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : ((term82 _85145 P Q) = (term83 _85145 P Q)) = ((term55 _85145 P Q) = (term90 _85145 P Q)).
Proof. exact (MK_COMB (@lem3252908 _85145 P Q) (@lem3252914 _85145 P Q)). Qed.
Lemma lem3252916 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term55 _85145 P Q) = (term90 _85145 P Q).
Proof. exact (EQ_MP (@lem3252915 _85145 P Q) (@lem3252900 _85145 P Q)). Qed.
Lemma lem3252917 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term62 _85145 P Q) = (term91 _85145 P Q).
Proof. exact (MK_COMB (@lem3252896 _85145 P Q) (@lem3252916 _85145 P Q)). Qed.
Lemma lem3252919 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3252920 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term92 _85145 P Q) = (term93 _85145 P Q).
Proof. exact (@lem3252919 _85145 P Q). Qed.
Lemma lem3252921 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term94 _85145 P Q) = (term95 _85145 P Q).
Proof. exact (@lem3252920 _85145 (term77 _85145 P Q) (term89 _85145 P Q)). Qed.
Lemma lem3252922 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term96 _85145 P Q x) = (term75 _85145 x P Q).
Proof. exact (eq_refl (term96 _85145 P Q x)). Qed.
Lemma lem3252923 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term97 _85145 P Q) = (term77 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252922 _85145 x P Q)). Qed.
Lemma lem3252924 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252925 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term98 _85145 P Q) = (term78 _85145 P Q).
Proof. exact (MK_COMB (@lem3252924 _85145) (@lem3252923 _85145 P Q)). Qed.
Lemma lem3252926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3252927 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term99 _85145 P Q) = (term79 _85145 P Q).
Proof. exact (MK_COMB (@lem3252926) (@lem3252925 _85145 P Q)). Qed.
Lemma lem3252928 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term100 _85145 P Q x) = (term87 _85145 P Q x).
Proof. exact (eq_refl (term100 _85145 P Q x)). Qed.
Lemma lem3252929 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term101 _85145 P Q) = (term89 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252928 _85145 P Q x)). Qed.
Lemma lem3252930 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252931 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term102 _85145 P Q) = (term90 _85145 P Q).
Proof. exact (MK_COMB (@lem3252930 _85145) (@lem3252929 _85145 P Q)). Qed.
Lemma lem3252932 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term94 _85145 P Q) = (term91 _85145 P Q).
Proof. exact (MK_COMB (@lem3252927 _85145 P Q) (@lem3252931 _85145 P Q)). Qed.
Lemma lem3252933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252934 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term103 _85145 P Q) = (term104 _85145 P Q).
Proof. exact (MK_COMB (@lem3252933) (@lem3252932 _85145 P Q)). Qed.
Lemma lem3252935 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term96 _85145 P Q x) = (term75 _85145 x P Q).
Proof. exact (eq_refl (term96 _85145 P Q x)). Qed.
Lemma lem3252936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3252937 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term105 _85145 P Q x) = (term106 _85145 x P Q).
Proof. exact (MK_COMB (@lem3252936) (@lem3252935 _85145 x P Q)). Qed.
Lemma lem3252938 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term100 _85145 P Q x) = (term87 _85145 P Q x).
Proof. exact (eq_refl (term100 _85145 P Q x)). Qed.
Lemma lem3252939 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term107 _85145 P Q x) = (term108 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252937 _85145 x P Q) (@lem3252938 _85145 P Q x)). Qed.
Lemma lem3252940 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term109 _85145 P Q) = (term110 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252939 _85145 P Q x)). Qed.
Lemma lem3252941 {_85145 : Type'} : (@ex _85145) = (@ex _85145).
Proof. exact (eq_refl (@ex _85145)). Qed.
Lemma lem3252942 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term95 _85145 P Q) = (term111 _85145 P Q).
Proof. exact (MK_COMB (@lem3252941 _85145) (@lem3252940 _85145 P Q)). Qed.
Lemma lem3252943 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : ((term94 _85145 P Q) = (term95 _85145 P Q)) = ((term91 _85145 P Q) = (term111 _85145 P Q)).
Proof. exact (MK_COMB (@lem3252934 _85145 P Q) (@lem3252942 _85145 P Q)). Qed.
Lemma lem3252944 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term91 _85145 P Q) = (term111 _85145 P Q).
Proof. exact (EQ_MP (@lem3252943 _85145 P Q) (@lem3252921 _85145 P Q)). Qed.
Lemma lem3252946 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term62 _85145 P Q) = (term111 _85145 P Q).
Proof. exact (TRANS (@lem3252917 _85145 P Q) (@lem3252944 _85145 P Q)). Qed.
Lemma lem3252947 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term9 _85145 P Q) = (term111 _85145 P Q).
Proof. exact (TRANS (@lem3252749 _85145 P Q) (@lem3252946 _85145 P Q)). Qed.
Lemma lem3252948 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : term111 _85145 P Q.
Proof. exact (EQ_MP (@lem3252947 _85145 P Q) (@lem3252682 _85145 P Q h1)). Qed.
Lemma lem3252949 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term108 _85145 P Q x) : term108 _85145 P Q x.
Proof. exact (h1). Qed.
Lemma lem3252958 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term26 _85145 P Q x) = (term26 _85145 P Q x).
Proof. exact (eq_refl (term26 _85145 P Q x)). Qed.
Lemma lem3252971 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term30 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (eq_refl (term30 _85145 P Q x)). Qed.
Lemma lem3252972 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term38 _85145 P Q) = (term38 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252971 _85145 P Q x)). Qed.
Lemma lem3252973 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3252974 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term39 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (MK_COMB (@lem3252973 _85145) (@lem3252972 _85145 P Q)). Qed.
Lemma lem3252975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252976 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term53 _85145 P Q) = (term53 _85145 P Q).
Proof. exact (MK_COMB (@lem3252975) (@lem3252974 _85145 P Q)). Qed.
Lemma lem3252977 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term87 _85145 P Q x) = (term87 _85145 P Q x).
Proof. exact (MK_COMB (@lem3252976 _85145 P Q) (@lem3252958 _85145 P Q x)). Qed.
Lemma lem3252990 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term30 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (eq_refl (term30 _85145 P Q x)). Qed.
Lemma lem3252991 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term38 _85145 P Q) = (term38 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3252990 _85145 P Q x)). Qed.
Lemma lem3252992 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3252993 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term39 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (MK_COMB (@lem3252992 _85145) (@lem3252991 _85145 P Q)). Qed.
Lemma lem3253004 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term73 _85145 P Q x) = (term73 _85145 P Q x).
Proof. exact (eq_refl (term73 _85145 P Q x)). Qed.
Lemma lem3253005 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term75 _85145 x P Q) = (term75 _85145 x P Q).
Proof. exact (MK_COMB (@lem3253004 _85145 P Q x) (@lem3252993 _85145 P Q)). Qed.
Lemma lem3253006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253007 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term106 _85145 x P Q) = (term106 _85145 x P Q).
Proof. exact (MK_COMB (@lem3253006) (@lem3253005 _85145 x P Q)). Qed.
Lemma lem3253008 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term108 _85145 P Q x) = (term108 _85145 P Q x).
Proof. exact (MK_COMB (@lem3253007 _85145 x P Q) (@lem3252977 _85145 P Q x)). Qed.
Lemma lem3253009 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term108 _85145 P Q x) : term108 _85145 P Q x.
Proof. exact (EQ_MP (@lem3253008 _85145 P Q x) (@lem3252949 _85145 P Q x h1)). Qed.
Lemma lem3253010 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term75 _85145 x P Q.
Proof. exact (h1). Qed.
Lemma lem3253011 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term87 _85145 P Q x.
Proof. exact (h1). Qed.
Lemma lem3253012 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term39 _85145 P Q.
Proof. exact (proj2 (@lem3253010 _85145 x P Q h1)). Qed.
Lemma lem3253013 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term26 _85145 P Q x.
Proof. exact (proj1 (@lem3253010 _85145 x P Q h1)). Qed.
Lemma lem3253016 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term26 _85145 P Q x.
Proof. exact (proj2 (@lem3253011 _85145 P Q x h1)). Qed.
Lemma lem3253017 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term39 _85145 P Q.
Proof. exact (proj1 (@lem3253011 _85145 P Q x h1)). Qed.
Lemma lem3253027 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term30 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (eq_refl (term30 _85145 P Q x)). Qed.
Lemma lem3253028 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term38 _85145 P Q) = (term38 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3253027 _85145 P Q x)). Qed.
Lemma lem3253029 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3253031 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term39 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (MK_COMB (@lem3253029 _85145) (@lem3253028 _85145 P Q)). Qed.
Lemma lem3253032 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term39 _85145 P Q.
Proof. exact (EQ_MP (@lem3253031 _85145 P Q) (@lem3253012 _85145 x P Q h1)). Qed.
Lemma lem3253048 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) : (term30 _85145 P Q x) = (term30 _85145 P Q x).
Proof. exact (eq_refl (term30 _85145 P Q x)). Qed.
Lemma lem3253049 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term38 _85145 P Q) = (term38 _85145 P Q).
Proof. exact (fun_ext (fun x : _85145 => @lem3253048 _85145 P Q x)). Qed.
Lemma lem3253050 {_85145 : Type'} : (@all _85145) = (@all _85145).
Proof. exact (eq_refl (@all _85145)). Qed.
Lemma lem3253052 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term39 _85145 P Q) = (term39 _85145 P Q).
Proof. exact (MK_COMB (@lem3253050 _85145) (@lem3253049 _85145 P Q)). Qed.
Lemma lem3253053 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term39 _85145 P Q.
Proof. exact (EQ_MP (@lem3253052 _85145 P Q) (@lem3253017 _85145 P Q x h1)). Qed.
Lemma lem3253062 {_85145 : Type'} (_33388 : _85145) (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term112 _85145 P Q _33388.
Proof. exact (@lem3253032 _85145 x P Q h1 _33388). Qed.
Lemma lem3253063 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33388 : _85145) : (term112 _85145 P Q _33388) = (term30 _85145 P Q _33388).
Proof. exact (eq_refl (term112 _85145 P Q _33388)). Qed.
Lemma lem3253065 {_85145 : Type'} (_33389 : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term112 _85145 P Q _33389.
Proof. exact (@lem3253053 _85145 P Q x h1 _33389). Qed.
Lemma lem3253066 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33389 : _85145) : (term112 _85145 P Q _33389) = (term30 _85145 P Q _33389).
Proof. exact (eq_refl (term112 _85145 P Q _33389)). Qed.
Lemma lem3253073 {_85145 : Type'} (_33388 : _85145) (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term30 _85145 P Q _33388.
Proof. exact (EQ_MP (@lem3253063 _85145 P Q _33388) (@lem3253062 _85145 _33388 x P Q h1)). Qed.
Lemma lem3253083 {_85145 : Type'} (_33389 : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term30 _85145 P Q _33389.
Proof. exact (EQ_MP (@lem3253066 _85145 P Q _33389) (@lem3253065 _85145 _33389 P Q x h1)). Qed.
Lemma lem3253089 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : P x.
Proof. exact (proj1 (@lem3253013 _85145 x P Q h1)). Qed.
Lemma lem3253090 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term113 _85145 P x.
Proof. exact (fun h0 : term44 _85145 P x => @lem3253089 _85145 x P Q h1). Qed.
Lemma lem3253092 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3253093 {_85145 : Type'} (P : _85145 -> Prop) (x : _85145) : (term113 _85145 P x) = (P x).
Proof. exact (@lem3253092 (P x)). Qed.
Lemma lem3253094 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : P x.
Proof. exact (EQ_MP (@lem3253093 _85145 P x) (@lem3253090 _85145 x P Q h1)). Qed.
Lemma lem3253096 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : Q x.
Proof. exact (proj2 (@lem3253013 _85145 x P Q h1)). Qed.
Lemma lem3253097 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term113 _85145 Q x.
Proof. exact (fun h0 : term44 _85145 Q x => @lem3253096 _85145 x P Q h1). Qed.
Lemma lem3253099 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3253100 {_85145 : Type'} (Q : _85145 -> Prop) (x : _85145) : (term113 _85145 Q x) = (Q x).
Proof. exact (@lem3253099 (Q x)). Qed.
Lemma lem3253101 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : Q x.
Proof. exact (EQ_MP (@lem3253100 _85145 Q x) (@lem3253097 _85145 x P Q h1)). Qed.
Lemma lem3253103 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3253104 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33388 : _85145) : (term30 _85145 P Q _33388) = (term29 _85145 P Q _33388).
Proof. exact (@lem3253103 (P _33388) (Q _33388)). Qed.
Lemma lem3253106 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3253107 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33388 : _85145) : (term29 _85145 P Q _33388) = (term117 _85145 P Q _33388).
Proof. exact (@lem3253106 (term26 _85145 P Q _33388)). Qed.
Lemma lem3253108 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33388 : _85145) : (term30 _85145 P Q _33388) = (term117 _85145 P Q _33388).
Proof. exact (TRANS (@lem3253104 _85145 P Q _33388) (@lem3253107 _85145 P Q _33388)). Qed.
Lemma lem3253110 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term26 _85145 P Q x.
Proof. exact (conj (@lem3253094 _85145 x P Q h1) (@lem3253101 _85145 x P Q h1)). Qed.
Lemma lem3253112 {_85145 : Type'} (_33388 : _85145) (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term117 _85145 P Q _33388.
Proof. exact (EQ_MP (@lem3253108 _85145 P Q _33388) (@lem3253073 _85145 _33388 x P Q h1)). Qed.
Lemma lem3253113 {_85145 : Type'} (_33388 : _85145) (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term117 _85145 P Q _33388.
Proof. exact (@lem3253112 _85145 _33388 x P Q h1). Qed.
Lemma lem3253114 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term117 _85145 P Q x.
Proof. exact (@lem3253113 _85145 x x P Q h1). Qed.
Lemma lem3253117 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : False.
Proof. exact (@lem3253114 _85145 x P Q h1 (@lem3253110 _85145 x P Q h1)). Qed.
Lemma lem3253118 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : term118.
Proof. exact (fun h0 : ~ False => @lem3253117 _85145 x P Q h1). Qed.
Lemma lem3253120 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3253121 : term118 = False.
Proof. exact (@lem3253120 False). Qed.
Lemma lem3253122 {_85145 : Type'} (x : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term75 _85145 x P Q) : False.
Proof. exact (EQ_MP (@lem3253121) (@lem3253118 _85145 x P Q h1)). Qed.
Lemma lem3253124 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : P x.
Proof. exact (proj1 (@lem3253016 _85145 P Q x h1)). Qed.
Lemma lem3253125 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term113 _85145 P x.
Proof. exact (fun h0 : term44 _85145 P x => @lem3253124 _85145 P Q x h1). Qed.
Lemma lem3253127 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3253128 {_85145 : Type'} (P : _85145 -> Prop) (x : _85145) : (term113 _85145 P x) = (P x).
Proof. exact (@lem3253127 (P x)). Qed.
Lemma lem3253129 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : P x.
Proof. exact (EQ_MP (@lem3253128 _85145 P x) (@lem3253125 _85145 P Q x h1)). Qed.
Lemma lem3253131 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : Q x.
Proof. exact (proj2 (@lem3253016 _85145 P Q x h1)). Qed.
Lemma lem3253132 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term113 _85145 Q x.
Proof. exact (fun h0 : term44 _85145 Q x => @lem3253131 _85145 P Q x h1). Qed.
Lemma lem3253134 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3253135 {_85145 : Type'} (Q : _85145 -> Prop) (x : _85145) : (term113 _85145 Q x) = (Q x).
Proof. exact (@lem3253134 (Q x)). Qed.
Lemma lem3253136 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : Q x.
Proof. exact (EQ_MP (@lem3253135 _85145 Q x) (@lem3253132 _85145 P Q x h1)). Qed.
Lemma lem3253138 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3253139 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33389 : _85145) : (term30 _85145 P Q _33389) = (term29 _85145 P Q _33389).
Proof. exact (@lem3253138 (P _33389) (Q _33389)). Qed.
Lemma lem3253141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3253142 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33389 : _85145) : (term29 _85145 P Q _33389) = (term117 _85145 P Q _33389).
Proof. exact (@lem3253141 (term26 _85145 P Q _33389)). Qed.
Lemma lem3253143 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (_33389 : _85145) : (term30 _85145 P Q _33389) = (term117 _85145 P Q _33389).
Proof. exact (TRANS (@lem3253139 _85145 P Q _33389) (@lem3253142 _85145 P Q _33389)). Qed.
Lemma lem3253145 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term26 _85145 P Q x.
Proof. exact (conj (@lem3253129 _85145 P Q x h1) (@lem3253136 _85145 P Q x h1)). Qed.
Lemma lem3253147 {_85145 : Type'} (_33389 : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term117 _85145 P Q _33389.
Proof. exact (EQ_MP (@lem3253143 _85145 P Q _33389) (@lem3253083 _85145 _33389 P Q x h1)). Qed.
Lemma lem3253148 {_85145 : Type'} (_33389 : _85145) (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term117 _85145 P Q _33389.
Proof. exact (@lem3253147 _85145 _33389 P Q x h1). Qed.
Lemma lem3253149 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term117 _85145 P Q x.
Proof. exact (@lem3253148 _85145 x P Q x h1). Qed.
Lemma lem3253152 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : False.
Proof. exact (@lem3253149 _85145 P Q x h1 (@lem3253145 _85145 P Q x h1)). Qed.
Lemma lem3253153 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : term118.
Proof. exact (fun h0 : ~ False => @lem3253152 _85145 P Q x h1). Qed.
Lemma lem3253155 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3253156 : term118 = False.
Proof. exact (@lem3253155 False). Qed.
Lemma lem3253157 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term87 _85145 P Q x) : False.
Proof. exact (EQ_MP (@lem3253156) (@lem3253153 _85145 P Q x h1)). Qed.
Lemma lem3253158 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term108 _85145 P Q x) : False.
Proof. exact (or_elim (@lem3253009 _85145 P Q x h1) (fun h0 : term75 _85145 x P Q => @lem3253122 _85145 x P Q h0) (fun h0 : term87 _85145 P Q x => @lem3253157 _85145 P Q x h0)). Qed.
Lemma lem3253159 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term108 _85145 P Q x) : (term108 _85145 P Q x) = False.
Proof. exact (prop_ext (fun h2 : term108 _85145 P Q x => @lem3253158 _85145 P Q x h1) (fun h2 : False => @lem3253009 _85145 P Q x h1)). Qed.
Lemma lem3253160 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (x : _85145) (h1 : term108 _85145 P Q x) : False.
Proof. exact (EQ_MP (@lem3253159 _85145 P Q x h1) (@lem3253009 _85145 P Q x h1)). Qed.
Lemma lem3253161 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : False.
Proof. exact (ex_elim (@lem3252948 _85145 P Q h1) (fun x : _85145 => fun h0 : term110 _85145 P Q x => @lem3253160 _85145 P Q x h0)). Qed.
Lemma lem3253162 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : (term9 _85145 P Q) = False.
Proof. exact (prop_ext (fun h2 : term9 _85145 P Q => @lem3253161 _85145 P Q h1) (fun h2 : False => @lem3252682 _85145 P Q h1)). Qed.
Lemma lem3253163 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : False.
Proof. exact (EQ_MP (@lem3253162 _85145 P Q h1) (@lem3252682 _85145 P Q h1)). Qed.
Lemma lem3253164 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term8 _85145 P Q.
Proof. exact (fun h0 : term9 _85145 P Q => @lem3253163 _85145 P Q h0). Qed.
Lemma lem3253165 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term6 _85145 P Q) = (term7 _85145 P Q).
Proof. exact (EQ_MP (@lem3252681 _85145 P Q) (@lem3253164 _85145 P Q)). Qed.
Lemma lem3253170 {_85145 : Type'} (Q : _85145 -> Prop) : term18 _85145 Q.
Proof. exact (fun P : _85145 -> Prop => @lem3253165 _85145 P Q). Qed.
Lemma lem3253175 {_85145 : Type'} : term22 _85145.
Proof. exact (fun Q : _85145 -> Prop => @lem3253170 _85145 Q). Qed.
Lemma lem3253176 {_85145 : Type'} : term21 _85145.
Proof. exact (EQ_MP (@lem3252677 _85145) (@lem3253175 _85145)). Qed.
Lemma lem3253177 {_85145 : Type'} (Q : _85145 -> Prop) : term119 _85145 Q.
Proof. exact (@lem3253176 _85145 Q). Qed.
Lemma lem3253178 {_85145 : Type'} (Q : _85145 -> Prop) : (term119 _85145 Q) = (term17 _85145 Q).
Proof. exact (eq_refl (term119 _85145 Q)). Qed.
Lemma lem3253179 {_85145 : Type'} (Q : _85145 -> Prop) : term17 _85145 Q.
Proof. exact (EQ_MP (@lem3253178 _85145 Q) (@lem3253177 _85145 Q)). Qed.
Lemma lem3253180 {_85145 : Type'} (Q : _85145 -> Prop) (P : _85145 -> Prop) : term120 _85145 Q P.
Proof. exact (@lem3253179 _85145 Q P). Qed.
Lemma lem3253181 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term120 _85145 Q P) = (term8 _85145 P Q).
Proof. exact (eq_refl (term120 _85145 Q P)). Qed.
Lemma lem3253182 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term8 _85145 P Q.
Proof. exact (EQ_MP (@lem3253181 _85145 P Q) (@lem3253180 _85145 Q P)). Qed.
Lemma lem3253184 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term8 _85145 P Q.
Proof. exact (@lem3252563 _85145 P Q (@lem3253182 _85145 P Q)). Qed.
Lemma lem3253185 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : False.
Proof. exact (@lem3253184 _85145 P Q (@lem3252547 _85145 P Q h1)). Qed.
Lemma lem3253186 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : (term9 _85145 P Q) = False.
Proof. exact (prop_ext (fun h2 : term9 _85145 P Q => @lem3253185 _85145 P Q h1) (fun h2 : False => @lem3252547 _85145 P Q h1)). Qed.
Lemma lem3253187 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) (h1 : term9 _85145 P Q) : False.
Proof. exact (EQ_MP (@lem3253186 _85145 P Q h1) (@lem3252547 _85145 P Q h1)). Qed.
Lemma lem3253188 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : term8 _85145 P Q.
Proof. exact (fun h0 : term9 _85145 P Q => @lem3253187 _85145 P Q h0). Qed.
Lemma lem3253201 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term6 _85145 P Q) = (term7 _85145 P Q).
Proof. exact (EQ_MP (@lem3252546 _85145 P Q) (@lem3253188 _85145 P Q)). Qed.
Lemma lem3253202 {A : Type'} (P : type686 A) (Q : type686 A) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3253201 (A -> Prop) P Q). Qed.
Lemma lem3253203 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term123 A a t P) = (term124 A a t P).
Proof. exact (@lem3253202 A (term125 A a t) P). Qed.
Lemma lem3253204 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term126 A a t s) = (term127 A s a t).
Proof. exact (eq_refl (term126 A a t s)). Qed.
Lemma lem3253205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253206 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term128 A a t s) = (term129 A s a t).
Proof. exact (MK_COMB (@lem3253205) (@lem3253204 A s a t)). Qed.
Lemma lem3253207 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3253208 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (s : A -> Prop) : (term130 A a t P s) = (term131 A a t P s).
Proof. exact (MK_COMB (@lem3253206 A s a t) (@lem3253207 A P s)). Qed.
Lemma lem3253209 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term132 A a t P) = (term133 A a t P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253208 A a t P s)). Qed.
Lemma lem3253210 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253211 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term123 A a t P) = (term134 A a t P).
Proof. exact (MK_COMB (@lem3253210 A) (@lem3253209 A a t P)). Qed.
Lemma lem3253212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253213 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term135 A a t P) = (term136 A a t P).
Proof. exact (MK_COMB (@lem3253212) (@lem3253211 A a t P)). Qed.
Lemma lem3253214 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term126 A a t s) = (term127 A s a t).
Proof. exact (eq_refl (term126 A a t s)). Qed.
Lemma lem3253215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3253216 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term137 A a t s) = (term138 A s a t).
Proof. exact (MK_COMB (@lem3253215) (@lem3253214 A s a t)). Qed.
Lemma lem3253217 {A : Type'} (P : type686 A) (s : A -> Prop) : (term139 A P s) = (term139 A P s).
Proof. exact (eq_refl (term139 A P s)). Qed.
Lemma lem3253218 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (s : A -> Prop) : (term140 A a t P s) = (term141 A a t P s).
Proof. exact (MK_COMB (@lem3253216 A s a t) (@lem3253217 A P s)). Qed.
Lemma lem3253219 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term142 A a t P) = (term143 A a t P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253218 A a t P s)). Qed.
Lemma lem3253220 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253221 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term144 A a t P) = (term145 A a t P).
Proof. exact (MK_COMB (@lem3253220 A) (@lem3253219 A a t P)). Qed.
Lemma lem3253222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253223 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term124 A a t P) = (term146 A a t P).
Proof. exact (MK_COMB (@lem3253222) (@lem3253221 A a t P)). Qed.
Lemma lem3253224 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : ((term123 A a t P) = (term124 A a t P)) = ((term134 A a t P) = (term146 A a t P)).
Proof. exact (MK_COMB (@lem3253213 A a t P) (@lem3253223 A a t P)). Qed.
Lemma lem3253225 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term134 A a t P) = (term146 A a t P).
Proof. exact (EQ_MP (@lem3253224 A a t P) (@lem3253203 A a t P)). Qed.
Lemma lem3253232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253233 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term136 A a t P) = (term147 A a t P).
Proof. exact (MK_COMB (@lem3253232) (@lem3253225 A a t P)). Qed.
Lemma lem3253235 {_85145 : Type'} (P : _85145 -> Prop) (Q : _85145 -> Prop) : (term6 _85145 P Q) = (term7 _85145 P Q).
Proof. exact (EQ_MP (@lem3252546 _85145 P Q) (@lem3253188 _85145 P Q)). Qed.
Lemma lem3253236 {A : Type'} (P : type686 A) (Q : type686 A) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3253235 (A -> Prop) P Q). Qed.
Lemma lem3253237 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term148 A t P a) = (term149 A t P a).
Proof. exact (@lem3253236 A (term150 A t) (term151 A P a)). Qed.
Lemma lem3253238 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term152 A t s)). Qed.
Lemma lem3253239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253240 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term153 A t s) = (term154 A s t).
Proof. exact (MK_COMB (@lem3253239) (@lem3253238 A s t)). Qed.
Lemma lem3253241 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term155 A P a s) = (term156 A P a s).
Proof. exact (eq_refl (term155 A P a s)). Qed.
Lemma lem3253242 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term157 A t P a s) = (term158 A t P a s).
Proof. exact (MK_COMB (@lem3253240 A s t) (@lem3253241 A P a s)). Qed.
Lemma lem3253243 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term159 A t P a) = (term160 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253242 A t P a s)). Qed.
Lemma lem3253244 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253245 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term148 A t P a) = (term161 A t P a).
Proof. exact (MK_COMB (@lem3253244 A) (@lem3253243 A t P a)). Qed.
Lemma lem3253246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253247 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term162 A t P a) = (term163 A t P a).
Proof. exact (MK_COMB (@lem3253246) (@lem3253245 A t P a)). Qed.
Lemma lem3253248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term152 A t s)). Qed.
Lemma lem3253249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3253250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term164 A t s) = (term165 A s t).
Proof. exact (MK_COMB (@lem3253249) (@lem3253248 A s t)). Qed.
Lemma lem3253251 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term155 A P a s) = (term156 A P a s).
Proof. exact (eq_refl (term155 A P a s)). Qed.
Lemma lem3253252 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253253 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term166 A P a s) = (term167 A P a s).
Proof. exact (MK_COMB (@lem3253252) (@lem3253251 A P a s)). Qed.
Lemma lem3253254 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term168 A t P a s) = (term169 A t P a s).
Proof. exact (MK_COMB (@lem3253250 A s t) (@lem3253253 A P a s)). Qed.
Lemma lem3253255 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term170 A t P a) = (term171 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253254 A t P a s)). Qed.
Lemma lem3253256 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253257 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term172 A t P a) = (term173 A t P a).
Proof. exact (MK_COMB (@lem3253256 A) (@lem3253255 A t P a)). Qed.
Lemma lem3253258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253259 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term149 A t P a) = (term174 A t P a).
Proof. exact (MK_COMB (@lem3253258) (@lem3253257 A t P a)). Qed.
Lemma lem3253260 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term148 A t P a) = (term149 A t P a)) = ((term161 A t P a) = (term174 A t P a)).
Proof. exact (MK_COMB (@lem3253247 A t P a) (@lem3253259 A t P a)). Qed.
Lemma lem3253261 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term161 A t P a) = (term174 A t P a).
Proof. exact (EQ_MP (@lem3253260 A t P a) (@lem3253237 A t P a)). Qed.
Lemma lem3253270 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term134 A a t P) = (term161 A t P a)) = ((term146 A a t P) = (term174 A t P a)).
Proof. exact (MK_COMB (@lem3253233 A a t P) (@lem3253261 A t P a)). Qed.
Lemma lem3253273 {A : Type'} (P : type686 A) (a : A) : (term175 A P a) = (term176 A P a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3253270 A t P a)). Qed.
Lemma lem3253274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253275 {A : Type'} (P : type686 A) (a : A) : (term177 A P a) = (term178 A P a).
Proof. exact (MK_COMB (@lem3253274 A) (@lem3253273 A P a)). Qed.
Lemma lem3253280 {A : Type'} (P : type686 A) : (term179 A P) = (term180 A P).
Proof. exact (fun_ext (fun a : A => @lem3253275 A P a)). Qed.
Lemma lem3253281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3253282 {A : Type'} (P : type686 A) : (term181 A P) = (term182 A P).
Proof. exact (MK_COMB (@lem3253281 A) (@lem3253280 A P)). Qed.
Lemma lem3253287 {A : Type'} (P : type686 A) : (term182 A P) = (term181 A P).
Proof. exact (SYM (@lem3253282 A P)). Qed.
Lemma lem3253299 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term3 A a t P) = (term4 A t P a).
Proof. exact (EQ_MP (@lem3252531 A t P a) (@lem3252530 A P a t)). Qed.
Lemma lem3253300 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term3 A a t P) = (term4 A t P a).
Proof. exact (@lem3253299 A t P a). Qed.
Lemma lem3253301 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term183 A a t P) = (term184 A t P a).
Proof. exact (@lem3253300 A t (term185 A P) a). Qed.
Lemma lem3253302 {A : Type'} (P : type686 A) (s : A -> Prop) : (term186 A P s) = (term139 A P s).
Proof. exact (eq_refl (term186 A P s)). Qed.
Lemma lem3253303 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term138 A s a t) = (term138 A s a t).
Proof. exact (eq_refl (term138 A s a t)). Qed.
Lemma lem3253304 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (s : A -> Prop) : (term187 A a t P s) = (term141 A a t P s).
Proof. exact (MK_COMB (@lem3253303 A s a t) (@lem3253302 A P s)). Qed.
Lemma lem3253305 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term188 A a t P) = (term143 A a t P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253304 A a t P s)). Qed.
Lemma lem3253306 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253307 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term183 A a t P) = (term145 A a t P).
Proof. exact (MK_COMB (@lem3253306 A) (@lem3253305 A a t P)). Qed.
Lemma lem3253308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253309 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term189 A a t P) = (term190 A a t P).
Proof. exact (MK_COMB (@lem3253308) (@lem3253307 A a t P)). Qed.
Lemma lem3253310 {A : Type'} (P : type686 A) (s : A -> Prop) : (term186 A P s) = (term139 A P s).
Proof. exact (eq_refl (term186 A P s)). Qed.
Lemma lem3253311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253312 {A : Type'} (P : type686 A) (s : A -> Prop) : (term191 A P s) = (term192 A P s).
Proof. exact (MK_COMB (@lem3253311) (@lem3253310 A P s)). Qed.
Lemma lem3253313 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term193 A P a s) = (term194 A P a s).
Proof. exact (eq_refl (term193 A P a s)). Qed.
Lemma lem3253314 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term195 A P a s) = (term196 A P a s).
Proof. exact (MK_COMB (@lem3253312 A P s) (@lem3253313 A P a s)). Qed.
Lemma lem3253315 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term165 A s t) = (term165 A s t).
Proof. exact (eq_refl (term165 A s t)). Qed.
Lemma lem3253316 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term197 A t P a s) = (term198 A t P a s).
Proof. exact (MK_COMB (@lem3253315 A s t) (@lem3253314 A P a s)). Qed.
Lemma lem3253317 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term199 A t P a) = (term200 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253316 A t P a s)). Qed.
Lemma lem3253318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253319 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term184 A t P a) = (term201 A t P a).
Proof. exact (MK_COMB (@lem3253318 A) (@lem3253317 A t P a)). Qed.
Lemma lem3253320 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term183 A a t P) = (term184 A t P a)) = ((term145 A a t P) = (term201 A t P a)).
Proof. exact (MK_COMB (@lem3253309 A a t P) (@lem3253319 A t P a)). Qed.
Lemma lem3253321 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term145 A a t P) = (term201 A t P a).
Proof. exact (EQ_MP (@lem3253320 A t P a) (@lem3253301 A t P a)). Qed.
Lemma lem3253330 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253331 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term146 A a t P) = (term202 A t P a).
Proof. exact (MK_COMB (@lem3253330) (@lem3253321 A t P a)). Qed.
Lemma lem3253332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253333 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term147 A a t P) = (term203 A t P a).
Proof. exact (MK_COMB (@lem3253332) (@lem3253331 A t P a)). Qed.
Lemma lem3253342 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term174 A t P a) = (term174 A t P a).
Proof. exact (eq_refl (term174 A t P a)). Qed.
Lemma lem3253343 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term146 A a t P) = (term174 A t P a)) = ((term202 A t P a) = (term174 A t P a)).
Proof. exact (MK_COMB (@lem3253333 A t P a) (@lem3253342 A t P a)). Qed.
Lemma lem3253346 {A : Type'} (P : type686 A) (a : A) : (term176 A P a) = (term204 A P a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3253343 A t P a)). Qed.
Lemma lem3253347 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253348 {A : Type'} (P : type686 A) (a : A) : (term178 A P a) = (term205 A P a).
Proof. exact (MK_COMB (@lem3253347 A) (@lem3253346 A P a)). Qed.
Lemma lem3253353 {A : Type'} (P : type686 A) : (term180 A P) = (term206 A P).
Proof. exact (fun_ext (fun a : A => @lem3253348 A P a)). Qed.
Lemma lem3253354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3253355 {A : Type'} (P : type686 A) : (term182 A P) = (term207 A P).
Proof. exact (MK_COMB (@lem3253354 A) (@lem3253353 A P)). Qed.
Lemma lem3253360 {A : Type'} (P : type686 A) : (term207 A P) = (term182 A P).
Proof. exact (SYM (@lem3253355 A P)). Qed.
Lemma lem3253362 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3253363 {A : Type'} (P : type686 A) : (term207 A P) = (term208 A P).
Proof. exact (@lem3253362 (term207 A P)). Qed.
Lemma lem3253364 {A : Type'} (P : type686 A) : (term208 A P) = (term207 A P).
Proof. exact (SYM (@lem3253363 A P)). Qed.
Lemma lem3253365 {A : Type'} (P : type686 A) (h1 : term209 A P) : term209 A P.
Proof. exact (h1). Qed.
Lemma lem3253368 {A : Type'} (P : type686 A) (h1 : term208 A P) : term208 A P.
Proof. exact (h1). Qed.
Lemma lem3253369 {A : Type'} (P : type686 A) : term210 A P.
Proof. exact (fun h0 : term208 A P => @lem3253368 A P h0). Qed.
Lemma lem3253370 {A : Type'} (P : type686 A) (h1 : term210 A P) : term210 A P.
Proof. exact (h1). Qed.
Lemma lem3253371 {A : Type'} (P : type686 A) (h1 : term208 A P) : term208 A P.
Proof. exact (h1). Qed.
Lemma lem3253372 {A : Type'} (P : type686 A) (h1 : term208 A P) (h2 : term210 A P) : term208 A P.
Proof. exact (@lem3253370 A P h2 (@lem3253371 A P h1)). Qed.
Lemma lem3253373 {A : Type'} (P : type686 A) (h1 : term208 A P) : term211 A P.
Proof. exact (fun h0 : term210 A P => @lem3253372 A P h1 h0). Qed.
Lemma lem3253374 {A : Type'} (P : type686 A) (h1 : term210 A P) : term210 A P.
Proof. exact (h1). Qed.
Lemma lem3253375 {A : Type'} (P : type686 A) (h1 : term208 A P) (h2 : term210 A P) : term208 A P.
Proof. exact (@lem3253373 A P h1 (@lem3253374 A P h2)). Qed.
Lemma lem3253376 {A : Type'} (P : type686 A) (h1 : term210 A P) : term210 A P.
Proof. exact (fun h0 : term208 A P => @lem3253375 A P h0 h1). Qed.
Lemma lem3253377 {A : Type'} (P : type686 A) : term212 A P.
Proof. exact (fun h0 : term210 A P => @lem3253376 A P h0). Qed.
Lemma lem3253380 {A : Type'} (P : type686 A) : term210 A P.
Proof. exact (@lem3253377 A P (@lem3253369 A P)). Qed.
Lemma lem3253381 {A : Type'} (P : type686 A) : term210 A P.
Proof. exact (@lem3253380 A P). Qed.
Lemma lem3253387 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3253388 {A : Type'} (P : type686 A) : (term208 A P) = (term213 A P).
Proof. exact (@lem3253387 (term209 A P)). Qed.
Lemma lem3253390 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3253391 {A : Type'} (P : type686 A) : (term213 A P) = (term207 A P).
Proof. exact (@lem3253390 (term207 A P)). Qed.
Lemma lem3253396 {A : Type'} (P : type686 A) : (term208 A P) = (term207 A P).
Proof. exact (TRANS (@lem3253388 A P) (@lem3253391 A P)). Qed.
Lemma lem3253417 {A : Type'} : (term214 A) = (term215 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3253396 A P)). Qed.
Lemma lem3253418 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3253427 {A : Type'} : (term216 A) = (term217 A).
Proof. exact (MK_COMB (@lem3253418 A) (@lem3253417 A)). Qed.
Lemma lem3253438 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term169 A t P a s) = (term169 A t P a s).
Proof. exact (eq_refl (term169 A t P a s)). Qed.
Lemma lem3253439 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term171 A t P a) = (term171 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253438 A t P a s)). Qed.
Lemma lem3253440 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253441 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term173 A t P a) = (term173 A t P a).
Proof. exact (MK_COMB (@lem3253440 A) (@lem3253439 A t P a)). Qed.
Lemma lem3253442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253443 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term174 A t P a) = (term174 A t P a).
Proof. exact (MK_COMB (@lem3253442) (@lem3253441 A t P a)). Qed.
Lemma lem3253456 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term198 A t P a s) = (term198 A t P a s).
Proof. exact (eq_refl (term198 A t P a s)). Qed.
Lemma lem3253457 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term200 A t P a) = (term200 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253456 A t P a s)). Qed.
Lemma lem3253458 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253459 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term201 A t P a) = (term201 A t P a).
Proof. exact (MK_COMB (@lem3253458 A) (@lem3253457 A t P a)). Qed.
Lemma lem3253460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253461 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term202 A t P a) = (term202 A t P a).
Proof. exact (MK_COMB (@lem3253460) (@lem3253459 A t P a)). Qed.
Lemma lem3253462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253463 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term203 A t P a) = (term203 A t P a).
Proof. exact (MK_COMB (@lem3253462) (@lem3253461 A t P a)). Qed.
Lemma lem3253464 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term202 A t P a) = (term174 A t P a)) = ((term202 A t P a) = (term174 A t P a)).
Proof. exact (MK_COMB (@lem3253463 A t P a) (@lem3253443 A t P a)). Qed.
Lemma lem3253465 {A : Type'} (P : type686 A) (a : A) : (term204 A P a) = (term204 A P a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3253464 A t P a)). Qed.
Lemma lem3253466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253467 {A : Type'} (P : type686 A) (a : A) : (term205 A P a) = (term205 A P a).
Proof. exact (MK_COMB (@lem3253466 A) (@lem3253465 A P a)). Qed.
Lemma lem3253468 {A : Type'} (P : type686 A) : (term206 A P) = (term206 A P).
Proof. exact (fun_ext (fun a : A => @lem3253467 A P a)). Qed.
Lemma lem3253469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3253470 {A : Type'} (P : type686 A) : (term207 A P) = (term207 A P).
Proof. exact (MK_COMB (@lem3253469 A) (@lem3253468 A P)). Qed.
Lemma lem3253471 {A : Type'} : (term215 A) = (term215 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3253470 A P)). Qed.
Lemma lem3253472 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3253473 {A : Type'} : (term217 A) = (term217 A).
Proof. exact (MK_COMB (@lem3253472 A) (@lem3253471 A)). Qed.
Lemma lem3253514 {A : Type'} : (term216 A) = (term217 A).
Proof. exact (TRANS (@lem3253427 A) (@lem3253473 A)). Qed.
Lemma lem3253515 {A : Type'} : (term217 A) = (term216 A).
Proof. exact (SYM (@lem3253514 A)). Qed.
Lemma lem3253517 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3253518 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term202 A t P a) = (term174 A t P a)) = (term218 A t P a).
Proof. exact (@lem3253517 ((term202 A t P a) = (term174 A t P a))). Qed.
Lemma lem3253519 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term218 A t P a) = ((term202 A t P a) = (term174 A t P a)).
Proof. exact (SYM (@lem3253518 A t P a)). Qed.
Lemma lem3253520 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term219 A t P a) : term219 A t P a.
Proof. exact (h1). Qed.
Lemma lem3253526 {A : Type'} (P : type686 A) (s : A -> Prop) : (term220 A P s) = (P s).
Proof. exact (@lem16933 (P s)). Qed.
Lemma lem3253530 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term221 A P a s) = (term222 A P a s).
Proof. exact (@lem16933 (term222 A P a s)). Qed.
Lemma lem3253531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253532 {A : Type'} (P : type686 A) (s : A -> Prop) : (term223 A P s) = (term224 A P s).
Proof. exact (MK_COMB (@lem3253531) (@lem3253526 A P s)). Qed.
Lemma lem3253533 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term225 A P a s) = (term156 A P a s).
Proof. exact (MK_COMB (@lem3253532 A P s) (@lem3253530 A P a s)). Qed.
Lemma lem3253534 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term226 A P a s) = (term225 A P a s).
Proof. exact (@lem17045 (term139 A P s) (term194 A P a s)). Qed.
Lemma lem3253535 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term226 A P a s) = (term156 A P a s).
Proof. exact (TRANS (@lem3253534 A P a s) (@lem3253533 A P a s)). Qed.
Lemma lem3253540 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term154 A s t).
Proof. exact (eq_refl (term154 A s t)). Qed.
Lemma lem3253541 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term227 A t P a s) = (term158 A t P a s).
Proof. exact (MK_COMB (@lem3253540 A s t) (@lem3253535 A P a s)). Qed.
Lemma lem3253542 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term228 A t P a s) = (term227 A t P a s).
Proof. exact (@lem17362 (@SUBSET A s t) (term196 A P a s)). Qed.
Lemma lem3253543 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term228 A t P a s) = (term158 A t P a s).
Proof. exact (TRANS (@lem3253542 A t P a s) (@lem3253541 A t P a s)). Qed.
Lemma lem3253548 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term198 A t P a s) = (term229 A t P a s).
Proof. exact (@lem17265 (@SUBSET A s t) (term196 A P a s)). Qed.
Lemma lem3253549 {A : Type'} (P : type686 A) : (term230 A P) = (term231 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3253550 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term202 A t P a) = (term232 A t P a).
Proof. exact (@lem3253549 A (term200 A t P a)). Qed.
Lemma lem3253551 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term233 A t P a s) = (term198 A t P a s).
Proof. exact (eq_refl (term233 A t P a s)). Qed.
Lemma lem3253552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253553 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term234 A t P a s) = (term228 A t P a s).
Proof. exact (MK_COMB (@lem3253552) (@lem3253551 A t P a s)). Qed.
Lemma lem3253554 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term234 A t P a s) = (term158 A t P a s).
Proof. exact (TRANS (@lem3253553 A t P a s) (@lem3253543 A t P a s)). Qed.
Lemma lem3253555 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term235 A t P a) = (term160 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253554 A t P a s)). Qed.
Lemma lem3253556 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253557 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term232 A t P a) = (term161 A t P a).
Proof. exact (MK_COMB (@lem3253556 A) (@lem3253555 A t P a)). Qed.
Lemma lem3253558 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term202 A t P a) = (term161 A t P a).
Proof. exact (TRANS (@lem3253550 A t P a) (@lem3253557 A t P a)). Qed.
Lemma lem3253559 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term200 A t P a) = (term236 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253548 A t P a s)). Qed.
Lemma lem3253560 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253561 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term201 A t P a) = (term237 A t P a).
Proof. exact (MK_COMB (@lem3253560 A) (@lem3253559 A t P a)). Qed.
Lemma lem3253562 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term238 A t P a) = (term201 A t P a).
Proof. exact (@lem16933 (term201 A t P a)). Qed.
Lemma lem3253563 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term238 A t P a) = (term237 A t P a).
Proof. exact (TRANS (@lem3253562 A t P a) (@lem3253561 A t P a)). Qed.
Lemma lem3253574 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term167 A P a s) = (term196 A P a s).
Proof. exact (@lem17160 (P s) (term222 A P a s)). Qed.
Lemma lem3253579 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term239 A P a s) = (term156 A P a s).
Proof. exact (@lem16933 (term156 A P a s)). Qed.
Lemma lem3253581 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term154 A s t).
Proof. exact (eq_refl (term154 A s t)). Qed.
Lemma lem3253582 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term240 A t P a s) = (term158 A t P a s).
Proof. exact (MK_COMB (@lem3253581 A s t) (@lem3253579 A P a s)). Qed.
Lemma lem3253583 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term241 A t P a s) = (term240 A t P a s).
Proof. exact (@lem17362 (@SUBSET A s t) (term167 A P a s)). Qed.
Lemma lem3253584 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term241 A t P a s) = (term158 A t P a s).
Proof. exact (TRANS (@lem3253583 A t P a s) (@lem3253582 A t P a s)). Qed.
Lemma lem3253586 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term242 A s t) = (term242 A s t).
Proof. exact (eq_refl (term242 A s t)). Qed.
Lemma lem3253587 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term243 A t P a s) = (term229 A t P a s).
Proof. exact (MK_COMB (@lem3253586 A s t) (@lem3253574 A P a s)). Qed.
Lemma lem3253588 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term169 A t P a s) = (term243 A t P a s).
Proof. exact (@lem17265 (@SUBSET A s t) (term167 A P a s)). Qed.
Lemma lem3253589 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term169 A t P a s) = (term229 A t P a s).
Proof. exact (TRANS (@lem3253588 A t P a s) (@lem3253587 A t P a s)). Qed.
Lemma lem3253590 {A : Type'} (P : type686 A) : (term230 A P) = (term231 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3253591 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term174 A t P a) = (term244 A t P a).
Proof. exact (@lem3253590 A (term171 A t P a)). Qed.
Lemma lem3253592 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term245 A t P a s) = (term169 A t P a s).
Proof. exact (eq_refl (term245 A t P a s)). Qed.
Lemma lem3253593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3253594 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term246 A t P a s) = (term241 A t P a s).
Proof. exact (MK_COMB (@lem3253593) (@lem3253592 A t P a s)). Qed.
Lemma lem3253595 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term246 A t P a s) = (term158 A t P a s).
Proof. exact (TRANS (@lem3253594 A t P a s) (@lem3253584 A t P a s)). Qed.
Lemma lem3253596 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term247 A t P a) = (term160 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253595 A t P a s)). Qed.
Lemma lem3253597 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253598 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term244 A t P a) = (term161 A t P a).
Proof. exact (MK_COMB (@lem3253597 A) (@lem3253596 A t P a)). Qed.
Lemma lem3253599 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term174 A t P a) = (term161 A t P a).
Proof. exact (TRANS (@lem3253591 A t P a) (@lem3253598 A t P a)). Qed.
Lemma lem3253600 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term171 A t P a) = (term236 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253589 A t P a s)). Qed.
Lemma lem3253601 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253602 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term173 A t P a) = (term237 A t P a).
Proof. exact (MK_COMB (@lem3253601 A) (@lem3253600 A t P a)). Qed.
Lemma lem3253603 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term248 A t P a) = (term173 A t P a).
Proof. exact (@lem16933 (term173 A t P a)). Qed.
Lemma lem3253604 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term248 A t P a) = (term237 A t P a).
Proof. exact (TRANS (@lem3253603 A t P a) (@lem3253602 A t P a)). Qed.
Lemma lem3253605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253606 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term249 A t P a) = (term250 A t P a).
Proof. exact (MK_COMB (@lem3253605) (@lem3253563 A t P a)). Qed.
Lemma lem3253607 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term251 A t P a) = (term252 A t P a).
Proof. exact (MK_COMB (@lem3253606 A t P a) (@lem3253599 A t P a)). Qed.
Lemma lem3253608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253609 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term253 A t P a) = (term254 A t P a).
Proof. exact (MK_COMB (@lem3253608) (@lem3253558 A t P a)). Qed.
Lemma lem3253610 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term255 A t P a) = (term256 A t P a).
Proof. exact (MK_COMB (@lem3253609 A t P a) (@lem3253604 A t P a)). Qed.
Lemma lem3253611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253612 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term257 A t P a) = (term258 A t P a).
Proof. exact (MK_COMB (@lem3253611) (@lem3253610 A t P a)). Qed.
Lemma lem3253613 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term259 A t P a) = (term260 A t P a).
Proof. exact (MK_COMB (@lem3253612 A t P a) (@lem3253607 A t P a)). Qed.
Lemma lem3253614 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term219 A t P a) = (term259 A t P a).
Proof. exact (@lem17646 (term202 A t P a) (term174 A t P a)). Qed.
Lemma lem3253615 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term219 A t P a) = (term260 A t P a).
Proof. exact (TRANS (@lem3253614 A t P a) (@lem3253613 A t P a)). Qed.
Lemma lem3253810 {A : Type'} (P : A -> Prop) (Q : Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3253811 {A : Type'} (P : type686 A) (Q : Prop) : (term261 A P Q) = (term262 A P Q).
Proof. exact (@lem3253810 (A -> Prop) P Q). Qed.
Lemma lem3253812 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term263 A t P a) = (term264 A t P a).
Proof. exact (@lem3253811 A (term160 A t P a) (term237 A t P a)). Qed.
Lemma lem3253813 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term265 A t P a s) = (term158 A t P a s).
Proof. exact (eq_refl (term265 A t P a s)). Qed.
Lemma lem3253814 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term266 A t P a) = (term160 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253813 A t P a s)). Qed.
Lemma lem3253815 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253816 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term267 A t P a) = (term161 A t P a).
Proof. exact (MK_COMB (@lem3253815 A) (@lem3253814 A t P a)). Qed.
Lemma lem3253817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253818 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term268 A t P a) = (term254 A t P a).
Proof. exact (MK_COMB (@lem3253817) (@lem3253816 A t P a)). Qed.
Lemma lem3253819 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term237 A t P a).
Proof. exact (eq_refl (term237 A t P a)). Qed.
Lemma lem3253820 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term263 A t P a) = (term256 A t P a).
Proof. exact (MK_COMB (@lem3253818 A t P a) (@lem3253819 A t P a)). Qed.
Lemma lem3253821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253822 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term269 A t P a) = (term270 A t P a).
Proof. exact (MK_COMB (@lem3253821) (@lem3253820 A t P a)). Qed.
Lemma lem3253823 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term265 A t P a s) = (term158 A t P a s).
Proof. exact (eq_refl (term265 A t P a s)). Qed.
Lemma lem3253824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253825 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term271 A t P a s) = (term272 A t P a s).
Proof. exact (MK_COMB (@lem3253824) (@lem3253823 A t P a s)). Qed.
Lemma lem3253826 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term237 A t P a).
Proof. exact (eq_refl (term237 A t P a)). Qed.
Lemma lem3253827 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term273 A s t P a) = (term274 A s t P a).
Proof. exact (MK_COMB (@lem3253825 A t P a s) (@lem3253826 A t P a)). Qed.
Lemma lem3253828 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term275 A t P a) = (term276 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253827 A s t P a)). Qed.
Lemma lem3253829 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253830 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term264 A t P a) = (term277 A t P a).
Proof. exact (MK_COMB (@lem3253829 A) (@lem3253828 A t P a)). Qed.
Lemma lem3253831 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term263 A t P a) = (term264 A t P a)) = ((term256 A t P a) = (term277 A t P a)).
Proof. exact (MK_COMB (@lem3253822 A t P a) (@lem3253830 A t P a)). Qed.
Lemma lem3253832 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term256 A t P a) = (term277 A t P a).
Proof. exact (EQ_MP (@lem3253831 A t P a) (@lem3253812 A t P a)). Qed.
Lemma lem3253833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253834 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term258 A t P a) = (term278 A t P a).
Proof. exact (MK_COMB (@lem3253833) (@lem3253832 A t P a)). Qed.
Lemma lem3253836 {A : Type'} (P : Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3253837 {A : Type'} (P : Prop) (Q : type686 A) : (term279 A P Q) = (term280 A P Q).
Proof. exact (@lem3253836 (A -> Prop) P Q). Qed.
Lemma lem3253838 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term281 A t P a) = (term282 A t P a).
Proof. exact (@lem3253837 A (term237 A t P a) (term160 A t P a)). Qed.
Lemma lem3253839 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term265 A t P a s) = (term158 A t P a s).
Proof. exact (eq_refl (term265 A t P a s)). Qed.
Lemma lem3253840 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term266 A t P a) = (term160 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253839 A t P a s)). Qed.
Lemma lem3253841 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253842 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term267 A t P a) = (term161 A t P a).
Proof. exact (MK_COMB (@lem3253841 A) (@lem3253840 A t P a)). Qed.
Lemma lem3253843 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term250 A t P a) = (term250 A t P a).
Proof. exact (eq_refl (term250 A t P a)). Qed.
Lemma lem3253844 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term281 A t P a) = (term252 A t P a).
Proof. exact (MK_COMB (@lem3253843 A t P a) (@lem3253842 A t P a)). Qed.
Lemma lem3253845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253846 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term283 A t P a) = (term284 A t P a).
Proof. exact (MK_COMB (@lem3253845) (@lem3253844 A t P a)). Qed.
Lemma lem3253847 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term265 A t P a s) = (term158 A t P a s).
Proof. exact (eq_refl (term265 A t P a s)). Qed.
Lemma lem3253848 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term250 A t P a) = (term250 A t P a).
Proof. exact (eq_refl (term250 A t P a)). Qed.
Lemma lem3253849 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term285 A t P a s) = (term286 A t P a s).
Proof. exact (MK_COMB (@lem3253848 A t P a) (@lem3253847 A t P a s)). Qed.
Lemma lem3253850 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term287 A t P a) = (term288 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253849 A t P a s)). Qed.
Lemma lem3253851 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253852 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term282 A t P a) = (term289 A t P a).
Proof. exact (MK_COMB (@lem3253851 A) (@lem3253850 A t P a)). Qed.
Lemma lem3253853 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term281 A t P a) = (term282 A t P a)) = ((term252 A t P a) = (term289 A t P a)).
Proof. exact (MK_COMB (@lem3253846 A t P a) (@lem3253852 A t P a)). Qed.
Lemma lem3253854 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term252 A t P a) = (term289 A t P a).
Proof. exact (EQ_MP (@lem3253853 A t P a) (@lem3253838 A t P a)). Qed.
Lemma lem3253855 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term260 A t P a) = (term290 A t P a).
Proof. exact (MK_COMB (@lem3253834 A t P a) (@lem3253854 A t P a)). Qed.
Lemma lem3253857 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3253858 {A : Type'} (P : type686 A) (Q : type686 A) : (term291 A P Q) = (term292 A P Q).
Proof. exact (@lem3253857 (A -> Prop) P Q). Qed.
Lemma lem3253859 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term293 A t P a) = (term294 A t P a).
Proof. exact (@lem3253858 A (term276 A t P a) (term288 A t P a)). Qed.
Lemma lem3253860 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term295 A t P a s) = (term274 A s t P a).
Proof. exact (eq_refl (term295 A t P a s)). Qed.
Lemma lem3253861 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term296 A t P a) = (term276 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253860 A s t P a)). Qed.
Lemma lem3253862 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253863 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term297 A t P a) = (term277 A t P a).
Proof. exact (MK_COMB (@lem3253862 A) (@lem3253861 A t P a)). Qed.
Lemma lem3253864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253865 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term298 A t P a) = (term278 A t P a).
Proof. exact (MK_COMB (@lem3253864) (@lem3253863 A t P a)). Qed.
Lemma lem3253866 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term299 A t P a s) = (term286 A t P a s).
Proof. exact (eq_refl (term299 A t P a s)). Qed.
Lemma lem3253867 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term300 A t P a) = (term288 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253866 A t P a s)). Qed.
Lemma lem3253868 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253869 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term301 A t P a) = (term289 A t P a).
Proof. exact (MK_COMB (@lem3253868 A) (@lem3253867 A t P a)). Qed.
Lemma lem3253870 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term293 A t P a) = (term290 A t P a).
Proof. exact (MK_COMB (@lem3253865 A t P a) (@lem3253869 A t P a)). Qed.
Lemma lem3253871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3253872 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term302 A t P a) = (term303 A t P a).
Proof. exact (MK_COMB (@lem3253871) (@lem3253870 A t P a)). Qed.
Lemma lem3253873 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term295 A t P a s) = (term274 A s t P a).
Proof. exact (eq_refl (term295 A t P a s)). Qed.
Lemma lem3253874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253875 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term304 A t P a s) = (term305 A s t P a).
Proof. exact (MK_COMB (@lem3253874) (@lem3253873 A s t P a)). Qed.
Lemma lem3253876 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term299 A t P a s) = (term286 A t P a s).
Proof. exact (eq_refl (term299 A t P a s)). Qed.
Lemma lem3253877 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term306 A t P a s) = (term307 A t P a s).
Proof. exact (MK_COMB (@lem3253875 A s t P a) (@lem3253876 A t P a s)). Qed.
Lemma lem3253878 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term308 A t P a) = (term309 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253877 A t P a s)). Qed.
Lemma lem3253879 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3253880 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term294 A t P a) = (term310 A t P a).
Proof. exact (MK_COMB (@lem3253879 A) (@lem3253878 A t P a)). Qed.
Lemma lem3253881 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term293 A t P a) = (term294 A t P a)) = ((term290 A t P a) = (term310 A t P a)).
Proof. exact (MK_COMB (@lem3253872 A t P a) (@lem3253880 A t P a)). Qed.
Lemma lem3253882 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term290 A t P a) = (term310 A t P a).
Proof. exact (EQ_MP (@lem3253881 A t P a) (@lem3253859 A t P a)). Qed.
Lemma lem3253884 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term260 A t P a) = (term310 A t P a).
Proof. exact (TRANS (@lem3253855 A t P a) (@lem3253882 A t P a)). Qed.
Lemma lem3253885 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term219 A t P a) = (term310 A t P a).
Proof. exact (TRANS (@lem3253615 A t P a) (@lem3253884 A t P a)). Qed.
Lemma lem3253886 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term219 A t P a) : term310 A t P a.
Proof. exact (EQ_MP (@lem3253885 A t P a) (@lem3253520 A t P a h1)). Qed.
Lemma lem3253887 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term307 A t P a s) : term307 A t P a s.
Proof. exact (h1). Qed.
Lemma lem3253908 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term158 A t P a s) = (term158 A t P a s).
Proof. exact (eq_refl (term158 A t P a s)). Qed.
Lemma lem3253935 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term229 A t P a s) = (term229 A t P a s).
Proof. exact (eq_refl (term229 A t P a s)). Qed.
Lemma lem3253936 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term236 A t P a) = (term236 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253935 A t P a s)). Qed.
Lemma lem3253937 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253938 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term237 A t P a).
Proof. exact (MK_COMB (@lem3253937 A) (@lem3253936 A t P a)). Qed.
Lemma lem3253939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3253940 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term250 A t P a) = (term250 A t P a).
Proof. exact (MK_COMB (@lem3253939) (@lem3253938 A t P a)). Qed.
Lemma lem3253941 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term286 A t P a s) = (term286 A t P a s).
Proof. exact (MK_COMB (@lem3253940 A t P a) (@lem3253908 A t P a s)). Qed.
Lemma lem3253968 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term229 A t P a s) = (term229 A t P a s).
Proof. exact (eq_refl (term229 A t P a s)). Qed.
Lemma lem3253969 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term236 A t P a) = (term236 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3253968 A t P a s)). Qed.
Lemma lem3253970 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3253971 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term237 A t P a).
Proof. exact (MK_COMB (@lem3253970 A) (@lem3253969 A t P a)). Qed.
Lemma lem3253994 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term272 A t P a s) = (term272 A t P a s).
Proof. exact (eq_refl (term272 A t P a s)). Qed.
Lemma lem3253995 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term274 A s t P a) = (term274 A s t P a).
Proof. exact (MK_COMB (@lem3253994 A t P a s) (@lem3253971 A t P a)). Qed.
Lemma lem3253996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3253997 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term305 A s t P a) = (term305 A s t P a).
Proof. exact (MK_COMB (@lem3253996) (@lem3253995 A s t P a)). Qed.
Lemma lem3253998 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term307 A t P a s) = (term307 A t P a s).
Proof. exact (MK_COMB (@lem3253997 A s t P a) (@lem3253941 A t P a s)). Qed.
Lemma lem3253999 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term307 A t P a s) : term307 A t P a s.
Proof. exact (EQ_MP (@lem3253998 A t P a s) (@lem3253887 A t P a s h1)). Qed.
Lemma lem3254000 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term274 A s t P a.
Proof. exact (h1). Qed.
Lemma lem3254001 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term286 A t P a s.
Proof. exact (h1). Qed.
Lemma lem3254002 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term237 A t P a.
Proof. exact (proj2 (@lem3254000 A s t P a h1)). Qed.
Lemma lem3254003 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term158 A t P a s.
Proof. exact (proj1 (@lem3254000 A s t P a h1)). Qed.
Lemma lem3254004 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term156 A P a s.
Proof. exact (proj2 (@lem3254003 A s t P a h1)). Qed.
Lemma lem3254008 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term158 A t P a s.
Proof. exact (proj2 (@lem3254001 A t P a s h1)). Qed.
Lemma lem3254009 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term237 A t P a.
Proof. exact (proj1 (@lem3254001 A t P a s h1)). Qed.
Lemma lem3254010 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term156 A P a s.
Proof. exact (proj2 (@lem3254008 A t P a s h1)). Qed.
Lemma lem3254031 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term229 A t P a s) = (term311 A t P a s).
Proof. exact (@lem19490 (term139 A P s) (term312 A s t) (term194 A P a s)). Qed.
Lemma lem3254032 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term236 A t P a) = (term313 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254031 A t P a s)). Qed.
Lemma lem3254033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254035 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term314 A t P a).
Proof. exact (MK_COMB (@lem3254033 A) (@lem3254032 A t P a)). Qed.
Lemma lem3254036 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term314 A t P a.
Proof. exact (EQ_MP (@lem3254035 A t P a) (@lem3254002 A s t P a h1)). Qed.
Lemma lem3254044 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3254062 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term229 A t P a s) = (term311 A t P a s).
Proof. exact (@lem19490 (term139 A P s) (term312 A s t) (term194 A P a s)). Qed.
Lemma lem3254063 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term236 A t P a) = (term313 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254062 A t P a s)). Qed.
Lemma lem3254064 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254066 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term314 A t P a).
Proof. exact (MK_COMB (@lem3254064 A) (@lem3254063 A t P a)). Qed.
Lemma lem3254067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term314 A t P a.
Proof. exact (EQ_MP (@lem3254066 A t P a) (@lem3254002 A s t P a h1)). Qed.
Lemma lem3254075 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (h1). Qed.
Lemma lem3254093 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term229 A t P a s) = (term311 A t P a s).
Proof. exact (@lem19490 (term139 A P s) (term312 A s t) (term194 A P a s)). Qed.
Lemma lem3254094 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term236 A t P a) = (term313 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254093 A t P a s)). Qed.
Lemma lem3254095 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254097 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term314 A t P a).
Proof. exact (MK_COMB (@lem3254095 A) (@lem3254094 A t P a)). Qed.
Lemma lem3254098 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term314 A t P a.
Proof. exact (EQ_MP (@lem3254097 A t P a) (@lem3254009 A t P a s h1)). Qed.
Lemma lem3254106 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3254124 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term229 A t P a s) = (term311 A t P a s).
Proof. exact (@lem19490 (term139 A P s) (term312 A s t) (term194 A P a s)). Qed.
Lemma lem3254125 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term236 A t P a) = (term313 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254124 A t P a s)). Qed.
Lemma lem3254126 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254128 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term237 A t P a) = (term314 A t P a).
Proof. exact (MK_COMB (@lem3254126 A) (@lem3254125 A t P a)). Qed.
Lemma lem3254129 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term314 A t P a.
Proof. exact (EQ_MP (@lem3254128 A t P a) (@lem3254009 A t P a s h1)). Qed.
Lemma lem3254137 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (h1). Qed.
Lemma lem3254138 {A : Type'} (_33390 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term315 A t P a _33390.
Proof. exact (@lem3254036 A s t P a h1 _33390). Qed.
Lemma lem3254139 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33390 : A -> Prop) : (term315 A t P a _33390) = (term311 A t P a _33390).
Proof. exact (eq_refl (term315 A t P a _33390)). Qed.
Lemma lem3254140 {A : Type'} (_33390 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term311 A t P a _33390.
Proof. exact (EQ_MP (@lem3254139 A t P a _33390) (@lem3254138 A _33390 s t P a h1)). Qed.
Lemma lem3254141 {A : Type'} (_33391 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term315 A t P a _33391.
Proof. exact (@lem3254067 A s t P a h1 _33391). Qed.
Lemma lem3254142 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33391 : A -> Prop) : (term315 A t P a _33391) = (term311 A t P a _33391).
Proof. exact (eq_refl (term315 A t P a _33391)). Qed.
Lemma lem3254143 {A : Type'} (_33391 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term311 A t P a _33391.
Proof. exact (EQ_MP (@lem3254142 A t P a _33391) (@lem3254141 A _33391 s t P a h1)). Qed.
Lemma lem3254144 {A : Type'} (_33392 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term315 A t P a _33392.
Proof. exact (@lem3254098 A t P a s h1 _33392). Qed.
Lemma lem3254145 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33392 : A -> Prop) : (term315 A t P a _33392) = (term311 A t P a _33392).
Proof. exact (eq_refl (term315 A t P a _33392)). Qed.
Lemma lem3254146 {A : Type'} (_33392 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term311 A t P a _33392.
Proof. exact (EQ_MP (@lem3254145 A t P a _33392) (@lem3254144 A _33392 t P a s h1)). Qed.
Lemma lem3254147 {A : Type'} (_33393 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term315 A t P a _33393.
Proof. exact (@lem3254129 A t P a s h1 _33393). Qed.
Lemma lem3254148 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33393 : A -> Prop) : (term315 A t P a _33393) = (term311 A t P a _33393).
Proof. exact (eq_refl (term315 A t P a _33393)). Qed.
Lemma lem3254149 {A : Type'} (_33393 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term311 A t P a _33393.
Proof. exact (EQ_MP (@lem3254148 A t P a _33393) (@lem3254147 A _33393 t P a s h1)). Qed.
Lemma lem3254161 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3254167 {A : Type'} (_33390 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term316 A t P _33390.
Proof. exact (proj1 (@lem3254140 A _33390 s t P a h1)). Qed.
Lemma lem3254177 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (h1). Qed.
Lemma lem3254189 {A : Type'} (_33391 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term317 A t P a _33391.
Proof. exact (proj2 (@lem3254143 A _33391 s t P a h1)). Qed.
Lemma lem3254193 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3254199 {A : Type'} (_33392 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term316 A t P _33392.
Proof. exact (proj1 (@lem3254146 A _33392 t P a s h1)). Qed.
Lemma lem3254209 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (h1). Qed.
Lemma lem3254221 {A : Type'} (_33393 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term317 A t P a _33393.
Proof. exact (proj2 (@lem3254149 A _33393 t P a s h1)). Qed.
Lemma lem3254223 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : @SUBSET A s t.
Proof. exact (proj1 (@lem3254003 A s t P a h1)). Qed.
Lemma lem3254224 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term318 A s t.
Proof. exact (fun h0 : term312 A s t => @lem3254223 A s t P a h1). Qed.
Lemma lem3254226 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (@SUBSET A s t).
Proof. exact (@lem3254226 (@SUBSET A s t)). Qed.
Lemma lem3254228 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3254227 A s t) (@lem3254224 A s t P a h1)). Qed.
Lemma lem3254230 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3254231 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : term319 A P s.
Proof. exact (fun h0 : term139 A P s => @lem3254230 A P s h1). Qed.
Lemma lem3254233 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254234 {A : Type'} (P : type686 A) (s : A -> Prop) : (term319 A P s) = (P s).
Proof. exact (@lem3254233 (P s)). Qed.
Lemma lem3254235 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (EQ_MP (@lem3254234 A P s) (@lem3254231 A P s h1)). Qed.
Lemma lem3254237 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3254238 {A : Type'} (t : A -> Prop) (P : type686 A) (_33390 : A -> Prop) : (term316 A t P _33390) = (term320 A t P _33390).
Proof. exact (@lem3254237 (@SUBSET A _33390 t) (P _33390)). Qed.
Lemma lem3254240 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3254241 {A : Type'} (t : A -> Prop) (P : type686 A) (_33390 : A -> Prop) : (term320 A t P _33390) = (term321 A t P _33390).
Proof. exact (@lem3254240 (term322 A t P _33390)). Qed.
Lemma lem3254242 {A : Type'} (t : A -> Prop) (P : type686 A) (_33390 : A -> Prop) : (term316 A t P _33390) = (term321 A t P _33390).
Proof. exact (TRANS (@lem3254238 A t P _33390) (@lem3254241 A t P _33390)). Qed.
Lemma lem3254244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : term322 A t P s.
Proof. exact (conj (@lem3254228 A s t P a h2) (@lem3254235 A P s h1)). Qed.
Lemma lem3254246 {A : Type'} (_33390 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term321 A t P _33390.
Proof. exact (EQ_MP (@lem3254242 A t P _33390) (@lem3254167 A _33390 s t P a h1)). Qed.
Lemma lem3254247 {A : Type'} (_33390 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term321 A t P _33390.
Proof. exact (@lem3254246 A _33390 s t P a h1). Qed.
Lemma lem3254248 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term321 A t P s.
Proof. exact (@lem3254247 A s s t P a h1). Qed.
Lemma lem3254251 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : False.
Proof. exact (@lem3254248 A s t P a h2 (@lem3254244 A s t P a h1 h2)). Qed.
Lemma lem3254252 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : term118.
Proof. exact (fun h0 : ~ False => @lem3254251 A s t P a h1 h2). Qed.
Lemma lem3254254 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254255 : term118 = False.
Proof. exact (@lem3254254 False). Qed.
Lemma lem3254256 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254255) (@lem3254252 A s t P a h1 h2)). Qed.
Lemma lem3254258 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : @SUBSET A s t.
Proof. exact (proj1 (@lem3254003 A s t P a h1)). Qed.
Lemma lem3254259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term318 A s t.
Proof. exact (fun h0 : term312 A s t => @lem3254258 A s t P a h1). Qed.
Lemma lem3254261 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254262 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (@SUBSET A s t).
Proof. exact (@lem3254261 (@SUBSET A s t)). Qed.
Lemma lem3254263 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3254262 A s t) (@lem3254259 A s t P a h1)). Qed.
Lemma lem3254265 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (h1). Qed.
Lemma lem3254266 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term323 A P a s.
Proof. exact (fun h0 : term194 A P a s => @lem3254265 A P a s h1). Qed.
Lemma lem3254268 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254269 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term323 A P a s) = (term222 A P a s).
Proof. exact (@lem3254268 (term222 A P a s)). Qed.
Lemma lem3254270 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (EQ_MP (@lem3254269 A P a s) (@lem3254266 A P a s h1)). Qed.
Lemma lem3254272 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3254273 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33391 : A -> Prop) : (term317 A t P a _33391) = (term324 A t P a _33391).
Proof. exact (@lem3254272 (@SUBSET A _33391 t) (term222 A P a _33391)). Qed.
Lemma lem3254275 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3254276 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33391 : A -> Prop) : (term324 A t P a _33391) = (term325 A t P a _33391).
Proof. exact (@lem3254275 (term326 A t P a _33391)). Qed.
Lemma lem3254277 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33391 : A -> Prop) : (term317 A t P a _33391) = (term325 A t P a _33391).
Proof. exact (TRANS (@lem3254273 A t P a _33391) (@lem3254276 A t P a _33391)). Qed.
Lemma lem3254279 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : term326 A t P a s.
Proof. exact (conj (@lem3254263 A s t P a h2) (@lem3254270 A P a s h1)). Qed.
Lemma lem3254281 {A : Type'} (_33391 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term325 A t P a _33391.
Proof. exact (EQ_MP (@lem3254277 A t P a _33391) (@lem3254189 A _33391 s t P a h1)). Qed.
Lemma lem3254282 {A : Type'} (_33391 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term325 A t P a _33391.
Proof. exact (@lem3254281 A _33391 s t P a h1). Qed.
Lemma lem3254283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : term325 A t P a s.
Proof. exact (@lem3254282 A s s t P a h1). Qed.
Lemma lem3254286 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : False.
Proof. exact (@lem3254283 A s t P a h2 (@lem3254279 A s t P a h1 h2)). Qed.
Lemma lem3254287 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : term118.
Proof. exact (fun h0 : ~ False => @lem3254286 A s t P a h1 h2). Qed.
Lemma lem3254289 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254290 : term118 = False.
Proof. exact (@lem3254289 False). Qed.
Lemma lem3254291 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254290) (@lem3254287 A s t P a h1 h2)). Qed.
Lemma lem3254293 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : @SUBSET A s t.
Proof. exact (proj1 (@lem3254008 A t P a s h1)). Qed.
Lemma lem3254294 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term318 A s t.
Proof. exact (fun h0 : term312 A s t => @lem3254293 A t P a s h1). Qed.
Lemma lem3254296 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254297 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (@SUBSET A s t).
Proof. exact (@lem3254296 (@SUBSET A s t)). Qed.
Lemma lem3254298 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3254297 A s t) (@lem3254294 A t P a s h1)). Qed.
Lemma lem3254300 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3254301 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : term319 A P s.
Proof. exact (fun h0 : term139 A P s => @lem3254300 A P s h1). Qed.
Lemma lem3254303 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254304 {A : Type'} (P : type686 A) (s : A -> Prop) : (term319 A P s) = (P s).
Proof. exact (@lem3254303 (P s)). Qed.
Lemma lem3254305 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (EQ_MP (@lem3254304 A P s) (@lem3254301 A P s h1)). Qed.
Lemma lem3254307 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3254308 {A : Type'} (t : A -> Prop) (P : type686 A) (_33392 : A -> Prop) : (term316 A t P _33392) = (term320 A t P _33392).
Proof. exact (@lem3254307 (@SUBSET A _33392 t) (P _33392)). Qed.
Lemma lem3254310 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3254311 {A : Type'} (t : A -> Prop) (P : type686 A) (_33392 : A -> Prop) : (term320 A t P _33392) = (term321 A t P _33392).
Proof. exact (@lem3254310 (term322 A t P _33392)). Qed.
Lemma lem3254312 {A : Type'} (t : A -> Prop) (P : type686 A) (_33392 : A -> Prop) : (term316 A t P _33392) = (term321 A t P _33392).
Proof. exact (TRANS (@lem3254308 A t P _33392) (@lem3254311 A t P _33392)). Qed.
Lemma lem3254314 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : term322 A t P s.
Proof. exact (conj (@lem3254298 A t P a s h2) (@lem3254305 A P s h1)). Qed.
Lemma lem3254316 {A : Type'} (_33392 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term321 A t P _33392.
Proof. exact (EQ_MP (@lem3254312 A t P _33392) (@lem3254199 A _33392 t P a s h1)). Qed.
Lemma lem3254317 {A : Type'} (_33392 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term321 A t P _33392.
Proof. exact (@lem3254316 A _33392 t P a s h1). Qed.
Lemma lem3254318 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term321 A t P s.
Proof. exact (@lem3254317 A s t P a s h1). Qed.
Lemma lem3254321 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : False.
Proof. exact (@lem3254318 A t P a s h2 (@lem3254314 A t P a s h1 h2)). Qed.
Lemma lem3254322 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : term118.
Proof. exact (fun h0 : ~ False => @lem3254321 A t P a s h1 h2). Qed.
Lemma lem3254324 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254325 : term118 = False.
Proof. exact (@lem3254324 False). Qed.
Lemma lem3254326 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254325) (@lem3254322 A t P a s h1 h2)). Qed.
Lemma lem3254328 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : @SUBSET A s t.
Proof. exact (proj1 (@lem3254008 A t P a s h1)). Qed.
Lemma lem3254329 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term318 A s t.
Proof. exact (fun h0 : term312 A s t => @lem3254328 A t P a s h1). Qed.
Lemma lem3254331 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254332 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (@SUBSET A s t).
Proof. exact (@lem3254331 (@SUBSET A s t)). Qed.
Lemma lem3254333 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3254332 A s t) (@lem3254329 A t P a s h1)). Qed.
Lemma lem3254335 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (h1). Qed.
Lemma lem3254336 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term323 A P a s.
Proof. exact (fun h0 : term194 A P a s => @lem3254335 A P a s h1). Qed.
Lemma lem3254338 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254339 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term323 A P a s) = (term222 A P a s).
Proof. exact (@lem3254338 (term222 A P a s)). Qed.
Lemma lem3254340 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) : term222 A P a s.
Proof. exact (EQ_MP (@lem3254339 A P a s) (@lem3254336 A P a s h1)). Qed.
Lemma lem3254342 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3254343 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33393 : A -> Prop) : (term317 A t P a _33393) = (term324 A t P a _33393).
Proof. exact (@lem3254342 (@SUBSET A _33393 t) (term222 A P a _33393)). Qed.
Lemma lem3254345 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3254346 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33393 : A -> Prop) : (term324 A t P a _33393) = (term325 A t P a _33393).
Proof. exact (@lem3254345 (term326 A t P a _33393)). Qed.
Lemma lem3254347 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33393 : A -> Prop) : (term317 A t P a _33393) = (term325 A t P a _33393).
Proof. exact (TRANS (@lem3254343 A t P a _33393) (@lem3254346 A t P a _33393)). Qed.
Lemma lem3254349 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : term326 A t P a s.
Proof. exact (conj (@lem3254333 A t P a s h2) (@lem3254340 A P a s h1)). Qed.
Lemma lem3254351 {A : Type'} (_33393 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term325 A t P a _33393.
Proof. exact (EQ_MP (@lem3254347 A t P a _33393) (@lem3254221 A _33393 t P a s h1)). Qed.
Lemma lem3254352 {A : Type'} (_33393 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term325 A t P a _33393.
Proof. exact (@lem3254351 A _33393 t P a s h1). Qed.
Lemma lem3254353 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : term325 A t P a s.
Proof. exact (@lem3254352 A s t P a s h1). Qed.
Lemma lem3254356 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : False.
Proof. exact (@lem3254353 A t P a s h2 (@lem3254349 A t P a s h1 h2)). Qed.
Lemma lem3254357 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : term118.
Proof. exact (fun h0 : ~ False => @lem3254356 A t P a s h1 h2). Qed.
Lemma lem3254359 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3254360 : term118 = False.
Proof. exact (@lem3254359 False). Qed.
Lemma lem3254361 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254360) (@lem3254357 A t P a s h1 h2)). Qed.
Lemma lem3254362 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : (term222 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term222 A P a s => @lem3254361 A t P a s h1 h2) (fun h3 : False => @lem3254209 A P a s h1)). Qed.
Lemma lem3254363 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254362 A t P a s h1 h2) (@lem3254209 A P a s h1)). Qed.
Lemma lem3254364 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : (P s) = False.
Proof. exact (prop_ext (fun h3 : P s => @lem3254326 A t P a s h1 h2) (fun h3 : False => @lem3254193 A P s h1)). Qed.
Lemma lem3254365 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254364 A t P a s h1 h2) (@lem3254193 A P s h1)). Qed.
Lemma lem3254366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : (term222 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term222 A P a s => @lem3254291 A s t P a h1 h2) (fun h3 : False => @lem3254177 A P a s h1)). Qed.
Lemma lem3254367 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254366 A s t P a h1 h2) (@lem3254177 A P a s h1)). Qed.
Lemma lem3254368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : (P s) = False.
Proof. exact (prop_ext (fun h3 : P s => @lem3254256 A s t P a h1 h2) (fun h3 : False => @lem3254161 A P s h1)). Qed.
Lemma lem3254369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254368 A s t P a h1 h2) (@lem3254161 A P s h1)). Qed.
Lemma lem3254370 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : (term222 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term222 A P a s => @lem3254363 A t P a s h1 h2) (fun h3 : False => @lem3254137 A P a s h1)). Qed.
Lemma lem3254371 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254370 A t P a s h1 h2) (@lem3254137 A P a s h1)). Qed.
Lemma lem3254372 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : (P s) = False.
Proof. exact (prop_ext (fun h3 : P s => @lem3254365 A t P a s h1 h2) (fun h3 : False => @lem3254106 A P s h1)). Qed.
Lemma lem3254373 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254372 A t P a s h1 h2) (@lem3254106 A P s h1)). Qed.
Lemma lem3254374 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : (term222 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term222 A P a s => @lem3254367 A s t P a h1 h2) (fun h3 : False => @lem3254075 A P a s h1)). Qed.
Lemma lem3254375 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254374 A s t P a h1 h2) (@lem3254075 A P a s h1)). Qed.
Lemma lem3254376 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : (P s) = False.
Proof. exact (prop_ext (fun h3 : P s => @lem3254369 A s t P a h1 h2) (fun h3 : False => @lem3254044 A P s h1)). Qed.
Lemma lem3254377 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254376 A s t P a h1 h2) (@lem3254044 A P s h1)). Qed.
Lemma lem3254378 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : (term222 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term222 A P a s => @lem3254371 A t P a s h1 h2) (fun h3 : False => @lem3254137 A P a s h1)). Qed.
Lemma lem3254379 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term222 A P a s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254378 A t P a s h1 h2) (@lem3254137 A P a s h1)). Qed.
Lemma lem3254380 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : (P s) = False.
Proof. exact (prop_ext (fun h3 : P s => @lem3254373 A t P a s h1 h2) (fun h3 : False => @lem3254106 A P s h1)). Qed.
Lemma lem3254381 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : P s) (h2 : term286 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254380 A t P a s h1 h2) (@lem3254106 A P s h1)). Qed.
Lemma lem3254382 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : (term222 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term222 A P a s => @lem3254375 A s t P a h1 h2) (fun h3 : False => @lem3254075 A P a s h1)). Qed.
Lemma lem3254383 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term222 A P a s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254382 A s t P a h1 h2) (@lem3254075 A P a s h1)). Qed.
Lemma lem3254384 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : (P s) = False.
Proof. exact (prop_ext (fun h3 : P s => @lem3254377 A s t P a h1 h2) (fun h3 : False => @lem3254044 A P s h1)). Qed.
Lemma lem3254385 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : P s) (h2 : term274 A s t P a) : False.
Proof. exact (EQ_MP (@lem3254384 A s t P a h1 h2) (@lem3254044 A P s h1)). Qed.
Lemma lem3254386 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term286 A t P a s) : False.
Proof. exact (or_elim (@lem3254010 A t P a s h1) (fun h0 : P s => @lem3254381 A t P a s h0 h1) (fun h0 : term222 A P a s => @lem3254379 A t P a s h0 h1)). Qed.
Lemma lem3254387 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term274 A s t P a) : False.
Proof. exact (or_elim (@lem3254004 A s t P a h1) (fun h0 : P s => @lem3254385 A s t P a h0 h1) (fun h0 : term222 A P a s => @lem3254383 A s t P a h0 h1)). Qed.
Lemma lem3254388 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term307 A t P a s) : False.
Proof. exact (or_elim (@lem3253999 A t P a s h1) (fun h0 : term274 A s t P a => @lem3254387 A s t P a h0) (fun h0 : term286 A t P a s => @lem3254386 A t P a s h0)). Qed.
Lemma lem3254389 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term307 A t P a s) : (term307 A t P a s) = False.
Proof. exact (prop_ext (fun h2 : term307 A t P a s => @lem3254388 A t P a s h1) (fun h2 : False => @lem3253999 A t P a s h1)). Qed.
Lemma lem3254390 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term307 A t P a s) : False.
Proof. exact (EQ_MP (@lem3254389 A t P a s h1) (@lem3253999 A t P a s h1)). Qed.
Lemma lem3254391 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term219 A t P a) : False.
Proof. exact (ex_elim (@lem3253886 A t P a h1) (fun s : A -> Prop => fun h0 : term309 A t P a s => @lem3254390 A t P a s h0)). Qed.
Lemma lem3254392 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term219 A t P a) : (term219 A t P a) = False.
Proof. exact (prop_ext (fun h2 : term219 A t P a => @lem3254391 A t P a h1) (fun h2 : False => @lem3253520 A t P a h1)). Qed.
Lemma lem3254393 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term219 A t P a) : False.
Proof. exact (EQ_MP (@lem3254392 A t P a h1) (@lem3253520 A t P a h1)). Qed.
Lemma lem3254394 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term218 A t P a.
Proof. exact (fun h0 : term219 A t P a => @lem3254393 A t P a h0). Qed.
Lemma lem3254395 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term202 A t P a) = (term174 A t P a).
Proof. exact (EQ_MP (@lem3253519 A t P a) (@lem3254394 A t P a)). Qed.
Lemma lem3254400 {A : Type'} (P : type686 A) (a : A) : term205 A P a.
Proof. exact (fun t : A -> Prop => @lem3254395 A t P a). Qed.
Lemma lem3254405 {A : Type'} (P : type686 A) : term207 A P.
Proof. exact (fun a : A => @lem3254400 A P a). Qed.
Lemma lem3254410 {A : Type'} : term217 A.
Proof. exact (fun P : type686 A => @lem3254405 A P). Qed.
Lemma lem3254411 {A : Type'} : term216 A.
Proof. exact (EQ_MP (@lem3253515 A) (@lem3254410 A)). Qed.
Lemma lem3254412 {A : Type'} (P : type686 A) : term327 A P.
Proof. exact (@lem3254411 A P). Qed.
Lemma lem3254413 {A : Type'} (P : type686 A) : (term327 A P) = (term208 A P).
Proof. exact (eq_refl (term327 A P)). Qed.
Lemma lem3254414 {A : Type'} (P : type686 A) : term208 A P.
Proof. exact (EQ_MP (@lem3254413 A P) (@lem3254412 A P)). Qed.
Lemma lem3254416 {A : Type'} (P : type686 A) : term208 A P.
Proof. exact (@lem3253381 A P (@lem3254414 A P)). Qed.
Lemma lem3254417 {A : Type'} (P : type686 A) (h1 : term209 A P) : False.
Proof. exact (@lem3254416 A P (@lem3253365 A P h1)). Qed.
Lemma lem3254418 {A : Type'} (P : type686 A) (h1 : term209 A P) : (term209 A P) = False.
Proof. exact (prop_ext (fun h2 : term209 A P => @lem3254417 A P h1) (fun h2 : False => @lem3253365 A P h1)). Qed.
Lemma lem3254419 {A : Type'} (P : type686 A) (h1 : term209 A P) : False.
Proof. exact (EQ_MP (@lem3254418 A P h1) (@lem3253365 A P h1)). Qed.
Lemma lem3254420 {A : Type'} (P : type686 A) : term208 A P.
Proof. exact (fun h0 : term209 A P => @lem3254419 A P h0). Qed.
Lemma lem3254421 {A : Type'} (P : type686 A) : term207 A P.
Proof. exact (EQ_MP (@lem3253364 A P) (@lem3254420 A P)). Qed.
Lemma lem3254422 {A : Type'} (P : type686 A) : term182 A P.
Proof. exact (EQ_MP (@lem3253360 A P) (@lem3254421 A P)). Qed.
Lemma lem3254423 {A : Type'} (P : type686 A) : term181 A P.
Proof. exact (EQ_MP (@lem3253287 A P) (@lem3254422 A P)). Qed.
