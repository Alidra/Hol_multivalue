Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_CARD_EQ_term_abbrevs.
Require Import CARD_SUBSET_spec.
Require Import CARD_SUBSET_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LE_ANTISYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem3904519 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3904520 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3904521 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3904520 t1) (@lem3904519 t1)). Qed.
Lemma lem3904522 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3904521 t1 t2). Qed.
Lemma lem3904523 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3904524 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3904523 t1 t2) (@lem3904522 t1 t2)). Qed.
Lemma lem3904525 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3904524 t1 t2 t3). Qed.
Lemma lem3904526 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3904527 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3904526 t1 t2 t3) (@lem3904525 t1 t2 t3)). Qed.
Lemma lem3904528 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3904527 t1 t2 t3)). Qed.
Lemma lem3904530 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3904531 {_100810 : Type'} : (term8 _100810) = (term9 _100810).
Proof. exact (@lem3904530 (term8 _100810)). Qed.
Lemma lem3904532 {_100810 : Type'} : (term9 _100810) = (term8 _100810).
Proof. exact (SYM (@lem3904531 _100810)). Qed.
Lemma lem3904533 {_100810 : Type'} (h1 : term10 _100810) : term10 _100810.
Proof. exact (h1). Qed.
Lemma lem3904534 {_100810 : Type'} : term11 _100810.
Proof. exact (@lem3900203 _100810). Qed.
Lemma lem3904538 {_100810 : Type'} : term12 _100810.
Proof. exact (@lem3902682 _100810). Qed.
Lemma lem3904539 {A : Type'} : term12 A.
Proof. exact (@lem3902682 A). Qed.
Lemma lem3904546 {_100810 A : Type'} (h1 : term13 _100810 A) : term13 _100810 A.
Proof. exact (h1). Qed.
Lemma lem3904547 {_100810 A : Type'} : term14 _100810 A.
Proof. exact (fun h0 : term13 _100810 A => @lem3904546 _100810 A h0). Qed.
Lemma lem3904548 {_100810 A : Type'} (h1 : term14 _100810 A) : term14 _100810 A.
Proof. exact (h1). Qed.
Lemma lem3904549 {_100810 A : Type'} (h1 : term13 _100810 A) : term13 _100810 A.
Proof. exact (h1). Qed.
Lemma lem3904550 {_100810 A : Type'} (h1 : term13 _100810 A) (h2 : term14 _100810 A) : term13 _100810 A.
Proof. exact (@lem3904548 _100810 A h2 (@lem3904549 _100810 A h1)). Qed.
Lemma lem3904551 {_100810 A : Type'} (h1 : term13 _100810 A) : term15 _100810 A.
Proof. exact (fun h0 : term14 _100810 A => @lem3904550 _100810 A h1 h0). Qed.
Lemma lem3904552 {_100810 A : Type'} (h1 : term14 _100810 A) : term14 _100810 A.
Proof. exact (h1). Qed.
Lemma lem3904553 {_100810 A : Type'} (h1 : term13 _100810 A) (h2 : term14 _100810 A) : term13 _100810 A.
Proof. exact (@lem3904551 _100810 A h1 (@lem3904552 _100810 A h2)). Qed.
Lemma lem3904554 {_100810 A : Type'} (h1 : term14 _100810 A) : term14 _100810 A.
Proof. exact (fun h0 : term13 _100810 A => @lem3904553 _100810 A h0 h1). Qed.
Lemma lem3904555 {_100810 A : Type'} : term16 _100810 A.
Proof. exact (fun h0 : term14 _100810 A => @lem3904554 _100810 A h0). Qed.
Lemma lem3904558 {_100810 A : Type'} : term14 _100810 A.
Proof. exact (@lem3904555 _100810 A (@lem3904547 _100810 A)). Qed.
Lemma lem3904559 {_100810 A : Type'} : term14 _100810 A.
Proof. exact (@lem3904558 _100810 A). Qed.
Lemma lem3904631 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3904632 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem3904631 (term11 A)). Qed.
Lemma lem3904647 {_100810 : Type'} : (term19 _100810) = (term19 _100810).
Proof. exact (eq_refl (term19 _100810)). Qed.
Lemma lem3904648 {_100810 A : Type'} : (term20 _100810 A) = (term21 _100810 A).
Proof. exact (MK_COMB (@lem3904647 _100810) (@lem3904632 A)). Qed.
Lemma lem3904651 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem3904652 {_100810 A : Type'} : (term23 _100810 A) = (term24 _100810 A).
Proof. exact (MK_COMB (@lem3904651) (@lem3904648 _100810 A)). Qed.
Lemma lem3904655 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem3904656 {_100810 A : Type'} : (term26 _100810 A) = (term27 _100810 A).
Proof. exact (MK_COMB (@lem3904655 A) (@lem3904652 _100810 A)). Qed.
Lemma lem3904659 {_100810 : Type'} : (term25 _100810) = (term25 _100810).
Proof. exact (eq_refl (term25 _100810)). Qed.
Lemma lem3904660 {_100810 A : Type'} : (term28 _100810 A) = (term29 _100810 A).
Proof. exact (MK_COMB (@lem3904659 _100810) (@lem3904656 _100810 A)). Qed.
Lemma lem3904663 {_100810 : Type'} : (term30 _100810) = (term30 _100810).
Proof. exact (eq_refl (term30 _100810)). Qed.
Lemma lem3904670 {_100810 A : Type'} : (term13 _100810 A) = (term31 _100810 A).
Proof. exact (MK_COMB (@lem3904663 _100810) (@lem3904660 _100810 A)). Qed.
Lemma lem3904683 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term32 A a b) = (term32 A a b).
Proof. exact (eq_refl (term32 A a b)). Qed.
Lemma lem3904684 {A : Type'} (a : A -> Prop) : (term33 A a) = (term33 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3904683 A a b)). Qed.
Lemma lem3904685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3904686 {A : Type'} (a : A -> Prop) : (term34 A a) = (term34 A a).
Proof. exact (MK_COMB (@lem3904685 A) (@lem3904684 A a)). Qed.
Lemma lem3904687 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3904686 A a)). Qed.
Lemma lem3904688 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3904689 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3904688 A) (@lem3904687 A)). Qed.
Lemma lem3904690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3904691 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem3904690) (@lem3904689 A)). Qed.
Lemma lem3904704 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term32 _100810 a b) = (term32 _100810 a b).
Proof. exact (eq_refl (term32 _100810 a b)). Qed.
Lemma lem3904705 {_100810 : Type'} (a : _100810 -> Prop) : (term33 _100810 a) = (term33 _100810 a).
Proof. exact (fun_ext (fun b : _100810 -> Prop => @lem3904704 _100810 a b)). Qed.
Lemma lem3904706 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3904707 {_100810 : Type'} (a : _100810 -> Prop) : (term34 _100810 a) = (term34 _100810 a).
Proof. exact (MK_COMB (@lem3904706 _100810) (@lem3904705 _100810 a)). Qed.
Lemma lem3904708 {_100810 : Type'} : (term35 _100810) = (term35 _100810).
Proof. exact (fun_ext (fun a : _100810 -> Prop => @lem3904707 _100810 a)). Qed.
Lemma lem3904709 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3904710 {_100810 : Type'} : (term11 _100810) = (term11 _100810).
Proof. exact (MK_COMB (@lem3904709 _100810) (@lem3904708 _100810)). Qed.
Lemma lem3904711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904712 {_100810 : Type'} : (term19 _100810) = (term19 _100810).
Proof. exact (MK_COMB (@lem3904711) (@lem3904710 _100810)). Qed.
Lemma lem3904713 {_100810 A : Type'} : (term21 _100810 A) = (term21 _100810 A).
Proof. exact (MK_COMB (@lem3904712 _100810) (@lem3904691 A)). Qed.
Lemma lem3904722 (m : nat) (n : nat) : ((term36 n m) = (m = n)) = ((term36 n m) = (m = n)).
Proof. exact (eq_refl ((term36 n m) = (m = n))). Qed.
Lemma lem3904723 (m : nat) : (term37 m) = (term37 m).
Proof. exact (fun_ext (fun n : nat => @lem3904722 m n)). Qed.
Lemma lem3904724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3904725 (m : nat) : (term38 m) = (term38 m).
Proof. exact (MK_COMB (@lem3904724) (@lem3904723 m)). Qed.
Lemma lem3904726 : term39 = term39.
Proof. exact (fun_ext (fun m : nat => @lem3904725 m)). Qed.
Lemma lem3904727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3904728 : term40 = term40.
Proof. exact (MK_COMB (@lem3904727) (@lem3904726)). Qed.
Lemma lem3904729 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904730 : term22 = term22.
Proof. exact (MK_COMB (@lem3904729) (@lem3904728)). Qed.
Lemma lem3904731 {_100810 A : Type'} : (term24 _100810 A) = (term24 _100810 A).
Proof. exact (MK_COMB (@lem3904730) (@lem3904713 _100810 A)). Qed.
Lemma lem3904740 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term41 A a b) = (term41 A a b).
Proof. exact (eq_refl (term41 A a b)). Qed.
Lemma lem3904741 {A : Type'} (a : A -> Prop) : (term42 A a) = (term42 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3904740 A a b)). Qed.
Lemma lem3904742 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3904743 {A : Type'} (a : A -> Prop) : (term43 A a) = (term43 A a).
Proof. exact (MK_COMB (@lem3904742 A) (@lem3904741 A a)). Qed.
Lemma lem3904744 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3904743 A a)). Qed.
Lemma lem3904745 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3904746 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3904745 A) (@lem3904744 A)). Qed.
Lemma lem3904747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904748 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3904747) (@lem3904746 A)). Qed.
Lemma lem3904749 {_100810 A : Type'} : (term27 _100810 A) = (term27 _100810 A).
Proof. exact (MK_COMB (@lem3904748 A) (@lem3904731 _100810 A)). Qed.
Lemma lem3904758 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term41 _100810 a b) = (term41 _100810 a b).
Proof. exact (eq_refl (term41 _100810 a b)). Qed.
Lemma lem3904759 {_100810 : Type'} (a : _100810 -> Prop) : (term42 _100810 a) = (term42 _100810 a).
Proof. exact (fun_ext (fun b : _100810 -> Prop => @lem3904758 _100810 a b)). Qed.
Lemma lem3904760 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3904761 {_100810 : Type'} (a : _100810 -> Prop) : (term43 _100810 a) = (term43 _100810 a).
Proof. exact (MK_COMB (@lem3904760 _100810) (@lem3904759 _100810 a)). Qed.
Lemma lem3904762 {_100810 : Type'} : (term44 _100810) = (term44 _100810).
Proof. exact (fun_ext (fun a : _100810 -> Prop => @lem3904761 _100810 a)). Qed.
Lemma lem3904763 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3904764 {_100810 : Type'} : (term12 _100810) = (term12 _100810).
Proof. exact (MK_COMB (@lem3904763 _100810) (@lem3904762 _100810)). Qed.
Lemma lem3904765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904766 {_100810 : Type'} : (term25 _100810) = (term25 _100810).
Proof. exact (MK_COMB (@lem3904765) (@lem3904764 _100810)). Qed.
Lemma lem3904767 {_100810 A : Type'} : (term29 _100810 A) = (term29 _100810 A).
Proof. exact (MK_COMB (@lem3904766 _100810) (@lem3904749 _100810 A)). Qed.
Lemma lem3904780 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term45 _100810 s t) = (term45 _100810 s t).
Proof. exact (eq_refl (term45 _100810 s t)). Qed.
Lemma lem3904781 {_100810 : Type'} (s : _100810 -> Prop) : (term46 _100810 s) = (term46 _100810 s).
Proof. exact (fun_ext (fun t : _100810 -> Prop => @lem3904780 _100810 s t)). Qed.
Lemma lem3904782 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3904783 {_100810 : Type'} (s : _100810 -> Prop) : (term47 _100810 s) = (term47 _100810 s).
Proof. exact (MK_COMB (@lem3904782 _100810) (@lem3904781 _100810 s)). Qed.
Lemma lem3904784 {_100810 : Type'} : (term48 _100810) = (term48 _100810).
Proof. exact (fun_ext (fun s : _100810 -> Prop => @lem3904783 _100810 s)). Qed.
Lemma lem3904785 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3904786 {_100810 : Type'} : (term8 _100810) = (term8 _100810).
Proof. exact (MK_COMB (@lem3904785 _100810) (@lem3904784 _100810)). Qed.
Lemma lem3904787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3904788 {_100810 : Type'} : (term10 _100810) = (term10 _100810).
Proof. exact (MK_COMB (@lem3904787) (@lem3904786 _100810)). Qed.
Lemma lem3904789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904790 {_100810 : Type'} : (term30 _100810) = (term30 _100810).
Proof. exact (MK_COMB (@lem3904789) (@lem3904788 _100810)). Qed.
Lemma lem3904791 {_100810 A : Type'} : (term31 _100810 A) = (term31 _100810 A).
Proof. exact (MK_COMB (@lem3904790 _100810) (@lem3904767 _100810 A)). Qed.
Lemma lem3904902 {_100810 A : Type'} : (term13 _100810 A) = (term31 _100810 A).
Proof. exact (TRANS (@lem3904670 _100810 A) (@lem3904791 _100810 A)). Qed.
Lemma lem3904903 {_100810 A : Type'} : (term31 _100810 A) = (term13 _100810 A).
Proof. exact (SYM (@lem3904902 _100810 A)). Qed.
Lemma lem3904904 {_100810 : Type'} (h1 : term10 _100810) : term10 _100810.
Proof. exact (h1). Qed.
Lemma lem3904908 {_100810 : Type'} (h1 : term11 _100810) : term11 _100810.
Proof. exact (h1). Qed.
Lemma lem3904929 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term49 _100810 s t) = (term50 _100810 s t).
Proof. exact (@lem17646 ((@CARD _100810 s) = (@CARD _100810 t)) (s = t)). Qed.
Lemma lem3904931 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term51 _100810 s t) = (term51 _100810 s t).
Proof. exact (eq_refl (term51 _100810 s t)). Qed.
Lemma lem3904932 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term52 _100810 s t) = (term53 _100810 s t).
Proof. exact (MK_COMB (@lem3904931 _100810 s t) (@lem3904929 _100810 s t)). Qed.
Lemma lem3904933 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term54 _100810 s t) = (term52 _100810 s t).
Proof. exact (@lem17362 (term55 _100810 s t) (((@CARD _100810 s) = (@CARD _100810 t)) = (s = t))). Qed.
Lemma lem3904934 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term54 _100810 s t) = (term53 _100810 s t).
Proof. exact (TRANS (@lem3904933 _100810 s t) (@lem3904932 _100810 s t)). Qed.
Lemma lem3904935 {_100810 : Type'} (P : type686 _100810) : (term56 _100810 P) = (term57 _100810 P).
Proof. exact (@lem18392 (_100810 -> Prop) P). Qed.
Lemma lem3904936 {_100810 : Type'} (s : _100810 -> Prop) : (term58 _100810 s) = (term59 _100810 s).
Proof. exact (@lem3904935 _100810 (term46 _100810 s)). Qed.
Lemma lem3904937 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term60 _100810 s t) = (term45 _100810 s t).
Proof. exact (eq_refl (term60 _100810 s t)). Qed.
Lemma lem3904938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3904939 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term61 _100810 s t) = (term54 _100810 s t).
Proof. exact (MK_COMB (@lem3904938) (@lem3904937 _100810 s t)). Qed.
Lemma lem3904940 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term61 _100810 s t) = (term53 _100810 s t).
Proof. exact (TRANS (@lem3904939 _100810 s t) (@lem3904934 _100810 s t)). Qed.
Lemma lem3904941 {_100810 : Type'} (s : _100810 -> Prop) : (term62 _100810 s) = (term63 _100810 s).
Proof. exact (fun_ext (fun t : _100810 -> Prop => @lem3904940 _100810 s t)). Qed.
Lemma lem3904942 {_100810 : Type'} : (@ex (_100810 -> Prop)) = (@ex (_100810 -> Prop)).
Proof. exact (eq_refl (@ex (_100810 -> Prop))). Qed.
Lemma lem3904943 {_100810 : Type'} (s : _100810 -> Prop) : (term59 _100810 s) = (term64 _100810 s).
Proof. exact (MK_COMB (@lem3904942 _100810) (@lem3904941 _100810 s)). Qed.
Lemma lem3904944 {_100810 : Type'} (s : _100810 -> Prop) : (term58 _100810 s) = (term64 _100810 s).
Proof. exact (TRANS (@lem3904936 _100810 s) (@lem3904943 _100810 s)). Qed.
Lemma lem3904945 {_100810 : Type'} (P : type686 _100810) : (term56 _100810 P) = (term57 _100810 P).
Proof. exact (@lem18392 (_100810 -> Prop) P). Qed.
Lemma lem3904946 {_100810 : Type'} : (term10 _100810) = (term65 _100810).
Proof. exact (@lem3904945 _100810 (term48 _100810)). Qed.
Lemma lem3904947 {_100810 : Type'} (s : _100810 -> Prop) : (term66 _100810 s) = (term47 _100810 s).
Proof. exact (eq_refl (term66 _100810 s)). Qed.
Lemma lem3904948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3904949 {_100810 : Type'} (s : _100810 -> Prop) : (term67 _100810 s) = (term58 _100810 s).
Proof. exact (MK_COMB (@lem3904948) (@lem3904947 _100810 s)). Qed.
Lemma lem3904950 {_100810 : Type'} (s : _100810 -> Prop) : (term67 _100810 s) = (term64 _100810 s).
Proof. exact (TRANS (@lem3904949 _100810 s) (@lem3904944 _100810 s)). Qed.
Lemma lem3904951 {_100810 : Type'} : (term68 _100810) = (term69 _100810).
Proof. exact (fun_ext (fun s : _100810 -> Prop => @lem3904950 _100810 s)). Qed.
Lemma lem3904952 {_100810 : Type'} : (@ex (_100810 -> Prop)) = (@ex (_100810 -> Prop)).
Proof. exact (eq_refl (@ex (_100810 -> Prop))). Qed.
Lemma lem3904953 {_100810 : Type'} : (term65 _100810) = (term70 _100810).
Proof. exact (MK_COMB (@lem3904952 _100810) (@lem3904951 _100810)). Qed.
Lemma lem3905010 {_100810 : Type'} : (term10 _100810) = (term70 _100810).
Proof. exact (TRANS (@lem3904946 _100810) (@lem3904953 _100810)). Qed.
Lemma lem3905011 {_100810 : Type'} (h1 : term10 _100810) : term70 _100810.
Proof. exact (EQ_MP (@lem3905010 _100810) (@lem3904904 _100810 h1)). Qed.
Lemma lem3905468 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term71 _100810 a b) = (term72 _100810 a b).
Proof. exact (@lem17045 (@SUBSET _100810 a b) ((@CARD _100810 a) = (@CARD _100810 b))). Qed.
Lemma lem3905470 {_100810 : Type'} (b : _100810 -> Prop) : (term73 _100810 b) = (term73 _100810 b).
Proof. exact (eq_refl (term73 _100810 b)). Qed.
Lemma lem3905471 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term74 _100810 a b) = (term75 _100810 a b).
Proof. exact (MK_COMB (@lem3905470 _100810 b) (@lem3905468 _100810 a b)). Qed.
Lemma lem3905472 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term76 _100810 a b) = (term74 _100810 a b).
Proof. exact (@lem17045 (@FINITE _100810 b) (term77 _100810 a b)). Qed.
Lemma lem3905473 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term76 _100810 a b) = (term75 _100810 a b).
Proof. exact (TRANS (@lem3905472 _100810 a b) (@lem3905471 _100810 a b)). Qed.
Lemma lem3905474 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (a = b) = (a = b).
Proof. exact (eq_refl (a = b)). Qed.
Lemma lem3905475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3905476 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term78 _100810 a b) = (term79 _100810 a b).
Proof. exact (MK_COMB (@lem3905475) (@lem3905473 _100810 a b)). Qed.
Lemma lem3905477 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term80 _100810 a b) = (term81 _100810 a b).
Proof. exact (MK_COMB (@lem3905476 _100810 a b) (@lem3905474 _100810 a b)). Qed.
Lemma lem3905478 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term32 _100810 a b) = (term80 _100810 a b).
Proof. exact (@lem17265 (term82 _100810 a b) (a = b)). Qed.
Lemma lem3905479 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term32 _100810 a b) = (term81 _100810 a b).
Proof. exact (TRANS (@lem3905478 _100810 a b) (@lem3905477 _100810 a b)). Qed.
Lemma lem3905480 {_100810 : Type'} (a : _100810 -> Prop) : (term33 _100810 a) = (term83 _100810 a).
Proof. exact (fun_ext (fun b : _100810 -> Prop => @lem3905479 _100810 a b)). Qed.
Lemma lem3905481 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3905482 {_100810 : Type'} (a : _100810 -> Prop) : (term34 _100810 a) = (term84 _100810 a).
Proof. exact (MK_COMB (@lem3905481 _100810) (@lem3905480 _100810 a)). Qed.
Lemma lem3905483 {_100810 : Type'} : (term35 _100810) = (term85 _100810).
Proof. exact (fun_ext (fun a : _100810 -> Prop => @lem3905482 _100810 a)). Qed.
Lemma lem3905484 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3905541 {_100810 : Type'} : (term11 _100810) = (term86 _100810).
Proof. exact (MK_COMB (@lem3905484 _100810) (@lem3905483 _100810)). Qed.
Lemma lem3905542 {_100810 : Type'} (h1 : term11 _100810) : term86 _100810.
Proof. exact (EQ_MP (@lem3905541 _100810) (@lem3904908 _100810 h1)). Qed.
Lemma lem3905625 {_100810 : Type'} (s : _100810 -> Prop) (h1 : term64 _100810 s) : term64 _100810 s.
Proof. exact (h1). Qed.
Lemma lem3905795 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term81 _100810 a b) = (term81 _100810 a b).
Proof. exact (eq_refl (term81 _100810 a b)). Qed.
Lemma lem3905796 {_100810 : Type'} (a : _100810 -> Prop) : (term83 _100810 a) = (term83 _100810 a).
Proof. exact (fun_ext (fun b : _100810 -> Prop => @lem3905795 _100810 a b)). Qed.
Lemma lem3905797 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3905798 {_100810 : Type'} (a : _100810 -> Prop) : (term84 _100810 a) = (term84 _100810 a).
Proof. exact (MK_COMB (@lem3905797 _100810) (@lem3905796 _100810 a)). Qed.
Lemma lem3905799 {_100810 : Type'} : (term85 _100810) = (term85 _100810).
Proof. exact (fun_ext (fun a : _100810 -> Prop => @lem3905798 _100810 a)). Qed.
Lemma lem3905800 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3905801 {_100810 : Type'} : (term86 _100810) = (term86 _100810).
Proof. exact (MK_COMB (@lem3905800 _100810) (@lem3905799 _100810)). Qed.
Lemma lem3905802 {_100810 : Type'} (h1 : term11 _100810) : term86 _100810.
Proof. exact (EQ_MP (@lem3905801 _100810) (@lem3905542 _100810 h1)). Qed.
Lemma lem3905902 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : term53 _100810 s t.
Proof. exact (h1). Qed.
Lemma lem3905903 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : term50 _100810 s t.
Proof. exact (proj2 (@lem3905902 _100810 s t h1)). Qed.
Lemma lem3905904 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : term55 _100810 s t.
Proof. exact (proj1 (@lem3905902 _100810 s t h1)). Qed.
Lemma lem3905909 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term87 _100810 s t) : term87 _100810 s t.
Proof. exact (h1). Qed.
Lemma lem3905910 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : term88 _100810 s t.
Proof. exact (h1). Qed.
Lemma lem3905978 {_100810 : Type'} (a : _100810 -> Prop) (b : _100810 -> Prop) : (term81 _100810 a b) = (term81 _100810 a b).
Proof. exact (eq_refl (term81 _100810 a b)). Qed.
Lemma lem3905979 {_100810 : Type'} (a : _100810 -> Prop) : (term83 _100810 a) = (term83 _100810 a).
Proof. exact (fun_ext (fun b : _100810 -> Prop => @lem3905978 _100810 a b)). Qed.
Lemma lem3905980 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3905981 {_100810 : Type'} (a : _100810 -> Prop) : (term84 _100810 a) = (term84 _100810 a).
Proof. exact (MK_COMB (@lem3905980 _100810) (@lem3905979 _100810 a)). Qed.
Lemma lem3905982 {_100810 : Type'} : (term85 _100810) = (term85 _100810).
Proof. exact (fun_ext (fun a : _100810 -> Prop => @lem3905981 _100810 a)). Qed.
Lemma lem3905983 {_100810 : Type'} : (@all (_100810 -> Prop)) = (@all (_100810 -> Prop)).
Proof. exact (eq_refl (@all (_100810 -> Prop))). Qed.
Lemma lem3905985 {_100810 : Type'} : (term86 _100810) = (term86 _100810).
Proof. exact (MK_COMB (@lem3905983 _100810) (@lem3905982 _100810)). Qed.
Lemma lem3905986 {_100810 : Type'} (h1 : term11 _100810) : term86 _100810.
Proof. exact (EQ_MP (@lem3905985 _100810) (@lem3905802 _100810 h1)). Qed.
Lemma lem3906255 {_100810 : Type'} (_45340 : _100810 -> Prop) (h1 : term11 _100810) : term89 _100810 _45340.
Proof. exact (@lem3905986 _100810 h1 _45340). Qed.
Lemma lem3906256 {_100810 : Type'} (_45340 : _100810 -> Prop) : (term89 _100810 _45340) = (term84 _100810 _45340).
Proof. exact (eq_refl (term89 _100810 _45340)). Qed.
Lemma lem3906257 {_100810 : Type'} (_45340 : _100810 -> Prop) (h1 : term11 _100810) : term84 _100810 _45340.
Proof. exact (EQ_MP (@lem3906256 _100810 _45340) (@lem3906255 _100810 _45340 h1)). Qed.
Lemma lem3906258 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) (h1 : term11 _100810) : term90 _100810 _45340 _45341.
Proof. exact (@lem3906257 _100810 _45340 h1 _45341). Qed.
Lemma lem3906259 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term90 _100810 _45340 _45341) = (term81 _100810 _45340 _45341).
Proof. exact (eq_refl (term90 _100810 _45340 _45341)). Qed.
Lemma lem3906260 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) (h1 : term11 _100810) : term81 _100810 _45340 _45341.
Proof. exact (EQ_MP (@lem3906259 _100810 _45340 _45341) (@lem3906258 _100810 _45340 _45341 h1)). Qed.
Lemma lem3906346 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term81 _100810 _45340 _45341) = (term91 _100810 _45340 _45341).
Proof. exact (@lem3904528 (term92 _100810 _45341) (term72 _100810 _45340 _45341) (_45340 = _45341)). Qed.
Lemma lem3906353 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term93 _100810 _45340 _45341) = (term94 _100810 _45340 _45341).
Proof. exact (@lem3904528 (term95 _100810 _45340 _45341) (term96 _100810 _45340 _45341) (_45340 = _45341)). Qed.
Lemma lem3906354 {_100810 : Type'} (_45341 : _100810 -> Prop) : (term73 _100810 _45341) = (term73 _100810 _45341).
Proof. exact (eq_refl (term73 _100810 _45341)). Qed.
Lemma lem3906357 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term91 _100810 _45340 _45341) = (term97 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906354 _100810 _45341) (@lem3906353 _100810 _45340 _45341)). Qed.
Lemma lem3906359 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term81 _100810 _45340 _45341) = (term97 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906346 _100810 _45340 _45341) (@lem3906357 _100810 _45340 _45341)). Qed.
Lemma lem3906360 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) (h1 : term11 _100810) : term97 _100810 _45340 _45341.
Proof. exact (EQ_MP (@lem3906359 _100810 _45340 _45341) (@lem3906260 _100810 _45340 _45341 h1)). Qed.
Lemma lem3906398 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term87 _100810 s t) : term98 _100810 s t.
Proof. exact (proj2 (@lem3905909 _100810 s t h1)). Qed.
Lemma lem3906488 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : term96 _100810 s t.
Proof. exact (proj1 (@lem3905910 _100810 s t h1)). Qed.
Lemma lem3906490 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : s = t.
Proof. exact (proj2 (@lem3905910 _100810 s t h1)). Qed.
Lemma lem3906614 {_100810 : Type'} (t : _100810 -> Prop) : (term99 _100810 t) = (term99 _100810 t).
Proof. exact (eq_refl (term99 _100810 t)). Qed.
Lemma lem3906615 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : (term100 _100810 t s) = (term101 _100810 t).
Proof. exact (MK_COMB (@lem3906614 _100810 t) (@lem3906490 _100810 s t h1)). Qed.
Lemma lem3906616 {_100810 : Type'} (t : _100810 -> Prop) : (term101 _100810 t) = (term102 _100810 t).
Proof. exact (eq_refl (term101 _100810 t)). Qed.
Lemma lem3906617 {_100810 : Type'} (t : _100810 -> Prop) (s : _100810 -> Prop) : (term103 _100810 t s) = (term103 _100810 t s).
Proof. exact (eq_refl (term103 _100810 t s)). Qed.
Lemma lem3906618 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : ((term100 _100810 t s) = (term101 _100810 t)) = ((term100 _100810 t s) = (term102 _100810 t)).
Proof. exact (MK_COMB (@lem3906617 _100810 t s) (@lem3906616 _100810 t)). Qed.
Lemma lem3906619 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term100 _100810 t s) = (term96 _100810 s t).
Proof. exact (eq_refl (term100 _100810 t s)). Qed.
Lemma lem3906620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3906621 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term103 _100810 t s) = (term104 _100810 s t).
Proof. exact (MK_COMB (@lem3906620) (@lem3906619 _100810 s t)). Qed.
Lemma lem3906622 {_100810 : Type'} (t : _100810 -> Prop) : (term102 _100810 t) = (term102 _100810 t).
Proof. exact (eq_refl (term102 _100810 t)). Qed.
Lemma lem3906623 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : ((term100 _100810 t s) = (term102 _100810 t)) = ((term96 _100810 s t) = (term102 _100810 t)).
Proof. exact (MK_COMB (@lem3906621 _100810 s t) (@lem3906622 _100810 t)). Qed.
Lemma lem3906624 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : ((term100 _100810 t s) = (term101 _100810 t)) = ((term96 _100810 s t) = (term102 _100810 t)).
Proof. exact (TRANS (@lem3906618 _100810 s t) (@lem3906623 _100810 s t)). Qed.
Lemma lem3906625 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : (term96 _100810 s t) = (term102 _100810 t).
Proof. exact (EQ_MP (@lem3906624 _100810 s t) (@lem3906615 _100810 s t h1)). Qed.
Lemma lem3906626 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : term102 _100810 t.
Proof. exact (EQ_MP (@lem3906625 _100810 s t h1) (@lem3906488 _100810 s t h1)). Qed.
Lemma lem3906759 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : @FINITE _100810 t.
Proof. exact (proj1 (@lem3905904 _100810 s t h1)). Qed.
Lemma lem3906760 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : term105 _100810 t.
Proof. exact (fun h0 : term92 _100810 t => @lem3906759 _100810 s t h1). Qed.
Lemma lem3906762 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3906763 {_100810 : Type'} (t : _100810 -> Prop) : (term105 _100810 t) = (@FINITE _100810 t).
Proof. exact (@lem3906762 (@FINITE _100810 t)). Qed.
Lemma lem3906764 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : @FINITE _100810 t.
Proof. exact (EQ_MP (@lem3906763 _100810 t) (@lem3906760 _100810 s t h1)). Qed.
Lemma lem3906766 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : @SUBSET _100810 s t.
Proof. exact (proj2 (@lem3905904 _100810 s t h1)). Qed.
Lemma lem3906767 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : term107 _100810 s t.
Proof. exact (fun h0 : term95 _100810 s t => @lem3906766 _100810 s t h1). Qed.
Lemma lem3906769 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3906770 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term107 _100810 s t) = (@SUBSET _100810 s t).
Proof. exact (@lem3906769 (@SUBSET _100810 s t)). Qed.
Lemma lem3906771 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) : @SUBSET _100810 s t.
Proof. exact (EQ_MP (@lem3906770 _100810 s t) (@lem3906767 _100810 s t h1)). Qed.
Lemma lem3906773 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term87 _100810 s t) : (@CARD _100810 s) = (@CARD _100810 t).
Proof. exact (proj1 (@lem3905909 _100810 s t h1)). Qed.
Lemma lem3906774 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term87 _100810 s t) : term108 _100810 s t.
Proof. exact (fun h0 : term96 _100810 s t => @lem3906773 _100810 s t h1). Qed.
Lemma lem3906776 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3906777 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term108 _100810 s t) = ((@CARD _100810 s) = (@CARD _100810 t)).
Proof. exact (@lem3906776 ((@CARD _100810 s) = (@CARD _100810 t))). Qed.
Lemma lem3906778 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term87 _100810 s t) : (@CARD _100810 s) = (@CARD _100810 t).
Proof. exact (EQ_MP (@lem3906777 _100810 s t) (@lem3906774 _100810 s t h1)). Qed.
Lemma lem3906794 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3906795 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term94 _100810 _45340 _45341) = (term109 _100810 _45340 _45341).
Proof. exact (@lem3906794 (term96 _100810 _45340 _45341) (term95 _100810 _45340 _45341) (_45340 = _45341)). Qed.
Lemma lem3906811 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3906812 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term110 _100810 _45340 _45341) = (term111 _100810 _45340 _45341).
Proof. exact (@lem3906811 (_45340 = _45341) (term95 _100810 _45340 _45341)). Qed.
Lemma lem3906820 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term112 _100810 _45340 _45341) = (term112 _100810 _45340 _45341).
Proof. exact (eq_refl (term112 _100810 _45340 _45341)). Qed.
Lemma lem3906821 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term109 _100810 _45340 _45341) = (term113 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906820 _100810 _45340 _45341) (@lem3906812 _100810 _45340 _45341)). Qed.
Lemma lem3906825 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3906826 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term113 _100810 _45340 _45341) = (term114 _100810 _45340 _45341).
Proof. exact (@lem3906825 (_45340 = _45341) (term96 _100810 _45340 _45341) (term95 _100810 _45340 _45341)). Qed.
Lemma lem3906846 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term109 _100810 _45340 _45341) = (term114 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906821 _100810 _45340 _45341) (@lem3906826 _100810 _45340 _45341)). Qed.
Lemma lem3906847 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term94 _100810 _45340 _45341) = (term114 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906795 _100810 _45340 _45341) (@lem3906846 _100810 _45340 _45341)). Qed.
Lemma lem3906848 {_100810 : Type'} (_45341 : _100810 -> Prop) : (term73 _100810 _45341) = (term73 _100810 _45341).
Proof. exact (eq_refl (term73 _100810 _45341)). Qed.
Lemma lem3906849 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term97 _100810 _45340 _45341) = (term115 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906848 _100810 _45341) (@lem3906847 _100810 _45340 _45341)). Qed.
Lemma lem3906853 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3906854 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term115 _100810 _45340 _45341) = (term116 _100810 _45340 _45341).
Proof. exact (@lem3906853 (_45340 = _45341) (term92 _100810 _45341) (term117 _100810 _45340 _45341)). Qed.
Lemma lem3906870 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3906871 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term118 _100810 _45340 _45341) = (term119 _100810 _45340 _45341).
Proof. exact (@lem3906870 (term96 _100810 _45340 _45341) (term92 _100810 _45341) (term95 _100810 _45340 _45341)). Qed.
Lemma lem3906889 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term120 _100810 _45340 _45341) = (term120 _100810 _45340 _45341).
Proof. exact (eq_refl (term120 _100810 _45340 _45341)). Qed.
Lemma lem3906890 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term116 _100810 _45340 _45341) = (term121 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906889 _100810 _45340 _45341) (@lem3906871 _100810 _45340 _45341)). Qed.
Lemma lem3906901 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term115 _100810 _45340 _45341) = (term121 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906854 _100810 _45340 _45341) (@lem3906890 _100810 _45340 _45341)). Qed.
Lemma lem3906902 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term97 _100810 _45340 _45341) = (term121 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906849 _100810 _45340 _45341) (@lem3906901 _100810 _45340 _45341)). Qed.
Lemma lem3906903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3906904 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term122 _100810 _45340 _45341) = (term123 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906903) (@lem3906902 _100810 _45340 _45341)). Qed.
Lemma lem3906930 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3906931 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term72 _100810 _45340 _45341) = (term117 _100810 _45340 _45341).
Proof. exact (@lem3906930 (term96 _100810 _45340 _45341) (term95 _100810 _45340 _45341)). Qed.
Lemma lem3906939 {_100810 : Type'} (_45341 : _100810 -> Prop) : (term73 _100810 _45341) = (term73 _100810 _45341).
Proof. exact (eq_refl (term73 _100810 _45341)). Qed.
Lemma lem3906940 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term75 _100810 _45340 _45341) = (term118 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906939 _100810 _45341) (@lem3906931 _100810 _45340 _45341)). Qed.
Lemma lem3906944 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3906945 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term118 _100810 _45340 _45341) = (term119 _100810 _45340 _45341).
Proof. exact (@lem3906944 (term96 _100810 _45340 _45341) (term92 _100810 _45341) (term95 _100810 _45340 _45341)). Qed.
Lemma lem3906963 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term75 _100810 _45340 _45341) = (term119 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906940 _100810 _45340 _45341) (@lem3906945 _100810 _45340 _45341)). Qed.
Lemma lem3906964 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term120 _100810 _45340 _45341) = (term120 _100810 _45340 _45341).
Proof. exact (eq_refl (term120 _100810 _45340 _45341)). Qed.
Lemma lem3906965 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term124 _100810 _45340 _45341) = (term121 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906964 _100810 _45340 _45341) (@lem3906963 _100810 _45340 _45341)). Qed.
Lemma lem3906976 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : ((term97 _100810 _45340 _45341) = (term124 _100810 _45340 _45341)) = ((term121 _100810 _45340 _45341) = (term121 _100810 _45340 _45341)).
Proof. exact (MK_COMB (@lem3906904 _100810 _45340 _45341) (@lem3906965 _100810 _45340 _45341)). Qed.
Lemma lem3906978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3906979 (x : Prop) : (x = x) = True.
Proof. exact (@lem3906978 Prop x). Qed.
Lemma lem3906980 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : ((term121 _100810 _45340 _45341) = (term121 _100810 _45340 _45341)) = True.
Proof. exact (@lem3906979 (term121 _100810 _45340 _45341)). Qed.
Lemma lem3906981 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : ((term97 _100810 _45340 _45341) = (term124 _100810 _45340 _45341)) = True.
Proof. exact (TRANS (@lem3906976 _100810 _45340 _45341) (@lem3906980 _100810 _45340 _45341)). Qed.
Lemma lem3906982 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : True = ((term97 _100810 _45340 _45341) = (term124 _100810 _45340 _45341)).
Proof. exact (SYM (@lem3906981 _100810 _45340 _45341)). Qed.
Lemma lem3906983 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term97 _100810 _45340 _45341) = (term124 _100810 _45340 _45341).
Proof. exact (EQ_MP (@lem3906982 _100810 _45340 _45341) (@lem0)). Qed.
Lemma lem3906984 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) (h1 : term11 _100810) : term124 _100810 _45340 _45341.
Proof. exact (EQ_MP (@lem3906983 _100810 _45340 _45341) (@lem3906360 _100810 _45340 _45341 h1)). Qed.
Lemma lem3906986 (b : Prop) (a : Prop) : (a \/ b) = (term125 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3906987 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term124 _100810 _45340 _45341) = (term126 _100810 _45340 _45341).
Proof. exact (@lem3906986 (term75 _100810 _45340 _45341) (_45340 = _45341)). Qed.
Lemma lem3906989 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3906990 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term129 _100810 _45340 _45341) = (term130 _100810 _45340 _45341).
Proof. exact (@lem3906989 (term92 _100810 _45341) (term72 _100810 _45340 _45341)). Qed.
Lemma lem3906992 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3906993 {_100810 : Type'} (_45341 : _100810 -> Prop) : (term132 _100810 _45341) = (@FINITE _100810 _45341).
Proof. exact (@lem3906992 (@FINITE _100810 _45341)). Qed.
Lemma lem3906994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3906995 {_100810 : Type'} (_45341 : _100810 -> Prop) : (term133 _100810 _45341) = (term134 _100810 _45341).
Proof. exact (MK_COMB (@lem3906994) (@lem3906993 _100810 _45341)). Qed.
Lemma lem3906997 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3906998 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term135 _100810 _45340 _45341) = (term136 _100810 _45340 _45341).
Proof. exact (@lem3906997 (term95 _100810 _45340 _45341) (term96 _100810 _45340 _45341)). Qed.
Lemma lem3907000 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3907001 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term137 _100810 _45340 _45341) = (@SUBSET _100810 _45340 _45341).
Proof. exact (@lem3907000 (@SUBSET _100810 _45340 _45341)). Qed.
Lemma lem3907002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3907003 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term138 _100810 _45340 _45341) = (term139 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3907002) (@lem3907001 _100810 _45340 _45341)). Qed.
Lemma lem3907005 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3907006 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term140 _100810 _45340 _45341) = ((@CARD _100810 _45340) = (@CARD _100810 _45341)).
Proof. exact (@lem3907005 ((@CARD _100810 _45340) = (@CARD _100810 _45341))). Qed.
Lemma lem3907007 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term136 _100810 _45340 _45341) = (term77 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3907003 _100810 _45340 _45341) (@lem3907006 _100810 _45340 _45341)). Qed.
Lemma lem3907008 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term135 _100810 _45340 _45341) = (term77 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906998 _100810 _45340 _45341) (@lem3907007 _100810 _45340 _45341)). Qed.
Lemma lem3907009 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term130 _100810 _45340 _45341) = (term82 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3906995 _100810 _45341) (@lem3907008 _100810 _45340 _45341)). Qed.
Lemma lem3907010 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term129 _100810 _45340 _45341) = (term82 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906990 _100810 _45340 _45341) (@lem3907009 _100810 _45340 _45341)). Qed.
Lemma lem3907011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3907012 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term141 _100810 _45340 _45341) = (term142 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3907011) (@lem3907010 _100810 _45340 _45341)). Qed.
Lemma lem3907013 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (_45340 = _45341) = (_45340 = _45341).
Proof. exact (eq_refl (_45340 = _45341)). Qed.
Lemma lem3907014 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term126 _100810 _45340 _45341) = (term32 _100810 _45340 _45341).
Proof. exact (MK_COMB (@lem3907012 _100810 _45340 _45341) (@lem3907013 _100810 _45340 _45341)). Qed.
Lemma lem3907015 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) : (term124 _100810 _45340 _45341) = (term32 _100810 _45340 _45341).
Proof. exact (TRANS (@lem3906987 _100810 _45340 _45341) (@lem3907014 _100810 _45340 _45341)). Qed.
Lemma lem3907017 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) (h2 : term87 _100810 s t) : term77 _100810 s t.
Proof. exact (conj (@lem3906771 _100810 s t h1) (@lem3906778 _100810 s t h2)). Qed.
Lemma lem3907018 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term53 _100810 s t) (h2 : term87 _100810 s t) : term82 _100810 s t.
Proof. exact (conj (@lem3906764 _100810 s t h1) (@lem3907017 _100810 s t h1 h2)). Qed.
Lemma lem3907020 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) (h1 : term11 _100810) : term32 _100810 _45340 _45341.
Proof. exact (EQ_MP (@lem3907015 _100810 _45340 _45341) (@lem3906984 _100810 _45340 _45341 h1)). Qed.
Lemma lem3907021 {_100810 : Type'} (_45340 : _100810 -> Prop) (_45341 : _100810 -> Prop) (h1 : term11 _100810) : term32 _100810 _45340 _45341.
Proof. exact (@lem3907020 _100810 _45340 _45341 h1). Qed.
Lemma lem3907022 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) : term32 _100810 s t.
Proof. exact (@lem3907021 _100810 s t h1). Qed.
Lemma lem3907025 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) (h3 : term87 _100810 s t) : s = t.
Proof. exact (@lem3907022 _100810 s t h1 (@lem3907018 _100810 s t h2 h3)). Qed.
Lemma lem3907026 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) (h3 : term87 _100810 s t) : term143 _100810 s t.
Proof. exact (fun h0 : term98 _100810 s t => @lem3907025 _100810 s t h1 h2 h3). Qed.
Lemma lem3907028 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3907029 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term143 _100810 s t) = (s = t).
Proof. exact (@lem3907028 (s = t)). Qed.
Lemma lem3907030 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) (h3 : term87 _100810 s t) : s = t.
Proof. exact (EQ_MP (@lem3907029 _100810 s t) (@lem3907026 _100810 s t h1 h2 h3)). Qed.
Lemma lem3907033 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3907035 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) : (term98 _100810 s t) = (term144 _100810 s t).
Proof. exact (@lem3907033 (s = t)). Qed.
Lemma lem3907038 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term87 _100810 s t) : term144 _100810 s t.
Proof. exact (EQ_MP (@lem3907035 _100810 s t) (@lem3906398 _100810 s t h1)). Qed.
Lemma lem3907041 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) (h3 : term87 _100810 s t) : False.
Proof. exact (@lem3907038 _100810 s t h3 (@lem3907030 _100810 s t h1 h2 h3)). Qed.
Lemma lem3907042 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) (h3 : term87 _100810 s t) : term145.
Proof. exact (fun h0 : ~ False => @lem3907041 _100810 s t h1 h2 h3). Qed.
Lemma lem3907044 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3907045 : term145 = False.
Proof. exact (@lem3907044 False). Qed.
Lemma lem3907046 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) (h3 : term87 _100810 s t) : False.
Proof. exact (EQ_MP (@lem3907045) (@lem3907042 _100810 s t h1 h2 h3)). Qed.
Lemma lem3907151 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3907152 {_100810 : Type'} (t : _100810 -> Prop) : (@CARD _100810 t) = (@CARD _100810 t).
Proof. exact (@lem3907151 (@CARD _100810 t)). Qed.
Lemma lem3907153 {_100810 : Type'} (t : _100810 -> Prop) : term146 _100810 t.
Proof. exact (fun h0 : term102 _100810 t => @lem3907152 _100810 t). Qed.
Lemma lem3907155 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3907156 {_100810 : Type'} (t : _100810 -> Prop) : (term146 _100810 t) = ((@CARD _100810 t) = (@CARD _100810 t)).
Proof. exact (@lem3907155 ((@CARD _100810 t) = (@CARD _100810 t))). Qed.
Lemma lem3907157 {_100810 : Type'} (t : _100810 -> Prop) : (@CARD _100810 t) = (@CARD _100810 t).
Proof. exact (EQ_MP (@lem3907156 _100810 t) (@lem3907153 _100810 t)). Qed.
Lemma lem3907160 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3907162 {_100810 : Type'} (t : _100810 -> Prop) : (term102 _100810 t) = (term147 _100810 t).
Proof. exact (@lem3907160 ((@CARD _100810 t) = (@CARD _100810 t))). Qed.
Lemma lem3907165 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : term147 _100810 t.
Proof. exact (EQ_MP (@lem3907162 _100810 t) (@lem3906626 _100810 s t h1)). Qed.
Lemma lem3907168 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : False.
Proof. exact (@lem3907165 _100810 s t h1 (@lem3907157 _100810 t)). Qed.
Lemma lem3907169 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : term145.
Proof. exact (fun h0 : ~ False => @lem3907168 _100810 s t h1). Qed.
Lemma lem3907171 (p : Prop) : (term106 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3907172 : term145 = False.
Proof. exact (@lem3907171 False). Qed.
Lemma lem3907174 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term88 _100810 s t) : False.
Proof. exact (EQ_MP (@lem3907172) (@lem3907169 _100810 s t h1)). Qed.
Lemma lem3907175 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) : False.
Proof. exact (or_elim (@lem3905903 _100810 s t h2) (fun h0 : term87 _100810 s t => @lem3907046 _100810 s t h1 h2 h0) (fun h0 : term88 _100810 s t => @lem3907174 _100810 s t h0)). Qed.
Lemma lem3907176 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) : (term53 _100810 s t) = False.
Proof. exact (prop_ext (fun h3 : term53 _100810 s t => @lem3907175 _100810 s t h1 h2) (fun h3 : False => @lem3905902 _100810 s t h2)). Qed.
Lemma lem3907177 {_100810 : Type'} (s : _100810 -> Prop) (t : _100810 -> Prop) (h1 : term11 _100810) (h2 : term53 _100810 s t) : False.
Proof. exact (EQ_MP (@lem3907176 _100810 s t h1 h2) (@lem3905902 _100810 s t h2)). Qed.
Lemma lem3907178 {_100810 : Type'} (s : _100810 -> Prop) (h1 : term11 _100810) (h2 : term64 _100810 s) : False.
Proof. exact (ex_elim (@lem3905625 _100810 s h2) (fun t : _100810 -> Prop => fun h0 : term63 _100810 s t => @lem3907177 _100810 s t h1 h0)). Qed.
Lemma lem3907179 {_100810 : Type'} (h1 : term11 _100810) (h2 : term10 _100810) : False.
Proof. exact (ex_elim (@lem3905011 _100810 h2) (fun s : _100810 -> Prop => fun h0 : term69 _100810 s => @lem3907178 _100810 s h1 h0)). Qed.
Lemma lem3907180 {_100810 A : Type'} (h1 : term11 _100810) (h2 : term10 _100810) : term17 A.
Proof. exact (fun h0 : term11 A => @lem3907179 _100810 h1 h2). Qed.
Lemma lem3907181 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem3907182 {_100810 A : Type'} (h1 : term11 _100810) (h2 : term10 _100810) : term18 A.
Proof. exact (EQ_MP (@lem3907181 A) (@lem3907180 _100810 A h1 h2)). Qed.
Lemma lem3907183 {_100810 A : Type'} (h1 : term10 _100810) : term21 _100810 A.
Proof. exact (fun h0 : term11 _100810 => @lem3907182 _100810 A h0 h1). Qed.
Lemma lem3907184 {_100810 A : Type'} (h1 : term10 _100810) : term24 _100810 A.
Proof. exact (fun h0 : term40 => @lem3907183 _100810 A h1). Qed.
Lemma lem3907185 {_100810 A : Type'} (h1 : term10 _100810) : term27 _100810 A.
Proof. exact (fun h0 : term12 A => @lem3907184 _100810 A h1). Qed.
Lemma lem3907186 {_100810 A : Type'} (h1 : term10 _100810) : term29 _100810 A.
Proof. exact (fun h0 : term12 _100810 => @lem3907185 _100810 A h1). Qed.
Lemma lem3907187 {_100810 A : Type'} : term31 _100810 A.
Proof. exact (fun h0 : term10 _100810 => @lem3907186 _100810 A h0). Qed.
Lemma lem3907188 {_100810 A : Type'} : term13 _100810 A.
Proof. exact (EQ_MP (@lem3904903 _100810 A) (@lem3907187 _100810 A)). Qed.
Lemma lem3907190 {_100810 A : Type'} : term13 _100810 A.
Proof. exact (@lem3904559 _100810 A (@lem3907188 _100810 A)). Qed.
Lemma lem3907191 {_100810 A : Type'} (h1 : term10 _100810) : term28 _100810 A.
Proof. exact (@lem3907190 _100810 A (@lem3904533 _100810 h1)). Qed.
Lemma lem3907192 {_100810 A : Type'} (h1 : term10 _100810) : term26 _100810 A.
Proof. exact (@lem3907191 _100810 A h1 (@lem3904538 _100810)). Qed.
Lemma lem3907193 {_100810 A : Type'} (h1 : term10 _100810) : term23 _100810 A.
Proof. exact (@lem3907192 _100810 A h1 (@lem3904539 A)). Qed.
Lemma lem3907194 {_100810 A : Type'} (h1 : term10 _100810) : term20 _100810 A.
Proof. exact (@lem3907193 _100810 A h1 (@lem92426)). Qed.
Lemma lem3907195 {_100810 A : Type'} (h1 : term10 _100810) : term17 A.
Proof. exact (@lem3907194 _100810 A h1 (@lem3904534 _100810)). Qed.
Lemma lem3907196 {_100810 : Type'} (h1 : term10 _100810) : False.
Proof. exact (@lem3907195 _100810 Prop h1 (@lem3900203 Prop)). Qed.
Lemma lem3907197 {_100810 : Type'} (h1 : term10 _100810) : (term10 _100810) = False.
Proof. exact (prop_ext (fun h2 : term10 _100810 => @lem3907196 _100810 h1) (fun h2 : False => @lem3904533 _100810 h1)). Qed.
Lemma lem3907198 {_100810 : Type'} (h1 : term10 _100810) : False.
Proof. exact (EQ_MP (@lem3907197 _100810 h1) (@lem3904533 _100810 h1)). Qed.
Lemma lem3907199 {_100810 : Type'} : term9 _100810.
Proof. exact (fun h0 : term10 _100810 => @lem3907198 _100810 h0). Qed.
Lemma lem3907200 {_100810 : Type'} : term8 _100810.
Proof. exact (EQ_MP (@lem3904532 _100810) (@lem3907199 _100810)). Qed.
