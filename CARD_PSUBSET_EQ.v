Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_PSUBSET_EQ_term_abbrevs.
Require Import CARD_PSUBSET_spec.
Require Import CARD_PSUBSET_IMP_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LT_REFL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem3921543 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3921544 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3921545 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3921544 t1) (@lem3921543 t1)). Qed.
Lemma lem3921546 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3921545 t1 t2). Qed.
Lemma lem3921547 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3921548 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3921547 t1 t2) (@lem3921546 t1 t2)). Qed.
Lemma lem3921549 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3921548 t1 t2 t3). Qed.
Lemma lem3921550 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3921551 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3921550 t1 t2 t3) (@lem3921549 t1 t2 t3)). Qed.
Lemma lem3921552 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3921551 t1 t2 t3)). Qed.
Lemma lem3921554 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3921555 {_100977 : Type'} : (term8 _100977) = (term9 _100977).
Proof. exact (@lem3921554 (term8 _100977)). Qed.
Lemma lem3921556 {_100977 : Type'} : (term9 _100977) = (term8 _100977).
Proof. exact (SYM (@lem3921555 _100977)). Qed.
Lemma lem3921557 {_100977 : Type'} (h1 : term10 _100977) : term10 _100977.
Proof. exact (h1). Qed.
Lemma lem3921558 {_100977 : Type'} : term11 _100977.
Proof. exact (@lem3921542 _100977). Qed.
Lemma lem3921561 {_100977 : Type'} : term12 _100977.
Proof. exact (@lem3921097 _100977). Qed.
Lemma lem3921566 {_100977 A : Type'} (h1 : term13 _100977 A) : term13 _100977 A.
Proof. exact (h1). Qed.
Lemma lem3921567 {_100977 A : Type'} : term14 _100977 A.
Proof. exact (fun h0 : term13 _100977 A => @lem3921566 _100977 A h0). Qed.
Lemma lem3921568 {_100977 A : Type'} (h1 : term14 _100977 A) : term14 _100977 A.
Proof. exact (h1). Qed.
Lemma lem3921569 {_100977 A : Type'} (h1 : term13 _100977 A) : term13 _100977 A.
Proof. exact (h1). Qed.
Lemma lem3921570 {_100977 A : Type'} (h1 : term13 _100977 A) (h2 : term14 _100977 A) : term13 _100977 A.
Proof. exact (@lem3921568 _100977 A h2 (@lem3921569 _100977 A h1)). Qed.
Lemma lem3921571 {_100977 A : Type'} (h1 : term13 _100977 A) : term15 _100977 A.
Proof. exact (fun h0 : term14 _100977 A => @lem3921570 _100977 A h1 h0). Qed.
Lemma lem3921572 {_100977 A : Type'} (h1 : term14 _100977 A) : term14 _100977 A.
Proof. exact (h1). Qed.
Lemma lem3921573 {_100977 A : Type'} (h1 : term13 _100977 A) (h2 : term14 _100977 A) : term13 _100977 A.
Proof. exact (@lem3921571 _100977 A h1 (@lem3921572 _100977 A h2)). Qed.
Lemma lem3921574 {_100977 A : Type'} (h1 : term14 _100977 A) : term14 _100977 A.
Proof. exact (fun h0 : term13 _100977 A => @lem3921573 _100977 A h0 h1). Qed.
Lemma lem3921575 {_100977 A : Type'} : term16 _100977 A.
Proof. exact (fun h0 : term14 _100977 A => @lem3921574 _100977 A h0). Qed.
Lemma lem3921578 {_100977 A : Type'} : term14 _100977 A.
Proof. exact (@lem3921575 _100977 A (@lem3921567 _100977 A)). Qed.
Lemma lem3921579 {_100977 A : Type'} : term14 _100977 A.
Proof. exact (@lem3921578 _100977 A). Qed.
Lemma lem3921629 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3921630 {_100977 : Type'} : (term17 _100977) = (term18 _100977).
Proof. exact (@lem3921629 (term11 _100977)). Qed.
Lemma lem3921643 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem3921644 {_100977 A : Type'} : (term20 _100977 A) = (term21 _100977 A).
Proof. exact (MK_COMB (@lem3921643 A) (@lem3921630 _100977)). Qed.
Lemma lem3921647 {_100977 : Type'} : (term19 _100977) = (term19 _100977).
Proof. exact (eq_refl (term19 _100977)). Qed.
Lemma lem3921648 {_100977 A : Type'} : (term22 _100977 A) = (term23 _100977 A).
Proof. exact (MK_COMB (@lem3921647 _100977) (@lem3921644 _100977 A)). Qed.
Lemma lem3921651 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem3921652 {_100977 A : Type'} : (term25 _100977 A) = (term26 _100977 A).
Proof. exact (MK_COMB (@lem3921651) (@lem3921648 _100977 A)). Qed.
Lemma lem3921655 {_100977 : Type'} : (term27 _100977) = (term27 _100977).
Proof. exact (eq_refl (term27 _100977)). Qed.
Lemma lem3921662 {_100977 A : Type'} : (term13 _100977 A) = (term28 _100977 A).
Proof. exact (MK_COMB (@lem3921655 _100977) (@lem3921652 _100977 A)). Qed.
Lemma lem3921673 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term29 _100977 a b) = (term29 _100977 a b).
Proof. exact (eq_refl (term29 _100977 a b)). Qed.
Lemma lem3921674 {_100977 : Type'} (a : _100977 -> Prop) : (term30 _100977 a) = (term30 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3921673 _100977 a b)). Qed.
Lemma lem3921675 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921676 {_100977 : Type'} (a : _100977 -> Prop) : (term31 _100977 a) = (term31 _100977 a).
Proof. exact (MK_COMB (@lem3921675 _100977) (@lem3921674 _100977 a)). Qed.
Lemma lem3921677 {_100977 : Type'} : (term32 _100977) = (term32 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3921676 _100977 a)). Qed.
Lemma lem3921678 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921679 {_100977 : Type'} : (term11 _100977) = (term11 _100977).
Proof. exact (MK_COMB (@lem3921678 _100977) (@lem3921677 _100977)). Qed.
Lemma lem3921680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3921681 {_100977 : Type'} : (term18 _100977) = (term18 _100977).
Proof. exact (MK_COMB (@lem3921680) (@lem3921679 _100977)). Qed.
Lemma lem3921690 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term33 A a b) = (term33 A a b).
Proof. exact (eq_refl (term33 A a b)). Qed.
Lemma lem3921691 {A : Type'} (a : A -> Prop) : (term34 A a) = (term34 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3921690 A a b)). Qed.
Lemma lem3921692 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3921693 {A : Type'} (a : A -> Prop) : (term35 A a) = (term35 A a).
Proof. exact (MK_COMB (@lem3921692 A) (@lem3921691 A a)). Qed.
Lemma lem3921694 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3921693 A a)). Qed.
Lemma lem3921695 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3921696 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3921695 A) (@lem3921694 A)). Qed.
Lemma lem3921697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3921698 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem3921697) (@lem3921696 A)). Qed.
Lemma lem3921699 {_100977 A : Type'} : (term21 _100977 A) = (term21 _100977 A).
Proof. exact (MK_COMB (@lem3921698 A) (@lem3921681 _100977)). Qed.
Lemma lem3921708 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term33 _100977 a b) = (term33 _100977 a b).
Proof. exact (eq_refl (term33 _100977 a b)). Qed.
Lemma lem3921709 {_100977 : Type'} (a : _100977 -> Prop) : (term34 _100977 a) = (term34 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3921708 _100977 a b)). Qed.
Lemma lem3921710 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921711 {_100977 : Type'} (a : _100977 -> Prop) : (term35 _100977 a) = (term35 _100977 a).
Proof. exact (MK_COMB (@lem3921710 _100977) (@lem3921709 _100977 a)). Qed.
Lemma lem3921712 {_100977 : Type'} : (term36 _100977) = (term36 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3921711 _100977 a)). Qed.
Lemma lem3921713 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921714 {_100977 : Type'} : (term12 _100977) = (term12 _100977).
Proof. exact (MK_COMB (@lem3921713 _100977) (@lem3921712 _100977)). Qed.
Lemma lem3921715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3921716 {_100977 : Type'} : (term19 _100977) = (term19 _100977).
Proof. exact (MK_COMB (@lem3921715) (@lem3921714 _100977)). Qed.
Lemma lem3921717 {_100977 A : Type'} : (term23 _100977 A) = (term23 _100977 A).
Proof. exact (MK_COMB (@lem3921716 _100977) (@lem3921699 _100977 A)). Qed.
Lemma lem3921720 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3921721 : term38 = term38.
Proof. exact (fun_ext (fun n : nat => @lem3921720 n)). Qed.
Lemma lem3921722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3921723 : term39 = term39.
Proof. exact (MK_COMB (@lem3921722) (@lem3921721)). Qed.
Lemma lem3921724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3921725 : term24 = term24.
Proof. exact (MK_COMB (@lem3921724) (@lem3921723)). Qed.
Lemma lem3921726 {_100977 A : Type'} : (term26 _100977 A) = (term26 _100977 A).
Proof. exact (MK_COMB (@lem3921725) (@lem3921717 _100977 A)). Qed.
Lemma lem3921739 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term40 _100977 a b) = (term40 _100977 a b).
Proof. exact (eq_refl (term40 _100977 a b)). Qed.
Lemma lem3921740 {_100977 : Type'} (a : _100977 -> Prop) : (term41 _100977 a) = (term41 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3921739 _100977 a b)). Qed.
Lemma lem3921741 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921742 {_100977 : Type'} (a : _100977 -> Prop) : (term42 _100977 a) = (term42 _100977 a).
Proof. exact (MK_COMB (@lem3921741 _100977) (@lem3921740 _100977 a)). Qed.
Lemma lem3921743 {_100977 : Type'} : (term43 _100977) = (term43 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3921742 _100977 a)). Qed.
Lemma lem3921744 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921745 {_100977 : Type'} : (term8 _100977) = (term8 _100977).
Proof. exact (MK_COMB (@lem3921744 _100977) (@lem3921743 _100977)). Qed.
Lemma lem3921746 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3921747 {_100977 : Type'} : (term10 _100977) = (term10 _100977).
Proof. exact (MK_COMB (@lem3921746) (@lem3921745 _100977)). Qed.
Lemma lem3921748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3921749 {_100977 : Type'} : (term27 _100977) = (term27 _100977).
Proof. exact (MK_COMB (@lem3921748) (@lem3921747 _100977)). Qed.
Lemma lem3921750 {_100977 A : Type'} : (term28 _100977 A) = (term28 _100977 A).
Proof. exact (MK_COMB (@lem3921749 _100977) (@lem3921726 _100977 A)). Qed.
Lemma lem3921831 {_100977 A : Type'} : (term13 _100977 A) = (term28 _100977 A).
Proof. exact (TRANS (@lem3921662 _100977 A) (@lem3921750 _100977 A)). Qed.
Lemma lem3921832 {_100977 A : Type'} : (term28 _100977 A) = (term13 _100977 A).
Proof. exact (SYM (@lem3921831 _100977 A)). Qed.
Lemma lem3921833 {_100977 : Type'} (h1 : term10 _100977) : term10 _100977.
Proof. exact (h1). Qed.
Lemma lem3921834 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem3921835 {_100977 : Type'} (h1 : term12 _100977) : term12 _100977.
Proof. exact (h1). Qed.
Lemma lem3921837 {_100977 : Type'} (h1 : term11 _100977) : term11 _100977.
Proof. exact (h1). Qed.
Lemma lem3921857 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term44 _100977 a b) = (term45 _100977 a b).
Proof. exact (@lem17646 (@PSUBSET _100977 a b) (term46 _100977 a b)). Qed.
Lemma lem3921859 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term47 _100977 a b) = (term47 _100977 a b).
Proof. exact (eq_refl (term47 _100977 a b)). Qed.
Lemma lem3921860 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term48 _100977 a b) = (term49 _100977 a b).
Proof. exact (MK_COMB (@lem3921859 _100977 a b) (@lem3921857 _100977 a b)). Qed.
Lemma lem3921861 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term50 _100977 a b) = (term48 _100977 a b).
Proof. exact (@lem17362 (term51 _100977 a b) ((@PSUBSET _100977 a b) = (term46 _100977 a b))). Qed.
Lemma lem3921862 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term50 _100977 a b) = (term49 _100977 a b).
Proof. exact (TRANS (@lem3921861 _100977 a b) (@lem3921860 _100977 a b)). Qed.
Lemma lem3921863 {_100977 : Type'} (P : type686 _100977) : (term52 _100977 P) = (term53 _100977 P).
Proof. exact (@lem18392 (_100977 -> Prop) P). Qed.
Lemma lem3921864 {_100977 : Type'} (a : _100977 -> Prop) : (term54 _100977 a) = (term55 _100977 a).
Proof. exact (@lem3921863 _100977 (term41 _100977 a)). Qed.
Lemma lem3921865 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term56 _100977 a b) = (term40 _100977 a b).
Proof. exact (eq_refl (term56 _100977 a b)). Qed.
Lemma lem3921866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3921867 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term57 _100977 a b) = (term50 _100977 a b).
Proof. exact (MK_COMB (@lem3921866) (@lem3921865 _100977 a b)). Qed.
Lemma lem3921868 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term57 _100977 a b) = (term49 _100977 a b).
Proof. exact (TRANS (@lem3921867 _100977 a b) (@lem3921862 _100977 a b)). Qed.
Lemma lem3921869 {_100977 : Type'} (a : _100977 -> Prop) : (term58 _100977 a) = (term59 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3921868 _100977 a b)). Qed.
Lemma lem3921870 {_100977 : Type'} : (@ex (_100977 -> Prop)) = (@ex (_100977 -> Prop)).
Proof. exact (eq_refl (@ex (_100977 -> Prop))). Qed.
Lemma lem3921871 {_100977 : Type'} (a : _100977 -> Prop) : (term55 _100977 a) = (term60 _100977 a).
Proof. exact (MK_COMB (@lem3921870 _100977) (@lem3921869 _100977 a)). Qed.
Lemma lem3921872 {_100977 : Type'} (a : _100977 -> Prop) : (term54 _100977 a) = (term60 _100977 a).
Proof. exact (TRANS (@lem3921864 _100977 a) (@lem3921871 _100977 a)). Qed.
Lemma lem3921873 {_100977 : Type'} (P : type686 _100977) : (term52 _100977 P) = (term53 _100977 P).
Proof. exact (@lem18392 (_100977 -> Prop) P). Qed.
Lemma lem3921874 {_100977 : Type'} : (term10 _100977) = (term61 _100977).
Proof. exact (@lem3921873 _100977 (term43 _100977)). Qed.
Lemma lem3921875 {_100977 : Type'} (a : _100977 -> Prop) : (term62 _100977 a) = (term42 _100977 a).
Proof. exact (eq_refl (term62 _100977 a)). Qed.
Lemma lem3921876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3921877 {_100977 : Type'} (a : _100977 -> Prop) : (term63 _100977 a) = (term54 _100977 a).
Proof. exact (MK_COMB (@lem3921876) (@lem3921875 _100977 a)). Qed.
Lemma lem3921878 {_100977 : Type'} (a : _100977 -> Prop) : (term63 _100977 a) = (term60 _100977 a).
Proof. exact (TRANS (@lem3921877 _100977 a) (@lem3921872 _100977 a)). Qed.
Lemma lem3921879 {_100977 : Type'} : (term64 _100977) = (term65 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3921878 _100977 a)). Qed.
Lemma lem3921880 {_100977 : Type'} : (@ex (_100977 -> Prop)) = (@ex (_100977 -> Prop)).
Proof. exact (eq_refl (@ex (_100977 -> Prop))). Qed.
Lemma lem3921881 {_100977 : Type'} : (term61 _100977) = (term66 _100977).
Proof. exact (MK_COMB (@lem3921880 _100977) (@lem3921879 _100977)). Qed.
Lemma lem3921938 {_100977 : Type'} : (term10 _100977) = (term66 _100977).
Proof. exact (TRANS (@lem3921874 _100977) (@lem3921881 _100977)). Qed.
Lemma lem3921939 {_100977 : Type'} (h1 : term10 _100977) : term66 _100977.
Proof. exact (EQ_MP (@lem3921938 _100977) (@lem3921833 _100977 h1)). Qed.
Lemma lem3921940 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3921941 : term38 = term38.
Proof. exact (fun_ext (fun n : nat => @lem3921940 n)). Qed.
Lemma lem3921942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3921951 : term39 = term39.
Proof. exact (MK_COMB (@lem3921942) (@lem3921941)). Qed.
Lemma lem3921952 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem3921951) (@lem3921834 h1)). Qed.
Lemma lem3921959 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term67 _100977 a b) = (term68 _100977 a b).
Proof. exact (@lem17045 (@PSUBSET _100977 a b) (@FINITE _100977 b)). Qed.
Lemma lem3921960 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term46 _100977 a b) = (term46 _100977 a b).
Proof. exact (eq_refl (term46 _100977 a b)). Qed.
Lemma lem3921961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3921962 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term69 _100977 a b) = (term70 _100977 a b).
Proof. exact (MK_COMB (@lem3921961) (@lem3921959 _100977 a b)). Qed.
Lemma lem3921963 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term71 _100977 a b) = (term72 _100977 a b).
Proof. exact (MK_COMB (@lem3921962 _100977 a b) (@lem3921960 _100977 a b)). Qed.
Lemma lem3921964 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term33 _100977 a b) = (term71 _100977 a b).
Proof. exact (@lem17265 (term73 _100977 a b) (term46 _100977 a b)). Qed.
Lemma lem3921965 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term33 _100977 a b) = (term72 _100977 a b).
Proof. exact (TRANS (@lem3921964 _100977 a b) (@lem3921963 _100977 a b)). Qed.
Lemma lem3921966 {_100977 : Type'} (a : _100977 -> Prop) : (term34 _100977 a) = (term74 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3921965 _100977 a b)). Qed.
Lemma lem3921967 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3921968 {_100977 : Type'} (a : _100977 -> Prop) : (term35 _100977 a) = (term75 _100977 a).
Proof. exact (MK_COMB (@lem3921967 _100977) (@lem3921966 _100977 a)). Qed.
Lemma lem3921969 {_100977 : Type'} : (term36 _100977) = (term76 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3921968 _100977 a)). Qed.
Lemma lem3921970 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922027 {_100977 : Type'} : (term12 _100977) = (term77 _100977).
Proof. exact (MK_COMB (@lem3921970 _100977) (@lem3921969 _100977)). Qed.
Lemma lem3922028 {_100977 : Type'} (h1 : term12 _100977) : term77 _100977.
Proof. exact (EQ_MP (@lem3922027 _100977) (@lem3921835 _100977 h1)). Qed.
Lemma lem3922108 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term78 _100977 a b) = ((@CARD _100977 a) = (@CARD _100977 b)).
Proof. exact (@lem16933 ((@CARD _100977 a) = (@CARD _100977 b))). Qed.
Lemma lem3922110 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term79 _100977 a b) = (term79 _100977 a b).
Proof. exact (eq_refl (term79 _100977 a b)). Qed.
Lemma lem3922111 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term80 _100977 a b) = (term81 _100977 a b).
Proof. exact (MK_COMB (@lem3922110 _100977 a b) (@lem3922108 _100977 a b)). Qed.
Lemma lem3922112 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term82 _100977 a b) = (term80 _100977 a b).
Proof. exact (@lem17045 (@SUBSET _100977 a b) (term83 _100977 a b)). Qed.
Lemma lem3922113 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term82 _100977 a b) = (term81 _100977 a b).
Proof. exact (TRANS (@lem3922112 _100977 a b) (@lem3922111 _100977 a b)). Qed.
Lemma lem3922114 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (@PSUBSET _100977 a b) = (@PSUBSET _100977 a b).
Proof. exact (eq_refl (@PSUBSET _100977 a b)). Qed.
Lemma lem3922115 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3922116 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term84 _100977 a b) = (term85 _100977 a b).
Proof. exact (MK_COMB (@lem3922115) (@lem3922113 _100977 a b)). Qed.
Lemma lem3922117 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term86 _100977 a b) = (term87 _100977 a b).
Proof. exact (MK_COMB (@lem3922116 _100977 a b) (@lem3922114 _100977 a b)). Qed.
Lemma lem3922118 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term29 _100977 a b) = (term86 _100977 a b).
Proof. exact (@lem17265 (term88 _100977 a b) (@PSUBSET _100977 a b)). Qed.
Lemma lem3922119 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term29 _100977 a b) = (term87 _100977 a b).
Proof. exact (TRANS (@lem3922118 _100977 a b) (@lem3922117 _100977 a b)). Qed.
Lemma lem3922120 {_100977 : Type'} (a : _100977 -> Prop) : (term30 _100977 a) = (term89 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3922119 _100977 a b)). Qed.
Lemma lem3922121 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922122 {_100977 : Type'} (a : _100977 -> Prop) : (term31 _100977 a) = (term90 _100977 a).
Proof. exact (MK_COMB (@lem3922121 _100977) (@lem3922120 _100977 a)). Qed.
Lemma lem3922123 {_100977 : Type'} : (term32 _100977) = (term91 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3922122 _100977 a)). Qed.
Lemma lem3922124 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922181 {_100977 : Type'} : (term11 _100977) = (term92 _100977).
Proof. exact (MK_COMB (@lem3922124 _100977) (@lem3922123 _100977)). Qed.
Lemma lem3922182 {_100977 : Type'} (h1 : term11 _100977) : term92 _100977.
Proof. exact (EQ_MP (@lem3922181 _100977) (@lem3921837 _100977 h1)). Qed.
Lemma lem3922183 {_100977 : Type'} (a : _100977 -> Prop) (h1 : term60 _100977 a) : term60 _100977 a.
Proof. exact (h1). Qed.
Lemma lem3922191 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3922192 : term38 = term38.
Proof. exact (fun_ext (fun n : nat => @lem3922191 n)). Qed.
Lemma lem3922193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3922194 : term39 = term39.
Proof. exact (MK_COMB (@lem3922193) (@lem3922192)). Qed.
Lemma lem3922195 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem3922194) (@lem3921952 h1)). Qed.
Lemma lem3922222 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term72 _100977 a b) = (term72 _100977 a b).
Proof. exact (eq_refl (term72 _100977 a b)). Qed.
Lemma lem3922223 {_100977 : Type'} (a : _100977 -> Prop) : (term74 _100977 a) = (term74 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3922222 _100977 a b)). Qed.
Lemma lem3922224 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922225 {_100977 : Type'} (a : _100977 -> Prop) : (term75 _100977 a) = (term75 _100977 a).
Proof. exact (MK_COMB (@lem3922224 _100977) (@lem3922223 _100977 a)). Qed.
Lemma lem3922226 {_100977 : Type'} : (term76 _100977) = (term76 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3922225 _100977 a)). Qed.
Lemma lem3922227 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922228 {_100977 : Type'} : (term77 _100977) = (term77 _100977).
Proof. exact (MK_COMB (@lem3922227 _100977) (@lem3922226 _100977)). Qed.
Lemma lem3922229 {_100977 : Type'} (h1 : term12 _100977) : term77 _100977.
Proof. exact (EQ_MP (@lem3922228 _100977) (@lem3922028 _100977 h1)). Qed.
Lemma lem3922290 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term87 _100977 a b) = (term87 _100977 a b).
Proof. exact (eq_refl (term87 _100977 a b)). Qed.
Lemma lem3922291 {_100977 : Type'} (a : _100977 -> Prop) : (term89 _100977 a) = (term89 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3922290 _100977 a b)). Qed.
Lemma lem3922292 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922293 {_100977 : Type'} (a : _100977 -> Prop) : (term90 _100977 a) = (term90 _100977 a).
Proof. exact (MK_COMB (@lem3922292 _100977) (@lem3922291 _100977 a)). Qed.
Lemma lem3922294 {_100977 : Type'} : (term91 _100977) = (term91 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3922293 _100977 a)). Qed.
Lemma lem3922295 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922296 {_100977 : Type'} : (term92 _100977) = (term92 _100977).
Proof. exact (MK_COMB (@lem3922295 _100977) (@lem3922294 _100977)). Qed.
Lemma lem3922297 {_100977 : Type'} (h1 : term11 _100977) : term92 _100977.
Proof. exact (EQ_MP (@lem3922296 _100977) (@lem3922182 _100977 h1)). Qed.
Lemma lem3922353 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : term49 _100977 a b.
Proof. exact (h1). Qed.
Lemma lem3922354 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : term45 _100977 a b.
Proof. exact (proj2 (@lem3922353 _100977 a b h1)). Qed.
Lemma lem3922355 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : term51 _100977 a b.
Proof. exact (proj1 (@lem3922353 _100977 a b h1)). Qed.
Lemma lem3922358 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term93 _100977 a b) : term93 _100977 a b.
Proof. exact (h1). Qed.
Lemma lem3922359 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term94 _100977 a b) : term94 _100977 a b.
Proof. exact (h1). Qed.
Lemma lem3922384 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term72 _100977 a b) = (term72 _100977 a b).
Proof. exact (eq_refl (term72 _100977 a b)). Qed.
Lemma lem3922385 {_100977 : Type'} (a : _100977 -> Prop) : (term74 _100977 a) = (term74 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3922384 _100977 a b)). Qed.
Lemma lem3922386 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922387 {_100977 : Type'} (a : _100977 -> Prop) : (term75 _100977 a) = (term75 _100977 a).
Proof. exact (MK_COMB (@lem3922386 _100977) (@lem3922385 _100977 a)). Qed.
Lemma lem3922388 {_100977 : Type'} : (term76 _100977) = (term76 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3922387 _100977 a)). Qed.
Lemma lem3922389 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922391 {_100977 : Type'} : (term77 _100977) = (term77 _100977).
Proof. exact (MK_COMB (@lem3922389 _100977) (@lem3922388 _100977)). Qed.
Lemma lem3922392 {_100977 : Type'} (h1 : term12 _100977) : term77 _100977.
Proof. exact (EQ_MP (@lem3922391 _100977) (@lem3922229 _100977 h1)). Qed.
Lemma lem3922454 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3922455 : term38 = term38.
Proof. exact (fun_ext (fun n : nat => @lem3922454 n)). Qed.
Lemma lem3922456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3922458 : term39 = term39.
Proof. exact (MK_COMB (@lem3922456) (@lem3922455)). Qed.
Lemma lem3922459 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem3922458) (@lem3922195 h1)). Qed.
Lemma lem3922517 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term87 _100977 a b) = (term87 _100977 a b).
Proof. exact (eq_refl (term87 _100977 a b)). Qed.
Lemma lem3922518 {_100977 : Type'} (a : _100977 -> Prop) : (term89 _100977 a) = (term89 _100977 a).
Proof. exact (fun_ext (fun b : _100977 -> Prop => @lem3922517 _100977 a b)). Qed.
Lemma lem3922519 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922520 {_100977 : Type'} (a : _100977 -> Prop) : (term90 _100977 a) = (term90 _100977 a).
Proof. exact (MK_COMB (@lem3922519 _100977) (@lem3922518 _100977 a)). Qed.
Lemma lem3922521 {_100977 : Type'} : (term91 _100977) = (term91 _100977).
Proof. exact (fun_ext (fun a : _100977 -> Prop => @lem3922520 _100977 a)). Qed.
Lemma lem3922522 {_100977 : Type'} : (@all (_100977 -> Prop)) = (@all (_100977 -> Prop)).
Proof. exact (eq_refl (@all (_100977 -> Prop))). Qed.
Lemma lem3922524 {_100977 : Type'} : (term92 _100977) = (term92 _100977).
Proof. exact (MK_COMB (@lem3922522 _100977) (@lem3922521 _100977)). Qed.
Lemma lem3922525 {_100977 : Type'} (h1 : term11 _100977) : term92 _100977.
Proof. exact (EQ_MP (@lem3922524 _100977) (@lem3922297 _100977 h1)). Qed.
Lemma lem3922545 {_100977 : Type'} (_45543 : _100977 -> Prop) (h1 : term12 _100977) : term95 _100977 _45543.
Proof. exact (@lem3922392 _100977 h1 _45543). Qed.
Lemma lem3922546 {_100977 : Type'} (_45543 : _100977 -> Prop) : (term95 _100977 _45543) = (term75 _100977 _45543).
Proof. exact (eq_refl (term95 _100977 _45543)). Qed.
Lemma lem3922547 {_100977 : Type'} (_45543 : _100977 -> Prop) (h1 : term12 _100977) : term75 _100977 _45543.
Proof. exact (EQ_MP (@lem3922546 _100977 _45543) (@lem3922545 _100977 _45543 h1)). Qed.
Lemma lem3922548 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) (h1 : term12 _100977) : term96 _100977 _45543 _45544.
Proof. exact (@lem3922547 _100977 _45543 h1 _45544). Qed.
Lemma lem3922549 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term96 _100977 _45543 _45544) = (term72 _100977 _45543 _45544).
Proof. exact (eq_refl (term96 _100977 _45543 _45544)). Qed.
Lemma lem3922550 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) (h1 : term12 _100977) : term72 _100977 _45543 _45544.
Proof. exact (EQ_MP (@lem3922549 _100977 _45543 _45544) (@lem3922548 _100977 _45543 _45544 h1)). Qed.
Lemma lem3922563 (_45549 : nat) (h1 : term39) : term97 _45549.
Proof. exact (@lem3922459 h1 _45549). Qed.
Lemma lem3922564 (_45549 : nat) : (term97 _45549) = (term37 _45549).
Proof. exact (eq_refl (term97 _45549)). Qed.
Lemma lem3922578 {_100977 : Type'} (_45554 : _100977 -> Prop) (h1 : term11 _100977) : term98 _100977 _45554.
Proof. exact (@lem3922525 _100977 h1 _45554). Qed.
Lemma lem3922579 {_100977 : Type'} (_45554 : _100977 -> Prop) : (term98 _100977 _45554) = (term90 _100977 _45554).
Proof. exact (eq_refl (term98 _100977 _45554)). Qed.
Lemma lem3922580 {_100977 : Type'} (_45554 : _100977 -> Prop) (h1 : term11 _100977) : term90 _100977 _45554.
Proof. exact (EQ_MP (@lem3922579 _100977 _45554) (@lem3922578 _100977 _45554 h1)). Qed.
Lemma lem3922581 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) (h1 : term11 _100977) : term99 _100977 _45554 _45555.
Proof. exact (@lem3922580 _100977 _45554 h1 _45555). Qed.
Lemma lem3922582 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term99 _100977 _45554 _45555) = (term87 _100977 _45554 _45555).
Proof. exact (eq_refl (term99 _100977 _45554 _45555)). Qed.
Lemma lem3922583 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) (h1 : term11 _100977) : term87 _100977 _45554 _45555.
Proof. exact (EQ_MP (@lem3922582 _100977 _45554 _45555) (@lem3922581 _100977 _45554 _45555 h1)). Qed.
Lemma lem3922596 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term72 _100977 _45543 _45544) = (term100 _100977 _45543 _45544).
Proof. exact (@lem3921552 (term101 _100977 _45543 _45544) (term102 _100977 _45544) (term46 _100977 _45543 _45544)). Qed.
Lemma lem3922597 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) (h1 : term12 _100977) : term100 _100977 _45543 _45544.
Proof. exact (EQ_MP (@lem3922596 _100977 _45543 _45544) (@lem3922550 _100977 _45543 _45544 h1)). Qed.
Lemma lem3922629 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term93 _100977 a b) : term103 _100977 a b.
Proof. exact (proj2 (@lem3922358 _100977 a b h1)). Qed.
Lemma lem3922666 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term87 _100977 _45554 _45555) = (term104 _100977 _45554 _45555).
Proof. exact (@lem3921552 (term105 _100977 _45554 _45555) ((@CARD _100977 _45554) = (@CARD _100977 _45555)) (@PSUBSET _100977 _45554 _45555)). Qed.
Lemma lem3922667 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) (h1 : term11 _100977) : term104 _100977 _45554 _45555.
Proof. exact (EQ_MP (@lem3922666 _100977 _45554 _45555) (@lem3922583 _100977 _45554 _45555 h1)). Qed.
Lemma lem3922673 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term94 _100977 a b) : term101 _100977 a b.
Proof. exact (proj1 (@lem3922359 _100977 a b h1)). Qed.
Lemma lem3922799 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term93 _100977 a b) : @PSUBSET _100977 a b.
Proof. exact (proj1 (@lem3922358 _100977 a b h1)). Qed.
Lemma lem3922800 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term93 _100977 a b) : term106 _100977 a b.
Proof. exact (fun h0 : term101 _100977 a b => @lem3922799 _100977 a b h1). Qed.
Lemma lem3922802 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3922803 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term106 _100977 a b) = (@PSUBSET _100977 a b).
Proof. exact (@lem3922802 (@PSUBSET _100977 a b)). Qed.
Lemma lem3922804 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term93 _100977 a b) : @PSUBSET _100977 a b.
Proof. exact (EQ_MP (@lem3922803 _100977 a b) (@lem3922800 _100977 a b h1)). Qed.
Lemma lem3922806 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : @FINITE _100977 b.
Proof. exact (proj1 (@lem3922355 _100977 a b h1)). Qed.
Lemma lem3922807 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : term108 _100977 b.
Proof. exact (fun h0 : term102 _100977 b => @lem3922806 _100977 a b h1). Qed.
Lemma lem3922809 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3922810 {_100977 : Type'} (b : _100977 -> Prop) : (term108 _100977 b) = (@FINITE _100977 b).
Proof. exact (@lem3922809 (@FINITE _100977 b)). Qed.
Lemma lem3922811 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : @FINITE _100977 b.
Proof. exact (EQ_MP (@lem3922810 _100977 b) (@lem3922807 _100977 a b h1)). Qed.
Lemma lem3922817 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3922818 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term100 _100977 _45543 _45544) = (term109 _100977 _45543 _45544).
Proof. exact (@lem3922817 (term102 _100977 _45544) (term101 _100977 _45543 _45544) (term46 _100977 _45543 _45544)). Qed.
Lemma lem3922832 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3922833 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term110 _100977 _45543 _45544) = (term111 _100977 _45543 _45544).
Proof. exact (@lem3922832 (term46 _100977 _45543 _45544) (term101 _100977 _45543 _45544)). Qed.
Lemma lem3922839 {_100977 : Type'} (_45544 : _100977 -> Prop) : (term112 _100977 _45544) = (term112 _100977 _45544).
Proof. exact (eq_refl (term112 _100977 _45544)). Qed.
Lemma lem3922840 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term109 _100977 _45543 _45544) = (term113 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922839 _100977 _45544) (@lem3922833 _100977 _45543 _45544)). Qed.
Lemma lem3922844 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3922845 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term113 _100977 _45543 _45544) = (term114 _100977 _45543 _45544).
Proof. exact (@lem3922844 (term46 _100977 _45543 _45544) (term102 _100977 _45544) (term101 _100977 _45543 _45544)). Qed.
Lemma lem3922861 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term109 _100977 _45543 _45544) = (term114 _100977 _45543 _45544).
Proof. exact (TRANS (@lem3922840 _100977 _45543 _45544) (@lem3922845 _100977 _45543 _45544)). Qed.
Lemma lem3922862 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term100 _100977 _45543 _45544) = (term114 _100977 _45543 _45544).
Proof. exact (TRANS (@lem3922818 _100977 _45543 _45544) (@lem3922861 _100977 _45543 _45544)). Qed.
Lemma lem3922863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3922864 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term115 _100977 _45543 _45544) = (term116 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922863) (@lem3922862 _100977 _45543 _45544)). Qed.
Lemma lem3922878 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3922879 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term68 _100977 _45543 _45544) = (term117 _100977 _45543 _45544).
Proof. exact (@lem3922878 (term102 _100977 _45544) (term101 _100977 _45543 _45544)). Qed.
Lemma lem3922885 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term118 _100977 _45543 _45544) = (term118 _100977 _45543 _45544).
Proof. exact (eq_refl (term118 _100977 _45543 _45544)). Qed.
Lemma lem3922886 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term119 _100977 _45543 _45544) = (term114 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922885 _100977 _45543 _45544) (@lem3922879 _100977 _45543 _45544)). Qed.
Lemma lem3922897 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : ((term100 _100977 _45543 _45544) = (term119 _100977 _45543 _45544)) = ((term114 _100977 _45543 _45544) = (term114 _100977 _45543 _45544)).
Proof. exact (MK_COMB (@lem3922864 _100977 _45543 _45544) (@lem3922886 _100977 _45543 _45544)). Qed.
Lemma lem3922899 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3922900 (x : Prop) : (x = x) = True.
Proof. exact (@lem3922899 Prop x). Qed.
Lemma lem3922901 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : ((term114 _100977 _45543 _45544) = (term114 _100977 _45543 _45544)) = True.
Proof. exact (@lem3922900 (term114 _100977 _45543 _45544)). Qed.
Lemma lem3922902 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : ((term100 _100977 _45543 _45544) = (term119 _100977 _45543 _45544)) = True.
Proof. exact (TRANS (@lem3922897 _100977 _45543 _45544) (@lem3922901 _100977 _45543 _45544)). Qed.
Lemma lem3922903 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : True = ((term100 _100977 _45543 _45544) = (term119 _100977 _45543 _45544)).
Proof. exact (SYM (@lem3922902 _100977 _45543 _45544)). Qed.
Lemma lem3922904 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term100 _100977 _45543 _45544) = (term119 _100977 _45543 _45544).
Proof. exact (EQ_MP (@lem3922903 _100977 _45543 _45544) (@lem0)). Qed.
Lemma lem3922905 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) (h1 : term12 _100977) : term119 _100977 _45543 _45544.
Proof. exact (EQ_MP (@lem3922904 _100977 _45543 _45544) (@lem3922597 _100977 _45543 _45544 h1)). Qed.
Lemma lem3922907 (b : Prop) (a : Prop) : (a \/ b) = (term120 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3922908 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term119 _100977 _45543 _45544) = (term121 _100977 _45543 _45544).
Proof. exact (@lem3922907 (term68 _100977 _45543 _45544) (term46 _100977 _45543 _45544)). Qed.
Lemma lem3922910 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3922911 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term124 _100977 _45543 _45544) = (term125 _100977 _45543 _45544).
Proof. exact (@lem3922910 (term101 _100977 _45543 _45544) (term102 _100977 _45544)). Qed.
Lemma lem3922913 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3922914 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term127 _100977 _45543 _45544) = (@PSUBSET _100977 _45543 _45544).
Proof. exact (@lem3922913 (@PSUBSET _100977 _45543 _45544)). Qed.
Lemma lem3922915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3922916 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term128 _100977 _45543 _45544) = (term129 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922915) (@lem3922914 _100977 _45543 _45544)). Qed.
Lemma lem3922918 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3922919 {_100977 : Type'} (_45544 : _100977 -> Prop) : (term130 _100977 _45544) = (@FINITE _100977 _45544).
Proof. exact (@lem3922918 (@FINITE _100977 _45544)). Qed.
Lemma lem3922920 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term125 _100977 _45543 _45544) = (term73 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922916 _100977 _45543 _45544) (@lem3922919 _100977 _45544)). Qed.
Lemma lem3922921 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term124 _100977 _45543 _45544) = (term73 _100977 _45543 _45544).
Proof. exact (TRANS (@lem3922911 _100977 _45543 _45544) (@lem3922920 _100977 _45543 _45544)). Qed.
Lemma lem3922922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3922923 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term131 _100977 _45543 _45544) = (term132 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922922) (@lem3922921 _100977 _45543 _45544)). Qed.
Lemma lem3922924 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term46 _100977 _45543 _45544) = (term46 _100977 _45543 _45544).
Proof. exact (eq_refl (term46 _100977 _45543 _45544)). Qed.
Lemma lem3922925 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term121 _100977 _45543 _45544) = (term33 _100977 _45543 _45544).
Proof. exact (MK_COMB (@lem3922923 _100977 _45543 _45544) (@lem3922924 _100977 _45543 _45544)). Qed.
Lemma lem3922926 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) : (term119 _100977 _45543 _45544) = (term33 _100977 _45543 _45544).
Proof. exact (TRANS (@lem3922908 _100977 _45543 _45544) (@lem3922925 _100977 _45543 _45544)). Qed.
Lemma lem3922928 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) (h2 : term93 _100977 a b) : term73 _100977 a b.
Proof. exact (conj (@lem3922804 _100977 a b h2) (@lem3922811 _100977 a b h1)). Qed.
Lemma lem3922930 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) (h1 : term12 _100977) : term33 _100977 _45543 _45544.
Proof. exact (EQ_MP (@lem3922926 _100977 _45543 _45544) (@lem3922905 _100977 _45543 _45544 h1)). Qed.
Lemma lem3922931 {_100977 : Type'} (_45543 : _100977 -> Prop) (_45544 : _100977 -> Prop) (h1 : term12 _100977) : term33 _100977 _45543 _45544.
Proof. exact (@lem3922930 _100977 _45543 _45544 h1). Qed.
Lemma lem3922932 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) : term33 _100977 a b.
Proof. exact (@lem3922931 _100977 a b h1). Qed.
Lemma lem3922935 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term49 _100977 a b) (h3 : term93 _100977 a b) : term46 _100977 a b.
Proof. exact (@lem3922932 _100977 a b h1 (@lem3922928 _100977 a b h2 h3)). Qed.
Lemma lem3922936 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term49 _100977 a b) (h3 : term93 _100977 a b) : term133 _100977 a b.
Proof. exact (fun h0 : term103 _100977 a b => @lem3922935 _100977 a b h1 h2 h3). Qed.
Lemma lem3922938 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3922939 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term133 _100977 a b) = (term46 _100977 a b).
Proof. exact (@lem3922938 (term46 _100977 a b)). Qed.
Lemma lem3922940 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term49 _100977 a b) (h3 : term93 _100977 a b) : term46 _100977 a b.
Proof. exact (EQ_MP (@lem3922939 _100977 a b) (@lem3922936 _100977 a b h1 h2 h3)). Qed.
Lemma lem3922943 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3922945 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term103 _100977 a b) = (term134 _100977 a b).
Proof. exact (@lem3922943 (term46 _100977 a b)). Qed.
Lemma lem3922948 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term93 _100977 a b) : term134 _100977 a b.
Proof. exact (EQ_MP (@lem3922945 _100977 a b) (@lem3922629 _100977 a b h1)). Qed.
Lemma lem3922951 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term49 _100977 a b) (h3 : term93 _100977 a b) : False.
Proof. exact (@lem3922948 _100977 a b h3 (@lem3922940 _100977 a b h1 h2 h3)). Qed.
Lemma lem3922952 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term49 _100977 a b) (h3 : term93 _100977 a b) : term135.
Proof. exact (fun h0 : ~ False => @lem3922951 _100977 a b h1 h2 h3). Qed.
Lemma lem3922954 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3922955 : term135 = False.
Proof. exact (@lem3922954 False). Qed.
Lemma lem3922956 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term49 _100977 a b) (h3 : term93 _100977 a b) : False.
Proof. exact (EQ_MP (@lem3922955) (@lem3922952 _100977 a b h1 h2 h3)). Qed.
Lemma lem3923038 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem3923039 (_45596 : nat) (_45598 : nat) (h1 : _45596 = _45598) : _45596 = _45598.
Proof. exact (h1). Qed.
Lemma lem3923040 (_45597 : nat) (_45599 : nat) (h1 : _45597 = _45599) : _45597 = _45599.
Proof. exact (h1). Qed.
Lemma lem3923041 (_45596 : nat) (_45598 : nat) (h1 : _45596 = _45598) : (Peano.lt _45596) = (Peano.lt _45598).
Proof. exact (MK_COMB (@lem3923038) (@lem3923039 _45596 _45598 h1)). Qed.
Lemma lem3923042 (_45596 : nat) (_45598 : nat) (_45597 : nat) (_45599 : nat) (h1 : _45596 = _45598) (h2 : _45597 = _45599) : (Peano.lt _45596 _45597) = (Peano.lt _45598 _45599).
Proof. exact (MK_COMB (@lem3923041 _45596 _45598 h1) (@lem3923040 _45597 _45599 h2)). Qed.
Lemma lem3923044 (b : Prop) (a : Prop) : term136 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3923045 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : term137 _45598 _45599 _45596 _45597.
Proof. exact (@lem3923044 (Peano.lt _45598 _45599) (Peano.lt _45596 _45597)). Qed.
Lemma lem3923046 (_45596 : nat) (_45598 : nat) (_45597 : nat) (_45599 : nat) (h1 : _45596 = _45598) (h2 : _45597 = _45599) : term138 _45598 _45599 _45596 _45597.
Proof. exact (@lem3923045 _45598 _45599 _45596 _45597 (@lem3923042 _45596 _45598 _45597 _45599 h1 h2)). Qed.
Lemma lem3923047 (_45599 : nat) (_45597 : nat) (_45596 : nat) (_45598 : nat) (h1 : _45596 = _45598) : term139 _45598 _45599 _45596 _45597.
Proof. exact (fun h0 : _45597 = _45599 => @lem3923046 _45596 _45598 _45597 _45599 h1 h0). Qed.
Lemma lem3923049 (a : Prop) (b : Prop) : (a -> b) = (term140 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3923050 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term139 _45598 _45599 _45596 _45597) = (term141 _45598 _45599 _45596 _45597).
Proof. exact (@lem3923049 (_45597 = _45599) (term138 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923051 (_45599 : nat) (_45597 : nat) (_45596 : nat) (_45598 : nat) (h1 : _45596 = _45598) : term141 _45598 _45599 _45596 _45597.
Proof. exact (EQ_MP (@lem3923050 _45598 _45599 _45596 _45597) (@lem3923047 _45599 _45597 _45596 _45598 h1)). Qed.
Lemma lem3923052 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : term142 _45598 _45599 _45596 _45597.
Proof. exact (fun h0 : _45596 = _45598 => @lem3923051 _45599 _45597 _45596 _45598 h0). Qed.
Lemma lem3923054 (a : Prop) (b : Prop) : (a -> b) = (term140 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3923055 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term142 _45598 _45599 _45596 _45597) = (term143 _45598 _45599 _45596 _45597).
Proof. exact (@lem3923054 (_45596 = _45598) (term141 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923056 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : term143 _45598 _45599 _45596 _45597.
Proof. exact (EQ_MP (@lem3923055 _45598 _45599 _45596 _45597) (@lem3923052 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923080 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : @SUBSET _100977 a b.
Proof. exact (proj2 (@lem3922355 _100977 a b h1)). Qed.
Lemma lem3923081 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : term144 _100977 a b.
Proof. exact (fun h0 : term105 _100977 a b => @lem3923080 _100977 a b h1). Qed.
Lemma lem3923083 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923084 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term144 _100977 a b) = (@SUBSET _100977 a b).
Proof. exact (@lem3923083 (@SUBSET _100977 a b)). Qed.
Lemma lem3923085 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term49 _100977 a b) : @SUBSET _100977 a b.
Proof. exact (EQ_MP (@lem3923084 _100977 a b) (@lem3923081 _100977 a b h1)). Qed.
Lemma lem3923087 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3923088 {_100977 : Type'} (b : _100977 -> Prop) : (@CARD _100977 b) = (@CARD _100977 b).
Proof. exact (@lem3923087 (@CARD _100977 b)). Qed.
Lemma lem3923089 {_100977 : Type'} (b : _100977 -> Prop) : term145 _100977 b.
Proof. exact (fun h0 : term146 _100977 b => @lem3923088 _100977 b). Qed.
Lemma lem3923091 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923092 {_100977 : Type'} (b : _100977 -> Prop) : (term145 _100977 b) = ((@CARD _100977 b) = (@CARD _100977 b)).
Proof. exact (@lem3923091 ((@CARD _100977 b) = (@CARD _100977 b))). Qed.
Lemma lem3923093 {_100977 : Type'} (b : _100977 -> Prop) : (@CARD _100977 b) = (@CARD _100977 b).
Proof. exact (EQ_MP (@lem3923092 _100977 b) (@lem3923089 _100977 b)). Qed.
Lemma lem3923095 (_45549 : nat) (h1 : term39) : term37 _45549.
Proof. exact (EQ_MP (@lem3922564 _45549) (@lem3922563 _45549 h1)). Qed.
Lemma lem3923096 {_100977 : Type'} (b : _100977 -> Prop) (h1 : term39) : term147 _100977 b.
Proof. exact (@lem3923095 (@CARD _100977 b) h1). Qed.
Lemma lem3923097 {_100977 : Type'} (b : _100977 -> Prop) (h1 : term39) : term148 _100977 b.
Proof. exact (fun h0 : term149 _100977 b => @lem3923096 _100977 b h1). Qed.
Lemma lem3923099 (p : Prop) : (term150 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3923100 {_100977 : Type'} (b : _100977 -> Prop) : (term148 _100977 b) = (term147 _100977 b).
Proof. exact (@lem3923099 (term149 _100977 b)). Qed.
Lemma lem3923101 {_100977 : Type'} (b : _100977 -> Prop) (h1 : term39) : term147 _100977 b.
Proof. exact (EQ_MP (@lem3923100 _100977 b) (@lem3923097 _100977 b h1)). Qed.
Lemma lem3923103 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term94 _100977 a b) : term46 _100977 a b.
Proof. exact (proj2 (@lem3922359 _100977 a b h1)). Qed.
Lemma lem3923104 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term94 _100977 a b) : term133 _100977 a b.
Proof. exact (fun h0 : term103 _100977 a b => @lem3923103 _100977 a b h1). Qed.
Lemma lem3923106 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923107 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term133 _100977 a b) = (term46 _100977 a b).
Proof. exact (@lem3923106 (term46 _100977 a b)). Qed.
Lemma lem3923108 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term94 _100977 a b) : term46 _100977 a b.
Proof. exact (EQ_MP (@lem3923107 _100977 a b) (@lem3923104 _100977 a b h1)). Qed.
Lemma lem3923110 (b : Prop) (a : Prop) : (a \/ b) = (term120 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3923111 (_45599 : nat) (_45597 : nat) (_45596 : nat) (_45598 : nat) : (term143 _45598 _45599 _45596 _45597) = (term151 _45599 _45597 _45596 _45598).
Proof. exact (@lem3923110 (term141 _45598 _45599 _45596 _45597) (term152 _45596 _45598)). Qed.
Lemma lem3923113 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3923114 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term153 _45598 _45599 _45596 _45597) = (term154 _45598 _45599 _45596 _45597).
Proof. exact (@lem3923113 (term152 _45597 _45599) (term138 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923116 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3923117 (_45597 : nat) (_45599 : nat) : (term155 _45597 _45599) = (_45597 = _45599).
Proof. exact (@lem3923116 (_45597 = _45599)). Qed.
Lemma lem3923118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3923119 (_45597 : nat) (_45599 : nat) : (term156 _45597 _45599) = (term157 _45597 _45599).
Proof. exact (MK_COMB (@lem3923118) (@lem3923117 _45597 _45599)). Qed.
Lemma lem3923121 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3923122 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term158 _45598 _45599 _45596 _45597) = (term159 _45598 _45599 _45596 _45597).
Proof. exact (@lem3923121 (Peano.lt _45598 _45599) (term160 _45596 _45597)). Qed.
Lemma lem3923124 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3923125 (_45596 : nat) (_45597 : nat) : (term161 _45596 _45597) = (Peano.lt _45596 _45597).
Proof. exact (@lem3923124 (Peano.lt _45596 _45597)). Qed.
Lemma lem3923126 (_45598 : nat) (_45599 : nat) : (term162 _45598 _45599) = (term162 _45598 _45599).
Proof. exact (eq_refl (term162 _45598 _45599)). Qed.
Lemma lem3923127 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term159 _45598 _45599 _45596 _45597) = (term163 _45598 _45599 _45596 _45597).
Proof. exact (MK_COMB (@lem3923126 _45598 _45599) (@lem3923125 _45596 _45597)). Qed.
Lemma lem3923128 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term158 _45598 _45599 _45596 _45597) = (term163 _45598 _45599 _45596 _45597).
Proof. exact (TRANS (@lem3923122 _45598 _45599 _45596 _45597) (@lem3923127 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923129 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term154 _45598 _45599 _45596 _45597) = (term164 _45598 _45599 _45596 _45597).
Proof. exact (MK_COMB (@lem3923119 _45597 _45599) (@lem3923128 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923130 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term153 _45598 _45599 _45596 _45597) = (term164 _45598 _45599 _45596 _45597).
Proof. exact (TRANS (@lem3923114 _45598 _45599 _45596 _45597) (@lem3923129 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3923132 (_45598 : nat) (_45599 : nat) (_45596 : nat) (_45597 : nat) : (term165 _45598 _45599 _45596 _45597) = (term166 _45598 _45599 _45596 _45597).
Proof. exact (MK_COMB (@lem3923131) (@lem3923130 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923133 (_45596 : nat) (_45598 : nat) : (term152 _45596 _45598) = (term152 _45596 _45598).
Proof. exact (eq_refl (term152 _45596 _45598)). Qed.
Lemma lem3923134 (_45599 : nat) (_45597 : nat) (_45596 : nat) (_45598 : nat) : (term151 _45599 _45597 _45596 _45598) = (term167 _45599 _45597 _45596 _45598).
Proof. exact (MK_COMB (@lem3923132 _45598 _45599 _45596 _45597) (@lem3923133 _45596 _45598)). Qed.
Lemma lem3923135 (_45599 : nat) (_45597 : nat) (_45596 : nat) (_45598 : nat) : (term143 _45598 _45599 _45596 _45597) = (term167 _45599 _45597 _45596 _45598).
Proof. exact (TRANS (@lem3923111 _45599 _45597 _45596 _45598) (@lem3923134 _45599 _45597 _45596 _45598)). Qed.
Lemma lem3923137 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term39) (h2 : term94 _100977 a b) : term168 _100977 a b.
Proof. exact (conj (@lem3923101 _100977 b h1) (@lem3923108 _100977 a b h2)). Qed.
Lemma lem3923138 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term39) (h2 : term94 _100977 a b) : term169 _100977 a b.
Proof. exact (conj (@lem3923093 _100977 b) (@lem3923137 _100977 a b h1 h2)). Qed.
Lemma lem3923140 (_45599 : nat) (_45597 : nat) (_45596 : nat) (_45598 : nat) : term167 _45599 _45597 _45596 _45598.
Proof. exact (EQ_MP (@lem3923135 _45599 _45597 _45596 _45598) (@lem3923056 _45598 _45599 _45596 _45597)). Qed.
Lemma lem3923141 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : term170 _100977 a b.
Proof. exact (@lem3923140 (@CARD _100977 b) (@CARD _100977 b) (@CARD _100977 a) (@CARD _100977 b)). Qed.
Lemma lem3923144 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term39) (h2 : term94 _100977 a b) : term83 _100977 a b.
Proof. exact (@lem3923141 _100977 a b (@lem3923138 _100977 a b h1 h2)). Qed.
Lemma lem3923145 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term39) (h2 : term94 _100977 a b) : term171 _100977 a b.
Proof. exact (fun h0 : (@CARD _100977 a) = (@CARD _100977 b) => @lem3923144 _100977 a b h1 h2). Qed.
Lemma lem3923147 (p : Prop) : (term150 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3923148 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term171 _100977 a b) = (term83 _100977 a b).
Proof. exact (@lem3923147 ((@CARD _100977 a) = (@CARD _100977 b))). Qed.
Lemma lem3923149 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term39) (h2 : term94 _100977 a b) : term83 _100977 a b.
Proof. exact (EQ_MP (@lem3923148 _100977 a b) (@lem3923145 _100977 a b h1 h2)). Qed.
Lemma lem3923155 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3923156 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term104 _100977 _45554 _45555) = (term172 _100977 _45554 _45555).
Proof. exact (@lem3923155 ((@CARD _100977 _45554) = (@CARD _100977 _45555)) (term105 _100977 _45554 _45555) (@PSUBSET _100977 _45554 _45555)). Qed.
Lemma lem3923172 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3923173 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term173 _100977 _45554 _45555) = (term174 _100977 _45554 _45555).
Proof. exact (@lem3923172 (@PSUBSET _100977 _45554 _45555) (term105 _100977 _45554 _45555)). Qed.
Lemma lem3923179 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term175 _100977 _45554 _45555) = (term175 _100977 _45554 _45555).
Proof. exact (eq_refl (term175 _100977 _45554 _45555)). Qed.
Lemma lem3923180 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term172 _100977 _45554 _45555) = (term176 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923179 _100977 _45554 _45555) (@lem3923173 _100977 _45554 _45555)). Qed.
Lemma lem3923191 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term104 _100977 _45554 _45555) = (term176 _100977 _45554 _45555).
Proof. exact (TRANS (@lem3923156 _100977 _45554 _45555) (@lem3923180 _100977 _45554 _45555)). Qed.
Lemma lem3923192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3923193 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term177 _100977 _45554 _45555) = (term178 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923192) (@lem3923191 _100977 _45554 _45555)). Qed.
Lemma lem3923207 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3923208 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term81 _100977 _45554 _45555) = (term179 _100977 _45554 _45555).
Proof. exact (@lem3923207 ((@CARD _100977 _45554) = (@CARD _100977 _45555)) (term105 _100977 _45554 _45555)). Qed.
Lemma lem3923216 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term180 _100977 _45554 _45555) = (term180 _100977 _45554 _45555).
Proof. exact (eq_refl (term180 _100977 _45554 _45555)). Qed.
Lemma lem3923217 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term181 _100977 _45554 _45555) = (term182 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923216 _100977 _45554 _45555) (@lem3923208 _100977 _45554 _45555)). Qed.
Lemma lem3923221 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3923222 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term182 _100977 _45554 _45555) = (term176 _100977 _45554 _45555).
Proof. exact (@lem3923221 ((@CARD _100977 _45554) = (@CARD _100977 _45555)) (@PSUBSET _100977 _45554 _45555) (term105 _100977 _45554 _45555)). Qed.
Lemma lem3923240 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term181 _100977 _45554 _45555) = (term176 _100977 _45554 _45555).
Proof. exact (TRANS (@lem3923217 _100977 _45554 _45555) (@lem3923222 _100977 _45554 _45555)). Qed.
Lemma lem3923241 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : ((term104 _100977 _45554 _45555) = (term181 _100977 _45554 _45555)) = ((term176 _100977 _45554 _45555) = (term176 _100977 _45554 _45555)).
Proof. exact (MK_COMB (@lem3923193 _100977 _45554 _45555) (@lem3923240 _100977 _45554 _45555)). Qed.
Lemma lem3923243 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3923244 (x : Prop) : (x = x) = True.
Proof. exact (@lem3923243 Prop x). Qed.
Lemma lem3923245 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : ((term176 _100977 _45554 _45555) = (term176 _100977 _45554 _45555)) = True.
Proof. exact (@lem3923244 (term176 _100977 _45554 _45555)). Qed.
Lemma lem3923246 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : ((term104 _100977 _45554 _45555) = (term181 _100977 _45554 _45555)) = True.
Proof. exact (TRANS (@lem3923241 _100977 _45554 _45555) (@lem3923245 _100977 _45554 _45555)). Qed.
Lemma lem3923247 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : True = ((term104 _100977 _45554 _45555) = (term181 _100977 _45554 _45555)).
Proof. exact (SYM (@lem3923246 _100977 _45554 _45555)). Qed.
Lemma lem3923248 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term104 _100977 _45554 _45555) = (term181 _100977 _45554 _45555).
Proof. exact (EQ_MP (@lem3923247 _100977 _45554 _45555) (@lem0)). Qed.
Lemma lem3923249 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) (h1 : term11 _100977) : term181 _100977 _45554 _45555.
Proof. exact (EQ_MP (@lem3923248 _100977 _45554 _45555) (@lem3922667 _100977 _45554 _45555 h1)). Qed.
Lemma lem3923251 (b : Prop) (a : Prop) : (a \/ b) = (term120 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3923252 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term181 _100977 _45554 _45555) = (term183 _100977 _45554 _45555).
Proof. exact (@lem3923251 (term81 _100977 _45554 _45555) (@PSUBSET _100977 _45554 _45555)). Qed.
Lemma lem3923254 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3923255 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term184 _100977 _45554 _45555) = (term185 _100977 _45554 _45555).
Proof. exact (@lem3923254 (term105 _100977 _45554 _45555) ((@CARD _100977 _45554) = (@CARD _100977 _45555))). Qed.
Lemma lem3923257 (a : Prop) : (term126 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3923258 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term186 _100977 _45554 _45555) = (@SUBSET _100977 _45554 _45555).
Proof. exact (@lem3923257 (@SUBSET _100977 _45554 _45555)). Qed.
Lemma lem3923259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3923260 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term187 _100977 _45554 _45555) = (term188 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923259) (@lem3923258 _100977 _45554 _45555)). Qed.
Lemma lem3923261 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term83 _100977 _45554 _45555) = (term83 _100977 _45554 _45555).
Proof. exact (eq_refl (term83 _100977 _45554 _45555)). Qed.
Lemma lem3923262 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term185 _100977 _45554 _45555) = (term88 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923260 _100977 _45554 _45555) (@lem3923261 _100977 _45554 _45555)). Qed.
Lemma lem3923263 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term184 _100977 _45554 _45555) = (term88 _100977 _45554 _45555).
Proof. exact (TRANS (@lem3923255 _100977 _45554 _45555) (@lem3923262 _100977 _45554 _45555)). Qed.
Lemma lem3923264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3923265 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term189 _100977 _45554 _45555) = (term190 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923264) (@lem3923263 _100977 _45554 _45555)). Qed.
Lemma lem3923266 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (@PSUBSET _100977 _45554 _45555) = (@PSUBSET _100977 _45554 _45555).
Proof. exact (eq_refl (@PSUBSET _100977 _45554 _45555)). Qed.
Lemma lem3923267 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term183 _100977 _45554 _45555) = (term29 _100977 _45554 _45555).
Proof. exact (MK_COMB (@lem3923265 _100977 _45554 _45555) (@lem3923266 _100977 _45554 _45555)). Qed.
Lemma lem3923268 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) : (term181 _100977 _45554 _45555) = (term29 _100977 _45554 _45555).
Proof. exact (TRANS (@lem3923252 _100977 _45554 _45555) (@lem3923267 _100977 _45554 _45555)). Qed.
Lemma lem3923270 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term39) (h2 : term94 _100977 a b) (h3 : term49 _100977 a b) : term88 _100977 a b.
Proof. exact (conj (@lem3923085 _100977 a b h3) (@lem3923149 _100977 a b h1 h2)). Qed.
Lemma lem3923272 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) (h1 : term11 _100977) : term29 _100977 _45554 _45555.
Proof. exact (EQ_MP (@lem3923268 _100977 _45554 _45555) (@lem3923249 _100977 _45554 _45555 h1)). Qed.
Lemma lem3923273 {_100977 : Type'} (_45554 : _100977 -> Prop) (_45555 : _100977 -> Prop) (h1 : term11 _100977) : term29 _100977 _45554 _45555.
Proof. exact (@lem3923272 _100977 _45554 _45555 h1). Qed.
Lemma lem3923274 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) : term29 _100977 a b.
Proof. exact (@lem3923273 _100977 a b h1). Qed.
Lemma lem3923277 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : @PSUBSET _100977 a b.
Proof. exact (@lem3923274 _100977 a b h1 (@lem3923270 _100977 a b h2 h3 h4)). Qed.
Lemma lem3923278 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : term106 _100977 a b.
Proof. exact (fun h0 : term101 _100977 a b => @lem3923277 _100977 a b h1 h2 h3 h4). Qed.
Lemma lem3923280 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923281 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term106 _100977 a b) = (@PSUBSET _100977 a b).
Proof. exact (@lem3923280 (@PSUBSET _100977 a b)). Qed.
Lemma lem3923282 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : @PSUBSET _100977 a b.
Proof. exact (EQ_MP (@lem3923281 _100977 a b) (@lem3923278 _100977 a b h1 h2 h3 h4)). Qed.
Lemma lem3923285 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923287 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) : (term101 _100977 a b) = (term191 _100977 a b).
Proof. exact (@lem3923285 (@PSUBSET _100977 a b)). Qed.
Lemma lem3923290 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term94 _100977 a b) : term191 _100977 a b.
Proof. exact (EQ_MP (@lem3923287 _100977 a b) (@lem3922673 _100977 a b h1)). Qed.
Lemma lem3923293 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : False.
Proof. exact (@lem3923290 _100977 a b h3 (@lem3923282 _100977 a b h1 h2 h3 h4)). Qed.
Lemma lem3923294 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : term135.
Proof. exact (fun h0 : ~ False => @lem3923293 _100977 a b h1 h2 h3 h4). Qed.
Lemma lem3923296 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923297 : term135 = False.
Proof. exact (@lem3923296 False). Qed.
Lemma lem3923298 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : False.
Proof. exact (EQ_MP (@lem3923297) (@lem3923294 _100977 a b h1 h2 h3 h4)). Qed.
Lemma lem3923299 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : term39 = False.
Proof. exact (prop_ext (fun h5 : term39 => @lem3923298 _100977 a b h1 h2 h3 h4) (fun h5 : False => @lem3922459 h2)). Qed.
Lemma lem3923300 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term11 _100977) (h2 : term39) (h3 : term94 _100977 a b) (h4 : term49 _100977 a b) : False.
Proof. exact (EQ_MP (@lem3923299 _100977 a b h1 h2 h3 h4) (@lem3922459 h2)). Qed.
Lemma lem3923301 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term49 _100977 a b) : False.
Proof. exact (or_elim (@lem3922354 _100977 a b h4) (fun h0 : term93 _100977 a b => @lem3922956 _100977 a b h1 h4 h0) (fun h0 : term94 _100977 a b => @lem3923300 _100977 a b h2 h3 h0 h4)). Qed.
Lemma lem3923302 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term49 _100977 a b) : (term49 _100977 a b) = False.
Proof. exact (prop_ext (fun h5 : term49 _100977 a b => @lem3923301 _100977 a b h1 h2 h3 h4) (fun h5 : False => @lem3922353 _100977 a b h4)). Qed.
Lemma lem3923303 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term49 _100977 a b) : False.
Proof. exact (EQ_MP (@lem3923302 _100977 a b h1 h2 h3 h4) (@lem3922353 _100977 a b h4)). Qed.
Lemma lem3923304 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term49 _100977 a b) : term39 = False.
Proof. exact (prop_ext (fun h5 : term39 => @lem3923303 _100977 a b h1 h2 h3 h4) (fun h5 : False => @lem3922195 h3)). Qed.
Lemma lem3923305 {_100977 : Type'} (a : _100977 -> Prop) (b : _100977 -> Prop) (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term49 _100977 a b) : False.
Proof. exact (EQ_MP (@lem3923304 _100977 a b h1 h2 h3 h4) (@lem3922195 h3)). Qed.
Lemma lem3923306 {_100977 : Type'} (a : _100977 -> Prop) (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term60 _100977 a) : False.
Proof. exact (ex_elim (@lem3922183 _100977 a h4) (fun b : _100977 -> Prop => fun h0 : term59 _100977 a b => @lem3923305 _100977 a b h1 h2 h3 h0)). Qed.
Lemma lem3923307 {_100977 : Type'} (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term10 _100977) : False.
Proof. exact (ex_elim (@lem3921939 _100977 h4) (fun a : _100977 -> Prop => fun h0 : term65 _100977 a => @lem3923306 _100977 a h1 h2 h3 h0)). Qed.
Lemma lem3923308 {_100977 : Type'} (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term10 _100977) : term39 = False.
Proof. exact (prop_ext (fun h5 : term39 => @lem3923307 _100977 h1 h2 h3 h4) (fun h5 : False => @lem3921952 h3)). Qed.
Lemma lem3923309 {_100977 : Type'} (h1 : term12 _100977) (h2 : term11 _100977) (h3 : term39) (h4 : term10 _100977) : False.
Proof. exact (EQ_MP (@lem3923308 _100977 h1 h2 h3 h4) (@lem3921952 h3)). Qed.
Lemma lem3923310 {_100977 : Type'} (h1 : term12 _100977) (h2 : term39) (h3 : term10 _100977) : term17 _100977.
Proof. exact (fun h0 : term11 _100977 => @lem3923309 _100977 h1 h0 h2 h3). Qed.
Lemma lem3923311 {_100977 : Type'} : (term17 _100977) = (term18 _100977).
Proof. exact (@lem69 (term11 _100977)). Qed.
Lemma lem3923312 {_100977 : Type'} (h1 : term12 _100977) (h2 : term39) (h3 : term10 _100977) : term18 _100977.
Proof. exact (EQ_MP (@lem3923311 _100977) (@lem3923310 _100977 h1 h2 h3)). Qed.
Lemma lem3923313 {_100977 A : Type'} (h1 : term12 _100977) (h2 : term39) (h3 : term10 _100977) : term21 _100977 A.
Proof. exact (fun h0 : term12 A => @lem3923312 _100977 h1 h2 h3). Qed.
Lemma lem3923314 {_100977 A : Type'} (h1 : term39) (h2 : term10 _100977) : term23 _100977 A.
Proof. exact (fun h0 : term12 _100977 => @lem3923313 _100977 A h0 h1 h2). Qed.
Lemma lem3923315 {_100977 A : Type'} (h1 : term10 _100977) : term26 _100977 A.
Proof. exact (fun h0 : term39 => @lem3923314 _100977 A h0 h1). Qed.
Lemma lem3923316 {_100977 A : Type'} : term28 _100977 A.
Proof. exact (fun h0 : term10 _100977 => @lem3923315 _100977 A h0). Qed.
Lemma lem3923317 {_100977 A : Type'} : term13 _100977 A.
Proof. exact (EQ_MP (@lem3921832 _100977 A) (@lem3923316 _100977 A)). Qed.
Lemma lem3923319 {_100977 A : Type'} : term13 _100977 A.
Proof. exact (@lem3921579 _100977 A (@lem3923317 _100977 A)). Qed.
Lemma lem3923320 {_100977 A : Type'} (h1 : term10 _100977) : term25 _100977 A.
Proof. exact (@lem3923319 _100977 A (@lem3921557 _100977 h1)). Qed.
Lemma lem3923321 {_100977 A : Type'} (h1 : term10 _100977) : term22 _100977 A.
Proof. exact (@lem3923320 _100977 A h1 (@lem91686)). Qed.
Lemma lem3923322 {_100977 A : Type'} (h1 : term10 _100977) : term20 _100977 A.
Proof. exact (@lem3923321 _100977 A h1 (@lem3921561 _100977)). Qed.
Lemma lem3923323 {_100977 : Type'} (h1 : term10 _100977) : term17 _100977.
Proof. exact (@lem3923322 _100977 Prop h1 (@lem3921097 Prop)). Qed.
Lemma lem3923324 {_100977 : Type'} (h1 : term10 _100977) : False.
Proof. exact (@lem3923323 _100977 h1 (@lem3921558 _100977)). Qed.
Lemma lem3923325 {_100977 : Type'} (h1 : term10 _100977) : (term10 _100977) = False.
Proof. exact (prop_ext (fun h2 : term10 _100977 => @lem3923324 _100977 h1) (fun h2 : False => @lem3921557 _100977 h1)). Qed.
Lemma lem3923326 {_100977 : Type'} (h1 : term10 _100977) : False.
Proof. exact (EQ_MP (@lem3923325 _100977 h1) (@lem3921557 _100977 h1)). Qed.
Lemma lem3923327 {_100977 : Type'} : term9 _100977.
Proof. exact (fun h0 : term10 _100977 => @lem3923326 _100977 h0). Qed.
Lemma lem3923328 {_100977 : Type'} : term8 _100977.
Proof. exact (EQ_MP (@lem3921556 _100977) (@lem3923327 _100977)). Qed.
