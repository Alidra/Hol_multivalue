Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LIST_OF_SET_SING_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import CONS_11_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_EMPTY_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NOT_SUC_spec.
Require Import SELECT_UNIQUE_spec.
Require Import SUC_INJ_spec.
Require Import list_INDUCT_spec.
Require Import list_of_set_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4790664 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem4790665 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem4790666 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem4790665 n) (@lem4790664 n)). Qed.
Lemma lem4790667 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem4790680 {A : Type'} (h : A) : term3 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem4790681 {A : Type'} (h : A) : (term3 A h) = (term4 A h).
Proof. exact (eq_refl (term3 A h)). Qed.
Lemma lem4790682 {A : Type'} (h : A) : term4 A h.
Proof. exact (EQ_MP (@lem4790681 A h) (@lem4790680 A h)). Qed.
Lemma lem4790683 {A : Type'} (h : A) (t : list A) : term5 A h t.
Proof. exact (@lem4790682 A h t). Qed.
Lemma lem4790684 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (eq_refl (term5 A h t)). Qed.
Lemma lem4790685 {A : Type'} (h : A) (t : list A) : term6 A h t.
Proof. exact (EQ_MP (@lem4790684 A h t) (@lem4790683 A h t)). Qed.
Lemma lem4790686 {A : Type'} (h : A) (t : list A) : term7 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem4790699 (m : nat) : term8 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem4790700 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem4790701 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem4790700 m) (@lem4790699 m)). Qed.
Lemma lem4790702 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem4790701 m n). Qed.
Lemma lem4790703 (m : nat) (n : nat) : (term10 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem4790705 {A : Type'} (h1' : A) : term11 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem4790706 {A : Type'} (h1' : A) : (term11 A h1') = (term12 A h1').
Proof. exact (eq_refl (term11 A h1')). Qed.
Lemma lem4790707 {A : Type'} (h1' : A) : term12 A h1'.
Proof. exact (EQ_MP (@lem4790706 A h1') (@lem4790705 A h1')). Qed.
Lemma lem4790708 {A : Type'} (h1' : A) (h2' : A) : term13 A h1' h2'.
Proof. exact (@lem4790707 A h1' h2'). Qed.
Lemma lem4790709 {A : Type'} (h1' : A) (h2' : A) : (term13 A h1' h2') = (term14 A h1' h2').
Proof. exact (eq_refl (term13 A h1' h2')). Qed.
Lemma lem4790710 {A : Type'} (h1' : A) (h2' : A) : term14 A h1' h2'.
Proof. exact (EQ_MP (@lem4790709 A h1' h2') (@lem4790708 A h1' h2')). Qed.
Lemma lem4790711 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term15 A h1' h2' t1.
Proof. exact (@lem4790710 A h1' h2' t1). Qed.
Lemma lem4790712 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term15 A h1' h2' t1) = (term16 A h1' h2' t1).
Proof. exact (eq_refl (term15 A h1' h2' t1)). Qed.
Lemma lem4790713 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term16 A h1' h2' t1.
Proof. exact (EQ_MP (@lem4790712 A h1' h2' t1) (@lem4790711 A h1' h2' t1)). Qed.
Lemma lem4790714 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term17 A h1' h2' t1 t2.
Proof. exact (@lem4790713 A h1' h2' t1 t2). Qed.
Lemma lem4790715 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term17 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term18 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term17 A h1' h2' t1 t2)). Qed.
Lemma lem4790719 {A : Type'} : term19 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem4790720 {A : Type'} (h : A) : term20 A h.
Proof. exact (@lem4790719 A h). Qed.
Lemma lem4790721 {A : Type'} (h : A) : (term20 A h) = (term21 A h).
Proof. exact (eq_refl (term20 A h)). Qed.
Lemma lem4790722 {A : Type'} (h : A) : term21 A h.
Proof. exact (EQ_MP (@lem4790721 A h) (@lem4790720 A h)). Qed.
Lemma lem4790723 {A : Type'} (h : A) (t : list A) : term22 A h t.
Proof. exact (@lem4790722 A h t). Qed.
Lemma lem4790724 {A : Type'} (h : A) (t : list A) : (term22 A h t) = ((term23 A h t) = (term24 A t)).
Proof. exact (eq_refl (term22 A h t)). Qed.
Lemma lem4790727 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem4790728 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem4790729 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem4790728 n) (@lem4790727 n)). Qed.
Lemma lem4790733 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem4790734 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem4790733 n h1)). Qed.
Lemma lem4790735 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem4790736 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem4790735 n h1)). Qed.
Lemma lem4790737 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem4790734 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem4790736 n h1)). Qed.
Lemma lem4790738 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4790739 (n : nat) : (term1 n) = (term25 n).
Proof. exact (MK_COMB (@lem4790738) (@lem4790737 n)). Qed.
Lemma lem4790740 (n : nat) : term25 n.
Proof. exact (EQ_MP (@lem4790739 n) (@lem4790729 n)). Qed.
Lemma lem4790741 (n : nat) : term26 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem4790743 {A : Type'} (x : A) : term27 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4790744 {A : Type'} (x : A) : (term27 A x) = (term28 A x).
Proof. exact (eq_refl (term27 A x)). Qed.
Lemma lem4790745 {A : Type'} (x : A) : term28 A x.
Proof. exact (EQ_MP (@lem4790744 A x) (@lem4790743 A x)). Qed.
Lemma lem4790746 {A : Type'} (x : A) : term29 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4790748 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4790750 {A : Type'} : term30 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4790751 {A : Type'} (x : A) : term31 A x.
Proof. exact (@lem4790750 A x). Qed.
Lemma lem4790752 {A : Type'} (x : A) : (term31 A x) = (term32 A x).
Proof. exact (eq_refl (term31 A x)). Qed.
Lemma lem4790753 {A : Type'} (x : A) : term32 A x.
Proof. exact (EQ_MP (@lem4790752 A x) (@lem4790751 A x)). Qed.
Lemma lem4790754 {A : Type'} (x : A) (s : A -> Prop) : term33 A x s.
Proof. exact (@lem4790753 A x s). Qed.
Lemma lem4790755 {A : Type'} (x : A) (s : A -> Prop) : (term33 A x s) = (term34 A x s).
Proof. exact (eq_refl (term33 A x s)). Qed.
Lemma lem4790756 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (EQ_MP (@lem4790755 A x s) (@lem4790754 A x s)). Qed.
Lemma lem4790757 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4790758 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term35 A x s) = (term36 A x s).
Proof. exact (@lem4790756 A x s (@lem4790757 A s h1)). Qed.
Lemma lem4790765 {A : Type'} : term19 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem4790766 {A : Type'} (h : A) : term20 A h.
Proof. exact (@lem4790765 A h). Qed.
Lemma lem4790767 {A : Type'} (h : A) : (term20 A h) = (term21 A h).
Proof. exact (eq_refl (term20 A h)). Qed.
Lemma lem4790768 {A : Type'} (h : A) : term21 A h.
Proof. exact (EQ_MP (@lem4790767 A h) (@lem4790766 A h)). Qed.
Lemma lem4790769 {A : Type'} (h : A) (t : list A) : term22 A h t.
Proof. exact (@lem4790768 A h t). Qed.
Lemma lem4790770 {A : Type'} (h : A) (t : list A) : (term22 A h t) = ((term23 A h t) = (term24 A t)).
Proof. exact (eq_refl (term22 A h t)). Qed.
Lemma lem4790773 {A : Type'} (h : A) : term3 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem4790774 {A : Type'} (h : A) : (term3 A h) = (term4 A h).
Proof. exact (eq_refl (term3 A h)). Qed.
Lemma lem4790775 {A : Type'} (h : A) : term4 A h.
Proof. exact (EQ_MP (@lem4790774 A h) (@lem4790773 A h)). Qed.
Lemma lem4790776 {A : Type'} (h : A) (t : list A) : term5 A h t.
Proof. exact (@lem4790775 A h t). Qed.
Lemma lem4790777 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (eq_refl (term5 A h t)). Qed.
Lemma lem4790778 {A : Type'} (h : A) (t : list A) : term6 A h t.
Proof. exact (EQ_MP (@lem4790777 A h t) (@lem4790776 A h t)). Qed.
Lemma lem4790782 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem4790783 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem4790782 A h t h1)). Qed.
Lemma lem4790784 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem4790785 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem4790784 A h t h1)). Qed.
Lemma lem4790786 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem4790783 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem4790785 A h t h1)). Qed.
Lemma lem4790787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4790788 {A : Type'} (h : A) (t : list A) : (term6 A h t) = (term37 A h t).
Proof. exact (MK_COMB (@lem4790787) (@lem4790786 A h t)). Qed.
Lemma lem4790789 {A : Type'} (h : A) (t : list A) : term37 A h t.
Proof. exact (EQ_MP (@lem4790788 A h t) (@lem4790778 A h t)). Qed.
Lemma lem4790790 {A : Type'} (h : A) (t : list A) : term38 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem4790792 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem4790793 {A : Type'} (P : type1143 A) (h1 : term39 A) : term40 A P.
Proof. exact (@lem4790792 A h1 P). Qed.
Lemma lem4790794 {A : Type'} (P : type1143 A) : (term40 A P) = (term41 A P).
Proof. exact (eq_refl (term40 A P)). Qed.
Lemma lem4790795 {A : Type'} (P : type1143 A) (h1 : term39 A) : term41 A P.
Proof. exact (EQ_MP (@lem4790794 A P) (@lem4790793 A P h1)). Qed.
Lemma lem4790796 {A : Type'} (P : type1143 A) (h1 : term42 A P) : term42 A P.
Proof. exact (h1). Qed.
Lemma lem4790797 {A : Type'} (P : type1143 A) (h1 : term39 A) (h2 : term42 A P) : term43 A P.
Proof. exact (@lem4790795 A P h1 (@lem4790796 A P h2)). Qed.
Lemma lem4790798 {A : Type'} (P : type1143 A) (h1 : term42 A P) : term44 A P.
Proof. exact (fun h0 : term39 A => @lem4790797 A P h0 h1). Qed.
Lemma lem4790799 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem4790800 {A : Type'} (P : type1143 A) (h1 : term39 A) (h2 : term42 A P) : term43 A P.
Proof. exact (@lem4790798 A P h2 (@lem4790799 A h1)). Qed.
Lemma lem4790801 {A : Type'} (P : type1143 A) (h1 : term39 A) : term41 A P.
Proof. exact (fun h0 : term42 A P => @lem4790800 A P h1 h0). Qed.
Lemma lem4790802 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (fun P : type1143 A => @lem4790801 A P h1). Qed.
Lemma lem4790803 {A : Type'} : term45 A.
Proof. exact (fun h0 : term39 A => @lem4790802 A h0). Qed.
Lemma lem4790804 {A : Type'} : term39 A.
Proof. exact (@lem4790803 A (@lem1071853 A)). Qed.
Lemma lem4790805 {A : Type'} (P : type1143 A) : term40 A P.
Proof. exact (@lem4790804 A P). Qed.
Lemma lem4790806 {A : Type'} (P : type1143 A) : (term40 A P) = (term41 A P).
Proof. exact (eq_refl (term40 A P)). Qed.
Lemma lem4790808 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem4790809 {A : Type'} (P : A -> Prop) (h1 : term46 A) : term47 A P.
Proof. exact (@lem4790808 A h1 P). Qed.
Lemma lem4790810 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem4790811 {A : Type'} (P : A -> Prop) (h1 : term46 A) : term48 A P.
Proof. exact (EQ_MP (@lem4790810 A P) (@lem4790809 A P h1)). Qed.
Lemma lem4790812 {A : Type'} (P : A -> Prop) (x : A) (h1 : term46 A) : term49 A P x.
Proof. exact (@lem4790811 A P h1 x). Qed.
Lemma lem4790813 {A : Type'} (P : A -> Prop) (x : A) : (term49 A P x) = (term50 A P x).
Proof. exact (eq_refl (term49 A P x)). Qed.
Lemma lem4790814 {A : Type'} (P : A -> Prop) (x : A) (h1 : term46 A) : term50 A P x.
Proof. exact (EQ_MP (@lem4790813 A P x) (@lem4790812 A P x h1)). Qed.
Lemma lem4790815 {A : Type'} (P : A -> Prop) (x : A) (h1 : term51 A P x) : term51 A P x.
Proof. exact (h1). Qed.
Lemma lem4790816 {A : Type'} (P : A -> Prop) (x : A) (h1 : term51 A P x) (h2 : term46 A) : (@ε A P) = x.
Proof. exact (@lem4790814 A P x h2 (@lem4790815 A P x h1)). Qed.
Lemma lem4790817 {A : Type'} (P : A -> Prop) (x : A) (h1 : term51 A P x) : term52 A P x.
Proof. exact (fun h0 : term46 A => @lem4790816 A P x h1 h0). Qed.
Lemma lem4790818 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem4790819 {A : Type'} (P : A -> Prop) (x : A) (h1 : term51 A P x) (h2 : term46 A) : (@ε A P) = x.
Proof. exact (@lem4790817 A P x h1 (@lem4790818 A h2)). Qed.
Lemma lem4790820 {A : Type'} (P : A -> Prop) (x : A) (h1 : term46 A) : term50 A P x.
Proof. exact (fun h0 : term51 A P x => @lem4790819 A P x h0 h1). Qed.
Lemma lem4790821 {A : Type'} (P : A -> Prop) (h1 : term46 A) : term48 A P.
Proof. exact (fun x : A => @lem4790820 A P x h1). Qed.
Lemma lem4790822 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (fun P : A -> Prop => @lem4790821 A P h1). Qed.
Lemma lem4790823 {A : Type'} : term53 A.
Proof. exact (fun h0 : term46 A => @lem4790822 A h0). Qed.
Lemma lem4790824 {A : Type'} : term46 A.
Proof. exact (@lem4790823 A (@lem9522 A)). Qed.
Lemma lem4790825 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (@lem4790824 A P). Qed.
Lemma lem4790826 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem4790827 {A : Type'} (P : A -> Prop) : term48 A P.
Proof. exact (EQ_MP (@lem4790826 A P) (@lem4790825 A P)). Qed.
Lemma lem4790828 {A : Type'} (P : A -> Prop) (x : A) : term49 A P x.
Proof. exact (@lem4790827 A P x). Qed.
Lemma lem4790829 {A : Type'} (P : A -> Prop) (x : A) : (term49 A P x) = (term50 A P x).
Proof. exact (eq_refl (term49 A P x)). Qed.
Lemma lem4790831 {_110256 : Type'} (s : _110256 -> Prop) : term54 _110256 s.
Proof. exact (@lem4786583 _110256 s). Qed.
Lemma lem4790832 {_110256 : Type'} (s : _110256 -> Prop) : (term54 _110256 s) = ((@list_of_set _110256 s) = (term55 _110256 s)).
Proof. exact (eq_refl (term54 _110256 s)). Qed.
Lemma lem4790837 {_110256 : Type'} (s : _110256 -> Prop) : (@list_of_set _110256 s) = (term55 _110256 s).
Proof. exact (EQ_MP (@lem4790832 _110256 s) (@lem4790831 _110256 s)). Qed.
Lemma lem4790838 {A : Type'} (s : A -> Prop) : (@list_of_set A s) = (term55 A s).
Proof. exact (@lem4790837 A s). Qed.
Lemma lem4790839 {A : Type'} (a : A) : (term56 A a) = (term57 A a).
Proof. exact (@lem4790838 A (@INSERT A a (@EMPTY A))). Qed.
Lemma lem4790846 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem4790847 {A : Type'} (a : A) : (term58 A a) = (term59 A a).
Proof. exact (MK_COMB (@lem4790846 A) (@lem4790839 A a)). Qed.
Lemma lem4790848 {A : Type'} (a : A) : (@cons A a (@nil A)) = (@cons A a (@nil A)).
Proof. exact (eq_refl (@cons A a (@nil A))). Qed.
Lemma lem4790849 {A : Type'} (a : A) : ((term56 A a) = (@cons A a (@nil A))) = ((term57 A a) = (@cons A a (@nil A))).
Proof. exact (MK_COMB (@lem4790847 A a) (@lem4790848 A a)). Qed.
Lemma lem4790852 {A : Type'} (a : A) : ((term57 A a) = (@cons A a (@nil A))) = ((term56 A a) = (@cons A a (@nil A))).
Proof. exact (SYM (@lem4790849 A a)). Qed.
Lemma lem4790854 {A : Type'} (P : A -> Prop) (x : A) : term50 A P x.
Proof. exact (EQ_MP (@lem4790829 A P x) (@lem4790828 A P x)). Qed.
Lemma lem4790855 {A : Type'} (P : type1143 A) (x : list A) : term60 A P x.
Proof. exact (@lem4790854 (list A) P x). Qed.
Lemma lem4790856 {A : Type'} (a : A) : term61 A a.
Proof. exact (@lem4790855 A (term62 A a) (@cons A a (@nil A))). Qed.
Lemma lem4790858 {A : Type'} (P : type1143 A) : term41 A P.
Proof. exact (EQ_MP (@lem4790806 A P) (@lem4790805 A P)). Qed.
Lemma lem4790859 {A : Type'} (P : type1143 A) : term41 A P.
Proof. exact (@lem4790858 A P). Qed.
Lemma lem4790860 {A : Type'} (a : A) : term63 A a.
Proof. exact (@lem4790859 A (term64 A a)). Qed.
Lemma lem4790861 {A : Type'} (a : A) : (term65 A a) = ((term66 A a) = ((@nil A) = (@cons A a (@nil A)))).
Proof. exact (eq_refl (term65 A a)). Qed.
Lemma lem4790862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4790863 {A : Type'} (a : A) : (term67 A a) = (term68 A a).
Proof. exact (MK_COMB (@lem4790862) (@lem4790861 A a)). Qed.
Lemma lem4790864 {A : Type'} (a1 : list A) (a : A) : (term69 A a a1) = ((term70 A a a1) = (a1 = (@cons A a (@nil A)))).
Proof. exact (eq_refl (term69 A a a1)). Qed.
Lemma lem4790865 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790866 {A : Type'} (a1 : list A) (a : A) : (term71 A a a1) = (term72 A a1 a).
Proof. exact (MK_COMB (@lem4790865) (@lem4790864 A a1 a)). Qed.
Lemma lem4790867 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term73 A a a0 a1) = ((term74 A a a0 a1) = ((@cons A a0 a1) = (@cons A a (@nil A)))).
Proof. exact (eq_refl (term73 A a a0 a1)). Qed.
Lemma lem4790868 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term75 A a a0 a1) = (term76 A a0 a1 a).
Proof. exact (MK_COMB (@lem4790866 A a1 a) (@lem4790867 A a0 a1 a)). Qed.
Lemma lem4790869 {A : Type'} (a0 : A) (a : A) : (term77 A a a0) = (term78 A a0 a).
Proof. exact (fun_ext (fun a1 : list A => @lem4790868 A a0 a1 a)). Qed.
Lemma lem4790870 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4790871 {A : Type'} (a0 : A) (a : A) : (term79 A a a0) = (term80 A a0 a).
Proof. exact (MK_COMB (@lem4790870 A) (@lem4790869 A a0 a)). Qed.
Lemma lem4790872 {A : Type'} (a : A) : (term81 A a) = (term82 A a).
Proof. exact (fun_ext (fun a0 : A => @lem4790871 A a0 a)). Qed.
Lemma lem4790873 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4790874 {A : Type'} (a : A) : (term83 A a) = (term84 A a).
Proof. exact (MK_COMB (@lem4790873 A) (@lem4790872 A a)). Qed.
Lemma lem4790875 {A : Type'} (a : A) : (term85 A a) = (term86 A a).
Proof. exact (MK_COMB (@lem4790863 A a) (@lem4790874 A a)). Qed.
Lemma lem4790876 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790877 {A : Type'} (a : A) : (term87 A a) = (term88 A a).
Proof. exact (MK_COMB (@lem4790876) (@lem4790875 A a)). Qed.
Lemma lem4790878 {A : Type'} (y : list A) (a : A) : (term69 A a y) = ((term70 A a y) = (y = (@cons A a (@nil A)))).
Proof. exact (eq_refl (term69 A a y)). Qed.
Lemma lem4790879 {A : Type'} (a : A) : (term89 A a) = (term64 A a).
Proof. exact (fun_ext (fun y : list A => @lem4790878 A y a)). Qed.
Lemma lem4790880 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4790881 {A : Type'} (a : A) : (term90 A a) = (term91 A a).
Proof. exact (MK_COMB (@lem4790880 A) (@lem4790879 A a)). Qed.
Lemma lem4790882 {A : Type'} (a : A) : (term63 A a) = (term92 A a).
Proof. exact (MK_COMB (@lem4790877 A a) (@lem4790881 A a)). Qed.
Lemma lem4790883 {A : Type'} (a : A) : term92 A a.
Proof. exact (EQ_MP (@lem4790882 A a) (@lem4790860 A a)). Qed.
Lemma lem4790889 {A B : Type'} (f : A -> B) (y : A) : (term93 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4790890 {A : Type'} (f : type1143 A) (y : list A) : (term94 A f y) = (f y).
Proof. exact (@lem4790889 (list A) Prop f y). Qed.
Lemma lem4790891 {A : Type'} (a : A) : (term95 A a) = (term66 A a).
Proof. exact (@lem4790890 A (term62 A a) (@nil A)). Qed.
Lemma lem4790892 {A : Type'} (l : list A) (a : A) : (term70 A a l) = (term96 A l a).
Proof. exact (eq_refl (term70 A a l)). Qed.
Lemma lem4790893 {A : Type'} (a : A) : (term97 A a) = (term62 A a).
Proof. exact (fun_ext (fun l : list A => @lem4790892 A l a)). Qed.
Lemma lem4790894 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem4790895 {A : Type'} (a : A) : (term95 A a) = (term66 A a).
Proof. exact (MK_COMB (@lem4790893 A a) (@lem4790894 A)). Qed.
Lemma lem4790896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790897 {A : Type'} (a : A) : (term98 A a) = (term99 A a).
Proof. exact (MK_COMB (@lem4790896) (@lem4790895 A a)). Qed.
Lemma lem4790898 {A : Type'} (a : A) : (term66 A a) = (term100 A a).
Proof. exact (eq_refl (term66 A a)). Qed.
Lemma lem4790899 {A : Type'} (a : A) : ((term95 A a) = (term66 A a)) = ((term66 A a) = (term100 A a)).
Proof. exact (MK_COMB (@lem4790897 A a) (@lem4790898 A a)). Qed.
Lemma lem4790900 {A : Type'} (a : A) : (term66 A a) = (term100 A a).
Proof. exact (EQ_MP (@lem4790899 A a) (@lem4790891 A a)). Qed.
Lemma lem4790907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790908 {A : Type'} (a : A) : (term99 A a) = (term101 A a).
Proof. exact (MK_COMB (@lem4790907) (@lem4790900 A a)). Qed.
Lemma lem4790910 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem4790790 A h t (@lem4790789 A h t)). Qed.
Lemma lem4790911 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem4790910 A h t). Qed.
Lemma lem4790912 {A : Type'} (a : A) : ((@nil A) = (@cons A a (@nil A))) = False.
Proof. exact (@lem4790911 A a (@nil A)). Qed.
Lemma lem4790913 {A : Type'} (a : A) : ((term66 A a) = ((@nil A) = (@cons A a (@nil A)))) = ((term100 A a) = False).
Proof. exact (MK_COMB (@lem4790908 A a) (@lem4790912 A a)). Qed.
Lemma lem4790915 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4790916 {A : Type'} (a : A) : ((term100 A a) = False) = (term102 A a).
Proof. exact (@lem4790915 (term100 A a)). Qed.
Lemma lem4790923 {A : Type'} (a : A) : ((term66 A a) = ((@nil A) = (@cons A a (@nil A)))) = (term102 A a).
Proof. exact (TRANS (@lem4790913 A a) (@lem4790916 A a)). Qed.
Lemma lem4790924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4790925 {A : Type'} (a : A) : (term68 A a) = (term103 A a).
Proof. exact (MK_COMB (@lem4790924) (@lem4790923 A a)). Qed.
Lemma lem4790941 {A B : Type'} (f : A -> B) (y : A) : (term93 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4790942 {A : Type'} (f : type1143 A) (y : list A) : (term94 A f y) = (f y).
Proof. exact (@lem4790941 (list A) Prop f y). Qed.
Lemma lem4790943 {A : Type'} (a : A) (a1 : list A) : (term104 A a a1) = (term70 A a a1).
Proof. exact (@lem4790942 A (term62 A a) a1). Qed.
Lemma lem4790944 {A : Type'} (l : list A) (a : A) : (term70 A a l) = (term96 A l a).
Proof. exact (eq_refl (term70 A a l)). Qed.
Lemma lem4790945 {A : Type'} (a : A) : (term97 A a) = (term62 A a).
Proof. exact (fun_ext (fun l : list A => @lem4790944 A l a)). Qed.
Lemma lem4790946 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem4790947 {A : Type'} (a : A) (a1 : list A) : (term104 A a a1) = (term70 A a a1).
Proof. exact (MK_COMB (@lem4790945 A a) (@lem4790946 A a1)). Qed.
Lemma lem4790948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790949 {A : Type'} (a : A) (a1 : list A) : (term105 A a a1) = (term106 A a a1).
Proof. exact (MK_COMB (@lem4790948) (@lem4790947 A a a1)). Qed.
Lemma lem4790950 {A : Type'} (a1 : list A) (a : A) : (term70 A a a1) = (term96 A a1 a).
Proof. exact (eq_refl (term70 A a a1)). Qed.
Lemma lem4790951 {A : Type'} (a1 : list A) (a : A) : ((term104 A a a1) = (term70 A a a1)) = ((term70 A a a1) = (term96 A a1 a)).
Proof. exact (MK_COMB (@lem4790949 A a a1) (@lem4790950 A a1 a)). Qed.
Lemma lem4790952 {A : Type'} (a1 : list A) (a : A) : (term70 A a a1) = (term96 A a1 a).
Proof. exact (EQ_MP (@lem4790951 A a1 a) (@lem4790943 A a a1)). Qed.
Lemma lem4790959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790960 {A : Type'} (a1 : list A) (a : A) : (term106 A a a1) = (term107 A a1 a).
Proof. exact (MK_COMB (@lem4790959) (@lem4790952 A a1 a)). Qed.
Lemma lem4790963 {A : Type'} (a1 : list A) (a : A) : (a1 = (@cons A a (@nil A))) = (a1 = (@cons A a (@nil A))).
Proof. exact (eq_refl (a1 = (@cons A a (@nil A)))). Qed.
Lemma lem4790964 {A : Type'} (a1 : list A) (a : A) : ((term70 A a a1) = (a1 = (@cons A a (@nil A)))) = ((term96 A a1 a) = (a1 = (@cons A a (@nil A)))).
Proof. exact (MK_COMB (@lem4790960 A a1 a) (@lem4790963 A a1 a)). Qed.
Lemma lem4790967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790968 {A : Type'} (a1 : list A) (a : A) : (term72 A a1 a) = (term108 A a1 a).
Proof. exact (MK_COMB (@lem4790967) (@lem4790964 A a1 a)). Qed.
Lemma lem4790972 {A B : Type'} (f : A -> B) (y : A) : (term93 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4790973 {A : Type'} (f : type1143 A) (y : list A) : (term94 A f y) = (f y).
Proof. exact (@lem4790972 (list A) Prop f y). Qed.
Lemma lem4790974 {A : Type'} (a : A) (a0 : A) (a1 : list A) : (term109 A a a0 a1) = (term74 A a a0 a1).
Proof. exact (@lem4790973 A (term62 A a) (@cons A a0 a1)). Qed.
Lemma lem4790975 {A : Type'} (l : list A) (a : A) : (term70 A a l) = (term96 A l a).
Proof. exact (eq_refl (term70 A a l)). Qed.
Lemma lem4790976 {A : Type'} (a : A) : (term97 A a) = (term62 A a).
Proof. exact (fun_ext (fun l : list A => @lem4790975 A l a)). Qed.
Lemma lem4790977 {A : Type'} (a0 : A) (a1 : list A) : (@cons A a0 a1) = (@cons A a0 a1).
Proof. exact (eq_refl (@cons A a0 a1)). Qed.
Lemma lem4790978 {A : Type'} (a : A) (a0 : A) (a1 : list A) : (term109 A a a0 a1) = (term74 A a a0 a1).
Proof. exact (MK_COMB (@lem4790976 A a) (@lem4790977 A a0 a1)). Qed.
Lemma lem4790979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790980 {A : Type'} (a : A) (a0 : A) (a1 : list A) : (term110 A a a0 a1) = (term111 A a a0 a1).
Proof. exact (MK_COMB (@lem4790979) (@lem4790978 A a a0 a1)). Qed.
Lemma lem4790981 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term74 A a a0 a1) = (term112 A a0 a1 a).
Proof. exact (eq_refl (term74 A a a0 a1)). Qed.
Lemma lem4790982 {A : Type'} (a0 : A) (a1 : list A) (a : A) : ((term109 A a a0 a1) = (term74 A a a0 a1)) = ((term74 A a a0 a1) = (term112 A a0 a1 a)).
Proof. exact (MK_COMB (@lem4790980 A a a0 a1) (@lem4790981 A a0 a1 a)). Qed.
Lemma lem4790983 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term74 A a a0 a1) = (term112 A a0 a1 a).
Proof. exact (EQ_MP (@lem4790982 A a0 a1 a) (@lem4790974 A a a0 a1)). Qed.
Lemma lem4790990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790991 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term111 A a a0 a1) = (term113 A a0 a1 a).
Proof. exact (MK_COMB (@lem4790990) (@lem4790983 A a0 a1 a)). Qed.
Lemma lem4790994 {A : Type'} (a0 : A) (a1 : list A) (a : A) : ((@cons A a0 a1) = (@cons A a (@nil A))) = ((@cons A a0 a1) = (@cons A a (@nil A))).
Proof. exact (eq_refl ((@cons A a0 a1) = (@cons A a (@nil A)))). Qed.
Lemma lem4790995 {A : Type'} (a0 : A) (a1 : list A) (a : A) : ((term74 A a a0 a1) = ((@cons A a0 a1) = (@cons A a (@nil A)))) = ((term112 A a0 a1 a) = ((@cons A a0 a1) = (@cons A a (@nil A)))).
Proof. exact (MK_COMB (@lem4790991 A a0 a1 a) (@lem4790994 A a0 a1 a)). Qed.
Lemma lem4790998 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term76 A a0 a1 a) = (term114 A a0 a1 a).
Proof. exact (MK_COMB (@lem4790968 A a1 a) (@lem4790995 A a0 a1 a)). Qed.
Lemma lem4791003 {A : Type'} (a0 : A) (a : A) : (term78 A a0 a) = (term115 A a0 a).
Proof. exact (fun_ext (fun a1 : list A => @lem4790998 A a0 a1 a)). Qed.
Lemma lem4791004 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4791005 {A : Type'} (a0 : A) (a : A) : (term80 A a0 a) = (term116 A a0 a).
Proof. exact (MK_COMB (@lem4791004 A) (@lem4791003 A a0 a)). Qed.
Lemma lem4791010 {A : Type'} (a : A) : (term82 A a) = (term117 A a).
Proof. exact (fun_ext (fun a0 : A => @lem4791005 A a0 a)). Qed.
Lemma lem4791011 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4791012 {A : Type'} (a : A) : (term84 A a) = (term118 A a).
Proof. exact (MK_COMB (@lem4791011 A) (@lem4791010 A a)). Qed.
Lemma lem4791017 {A : Type'} (a : A) : (term86 A a) = (term119 A a).
Proof. exact (MK_COMB (@lem4790925 A a) (@lem4791012 A a)). Qed.
Lemma lem4791020 {A : Type'} (a : A) : (term119 A a) = (term86 A a).
Proof. exact (SYM (@lem4791017 A a)). Qed.
Lemma lem4791030 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem4791031 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4791032 {A : Type'} : (term120 A) = term121.
Proof. exact (MK_COMB (@lem4791031) (@lem4791030 A)). Qed.
Lemma lem4791034 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4790758 A x s h0). Qed.
Lemma lem4791035 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (@lem4791034 A x s). Qed.
Lemma lem4791036 {A : Type'} (a : A) : term122 A a.
Proof. exact (@lem4791035 A a (@EMPTY A)). Qed.
Lemma lem4791038 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4790748 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4791039 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem4791038 A). Qed.
Lemma lem4791040 {A : Type'} : True = (@FINITE A (@EMPTY A)).
Proof. exact (SYM (@lem4791039 A)). Qed.
Lemma lem4791041 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4791040 A) (@lem0)). Qed.
Lemma lem4791042 {A : Type'} (a : A) : (term123 A a) = (term124 A a).
Proof. exact (@lem4791036 A a (@lem4791041 A)). Qed.
Lemma lem4791044 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term125 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4791045 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term126 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4791044 _2963 g t e g' t' e'). Qed.
Lemma lem4791046 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term127 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4791045 _2963 g t e g' t'). Qed.
Lemma lem4791047 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term128 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4791046 _2963 g t e g'). Qed.
Lemma lem4791048 (g : Prop) (t : nat) (e : nat) : term129 g t e.
Proof. exact (@lem4791047 nat g t e). Qed.
Lemma lem4791049 {A : Type'} (a : A) : term130 A a.
Proof. exact (@lem4791048 (@IN A a (@EMPTY A)) (@CARD A (@EMPTY A)) (term131 A)). Qed.
Lemma lem4791050 {A : Type'} (a : A) (g' : Prop) : term132 A a g'.
Proof. exact (@lem4791049 A a g'). Qed.
Lemma lem4791051 {A : Type'} (a : A) (g' : Prop) : (term132 A a g') = (term133 A a g').
Proof. exact (eq_refl (term132 A a g')). Qed.
Lemma lem4791052 {A : Type'} (a : A) (g' : Prop) : term133 A a g'.
Proof. exact (EQ_MP (@lem4791051 A a g') (@lem4791050 A a g')). Qed.
Lemma lem4791053 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term134 A a g' t'.
Proof. exact (@lem4791052 A a g' t'). Qed.
Lemma lem4791054 {A : Type'} (a : A) (g' : Prop) (t' : nat) : (term134 A a g' t') = (term135 A a g' t').
Proof. exact (eq_refl (term134 A a g' t')). Qed.
Lemma lem4791055 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term135 A a g' t'.
Proof. exact (EQ_MP (@lem4791054 A a g' t') (@lem4791053 A a g' t')). Qed.
Lemma lem4791056 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term136 A a g' t' e'.
Proof. exact (@lem4791055 A a g' t' e'). Qed.
Lemma lem4791057 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : (term136 A a g' t' e') = (term137 A a g' t' e').
Proof. exact (eq_refl (term136 A a g' t' e')). Qed.
Lemma lem4791058 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term137 A a g' t' e'.
Proof. exact (EQ_MP (@lem4791057 A a g' t' e') (@lem4791056 A a g' t' e')). Qed.
Lemma lem4791060 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4790746 A x (@lem4790745 A x)). Qed.
Lemma lem4791061 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4791060 A x). Qed.
Lemma lem4791062 {A : Type'} (a : A) : (@IN A a (@EMPTY A)) = False.
Proof. exact (@lem4791061 A a). Qed.
Lemma lem4791063 {A : Type'} (a : A) (t' : nat) (e' : nat) : term138 A a t' e'.
Proof. exact (@lem4791058 A a False t' e'). Qed.
Lemma lem4791064 {A : Type'} (a : A) (t' : nat) (e' : nat) : term139 A a t' e'.
Proof. exact (@lem4791063 A a t' e' (@lem4791062 A a)). Qed.
Lemma lem4791069 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4791070 {A : Type'} : term140 A.
Proof. exact (fun h0 : False => @lem4791069 A). Qed.
Lemma lem4791071 {A : Type'} (a : A) (e' : nat) : term141 A a e'.
Proof. exact (@lem4791064 A a (NUMERAL 0) e'). Qed.
Lemma lem4791072 {A : Type'} (a : A) (e' : nat) : term142 A a e'.
Proof. exact (@lem4791071 A a e' (@lem4791070 A)). Qed.
Lemma lem4791079 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4791080 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4791081 {A : Type'} : (term131 A) = term143.
Proof. exact (MK_COMB (@lem4791080) (@lem4791079 A)). Qed.
Lemma lem4791082 {A : Type'} : term144 A.
Proof. exact (fun h0 : ~ False => @lem4791081 A). Qed.
Lemma lem4791083 {A : Type'} (a : A) : term145 A a.
Proof. exact (@lem4791072 A a term143). Qed.
Lemma lem4791084 {A : Type'} (a : A) : (term124 A a) = term146.
Proof. exact (@lem4791083 A a (@lem4791082 A)). Qed.
Lemma lem4791086 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4791087 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4791086 nat t1 t2). Qed.
Lemma lem4791088 : term146 = term143.
Proof. exact (@lem4791087 (NUMERAL 0) term143). Qed.
Lemma lem4791089 {A : Type'} (a : A) : (term124 A a) = term143.
Proof. exact (TRANS (@lem4791084 A a) (@lem4791088)). Qed.
Lemma lem4791090 {A : Type'} (a : A) : (term123 A a) = term143.
Proof. exact (TRANS (@lem4791042 A a) (@lem4791089 A a)). Qed.
Lemma lem4791091 {A : Type'} (a : A) : ((@List.length A (@nil A)) = (term123 A a)) = ((NUMERAL 0) = term143).
Proof. exact (MK_COMB (@lem4791032 A) (@lem4791090 A a)). Qed.
Lemma lem4791093 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem4790741 n (@lem4790740 n)). Qed.
Lemma lem4791094 : ((NUMERAL 0) = term143) = False.
Proof. exact (@lem4791093 (NUMERAL 0)). Qed.
Lemma lem4791095 {A : Type'} (a : A) : ((@List.length A (@nil A)) = (term123 A a)) = False.
Proof. exact (TRANS (@lem4791091 A a) (@lem4791094)). Qed.
Lemma lem4791096 {A : Type'} (a : A) : (term147 A a) = (term147 A a).
Proof. exact (eq_refl (term147 A a)). Qed.
Lemma lem4791097 {A : Type'} (a : A) : (term100 A a) = (term148 A a).
Proof. exact (MK_COMB (@lem4791096 A a) (@lem4791095 A a)). Qed.
Lemma lem4791099 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4791100 {A : Type'} (a : A) : (term148 A a) = False.
Proof. exact (@lem4791099 ((@set_of_list A (@nil A)) = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem4791101 {A : Type'} (a : A) : (term100 A a) = False.
Proof. exact (TRANS (@lem4791097 A a) (@lem4791100 A a)). Qed.
Lemma lem4791102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4791103 {A : Type'} (a : A) : (term102 A a) = (~ False).
Proof. exact (MK_COMB (@lem4791102) (@lem4791101 A a)). Qed.
Lemma lem4791105 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4791106 {A : Type'} (a : A) : (term102 A a) = True.
Proof. exact (TRANS (@lem4791103 A a) (@lem4791105)). Qed.
Lemma lem4791107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4791108 {A : Type'} (a : A) : (term103 A a) = (and True).
Proof. exact (MK_COMB (@lem4791107) (@lem4791106 A a)). Qed.
Lemma lem4791122 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term149 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4791123 (p : Prop) (q : Prop) (p' : Prop) : term150 p q p'.
Proof. exact (fun q' : Prop => @lem4791122 p q p' q'). Qed.
Lemma lem4791124 (p : Prop) (q : Prop) : term151 p q.
Proof. exact (fun p' : Prop => @lem4791123 p q p'). Qed.
Lemma lem4791125 {A : Type'} (a0 : A) (a1 : list A) (a : A) : term152 A a0 a1 a.
Proof. exact (@lem4791124 ((term96 A a1 a) = (a1 = (@cons A a (@nil A)))) ((term112 A a0 a1 a) = ((@cons A a0 a1) = (@cons A a (@nil A))))). Qed.
Lemma lem4791126 {A : Type'} (a0 : A) (a1 : list A) (a : A) (p' : Prop) : term153 A a0 a1 a p'.
Proof. exact (@lem4791125 A a0 a1 a p'). Qed.
Lemma lem4791127 {A : Type'} (a0 : A) (a1 : list A) (a : A) (p' : Prop) : (term153 A a0 a1 a p') = (term154 A a0 a1 a p').
Proof. exact (eq_refl (term153 A a0 a1 a p')). Qed.
Lemma lem4791128 {A : Type'} (a0 : A) (a1 : list A) (a : A) (p' : Prop) : term154 A a0 a1 a p'.
Proof. exact (EQ_MP (@lem4791127 A a0 a1 a p') (@lem4791126 A a0 a1 a p')). Qed.
Lemma lem4791129 {A : Type'} (a0 : A) (a1 : list A) (a : A) (p' : Prop) (q' : Prop) : term155 A a0 a1 a p' q'.
Proof. exact (@lem4791128 A a0 a1 a p' q'). Qed.
Lemma lem4791130 {A : Type'} (a0 : A) (a1 : list A) (a : A) (p' : Prop) (q' : Prop) : (term155 A a0 a1 a p' q') = (term156 A a0 a1 a p' q').
Proof. exact (eq_refl (term155 A a0 a1 a p' q')). Qed.
Lemma lem4791131 {A : Type'} (a0 : A) (a1 : list A) (a : A) (p' : Prop) (q' : Prop) : term156 A a0 a1 a p' q'.
Proof. exact (EQ_MP (@lem4791130 A a0 a1 a p' q') (@lem4791129 A a0 a1 a p' q')). Qed.
Lemma lem4791141 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4790758 A x s h0). Qed.
Lemma lem4791142 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (@lem4791141 A x s). Qed.
Lemma lem4791143 {A : Type'} (a : A) : term122 A a.
Proof. exact (@lem4791142 A a (@EMPTY A)). Qed.
Lemma lem4791145 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4790748 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4791146 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem4791145 A). Qed.
Lemma lem4791147 {A : Type'} : True = (@FINITE A (@EMPTY A)).
Proof. exact (SYM (@lem4791146 A)). Qed.
Lemma lem4791148 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4791147 A) (@lem0)). Qed.
Lemma lem4791149 {A : Type'} (a : A) : (term123 A a) = (term124 A a).
Proof. exact (@lem4791143 A a (@lem4791148 A)). Qed.
Lemma lem4791151 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term125 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4791152 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term126 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4791151 _2963 g t e g' t' e'). Qed.
Lemma lem4791153 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term127 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4791152 _2963 g t e g' t'). Qed.
Lemma lem4791154 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term128 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4791153 _2963 g t e g'). Qed.
Lemma lem4791155 (g : Prop) (t : nat) (e : nat) : term129 g t e.
Proof. exact (@lem4791154 nat g t e). Qed.
Lemma lem4791156 {A : Type'} (a : A) : term130 A a.
Proof. exact (@lem4791155 (@IN A a (@EMPTY A)) (@CARD A (@EMPTY A)) (term131 A)). Qed.
Lemma lem4791157 {A : Type'} (a : A) (g' : Prop) : term132 A a g'.
Proof. exact (@lem4791156 A a g'). Qed.
Lemma lem4791158 {A : Type'} (a : A) (g' : Prop) : (term132 A a g') = (term133 A a g').
Proof. exact (eq_refl (term132 A a g')). Qed.
Lemma lem4791159 {A : Type'} (a : A) (g' : Prop) : term133 A a g'.
Proof. exact (EQ_MP (@lem4791158 A a g') (@lem4791157 A a g')). Qed.
Lemma lem4791160 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term134 A a g' t'.
Proof. exact (@lem4791159 A a g' t'). Qed.
Lemma lem4791161 {A : Type'} (a : A) (g' : Prop) (t' : nat) : (term134 A a g' t') = (term135 A a g' t').
Proof. exact (eq_refl (term134 A a g' t')). Qed.
Lemma lem4791162 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term135 A a g' t'.
Proof. exact (EQ_MP (@lem4791161 A a g' t') (@lem4791160 A a g' t')). Qed.
Lemma lem4791163 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term136 A a g' t' e'.
Proof. exact (@lem4791162 A a g' t' e'). Qed.
Lemma lem4791164 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : (term136 A a g' t' e') = (term137 A a g' t' e').
Proof. exact (eq_refl (term136 A a g' t' e')). Qed.
Lemma lem4791165 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term137 A a g' t' e'.
Proof. exact (EQ_MP (@lem4791164 A a g' t' e') (@lem4791163 A a g' t' e')). Qed.
Lemma lem4791167 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4790746 A x (@lem4790745 A x)). Qed.
Lemma lem4791168 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4791167 A x). Qed.
Lemma lem4791169 {A : Type'} (a : A) : (@IN A a (@EMPTY A)) = False.
Proof. exact (@lem4791168 A a). Qed.
Lemma lem4791170 {A : Type'} (a : A) (t' : nat) (e' : nat) : term138 A a t' e'.
Proof. exact (@lem4791165 A a False t' e'). Qed.
Lemma lem4791171 {A : Type'} (a : A) (t' : nat) (e' : nat) : term139 A a t' e'.
Proof. exact (@lem4791170 A a t' e' (@lem4791169 A a)). Qed.
Lemma lem4791176 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4791177 {A : Type'} : term140 A.
Proof. exact (fun h0 : False => @lem4791176 A). Qed.
Lemma lem4791178 {A : Type'} (a : A) (e' : nat) : term141 A a e'.
Proof. exact (@lem4791171 A a (NUMERAL 0) e'). Qed.
Lemma lem4791179 {A : Type'} (a : A) (e' : nat) : term142 A a e'.
Proof. exact (@lem4791178 A a e' (@lem4791177 A)). Qed.
Lemma lem4791186 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4791187 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4791188 {A : Type'} : (term131 A) = term143.
Proof. exact (MK_COMB (@lem4791187) (@lem4791186 A)). Qed.
Lemma lem4791189 {A : Type'} : term144 A.
Proof. exact (fun h0 : ~ False => @lem4791188 A). Qed.
Lemma lem4791190 {A : Type'} (a : A) : term145 A a.
Proof. exact (@lem4791179 A a term143). Qed.
Lemma lem4791191 {A : Type'} (a : A) : (term124 A a) = term146.
Proof. exact (@lem4791190 A a (@lem4791189 A)). Qed.
Lemma lem4791193 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4791194 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4791193 nat t1 t2). Qed.
Lemma lem4791195 : term146 = term143.
Proof. exact (@lem4791194 (NUMERAL 0) term143). Qed.
Lemma lem4791196 {A : Type'} (a : A) : (term124 A a) = term143.
Proof. exact (TRANS (@lem4791191 A a) (@lem4791195)). Qed.
Lemma lem4791197 {A : Type'} (a : A) : (term123 A a) = term143.
Proof. exact (TRANS (@lem4791149 A a) (@lem4791196 A a)). Qed.
Lemma lem4791198 {A : Type'} (a1 : list A) : (term157 A a1) = (term157 A a1).
Proof. exact (eq_refl (term157 A a1)). Qed.
Lemma lem4791199 {A : Type'} (a : A) (a1 : list A) : ((@List.length A a1) = (term123 A a)) = ((@List.length A a1) = term143).
Proof. exact (MK_COMB (@lem4791198 A a1) (@lem4791197 A a)). Qed.
Lemma lem4791202 {A : Type'} (a1 : list A) (a : A) : (term158 A a1 a) = (term158 A a1 a).
Proof. exact (eq_refl (term158 A a1 a)). Qed.
Lemma lem4791203 {A : Type'} (a : A) (a1 : list A) : (term96 A a1 a) = (term159 A a a1).
Proof. exact (MK_COMB (@lem4791202 A a1 a) (@lem4791199 A a a1)). Qed.
Lemma lem4791210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4791211 {A : Type'} (a : A) (a1 : list A) : (term107 A a1 a) = (term160 A a a1).
Proof. exact (MK_COMB (@lem4791210) (@lem4791203 A a a1)). Qed.
Lemma lem4791220 {A : Type'} (a1 : list A) (a : A) : (a1 = (@cons A a (@nil A))) = (a1 = (@cons A a (@nil A))).
Proof. exact (eq_refl (a1 = (@cons A a (@nil A)))). Qed.
Lemma lem4791221 {A : Type'} (a1 : list A) (a : A) : ((term96 A a1 a) = (a1 = (@cons A a (@nil A)))) = ((term159 A a a1) = (a1 = (@cons A a (@nil A)))).
Proof. exact (MK_COMB (@lem4791211 A a a1) (@lem4791220 A a1 a)). Qed.
Lemma lem4791232 {A : Type'} (a0 : A) (a1 : list A) (a : A) (q' : Prop) : term161 A a0 a1 a q'.
Proof. exact (@lem4791131 A a0 a1 a ((term159 A a a1) = (a1 = (@cons A a (@nil A)))) q'). Qed.
Lemma lem4791233 {A : Type'} (a0 : A) (a1 : list A) (a : A) (q' : Prop) : term162 A a0 a1 a q'.
Proof. exact (@lem4791232 A a0 a1 a q' (@lem4791221 A a1 a)). Qed.
Lemma lem4791244 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (term24 A t).
Proof. exact (EQ_MP (@lem4790770 A h t) (@lem4790769 A h t)). Qed.
Lemma lem4791245 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (term24 A t).
Proof. exact (@lem4791244 A h t). Qed.
Lemma lem4791246 {A : Type'} (a0 : A) (a1 : list A) : (term23 A a0 a1) = (term24 A a1).
Proof. exact (@lem4791245 A a0 a1). Qed.
Lemma lem4791247 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4791248 {A : Type'} (a0 : A) (a1 : list A) : (term163 A a0 a1) = (term164 A a1).
Proof. exact (MK_COMB (@lem4791247) (@lem4791246 A a0 a1)). Qed.
Lemma lem4791250 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4790758 A x s h0). Qed.
Lemma lem4791251 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (@lem4791250 A x s). Qed.
Lemma lem4791252 {A : Type'} (a : A) : term122 A a.
Proof. exact (@lem4791251 A a (@EMPTY A)). Qed.
Lemma lem4791254 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4790748 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4791255 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem4791254 A). Qed.
Lemma lem4791256 {A : Type'} : True = (@FINITE A (@EMPTY A)).
Proof. exact (SYM (@lem4791255 A)). Qed.
Lemma lem4791257 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem4791256 A) (@lem0)). Qed.
Lemma lem4791258 {A : Type'} (a : A) : (term123 A a) = (term124 A a).
Proof. exact (@lem4791252 A a (@lem4791257 A)). Qed.
Lemma lem4791260 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term125 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4791261 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term126 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4791260 _2963 g t e g' t' e'). Qed.
Lemma lem4791262 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term127 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4791261 _2963 g t e g' t'). Qed.
Lemma lem4791263 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term128 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4791262 _2963 g t e g'). Qed.
Lemma lem4791264 (g : Prop) (t : nat) (e : nat) : term129 g t e.
Proof. exact (@lem4791263 nat g t e). Qed.
Lemma lem4791265 {A : Type'} (a : A) : term130 A a.
Proof. exact (@lem4791264 (@IN A a (@EMPTY A)) (@CARD A (@EMPTY A)) (term131 A)). Qed.
Lemma lem4791266 {A : Type'} (a : A) (g' : Prop) : term132 A a g'.
Proof. exact (@lem4791265 A a g'). Qed.
Lemma lem4791267 {A : Type'} (a : A) (g' : Prop) : (term132 A a g') = (term133 A a g').
Proof. exact (eq_refl (term132 A a g')). Qed.
Lemma lem4791268 {A : Type'} (a : A) (g' : Prop) : term133 A a g'.
Proof. exact (EQ_MP (@lem4791267 A a g') (@lem4791266 A a g')). Qed.
Lemma lem4791269 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term134 A a g' t'.
Proof. exact (@lem4791268 A a g' t'). Qed.
Lemma lem4791270 {A : Type'} (a : A) (g' : Prop) (t' : nat) : (term134 A a g' t') = (term135 A a g' t').
Proof. exact (eq_refl (term134 A a g' t')). Qed.
Lemma lem4791271 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term135 A a g' t'.
Proof. exact (EQ_MP (@lem4791270 A a g' t') (@lem4791269 A a g' t')). Qed.
Lemma lem4791272 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term136 A a g' t' e'.
Proof. exact (@lem4791271 A a g' t' e'). Qed.
Lemma lem4791273 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : (term136 A a g' t' e') = (term137 A a g' t' e').
Proof. exact (eq_refl (term136 A a g' t' e')). Qed.
Lemma lem4791274 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term137 A a g' t' e'.
Proof. exact (EQ_MP (@lem4791273 A a g' t' e') (@lem4791272 A a g' t' e')). Qed.
Lemma lem4791276 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4790746 A x (@lem4790745 A x)). Qed.
Lemma lem4791277 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4791276 A x). Qed.
Lemma lem4791278 {A : Type'} (a : A) : (@IN A a (@EMPTY A)) = False.
Proof. exact (@lem4791277 A a). Qed.
Lemma lem4791279 {A : Type'} (a : A) (t' : nat) (e' : nat) : term138 A a t' e'.
Proof. exact (@lem4791274 A a False t' e'). Qed.
Lemma lem4791280 {A : Type'} (a : A) (t' : nat) (e' : nat) : term139 A a t' e'.
Proof. exact (@lem4791279 A a t' e' (@lem4791278 A a)). Qed.
Lemma lem4791285 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4791286 {A : Type'} : term140 A.
Proof. exact (fun h0 : False => @lem4791285 A). Qed.
Lemma lem4791287 {A : Type'} (a : A) (e' : nat) : term141 A a e'.
Proof. exact (@lem4791280 A a (NUMERAL 0) e'). Qed.
Lemma lem4791288 {A : Type'} (a : A) (e' : nat) : term142 A a e'.
Proof. exact (@lem4791287 A a e' (@lem4791286 A)). Qed.
Lemma lem4791295 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4791296 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4791297 {A : Type'} : (term131 A) = term143.
Proof. exact (MK_COMB (@lem4791296) (@lem4791295 A)). Qed.
Lemma lem4791298 {A : Type'} : term144 A.
Proof. exact (fun h0 : ~ False => @lem4791297 A). Qed.
Lemma lem4791299 {A : Type'} (a : A) : term145 A a.
Proof. exact (@lem4791288 A a term143). Qed.
Lemma lem4791300 {A : Type'} (a : A) : (term124 A a) = term146.
Proof. exact (@lem4791299 A a (@lem4791298 A)). Qed.
Lemma lem4791302 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4791303 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4791302 nat t1 t2). Qed.
Lemma lem4791304 : term146 = term143.
Proof. exact (@lem4791303 (NUMERAL 0) term143). Qed.
Lemma lem4791305 {A : Type'} (a : A) : (term124 A a) = term143.
Proof. exact (TRANS (@lem4791300 A a) (@lem4791304)). Qed.
Lemma lem4791306 {A : Type'} (a : A) : (term123 A a) = term143.
Proof. exact (TRANS (@lem4791258 A a) (@lem4791305 A a)). Qed.
Lemma lem4791307 {A : Type'} (a0 : A) (a : A) (a1 : list A) : ((term23 A a0 a1) = (term123 A a)) = ((term24 A a1) = term143).
Proof. exact (MK_COMB (@lem4791248 A a0 a1) (@lem4791306 A a)). Qed.
Lemma lem4791310 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term165 A a0 a1 a) = (term165 A a0 a1 a).
Proof. exact (eq_refl (term165 A a0 a1 a)). Qed.
Lemma lem4791311 {A : Type'} (a0 : A) (a : A) (a1 : list A) : (term112 A a0 a1 a) = (term166 A a0 a a1).
Proof. exact (MK_COMB (@lem4791310 A a0 a1 a) (@lem4791307 A a0 a a1)). Qed.
Lemma lem4791318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4791319 {A : Type'} (a0 : A) (a : A) (a1 : list A) : (term113 A a0 a1 a) = (term167 A a0 a a1).
Proof. exact (MK_COMB (@lem4791318) (@lem4791311 A a0 a a1)). Qed.
Lemma lem4791328 {A : Type'} (a0 : A) (a1 : list A) (a : A) : ((@cons A a0 a1) = (@cons A a (@nil A))) = ((@cons A a0 a1) = (@cons A a (@nil A))).
Proof. exact (eq_refl ((@cons A a0 a1) = (@cons A a (@nil A)))). Qed.
Lemma lem4791329 {A : Type'} (a0 : A) (a1 : list A) (a : A) : ((term112 A a0 a1 a) = ((@cons A a0 a1) = (@cons A a (@nil A)))) = ((term166 A a0 a a1) = ((@cons A a0 a1) = (@cons A a (@nil A)))).
Proof. exact (MK_COMB (@lem4791319 A a0 a a1) (@lem4791328 A a0 a1 a)). Qed.
Lemma lem4791340 {A : Type'} (a0 : A) (a1 : list A) (a : A) : term168 A a0 a1 a.
Proof. exact (fun h0 : (term159 A a a1) = (a1 = (@cons A a (@nil A))) => @lem4791329 A a0 a1 a). Qed.
Lemma lem4791341 {A : Type'} (a0 : A) (a1 : list A) (a : A) : term169 A a0 a1 a.
Proof. exact (@lem4791233 A a0 a1 a ((term166 A a0 a a1) = ((@cons A a0 a1) = (@cons A a (@nil A))))). Qed.
Lemma lem4791342 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term114 A a0 a1 a) = (term170 A a0 a1 a).
Proof. exact (@lem4791341 A a0 a1 a (@lem4791340 A a0 a1 a)). Qed.
Lemma lem4791406 {A : Type'} (a0 : A) (a : A) : (term115 A a0 a) = (term171 A a0 a).
Proof. exact (fun_ext (fun a1 : list A => @lem4791342 A a0 a1 a)). Qed.
Lemma lem4791470 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4791471 {A : Type'} (a0 : A) (a : A) : (term116 A a0 a) = (term172 A a0 a).
Proof. exact (MK_COMB (@lem4791470 A) (@lem4791406 A a0 a)). Qed.
Lemma lem4791539 {A : Type'} (a : A) : (term117 A a) = (term173 A a).
Proof. exact (fun_ext (fun a0 : A => @lem4791471 A a0 a)). Qed.
Lemma lem4791607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4791608 {A : Type'} (a : A) : (term118 A a) = (term174 A a).
Proof. exact (MK_COMB (@lem4791607 A) (@lem4791539 A a)). Qed.
Lemma lem4791680 {A : Type'} (a : A) : (term119 A a) = (term175 A a).
Proof. exact (MK_COMB (@lem4791108 A a) (@lem4791608 A a)). Qed.
Lemma lem4791682 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4791683 {A : Type'} (a : A) : (term175 A a) = (term174 A a).
Proof. exact (@lem4791682 (term174 A a)). Qed.
Lemma lem4791755 {A : Type'} (a : A) : (term119 A a) = (term174 A a).
Proof. exact (TRANS (@lem4791680 A a) (@lem4791683 A a)). Qed.
Lemma lem4791756 {A : Type'} (a : A) : (term174 A a) = (term119 A a).
Proof. exact (SYM (@lem4791755 A a)). Qed.
Lemma lem4791758 {A : Type'} (P : type1143 A) : term41 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4791759 {A : Type'} (P : type1143 A) : term41 A P.
Proof. exact (@lem4791758 A P). Qed.
Lemma lem4791760 {A : Type'} (a0 : A) (a : A) : term176 A a0 a.
Proof. exact (@lem4791759 A (term171 A a0 a)). Qed.
Lemma lem4791761 {A : Type'} (a0 : A) (a : A) : (term177 A a0 a) = (term178 A a0 a).
Proof. exact (eq_refl (term177 A a0 a)). Qed.
Lemma lem4791762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4791763 {A : Type'} (a0 : A) (a : A) : (term179 A a0 a) = (term180 A a0 a).
Proof. exact (MK_COMB (@lem4791762) (@lem4791761 A a0 a)). Qed.
Lemma lem4791764 {A : Type'} (a0 : A) (t : list A) (a : A) : (term181 A a0 a t) = (term170 A a0 t a).
Proof. exact (eq_refl (term181 A a0 a t)). Qed.
Lemma lem4791765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4791766 {A : Type'} (a0 : A) (t : list A) (a : A) : (term182 A a0 a t) = (term183 A a0 t a).
Proof. exact (MK_COMB (@lem4791765) (@lem4791764 A a0 t a)). Qed.
Lemma lem4791767 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : (term184 A a0 a h t) = (term185 A a0 h t a).
Proof. exact (eq_refl (term184 A a0 a h t)). Qed.
Lemma lem4791768 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : (term186 A a0 a h t) = (term187 A a0 h t a).
Proof. exact (MK_COMB (@lem4791766 A a0 t a) (@lem4791767 A a0 h t a)). Qed.
Lemma lem4791769 {A : Type'} (a0 : A) (h : A) (a : A) : (term188 A a0 a h) = (term189 A a0 h a).
Proof. exact (fun_ext (fun t : list A => @lem4791768 A a0 h t a)). Qed.
Lemma lem4791770 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4791771 {A : Type'} (a0 : A) (h : A) (a : A) : (term190 A a0 a h) = (term191 A a0 h a).
Proof. exact (MK_COMB (@lem4791770 A) (@lem4791769 A a0 h a)). Qed.
Lemma lem4791772 {A : Type'} (a0 : A) (a : A) : (term192 A a0 a) = (term193 A a0 a).
Proof. exact (fun_ext (fun h : A => @lem4791771 A a0 h a)). Qed.
Lemma lem4791773 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4791774 {A : Type'} (a0 : A) (a : A) : (term194 A a0 a) = (term195 A a0 a).
Proof. exact (MK_COMB (@lem4791773 A) (@lem4791772 A a0 a)). Qed.
Lemma lem4791775 {A : Type'} (a0 : A) (a : A) : (term196 A a0 a) = (term197 A a0 a).
Proof. exact (MK_COMB (@lem4791763 A a0 a) (@lem4791774 A a0 a)). Qed.
Lemma lem4791776 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4791777 {A : Type'} (a0 : A) (a : A) : (term198 A a0 a) = (term199 A a0 a).
Proof. exact (MK_COMB (@lem4791776) (@lem4791775 A a0 a)). Qed.
Lemma lem4791778 {A : Type'} (a0 : A) (a1 : list A) (a : A) : (term181 A a0 a a1) = (term170 A a0 a1 a).
Proof. exact (eq_refl (term181 A a0 a a1)). Qed.
Lemma lem4791779 {A : Type'} (a0 : A) (a : A) : (term200 A a0 a) = (term171 A a0 a).
Proof. exact (fun_ext (fun a1 : list A => @lem4791778 A a0 a1 a)). Qed.
Lemma lem4791780 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4791781 {A : Type'} (a0 : A) (a : A) : (term201 A a0 a) = (term172 A a0 a).
Proof. exact (MK_COMB (@lem4791780 A) (@lem4791779 A a0 a)). Qed.
Lemma lem4791782 {A : Type'} (a0 : A) (a : A) : (term176 A a0 a) = (term202 A a0 a).
Proof. exact (MK_COMB (@lem4791777 A a0 a) (@lem4791781 A a0 a)). Qed.
Lemma lem4791783 {A : Type'} (a0 : A) (a : A) : term202 A a0 a.
Proof. exact (EQ_MP (@lem4791782 A a0 a) (@lem4791760 A a0 a)). Qed.
Lemma lem4791794 {A : Type'} (h : A) (t : list A) : (term203 A h t) = (term204 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4791795 {A : Type'} (h : A) (t : list A) : (term203 A h t) = (term204 A h t).
Proof. exact (@lem4791794 A h t). Qed.
Lemma lem4791796 {A : Type'} (a0 : A) : (term205 A a0) = (term206 A a0).
Proof. exact (@lem4791795 A a0 (@nil A)). Qed.
Lemma lem4791798 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4791799 {A : Type'} (a0 : A) : (@INSERT A a0) = (@INSERT A a0).
Proof. exact (eq_refl (@INSERT A a0)). Qed.
Lemma lem4791800 {A : Type'} (a0 : A) : (term206 A a0) = (@INSERT A a0 (@EMPTY A)).
Proof. exact (MK_COMB (@lem4791799 A a0) (@lem4791798 A)). Qed.
Lemma lem4791801 {A : Type'} (a0 : A) : (term205 A a0) = (@INSERT A a0 (@EMPTY A)).
Proof. exact (TRANS (@lem4791796 A a0) (@lem4791800 A a0)). Qed.
Lemma lem4791802 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4791803 {A : Type'} (a0 : A) : (term207 A a0) = (term208 A a0).
Proof. exact (MK_COMB (@lem4791802 A) (@lem4791801 A a0)). Qed.
Lemma lem4791804 {A : Type'} (a : A) : (@INSERT A a (@EMPTY A)) = (@INSERT A a (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A a (@EMPTY A))). Qed.
Lemma lem4791805 {A : Type'} (a0 : A) (a : A) : ((term205 A a0) = (@INSERT A a (@EMPTY A))) = ((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))).
Proof. exact (MK_COMB (@lem4791803 A a0) (@lem4791804 A a)). Qed.
Lemma lem4791808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4791809 {A : Type'} (a0 : A) (a : A) : (term209 A a0 a) = (term210 A a0 a).
Proof. exact (MK_COMB (@lem4791808) (@lem4791805 A a0 a)). Qed.
Lemma lem4791813 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem4790703 m n) (@lem4790702 m n)). Qed.
Lemma lem4791814 {A : Type'} : ((term211 A) = term143) = ((@List.length A (@nil A)) = (NUMERAL 0)).
Proof. exact (@lem4791813 (@List.length A (@nil A)) (NUMERAL 0)). Qed.
Lemma lem4791818 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem4791819 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4791820 {A : Type'} : (term120 A) = term121.
Proof. exact (MK_COMB (@lem4791819) (@lem4791818 A)). Qed.
Lemma lem4791821 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem4791822 {A : Type'} : ((@List.length A (@nil A)) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4791820 A) (@lem4791821)). Qed.
Lemma lem4791824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4791825 (x : nat) : (x = x) = True.
Proof. exact (@lem4791824 nat x). Qed.
Lemma lem4791826 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem4791825 (NUMERAL 0)). Qed.
Lemma lem4791827 {A : Type'} : ((@List.length A (@nil A)) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem4791822 A) (@lem4791826)). Qed.
Lemma lem4791828 {A : Type'} : ((term211 A) = term143) = True.
Proof. exact (TRANS (@lem4791814 A) (@lem4791827 A)). Qed.
Lemma lem4791829 {A : Type'} (a0 : A) (a : A) : (term212 A a0 a) = (term213 A a0 a).
Proof. exact (MK_COMB (@lem4791809 A a0 a) (@lem4791828 A)). Qed.
Lemma lem4791831 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4791832 {A : Type'} (a0 : A) (a : A) : (term213 A a0 a) = ((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))).
Proof. exact (@lem4791831 ((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem4791835 {A : Type'} (a0 : A) (a : A) : (term212 A a0 a) = ((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))).
Proof. exact (TRANS (@lem4791829 A a0 a) (@lem4791832 A a0 a)). Qed.
Lemma lem4791836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4791837 {A : Type'} (a0 : A) (a : A) : (term214 A a0 a) = (term215 A a0 a).
Proof. exact (MK_COMB (@lem4791836) (@lem4791835 A a0 a)). Qed.
Lemma lem4791841 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term18 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem4790715 A h1' h2' t1 t2) (@lem4790714 A h1' h2' t1 t2)). Qed.
Lemma lem4791842 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term18 A h1' h2' t1 t2).
Proof. exact (@lem4791841 A h1' h2' t1 t2). Qed.
Lemma lem4791843 {A : Type'} (a0 : A) (a : A) : ((@cons A a0 (@nil A)) = (@cons A a (@nil A))) = (term216 A a0 a).
Proof. exact (@lem4791842 A a0 a (@nil A) (@nil A)). Qed.
Lemma lem4791849 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4791850 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem4791849 (list A) x). Qed.
Lemma lem4791851 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem4791850 A (@nil A)). Qed.
Lemma lem4791852 {A : Type'} (a0 : A) (a : A) : (term217 A a0 a) = (term217 A a0 a).
Proof. exact (eq_refl (term217 A a0 a)). Qed.
Lemma lem4791853 {A : Type'} (a0 : A) (a : A) : (term216 A a0 a) = (term218 A a0 a).
Proof. exact (MK_COMB (@lem4791852 A a0 a) (@lem4791851 A)). Qed.
Lemma lem4791855 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4791856 {A : Type'} (a0 : A) (a : A) : (term218 A a0 a) = (a0 = a).
Proof. exact (@lem4791855 (a0 = a)). Qed.
Lemma lem4791859 {A : Type'} (a0 : A) (a : A) : (term216 A a0 a) = (a0 = a).
Proof. exact (TRANS (@lem4791853 A a0 a) (@lem4791856 A a0 a)). Qed.
Lemma lem4791860 {A : Type'} (a0 : A) (a : A) : ((@cons A a0 (@nil A)) = (@cons A a (@nil A))) = (a0 = a).
Proof. exact (TRANS (@lem4791843 A a0 a) (@lem4791859 A a0 a)). Qed.
Lemma lem4791861 {A : Type'} (a0 : A) (a : A) : ((term212 A a0 a) = ((@cons A a0 (@nil A)) = (@cons A a (@nil A)))) = (((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))) = (a0 = a)).
Proof. exact (MK_COMB (@lem4791837 A a0 a) (@lem4791860 A a0 a)). Qed.
Lemma lem4791868 {A : Type'} (a0 : A) (a : A) : (((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))) = (a0 = a)) = ((term212 A a0 a) = ((@cons A a0 (@nil A)) = (@cons A a (@nil A)))).
Proof. exact (SYM (@lem4791861 A a0 a)). Qed.
Lemma lem4791876 {A : Type'} (h : A) (t : list A) : (term203 A h t) = (term204 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4791877 {A : Type'} (h : A) (t : list A) : (term203 A h t) = (term204 A h t).
Proof. exact (@lem4791876 A h t). Qed.
Lemma lem4791878 {A : Type'} (a0 : A) (h : A) (t : list A) : (term219 A a0 h t) = (term220 A a0 h t).
Proof. exact (@lem4791877 A a0 (@cons A h t)). Qed.
Lemma lem4791880 {A : Type'} (h : A) (t : list A) : (term203 A h t) = (term204 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4791881 {A : Type'} (h : A) (t : list A) : (term203 A h t) = (term204 A h t).
Proof. exact (@lem4791880 A h t). Qed.
Lemma lem4791882 {A : Type'} (a0 : A) : (@INSERT A a0) = (@INSERT A a0).
Proof. exact (eq_refl (@INSERT A a0)). Qed.
Lemma lem4791883 {A : Type'} (a0 : A) (h : A) (t : list A) : (term220 A a0 h t) = (term221 A a0 h t).
Proof. exact (MK_COMB (@lem4791882 A a0) (@lem4791881 A h t)). Qed.
Lemma lem4791884 {A : Type'} (a0 : A) (h : A) (t : list A) : (term219 A a0 h t) = (term221 A a0 h t).
Proof. exact (TRANS (@lem4791878 A a0 h t) (@lem4791883 A a0 h t)). Qed.
Lemma lem4791885 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4791886 {A : Type'} (a0 : A) (h : A) (t : list A) : (term222 A a0 h t) = (term223 A a0 h t).
Proof. exact (MK_COMB (@lem4791885 A) (@lem4791884 A a0 h t)). Qed.
Lemma lem4791887 {A : Type'} (a : A) : (@INSERT A a (@EMPTY A)) = (@INSERT A a (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A a (@EMPTY A))). Qed.
Lemma lem4791888 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : ((term219 A a0 h t) = (@INSERT A a (@EMPTY A))) = ((term221 A a0 h t) = (@INSERT A a (@EMPTY A))).
Proof. exact (MK_COMB (@lem4791886 A a0 h t) (@lem4791887 A a)). Qed.
Lemma lem4791891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4791892 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : (term224 A a0 h t a) = (term225 A a0 h t a).
Proof. exact (MK_COMB (@lem4791891) (@lem4791888 A a0 h t a)). Qed.
Lemma lem4791896 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem4790703 m n) (@lem4790702 m n)). Qed.
Lemma lem4791897 {A : Type'} (h : A) (t : list A) : ((term226 A h t) = term143) = ((term23 A h t) = (NUMERAL 0)).
Proof. exact (@lem4791896 (term23 A h t) (NUMERAL 0)). Qed.
Lemma lem4791901 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (term24 A t).
Proof. exact (EQ_MP (@lem4790724 A h t) (@lem4790723 A h t)). Qed.
Lemma lem4791902 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (term24 A t).
Proof. exact (@lem4791901 A h t). Qed.
Lemma lem4791903 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4791904 {A : Type'} (h : A) (t : list A) : (term163 A h t) = (term164 A t).
Proof. exact (MK_COMB (@lem4791903) (@lem4791902 A h t)). Qed.
Lemma lem4791905 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem4791906 {A : Type'} (h : A) (t : list A) : ((term23 A h t) = (NUMERAL 0)) = ((term24 A t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4791904 A h t) (@lem4791905)). Qed.
Lemma lem4791908 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem4790667 n (@lem4790666 n)). Qed.
Lemma lem4791909 {A : Type'} (t : list A) : ((term24 A t) = (NUMERAL 0)) = False.
Proof. exact (@lem4791908 (@List.length A t)). Qed.
Lemma lem4791910 {A : Type'} (h : A) (t : list A) : ((term23 A h t) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem4791906 A h t) (@lem4791909 A t)). Qed.
Lemma lem4791911 {A : Type'} (h : A) (t : list A) : ((term226 A h t) = term143) = False.
Proof. exact (TRANS (@lem4791897 A h t) (@lem4791910 A h t)). Qed.
Lemma lem4791912 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : (term227 A a0 a h t) = (term228 A a0 h t a).
Proof. exact (MK_COMB (@lem4791892 A a0 h t a) (@lem4791911 A h t)). Qed.
Lemma lem4791914 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4791915 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : (term228 A a0 h t a) = False.
Proof. exact (@lem4791914 ((term221 A a0 h t) = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem4791916 {A : Type'} (a0 : A) (a : A) (h : A) (t : list A) : (term227 A a0 a h t) = False.
Proof. exact (TRANS (@lem4791912 A a0 h t a) (@lem4791915 A a0 h t a)). Qed.
Lemma lem4791917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4791918 {A : Type'} (a0 : A) (a : A) (h : A) (t : list A) : (term229 A a0 a h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4791917) (@lem4791916 A a0 a h t)). Qed.
Lemma lem4791920 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term18 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem4790715 A h1' h2' t1 t2) (@lem4790714 A h1' h2' t1 t2)). Qed.
Lemma lem4791921 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term18 A h1' h2' t1 t2).
Proof. exact (@lem4791920 A h1' h2' t1 t2). Qed.
Lemma lem4791922 {A : Type'} (a0 : A) (a : A) (h : A) (t : list A) : ((term230 A a0 h t) = (@cons A a (@nil A))) = (term231 A a0 a h t).
Proof. exact (@lem4791921 A a0 a (@cons A h t) (@nil A)). Qed.
Lemma lem4791928 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem4790686 A h t (@lem4790685 A h t)). Qed.
Lemma lem4791929 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem4791928 A h t). Qed.
Lemma lem4791930 {A : Type'} (a0 : A) (a : A) : (term217 A a0 a) = (term217 A a0 a).
Proof. exact (eq_refl (term217 A a0 a)). Qed.
Lemma lem4791931 {A : Type'} (h : A) (t : list A) (a0 : A) (a : A) : (term231 A a0 a h t) = (term232 A a0 a).
Proof. exact (MK_COMB (@lem4791930 A a0 a) (@lem4791929 A h t)). Qed.
Lemma lem4791933 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4791934 {A : Type'} (a0 : A) (a : A) : (term232 A a0 a) = False.
Proof. exact (@lem4791933 (a0 = a)). Qed.
Lemma lem4791935 {A : Type'} (a0 : A) (a : A) (h : A) (t : list A) : (term231 A a0 a h t) = False.
Proof. exact (TRANS (@lem4791931 A h t a0 a) (@lem4791934 A a0 a)). Qed.
Lemma lem4791936 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : ((term230 A a0 h t) = (@cons A a (@nil A))) = False.
Proof. exact (TRANS (@lem4791922 A a0 a h t) (@lem4791935 A a0 a h t)). Qed.
Lemma lem4791937 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : ((term227 A a0 a h t) = ((term230 A a0 h t) = (@cons A a (@nil A)))) = (False = False).
Proof. exact (MK_COMB (@lem4791918 A a0 a h t) (@lem4791936 A a0 h t a)). Qed.
Lemma lem4791939 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4791940 : (False = False) = (~ False).
Proof. exact (@lem4791939 False). Qed.
Lemma lem4791942 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4791943 : (False = False) = True.
Proof. exact (TRANS (@lem4791940) (@lem4791942)). Qed.
Lemma lem4791944 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : ((term227 A a0 a h t) = ((term230 A a0 h t) = (@cons A a (@nil A)))) = True.
Proof. exact (TRANS (@lem4791937 A a0 h t a) (@lem4791943)). Qed.
Lemma lem4791945 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : True = ((term227 A a0 a h t) = ((term230 A a0 h t) = (@cons A a (@nil A)))).
Proof. exact (SYM (@lem4791944 A a0 h t a)). Qed.
Lemma lem4791946 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : (term227 A a0 a h t) = ((term230 A a0 h t) = (@cons A a (@nil A))).
Proof. exact (EQ_MP (@lem4791945 A a0 h t a) (@lem0)). Qed.
Lemma lem4791954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term233 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4791955 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term233 A s t).
Proof. exact (@lem4791954 A s t). Qed.
Lemma lem4791956 {A : Type'} (a0 : A) (a : A) : ((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))) = (term234 A a0 a).
Proof. exact (@lem4791955 A (@INSERT A a0 (@EMPTY A)) (@INSERT A a (@EMPTY A))). Qed.
Lemma lem4791965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4791966 {A : Type'} (a0 : A) (a : A) : (term215 A a0 a) = (term235 A a0 a).
Proof. exact (MK_COMB (@lem4791965) (@lem4791956 A a0 a)). Qed.
Lemma lem4791971 {A : Type'} (a0 : A) (a : A) : (a0 = a) = (a0 = a).
Proof. exact (eq_refl (a0 = a)). Qed.
Lemma lem4791972 {A : Type'} (a0 : A) (a : A) : (((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))) = (a0 = a)) = ((term234 A a0 a) = (a0 = a)).
Proof. exact (MK_COMB (@lem4791966 A a0 a) (@lem4791971 A a0 a)). Qed.
Lemma lem4791977 {A : Type'} (a0 : A) (a : A) : ((term234 A a0 a) = (a0 = a)) = (((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))) = (a0 = a)).
Proof. exact (SYM (@lem4791972 A a0 a)). Qed.
Lemma lem4791987 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term236 A x y s) = (term237 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4791988 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term236 A x y s) = (term237 A y x s).
Proof. exact (@lem4791987 A y x s). Qed.
Lemma lem4791989 {A : Type'} (a0 : A) (x : A) : (term238 A x a0) = (term239 A a0 x).
Proof. exact (@lem4791988 A a0 x (@EMPTY A)). Qed.
Lemma lem4791995 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4791996 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4791995 A x). Qed.
Lemma lem4791997 {A : Type'} (x : A) (a0 : A) : (term240 A x a0) = (term240 A x a0).
Proof. exact (eq_refl (term240 A x a0)). Qed.
Lemma lem4791998 {A : Type'} (x : A) (a0 : A) : (term239 A a0 x) = (term241 A x a0).
Proof. exact (MK_COMB (@lem4791997 A x a0) (@lem4791996 A x)). Qed.
Lemma lem4792000 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4792001 {A : Type'} (x : A) (a0 : A) : (term241 A x a0) = (x = a0).
Proof. exact (@lem4792000 (x = a0)). Qed.
Lemma lem4792004 {A : Type'} (x : A) (a0 : A) : (term239 A a0 x) = (x = a0).
Proof. exact (TRANS (@lem4791998 A x a0) (@lem4792001 A x a0)). Qed.
Lemma lem4792005 {A : Type'} (x : A) (a0 : A) : (term238 A x a0) = (x = a0).
Proof. exact (TRANS (@lem4791989 A a0 x) (@lem4792004 A x a0)). Qed.
Lemma lem4792006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792007 {A : Type'} (x : A) (a0 : A) : (term242 A x a0) = (term243 A x a0).
Proof. exact (MK_COMB (@lem4792006) (@lem4792005 A x a0)). Qed.
Lemma lem4792009 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term236 A x y s) = (term237 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4792010 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term236 A x y s) = (term237 A y x s).
Proof. exact (@lem4792009 A y x s). Qed.
Lemma lem4792011 {A : Type'} (a : A) (x : A) : (term238 A x a) = (term239 A a x).
Proof. exact (@lem4792010 A a x (@EMPTY A)). Qed.
Lemma lem4792017 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4792018 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4792017 A x). Qed.
Lemma lem4792019 {A : Type'} (x : A) (a : A) : (term240 A x a) = (term240 A x a).
Proof. exact (eq_refl (term240 A x a)). Qed.
Lemma lem4792020 {A : Type'} (x : A) (a : A) : (term239 A a x) = (term241 A x a).
Proof. exact (MK_COMB (@lem4792019 A x a) (@lem4792018 A x)). Qed.
Lemma lem4792022 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4792023 {A : Type'} (x : A) (a : A) : (term241 A x a) = (x = a).
Proof. exact (@lem4792022 (x = a)). Qed.
Lemma lem4792026 {A : Type'} (x : A) (a : A) : (term239 A a x) = (x = a).
Proof. exact (TRANS (@lem4792020 A x a) (@lem4792023 A x a)). Qed.
Lemma lem4792027 {A : Type'} (x : A) (a : A) : (term238 A x a) = (x = a).
Proof. exact (TRANS (@lem4792011 A a x) (@lem4792026 A x a)). Qed.
Lemma lem4792028 {A : Type'} (a0 : A) (x : A) (a : A) : ((term238 A x a0) = (term238 A x a)) = ((x = a0) = (x = a)).
Proof. exact (MK_COMB (@lem4792007 A x a0) (@lem4792027 A x a)). Qed.
Lemma lem4792031 {A : Type'} (a0 : A) (a : A) : (term244 A a0 a) = (term245 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792028 A a0 x a)). Qed.
Lemma lem4792032 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792033 {A : Type'} (a0 : A) (a : A) : (term234 A a0 a) = (term246 A a0 a).
Proof. exact (MK_COMB (@lem4792032 A) (@lem4792031 A a0 a)). Qed.
Lemma lem4792038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792039 {A : Type'} (a0 : A) (a : A) : (term235 A a0 a) = (term247 A a0 a).
Proof. exact (MK_COMB (@lem4792038) (@lem4792033 A a0 a)). Qed.
Lemma lem4792042 {A : Type'} (a0 : A) (a : A) : (a0 = a) = (a0 = a).
Proof. exact (eq_refl (a0 = a)). Qed.
Lemma lem4792043 {A : Type'} (a0 : A) (a : A) : ((term234 A a0 a) = (a0 = a)) = ((term246 A a0 a) = (a0 = a)).
Proof. exact (MK_COMB (@lem4792039 A a0 a) (@lem4792042 A a0 a)). Qed.
Lemma lem4792046 {A : Type'} (a0 : A) (a : A) : ((term246 A a0 a) = (a0 = a)) = ((term234 A a0 a) = (a0 = a)).
Proof. exact (SYM (@lem4792043 A a0 a)). Qed.
Lemma lem4792048 (p : Prop) : p = (term248 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4792049 {A : Type'} (a0 : A) (a : A) : ((term246 A a0 a) = (a0 = a)) = (term249 A a0 a).
Proof. exact (@lem4792048 ((term246 A a0 a) = (a0 = a))). Qed.
Lemma lem4792050 {A : Type'} (a0 : A) (a : A) : (term249 A a0 a) = ((term246 A a0 a) = (a0 = a)).
Proof. exact (SYM (@lem4792049 A a0 a)). Qed.
Lemma lem4792051 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : term250 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792054 {A : Type'} (a0 : A) (a : A) (h1 : term249 A a0 a) : term249 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792055 {A : Type'} (a0 : A) (a : A) : term251 A a0 a.
Proof. exact (fun h0 : term249 A a0 a => @lem4792054 A a0 a h0). Qed.
Lemma lem4792056 {A : Type'} (a0 : A) (a : A) (h1 : term251 A a0 a) : term251 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792057 {A : Type'} (a0 : A) (a : A) (h1 : term249 A a0 a) : term249 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792058 {A : Type'} (a0 : A) (a : A) (h1 : term249 A a0 a) (h2 : term251 A a0 a) : term249 A a0 a.
Proof. exact (@lem4792056 A a0 a h2 (@lem4792057 A a0 a h1)). Qed.
Lemma lem4792059 {A : Type'} (a0 : A) (a : A) (h1 : term249 A a0 a) : term252 A a0 a.
Proof. exact (fun h0 : term251 A a0 a => @lem4792058 A a0 a h1 h0). Qed.
Lemma lem4792060 {A : Type'} (a0 : A) (a : A) (h1 : term251 A a0 a) : term251 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792061 {A : Type'} (a0 : A) (a : A) (h1 : term249 A a0 a) (h2 : term251 A a0 a) : term249 A a0 a.
Proof. exact (@lem4792059 A a0 a h1 (@lem4792060 A a0 a h2)). Qed.
Lemma lem4792062 {A : Type'} (a0 : A) (a : A) (h1 : term251 A a0 a) : term251 A a0 a.
Proof. exact (fun h0 : term249 A a0 a => @lem4792061 A a0 a h0 h1). Qed.
Lemma lem4792063 {A : Type'} (a0 : A) (a : A) : term253 A a0 a.
Proof. exact (fun h0 : term251 A a0 a => @lem4792062 A a0 a h0). Qed.
Lemma lem4792066 {A : Type'} (a0 : A) (a : A) : term251 A a0 a.
Proof. exact (@lem4792063 A a0 a (@lem4792055 A a0 a)). Qed.
Lemma lem4792067 {A : Type'} (a0 : A) (a : A) : term251 A a0 a.
Proof. exact (@lem4792066 A a0 a). Qed.
Lemma lem4792077 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4792078 {A : Type'} (a0 : A) (a : A) : (term249 A a0 a) = (term254 A a0 a).
Proof. exact (@lem4792077 (term250 A a0 a)). Qed.
Lemma lem4792080 (t : Prop) : (term255 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4792081 {A : Type'} (a0 : A) (a : A) : (term254 A a0 a) = ((term246 A a0 a) = (a0 = a)).
Proof. exact (@lem4792080 ((term246 A a0 a) = (a0 = a))). Qed.
Lemma lem4792082 {A : Type'} (a0 : A) (a : A) : (term249 A a0 a) = ((term246 A a0 a) = (a0 = a)).
Proof. exact (TRANS (@lem4792078 A a0 a) (@lem4792081 A a0 a)). Qed.
Lemma lem4792087 {A : Type'} (a : A) : (term256 A a) = (term257 A a).
Proof. exact (fun_ext (fun a0 : A => @lem4792082 A a0 a)). Qed.
Lemma lem4792088 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792089 {A : Type'} (a : A) : (term258 A a) = (term259 A a).
Proof. exact (MK_COMB (@lem4792088 A) (@lem4792087 A a)). Qed.
Lemma lem4792094 {A : Type'} : (term260 A) = (term261 A).
Proof. exact (fun_ext (fun a : A => @lem4792089 A a)). Qed.
Lemma lem4792095 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792104 {A : Type'} : (term262 A) = (term263 A).
Proof. exact (MK_COMB (@lem4792095 A) (@lem4792094 A)). Qed.
Lemma lem4792105 {A : Type'} (a0 : A) (a : A) : (a0 = a) = (a0 = a).
Proof. exact (eq_refl (a0 = a)). Qed.
Lemma lem4792110 {A : Type'} (a0 : A) (x : A) (a : A) : ((x = a0) = (x = a)) = ((x = a0) = (x = a)).
Proof. exact (eq_refl ((x = a0) = (x = a))). Qed.
Lemma lem4792111 {A : Type'} (a0 : A) (a : A) : (term245 A a0 a) = (term245 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792110 A a0 x a)). Qed.
Lemma lem4792112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792113 {A : Type'} (a0 : A) (a : A) : (term246 A a0 a) = (term246 A a0 a).
Proof. exact (MK_COMB (@lem4792112 A) (@lem4792111 A a0 a)). Qed.
Lemma lem4792114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792115 {A : Type'} (a0 : A) (a : A) : (term247 A a0 a) = (term247 A a0 a).
Proof. exact (MK_COMB (@lem4792114) (@lem4792113 A a0 a)). Qed.
Lemma lem4792116 {A : Type'} (a0 : A) (a : A) : ((term246 A a0 a) = (a0 = a)) = ((term246 A a0 a) = (a0 = a)).
Proof. exact (MK_COMB (@lem4792115 A a0 a) (@lem4792105 A a0 a)). Qed.
Lemma lem4792117 {A : Type'} (a : A) : (term257 A a) = (term257 A a).
Proof. exact (fun_ext (fun a0 : A => @lem4792116 A a0 a)). Qed.
Lemma lem4792118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792119 {A : Type'} (a : A) : (term259 A a) = (term259 A a).
Proof. exact (MK_COMB (@lem4792118 A) (@lem4792117 A a)). Qed.
Lemma lem4792120 {A : Type'} : (term261 A) = (term261 A).
Proof. exact (fun_ext (fun a : A => @lem4792119 A a)). Qed.
Lemma lem4792121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792122 {A : Type'} : (term263 A) = (term263 A).
Proof. exact (MK_COMB (@lem4792121 A) (@lem4792120 A)). Qed.
Lemma lem4792143 {A : Type'} : (term262 A) = (term263 A).
Proof. exact (TRANS (@lem4792104 A) (@lem4792122 A)). Qed.
Lemma lem4792144 {A : Type'} : (term263 A) = (term262 A).
Proof. exact (SYM (@lem4792143 A)). Qed.
Lemma lem4792146 (p : Prop) : p = (term248 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4792147 {A : Type'} (a0 : A) (a : A) : ((term246 A a0 a) = (a0 = a)) = (term249 A a0 a).
Proof. exact (@lem4792146 ((term246 A a0 a) = (a0 = a))). Qed.
Lemma lem4792148 {A : Type'} (a0 : A) (a : A) : (term249 A a0 a) = ((term246 A a0 a) = (a0 = a)).
Proof. exact (SYM (@lem4792147 A a0 a)). Qed.
Lemma lem4792149 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : term250 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792164 {A : Type'} (a0 : A) (x : A) (a : A) : (term264 A a0 x a) = (term265 A a0 x a).
Proof. exact (@lem17930 (x = a0) (x = a)). Qed.
Lemma lem4792175 {A : Type'} (a0 : A) (x : A) (a : A) : ((x = a0) = (x = a)) = (term266 A a0 x a).
Proof. exact (@lem17784 (x = a0) (x = a)). Qed.
Lemma lem4792176 {A : Type'} (P : A -> Prop) : (term267 A P) = (term268 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4792177 {A : Type'} (a0 : A) (a : A) : (term269 A a0 a) = (term270 A a0 a).
Proof. exact (@lem4792176 A (term245 A a0 a)). Qed.
Lemma lem4792178 {A : Type'} (a0 : A) (x : A) (a : A) : (term271 A a0 a x) = ((x = a0) = (x = a)).
Proof. exact (eq_refl (term271 A a0 a x)). Qed.
Lemma lem4792179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4792180 {A : Type'} (a0 : A) (x : A) (a : A) : (term272 A a0 a x) = (term264 A a0 x a).
Proof. exact (MK_COMB (@lem4792179) (@lem4792178 A a0 x a)). Qed.
Lemma lem4792181 {A : Type'} (a0 : A) (x : A) (a : A) : (term272 A a0 a x) = (term265 A a0 x a).
Proof. exact (TRANS (@lem4792180 A a0 x a) (@lem4792164 A a0 x a)). Qed.
Lemma lem4792182 {A : Type'} (a0 : A) (a : A) : (term273 A a0 a) = (term274 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792181 A a0 x a)). Qed.
Lemma lem4792183 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4792184 {A : Type'} (a0 : A) (a : A) : (term270 A a0 a) = (term275 A a0 a).
Proof. exact (MK_COMB (@lem4792183 A) (@lem4792182 A a0 a)). Qed.
Lemma lem4792185 {A : Type'} (a0 : A) (a : A) : (term269 A a0 a) = (term275 A a0 a).
Proof. exact (TRANS (@lem4792177 A a0 a) (@lem4792184 A a0 a)). Qed.
Lemma lem4792186 {A : Type'} (a0 : A) (a : A) : (term245 A a0 a) = (term276 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792175 A a0 x a)). Qed.
Lemma lem4792187 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792188 {A : Type'} (a0 : A) (a : A) : (term246 A a0 a) = (term277 A a0 a).
Proof. exact (MK_COMB (@lem4792187 A) (@lem4792186 A a0 a)). Qed.
Lemma lem4792189 {A : Type'} (a0 : A) (a : A) : (term278 A a0 a) = (term278 A a0 a).
Proof. exact (eq_refl (term278 A a0 a)). Qed.
Lemma lem4792190 {A : Type'} (a0 : A) (a : A) : (a0 = a) = (a0 = a).
Proof. exact (eq_refl (a0 = a)). Qed.
Lemma lem4792191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792192 {A : Type'} (a0 : A) (a : A) : (term279 A a0 a) = (term280 A a0 a).
Proof. exact (MK_COMB (@lem4792191) (@lem4792185 A a0 a)). Qed.
Lemma lem4792193 {A : Type'} (a0 : A) (a : A) : (term281 A a0 a) = (term282 A a0 a).
Proof. exact (MK_COMB (@lem4792192 A a0 a) (@lem4792190 A a0 a)). Qed.
Lemma lem4792194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792195 {A : Type'} (a0 : A) (a : A) : (term283 A a0 a) = (term284 A a0 a).
Proof. exact (MK_COMB (@lem4792194) (@lem4792188 A a0 a)). Qed.
Lemma lem4792196 {A : Type'} (a0 : A) (a : A) : (term285 A a0 a) = (term286 A a0 a).
Proof. exact (MK_COMB (@lem4792195 A a0 a) (@lem4792189 A a0 a)). Qed.
Lemma lem4792197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4792198 {A : Type'} (a0 : A) (a : A) : (term287 A a0 a) = (term288 A a0 a).
Proof. exact (MK_COMB (@lem4792197) (@lem4792196 A a0 a)). Qed.
Lemma lem4792199 {A : Type'} (a0 : A) (a : A) : (term289 A a0 a) = (term290 A a0 a).
Proof. exact (MK_COMB (@lem4792198 A a0 a) (@lem4792193 A a0 a)). Qed.
Lemma lem4792200 {A : Type'} (a0 : A) (a : A) : (term250 A a0 a) = (term289 A a0 a).
Proof. exact (@lem17646 (term246 A a0 a) (a0 = a)). Qed.
Lemma lem4792201 {A : Type'} (a0 : A) (a : A) : (term250 A a0 a) = (term290 A a0 a).
Proof. exact (TRANS (@lem4792200 A a0 a) (@lem4792199 A a0 a)). Qed.
Lemma lem4792203 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4792204 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (@lem4792203 A P Q). Qed.
Lemma lem4792205 {A : Type'} (a0 : A) (a : A) : (term293 A a0 a) = (term294 A a0 a).
Proof. exact (@lem4792204 A (term295 A a0 a) (term296 A a0 a)). Qed.
Lemma lem4792206 {A : Type'} (a0 : A) (x : A) (a : A) : (term297 A a0 a x) = (term298 A a0 x a).
Proof. exact (eq_refl (term297 A a0 a x)). Qed.
Lemma lem4792207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792208 {A : Type'} (a0 : A) (x : A) (a : A) : (term299 A a0 a x) = (term300 A a0 x a).
Proof. exact (MK_COMB (@lem4792207) (@lem4792206 A a0 x a)). Qed.
Lemma lem4792209 {A : Type'} (a0 : A) (x : A) (a : A) : (term301 A a0 a x) = (term302 A a0 x a).
Proof. exact (eq_refl (term301 A a0 a x)). Qed.
Lemma lem4792210 {A : Type'} (a0 : A) (x : A) (a : A) : (term303 A a0 a x) = (term266 A a0 x a).
Proof. exact (MK_COMB (@lem4792208 A a0 x a) (@lem4792209 A a0 x a)). Qed.
Lemma lem4792211 {A : Type'} (a0 : A) (a : A) : (term304 A a0 a) = (term276 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792210 A a0 x a)). Qed.
Lemma lem4792212 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792213 {A : Type'} (a0 : A) (a : A) : (term293 A a0 a) = (term277 A a0 a).
Proof. exact (MK_COMB (@lem4792212 A) (@lem4792211 A a0 a)). Qed.
Lemma lem4792214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792215 {A : Type'} (a0 : A) (a : A) : (term305 A a0 a) = (term306 A a0 a).
Proof. exact (MK_COMB (@lem4792214) (@lem4792213 A a0 a)). Qed.
Lemma lem4792216 {A : Type'} (a0 : A) (x : A) (a : A) : (term297 A a0 a x) = (term298 A a0 x a).
Proof. exact (eq_refl (term297 A a0 a x)). Qed.
Lemma lem4792217 {A : Type'} (a0 : A) (a : A) : (term307 A a0 a) = (term295 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792216 A a0 x a)). Qed.
Lemma lem4792218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792219 {A : Type'} (a0 : A) (a : A) : (term308 A a0 a) = (term309 A a0 a).
Proof. exact (MK_COMB (@lem4792218 A) (@lem4792217 A a0 a)). Qed.
Lemma lem4792220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792221 {A : Type'} (a0 : A) (a : A) : (term310 A a0 a) = (term311 A a0 a).
Proof. exact (MK_COMB (@lem4792220) (@lem4792219 A a0 a)). Qed.
Lemma lem4792222 {A : Type'} (a0 : A) (x : A) (a : A) : (term301 A a0 a x) = (term302 A a0 x a).
Proof. exact (eq_refl (term301 A a0 a x)). Qed.
Lemma lem4792223 {A : Type'} (a0 : A) (a : A) : (term312 A a0 a) = (term296 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792222 A a0 x a)). Qed.
Lemma lem4792224 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792225 {A : Type'} (a0 : A) (a : A) : (term313 A a0 a) = (term314 A a0 a).
Proof. exact (MK_COMB (@lem4792224 A) (@lem4792223 A a0 a)). Qed.
Lemma lem4792226 {A : Type'} (a0 : A) (a : A) : (term294 A a0 a) = (term315 A a0 a).
Proof. exact (MK_COMB (@lem4792221 A a0 a) (@lem4792225 A a0 a)). Qed.
Lemma lem4792227 {A : Type'} (a0 : A) (a : A) : ((term293 A a0 a) = (term294 A a0 a)) = ((term277 A a0 a) = (term315 A a0 a)).
Proof. exact (MK_COMB (@lem4792215 A a0 a) (@lem4792226 A a0 a)). Qed.
Lemma lem4792228 {A : Type'} (a0 : A) (a : A) : (term277 A a0 a) = (term315 A a0 a).
Proof. exact (EQ_MP (@lem4792227 A a0 a) (@lem4792205 A a0 a)). Qed.
Lemma lem4792325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792326 {A : Type'} (a0 : A) (a : A) : (term284 A a0 a) = (term316 A a0 a).
Proof. exact (MK_COMB (@lem4792325) (@lem4792228 A a0 a)). Qed.
Lemma lem4792327 {A : Type'} (a0 : A) (a : A) : (term278 A a0 a) = (term278 A a0 a).
Proof. exact (eq_refl (term278 A a0 a)). Qed.
Lemma lem4792328 {A : Type'} (a0 : A) (a : A) : (term286 A a0 a) = (term317 A a0 a).
Proof. exact (MK_COMB (@lem4792326 A a0 a) (@lem4792327 A a0 a)). Qed.
Lemma lem4792329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4792330 {A : Type'} (a0 : A) (a : A) : (term288 A a0 a) = (term318 A a0 a).
Proof. exact (MK_COMB (@lem4792329) (@lem4792328 A a0 a)). Qed.
Lemma lem4792379 {A : Type'} (a0 : A) (a : A) : (term282 A a0 a) = (term282 A a0 a).
Proof. exact (eq_refl (term282 A a0 a)). Qed.
Lemma lem4792380 {A : Type'} (a0 : A) (a : A) : (term290 A a0 a) = (term319 A a0 a).
Proof. exact (MK_COMB (@lem4792330 A a0 a) (@lem4792379 A a0 a)). Qed.
Lemma lem4792382 {A : Type'} (P : A -> Prop) (Q : Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4792383 {A : Type'} (P : A -> Prop) (Q : Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (@lem4792382 A P Q). Qed.
Lemma lem4792384 {A : Type'} (a0 : A) (a : A) : (term322 A a0 a) = (term323 A a0 a).
Proof. exact (@lem4792383 A (term274 A a0 a) (a0 = a)). Qed.
Lemma lem4792385 {A : Type'} (a0 : A) (x : A) (a : A) : (term324 A a0 a x) = (term265 A a0 x a).
Proof. exact (eq_refl (term324 A a0 a x)). Qed.
Lemma lem4792386 {A : Type'} (a0 : A) (a : A) : (term325 A a0 a) = (term274 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792385 A a0 x a)). Qed.
Lemma lem4792387 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4792388 {A : Type'} (a0 : A) (a : A) : (term326 A a0 a) = (term275 A a0 a).
Proof. exact (MK_COMB (@lem4792387 A) (@lem4792386 A a0 a)). Qed.
Lemma lem4792389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792390 {A : Type'} (a0 : A) (a : A) : (term327 A a0 a) = (term280 A a0 a).
Proof. exact (MK_COMB (@lem4792389) (@lem4792388 A a0 a)). Qed.
Lemma lem4792391 {A : Type'} (a0 : A) (a : A) : (a0 = a) = (a0 = a).
Proof. exact (eq_refl (a0 = a)). Qed.
Lemma lem4792392 {A : Type'} (a0 : A) (a : A) : (term322 A a0 a) = (term282 A a0 a).
Proof. exact (MK_COMB (@lem4792390 A a0 a) (@lem4792391 A a0 a)). Qed.
Lemma lem4792393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792394 {A : Type'} (a0 : A) (a : A) : (term328 A a0 a) = (term329 A a0 a).
Proof. exact (MK_COMB (@lem4792393) (@lem4792392 A a0 a)). Qed.
Lemma lem4792395 {A : Type'} (a0 : A) (x : A) (a : A) : (term324 A a0 a x) = (term265 A a0 x a).
Proof. exact (eq_refl (term324 A a0 a x)). Qed.
Lemma lem4792396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792397 {A : Type'} (a0 : A) (x : A) (a : A) : (term330 A a0 a x) = (term331 A a0 x a).
Proof. exact (MK_COMB (@lem4792396) (@lem4792395 A a0 x a)). Qed.
Lemma lem4792398 {A : Type'} (a0 : A) (a : A) : (a0 = a) = (a0 = a).
Proof. exact (eq_refl (a0 = a)). Qed.
Lemma lem4792399 {A : Type'} (x : A) (a0 : A) (a : A) : (term332 A x a0 a) = (term333 A x a0 a).
Proof. exact (MK_COMB (@lem4792397 A a0 x a) (@lem4792398 A a0 a)). Qed.
Lemma lem4792400 {A : Type'} (a0 : A) (a : A) : (term334 A a0 a) = (term335 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792399 A x a0 a)). Qed.
Lemma lem4792401 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4792402 {A : Type'} (a0 : A) (a : A) : (term323 A a0 a) = (term336 A a0 a).
Proof. exact (MK_COMB (@lem4792401 A) (@lem4792400 A a0 a)). Qed.
Lemma lem4792403 {A : Type'} (a0 : A) (a : A) : ((term322 A a0 a) = (term323 A a0 a)) = ((term282 A a0 a) = (term336 A a0 a)).
Proof. exact (MK_COMB (@lem4792394 A a0 a) (@lem4792402 A a0 a)). Qed.
Lemma lem4792404 {A : Type'} (a0 : A) (a : A) : (term282 A a0 a) = (term336 A a0 a).
Proof. exact (EQ_MP (@lem4792403 A a0 a) (@lem4792384 A a0 a)). Qed.
Lemma lem4792405 {A : Type'} (a0 : A) (a : A) : (term318 A a0 a) = (term318 A a0 a).
Proof. exact (eq_refl (term318 A a0 a)). Qed.
Lemma lem4792406 {A : Type'} (a0 : A) (a : A) : (term319 A a0 a) = (term337 A a0 a).
Proof. exact (MK_COMB (@lem4792405 A a0 a) (@lem4792404 A a0 a)). Qed.
Lemma lem4792408 {A : Type'} (P : Prop) (Q : A -> Prop) : (term338 A P Q) = (term339 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4792409 {A : Type'} (P : Prop) (Q : A -> Prop) : (term338 A P Q) = (term339 A P Q).
Proof. exact (@lem4792408 A P Q). Qed.
Lemma lem4792410 {A : Type'} (a0 : A) (a : A) : (term340 A a0 a) = (term341 A a0 a).
Proof. exact (@lem4792409 A (term317 A a0 a) (term335 A a0 a)). Qed.
Lemma lem4792411 {A : Type'} (x : A) (a0 : A) (a : A) : (term342 A a0 a x) = (term333 A x a0 a).
Proof. exact (eq_refl (term342 A a0 a x)). Qed.
Lemma lem4792412 {A : Type'} (a0 : A) (a : A) : (term343 A a0 a) = (term335 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792411 A x a0 a)). Qed.
Lemma lem4792413 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4792414 {A : Type'} (a0 : A) (a : A) : (term344 A a0 a) = (term336 A a0 a).
Proof. exact (MK_COMB (@lem4792413 A) (@lem4792412 A a0 a)). Qed.
Lemma lem4792415 {A : Type'} (a0 : A) (a : A) : (term318 A a0 a) = (term318 A a0 a).
Proof. exact (eq_refl (term318 A a0 a)). Qed.
Lemma lem4792416 {A : Type'} (a0 : A) (a : A) : (term340 A a0 a) = (term337 A a0 a).
Proof. exact (MK_COMB (@lem4792415 A a0 a) (@lem4792414 A a0 a)). Qed.
Lemma lem4792417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792418 {A : Type'} (a0 : A) (a : A) : (term345 A a0 a) = (term346 A a0 a).
Proof. exact (MK_COMB (@lem4792417) (@lem4792416 A a0 a)). Qed.
Lemma lem4792419 {A : Type'} (x : A) (a0 : A) (a : A) : (term342 A a0 a x) = (term333 A x a0 a).
Proof. exact (eq_refl (term342 A a0 a x)). Qed.
Lemma lem4792420 {A : Type'} (a0 : A) (a : A) : (term318 A a0 a) = (term318 A a0 a).
Proof. exact (eq_refl (term318 A a0 a)). Qed.
Lemma lem4792421 {A : Type'} (x : A) (a0 : A) (a : A) : (term347 A a0 a x) = (term348 A x a0 a).
Proof. exact (MK_COMB (@lem4792420 A a0 a) (@lem4792419 A x a0 a)). Qed.
Lemma lem4792422 {A : Type'} (a0 : A) (a : A) : (term349 A a0 a) = (term350 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792421 A x a0 a)). Qed.
Lemma lem4792423 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4792424 {A : Type'} (a0 : A) (a : A) : (term341 A a0 a) = (term351 A a0 a).
Proof. exact (MK_COMB (@lem4792423 A) (@lem4792422 A a0 a)). Qed.
Lemma lem4792425 {A : Type'} (a0 : A) (a : A) : ((term340 A a0 a) = (term341 A a0 a)) = ((term337 A a0 a) = (term351 A a0 a)).
Proof. exact (MK_COMB (@lem4792418 A a0 a) (@lem4792424 A a0 a)). Qed.
Lemma lem4792426 {A : Type'} (a0 : A) (a : A) : (term337 A a0 a) = (term351 A a0 a).
Proof. exact (EQ_MP (@lem4792425 A a0 a) (@lem4792410 A a0 a)). Qed.
Lemma lem4792427 {A : Type'} (a0 : A) (a : A) : (term319 A a0 a) = (term351 A a0 a).
Proof. exact (TRANS (@lem4792406 A a0 a) (@lem4792426 A a0 a)). Qed.
Lemma lem4792428 {A : Type'} (a0 : A) (a : A) : (term290 A a0 a) = (term351 A a0 a).
Proof. exact (TRANS (@lem4792380 A a0 a) (@lem4792427 A a0 a)). Qed.
Lemma lem4792429 {A : Type'} (a0 : A) (a : A) : (term250 A a0 a) = (term351 A a0 a).
Proof. exact (TRANS (@lem4792201 A a0 a) (@lem4792428 A a0 a)). Qed.
Lemma lem4792430 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : term351 A a0 a.
Proof. exact (EQ_MP (@lem4792429 A a0 a) (@lem4792149 A a0 a h1)). Qed.
Lemma lem4792431 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term348 A x a0 a) : term348 A x a0 a.
Proof. exact (h1). Qed.
Lemma lem4792472 {A : Type'} (x : A) (a0 : A) (a : A) : (term333 A x a0 a) = (term333 A x a0 a).
Proof. exact (eq_refl (term333 A x a0 a)). Qed.
Lemma lem4792479 {A : Type'} (a0 : A) (a : A) : (term278 A a0 a) = (term278 A a0 a).
Proof. exact (eq_refl (term278 A a0 a)). Qed.
Lemma lem4792494 {A : Type'} (a0 : A) (x : A) (a : A) : (term302 A a0 x a) = (term302 A a0 x a).
Proof. exact (eq_refl (term302 A a0 x a)). Qed.
Lemma lem4792495 {A : Type'} (a0 : A) (a : A) : (term296 A a0 a) = (term296 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792494 A a0 x a)). Qed.
Lemma lem4792496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792497 {A : Type'} (a0 : A) (a : A) : (term314 A a0 a) = (term314 A a0 a).
Proof. exact (MK_COMB (@lem4792496 A) (@lem4792495 A a0 a)). Qed.
Lemma lem4792512 {A : Type'} (a0 : A) (x : A) (a : A) : (term298 A a0 x a) = (term298 A a0 x a).
Proof. exact (eq_refl (term298 A a0 x a)). Qed.
Lemma lem4792513 {A : Type'} (a0 : A) (a : A) : (term295 A a0 a) = (term295 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792512 A a0 x a)). Qed.
Lemma lem4792514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792515 {A : Type'} (a0 : A) (a : A) : (term309 A a0 a) = (term309 A a0 a).
Proof. exact (MK_COMB (@lem4792514 A) (@lem4792513 A a0 a)). Qed.
Lemma lem4792516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792517 {A : Type'} (a0 : A) (a : A) : (term311 A a0 a) = (term311 A a0 a).
Proof. exact (MK_COMB (@lem4792516) (@lem4792515 A a0 a)). Qed.
Lemma lem4792518 {A : Type'} (a0 : A) (a : A) : (term315 A a0 a) = (term315 A a0 a).
Proof. exact (MK_COMB (@lem4792517 A a0 a) (@lem4792497 A a0 a)). Qed.
Lemma lem4792519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4792520 {A : Type'} (a0 : A) (a : A) : (term316 A a0 a) = (term316 A a0 a).
Proof. exact (MK_COMB (@lem4792519) (@lem4792518 A a0 a)). Qed.
Lemma lem4792521 {A : Type'} (a0 : A) (a : A) : (term317 A a0 a) = (term317 A a0 a).
Proof. exact (MK_COMB (@lem4792520 A a0 a) (@lem4792479 A a0 a)). Qed.
Lemma lem4792522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4792523 {A : Type'} (a0 : A) (a : A) : (term318 A a0 a) = (term318 A a0 a).
Proof. exact (MK_COMB (@lem4792522) (@lem4792521 A a0 a)). Qed.
Lemma lem4792524 {A : Type'} (x : A) (a0 : A) (a : A) : (term348 A x a0 a) = (term348 A x a0 a).
Proof. exact (MK_COMB (@lem4792523 A a0 a) (@lem4792472 A x a0 a)). Qed.
Lemma lem4792525 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term348 A x a0 a) : term348 A x a0 a.
Proof. exact (EQ_MP (@lem4792524 A x a0 a) (@lem4792431 A x a0 a h1)). Qed.
Lemma lem4792526 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term317 A a0 a.
Proof. exact (h1). Qed.
Lemma lem4792527 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : term333 A x a0 a.
Proof. exact (h1). Qed.
Lemma lem4792529 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term315 A a0 a.
Proof. exact (proj1 (@lem4792526 A a0 a h1)). Qed.
Lemma lem4792530 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term314 A a0 a.
Proof. exact (proj2 (@lem4792529 A a0 a h1)). Qed.
Lemma lem4792533 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : term265 A a0 x a.
Proof. exact (proj1 (@lem4792527 A x a0 a h1)). Qed.
Lemma lem4792534 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : term352 A a0 x a.
Proof. exact (proj2 (@lem4792533 A x a0 a h1)). Qed.
Lemma lem4792535 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : term353 A a0 x a.
Proof. exact (proj1 (@lem4792533 A x a0 a h1)). Qed.
Lemma lem4792566 {A : Type'} (a0 : A) (x : A) (a : A) : (term302 A a0 x a) = (term302 A a0 x a).
Proof. exact (eq_refl (term302 A a0 x a)). Qed.
Lemma lem4792567 {A : Type'} (a0 : A) (a : A) : (term296 A a0 a) = (term296 A a0 a).
Proof. exact (fun_ext (fun x : A => @lem4792566 A a0 x a)). Qed.
Lemma lem4792568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4792570 {A : Type'} (a0 : A) (a : A) : (term314 A a0 a) = (term314 A a0 a).
Proof. exact (MK_COMB (@lem4792568 A) (@lem4792567 A a0 a)). Qed.
Lemma lem4792571 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term314 A a0 a.
Proof. exact (EQ_MP (@lem4792570 A a0 a) (@lem4792530 A a0 a h1)). Qed.
Lemma lem4792579 {A : Type'} (x : A) (a0 : A) (h1 : term278 A x a0) : term278 A x a0.
Proof. exact (h1). Qed.
Lemma lem4792583 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : x = a0.
Proof. exact (h1). Qed.
Lemma lem4792591 {A : Type'} (x : A) (a0 : A) (h1 : term278 A x a0) : term278 A x a0.
Proof. exact (h1). Qed.
Lemma lem4792595 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4792603 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) : term278 A x a.
Proof. exact (h1). Qed.
Lemma lem4792607 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : x = a0.
Proof. exact (h1). Qed.
Lemma lem4792615 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) : term278 A x a.
Proof. exact (h1). Qed.
Lemma lem4792619 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4792623 {A : Type'} (_59278 : A) (a0 : A) (a : A) (h1 : term317 A a0 a) : term301 A a0 a _59278.
Proof. exact (@lem4792571 A a0 a h1 _59278). Qed.
Lemma lem4792624 {A : Type'} (a0 : A) (_59278 : A) (a : A) : (term301 A a0 a _59278) = (term302 A a0 _59278 a).
Proof. exact (eq_refl (term301 A a0 a _59278)). Qed.
Lemma lem4792627 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term278 A a0 a.
Proof. exact (proj2 (@lem4792526 A a0 a h1)). Qed.
Lemma lem4792639 {A : Type'} (_59278 : A) (a0 : A) (a : A) (h1 : term317 A a0 a) : term302 A a0 _59278 a.
Proof. exact (EQ_MP (@lem4792624 A a0 _59278 a) (@lem4792623 A _59278 a0 a h1)). Qed.
Lemma lem4792643 {A : Type'} (x : A) (a0 : A) (h1 : term278 A x a0) : term278 A x a0.
Proof. exact (h1). Qed.
Lemma lem4792645 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : x = a0.
Proof. exact (h1). Qed.
Lemma lem4792649 {A : Type'} (x : A) (a0 : A) (h1 : term278 A x a0) : term278 A x a0.
Proof. exact (h1). Qed.
Lemma lem4792651 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4792655 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) : term278 A x a.
Proof. exact (h1). Qed.
Lemma lem4792657 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : x = a0.
Proof. exact (h1). Qed.
Lemma lem4792661 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) : term278 A x a.
Proof. exact (h1). Qed.
Lemma lem4792663 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4792691 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : a0 = a.
Proof. exact (proj2 (@lem4792527 A x a0 a h1)). Qed.
Lemma lem4792692 {A : Type'} (a0 : A) : (term354 A a0) = (term354 A a0).
Proof. exact (eq_refl (term354 A a0)). Qed.
Lemma lem4792693 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : (term355 A a0 x) = (term356 A a0).
Proof. exact (MK_COMB (@lem4792692 A a0) (@lem4792645 A x a0 h1)). Qed.
Lemma lem4792694 {A : Type'} (a0 : A) : (term356 A a0) = (term357 A a0).
Proof. exact (eq_refl (term356 A a0)). Qed.
Lemma lem4792695 {A : Type'} (a0 : A) (x : A) : (term358 A a0 x) = (term358 A a0 x).
Proof. exact (eq_refl (term358 A a0 x)). Qed.
Lemma lem4792696 {A : Type'} (x : A) (a0 : A) : ((term355 A a0 x) = (term356 A a0)) = ((term355 A a0 x) = (term357 A a0)).
Proof. exact (MK_COMB (@lem4792695 A a0 x) (@lem4792694 A a0)). Qed.
Lemma lem4792697 {A : Type'} (x : A) (a0 : A) : (term355 A a0 x) = (term278 A x a0).
Proof. exact (eq_refl (term355 A a0 x)). Qed.
Lemma lem4792698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792699 {A : Type'} (x : A) (a0 : A) : (term358 A a0 x) = (term359 A x a0).
Proof. exact (MK_COMB (@lem4792698) (@lem4792697 A x a0)). Qed.
Lemma lem4792700 {A : Type'} (a0 : A) : (term357 A a0) = (term357 A a0).
Proof. exact (eq_refl (term357 A a0)). Qed.
Lemma lem4792701 {A : Type'} (x : A) (a0 : A) : ((term355 A a0 x) = (term357 A a0)) = ((term278 A x a0) = (term357 A a0)).
Proof. exact (MK_COMB (@lem4792699 A x a0) (@lem4792700 A a0)). Qed.
Lemma lem4792702 {A : Type'} (x : A) (a0 : A) : ((term355 A a0 x) = (term356 A a0)) = ((term278 A x a0) = (term357 A a0)).
Proof. exact (TRANS (@lem4792696 A x a0) (@lem4792701 A x a0)). Qed.
Lemma lem4792703 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : (term278 A x a0) = (term357 A a0).
Proof. exact (EQ_MP (@lem4792702 A x a0) (@lem4792693 A x a0 h1)). Qed.
Lemma lem4792704 {A : Type'} (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : x = a0) : term357 A a0.
Proof. exact (EQ_MP (@lem4792703 A x a0 h2) (@lem4792643 A x a0 h1)). Qed.
Lemma lem4792719 {A : Type'} : (term360 A) = (term360 A).
Proof. exact (eq_refl (term360 A)). Qed.
Lemma lem4792720 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : (term361 A a0) = (term361 A a).
Proof. exact (MK_COMB (@lem4792719 A) (@lem4792691 A x a0 a h1)). Qed.
Lemma lem4792721 {A : Type'} (a : A) : (term361 A a) = (term357 A a).
Proof. exact (eq_refl (term361 A a)). Qed.
Lemma lem4792722 {A : Type'} (a0 : A) : (term362 A a0) = (term362 A a0).
Proof. exact (eq_refl (term362 A a0)). Qed.
Lemma lem4792723 {A : Type'} (a0 : A) (a : A) : ((term361 A a0) = (term361 A a)) = ((term361 A a0) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792722 A a0) (@lem4792721 A a)). Qed.
Lemma lem4792724 {A : Type'} (a0 : A) : (term361 A a0) = (term357 A a0).
Proof. exact (eq_refl (term361 A a0)). Qed.
Lemma lem4792725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792726 {A : Type'} (a0 : A) : (term362 A a0) = (term363 A a0).
Proof. exact (MK_COMB (@lem4792725) (@lem4792724 A a0)). Qed.
Lemma lem4792727 {A : Type'} (a : A) : (term357 A a) = (term357 A a).
Proof. exact (eq_refl (term357 A a)). Qed.
Lemma lem4792728 {A : Type'} (a0 : A) (a : A) : ((term361 A a0) = (term357 A a)) = ((term357 A a0) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792726 A a0) (@lem4792727 A a)). Qed.
Lemma lem4792729 {A : Type'} (a0 : A) (a : A) : ((term361 A a0) = (term361 A a)) = ((term357 A a0) = (term357 A a)).
Proof. exact (TRANS (@lem4792723 A a0 a) (@lem4792728 A a0 a)). Qed.
Lemma lem4792730 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : (term357 A a0) = (term357 A a).
Proof. exact (EQ_MP (@lem4792729 A a0 a) (@lem4792720 A x a0 a h1)). Qed.
Lemma lem4792731 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : term357 A a.
Proof. exact (EQ_MP (@lem4792730 A x a0 a h2) (@lem4792704 A x a0 h1 h3)). Qed.
Lemma lem4792759 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : a0 = a.
Proof. exact (proj2 (@lem4792527 A x a0 a h1)). Qed.
Lemma lem4792760 {A : Type'} (a0 : A) : (term354 A a0) = (term354 A a0).
Proof. exact (eq_refl (term354 A a0)). Qed.
Lemma lem4792761 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : x = a) : (term355 A a0 x) = (term355 A a0 a).
Proof. exact (MK_COMB (@lem4792760 A a0) (@lem4792651 A x a h1)). Qed.
Lemma lem4792762 {A : Type'} (a : A) (a0 : A) : (term355 A a0 a) = (term278 A a a0).
Proof. exact (eq_refl (term355 A a0 a)). Qed.
Lemma lem4792763 {A : Type'} (a0 : A) (x : A) : (term358 A a0 x) = (term358 A a0 x).
Proof. exact (eq_refl (term358 A a0 x)). Qed.
Lemma lem4792764 {A : Type'} (x : A) (a : A) (a0 : A) : ((term355 A a0 x) = (term355 A a0 a)) = ((term355 A a0 x) = (term278 A a a0)).
Proof. exact (MK_COMB (@lem4792763 A a0 x) (@lem4792762 A a a0)). Qed.
Lemma lem4792765 {A : Type'} (x : A) (a0 : A) : (term355 A a0 x) = (term278 A x a0).
Proof. exact (eq_refl (term355 A a0 x)). Qed.
Lemma lem4792766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792767 {A : Type'} (x : A) (a0 : A) : (term358 A a0 x) = (term359 A x a0).
Proof. exact (MK_COMB (@lem4792766) (@lem4792765 A x a0)). Qed.
Lemma lem4792768 {A : Type'} (a : A) (a0 : A) : (term278 A a a0) = (term278 A a a0).
Proof. exact (eq_refl (term278 A a a0)). Qed.
Lemma lem4792769 {A : Type'} (x : A) (a : A) (a0 : A) : ((term355 A a0 x) = (term278 A a a0)) = ((term278 A x a0) = (term278 A a a0)).
Proof. exact (MK_COMB (@lem4792767 A x a0) (@lem4792768 A a a0)). Qed.
Lemma lem4792770 {A : Type'} (x : A) (a : A) (a0 : A) : ((term355 A a0 x) = (term355 A a0 a)) = ((term278 A x a0) = (term278 A a a0)).
Proof. exact (TRANS (@lem4792764 A x a a0) (@lem4792769 A x a a0)). Qed.
Lemma lem4792771 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : x = a) : (term278 A x a0) = (term278 A a a0).
Proof. exact (EQ_MP (@lem4792770 A x a a0) (@lem4792761 A a0 x a h1)). Qed.
Lemma lem4792772 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : x = a) : term278 A a a0.
Proof. exact (EQ_MP (@lem4792771 A a0 x a h2) (@lem4792649 A x a0 h1)). Qed.
Lemma lem4792787 {A : Type'} (a : A) : (term364 A a) = (term364 A a).
Proof. exact (eq_refl (term364 A a)). Qed.
Lemma lem4792788 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : (term365 A a a0) = (term366 A a).
Proof. exact (MK_COMB (@lem4792787 A a) (@lem4792759 A x a0 a h1)). Qed.
Lemma lem4792789 {A : Type'} (a : A) : (term366 A a) = (term357 A a).
Proof. exact (eq_refl (term366 A a)). Qed.
Lemma lem4792790 {A : Type'} (a : A) (a0 : A) : (term367 A a a0) = (term367 A a a0).
Proof. exact (eq_refl (term367 A a a0)). Qed.
Lemma lem4792791 {A : Type'} (a0 : A) (a : A) : ((term365 A a a0) = (term366 A a)) = ((term365 A a a0) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792790 A a a0) (@lem4792789 A a)). Qed.
Lemma lem4792792 {A : Type'} (a : A) (a0 : A) : (term365 A a a0) = (term278 A a a0).
Proof. exact (eq_refl (term365 A a a0)). Qed.
Lemma lem4792793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792794 {A : Type'} (a : A) (a0 : A) : (term367 A a a0) = (term359 A a a0).
Proof. exact (MK_COMB (@lem4792793) (@lem4792792 A a a0)). Qed.
Lemma lem4792795 {A : Type'} (a : A) : (term357 A a) = (term357 A a).
Proof. exact (eq_refl (term357 A a)). Qed.
Lemma lem4792796 {A : Type'} (a0 : A) (a : A) : ((term365 A a a0) = (term357 A a)) = ((term278 A a a0) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792794 A a a0) (@lem4792795 A a)). Qed.
Lemma lem4792797 {A : Type'} (a0 : A) (a : A) : ((term365 A a a0) = (term366 A a)) = ((term278 A a a0) = (term357 A a)).
Proof. exact (TRANS (@lem4792791 A a0 a) (@lem4792796 A a0 a)). Qed.
Lemma lem4792798 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : (term278 A a a0) = (term357 A a).
Proof. exact (EQ_MP (@lem4792797 A a0 a) (@lem4792788 A x a0 a h1)). Qed.
Lemma lem4792799 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : term357 A a.
Proof. exact (EQ_MP (@lem4792798 A x a0 a h2) (@lem4792772 A a0 x a h1 h3)). Qed.
Lemma lem4792827 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : a0 = a.
Proof. exact (proj2 (@lem4792527 A x a0 a h1)). Qed.
Lemma lem4792828 {A : Type'} (a : A) : (term354 A a) = (term354 A a).
Proof. exact (eq_refl (term354 A a)). Qed.
Lemma lem4792829 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : x = a0) : (term355 A a x) = (term355 A a a0).
Proof. exact (MK_COMB (@lem4792828 A a) (@lem4792657 A x a0 h1)). Qed.
Lemma lem4792830 {A : Type'} (a0 : A) (a : A) : (term355 A a a0) = (term278 A a0 a).
Proof. exact (eq_refl (term355 A a a0)). Qed.
Lemma lem4792831 {A : Type'} (a : A) (x : A) : (term358 A a x) = (term358 A a x).
Proof. exact (eq_refl (term358 A a x)). Qed.
Lemma lem4792832 {A : Type'} (x : A) (a0 : A) (a : A) : ((term355 A a x) = (term355 A a a0)) = ((term355 A a x) = (term278 A a0 a)).
Proof. exact (MK_COMB (@lem4792831 A a x) (@lem4792830 A a0 a)). Qed.
Lemma lem4792833 {A : Type'} (x : A) (a : A) : (term355 A a x) = (term278 A x a).
Proof. exact (eq_refl (term355 A a x)). Qed.
Lemma lem4792834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792835 {A : Type'} (x : A) (a : A) : (term358 A a x) = (term359 A x a).
Proof. exact (MK_COMB (@lem4792834) (@lem4792833 A x a)). Qed.
Lemma lem4792836 {A : Type'} (a0 : A) (a : A) : (term278 A a0 a) = (term278 A a0 a).
Proof. exact (eq_refl (term278 A a0 a)). Qed.
Lemma lem4792837 {A : Type'} (x : A) (a0 : A) (a : A) : ((term355 A a x) = (term278 A a0 a)) = ((term278 A x a) = (term278 A a0 a)).
Proof. exact (MK_COMB (@lem4792835 A x a) (@lem4792836 A a0 a)). Qed.
Lemma lem4792838 {A : Type'} (x : A) (a0 : A) (a : A) : ((term355 A a x) = (term355 A a a0)) = ((term278 A x a) = (term278 A a0 a)).
Proof. exact (TRANS (@lem4792832 A x a0 a) (@lem4792837 A x a0 a)). Qed.
Lemma lem4792839 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : x = a0) : (term278 A x a) = (term278 A a0 a).
Proof. exact (EQ_MP (@lem4792838 A x a0 a) (@lem4792829 A a x a0 h1)). Qed.
Lemma lem4792840 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : x = a0) : term278 A a0 a.
Proof. exact (EQ_MP (@lem4792839 A a x a0 h2) (@lem4792655 A x a h1)). Qed.
Lemma lem4792855 {A : Type'} (a : A) : (term354 A a) = (term354 A a).
Proof. exact (eq_refl (term354 A a)). Qed.
Lemma lem4792856 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : (term355 A a a0) = (term356 A a).
Proof. exact (MK_COMB (@lem4792855 A a) (@lem4792827 A x a0 a h1)). Qed.
Lemma lem4792857 {A : Type'} (a : A) : (term356 A a) = (term357 A a).
Proof. exact (eq_refl (term356 A a)). Qed.
Lemma lem4792858 {A : Type'} (a : A) (a0 : A) : (term358 A a a0) = (term358 A a a0).
Proof. exact (eq_refl (term358 A a a0)). Qed.
Lemma lem4792859 {A : Type'} (a0 : A) (a : A) : ((term355 A a a0) = (term356 A a)) = ((term355 A a a0) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792858 A a a0) (@lem4792857 A a)). Qed.
Lemma lem4792860 {A : Type'} (a0 : A) (a : A) : (term355 A a a0) = (term278 A a0 a).
Proof. exact (eq_refl (term355 A a a0)). Qed.
Lemma lem4792861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792862 {A : Type'} (a0 : A) (a : A) : (term358 A a a0) = (term359 A a0 a).
Proof. exact (MK_COMB (@lem4792861) (@lem4792860 A a0 a)). Qed.
Lemma lem4792863 {A : Type'} (a : A) : (term357 A a) = (term357 A a).
Proof. exact (eq_refl (term357 A a)). Qed.
Lemma lem4792864 {A : Type'} (a0 : A) (a : A) : ((term355 A a a0) = (term357 A a)) = ((term278 A a0 a) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792862 A a0 a) (@lem4792863 A a)). Qed.
Lemma lem4792865 {A : Type'} (a0 : A) (a : A) : ((term355 A a a0) = (term356 A a)) = ((term278 A a0 a) = (term357 A a)).
Proof. exact (TRANS (@lem4792859 A a0 a) (@lem4792864 A a0 a)). Qed.
Lemma lem4792866 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : (term278 A a0 a) = (term357 A a).
Proof. exact (EQ_MP (@lem4792865 A a0 a) (@lem4792856 A x a0 a h1)). Qed.
Lemma lem4792867 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : term357 A a.
Proof. exact (EQ_MP (@lem4792866 A x a0 a h2) (@lem4792840 A a x a0 h1 h3)). Qed.
Lemma lem4792896 {A : Type'} (a : A) : (term354 A a) = (term354 A a).
Proof. exact (eq_refl (term354 A a)). Qed.
Lemma lem4792897 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term355 A a x) = (term356 A a).
Proof. exact (MK_COMB (@lem4792896 A a) (@lem4792663 A x a h1)). Qed.
Lemma lem4792898 {A : Type'} (a : A) : (term356 A a) = (term357 A a).
Proof. exact (eq_refl (term356 A a)). Qed.
Lemma lem4792899 {A : Type'} (a : A) (x : A) : (term358 A a x) = (term358 A a x).
Proof. exact (eq_refl (term358 A a x)). Qed.
Lemma lem4792900 {A : Type'} (x : A) (a : A) : ((term355 A a x) = (term356 A a)) = ((term355 A a x) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792899 A a x) (@lem4792898 A a)). Qed.
Lemma lem4792901 {A : Type'} (x : A) (a : A) : (term355 A a x) = (term278 A x a).
Proof. exact (eq_refl (term355 A a x)). Qed.
Lemma lem4792902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792903 {A : Type'} (x : A) (a : A) : (term358 A a x) = (term359 A x a).
Proof. exact (MK_COMB (@lem4792902) (@lem4792901 A x a)). Qed.
Lemma lem4792904 {A : Type'} (a : A) : (term357 A a) = (term357 A a).
Proof. exact (eq_refl (term357 A a)). Qed.
Lemma lem4792905 {A : Type'} (x : A) (a : A) : ((term355 A a x) = (term357 A a)) = ((term278 A x a) = (term357 A a)).
Proof. exact (MK_COMB (@lem4792903 A x a) (@lem4792904 A a)). Qed.
Lemma lem4792906 {A : Type'} (x : A) (a : A) : ((term355 A a x) = (term356 A a)) = ((term278 A x a) = (term357 A a)).
Proof. exact (TRANS (@lem4792900 A x a) (@lem4792905 A x a)). Qed.
Lemma lem4792907 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term278 A x a) = (term357 A a).
Proof. exact (EQ_MP (@lem4792906 A x a) (@lem4792897 A x a h1)). Qed.
Lemma lem4792936 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : term357 A a.
Proof. exact (EQ_MP (@lem4792907 A x a h2) (@lem4792661 A x a h1)). Qed.
Lemma lem4792940 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4792941 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4792940 A x). Qed.
Lemma lem4792942 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (@lem4792941 A a0). Qed.
Lemma lem4792943 {A : Type'} (a0 : A) : term368 A a0.
Proof. exact (fun h0 : term357 A a0 => @lem4792942 A a0). Qed.
Lemma lem4792945 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4792946 {A : Type'} (a0 : A) : (term368 A a0) = (a0 = a0).
Proof. exact (@lem4792945 (a0 = a0)). Qed.
Lemma lem4792947 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (EQ_MP (@lem4792946 A a0) (@lem4792943 A a0)). Qed.
Lemma lem4792953 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4792954 {A : Type'} (a : A) (_59278 : A) (a0 : A) : (term302 A a0 _59278 a) = (term298 A a _59278 a0).
Proof. exact (@lem4792953 (_59278 = a) (term278 A _59278 a0)). Qed.
Lemma lem4792964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4792965 {A : Type'} (a : A) (_59278 : A) (a0 : A) : (term370 A a0 _59278 a) = (term371 A a _59278 a0).
Proof. exact (MK_COMB (@lem4792964) (@lem4792954 A a _59278 a0)). Qed.
Lemma lem4792975 {A : Type'} (a : A) (_59278 : A) (a0 : A) : (term298 A a _59278 a0) = (term298 A a _59278 a0).
Proof. exact (eq_refl (term298 A a _59278 a0)). Qed.
Lemma lem4792976 {A : Type'} (a : A) (_59278 : A) (a0 : A) : ((term302 A a0 _59278 a) = (term298 A a _59278 a0)) = ((term298 A a _59278 a0) = (term298 A a _59278 a0)).
Proof. exact (MK_COMB (@lem4792965 A a _59278 a0) (@lem4792975 A a _59278 a0)). Qed.
Lemma lem4792978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4792979 (x : Prop) : (x = x) = True.
Proof. exact (@lem4792978 Prop x). Qed.
Lemma lem4792980 {A : Type'} (a : A) (_59278 : A) (a0 : A) : ((term298 A a _59278 a0) = (term298 A a _59278 a0)) = True.
Proof. exact (@lem4792979 (term298 A a _59278 a0)). Qed.
Lemma lem4792981 {A : Type'} (a : A) (_59278 : A) (a0 : A) : ((term302 A a0 _59278 a) = (term298 A a _59278 a0)) = True.
Proof. exact (TRANS (@lem4792976 A a _59278 a0) (@lem4792980 A a _59278 a0)). Qed.
Lemma lem4792982 {A : Type'} (a : A) (_59278 : A) (a0 : A) : True = ((term302 A a0 _59278 a) = (term298 A a _59278 a0)).
Proof. exact (SYM (@lem4792981 A a _59278 a0)). Qed.
Lemma lem4792983 {A : Type'} (a : A) (_59278 : A) (a0 : A) : (term302 A a0 _59278 a) = (term298 A a _59278 a0).
Proof. exact (EQ_MP (@lem4792982 A a _59278 a0) (@lem0)). Qed.
Lemma lem4792984 {A : Type'} (_59278 : A) (a0 : A) (a : A) (h1 : term317 A a0 a) : term298 A a _59278 a0.
Proof. exact (EQ_MP (@lem4792983 A a _59278 a0) (@lem4792639 A _59278 a0 a h1)). Qed.
Lemma lem4792986 (b : Prop) (a : Prop) : (a \/ b) = (term372 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4792987 {A : Type'} (a0 : A) (_59278 : A) (a : A) : (term298 A a _59278 a0) = (term373 A a0 _59278 a).
Proof. exact (@lem4792986 (term278 A _59278 a0) (_59278 = a)). Qed.
Lemma lem4792989 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4792990 {A : Type'} (_59278 : A) (a0 : A) : (term374 A _59278 a0) = (_59278 = a0).
Proof. exact (@lem4792989 (_59278 = a0)). Qed.
Lemma lem4792991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4792992 {A : Type'} (_59278 : A) (a0 : A) : (term375 A _59278 a0) = (term376 A _59278 a0).
Proof. exact (MK_COMB (@lem4792991) (@lem4792990 A _59278 a0)). Qed.
Lemma lem4792993 {A : Type'} (_59278 : A) (a : A) : (_59278 = a) = (_59278 = a).
Proof. exact (eq_refl (_59278 = a)). Qed.
Lemma lem4792994 {A : Type'} (a0 : A) (_59278 : A) (a : A) : (term373 A a0 _59278 a) = (term377 A a0 _59278 a).
Proof. exact (MK_COMB (@lem4792992 A _59278 a0) (@lem4792993 A _59278 a)). Qed.
Lemma lem4792995 {A : Type'} (a0 : A) (_59278 : A) (a : A) : (term298 A a _59278 a0) = (term377 A a0 _59278 a).
Proof. exact (TRANS (@lem4792987 A a0 _59278 a) (@lem4792994 A a0 _59278 a)). Qed.
Lemma lem4792998 {A : Type'} (_59278 : A) (a0 : A) (a : A) (h1 : term317 A a0 a) : term377 A a0 _59278 a.
Proof. exact (EQ_MP (@lem4792995 A a0 _59278 a) (@lem4792984 A _59278 a0 a h1)). Qed.
Lemma lem4792999 {A : Type'} (_59278 : A) (a0 : A) (a : A) (h1 : term317 A a0 a) : term377 A a0 _59278 a.
Proof. exact (@lem4792998 A _59278 a0 a h1). Qed.
Lemma lem4793000 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term378 A a0 a.
Proof. exact (@lem4792999 A a0 a0 a h1). Qed.
Lemma lem4793003 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : a0 = a.
Proof. exact (@lem4793000 A a0 a h1 (@lem4792947 A a0)). Qed.
Lemma lem4793004 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term379 A a0 a.
Proof. exact (fun h0 : term278 A a0 a => @lem4793003 A a0 a h1). Qed.
Lemma lem4793006 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793007 {A : Type'} (a0 : A) (a : A) : (term379 A a0 a) = (a0 = a).
Proof. exact (@lem4793006 (a0 = a)). Qed.
Lemma lem4793008 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : a0 = a.
Proof. exact (EQ_MP (@lem4793007 A a0 a) (@lem4793004 A a0 a h1)). Qed.
Lemma lem4793011 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4793013 {A : Type'} (a0 : A) (a : A) : (term278 A a0 a) = (term380 A a0 a).
Proof. exact (@lem4793011 (a0 = a)). Qed.
Lemma lem4793016 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term380 A a0 a.
Proof. exact (EQ_MP (@lem4793013 A a0 a) (@lem4792627 A a0 a h1)). Qed.
Lemma lem4793019 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : False.
Proof. exact (@lem4793016 A a0 a h1 (@lem4793008 A a0 a h1)). Qed.
Lemma lem4793020 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : term381.
Proof. exact (fun h0 : ~ False => @lem4793019 A a0 a h1). Qed.
Lemma lem4793022 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793023 : term381 = False.
Proof. exact (@lem4793022 False). Qed.
Lemma lem4793024 {A : Type'} (a0 : A) (a : A) (h1 : term317 A a0 a) : False.
Proof. exact (EQ_MP (@lem4793023) (@lem4793020 A a0 a h1)). Qed.
Lemma lem4793028 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4793029 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4793028 A x). Qed.
Lemma lem4793030 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4793029 A a). Qed.
Lemma lem4793031 {A : Type'} (a : A) : term368 A a.
Proof. exact (fun h0 : term357 A a => @lem4793030 A a). Qed.
Lemma lem4793033 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793034 {A : Type'} (a : A) : (term368 A a) = (a = a).
Proof. exact (@lem4793033 (a = a)). Qed.
Lemma lem4793035 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4793034 A a) (@lem4793031 A a)). Qed.
Lemma lem4793038 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4793040 {A : Type'} (a : A) : (term357 A a) = (term382 A a).
Proof. exact (@lem4793038 (a = a)). Qed.
Lemma lem4793043 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : term382 A a.
Proof. exact (EQ_MP (@lem4793040 A a) (@lem4792731 A a x a0 h1 h2 h3)). Qed.
Lemma lem4793046 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (@lem4793043 A a x a0 h1 h2 h3 (@lem4793035 A a)). Qed.
Lemma lem4793047 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : term381.
Proof. exact (fun h0 : ~ False => @lem4793046 A a x a0 h1 h2 h3). Qed.
Lemma lem4793049 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793050 : term381 = False.
Proof. exact (@lem4793049 False). Qed.
Lemma lem4793055 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4793056 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4793055 A x). Qed.
Lemma lem4793057 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4793056 A a). Qed.
Lemma lem4793058 {A : Type'} (a : A) : term368 A a.
Proof. exact (fun h0 : term357 A a => @lem4793057 A a). Qed.
Lemma lem4793060 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793061 {A : Type'} (a : A) : (term368 A a) = (a = a).
Proof. exact (@lem4793060 (a = a)). Qed.
Lemma lem4793062 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4793061 A a) (@lem4793058 A a)). Qed.
Lemma lem4793065 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4793067 {A : Type'} (a : A) : (term357 A a) = (term382 A a).
Proof. exact (@lem4793065 (a = a)). Qed.
Lemma lem4793070 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : term382 A a.
Proof. exact (EQ_MP (@lem4793067 A a) (@lem4792799 A a0 x a h1 h2 h3)). Qed.
Lemma lem4793073 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (@lem4793070 A a0 x a h1 h2 h3 (@lem4793062 A a)). Qed.
Lemma lem4793074 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : term381.
Proof. exact (fun h0 : ~ False => @lem4793073 A a0 x a h1 h2 h3). Qed.
Lemma lem4793076 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793077 : term381 = False.
Proof. exact (@lem4793076 False). Qed.
Lemma lem4793082 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4793083 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4793082 A x). Qed.
Lemma lem4793084 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4793083 A a). Qed.
Lemma lem4793085 {A : Type'} (a : A) : term368 A a.
Proof. exact (fun h0 : term357 A a => @lem4793084 A a). Qed.
Lemma lem4793087 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793088 {A : Type'} (a : A) : (term368 A a) = (a = a).
Proof. exact (@lem4793087 (a = a)). Qed.
Lemma lem4793089 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4793088 A a) (@lem4793085 A a)). Qed.
Lemma lem4793092 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4793094 {A : Type'} (a : A) : (term357 A a) = (term382 A a).
Proof. exact (@lem4793092 (a = a)). Qed.
Lemma lem4793097 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : term382 A a.
Proof. exact (EQ_MP (@lem4793094 A a) (@lem4792867 A a x a0 h1 h2 h3)). Qed.
Lemma lem4793100 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (@lem4793097 A a x a0 h1 h2 h3 (@lem4793089 A a)). Qed.
Lemma lem4793101 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : term381.
Proof. exact (fun h0 : ~ False => @lem4793100 A a x a0 h1 h2 h3). Qed.
Lemma lem4793103 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793104 : term381 = False.
Proof. exact (@lem4793103 False). Qed.
Lemma lem4793109 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4793110 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4793109 A x). Qed.
Lemma lem4793111 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4793110 A a). Qed.
Lemma lem4793112 {A : Type'} (a : A) : term368 A a.
Proof. exact (fun h0 : term357 A a => @lem4793111 A a). Qed.
Lemma lem4793114 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793115 {A : Type'} (a : A) : (term368 A a) = (a = a).
Proof. exact (@lem4793114 (a = a)). Qed.
Lemma lem4793116 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4793115 A a) (@lem4793112 A a)). Qed.
Lemma lem4793119 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4793121 {A : Type'} (a : A) : (term357 A a) = (term382 A a).
Proof. exact (@lem4793119 (a = a)). Qed.
Lemma lem4793124 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : term382 A a.
Proof. exact (EQ_MP (@lem4793121 A a) (@lem4792936 A x a h1 h2)). Qed.
Lemma lem4793127 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (@lem4793124 A x a h1 h2 (@lem4793116 A a)). Qed.
Lemma lem4793128 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : term381.
Proof. exact (fun h0 : ~ False => @lem4793127 A x a h1 h2). Qed.
Lemma lem4793130 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4793131 : term381 = False.
Proof. exact (@lem4793130 False). Qed.
Lemma lem4793134 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793131) (@lem4793128 A x a h1 h2)). Qed.
Lemma lem4793136 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793104) (@lem4793101 A a x a0 h1 h2 h3)). Qed.
Lemma lem4793138 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793077) (@lem4793074 A a0 x a h1 h2 h3)). Qed.
Lemma lem4793140 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793050) (@lem4793047 A a x a0 h1 h2 h3)). Qed.
Lemma lem4793141 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4793134 A x a h1 h2) (fun h3 : False => @lem4792663 A x a h2)). Qed.
Lemma lem4793142 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793141 A x a h1 h2) (@lem4792663 A x a h2)). Qed.
Lemma lem4793143 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : (term278 A x a) = False.
Proof. exact (prop_ext (fun h3 : term278 A x a => @lem4793142 A x a h1 h2) (fun h3 : False => @lem4792661 A x a h1)). Qed.
Lemma lem4793144 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793143 A x a h1 h2) (@lem4792661 A x a h1)). Qed.
Lemma lem4793145 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem4793136 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792657 A x a0 h3)). Qed.
Lemma lem4793146 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793145 A a x a0 h1 h2 h3) (@lem4792657 A x a0 h3)). Qed.
Lemma lem4793147 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : (term278 A x a) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a => @lem4793146 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792655 A x a h1)). Qed.
Lemma lem4793148 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793147 A a x a0 h1 h2 h3) (@lem4792655 A x a h1)). Qed.
Lemma lem4793149 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem4793138 A a0 x a h1 h2 h3) (fun h4 : False => @lem4792651 A x a h3)). Qed.
Lemma lem4793150 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793149 A a0 x a h1 h2 h3) (@lem4792651 A x a h3)). Qed.
Lemma lem4793151 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : (term278 A x a0) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a0 => @lem4793150 A a0 x a h1 h2 h3) (fun h4 : False => @lem4792649 A x a0 h1)). Qed.
Lemma lem4793152 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793151 A a0 x a h1 h2 h3) (@lem4792649 A x a0 h1)). Qed.
Lemma lem4793153 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem4793140 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792645 A x a0 h3)). Qed.
Lemma lem4793154 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793153 A a x a0 h1 h2 h3) (@lem4792645 A x a0 h3)). Qed.
Lemma lem4793155 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : (term278 A x a0) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a0 => @lem4793154 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792643 A x a0 h1)). Qed.
Lemma lem4793156 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793155 A a x a0 h1 h2 h3) (@lem4792643 A x a0 h1)). Qed.
Lemma lem4793157 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4793144 A x a h1 h2) (fun h3 : False => @lem4792619 A x a h2)). Qed.
Lemma lem4793158 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793157 A x a h1 h2) (@lem4792619 A x a h2)). Qed.
Lemma lem4793159 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : (term278 A x a) = False.
Proof. exact (prop_ext (fun h3 : term278 A x a => @lem4793158 A x a h1 h2) (fun h3 : False => @lem4792615 A x a h1)). Qed.
Lemma lem4793160 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793159 A x a h1 h2) (@lem4792615 A x a h1)). Qed.
Lemma lem4793161 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem4793148 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792607 A x a0 h3)). Qed.
Lemma lem4793162 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793161 A a x a0 h1 h2 h3) (@lem4792607 A x a0 h3)). Qed.
Lemma lem4793163 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : (term278 A x a) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a => @lem4793162 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792603 A x a h1)). Qed.
Lemma lem4793164 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793163 A a x a0 h1 h2 h3) (@lem4792603 A x a h1)). Qed.
Lemma lem4793165 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem4793152 A a0 x a h1 h2 h3) (fun h4 : False => @lem4792595 A x a h3)). Qed.
Lemma lem4793166 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793165 A a0 x a h1 h2 h3) (@lem4792595 A x a h3)). Qed.
Lemma lem4793167 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : (term278 A x a0) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a0 => @lem4793166 A a0 x a h1 h2 h3) (fun h4 : False => @lem4792591 A x a0 h1)). Qed.
Lemma lem4793168 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793167 A a0 x a h1 h2 h3) (@lem4792591 A x a0 h1)). Qed.
Lemma lem4793169 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem4793156 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792583 A x a0 h3)). Qed.
Lemma lem4793170 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793169 A a x a0 h1 h2 h3) (@lem4792583 A x a0 h3)). Qed.
Lemma lem4793171 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : (term278 A x a0) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a0 => @lem4793170 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792579 A x a0 h1)). Qed.
Lemma lem4793172 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793171 A a x a0 h1 h2 h3) (@lem4792579 A x a0 h1)). Qed.
Lemma lem4793173 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4793160 A x a h1 h2) (fun h3 : False => @lem4792619 A x a h2)). Qed.
Lemma lem4793174 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793173 A x a h1 h2) (@lem4792619 A x a h2)). Qed.
Lemma lem4793175 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : (term278 A x a) = False.
Proof. exact (prop_ext (fun h3 : term278 A x a => @lem4793174 A x a h1 h2) (fun h3 : False => @lem4792615 A x a h1)). Qed.
Lemma lem4793176 {A : Type'} (x : A) (a : A) (h1 : term278 A x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4793175 A x a h1 h2) (@lem4792615 A x a h1)). Qed.
Lemma lem4793177 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem4793164 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792607 A x a0 h3)). Qed.
Lemma lem4793178 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793177 A a x a0 h1 h2 h3) (@lem4792607 A x a0 h3)). Qed.
Lemma lem4793179 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : (term278 A x a) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a => @lem4793178 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792603 A x a h1)). Qed.
Lemma lem4793180 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793179 A a x a0 h1 h2 h3) (@lem4792603 A x a h1)). Qed.
Lemma lem4793181 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem4793168 A a0 x a h1 h2 h3) (fun h4 : False => @lem4792595 A x a h3)). Qed.
Lemma lem4793182 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793181 A a0 x a h1 h2 h3) (@lem4792595 A x a h3)). Qed.
Lemma lem4793183 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : (term278 A x a0) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a0 => @lem4793182 A a0 x a h1 h2 h3) (fun h4 : False => @lem4792591 A x a0 h1)). Qed.
Lemma lem4793184 {A : Type'} (a0 : A) (x : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4793183 A a0 x a h1 h2 h3) (@lem4792591 A x a0 h1)). Qed.
Lemma lem4793185 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem4793172 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792583 A x a0 h3)). Qed.
Lemma lem4793186 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793185 A a x a0 h1 h2 h3) (@lem4792583 A x a0 h3)). Qed.
Lemma lem4793187 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : (term278 A x a0) = False.
Proof. exact (prop_ext (fun h4 : term278 A x a0 => @lem4793186 A a x a0 h1 h2 h3) (fun h4 : False => @lem4792579 A x a0 h1)). Qed.
Lemma lem4793188 {A : Type'} (a : A) (x : A) (a0 : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem4793187 A a x a0 h1 h2 h3) (@lem4792579 A x a0 h1)). Qed.
Lemma lem4793189 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term278 A x a) (h2 : term333 A x a0 a) : False.
Proof. exact (or_elim (@lem4792535 A x a0 a h2) (fun h0 : x = a0 => @lem4793180 A a x a0 h1 h2 h0) (fun h0 : x = a => @lem4793176 A x a h1 h0)). Qed.
Lemma lem4793190 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term278 A x a0) (h2 : term333 A x a0 a) : False.
Proof. exact (or_elim (@lem4792535 A x a0 a h2) (fun h0 : x = a0 => @lem4793188 A a x a0 h1 h2 h0) (fun h0 : x = a => @lem4793184 A a0 x a h1 h2 h0)). Qed.
Lemma lem4793191 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term333 A x a0 a) : False.
Proof. exact (or_elim (@lem4792534 A x a0 a h1) (fun h0 : term278 A x a0 => @lem4793190 A x a0 a h0 h1) (fun h0 : term278 A x a => @lem4793189 A x a0 a h0 h1)). Qed.
Lemma lem4793192 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term348 A x a0 a) : False.
Proof. exact (or_elim (@lem4792525 A x a0 a h1) (fun h0 : term317 A a0 a => @lem4793024 A a0 a h0) (fun h0 : term333 A x a0 a => @lem4793191 A x a0 a h0)). Qed.
Lemma lem4793193 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term348 A x a0 a) : (term348 A x a0 a) = False.
Proof. exact (prop_ext (fun h2 : term348 A x a0 a => @lem4793192 A x a0 a h1) (fun h2 : False => @lem4792525 A x a0 a h1)). Qed.
Lemma lem4793194 {A : Type'} (x : A) (a0 : A) (a : A) (h1 : term348 A x a0 a) : False.
Proof. exact (EQ_MP (@lem4793193 A x a0 a h1) (@lem4792525 A x a0 a h1)). Qed.
Lemma lem4793195 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : False.
Proof. exact (ex_elim (@lem4792430 A a0 a h1) (fun x : A => fun h0 : term350 A a0 a x => @lem4793194 A x a0 a h0)). Qed.
Lemma lem4793196 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : (term250 A a0 a) = False.
Proof. exact (prop_ext (fun h2 : term250 A a0 a => @lem4793195 A a0 a h1) (fun h2 : False => @lem4792149 A a0 a h1)). Qed.
Lemma lem4793197 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : False.
Proof. exact (EQ_MP (@lem4793196 A a0 a h1) (@lem4792149 A a0 a h1)). Qed.
Lemma lem4793198 {A : Type'} (a0 : A) (a : A) : term249 A a0 a.
Proof. exact (fun h0 : term250 A a0 a => @lem4793197 A a0 a h0). Qed.
Lemma lem4793199 {A : Type'} (a0 : A) (a : A) : (term246 A a0 a) = (a0 = a).
Proof. exact (EQ_MP (@lem4792148 A a0 a) (@lem4793198 A a0 a)). Qed.
Lemma lem4793204 {A : Type'} (a : A) : term259 A a.
Proof. exact (fun a0 : A => @lem4793199 A a0 a). Qed.
Lemma lem4793209 {A : Type'} : term263 A.
Proof. exact (fun a : A => @lem4793204 A a). Qed.
Lemma lem4793210 {A : Type'} : term262 A.
Proof. exact (EQ_MP (@lem4792144 A) (@lem4793209 A)). Qed.
Lemma lem4793211 {A : Type'} (a : A) : term383 A a.
Proof. exact (@lem4793210 A a). Qed.
Lemma lem4793212 {A : Type'} (a : A) : (term383 A a) = (term258 A a).
Proof. exact (eq_refl (term383 A a)). Qed.
Lemma lem4793213 {A : Type'} (a : A) : term258 A a.
Proof. exact (EQ_MP (@lem4793212 A a) (@lem4793211 A a)). Qed.
Lemma lem4793214 {A : Type'} (a : A) (a0 : A) : term384 A a a0.
Proof. exact (@lem4793213 A a a0). Qed.
Lemma lem4793215 {A : Type'} (a0 : A) (a : A) : (term384 A a a0) = (term249 A a0 a).
Proof. exact (eq_refl (term384 A a a0)). Qed.
Lemma lem4793216 {A : Type'} (a0 : A) (a : A) : term249 A a0 a.
Proof. exact (EQ_MP (@lem4793215 A a0 a) (@lem4793214 A a a0)). Qed.
Lemma lem4793218 {A : Type'} (a0 : A) (a : A) : term249 A a0 a.
Proof. exact (@lem4792067 A a0 a (@lem4793216 A a0 a)). Qed.
Lemma lem4793219 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : False.
Proof. exact (@lem4793218 A a0 a (@lem4792051 A a0 a h1)). Qed.
Lemma lem4793220 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : (term250 A a0 a) = False.
Proof. exact (prop_ext (fun h2 : term250 A a0 a => @lem4793219 A a0 a h1) (fun h2 : False => @lem4792051 A a0 a h1)). Qed.
Lemma lem4793221 {A : Type'} (a0 : A) (a : A) (h1 : term250 A a0 a) : False.
Proof. exact (EQ_MP (@lem4793220 A a0 a h1) (@lem4792051 A a0 a h1)). Qed.
Lemma lem4793222 {A : Type'} (a0 : A) (a : A) : term249 A a0 a.
Proof. exact (fun h0 : term250 A a0 a => @lem4793221 A a0 a h0). Qed.
Lemma lem4793223 {A : Type'} (a0 : A) (a : A) : (term246 A a0 a) = (a0 = a).
Proof. exact (EQ_MP (@lem4792050 A a0 a) (@lem4793222 A a0 a)). Qed.
Lemma lem4793224 {A : Type'} (a0 : A) (a : A) : (term234 A a0 a) = (a0 = a).
Proof. exact (EQ_MP (@lem4792046 A a0 a) (@lem4793223 A a0 a)). Qed.
Lemma lem4793225 {A : Type'} (a0 : A) (a : A) : ((@INSERT A a0 (@EMPTY A)) = (@INSERT A a (@EMPTY A))) = (a0 = a).
Proof. exact (EQ_MP (@lem4791977 A a0 a) (@lem4793224 A a0 a)). Qed.
Lemma lem4793226 {A : Type'} (a0 : A) (a : A) : (term212 A a0 a) = ((@cons A a0 (@nil A)) = (@cons A a (@nil A))).
Proof. exact (EQ_MP (@lem4791868 A a0 a) (@lem4793225 A a0 a)). Qed.
Lemma lem4793227 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : term185 A a0 h t a.
Proof. exact (fun h0 : (term385 A a h t) = ((@cons A h t) = (@cons A a (@nil A))) => @lem4791946 A a0 h t a). Qed.
Lemma lem4793228 {A : Type'} (a0 : A) (a : A) : term178 A a0 a.
Proof. exact (fun h0 : (term386 A a) = ((@nil A) = (@cons A a (@nil A))) => @lem4793226 A a0 a). Qed.
Lemma lem4793229 {A : Type'} (a0 : A) (h : A) (t : list A) (a : A) : term187 A a0 h t a.
Proof. exact (fun h0 : term170 A a0 t a => @lem4793227 A a0 h t a). Qed.
Lemma lem4793234 {A : Type'} (a0 : A) (h : A) (a : A) : term191 A a0 h a.
Proof. exact (fun t : list A => @lem4793229 A a0 h t a). Qed.
Lemma lem4793239 {A : Type'} (a0 : A) (a : A) : term195 A a0 a.
Proof. exact (fun h : A => @lem4793234 A a0 h a). Qed.
Lemma lem4793240 {A : Type'} (a0 : A) (a : A) : term197 A a0 a.
Proof. exact (conj (@lem4793228 A a0 a) (@lem4793239 A a0 a)). Qed.
Lemma lem4793241 {A : Type'} (a0 : A) (a : A) : term172 A a0 a.
Proof. exact (@lem4791783 A a0 a (@lem4793240 A a0 a)). Qed.
Lemma lem4793246 {A : Type'} (a : A) : term174 A a.
Proof. exact (fun a0 : A => @lem4793241 A a0 a). Qed.
Lemma lem4793247 {A : Type'} (a : A) : term119 A a.
Proof. exact (EQ_MP (@lem4791756 A a) (@lem4793246 A a)). Qed.
Lemma lem4793248 {A : Type'} (a : A) : term86 A a.
Proof. exact (EQ_MP (@lem4791020 A a) (@lem4793247 A a)). Qed.
Lemma lem4793249 {A : Type'} (a : A) : term91 A a.
Proof. exact (@lem4790883 A a (@lem4793248 A a)). Qed.
Lemma lem4793250 {A : Type'} (a : A) : (term57 A a) = (@cons A a (@nil A)).
Proof. exact (@lem4790856 A a (@lem4793249 A a)). Qed.
Lemma lem4793251 {A : Type'} (a : A) : (term56 A a) = (@cons A a (@nil A)).
Proof. exact (EQ_MP (@lem4790852 A a) (@lem4793250 A a)). Qed.
Lemma lem4793256 {A : Type'} : term387 A.
Proof. exact (fun a : A => @lem4793251 A a). Qed.
