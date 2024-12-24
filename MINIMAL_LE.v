Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MINIMAL_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LE_MINIMAL_spec.
Require Import LE_SUC_LT_spec.
Require Import NOT_LT_spec.
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
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem276701 (P : nat -> Prop) : term0 P.
Proof. exact (@lem276690 P). Qed.
Lemma lem276702 (P : nat -> Prop) : (term0 P) = (term1 P).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem276703 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem276702 P) (@lem276701 P)). Qed.
Lemma lem276704 (P : nat -> Prop) (n : nat) : term2 P n.
Proof. exact (@lem276703 P n). Qed.
Lemma lem276705 (P : nat -> Prop) (n : nat) : (term2 P n) = (term3 P n).
Proof. exact (eq_refl (term2 P n)). Qed.
Lemma lem276706 (P : nat -> Prop) (n : nat) : term3 P n.
Proof. exact (EQ_MP (@lem276705 P n) (@lem276704 P n)). Qed.
Lemma lem276707 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem276708 (n : nat) (P : nat -> Prop) (h1 : term4 P) : (term5 n P) = (term6 P n).
Proof. exact (@lem276706 P n (@lem276707 P h1)). Qed.
Lemma lem276716 (m : nat) (n : nat) (h1 : (term7 m n) = (Peano.lt m n)) : (term7 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem276717 (m : nat) (n : nat) (h1 : (term7 m n) = (Peano.lt m n)) : (Peano.lt m n) = (term7 m n).
Proof. exact (SYM (@lem276716 m n h1)). Qed.
Lemma lem276718 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term7 m n)) : (Peano.lt m n) = (term7 m n).
Proof. exact (h1). Qed.
Lemma lem276719 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term7 m n)) : (term7 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem276718 m n h1)). Qed.
Lemma lem276720 (m : nat) (n : nat) : ((term7 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (term7 m n)).
Proof. exact (prop_ext (fun h1 : (term7 m n) = (Peano.lt m n) => @lem276717 m n h1) (fun h1 : (Peano.lt m n) = (term7 m n) => @lem276719 m n h1)). Qed.
Lemma lem276721 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem276720 m n)). Qed.
Lemma lem276722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276723 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem276722) (@lem276721 m)). Qed.
Lemma lem276724 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem276723 m)). Qed.
Lemma lem276725 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276726 : term14 = term15.
Proof. exact (MK_COMB (@lem276725) (@lem276724)). Qed.
Lemma lem276727 : term15.
Proof. exact (EQ_MP (@lem276726) (@lem91144)). Qed.
Lemma lem276728 (m : nat) : term16 m.
Proof. exact (@lem276727 m). Qed.
Lemma lem276729 (m : nat) : (term16 m) = (term11 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem276730 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem276729 m) (@lem276728 m)). Qed.
Lemma lem276731 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem276730 m n). Qed.
Lemma lem276732 (m : nat) (n : nat) : (term17 m n) = ((Peano.lt m n) = (term7 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem276736 (n : nat) (m : nat) (h1 : (term18 m n) = (Peano.le n m)) : (term18 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem276737 (n : nat) (m : nat) (h1 : (term18 m n) = (Peano.le n m)) : (Peano.le n m) = (term18 m n).
Proof. exact (SYM (@lem276736 n m h1)). Qed.
Lemma lem276738 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term18 m n)) : (Peano.le n m) = (term18 m n).
Proof. exact (h1). Qed.
Lemma lem276739 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term18 m n)) : (term18 m n) = (Peano.le n m).
Proof. exact (SYM (@lem276738 m n h1)). Qed.
Lemma lem276740 (m : nat) (n : nat) : ((term18 m n) = (Peano.le n m)) = ((Peano.le n m) = (term18 m n)).
Proof. exact (prop_ext (fun h1 : (term18 m n) = (Peano.le n m) => @lem276737 n m h1) (fun h1 : (Peano.le n m) = (term18 m n) => @lem276739 m n h1)). Qed.
Lemma lem276741 (m : nat) : (term19 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem276740 m n)). Qed.
Lemma lem276742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276743 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem276742) (@lem276741 m)). Qed.
Lemma lem276744 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem276743 m)). Qed.
Lemma lem276745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276746 : term25 = term26.
Proof. exact (MK_COMB (@lem276745) (@lem276744)). Qed.
Lemma lem276747 : term26.
Proof. exact (EQ_MP (@lem276746) (@lem98377)). Qed.
Lemma lem276748 (m : nat) : term27 m.
Proof. exact (@lem276747 m). Qed.
Lemma lem276749 (m : nat) : (term27 m) = (term22 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem276750 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem276749 m) (@lem276748 m)). Qed.
Lemma lem276751 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem276750 m n). Qed.
Lemma lem276752 (m : nat) (n : nat) : (term28 m n) = ((Peano.le n m) = (term18 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem276771 (m : nat) (n : nat) : (Peano.le n m) = (term18 m n).
Proof. exact (EQ_MP (@lem276752 m n) (@lem276751 m n)). Qed.
Lemma lem276772 (n : nat) (P : nat -> Prop) : (term29 P n) = (term30 n P).
Proof. exact (@lem276771 n (minimal P)). Qed.
Lemma lem276773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem276774 (n : nat) (P : nat -> Prop) : (term31 P n) = (term32 n P).
Proof. exact (MK_COMB (@lem276773) (@lem276772 n P)). Qed.
Lemma lem276782 (m : nat) (n : nat) : (Peano.le n m) = (term18 m n).
Proof. exact (EQ_MP (@lem276752 m n) (@lem276751 m n)). Qed.
Lemma lem276783 (n : nat) (i : nat) : (Peano.le i n) = (term18 n i).
Proof. exact (@lem276782 n i). Qed.
Lemma lem276784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem276785 (n : nat) (i : nat) : (term33 i n) = (term34 n i).
Proof. exact (MK_COMB (@lem276784) (@lem276783 n i)). Qed.
Lemma lem276786 (P : nat -> Prop) (i : nat) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem276787 (n : nat) (P : nat -> Prop) (i : nat) : (term35 n P i) = (term36 n P i).
Proof. exact (MK_COMB (@lem276785 n i) (@lem276786 P i)). Qed.
Lemma lem276790 (n : nat) (P : nat -> Prop) : (term37 n P) = (term38 n P).
Proof. exact (fun_ext (fun i : nat => @lem276787 n P i)). Qed.
Lemma lem276791 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem276792 (n : nat) (P : nat -> Prop) : (term39 n P) = (term40 n P).
Proof. exact (MK_COMB (@lem276791) (@lem276790 n P)). Qed.
Lemma lem276797 (n : nat) (P : nat -> Prop) : ((term29 P n) = (term39 n P)) = ((term30 n P) = (term40 n P)).
Proof. exact (MK_COMB (@lem276774 n P) (@lem276792 n P)). Qed.
Lemma lem276800 (P : nat -> Prop) : (term41 P) = (term41 P).
Proof. exact (eq_refl (term41 P)). Qed.
Lemma lem276801 (n : nat) (P : nat -> Prop) : (term42 n P) = (term43 n P).
Proof. exact (MK_COMB (@lem276800 P) (@lem276797 n P)). Qed.
Lemma lem276804 (P : nat -> Prop) : (term44 P) = (term45 P).
Proof. exact (fun_ext (fun n : nat => @lem276801 n P)). Qed.
Lemma lem276805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276806 (P : nat -> Prop) : (term46 P) = (term47 P).
Proof. exact (MK_COMB (@lem276805) (@lem276804 P)). Qed.
Lemma lem276811 : term48 = term49.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem276806 P)). Qed.
Lemma lem276812 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem276813 : term50 = term51.
Proof. exact (MK_COMB (@lem276812) (@lem276811)). Qed.
Lemma lem276818 : term51 = term50.
Proof. exact (SYM (@lem276813)). Qed.
Lemma lem276836 (m : nat) (n : nat) : (Peano.lt m n) = (term7 m n).
Proof. exact (EQ_MP (@lem276732 m n) (@lem276731 m n)). Qed.
Lemma lem276837 (n : nat) (P : nat -> Prop) : (term52 n P) = (term53 n P).
Proof. exact (@lem276836 n (minimal P)). Qed.
Lemma lem276838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem276839 (n : nat) (P : nat -> Prop) : (term30 n P) = (term54 n P).
Proof. exact (MK_COMB (@lem276838) (@lem276837 n P)). Qed.
Lemma lem276840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem276841 (n : nat) (P : nat -> Prop) : (term32 n P) = (term55 n P).
Proof. exact (MK_COMB (@lem276840) (@lem276839 n P)). Qed.
Lemma lem276849 (m : nat) (n : nat) : (Peano.lt m n) = (term7 m n).
Proof. exact (EQ_MP (@lem276732 m n) (@lem276731 m n)). Qed.
Lemma lem276850 (n : nat) (i : nat) : (Peano.lt n i) = (term7 n i).
Proof. exact (@lem276849 n i). Qed.
Lemma lem276851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem276852 (n : nat) (i : nat) : (term18 n i) = (term56 n i).
Proof. exact (MK_COMB (@lem276851) (@lem276850 n i)). Qed.
Lemma lem276853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem276854 (n : nat) (i : nat) : (term34 n i) = (term57 n i).
Proof. exact (MK_COMB (@lem276853) (@lem276852 n i)). Qed.
Lemma lem276855 (P : nat -> Prop) (i : nat) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem276856 (n : nat) (P : nat -> Prop) (i : nat) : (term36 n P i) = (term58 n P i).
Proof. exact (MK_COMB (@lem276854 n i) (@lem276855 P i)). Qed.
Lemma lem276859 (n : nat) (P : nat -> Prop) : (term38 n P) = (term59 n P).
Proof. exact (fun_ext (fun i : nat => @lem276856 n P i)). Qed.
Lemma lem276860 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem276861 (n : nat) (P : nat -> Prop) : (term40 n P) = (term60 n P).
Proof. exact (MK_COMB (@lem276860) (@lem276859 n P)). Qed.
Lemma lem276866 (n : nat) (P : nat -> Prop) : ((term30 n P) = (term40 n P)) = ((term54 n P) = (term60 n P)).
Proof. exact (MK_COMB (@lem276841 n P) (@lem276861 n P)). Qed.
Lemma lem276869 (P : nat -> Prop) : (term41 P) = (term41 P).
Proof. exact (eq_refl (term41 P)). Qed.
Lemma lem276870 (n : nat) (P : nat -> Prop) : (term43 n P) = (term61 n P).
Proof. exact (MK_COMB (@lem276869 P) (@lem276866 n P)). Qed.
Lemma lem276873 (P : nat -> Prop) : (term45 P) = (term62 P).
Proof. exact (fun_ext (fun n : nat => @lem276870 n P)). Qed.
Lemma lem276874 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276875 (P : nat -> Prop) : (term47 P) = (term63 P).
Proof. exact (MK_COMB (@lem276874) (@lem276873 P)). Qed.
Lemma lem276880 : term49 = term64.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem276875 P)). Qed.
Lemma lem276881 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem276882 : term51 = term65.
Proof. exact (MK_COMB (@lem276881) (@lem276880)). Qed.
Lemma lem276887 : term65 = term51.
Proof. exact (SYM (@lem276882)). Qed.
Lemma lem276899 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term66 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem276900 (p : Prop) (q : Prop) (p' : Prop) : term67 p q p'.
Proof. exact (fun q' : Prop => @lem276899 p q p' q'). Qed.
Lemma lem276901 (p : Prop) (q : Prop) : term68 p q.
Proof. exact (fun p' : Prop => @lem276900 p q p'). Qed.
Lemma lem276902 (n : nat) (P : nat -> Prop) : term69 n P.
Proof. exact (@lem276901 (term4 P) ((term54 n P) = (term60 n P))). Qed.
Lemma lem276903 (n : nat) (P : nat -> Prop) (p' : Prop) : term70 n P p'.
Proof. exact (@lem276902 n P p'). Qed.
Lemma lem276904 (n : nat) (P : nat -> Prop) (p' : Prop) : (term70 n P p') = (term71 n P p').
Proof. exact (eq_refl (term70 n P p')). Qed.
Lemma lem276905 (n : nat) (P : nat -> Prop) (p' : Prop) : term71 n P p'.
Proof. exact (EQ_MP (@lem276904 n P p') (@lem276903 n P p')). Qed.
Lemma lem276906 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term72 n P p' q'.
Proof. exact (@lem276905 n P p' q'). Qed.
Lemma lem276907 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term72 n P p' q') = (term73 n P p' q').
Proof. exact (eq_refl (term72 n P p' q')). Qed.
Lemma lem276908 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term73 n P p' q'.
Proof. exact (EQ_MP (@lem276907 n P p' q') (@lem276906 n P p' q')). Qed.
Lemma lem276913 (P : nat -> Prop) : (term4 P) = (term4 P).
Proof. exact (eq_refl (term4 P)). Qed.
Lemma lem276914 (n : nat) (P : nat -> Prop) (q' : Prop) : term74 n P q'.
Proof. exact (@lem276908 n P (term4 P) q'). Qed.
Lemma lem276915 (n : nat) (P : nat -> Prop) (q' : Prop) : term75 n P q'.
Proof. exact (@lem276914 n P q' (@lem276913 P)). Qed.
Lemma lem276916 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem276917 (P : nat -> Prop) : (term4 P) = ((term4 P) = True).
Proof. exact (@lem7 (term4 P)). Qed.
Lemma lem276922 (P : nat -> Prop) (n : nat) : term3 P n.
Proof. exact (fun h0 : term4 P => @lem276708 n P h0). Qed.
Lemma lem276923 (P : nat -> Prop) (n : nat) : term76 P n.
Proof. exact (@lem276922 P (S n)). Qed.
Lemma lem276925 (P : nat -> Prop) (h1 : term4 P) : (term4 P) = True.
Proof. exact (EQ_MP (@lem276917 P) (@lem276916 P h1)). Qed.
Lemma lem276926 (P : nat -> Prop) (h1 : term4 P) : True = (term4 P).
Proof. exact (SYM (@lem276925 P h1)). Qed.
Lemma lem276927 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (EQ_MP (@lem276926 P h1) (@lem0)). Qed.
Lemma lem276928 (n : nat) (P : nat -> Prop) (h1 : term4 P) : (term53 n P) = (term77 P n).
Proof. exact (@lem276923 P n (@lem276927 P h1)). Qed.
Lemma lem276956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem276957 (n : nat) (P : nat -> Prop) (h1 : term4 P) : (term54 n P) = (term78 P n).
Proof. exact (MK_COMB (@lem276956) (@lem276928 n P h1)). Qed.
Lemma lem276985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem276986 (n : nat) (P : nat -> Prop) (h1 : term4 P) : (term55 n P) = (term79 P n).
Proof. exact (MK_COMB (@lem276985) (@lem276957 n P h1)). Qed.
Lemma lem277020 (n : nat) (P : nat -> Prop) : (term60 n P) = (term60 n P).
Proof. exact (eq_refl (term60 n P)). Qed.
Lemma lem277021 (n : nat) (P : nat -> Prop) (h1 : term4 P) : ((term54 n P) = (term60 n P)) = ((term78 P n) = (term60 n P)).
Proof. exact (MK_COMB (@lem276986 n P h1) (@lem277020 n P)). Qed.
Lemma lem277057 (n : nat) (P : nat -> Prop) : term80 n P.
Proof. exact (fun h0 : term4 P => @lem277021 n P h0). Qed.
Lemma lem277058 (n : nat) (P : nat -> Prop) : term81 n P.
Proof. exact (@lem276915 n P ((term78 P n) = (term60 n P))). Qed.
Lemma lem277059 (n : nat) (P : nat -> Prop) : (term61 n P) = (term82 n P).
Proof. exact (@lem277058 n P (@lem277057 n P)). Qed.
Lemma lem277161 (P : nat -> Prop) : (term62 P) = (term83 P).
Proof. exact (fun_ext (fun n : nat => @lem277059 n P)). Qed.
Lemma lem277263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem277264 (P : nat -> Prop) : (term63 P) = (term84 P).
Proof. exact (MK_COMB (@lem277263) (@lem277161 P)). Qed.
Lemma lem277370 : term64 = term85.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem277264 P)). Qed.
Lemma lem277476 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem277477 : term65 = term86.
Proof. exact (MK_COMB (@lem277476) (@lem277370)). Qed.
Lemma lem277587 : term86 = term65.
Proof. exact (SYM (@lem277477)). Qed.
Lemma lem277589 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem277590 : term86 = term88.
Proof. exact (@lem277589 term86). Qed.
Lemma lem277591 : term88 = term86.
Proof. exact (SYM (@lem277590)). Qed.
Lemma lem277592 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem277595 (h1 : term88) : term88.
Proof. exact (h1). Qed.
Lemma lem277596 : term90.
Proof. exact (fun h0 : term88 => @lem277595 h0). Qed.
Lemma lem277597 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem277598 (h1 : term88) : term88.
Proof. exact (h1). Qed.
Lemma lem277599 (h1 : term88) (h2 : term90) : term88.
Proof. exact (@lem277597 h2 (@lem277598 h1)). Qed.
Lemma lem277600 (h1 : term88) : term91.
Proof. exact (fun h0 : term90 => @lem277599 h1 h0). Qed.
Lemma lem277601 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem277602 (h1 : term88) (h2 : term90) : term88.
Proof. exact (@lem277600 h1 (@lem277601 h2)). Qed.
Lemma lem277603 (h1 : term90) : term90.
Proof. exact (fun h0 : term88 => @lem277602 h0 h1). Qed.
Lemma lem277604 : term92.
Proof. exact (fun h0 : term90 => @lem277603 h0). Qed.
Lemma lem277607 : term90.
Proof. exact (@lem277604 (@lem277596)). Qed.
Lemma lem277609 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem277610 : term88 = term93.
Proof. exact (@lem277609 term89). Qed.
Lemma lem277612 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem277613 : term93 = term86.
Proof. exact (@lem277612 term86). Qed.
Lemma lem277672 : term88 = term86.
Proof. exact (TRANS (@lem277610) (@lem277613)). Qed.
Lemma lem277679 (n : nat) (P : nat -> Prop) (i : nat) : (term58 n P i) = (term58 n P i).
Proof. exact (eq_refl (term58 n P i)). Qed.
Lemma lem277680 (n : nat) (P : nat -> Prop) : (term59 n P) = (term59 n P).
Proof. exact (fun_ext (fun i : nat => @lem277679 n P i)). Qed.
Lemma lem277681 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem277682 (n : nat) (P : nat -> Prop) : (term60 n P) = (term60 n P).
Proof. exact (MK_COMB (@lem277681) (@lem277680 n P)). Qed.
Lemma lem277687 (P : nat -> Prop) (n : nat) (i : nat) : (term95 P n i) = (term95 P n i).
Proof. exact (eq_refl (term95 P n i)). Qed.
Lemma lem277688 (P : nat -> Prop) (n : nat) : (term96 P n) = (term96 P n).
Proof. exact (fun_ext (fun i : nat => @lem277687 P n i)). Qed.
Lemma lem277689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem277690 (P : nat -> Prop) (n : nat) : (term77 P n) = (term77 P n).
Proof. exact (MK_COMB (@lem277689) (@lem277688 P n)). Qed.
Lemma lem277691 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem277692 (P : nat -> Prop) (n : nat) : (term78 P n) = (term78 P n).
Proof. exact (MK_COMB (@lem277691) (@lem277690 P n)). Qed.
Lemma lem277693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem277694 (P : nat -> Prop) (n : nat) : (term79 P n) = (term79 P n).
Proof. exact (MK_COMB (@lem277693) (@lem277692 P n)). Qed.
Lemma lem277695 (n : nat) (P : nat -> Prop) : ((term78 P n) = (term60 n P)) = ((term78 P n) = (term60 n P)).
Proof. exact (MK_COMB (@lem277694 P n) (@lem277682 n P)). Qed.
Lemma lem277696 (P : nat -> Prop) (r : nat) : (P r) = (P r).
Proof. exact (eq_refl (P r)). Qed.
Lemma lem277697 (P : nat -> Prop) : (term97 P) = (term97 P).
Proof. exact (fun_ext (fun r : nat => @lem277696 P r)). Qed.
Lemma lem277698 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem277699 (P : nat -> Prop) : (term4 P) = (term4 P).
Proof. exact (MK_COMB (@lem277698) (@lem277697 P)). Qed.
Lemma lem277700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem277701 (P : nat -> Prop) : (term41 P) = (term41 P).
Proof. exact (MK_COMB (@lem277700) (@lem277699 P)). Qed.
Lemma lem277702 (n : nat) (P : nat -> Prop) : (term82 n P) = (term82 n P).
Proof. exact (MK_COMB (@lem277701 P) (@lem277695 n P)). Qed.
Lemma lem277703 (P : nat -> Prop) : (term83 P) = (term83 P).
Proof. exact (fun_ext (fun n : nat => @lem277702 n P)). Qed.
Lemma lem277704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem277705 (P : nat -> Prop) : (term84 P) = (term84 P).
Proof. exact (MK_COMB (@lem277704) (@lem277703 P)). Qed.
Lemma lem277706 : term85 = term85.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem277705 P)). Qed.
Lemma lem277707 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem277708 : term86 = term86.
Proof. exact (MK_COMB (@lem277707) (@lem277706)). Qed.
Lemma lem277747 : term88 = term86.
Proof. exact (TRANS (@lem277672) (@lem277708)). Qed.
Lemma lem277748 : term86 = term88.
Proof. exact (SYM (@lem277747)). Qed.
Lemma lem277749 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem277751 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem277752 (n : nat) (P : nat -> Prop) : ((term78 P n) = (term60 n P)) = (term98 n P).
Proof. exact (@lem277751 ((term78 P n) = (term60 n P))). Qed.
Lemma lem277753 (n : nat) (P : nat -> Prop) : (term98 n P) = ((term78 P n) = (term60 n P)).
Proof. exact (SYM (@lem277752 n P)). Qed.
Lemma lem277754 (n : nat) (P : nat -> Prop) (h1 : term99 n P) : term99 n P.
Proof. exact (h1). Qed.
Lemma lem277755 (P : nat -> Prop) (r : nat) : (P r) = (P r).
Proof. exact (eq_refl (P r)). Qed.
Lemma lem277756 (P : nat -> Prop) : (term97 P) = (term97 P).
Proof. exact (fun_ext (fun r : nat => @lem277755 P r)). Qed.
Lemma lem277757 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem277766 (P : nat -> Prop) : (term4 P) = (term4 P).
Proof. exact (MK_COMB (@lem277757) (@lem277756 P)). Qed.
Lemma lem277767 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (EQ_MP (@lem277766 P) (@lem277749 P h1)). Qed.
Lemma lem277776 (P : nat -> Prop) (n : nat) (i : nat) : (term100 P n i) = (term101 P n i).
Proof. exact (@lem17362 (P i) (term7 n i)). Qed.
Lemma lem277781 (P : nat -> Prop) (n : nat) (i : nat) : (term95 P n i) = (term102 P n i).
Proof. exact (@lem17265 (P i) (term7 n i)). Qed.
Lemma lem277782 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem277783 (P : nat -> Prop) (n : nat) : (term78 P n) = (term105 P n).
Proof. exact (@lem277782 (term96 P n)). Qed.
Lemma lem277784 (P : nat -> Prop) (n : nat) (i : nat) : (term106 P n i) = (term95 P n i).
Proof. exact (eq_refl (term106 P n i)). Qed.
Lemma lem277785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem277786 (P : nat -> Prop) (n : nat) (i : nat) : (term107 P n i) = (term100 P n i).
Proof. exact (MK_COMB (@lem277785) (@lem277784 P n i)). Qed.
Lemma lem277787 (P : nat -> Prop) (n : nat) (i : nat) : (term107 P n i) = (term101 P n i).
Proof. exact (TRANS (@lem277786 P n i) (@lem277776 P n i)). Qed.
Lemma lem277788 (P : nat -> Prop) (n : nat) : (term108 P n) = (term109 P n).
Proof. exact (fun_ext (fun i : nat => @lem277787 P n i)). Qed.
Lemma lem277789 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem277790 (P : nat -> Prop) (n : nat) : (term105 P n) = (term110 P n).
Proof. exact (MK_COMB (@lem277789) (@lem277788 P n)). Qed.
Lemma lem277791 (P : nat -> Prop) (n : nat) : (term78 P n) = (term110 P n).
Proof. exact (TRANS (@lem277783 P n) (@lem277790 P n)). Qed.
Lemma lem277792 (P : nat -> Prop) (n : nat) : (term96 P n) = (term111 P n).
Proof. exact (fun_ext (fun i : nat => @lem277781 P n i)). Qed.
Lemma lem277793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem277794 (P : nat -> Prop) (n : nat) : (term77 P n) = (term112 P n).
Proof. exact (MK_COMB (@lem277793) (@lem277792 P n)). Qed.
Lemma lem277795 (P : nat -> Prop) (n : nat) : (term113 P n) = (term77 P n).
Proof. exact (@lem16933 (term77 P n)). Qed.
Lemma lem277796 (P : nat -> Prop) (n : nat) : (term113 P n) = (term112 P n).
Proof. exact (TRANS (@lem277795 P n) (@lem277794 P n)). Qed.
Lemma lem277800 (n : nat) (i : nat) : (term114 n i) = (term7 n i).
Proof. exact (@lem16933 (term7 n i)). Qed.
Lemma lem277801 (P : nat -> Prop) (i : nat) : (term115 P i) = (term115 P i).
Proof. exact (eq_refl (term115 P i)). Qed.
Lemma lem277803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem277804 (n : nat) (i : nat) : (term116 n i) = (term117 n i).
Proof. exact (MK_COMB (@lem277803) (@lem277800 n i)). Qed.
Lemma lem277805 (n : nat) (P : nat -> Prop) (i : nat) : (term118 n P i) = (term119 n P i).
Proof. exact (MK_COMB (@lem277804 n i) (@lem277801 P i)). Qed.
Lemma lem277806 (n : nat) (P : nat -> Prop) (i : nat) : (term120 n P i) = (term118 n P i).
Proof. exact (@lem17045 (term56 n i) (P i)). Qed.
Lemma lem277807 (n : nat) (P : nat -> Prop) (i : nat) : (term120 n P i) = (term119 n P i).
Proof. exact (TRANS (@lem277806 n P i) (@lem277805 n P i)). Qed.
Lemma lem277810 (n : nat) (P : nat -> Prop) (i : nat) : (term58 n P i) = (term58 n P i).
Proof. exact (eq_refl (term58 n P i)). Qed.
Lemma lem277811 (P : nat -> Prop) : (term121 P) = (term122 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem277812 (n : nat) (P : nat -> Prop) : (term123 n P) = (term124 n P).
Proof. exact (@lem277811 (term59 n P)). Qed.
Lemma lem277813 (n : nat) (P : nat -> Prop) (i : nat) : (term125 n P i) = (term58 n P i).
Proof. exact (eq_refl (term125 n P i)). Qed.
Lemma lem277814 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem277815 (n : nat) (P : nat -> Prop) (i : nat) : (term126 n P i) = (term120 n P i).
Proof. exact (MK_COMB (@lem277814) (@lem277813 n P i)). Qed.
Lemma lem277816 (n : nat) (P : nat -> Prop) (i : nat) : (term126 n P i) = (term119 n P i).
Proof. exact (TRANS (@lem277815 n P i) (@lem277807 n P i)). Qed.
Lemma lem277817 (n : nat) (P : nat -> Prop) : (term127 n P) = (term128 n P).
Proof. exact (fun_ext (fun i : nat => @lem277816 n P i)). Qed.
Lemma lem277818 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem277819 (n : nat) (P : nat -> Prop) : (term124 n P) = (term129 n P).
Proof. exact (MK_COMB (@lem277818) (@lem277817 n P)). Qed.
Lemma lem277820 (n : nat) (P : nat -> Prop) : (term123 n P) = (term129 n P).
Proof. exact (TRANS (@lem277812 n P) (@lem277819 n P)). Qed.
Lemma lem277821 (n : nat) (P : nat -> Prop) : (term59 n P) = (term59 n P).
Proof. exact (fun_ext (fun i : nat => @lem277810 n P i)). Qed.
Lemma lem277822 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem277823 (n : nat) (P : nat -> Prop) : (term60 n P) = (term60 n P).
Proof. exact (MK_COMB (@lem277822) (@lem277821 n P)). Qed.
Lemma lem277824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem277825 (P : nat -> Prop) (n : nat) : (term130 P n) = (term131 P n).
Proof. exact (MK_COMB (@lem277824) (@lem277796 P n)). Qed.
Lemma lem277826 (n : nat) (P : nat -> Prop) : (term132 n P) = (term133 n P).
Proof. exact (MK_COMB (@lem277825 P n) (@lem277823 n P)). Qed.
Lemma lem277827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem277828 (P : nat -> Prop) (n : nat) : (term134 P n) = (term135 P n).
Proof. exact (MK_COMB (@lem277827) (@lem277791 P n)). Qed.
Lemma lem277829 (n : nat) (P : nat -> Prop) : (term136 n P) = (term137 n P).
Proof. exact (MK_COMB (@lem277828 P n) (@lem277820 n P)). Qed.
Lemma lem277830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem277831 (n : nat) (P : nat -> Prop) : (term138 n P) = (term139 n P).
Proof. exact (MK_COMB (@lem277830) (@lem277829 n P)). Qed.
Lemma lem277832 (n : nat) (P : nat -> Prop) : (term140 n P) = (term141 n P).
Proof. exact (MK_COMB (@lem277831 n P) (@lem277826 n P)). Qed.
Lemma lem277833 (n : nat) (P : nat -> Prop) : (term99 n P) = (term140 n P).
Proof. exact (@lem17646 (term78 P n) (term60 n P)). Qed.
Lemma lem277834 (n : nat) (P : nat -> Prop) : (term99 n P) = (term141 n P).
Proof. exact (TRANS (@lem277833 n P) (@lem277832 n P)). Qed.
Lemma lem277993 {A : Type'} (P : A -> Prop) (Q : Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem277994 (P : nat -> Prop) (Q : Prop) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem277993 nat P Q). Qed.
Lemma lem277995 (n : nat) (P : nat -> Prop) : (term146 n P) = (term147 n P).
Proof. exact (@lem277994 (term109 P n) (term129 n P)). Qed.
Lemma lem277996 (P : nat -> Prop) (n : nat) (i : nat) : (term148 P n i) = (term101 P n i).
Proof. exact (eq_refl (term148 P n i)). Qed.
Lemma lem277997 (P : nat -> Prop) (n : nat) : (term149 P n) = (term109 P n).
Proof. exact (fun_ext (fun i : nat => @lem277996 P n i)). Qed.
Lemma lem277998 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem277999 (P : nat -> Prop) (n : nat) : (term150 P n) = (term110 P n).
Proof. exact (MK_COMB (@lem277998) (@lem277997 P n)). Qed.
Lemma lem278000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278001 (P : nat -> Prop) (n : nat) : (term151 P n) = (term135 P n).
Proof. exact (MK_COMB (@lem278000) (@lem277999 P n)). Qed.
Lemma lem278002 (n : nat) (P : nat -> Prop) : (term129 n P) = (term129 n P).
Proof. exact (eq_refl (term129 n P)). Qed.
Lemma lem278003 (n : nat) (P : nat -> Prop) : (term146 n P) = (term137 n P).
Proof. exact (MK_COMB (@lem278001 P n) (@lem278002 n P)). Qed.
Lemma lem278004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278005 (n : nat) (P : nat -> Prop) : (term152 n P) = (term153 n P).
Proof. exact (MK_COMB (@lem278004) (@lem278003 n P)). Qed.
Lemma lem278006 (P : nat -> Prop) (n : nat) (i : nat) : (term148 P n i) = (term101 P n i).
Proof. exact (eq_refl (term148 P n i)). Qed.
Lemma lem278007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278008 (P : nat -> Prop) (n : nat) (i : nat) : (term154 P n i) = (term155 P n i).
Proof. exact (MK_COMB (@lem278007) (@lem278006 P n i)). Qed.
Lemma lem278009 (n : nat) (P : nat -> Prop) : (term129 n P) = (term129 n P).
Proof. exact (eq_refl (term129 n P)). Qed.
Lemma lem278010 (i : nat) (n : nat) (P : nat -> Prop) : (term156 i n P) = (term157 i n P).
Proof. exact (MK_COMB (@lem278008 P n i) (@lem278009 n P)). Qed.
Lemma lem278011 (n : nat) (P : nat -> Prop) : (term158 n P) = (term159 n P).
Proof. exact (fun_ext (fun i : nat => @lem278010 i n P)). Qed.
Lemma lem278012 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278013 (n : nat) (P : nat -> Prop) : (term147 n P) = (term160 n P).
Proof. exact (MK_COMB (@lem278012) (@lem278011 n P)). Qed.
Lemma lem278014 (n : nat) (P : nat -> Prop) : ((term146 n P) = (term147 n P)) = ((term137 n P) = (term160 n P)).
Proof. exact (MK_COMB (@lem278005 n P) (@lem278013 n P)). Qed.
Lemma lem278015 (n : nat) (P : nat -> Prop) : (term137 n P) = (term160 n P).
Proof. exact (EQ_MP (@lem278014 n P) (@lem277995 n P)). Qed.
Lemma lem278016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem278017 (n : nat) (P : nat -> Prop) : (term139 n P) = (term161 n P).
Proof. exact (MK_COMB (@lem278016) (@lem278015 n P)). Qed.
Lemma lem278019 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem278020 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem278019 nat P Q). Qed.
Lemma lem278021 (n : nat) (P : nat -> Prop) : (term166 n P) = (term167 n P).
Proof. exact (@lem278020 (term112 P n) (term59 n P)). Qed.
Lemma lem278022 (n : nat) (P : nat -> Prop) (i : nat) : (term125 n P i) = (term58 n P i).
Proof. exact (eq_refl (term125 n P i)). Qed.
Lemma lem278023 (n : nat) (P : nat -> Prop) : (term168 n P) = (term59 n P).
Proof. exact (fun_ext (fun i : nat => @lem278022 n P i)). Qed.
Lemma lem278024 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278025 (n : nat) (P : nat -> Prop) : (term169 n P) = (term60 n P).
Proof. exact (MK_COMB (@lem278024) (@lem278023 n P)). Qed.
Lemma lem278026 (P : nat -> Prop) (n : nat) : (term131 P n) = (term131 P n).
Proof. exact (eq_refl (term131 P n)). Qed.
Lemma lem278027 (n : nat) (P : nat -> Prop) : (term166 n P) = (term133 n P).
Proof. exact (MK_COMB (@lem278026 P n) (@lem278025 n P)). Qed.
Lemma lem278028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278029 (n : nat) (P : nat -> Prop) : (term170 n P) = (term171 n P).
Proof. exact (MK_COMB (@lem278028) (@lem278027 n P)). Qed.
Lemma lem278030 (n : nat) (P : nat -> Prop) (i : nat) : (term125 n P i) = (term58 n P i).
Proof. exact (eq_refl (term125 n P i)). Qed.
Lemma lem278031 (P : nat -> Prop) (n : nat) : (term131 P n) = (term131 P n).
Proof. exact (eq_refl (term131 P n)). Qed.
Lemma lem278032 (n : nat) (P : nat -> Prop) (i : nat) : (term172 n P i) = (term173 n P i).
Proof. exact (MK_COMB (@lem278031 P n) (@lem278030 n P i)). Qed.
Lemma lem278033 (n : nat) (P : nat -> Prop) : (term174 n P) = (term175 n P).
Proof. exact (fun_ext (fun i : nat => @lem278032 n P i)). Qed.
Lemma lem278034 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278035 (n : nat) (P : nat -> Prop) : (term167 n P) = (term176 n P).
Proof. exact (MK_COMB (@lem278034) (@lem278033 n P)). Qed.
Lemma lem278036 (n : nat) (P : nat -> Prop) : ((term166 n P) = (term167 n P)) = ((term133 n P) = (term176 n P)).
Proof. exact (MK_COMB (@lem278029 n P) (@lem278035 n P)). Qed.
Lemma lem278037 (n : nat) (P : nat -> Prop) : (term133 n P) = (term176 n P).
Proof. exact (EQ_MP (@lem278036 n P) (@lem278021 n P)). Qed.
Lemma lem278038 (n : nat) (P : nat -> Prop) : (term141 n P) = (term177 n P).
Proof. exact (MK_COMB (@lem278017 n P) (@lem278037 n P)). Qed.
Lemma lem278040 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem278041 (P : nat -> Prop) (Q : nat -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem278040 nat P Q). Qed.
Lemma lem278042 (n : nat) (P : nat -> Prop) : (term182 n P) = (term183 n P).
Proof. exact (@lem278041 (term159 n P) (term175 n P)). Qed.
Lemma lem278043 (i : nat) (n : nat) (P : nat -> Prop) : (term184 n P i) = (term157 i n P).
Proof. exact (eq_refl (term184 n P i)). Qed.
Lemma lem278044 (n : nat) (P : nat -> Prop) : (term185 n P) = (term159 n P).
Proof. exact (fun_ext (fun i : nat => @lem278043 i n P)). Qed.
Lemma lem278045 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278046 (n : nat) (P : nat -> Prop) : (term186 n P) = (term160 n P).
Proof. exact (MK_COMB (@lem278045) (@lem278044 n P)). Qed.
Lemma lem278047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem278048 (n : nat) (P : nat -> Prop) : (term187 n P) = (term161 n P).
Proof. exact (MK_COMB (@lem278047) (@lem278046 n P)). Qed.
Lemma lem278049 (n : nat) (P : nat -> Prop) (i : nat) : (term188 n P i) = (term173 n P i).
Proof. exact (eq_refl (term188 n P i)). Qed.
Lemma lem278050 (n : nat) (P : nat -> Prop) : (term189 n P) = (term175 n P).
Proof. exact (fun_ext (fun i : nat => @lem278049 n P i)). Qed.
Lemma lem278051 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278052 (n : nat) (P : nat -> Prop) : (term190 n P) = (term176 n P).
Proof. exact (MK_COMB (@lem278051) (@lem278050 n P)). Qed.
Lemma lem278053 (n : nat) (P : nat -> Prop) : (term182 n P) = (term177 n P).
Proof. exact (MK_COMB (@lem278048 n P) (@lem278052 n P)). Qed.
Lemma lem278054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278055 (n : nat) (P : nat -> Prop) : (term191 n P) = (term192 n P).
Proof. exact (MK_COMB (@lem278054) (@lem278053 n P)). Qed.
Lemma lem278056 (i : nat) (n : nat) (P : nat -> Prop) : (term184 n P i) = (term157 i n P).
Proof. exact (eq_refl (term184 n P i)). Qed.
Lemma lem278057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem278058 (i : nat) (n : nat) (P : nat -> Prop) : (term193 n P i) = (term194 i n P).
Proof. exact (MK_COMB (@lem278057) (@lem278056 i n P)). Qed.
Lemma lem278059 (n : nat) (P : nat -> Prop) (i : nat) : (term188 n P i) = (term173 n P i).
Proof. exact (eq_refl (term188 n P i)). Qed.
Lemma lem278060 (n : nat) (P : nat -> Prop) (i : nat) : (term195 n P i) = (term196 n P i).
Proof. exact (MK_COMB (@lem278058 i n P) (@lem278059 n P i)). Qed.
Lemma lem278061 (n : nat) (P : nat -> Prop) : (term197 n P) = (term198 n P).
Proof. exact (fun_ext (fun i : nat => @lem278060 n P i)). Qed.
Lemma lem278062 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278063 (n : nat) (P : nat -> Prop) : (term183 n P) = (term199 n P).
Proof. exact (MK_COMB (@lem278062) (@lem278061 n P)). Qed.
Lemma lem278064 (n : nat) (P : nat -> Prop) : ((term182 n P) = (term183 n P)) = ((term177 n P) = (term199 n P)).
Proof. exact (MK_COMB (@lem278055 n P) (@lem278063 n P)). Qed.
Lemma lem278065 (n : nat) (P : nat -> Prop) : (term177 n P) = (term199 n P).
Proof. exact (EQ_MP (@lem278064 n P) (@lem278042 n P)). Qed.
Lemma lem278067 (n : nat) (P : nat -> Prop) : (term141 n P) = (term199 n P).
Proof. exact (TRANS (@lem278038 n P) (@lem278065 n P)). Qed.
Lemma lem278068 (n : nat) (P : nat -> Prop) : (term99 n P) = (term199 n P).
Proof. exact (TRANS (@lem277834 n P) (@lem278067 n P)). Qed.
Lemma lem278069 (n : nat) (P : nat -> Prop) (h1 : term99 n P) : term199 n P.
Proof. exact (EQ_MP (@lem278068 n P) (@lem277754 n P h1)). Qed.
Lemma lem278070 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term196 n P i) : term196 n P i.
Proof. exact (h1). Qed.
Lemma lem278086 (n : nat) (P : nat -> Prop) (i : nat) : (term58 n P i) = (term58 n P i).
Proof. exact (eq_refl (term58 n P i)). Qed.
Lemma lem278101 (P : nat -> Prop) (n : nat) (i : nat) : (term102 P n i) = (term102 P n i).
Proof. exact (eq_refl (term102 P n i)). Qed.
Lemma lem278102 (P : nat -> Prop) (n : nat) : (term111 P n) = (term111 P n).
Proof. exact (fun_ext (fun i : nat => @lem278101 P n i)). Qed.
Lemma lem278103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278104 (P : nat -> Prop) (n : nat) : (term112 P n) = (term112 P n).
Proof. exact (MK_COMB (@lem278103) (@lem278102 P n)). Qed.
Lemma lem278105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278106 (P : nat -> Prop) (n : nat) : (term131 P n) = (term131 P n).
Proof. exact (MK_COMB (@lem278105) (@lem278104 P n)). Qed.
Lemma lem278107 (n : nat) (P : nat -> Prop) (i : nat) : (term173 n P i) = (term173 n P i).
Proof. exact (MK_COMB (@lem278106 P n) (@lem278086 n P i)). Qed.
Lemma lem278122 (n : nat) (P : nat -> Prop) (i : nat) : (term119 n P i) = (term119 n P i).
Proof. exact (eq_refl (term119 n P i)). Qed.
Lemma lem278123 (n : nat) (P : nat -> Prop) : (term128 n P) = (term128 n P).
Proof. exact (fun_ext (fun i : nat => @lem278122 n P i)). Qed.
Lemma lem278124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278125 (n : nat) (P : nat -> Prop) : (term129 n P) = (term129 n P).
Proof. exact (MK_COMB (@lem278124) (@lem278123 n P)). Qed.
Lemma lem278142 (P : nat -> Prop) (n : nat) (i : nat) : (term155 P n i) = (term155 P n i).
Proof. exact (eq_refl (term155 P n i)). Qed.
Lemma lem278143 (i : nat) (n : nat) (P : nat -> Prop) : (term157 i n P) = (term157 i n P).
Proof. exact (MK_COMB (@lem278142 P n i) (@lem278125 n P)). Qed.
Lemma lem278144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem278145 (i : nat) (n : nat) (P : nat -> Prop) : (term194 i n P) = (term194 i n P).
Proof. exact (MK_COMB (@lem278144) (@lem278143 i n P)). Qed.
Lemma lem278146 (n : nat) (P : nat -> Prop) (i : nat) : (term196 n P i) = (term196 n P i).
Proof. exact (MK_COMB (@lem278145 i n P) (@lem278107 n P i)). Qed.
Lemma lem278147 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term196 n P i) : term196 n P i.
Proof. exact (EQ_MP (@lem278146 n P i) (@lem278070 n P i h1)). Qed.
Lemma lem278152 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term157 i n P.
Proof. exact (h1). Qed.
Lemma lem278153 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term173 n P i.
Proof. exact (h1). Qed.
Lemma lem278154 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term129 n P.
Proof. exact (proj2 (@lem278152 i n P h1)). Qed.
Lemma lem278155 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term101 P n i.
Proof. exact (proj1 (@lem278152 i n P h1)). Qed.
Lemma lem278158 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term58 n P i.
Proof. exact (proj2 (@lem278153 n P i h1)). Qed.
Lemma lem278159 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term112 P n.
Proof. exact (proj1 (@lem278153 n P i h1)). Qed.
Lemma lem278173 (n : nat) (P : nat -> Prop) (i : nat) : (term119 n P i) = (term119 n P i).
Proof. exact (eq_refl (term119 n P i)). Qed.
Lemma lem278174 (n : nat) (P : nat -> Prop) : (term128 n P) = (term128 n P).
Proof. exact (fun_ext (fun i : nat => @lem278173 n P i)). Qed.
Lemma lem278175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278177 (n : nat) (P : nat -> Prop) : (term129 n P) = (term129 n P).
Proof. exact (MK_COMB (@lem278175) (@lem278174 n P)). Qed.
Lemma lem278178 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term129 n P.
Proof. exact (EQ_MP (@lem278177 n P) (@lem278154 i n P h1)). Qed.
Lemma lem278198 (P : nat -> Prop) (n : nat) (i : nat) : (term102 P n i) = (term102 P n i).
Proof. exact (eq_refl (term102 P n i)). Qed.
Lemma lem278199 (P : nat -> Prop) (n : nat) : (term111 P n) = (term111 P n).
Proof. exact (fun_ext (fun i : nat => @lem278198 P n i)). Qed.
Lemma lem278200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278202 (P : nat -> Prop) (n : nat) : (term112 P n) = (term112 P n).
Proof. exact (MK_COMB (@lem278200) (@lem278199 P n)). Qed.
Lemma lem278203 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term112 P n.
Proof. exact (EQ_MP (@lem278202 P n) (@lem278159 n P i h1)). Qed.
Lemma lem278212 (_6445 : nat) (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term200 n P _6445.
Proof. exact (@lem278178 i n P h1 _6445). Qed.
Lemma lem278213 (n : nat) (P : nat -> Prop) (_6445 : nat) : (term200 n P _6445) = (term119 n P _6445).
Proof. exact (eq_refl (term200 n P _6445)). Qed.
Lemma lem278215 (_6446 : nat) (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term201 P n _6446.
Proof. exact (@lem278203 n P i h1 _6446). Qed.
Lemma lem278216 (P : nat -> Prop) (n : nat) (_6446 : nat) : (term201 P n _6446) = (term102 P n _6446).
Proof. exact (eq_refl (term201 P n _6446)). Qed.
Lemma lem278225 (_6445 : nat) (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term119 n P _6445.
Proof. exact (EQ_MP (@lem278213 n P _6445) (@lem278212 _6445 i n P h1)). Qed.
Lemma lem278229 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term56 n i.
Proof. exact (proj2 (@lem278155 i n P h1)). Qed.
Lemma lem278237 (_6446 : nat) (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term102 P n _6446.
Proof. exact (EQ_MP (@lem278216 P n _6446) (@lem278215 _6446 n P i h1)). Qed.
Lemma lem278239 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term56 n i.
Proof. exact (proj1 (@lem278158 n P i h1)). Qed.
Lemma lem278243 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : P i.
Proof. exact (proj1 (@lem278155 i n P h1)). Qed.
Lemma lem278244 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term202 P i.
Proof. exact (fun h0 : term115 P i => @lem278243 i n P h1). Qed.
Lemma lem278246 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem278247 (P : nat -> Prop) (i : nat) : (term202 P i) = (P i).
Proof. exact (@lem278246 (P i)). Qed.
Lemma lem278248 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : P i.
Proof. exact (EQ_MP (@lem278247 P i) (@lem278244 i n P h1)). Qed.
Lemma lem278250 (b : Prop) (a : Prop) : (a \/ b) = (term204 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem278251 (P : nat -> Prop) (n : nat) (_6445 : nat) : (term119 n P _6445) = (term205 P n _6445).
Proof. exact (@lem278250 (term115 P _6445) (term7 n _6445)). Qed.
Lemma lem278253 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem278254 (P : nat -> Prop) (_6445 : nat) : (term206 P _6445) = (P _6445).
Proof. exact (@lem278253 (P _6445)). Qed.
Lemma lem278255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem278256 (P : nat -> Prop) (_6445 : nat) : (term207 P _6445) = (term208 P _6445).
Proof. exact (MK_COMB (@lem278255) (@lem278254 P _6445)). Qed.
Lemma lem278257 (n : nat) (_6445 : nat) : (term7 n _6445) = (term7 n _6445).
Proof. exact (eq_refl (term7 n _6445)). Qed.
Lemma lem278258 (P : nat -> Prop) (n : nat) (_6445 : nat) : (term205 P n _6445) = (term95 P n _6445).
Proof. exact (MK_COMB (@lem278256 P _6445) (@lem278257 n _6445)). Qed.
Lemma lem278259 (P : nat -> Prop) (n : nat) (_6445 : nat) : (term119 n P _6445) = (term95 P n _6445).
Proof. exact (TRANS (@lem278251 P n _6445) (@lem278258 P n _6445)). Qed.
Lemma lem278262 (_6445 : nat) (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term95 P n _6445.
Proof. exact (EQ_MP (@lem278259 P n _6445) (@lem278225 _6445 i n P h1)). Qed.
Lemma lem278263 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term95 P n i.
Proof. exact (@lem278262 i i n P h1). Qed.
Lemma lem278266 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term7 n i.
Proof. exact (@lem278263 i n P h1 (@lem278248 i n P h1)). Qed.
Lemma lem278267 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term209 n i.
Proof. exact (fun h0 : term56 n i => @lem278266 i n P h1). Qed.
Lemma lem278269 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem278270 (n : nat) (i : nat) : (term209 n i) = (term7 n i).
Proof. exact (@lem278269 (term7 n i)). Qed.
Lemma lem278271 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term7 n i.
Proof. exact (EQ_MP (@lem278270 n i) (@lem278267 i n P h1)). Qed.
Lemma lem278274 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem278276 (n : nat) (i : nat) : (term56 n i) = (term210 n i).
Proof. exact (@lem278274 (term7 n i)). Qed.
Lemma lem278279 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term210 n i.
Proof. exact (EQ_MP (@lem278276 n i) (@lem278229 i n P h1)). Qed.
Lemma lem278282 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : False.
Proof. exact (@lem278279 i n P h1 (@lem278271 i n P h1)). Qed.
Lemma lem278283 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : term211.
Proof. exact (fun h0 : ~ False => @lem278282 i n P h1). Qed.
Lemma lem278285 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem278286 : term211 = False.
Proof. exact (@lem278285 False). Qed.
Lemma lem278287 (i : nat) (n : nat) (P : nat -> Prop) (h1 : term157 i n P) : False.
Proof. exact (EQ_MP (@lem278286) (@lem278283 i n P h1)). Qed.
Lemma lem278289 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : P i.
Proof. exact (proj2 (@lem278158 n P i h1)). Qed.
Lemma lem278290 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term202 P i.
Proof. exact (fun h0 : term115 P i => @lem278289 n P i h1). Qed.
Lemma lem278292 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem278293 (P : nat -> Prop) (i : nat) : (term202 P i) = (P i).
Proof. exact (@lem278292 (P i)). Qed.
Lemma lem278294 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : P i.
Proof. exact (EQ_MP (@lem278293 P i) (@lem278290 n P i h1)). Qed.
Lemma lem278300 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem278301 (n : nat) (P : nat -> Prop) (_6446 : nat) : (term102 P n _6446) = (term119 n P _6446).
Proof. exact (@lem278300 (term7 n _6446) (term115 P _6446)). Qed.
Lemma lem278307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278308 (n : nat) (P : nat -> Prop) (_6446 : nat) : (term212 P n _6446) = (term213 n P _6446).
Proof. exact (MK_COMB (@lem278307) (@lem278301 n P _6446)). Qed.
Lemma lem278314 (n : nat) (P : nat -> Prop) (_6446 : nat) : (term119 n P _6446) = (term119 n P _6446).
Proof. exact (eq_refl (term119 n P _6446)). Qed.
Lemma lem278315 (n : nat) (P : nat -> Prop) (_6446 : nat) : ((term102 P n _6446) = (term119 n P _6446)) = ((term119 n P _6446) = (term119 n P _6446)).
Proof. exact (MK_COMB (@lem278308 n P _6446) (@lem278314 n P _6446)). Qed.
Lemma lem278317 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem278318 (x : Prop) : (x = x) = True.
Proof. exact (@lem278317 Prop x). Qed.
Lemma lem278319 (n : nat) (P : nat -> Prop) (_6446 : nat) : ((term119 n P _6446) = (term119 n P _6446)) = True.
Proof. exact (@lem278318 (term119 n P _6446)). Qed.
Lemma lem278320 (n : nat) (P : nat -> Prop) (_6446 : nat) : ((term102 P n _6446) = (term119 n P _6446)) = True.
Proof. exact (TRANS (@lem278315 n P _6446) (@lem278319 n P _6446)). Qed.
Lemma lem278321 (n : nat) (P : nat -> Prop) (_6446 : nat) : True = ((term102 P n _6446) = (term119 n P _6446)).
Proof. exact (SYM (@lem278320 n P _6446)). Qed.
Lemma lem278322 (n : nat) (P : nat -> Prop) (_6446 : nat) : (term102 P n _6446) = (term119 n P _6446).
Proof. exact (EQ_MP (@lem278321 n P _6446) (@lem0)). Qed.
Lemma lem278323 (_6446 : nat) (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term119 n P _6446.
Proof. exact (EQ_MP (@lem278322 n P _6446) (@lem278237 _6446 n P i h1)). Qed.
Lemma lem278325 (b : Prop) (a : Prop) : (a \/ b) = (term204 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem278326 (P : nat -> Prop) (n : nat) (_6446 : nat) : (term119 n P _6446) = (term205 P n _6446).
Proof. exact (@lem278325 (term115 P _6446) (term7 n _6446)). Qed.
Lemma lem278328 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem278329 (P : nat -> Prop) (_6446 : nat) : (term206 P _6446) = (P _6446).
Proof. exact (@lem278328 (P _6446)). Qed.
Lemma lem278330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem278331 (P : nat -> Prop) (_6446 : nat) : (term207 P _6446) = (term208 P _6446).
Proof. exact (MK_COMB (@lem278330) (@lem278329 P _6446)). Qed.
Lemma lem278332 (n : nat) (_6446 : nat) : (term7 n _6446) = (term7 n _6446).
Proof. exact (eq_refl (term7 n _6446)). Qed.
Lemma lem278333 (P : nat -> Prop) (n : nat) (_6446 : nat) : (term205 P n _6446) = (term95 P n _6446).
Proof. exact (MK_COMB (@lem278331 P _6446) (@lem278332 n _6446)). Qed.
Lemma lem278334 (P : nat -> Prop) (n : nat) (_6446 : nat) : (term119 n P _6446) = (term95 P n _6446).
Proof. exact (TRANS (@lem278326 P n _6446) (@lem278333 P n _6446)). Qed.
Lemma lem278337 (_6446 : nat) (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term95 P n _6446.
Proof. exact (EQ_MP (@lem278334 P n _6446) (@lem278323 _6446 n P i h1)). Qed.
Lemma lem278338 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term95 P n i.
Proof. exact (@lem278337 i n P i h1). Qed.
Lemma lem278341 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term7 n i.
Proof. exact (@lem278338 n P i h1 (@lem278294 n P i h1)). Qed.
Lemma lem278342 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term209 n i.
Proof. exact (fun h0 : term56 n i => @lem278341 n P i h1). Qed.
Lemma lem278344 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem278345 (n : nat) (i : nat) : (term209 n i) = (term7 n i).
Proof. exact (@lem278344 (term7 n i)). Qed.
Lemma lem278346 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term7 n i.
Proof. exact (EQ_MP (@lem278345 n i) (@lem278342 n P i h1)). Qed.
Lemma lem278349 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem278351 (n : nat) (i : nat) : (term56 n i) = (term210 n i).
Proof. exact (@lem278349 (term7 n i)). Qed.
Lemma lem278354 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term210 n i.
Proof. exact (EQ_MP (@lem278351 n i) (@lem278239 n P i h1)). Qed.
Lemma lem278357 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : False.
Proof. exact (@lem278354 n P i h1 (@lem278346 n P i h1)). Qed.
Lemma lem278358 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : term211.
Proof. exact (fun h0 : ~ False => @lem278357 n P i h1). Qed.
Lemma lem278360 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem278361 : term211 = False.
Proof. exact (@lem278360 False). Qed.
Lemma lem278362 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term173 n P i) : False.
Proof. exact (EQ_MP (@lem278361) (@lem278358 n P i h1)). Qed.
Lemma lem278363 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term196 n P i) : False.
Proof. exact (or_elim (@lem278147 n P i h1) (fun h0 : term157 i n P => @lem278287 i n P h0) (fun h0 : term173 n P i => @lem278362 n P i h0)). Qed.
Lemma lem278364 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term196 n P i) : (term196 n P i) = False.
Proof. exact (prop_ext (fun h2 : term196 n P i => @lem278363 n P i h1) (fun h2 : False => @lem278147 n P i h1)). Qed.
Lemma lem278365 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term196 n P i) : False.
Proof. exact (EQ_MP (@lem278364 n P i h1) (@lem278147 n P i h1)). Qed.
Lemma lem278366 (n : nat) (P : nat -> Prop) (i : nat) (h1 : term4 P) (h2 : term196 n P i) : False.
Proof. exact (ex_elim (@lem277767 P h1) (fun r : nat => fun h0 : term97 P r => @lem278365 n P i h2)). Qed.
Lemma lem278367 (n : nat) (P : nat -> Prop) (h1 : term4 P) (h2 : term99 n P) : False.
Proof. exact (ex_elim (@lem278069 n P h2) (fun i : nat => fun h0 : term198 n P i => @lem278366 n P i h1 h0)). Qed.
Lemma lem278368 (n : nat) (P : nat -> Prop) (h1 : term4 P) (h2 : term99 n P) : (term4 P) = False.
Proof. exact (prop_ext (fun h3 : term4 P => @lem278367 n P h1 h2) (fun h3 : False => @lem277767 P h1)). Qed.
Lemma lem278369 (n : nat) (P : nat -> Prop) (h1 : term4 P) (h2 : term99 n P) : False.
Proof. exact (EQ_MP (@lem278368 n P h1 h2) (@lem277767 P h1)). Qed.
Lemma lem278370 (n : nat) (P : nat -> Prop) (h1 : term4 P) (h2 : term99 n P) : (term99 n P) = False.
Proof. exact (prop_ext (fun h3 : term99 n P => @lem278369 n P h1 h2) (fun h3 : False => @lem277754 n P h2)). Qed.
Lemma lem278371 (n : nat) (P : nat -> Prop) (h1 : term4 P) (h2 : term99 n P) : False.
Proof. exact (EQ_MP (@lem278370 n P h1 h2) (@lem277754 n P h2)). Qed.
Lemma lem278372 (n : nat) (P : nat -> Prop) (h1 : term4 P) : term98 n P.
Proof. exact (fun h0 : term99 n P => @lem278371 n P h1 h0). Qed.
Lemma lem278373 (n : nat) (P : nat -> Prop) (h1 : term4 P) : (term78 P n) = (term60 n P).
Proof. exact (EQ_MP (@lem277753 n P) (@lem278372 n P h1)). Qed.
Lemma lem278374 (n : nat) (P : nat -> Prop) : term82 n P.
Proof. exact (fun h0 : term4 P => @lem278373 n P h0). Qed.
Lemma lem278379 (P : nat -> Prop) : term84 P.
Proof. exact (fun n : nat => @lem278374 n P). Qed.
Lemma lem278384 : term86.
Proof. exact (fun P : nat -> Prop => @lem278379 P). Qed.
Lemma lem278385 : term88.
Proof. exact (EQ_MP (@lem277748) (@lem278384)). Qed.
Lemma lem278387 : term88.
Proof. exact (@lem277607 (@lem278385)). Qed.
Lemma lem278388 (h1 : term89) : False.
Proof. exact (@lem278387 (@lem277592 h1)). Qed.
Lemma lem278389 (h1 : term89) : term89 = False.
Proof. exact (prop_ext (fun h2 : term89 => @lem278388 h1) (fun h2 : False => @lem277592 h1)). Qed.
Lemma lem278390 (h1 : term89) : False.
Proof. exact (EQ_MP (@lem278389 h1) (@lem277592 h1)). Qed.
Lemma lem278391 : term88.
Proof. exact (fun h0 : term89 => @lem278390 h0). Qed.
Lemma lem278392 : term86.
Proof. exact (EQ_MP (@lem277591) (@lem278391)). Qed.
Lemma lem278393 : term65.
Proof. exact (EQ_MP (@lem277587) (@lem278392)). Qed.
Lemma lem278394 : term51.
Proof. exact (EQ_MP (@lem276887) (@lem278393)). Qed.
Lemma lem278395 : term50.
Proof. exact (EQ_MP (@lem276818) (@lem278394)). Qed.
