Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_IMP_NE_term_abbrevs.
Require Import LT_REFL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem91698 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem91699 : term1 = term2.
Proof. exact (@lem91698 term1). Qed.
Lemma lem91700 : term2 = term1.
Proof. exact (SYM (@lem91699)). Qed.
Lemma lem91701 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem91704 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem91705 : term5.
Proof. exact (fun h0 : term4 => @lem91704 h0). Qed.
Lemma lem91706 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem91707 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem91708 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem91706 h2 (@lem91707 h1)). Qed.
Lemma lem91709 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem91708 h1 h0). Qed.
Lemma lem91710 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem91711 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem91709 h1 (@lem91710 h2)). Qed.
Lemma lem91712 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem91711 h0 h1). Qed.
Lemma lem91713 : term7.
Proof. exact (fun h0 : term5 => @lem91712 h0). Qed.
Lemma lem91716 : term5.
Proof. exact (@lem91713 (@lem91705)). Qed.
Lemma lem91730 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem91731 : term8 = term9.
Proof. exact (@lem91730 term10). Qed.
Lemma lem91736 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem91743 : term4 = term12.
Proof. exact (MK_COMB (@lem91736) (@lem91731)). Qed.
Lemma lem91746 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem91747 : term14 = term14.
Proof. exact (fun_ext (fun n : nat => @lem91746 n)). Qed.
Lemma lem91748 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91749 : term10 = term10.
Proof. exact (MK_COMB (@lem91748) (@lem91747)). Qed.
Lemma lem91750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem91751 : term9 = term9.
Proof. exact (MK_COMB (@lem91750) (@lem91749)). Qed.
Lemma lem91758 (m : nat) (n : nat) : (term15 m n) = (term15 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem91759 (m : nat) : (term16 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem91758 m n)). Qed.
Lemma lem91760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91761 (m : nat) : (term17 m) = (term17 m).
Proof. exact (MK_COMB (@lem91760) (@lem91759 m)). Qed.
Lemma lem91762 : term18 = term18.
Proof. exact (fun_ext (fun m : nat => @lem91761 m)). Qed.
Lemma lem91763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91764 : term1 = term1.
Proof. exact (MK_COMB (@lem91763) (@lem91762)). Qed.
Lemma lem91765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem91766 : term3 = term3.
Proof. exact (MK_COMB (@lem91765) (@lem91764)). Qed.
Lemma lem91767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91768 : term11 = term11.
Proof. exact (MK_COMB (@lem91767) (@lem91766)). Qed.
Lemma lem91769 : term12 = term12.
Proof. exact (MK_COMB (@lem91768) (@lem91751)). Qed.
Lemma lem91794 : term4 = term12.
Proof. exact (TRANS (@lem91743) (@lem91769)). Qed.
Lemma lem91795 : term12 = term4.
Proof. exact (SYM (@lem91794)). Qed.
Lemma lem91796 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem91797 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem91801 (m : nat) (n : nat) : (term19 m n) = (m = n).
Proof. exact (@lem16933 (m = n)). Qed.
Lemma lem91803 (m : nat) (n : nat) : (term20 m n) = (term20 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem91804 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem91803 m n) (@lem91801 m n)). Qed.
Lemma lem91805 (m : nat) (n : nat) : (term23 m n) = (term21 m n).
Proof. exact (@lem17362 (Peano.lt m n) (term24 m n)). Qed.
Lemma lem91806 (m : nat) (n : nat) : (term23 m n) = (term22 m n).
Proof. exact (TRANS (@lem91805 m n) (@lem91804 m n)). Qed.
Lemma lem91807 (P : nat -> Prop) : (term25 P) = (term26 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem91808 (m : nat) : (term27 m) = (term28 m).
Proof. exact (@lem91807 (term16 m)). Qed.
Lemma lem91809 (m : nat) (n : nat) : (term29 m n) = (term15 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem91810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem91811 (m : nat) (n : nat) : (term30 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem91810) (@lem91809 m n)). Qed.
Lemma lem91812 (m : nat) (n : nat) : (term30 m n) = (term22 m n).
Proof. exact (TRANS (@lem91811 m n) (@lem91806 m n)). Qed.
Lemma lem91813 (m : nat) : (term31 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem91812 m n)). Qed.
Lemma lem91814 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem91815 (m : nat) : (term28 m) = (term33 m).
Proof. exact (MK_COMB (@lem91814) (@lem91813 m)). Qed.
Lemma lem91816 (m : nat) : (term27 m) = (term33 m).
Proof. exact (TRANS (@lem91808 m) (@lem91815 m)). Qed.
Lemma lem91817 (P : nat -> Prop) : (term25 P) = (term26 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem91818 : term3 = term34.
Proof. exact (@lem91817 term18). Qed.
Lemma lem91819 (m : nat) : (term35 m) = (term17 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem91820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem91821 (m : nat) : (term36 m) = (term27 m).
Proof. exact (MK_COMB (@lem91820) (@lem91819 m)). Qed.
Lemma lem91822 (m : nat) : (term36 m) = (term33 m).
Proof. exact (TRANS (@lem91821 m) (@lem91816 m)). Qed.
Lemma lem91823 : term37 = term38.
Proof. exact (fun_ext (fun m : nat => @lem91822 m)). Qed.
Lemma lem91824 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem91825 : term34 = term39.
Proof. exact (MK_COMB (@lem91824) (@lem91823)). Qed.
Lemma lem91882 : term3 = term39.
Proof. exact (TRANS (@lem91818) (@lem91825)). Qed.
Lemma lem91883 (h1 : term3) : term39.
Proof. exact (EQ_MP (@lem91882) (@lem91796 h1)). Qed.
Lemma lem91884 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem91885 : term14 = term14.
Proof. exact (fun_ext (fun n : nat => @lem91884 n)). Qed.
Lemma lem91886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91895 : term10 = term10.
Proof. exact (MK_COMB (@lem91886) (@lem91885)). Qed.
Lemma lem91896 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem91895) (@lem91797 h1)). Qed.
Lemma lem91897 (m : nat) (h1 : term33 m) : term33 m.
Proof. exact (h1). Qed.
Lemma lem91905 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem91906 : term14 = term14.
Proof. exact (fun_ext (fun n : nat => @lem91905 n)). Qed.
Lemma lem91907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91908 : term10 = term10.
Proof. exact (MK_COMB (@lem91907) (@lem91906)). Qed.
Lemma lem91909 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem91908) (@lem91896 h1)). Qed.
Lemma lem91923 (m : nat) (n : nat) (h1 : term22 m n) : term22 m n.
Proof. exact (h1). Qed.
Lemma lem91927 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem91928 : term14 = term14.
Proof. exact (fun_ext (fun n : nat => @lem91927 n)). Qed.
Lemma lem91929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91931 : term10 = term10.
Proof. exact (MK_COMB (@lem91929) (@lem91928)). Qed.
Lemma lem91932 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem91931) (@lem91909 h1)). Qed.
Lemma lem91941 (_2297 : nat) (h1 : term10) : term40 _2297.
Proof. exact (@lem91932 h1 _2297). Qed.
Lemma lem91942 (_2297 : nat) : (term40 _2297) = (term13 _2297).
Proof. exact (eq_refl (term40 _2297)). Qed.
Lemma lem91947 (m : nat) (n : nat) (h1 : term22 m n) : Peano.lt m n.
Proof. exact (proj1 (@lem91923 m n h1)). Qed.
Lemma lem91949 (m : nat) (n : nat) (h1 : term22 m n) : m = n.
Proof. exact (proj2 (@lem91923 m n h1)). Qed.
Lemma lem91977 (_2297 : nat) (h1 : term10) : term13 _2297.
Proof. exact (EQ_MP (@lem91942 _2297) (@lem91941 _2297 h1)). Qed.
Lemma lem91978 (n : nat) : (term41 n) = (term41 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem91979 (m : nat) (n : nat) (h1 : term22 m n) : (term42 n m) = (term43 n).
Proof. exact (MK_COMB (@lem91978 n) (@lem91949 m n h1)). Qed.
Lemma lem91980 (n : nat) : (term43 n) = (Peano.lt n n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem91981 (n : nat) (m : nat) : (term44 n m) = (term44 n m).
Proof. exact (eq_refl (term44 n m)). Qed.
Lemma lem91982 (m : nat) (n : nat) : ((term42 n m) = (term43 n)) = ((term42 n m) = (Peano.lt n n)).
Proof. exact (MK_COMB (@lem91981 n m) (@lem91980 n)). Qed.
Lemma lem91983 (m : nat) (n : nat) : (term42 n m) = (Peano.lt m n).
Proof. exact (eq_refl (term42 n m)). Qed.
Lemma lem91984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91985 (m : nat) (n : nat) : (term44 n m) = (term45 m n).
Proof. exact (MK_COMB (@lem91984) (@lem91983 m n)). Qed.
Lemma lem91986 (n : nat) : (Peano.lt n n) = (Peano.lt n n).
Proof. exact (eq_refl (Peano.lt n n)). Qed.
Lemma lem91987 (m : nat) (n : nat) : ((term42 n m) = (Peano.lt n n)) = ((Peano.lt m n) = (Peano.lt n n)).
Proof. exact (MK_COMB (@lem91985 m n) (@lem91986 n)). Qed.
Lemma lem91988 (m : nat) (n : nat) : ((term42 n m) = (term43 n)) = ((Peano.lt m n) = (Peano.lt n n)).
Proof. exact (TRANS (@lem91982 m n) (@lem91987 m n)). Qed.
Lemma lem91989 (m : nat) (n : nat) (h1 : term22 m n) : (Peano.lt m n) = (Peano.lt n n).
Proof. exact (EQ_MP (@lem91988 m n) (@lem91979 m n h1)). Qed.
Lemma lem91992 (m : nat) (n : nat) (h1 : term22 m n) : Peano.lt n n.
Proof. exact (EQ_MP (@lem91989 m n h1) (@lem91947 m n h1)). Qed.
Lemma lem91993 (m : nat) (n : nat) (h1 : term22 m n) : term46 n.
Proof. exact (fun h0 : term13 n => @lem91992 m n h1). Qed.
Lemma lem91995 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem91996 (n : nat) : (term46 n) = (Peano.lt n n).
Proof. exact (@lem91995 (Peano.lt n n)). Qed.
Lemma lem91997 (m : nat) (n : nat) (h1 : term22 m n) : Peano.lt n n.
Proof. exact (EQ_MP (@lem91996 n) (@lem91993 m n h1)). Qed.
Lemma lem92000 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem92002 (_2297 : nat) : (term13 _2297) = (term48 _2297).
Proof. exact (@lem92000 (Peano.lt _2297 _2297)). Qed.
Lemma lem92005 (_2297 : nat) (h1 : term10) : term48 _2297.
Proof. exact (EQ_MP (@lem92002 _2297) (@lem91977 _2297 h1)). Qed.
Lemma lem92006 (n : nat) (h1 : term10) : term48 n.
Proof. exact (@lem92005 n h1). Qed.
Lemma lem92009 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : False.
Proof. exact (@lem92006 n h1 (@lem91997 m n h2)). Qed.
Lemma lem92010 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : term49.
Proof. exact (fun h0 : ~ False => @lem92009 m n h1 h2). Qed.
Lemma lem92012 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem92013 : term49 = False.
Proof. exact (@lem92012 False). Qed.
Lemma lem92015 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : False.
Proof. exact (EQ_MP (@lem92013) (@lem92010 m n h1 h2)). Qed.
Lemma lem92016 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem92015 m n h1 h2) (fun h3 : False => @lem91932 h1)). Qed.
Lemma lem92017 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : False.
Proof. exact (EQ_MP (@lem92016 m n h1 h2) (@lem91932 h1)). Qed.
Lemma lem92018 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : (term22 m n) = False.
Proof. exact (prop_ext (fun h3 : term22 m n => @lem92017 m n h1 h2) (fun h3 : False => @lem91923 m n h2)). Qed.
Lemma lem92019 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : False.
Proof. exact (EQ_MP (@lem92018 m n h1 h2) (@lem91923 m n h2)). Qed.
Lemma lem92020 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem92019 m n h1 h2) (fun h3 : False => @lem91909 h1)). Qed.
Lemma lem92021 (m : nat) (n : nat) (h1 : term10) (h2 : term22 m n) : False.
Proof. exact (EQ_MP (@lem92020 m n h1 h2) (@lem91909 h1)). Qed.
Lemma lem92022 (m : nat) (h1 : term10) (h2 : term33 m) : False.
Proof. exact (ex_elim (@lem91897 m h2) (fun n : nat => fun h0 : term32 m n => @lem92021 m n h1 h0)). Qed.
Lemma lem92023 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem91883 h2) (fun m : nat => fun h0 : term38 m => @lem92022 m h1 h0)). Qed.
Lemma lem92024 (h1 : term10) (h2 : term3) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem92023 h1 h2) (fun h3 : False => @lem91896 h1)). Qed.
Lemma lem92025 (h1 : term10) (h2 : term3) : False.
Proof. exact (EQ_MP (@lem92024 h1 h2) (@lem91896 h1)). Qed.
Lemma lem92026 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem92025 h0 h1). Qed.
Lemma lem92027 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem92028 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem92027) (@lem92026 h1)). Qed.
Lemma lem92029 : term12.
Proof. exact (fun h0 : term3 => @lem92028 h0). Qed.
Lemma lem92030 : term4.
Proof. exact (EQ_MP (@lem91795) (@lem92029)). Qed.
Lemma lem92032 : term4.
Proof. exact (@lem91716 (@lem92030)). Qed.
Lemma lem92033 (h1 : term3) : term8.
Proof. exact (@lem92032 (@lem91701 h1)). Qed.
Lemma lem92034 (h1 : term3) : False.
Proof. exact (@lem92033 h1 (@lem91686)). Qed.
Lemma lem92035 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem92034 h1) (fun h2 : False => @lem91701 h1)). Qed.
Lemma lem92036 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem92035 h1) (@lem91701 h1)). Qed.
Lemma lem92037 : term2.
Proof. exact (fun h0 : term3 => @lem92036 h0). Qed.
Lemma lem92038 : term1.
Proof. exact (EQ_MP (@lem91700) (@lem92037)). Qed.
