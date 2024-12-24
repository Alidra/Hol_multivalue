Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm520356_term_abbrevs.
Require Import ARITH_LE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem519815 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem519816 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem519815 n m h1)). Qed.
Lemma lem519817 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem519818 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem519817 m n h1)). Qed.
Lemma lem519819 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem519816 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem519818 m n h1)). Qed.
Lemma lem519820 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem519819 m n)). Qed.
Lemma lem519821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519822 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem519821) (@lem519820 m)). Qed.
Lemma lem519823 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem519822 m)). Qed.
Lemma lem519824 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519825 : term7 = term8.
Proof. exact (MK_COMB (@lem519824) (@lem519823)). Qed.
Lemma lem519826 : term8.
Proof. exact (EQ_MP (@lem519825) (@lem97961)). Qed.
Lemma lem519827 : term9.
Proof. exact (proj2 (@lem519780)). Qed.
Lemma lem519828 : term10.
Proof. exact (proj2 (@lem519827)). Qed.
Lemma lem519829 : term11.
Proof. exact (proj2 (@lem519828)). Qed.
Lemma lem519830 : term12.
Proof. exact (proj2 (@lem519829)). Qed.
Lemma lem519831 : term13.
Proof. exact (proj2 (@lem519830)). Qed.
Lemma lem519832 : term14.
Proof. exact (proj2 (@lem519831)). Qed.
Lemma lem519833 : term15.
Proof. exact (proj2 (@lem519832)). Qed.
Lemma lem519834 : term16.
Proof. exact (proj2 (@lem519833)). Qed.
Lemma lem519835 : term17.
Proof. exact (proj2 (@lem519834)). Qed.
Lemma lem519836 (m : nat) : term18 m.
Proof. exact (@lem519835 m). Qed.
Lemma lem519837 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem519838 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem519837 m) (@lem519836 m)). Qed.
Lemma lem519839 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem519838 m n). Qed.
Lemma lem519840 (m : nat) (n : nat) : (term20 m n) = ((term21 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem519842 : term22.
Proof. exact (proj1 (@lem519834)). Qed.
Lemma lem519843 (m : nat) : term23 m.
Proof. exact (@lem519842 m). Qed.
Lemma lem519844 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem519845 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem519844 m) (@lem519843 m)). Qed.
Lemma lem519846 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem519845 m n). Qed.
Lemma lem519847 (m : nat) (n : nat) : (term25 m n) = ((term26 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem519849 : term27.
Proof. exact (proj1 (@lem519833)). Qed.
Lemma lem519850 (m : nat) : term28 m.
Proof. exact (@lem519849 m). Qed.
Lemma lem519851 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem519852 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem519851 m) (@lem519850 m)). Qed.
Lemma lem519853 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem519852 m n). Qed.
Lemma lem519854 (m : nat) (n : nat) : (term30 m n) = ((term31 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem519856 : term32.
Proof. exact (proj1 (@lem519832)). Qed.
Lemma lem519857 (m : nat) : term33 m.
Proof. exact (@lem519856 m). Qed.
Lemma lem519858 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem519859 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem519858 m) (@lem519857 m)). Qed.
Lemma lem519860 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem519859 m n). Qed.
Lemma lem519861 (m : nat) (n : nat) : (term35 m n) = ((term36 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem519863 : term37.
Proof. exact (proj1 (@lem519831)). Qed.
Lemma lem519864 (n : nat) : term38 n.
Proof. exact (@lem519863 n). Qed.
Lemma lem519865 (n : nat) : (term38 n) = ((term39 n) = True).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem519867 : term40.
Proof. exact (proj1 (@lem519830)). Qed.
Lemma lem519868 (n : nat) : term41 n.
Proof. exact (@lem519867 n). Qed.
Lemma lem519869 (n : nat) : (term41 n) = ((term42 n) = True).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem519871 : term43.
Proof. exact (proj1 (@lem519829)). Qed.
Lemma lem519872 (n : nat) : term44 n.
Proof. exact (@lem519871 n). Qed.
Lemma lem519873 (n : nat) : (term44 n) = ((term45 n) = False).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem519875 : term46.
Proof. exact (proj1 (@lem519828)). Qed.
Lemma lem519876 (n : nat) : term47 n.
Proof. exact (@lem519875 n). Qed.
Lemma lem519877 (n : nat) : (term47 n) = ((term48 n) = (Peano.le n 0)).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem519880 : term49.
Proof. exact (proj1 (@lem519780)). Qed.
Lemma lem519881 (m : nat) : term50 m.
Proof. exact (@lem519880 m). Qed.
Lemma lem519882 (m : nat) : (term50 m) = (term51 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem519883 (m : nat) : term51 m.
Proof. exact (EQ_MP (@lem519882 m) (@lem519881 m)). Qed.
Lemma lem519884 (m : nat) (n : nat) : term52 m n.
Proof. exact (@lem519883 m n). Qed.
Lemma lem519885 (m : nat) (n : nat) : (term52 m n) = ((term53 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem519887 (m : nat) : term54 m.
Proof. exact (@lem519826 m). Qed.
Lemma lem519888 (m : nat) : (term54 m) = (term4 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem519889 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem519888 m) (@lem519887 m)). Qed.
Lemma lem519890 (m : nat) (n : nat) : term55 m n.
Proof. exact (@lem519889 m n). Qed.
Lemma lem519891 (m : nat) (n : nat) : (term55 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem519909 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem519910 (n : nat) (m : nat) : (term56 m n) = (term57 n m).
Proof. exact (@lem519909 (NUMERAL n) (NUMERAL m)). Qed.
Lemma lem519912 (m : nat) (n : nat) : (term53 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem519885 m n) (@lem519884 m n)). Qed.
Lemma lem519913 (n : nat) (m : nat) : (term53 n m) = (Peano.le n m).
Proof. exact (@lem519912 n m). Qed.
Lemma lem519914 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519915 (n : nat) (m : nat) : (term57 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem519914) (@lem519913 n m)). Qed.
Lemma lem519916 (n : nat) (m : nat) : (term56 m n) = (term0 n m).
Proof. exact (TRANS (@lem519910 n m) (@lem519915 n m)). Qed.
Lemma lem519917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519918 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem519917) (@lem519916 n m)). Qed.
Lemma lem519920 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem519921 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem519920 n m). Qed.
Lemma lem519922 (n : nat) (m : nat) : ((term56 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem519918 n m) (@lem519921 n m)). Qed.
Lemma lem519924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519925 (x : Prop) : (x = x) = True.
Proof. exact (@lem519924 Prop x). Qed.
Lemma lem519926 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem519925 (term0 n m)). Qed.
Lemma lem519927 (m : nat) (n : nat) : ((term56 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem519922 n m) (@lem519926 n m)). Qed.
Lemma lem519928 (m : nat) : (term60 m) = term61.
Proof. exact (fun_ext (fun n : nat => @lem519927 m n)). Qed.
Lemma lem519929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519930 (m : nat) : (term62 m) = term63.
Proof. exact (MK_COMB (@lem519929) (@lem519928 m)). Qed.
Lemma lem519932 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519933 (t : Prop) : (term65 t) = t.
Proof. exact (@lem519932 nat t). Qed.
Lemma lem519934 : term63 = True.
Proof. exact (@lem519933 True). Qed.
Lemma lem519935 (m : nat) : (term62 m) = True.
Proof. exact (TRANS (@lem519930 m) (@lem519934)). Qed.
Lemma lem519936 : term66 = term61.
Proof. exact (fun_ext (fun m : nat => @lem519935 m)). Qed.
Lemma lem519937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519938 : term67 = term63.
Proof. exact (MK_COMB (@lem519937) (@lem519936)). Qed.
Lemma lem519940 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519941 (t : Prop) : (term65 t) = t.
Proof. exact (@lem519940 nat t). Qed.
Lemma lem519942 : term63 = True.
Proof. exact (@lem519941 True). Qed.
Lemma lem519943 : term67 = True.
Proof. exact (TRANS (@lem519938) (@lem519942)). Qed.
Lemma lem519944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519945 : term68 = (and True).
Proof. exact (MK_COMB (@lem519944) (@lem519943)). Qed.
Lemma lem519949 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem519950 : ((Peano.lt 0 0) = False) = term69.
Proof. exact (@lem519949 (Peano.lt 0 0)). Qed.
Lemma lem519952 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem519953 : (Peano.lt 0 0) = term70.
Proof. exact (@lem519952 0 0). Qed.
Lemma lem519955 : (Peano.le 0 0) = True.
Proof. exact (proj1 (@lem519827)). Qed.
Lemma lem519956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519957 : term70 = (~ True).
Proof. exact (MK_COMB (@lem519956) (@lem519955)). Qed.
Lemma lem519959 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem519960 : term70 = False.
Proof. exact (TRANS (@lem519957) (@lem519959)). Qed.
Lemma lem519961 : (Peano.lt 0 0) = False.
Proof. exact (TRANS (@lem519953) (@lem519960)). Qed.
Lemma lem519962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519963 : term69 = (~ False).
Proof. exact (MK_COMB (@lem519962) (@lem519961)). Qed.
Lemma lem519965 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519966 : term69 = True.
Proof. exact (TRANS (@lem519963) (@lem519965)). Qed.
Lemma lem519967 : ((Peano.lt 0 0) = False) = True.
Proof. exact (TRANS (@lem519950) (@lem519966)). Qed.
Lemma lem519968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519969 : term71 = (and True).
Proof. exact (MK_COMB (@lem519968) (@lem519967)). Qed.
Lemma lem519977 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem519978 (n : nat) : ((term72 n) = False) = (term73 n).
Proof. exact (@lem519977 (term72 n)). Qed.
Lemma lem519980 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem519981 (n : nat) : (term72 n) = (term74 n).
Proof. exact (@lem519980 0 (BIT0 n)). Qed.
Lemma lem519983 (n : nat) : (term42 n) = True.
Proof. exact (EQ_MP (@lem519869 n) (@lem519868 n)). Qed.
Lemma lem519984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519985 (n : nat) : (term74 n) = (~ True).
Proof. exact (MK_COMB (@lem519984) (@lem519983 n)). Qed.
Lemma lem519987 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem519988 (n : nat) : (term74 n) = False.
Proof. exact (TRANS (@lem519985 n) (@lem519987)). Qed.
Lemma lem519989 (n : nat) : (term72 n) = False.
Proof. exact (TRANS (@lem519981 n) (@lem519988 n)). Qed.
Lemma lem519990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519991 (n : nat) : (term73 n) = (~ False).
Proof. exact (MK_COMB (@lem519990) (@lem519989 n)). Qed.
Lemma lem519993 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519994 (n : nat) : (term73 n) = True.
Proof. exact (TRANS (@lem519991 n) (@lem519993)). Qed.
Lemma lem519995 (n : nat) : ((term72 n) = False) = True.
Proof. exact (TRANS (@lem519978 n) (@lem519994 n)). Qed.
Lemma lem519996 : term75 = term61.
Proof. exact (fun_ext (fun n : nat => @lem519995 n)). Qed.
Lemma lem519997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519998 : term76 = term63.
Proof. exact (MK_COMB (@lem519997) (@lem519996)). Qed.
Lemma lem520000 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520001 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520000 nat t). Qed.
Lemma lem520002 : term63 = True.
Proof. exact (@lem520001 True). Qed.
Lemma lem520003 : term76 = True.
Proof. exact (TRANS (@lem519998) (@lem520002)). Qed.
Lemma lem520004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520005 : term77 = (and True).
Proof. exact (MK_COMB (@lem520004) (@lem520003)). Qed.
Lemma lem520013 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem520014 (n : nat) : ((term78 n) = False) = (term79 n).
Proof. exact (@lem520013 (term78 n)). Qed.
Lemma lem520016 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520017 (n : nat) : (term78 n) = (term80 n).
Proof. exact (@lem520016 0 (BIT1 n)). Qed.
Lemma lem520019 (n : nat) : (term39 n) = True.
Proof. exact (EQ_MP (@lem519865 n) (@lem519864 n)). Qed.
Lemma lem520020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520021 (n : nat) : (term80 n) = (~ True).
Proof. exact (MK_COMB (@lem520020) (@lem520019 n)). Qed.
Lemma lem520023 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem520024 (n : nat) : (term80 n) = False.
Proof. exact (TRANS (@lem520021 n) (@lem520023)). Qed.
Lemma lem520025 (n : nat) : (term78 n) = False.
Proof. exact (TRANS (@lem520017 n) (@lem520024 n)). Qed.
Lemma lem520026 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520027 (n : nat) : (term79 n) = (~ False).
Proof. exact (MK_COMB (@lem520026) (@lem520025 n)). Qed.
Lemma lem520029 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem520030 (n : nat) : (term79 n) = True.
Proof. exact (TRANS (@lem520027 n) (@lem520029)). Qed.
Lemma lem520031 (n : nat) : ((term78 n) = False) = True.
Proof. exact (TRANS (@lem520014 n) (@lem520030 n)). Qed.
Lemma lem520032 : term81 = term61.
Proof. exact (fun_ext (fun n : nat => @lem520031 n)). Qed.
Lemma lem520033 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520034 : term82 = term63.
Proof. exact (MK_COMB (@lem520033) (@lem520032)). Qed.
Lemma lem520036 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520037 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520036 nat t). Qed.
Lemma lem520038 : term63 = True.
Proof. exact (@lem520037 True). Qed.
Lemma lem520039 : term82 = True.
Proof. exact (TRANS (@lem520034) (@lem520038)). Qed.
Lemma lem520040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520041 : term83 = (and True).
Proof. exact (MK_COMB (@lem520040) (@lem520039)). Qed.
Lemma lem520051 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520052 (n : nat) : (term84 n) = (term85 n).
Proof. exact (@lem520051 (BIT0 n) 0). Qed.
Lemma lem520054 (n : nat) : (term48 n) = (Peano.le n 0).
Proof. exact (EQ_MP (@lem519877 n) (@lem519876 n)). Qed.
Lemma lem520055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520056 (n : nat) : (term85 n) = (term86 n).
Proof. exact (MK_COMB (@lem520055) (@lem520054 n)). Qed.
Lemma lem520057 (n : nat) : (term84 n) = (term86 n).
Proof. exact (TRANS (@lem520052 n) (@lem520056 n)). Qed.
Lemma lem520058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem520059 (n : nat) : (term87 n) = (term88 n).
Proof. exact (MK_COMB (@lem520058) (@lem520057 n)). Qed.
Lemma lem520061 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520062 (n : nat) : (Peano.lt 0 n) = (term86 n).
Proof. exact (@lem520061 n 0). Qed.
Lemma lem520063 (n : nat) : ((term84 n) = (Peano.lt 0 n)) = ((term86 n) = (term86 n)).
Proof. exact (MK_COMB (@lem520059 n) (@lem520062 n)). Qed.
Lemma lem520065 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem520066 (x : Prop) : (x = x) = True.
Proof. exact (@lem520065 Prop x). Qed.
Lemma lem520067 (n : nat) : ((term86 n) = (term86 n)) = True.
Proof. exact (@lem520066 (term86 n)). Qed.
Lemma lem520068 (n : nat) : ((term84 n) = (Peano.lt 0 n)) = True.
Proof. exact (TRANS (@lem520063 n) (@lem520067 n)). Qed.
Lemma lem520069 : term89 = term61.
Proof. exact (fun_ext (fun n : nat => @lem520068 n)). Qed.
Lemma lem520070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520071 : term90 = term63.
Proof. exact (MK_COMB (@lem520070) (@lem520069)). Qed.
Lemma lem520073 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520074 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520073 nat t). Qed.
Lemma lem520075 : term63 = True.
Proof. exact (@lem520074 True). Qed.
Lemma lem520076 : term90 = True.
Proof. exact (TRANS (@lem520071) (@lem520075)). Qed.
Lemma lem520077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520078 : term91 = (and True).
Proof. exact (MK_COMB (@lem520077) (@lem520076)). Qed.
Lemma lem520086 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem520087 (n : nat) : ((term92 n) = True) = (term92 n).
Proof. exact (@lem520086 (term92 n)). Qed.
Lemma lem520089 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520090 (n : nat) : (term92 n) = (term93 n).
Proof. exact (@lem520089 (BIT1 n) 0). Qed.
Lemma lem520091 (n : nat) : ((term92 n) = True) = (term93 n).
Proof. exact (TRANS (@lem520087 n) (@lem520090 n)). Qed.
Lemma lem520093 (n : nat) : (term45 n) = False.
Proof. exact (EQ_MP (@lem519873 n) (@lem519872 n)). Qed.
Lemma lem520094 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520095 (n : nat) : (term93 n) = (~ False).
Proof. exact (MK_COMB (@lem520094) (@lem520093 n)). Qed.
Lemma lem520097 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem520098 (n : nat) : (term93 n) = True.
Proof. exact (TRANS (@lem520095 n) (@lem520097)). Qed.
Lemma lem520099 (n : nat) : ((term92 n) = True) = True.
Proof. exact (TRANS (@lem520091 n) (@lem520098 n)). Qed.
Lemma lem520100 : term94 = term61.
Proof. exact (fun_ext (fun n : nat => @lem520099 n)). Qed.
Lemma lem520101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520102 : term95 = term63.
Proof. exact (MK_COMB (@lem520101) (@lem520100)). Qed.
Lemma lem520104 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520105 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520104 nat t). Qed.
Lemma lem520106 : term63 = True.
Proof. exact (@lem520105 True). Qed.
Lemma lem520107 : term95 = True.
Proof. exact (TRANS (@lem520102) (@lem520106)). Qed.
Lemma lem520108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520109 : term96 = (and True).
Proof. exact (MK_COMB (@lem520108) (@lem520107)). Qed.
Lemma lem520123 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520124 (n : nat) (m : nat) : (term97 m n) = (term98 n m).
Proof. exact (@lem520123 (BIT0 n) (BIT0 m)). Qed.
Lemma lem520126 (m : nat) (n : nat) : (term36 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem519861 m n) (@lem519860 m n)). Qed.
Lemma lem520127 (n : nat) (m : nat) : (term36 n m) = (Peano.le n m).
Proof. exact (@lem520126 n m). Qed.
Lemma lem520128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520129 (n : nat) (m : nat) : (term98 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem520128) (@lem520127 n m)). Qed.
Lemma lem520130 (n : nat) (m : nat) : (term97 m n) = (term0 n m).
Proof. exact (TRANS (@lem520124 n m) (@lem520129 n m)). Qed.
Lemma lem520131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem520132 (n : nat) (m : nat) : (term99 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem520131) (@lem520130 n m)). Qed.
Lemma lem520134 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520135 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem520134 n m). Qed.
Lemma lem520136 (n : nat) (m : nat) : ((term97 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem520132 n m) (@lem520135 n m)). Qed.
Lemma lem520138 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem520139 (x : Prop) : (x = x) = True.
Proof. exact (@lem520138 Prop x). Qed.
Lemma lem520140 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem520139 (term0 n m)). Qed.
Lemma lem520141 (m : nat) (n : nat) : ((term97 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem520136 n m) (@lem520140 n m)). Qed.
Lemma lem520142 (m : nat) : (term100 m) = term61.
Proof. exact (fun_ext (fun n : nat => @lem520141 m n)). Qed.
Lemma lem520143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520144 (m : nat) : (term101 m) = term63.
Proof. exact (MK_COMB (@lem520143) (@lem520142 m)). Qed.
Lemma lem520146 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520147 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520146 nat t). Qed.
Lemma lem520148 : term63 = True.
Proof. exact (@lem520147 True). Qed.
Lemma lem520149 (m : nat) : (term101 m) = True.
Proof. exact (TRANS (@lem520144 m) (@lem520148)). Qed.
Lemma lem520150 : term102 = term61.
Proof. exact (fun_ext (fun m : nat => @lem520149 m)). Qed.
Lemma lem520151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520152 : term103 = term63.
Proof. exact (MK_COMB (@lem520151) (@lem520150)). Qed.
Lemma lem520154 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520155 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520154 nat t). Qed.
Lemma lem520156 : term63 = True.
Proof. exact (@lem520155 True). Qed.
Lemma lem520157 : term103 = True.
Proof. exact (TRANS (@lem520152) (@lem520156)). Qed.
Lemma lem520158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520159 : term104 = (and True).
Proof. exact (MK_COMB (@lem520158) (@lem520157)). Qed.
Lemma lem520173 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520174 (n : nat) (m : nat) : (term105 m n) = (term106 n m).
Proof. exact (@lem520173 (BIT1 n) (BIT0 m)). Qed.
Lemma lem520176 (m : nat) (n : nat) : (term26 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem519847 m n) (@lem519846 m n)). Qed.
Lemma lem520177 (n : nat) (m : nat) : (term26 n m) = (Peano.lt n m).
Proof. exact (@lem520176 n m). Qed.
Lemma lem520179 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520180 (m : nat) (n : nat) : (term26 n m) = (term0 m n).
Proof. exact (TRANS (@lem520177 n m) (@lem520179 m n)). Qed.
Lemma lem520181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520182 (m : nat) (n : nat) : (term106 n m) = (term107 m n).
Proof. exact (MK_COMB (@lem520181) (@lem520180 m n)). Qed.
Lemma lem520184 (t : Prop) : (term108 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem520185 (m : nat) (n : nat) : (term107 m n) = (Peano.le m n).
Proof. exact (@lem520184 (Peano.le m n)). Qed.
Lemma lem520186 (m : nat) (n : nat) : (term106 n m) = (Peano.le m n).
Proof. exact (TRANS (@lem520182 m n) (@lem520185 m n)). Qed.
Lemma lem520187 (m : nat) (n : nat) : (term105 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem520174 n m) (@lem520186 m n)). Qed.
Lemma lem520188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem520189 (m : nat) (n : nat) : (term109 m n) = (term110 m n).
Proof. exact (MK_COMB (@lem520188) (@lem520187 m n)). Qed.
Lemma lem520190 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem520191 (m : nat) (n : nat) : ((term105 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem520189 m n) (@lem520190 m n)). Qed.
Lemma lem520193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem520194 (x : Prop) : (x = x) = True.
Proof. exact (@lem520193 Prop x). Qed.
Lemma lem520195 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem520194 (Peano.le m n)). Qed.
Lemma lem520196 (m : nat) (n : nat) : ((term105 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem520191 m n) (@lem520195 m n)). Qed.
Lemma lem520197 (m : nat) : (term111 m) = term61.
Proof. exact (fun_ext (fun n : nat => @lem520196 m n)). Qed.
Lemma lem520198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520199 (m : nat) : (term112 m) = term63.
Proof. exact (MK_COMB (@lem520198) (@lem520197 m)). Qed.
Lemma lem520201 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520202 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520201 nat t). Qed.
Lemma lem520203 : term63 = True.
Proof. exact (@lem520202 True). Qed.
Lemma lem520204 (m : nat) : (term112 m) = True.
Proof. exact (TRANS (@lem520199 m) (@lem520203)). Qed.
Lemma lem520205 : term113 = term61.
Proof. exact (fun_ext (fun m : nat => @lem520204 m)). Qed.
Lemma lem520206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520207 : term114 = term63.
Proof. exact (MK_COMB (@lem520206) (@lem520205)). Qed.
Lemma lem520209 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520210 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520209 nat t). Qed.
Lemma lem520211 : term63 = True.
Proof. exact (@lem520210 True). Qed.
Lemma lem520212 : term114 = True.
Proof. exact (TRANS (@lem520207) (@lem520211)). Qed.
Lemma lem520213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520214 : term115 = (and True).
Proof. exact (MK_COMB (@lem520213) (@lem520212)). Qed.
Lemma lem520228 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520229 (n : nat) (m : nat) : (term116 m n) = (term117 n m).
Proof. exact (@lem520228 (BIT0 n) (BIT1 m)). Qed.
Lemma lem520231 (m : nat) (n : nat) : (term31 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem519854 m n) (@lem519853 m n)). Qed.
Lemma lem520232 (n : nat) (m : nat) : (term31 n m) = (Peano.le n m).
Proof. exact (@lem520231 n m). Qed.
Lemma lem520233 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520234 (n : nat) (m : nat) : (term117 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem520233) (@lem520232 n m)). Qed.
Lemma lem520235 (n : nat) (m : nat) : (term116 m n) = (term0 n m).
Proof. exact (TRANS (@lem520229 n m) (@lem520234 n m)). Qed.
Lemma lem520236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem520237 (n : nat) (m : nat) : (term118 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem520236) (@lem520235 n m)). Qed.
Lemma lem520239 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520240 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem520239 n m). Qed.
Lemma lem520241 (n : nat) (m : nat) : ((term116 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem520237 n m) (@lem520240 n m)). Qed.
Lemma lem520243 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem520244 (x : Prop) : (x = x) = True.
Proof. exact (@lem520243 Prop x). Qed.
Lemma lem520245 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem520244 (term0 n m)). Qed.
Lemma lem520246 (m : nat) (n : nat) : ((term116 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem520241 n m) (@lem520245 n m)). Qed.
Lemma lem520247 (m : nat) : (term119 m) = term61.
Proof. exact (fun_ext (fun n : nat => @lem520246 m n)). Qed.
Lemma lem520248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520249 (m : nat) : (term120 m) = term63.
Proof. exact (MK_COMB (@lem520248) (@lem520247 m)). Qed.
Lemma lem520251 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520252 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520251 nat t). Qed.
Lemma lem520253 : term63 = True.
Proof. exact (@lem520252 True). Qed.
Lemma lem520254 (m : nat) : (term120 m) = True.
Proof. exact (TRANS (@lem520249 m) (@lem520253)). Qed.
Lemma lem520255 : term121 = term61.
Proof. exact (fun_ext (fun m : nat => @lem520254 m)). Qed.
Lemma lem520256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520257 : term122 = term63.
Proof. exact (MK_COMB (@lem520256) (@lem520255)). Qed.
Lemma lem520259 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520260 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520259 nat t). Qed.
Lemma lem520261 : term63 = True.
Proof. exact (@lem520260 True). Qed.
Lemma lem520262 : term122 = True.
Proof. exact (TRANS (@lem520257) (@lem520261)). Qed.
Lemma lem520263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem520264 : term123 = (and True).
Proof. exact (MK_COMB (@lem520263) (@lem520262)). Qed.
Lemma lem520276 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520277 (n : nat) (m : nat) : (term124 m n) = (term125 n m).
Proof. exact (@lem520276 (BIT1 n) (BIT1 m)). Qed.
Lemma lem520279 (m : nat) (n : nat) : (term21 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem519840 m n) (@lem519839 m n)). Qed.
Lemma lem520280 (n : nat) (m : nat) : (term21 n m) = (Peano.le n m).
Proof. exact (@lem520279 n m). Qed.
Lemma lem520281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem520282 (n : nat) (m : nat) : (term125 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem520281) (@lem520280 n m)). Qed.
Lemma lem520283 (n : nat) (m : nat) : (term124 m n) = (term0 n m).
Proof. exact (TRANS (@lem520277 n m) (@lem520282 n m)). Qed.
Lemma lem520284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem520285 (n : nat) (m : nat) : (term126 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem520284) (@lem520283 n m)). Qed.
Lemma lem520287 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem519891 m n) (@lem519890 m n)). Qed.
Lemma lem520288 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem520287 n m). Qed.
Lemma lem520289 (n : nat) (m : nat) : ((term124 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem520285 n m) (@lem520288 n m)). Qed.
Lemma lem520291 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem520292 (x : Prop) : (x = x) = True.
Proof. exact (@lem520291 Prop x). Qed.
Lemma lem520293 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem520292 (term0 n m)). Qed.
Lemma lem520294 (m : nat) (n : nat) : ((term124 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem520289 n m) (@lem520293 n m)). Qed.
Lemma lem520295 (m : nat) : (term127 m) = term61.
Proof. exact (fun_ext (fun n : nat => @lem520294 m n)). Qed.
Lemma lem520296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520297 (m : nat) : (term128 m) = term63.
Proof. exact (MK_COMB (@lem520296) (@lem520295 m)). Qed.
Lemma lem520299 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520300 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520299 nat t). Qed.
Lemma lem520301 : term63 = True.
Proof. exact (@lem520300 True). Qed.
Lemma lem520302 (m : nat) : (term128 m) = True.
Proof. exact (TRANS (@lem520297 m) (@lem520301)). Qed.
Lemma lem520303 : term129 = term61.
Proof. exact (fun_ext (fun m : nat => @lem520302 m)). Qed.
Lemma lem520304 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem520305 : term130 = term63.
Proof. exact (MK_COMB (@lem520304) (@lem520303)). Qed.
Lemma lem520307 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem520308 (t : Prop) : (term65 t) = t.
Proof. exact (@lem520307 nat t). Qed.
Lemma lem520309 : term63 = True.
Proof. exact (@lem520308 True). Qed.
Lemma lem520310 : term130 = True.
Proof. exact (TRANS (@lem520305) (@lem520309)). Qed.
Lemma lem520311 : term131 = (True /\ True).
Proof. exact (MK_COMB (@lem520264) (@lem520310)). Qed.
Lemma lem520313 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520314 : (True /\ True) = True.
Proof. exact (@lem520313 True). Qed.
Lemma lem520315 : term131 = True.
Proof. exact (TRANS (@lem520311) (@lem520314)). Qed.
Lemma lem520316 : term132 = (True /\ True).
Proof. exact (MK_COMB (@lem520214) (@lem520315)). Qed.
Lemma lem520318 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520319 : (True /\ True) = True.
Proof. exact (@lem520318 True). Qed.
Lemma lem520320 : term132 = True.
Proof. exact (TRANS (@lem520316) (@lem520319)). Qed.
Lemma lem520321 : term133 = (True /\ True).
Proof. exact (MK_COMB (@lem520159) (@lem520320)). Qed.
Lemma lem520323 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520324 : (True /\ True) = True.
Proof. exact (@lem520323 True). Qed.
Lemma lem520325 : term133 = True.
Proof. exact (TRANS (@lem520321) (@lem520324)). Qed.
Lemma lem520326 : term134 = (True /\ True).
Proof. exact (MK_COMB (@lem520109) (@lem520325)). Qed.
Lemma lem520328 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520329 : (True /\ True) = True.
Proof. exact (@lem520328 True). Qed.
Lemma lem520330 : term134 = True.
Proof. exact (TRANS (@lem520326) (@lem520329)). Qed.
Lemma lem520331 : term135 = (True /\ True).
Proof. exact (MK_COMB (@lem520078) (@lem520330)). Qed.
Lemma lem520333 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520334 : (True /\ True) = True.
Proof. exact (@lem520333 True). Qed.
Lemma lem520335 : term135 = True.
Proof. exact (TRANS (@lem520331) (@lem520334)). Qed.
Lemma lem520336 : term136 = (True /\ True).
Proof. exact (MK_COMB (@lem520041) (@lem520335)). Qed.
Lemma lem520338 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520339 : (True /\ True) = True.
Proof. exact (@lem520338 True). Qed.
Lemma lem520340 : term136 = True.
Proof. exact (TRANS (@lem520336) (@lem520339)). Qed.
Lemma lem520341 : term137 = (True /\ True).
Proof. exact (MK_COMB (@lem520005) (@lem520340)). Qed.
Lemma lem520343 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520344 : (True /\ True) = True.
Proof. exact (@lem520343 True). Qed.
Lemma lem520345 : term137 = True.
Proof. exact (TRANS (@lem520341) (@lem520344)). Qed.
Lemma lem520346 : term138 = (True /\ True).
Proof. exact (MK_COMB (@lem519969) (@lem520345)). Qed.
Lemma lem520348 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520349 : (True /\ True) = True.
Proof. exact (@lem520348 True). Qed.
Lemma lem520350 : term138 = True.
Proof. exact (TRANS (@lem520346) (@lem520349)). Qed.
Lemma lem520351 : term139 = (True /\ True).
Proof. exact (MK_COMB (@lem519945) (@lem520350)). Qed.
Lemma lem520353 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem520354 : (True /\ True) = True.
Proof. exact (@lem520353 True). Qed.
Lemma lem520355 : term139 = True.
Proof. exact (TRANS (@lem520351) (@lem520354)). Qed.
Lemma lem520356 : True = term139.
Proof. exact (SYM (@lem520355)). Qed.
