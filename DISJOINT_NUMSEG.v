Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_NUMSEG_term_abbrevs.
Require Import DISJOINT_spec.
Require Import INTER_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import NUMSEG_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482685_spec.
Require Import thm1482698_spec.
Require Import thm1483205_spec.
Require Import thm1483429_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318505_spec.
Require Import thm2318506_spec.
Require Import thm2318511_spec.
Require Import thm2318512_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841368_spec.
Require Import thm2841369_spec.
Require Import thm2841374_spec.
Require Import thm2841375_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5443757 (m : nat) : term0 m.
Proof. exact (@lem5443756 m). Qed.
Lemma lem5443758 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5443759 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5443758 m) (@lem5443757 m)). Qed.
Lemma lem5443760 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5443759 m n). Qed.
Lemma lem5443761 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5443762 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5443761 m n) (@lem5443760 m n)). Qed.
Lemma lem5443763 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem5443762 m n p). Qed.
Lemma lem5443764 (m : nat) (p : nat) (n : nat) : (term4 m n p) = (term5 m p n).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem5443765 (m : nat) (p : nat) (n : nat) : term5 m p n.
Proof. exact (EQ_MP (@lem5443764 m p n) (@lem5443763 m n p)). Qed.
Lemma lem5443766 (m : nat) (p : nat) (n : nat) (q : nat) : term6 m p n q.
Proof. exact (@lem5443765 m p n q). Qed.
Lemma lem5443767 (m : nat) (p : nat) (n : nat) (q : nat) : (term6 m p n q) = ((term7 m n p q) = (term8 m p n q)).
Proof. exact (eq_refl (term6 m p n q)). Qed.
Lemma lem5443769 (m : nat) : term9 m.
Proof. exact (@lem5376447 m). Qed.
Lemma lem5443770 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem5443771 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem5443770 m) (@lem5443769 m)). Qed.
Lemma lem5443772 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem5443771 m n). Qed.
Lemma lem5443773 (n : nat) (m : nat) : (term11 m n) = (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem5443775 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem5443776 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem5443777 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem5443776 A s) (@lem5443775 A s)). Qed.
Lemma lem5443778 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem5443777 A s t). Qed.
Lemma lem5443779 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem5443800 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem5443779 A s t) (@lem5443778 A s t)). Qed.
Lemma lem5443801 (s : nat -> Prop) (t : nat -> Prop) : (@DISJOINT nat s t) = ((@INTER nat s t) = (@EMPTY nat)).
Proof. exact (@lem5443800 nat s t). Qed.
Lemma lem5443802 (m : nat) (n : nat) (p : nat) (q : nat) : (term15 m n p q) = ((term7 m n p q) = (@EMPTY nat)).
Proof. exact (@lem5443801 (dotdot m n) (dotdot p q)). Qed.
Lemma lem5443806 (m : nat) (p : nat) (n : nat) (q : nat) : (term7 m n p q) = (term8 m p n q).
Proof. exact (EQ_MP (@lem5443767 m p n q) (@lem5443766 m p n q)). Qed.
Lemma lem5443807 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem5443808 (m : nat) (p : nat) (n : nat) (q : nat) : (term16 m n p q) = (term17 m p n q).
Proof. exact (MK_COMB (@lem5443807) (@lem5443806 m p n q)). Qed.
Lemma lem5443809 : (@EMPTY nat) = (@EMPTY nat).
Proof. exact (eq_refl (@EMPTY nat)). Qed.
Lemma lem5443810 (m : nat) (p : nat) (n : nat) (q : nat) : ((term7 m n p q) = (@EMPTY nat)) = ((term8 m p n q) = (@EMPTY nat)).
Proof. exact (MK_COMB (@lem5443808 m p n q) (@lem5443809)). Qed.
Lemma lem5443812 (n : nat) (m : nat) : ((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem5443773 n m) (@lem5443772 m n)). Qed.
Lemma lem5443813 (n : nat) (q : nat) (m : nat) (p : nat) : ((term8 m p n q) = (@EMPTY nat)) = (term18 n q m p).
Proof. exact (@lem5443812 (Nat.min n q) (Nat.max m p)). Qed.
Lemma lem5443814 (n : nat) (q : nat) (m : nat) (p : nat) : ((term7 m n p q) = (@EMPTY nat)) = (term18 n q m p).
Proof. exact (TRANS (@lem5443810 m p n q) (@lem5443813 n q m p)). Qed.
Lemma lem5443815 (n : nat) (q : nat) (m : nat) (p : nat) : (term15 m n p q) = (term18 n q m p).
Proof. exact (TRANS (@lem5443802 m n p q) (@lem5443814 n q m p)). Qed.
Lemma lem5443816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5443817 (n : nat) (q : nat) (m : nat) (p : nat) : (term19 m n p q) = (term20 n q m p).
Proof. exact (MK_COMB (@lem5443816) (@lem5443815 n q m p)). Qed.
Lemma lem5443824 (n : nat) (m : nat) (q : nat) (p : nat) : (term21 n m q p) = (term21 n m q p).
Proof. exact (eq_refl (term21 n m q p)). Qed.
Lemma lem5443825 (n : nat) (m : nat) (q : nat) (p : nat) : ((term15 m n p q) = (term21 n m q p)) = ((term18 n q m p) = (term21 n m q p)).
Proof. exact (MK_COMB (@lem5443817 n q m p) (@lem5443824 n m q p)). Qed.
Lemma lem5443828 (n : nat) (m : nat) (p : nat) : (term22 n m p) = (term23 n m p).
Proof. exact (fun_ext (fun q : nat => @lem5443825 n m q p)). Qed.
Lemma lem5443829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443830 (n : nat) (m : nat) (p : nat) : (term24 n m p) = (term25 n m p).
Proof. exact (MK_COMB (@lem5443829) (@lem5443828 n m p)). Qed.
Lemma lem5443835 (n : nat) (m : nat) : (term26 n m) = (term27 n m).
Proof. exact (fun_ext (fun p : nat => @lem5443830 n m p)). Qed.
Lemma lem5443836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443837 (n : nat) (m : nat) : (term28 n m) = (term29 n m).
Proof. exact (MK_COMB (@lem5443836) (@lem5443835 n m)). Qed.
Lemma lem5443842 (m : nat) : (term30 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem5443837 n m)). Qed.
Lemma lem5443843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443844 (m : nat) : (term32 m) = (term33 m).
Proof. exact (MK_COMB (@lem5443843) (@lem5443842 m)). Qed.
Lemma lem5443849 : term34 = term35.
Proof. exact (fun_ext (fun m : nat => @lem5443844 m)). Qed.
Lemma lem5443850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443851 : term36 = term37.
Proof. exact (MK_COMB (@lem5443850) (@lem5443849)). Qed.
Lemma lem5443856 : term37 = term36.
Proof. exact (SYM (@lem5443851)). Qed.
Lemma lem5443898 (n : nat) (m : nat) (q : nat) (p : nat) : ((term18 n q m p) = (term21 n m q p)) = ((term18 n q m p) = (term21 n m q p)).
Proof. exact (eq_refl ((term18 n q m p) = (term21 n m q p))). Qed.
Lemma lem5443899 (n : nat) (m : nat) (p : nat) : (term23 n m p) = (term23 n m p).
Proof. exact (fun_ext (fun q : nat => @lem5443898 n m q p)). Qed.
Lemma lem5443900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443901 (n : nat) (m : nat) (p : nat) : (term25 n m p) = (term25 n m p).
Proof. exact (MK_COMB (@lem5443900) (@lem5443899 n m p)). Qed.
Lemma lem5443902 (n : nat) (m : nat) : (term27 n m) = (term27 n m).
Proof. exact (fun_ext (fun p : nat => @lem5443901 n m p)). Qed.
Lemma lem5443903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443904 (n : nat) (m : nat) : (term29 n m) = (term29 n m).
Proof. exact (MK_COMB (@lem5443903) (@lem5443902 n m)). Qed.
Lemma lem5443905 (m : nat) : (term31 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem5443904 n m)). Qed.
Lemma lem5443906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443907 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem5443906) (@lem5443905 m)). Qed.
Lemma lem5443908 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem5443907 m)). Qed.
Lemma lem5443909 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443911 : term37 = term37.
Proof. exact (MK_COMB (@lem5443909) (@lem5443908)). Qed.
Lemma lem5443926 (n : nat) (m : nat) (q : nat) (p : nat) : (term38 n m q p) = (term39 n m q p).
Proof. exact (@lem17160 (Peano.lt n m) (Peano.lt q p)). Qed.
Lemma lem5443931 (q : nat) (m : nat) : (term40 q m) = (term40 q m).
Proof. exact (eq_refl (term40 q m)). Qed.
Lemma lem5443932 (n : nat) (m : nat) (q : nat) (p : nat) : (term41 n m q p) = (term42 n m q p).
Proof. exact (MK_COMB (@lem5443931 q m) (@lem5443926 n m q p)). Qed.
Lemma lem5443933 (n : nat) (m : nat) (q : nat) (p : nat) : (term43 n m q p) = (term41 n m q p).
Proof. exact (@lem17160 (Peano.lt q m) (term44 n m q p)). Qed.
Lemma lem5443934 (n : nat) (m : nat) (q : nat) (p : nat) : (term43 n m q p) = (term42 n m q p).
Proof. exact (TRANS (@lem5443933 n m q p) (@lem5443932 n m q p)). Qed.
Lemma lem5443939 (n : nat) (p : nat) : (term40 n p) = (term40 n p).
Proof. exact (eq_refl (term40 n p)). Qed.
Lemma lem5443940 (n : nat) (m : nat) (q : nat) (p : nat) : (term45 n m q p) = (term46 n m q p).
Proof. exact (MK_COMB (@lem5443939 n p) (@lem5443934 n m q p)). Qed.
Lemma lem5443941 (n : nat) (m : nat) (q : nat) (p : nat) : (term47 n m q p) = (term45 n m q p).
Proof. exact (@lem17160 (Peano.lt n p) (term48 n m q p)). Qed.
Lemma lem5443942 (n : nat) (m : nat) (q : nat) (p : nat) : (term47 n m q p) = (term46 n m q p).
Proof. exact (TRANS (@lem5443941 n m q p) (@lem5443940 n m q p)). Qed.
Lemma lem5443948 (n : nat) (m : nat) (q : nat) (p : nat) : (term49 n m q p) = (term49 n m q p).
Proof. exact (eq_refl (term49 n m q p)). Qed.
Lemma lem5443950 (n : nat) (q : nat) (m : nat) (p : nat) : (term50 n q m p) = (term50 n q m p).
Proof. exact (eq_refl (term50 n q m p)). Qed.
Lemma lem5443951 (n : nat) (m : nat) (q : nat) (p : nat) : (term51 n m q p) = (term52 n m q p).
Proof. exact (MK_COMB (@lem5443950 n q m p) (@lem5443942 n m q p)). Qed.
Lemma lem5443952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5443953 (n : nat) (m : nat) (q : nat) (p : nat) : (term53 n m q p) = (term54 n m q p).
Proof. exact (MK_COMB (@lem5443952) (@lem5443951 n m q p)). Qed.
Lemma lem5443954 (n : nat) (m : nat) (q : nat) (p : nat) : (term55 n m q p) = (term56 n m q p).
Proof. exact (MK_COMB (@lem5443953 n m q p) (@lem5443948 n m q p)). Qed.
Lemma lem5443955 (n : nat) (m : nat) (q : nat) (p : nat) : ((term18 n q m p) = (term21 n m q p)) = (term55 n m q p).
Proof. exact (@lem17784 (term18 n q m p) (term21 n m q p)). Qed.
Lemma lem5443956 (n : nat) (m : nat) (q : nat) (p : nat) : ((term18 n q m p) = (term21 n m q p)) = (term56 n m q p).
Proof. exact (TRANS (@lem5443955 n m q p) (@lem5443954 n m q p)). Qed.
Lemma lem5443957 (n : nat) (m : nat) (p : nat) : (term23 n m p) = (term57 n m p).
Proof. exact (fun_ext (fun q : nat => @lem5443956 n m q p)). Qed.
Lemma lem5443958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443959 (n : nat) (m : nat) (p : nat) : (term25 n m p) = (term58 n m p).
Proof. exact (MK_COMB (@lem5443958) (@lem5443957 n m p)). Qed.
Lemma lem5443960 (n : nat) (m : nat) : (term27 n m) = (term59 n m).
Proof. exact (fun_ext (fun p : nat => @lem5443959 n m p)). Qed.
Lemma lem5443961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443962 (n : nat) (m : nat) : (term29 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem5443961) (@lem5443960 n m)). Qed.
Lemma lem5443963 (m : nat) : (term31 m) = (term61 m).
Proof. exact (fun_ext (fun n : nat => @lem5443962 n m)). Qed.
Lemma lem5443964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443965 (m : nat) : (term33 m) = (term62 m).
Proof. exact (MK_COMB (@lem5443964) (@lem5443963 m)). Qed.
Lemma lem5443966 : term35 = term63.
Proof. exact (fun_ext (fun m : nat => @lem5443965 m)). Qed.
Lemma lem5443967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443968 : term37 = term64.
Proof. exact (MK_COMB (@lem5443967) (@lem5443966)). Qed.
Lemma lem5443969 : term37 = term64.
Proof. exact (TRANS (@lem5443911) (@lem5443968)). Qed.
Lemma lem5443970 (n : nat) (m : nat) (q : nat) (p : nat) : (term56 n m q p) = (term56 n m q p).
Proof. exact (eq_refl (term56 n m q p)). Qed.
Lemma lem5443971 (n : nat) (m : nat) (p : nat) : (term57 n m p) = (term57 n m p).
Proof. exact (fun_ext (fun q : nat => @lem5443970 n m q p)). Qed.
Lemma lem5443972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443973 (n : nat) (m : nat) (p : nat) : (term58 n m p) = (term58 n m p).
Proof. exact (MK_COMB (@lem5443972) (@lem5443971 n m p)). Qed.
Lemma lem5443974 (n : nat) (m : nat) : (term59 n m) = (term59 n m).
Proof. exact (fun_ext (fun p : nat => @lem5443973 n m p)). Qed.
Lemma lem5443975 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443976 (n : nat) (m : nat) : (term60 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem5443975) (@lem5443974 n m)). Qed.
Lemma lem5443977 (m : nat) : (term61 m) = (term61 m).
Proof. exact (fun_ext (fun n : nat => @lem5443976 n m)). Qed.
Lemma lem5443978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443979 (m : nat) : (term62 m) = (term62 m).
Proof. exact (MK_COMB (@lem5443978) (@lem5443977 m)). Qed.
Lemma lem5443980 : term63 = term63.
Proof. exact (fun_ext (fun m : nat => @lem5443979 m)). Qed.
Lemma lem5443981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5443982 : term64 = term64.
Proof. exact (MK_COMB (@lem5443981) (@lem5443980)). Qed.
Lemma lem5444023 : term37 = term64.
Proof. exact (TRANS (@lem5443969) (@lem5443982)). Qed.
Lemma lem5444110 (n : nat) (m : nat) (q : nat) (p : nat) : (term56 n m q p) = (term56 n m q p).
Proof. exact (eq_refl (term56 n m q p)). Qed.
Lemma lem5444111 (n : nat) (m : nat) (p : nat) : (term57 n m p) = (term57 n m p).
Proof. exact (fun_ext (fun q : nat => @lem5444110 n m q p)). Qed.
Lemma lem5444112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444113 (n : nat) (m : nat) (p : nat) : (term58 n m p) = (term58 n m p).
Proof. exact (MK_COMB (@lem5444112) (@lem5444111 n m p)). Qed.
Lemma lem5444114 (n : nat) (m : nat) : (term59 n m) = (term59 n m).
Proof. exact (fun_ext (fun p : nat => @lem5444113 n m p)). Qed.
Lemma lem5444115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444116 (n : nat) (m : nat) : (term60 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem5444115) (@lem5444114 n m)). Qed.
Lemma lem5444117 (m : nat) : (term61 m) = (term61 m).
Proof. exact (fun_ext (fun n : nat => @lem5444116 n m)). Qed.
Lemma lem5444118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444119 (m : nat) : (term62 m) = (term62 m).
Proof. exact (MK_COMB (@lem5444118) (@lem5444117 m)). Qed.
Lemma lem5444120 : term63 = term63.
Proof. exact (fun_ext (fun m : nat => @lem5444119 m)). Qed.
Lemma lem5444121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444122 : term64 = term64.
Proof. exact (MK_COMB (@lem5444121) (@lem5444120)). Qed.
Lemma lem5444125 : term37 = term64.
Proof. exact (TRANS (@lem5444023) (@lem5444122)). Qed.
Lemma lem5444127 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444128 (n : nat) (q : nat) (m : nat) (p : nat) : (term18 n q m p) = (term66 n q m p).
Proof. exact (@lem5444127 (Nat.min n q) (Nat.max m p)). Qed.
Lemma lem5444130 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (EQ_MP (@lem2841369 m n) (@lem2841368 m n)). Qed.
Lemma lem5444131 (n : nat) (q : nat) : (term67 n q) = (term68 n q).
Proof. exact (@lem5444130 n q). Qed.
Lemma lem5444132 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem5444133 (n : nat) (q : nat) : (term69 n q) = (term70 n q).
Proof. exact (MK_COMB (@lem5444132) (@lem5444131 n q)). Qed.
Lemma lem5444135 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem5444136 (m : nat) (p : nat) : (term71 m p) = (term72 m p).
Proof. exact (@lem5444135 m p). Qed.
Lemma lem5444137 (n : nat) (q : nat) (m : nat) (p : nat) : (term66 n q m p) = (term73 n q m p).
Proof. exact (MK_COMB (@lem5444133 n q) (@lem5444136 m p)). Qed.
Lemma lem5444138 (n : nat) (q : nat) (m : nat) (p : nat) : (term18 n q m p) = (term73 n q m p).
Proof. exact (TRANS (@lem5444128 n q m p) (@lem5444137 n q m p)). Qed.
Lemma lem5444139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444140 (n : nat) (q : nat) (m : nat) (p : nat) : (term50 n q m p) = (term74 n q m p).
Proof. exact (MK_COMB (@lem5444139) (@lem5444138 n q m p)). Qed.
Lemma lem5444142 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444143 (n : nat) (p : nat) : (Peano.lt n p) = (term65 n p).
Proof. exact (@lem5444142 n p). Qed.
Lemma lem5444144 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5444145 (n : nat) (p : nat) : (term75 n p) = (term76 n p).
Proof. exact (MK_COMB (@lem5444144) (@lem5444143 n p)). Qed.
Lemma lem5444146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444147 (n : nat) (p : nat) : (term40 n p) = (term77 n p).
Proof. exact (MK_COMB (@lem5444146) (@lem5444145 n p)). Qed.
Lemma lem5444149 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444150 (q : nat) (m : nat) : (Peano.lt q m) = (term65 q m).
Proof. exact (@lem5444149 q m). Qed.
Lemma lem5444151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5444152 (q : nat) (m : nat) : (term75 q m) = (term76 q m).
Proof. exact (MK_COMB (@lem5444151) (@lem5444150 q m)). Qed.
Lemma lem5444153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444154 (q : nat) (m : nat) : (term40 q m) = (term77 q m).
Proof. exact (MK_COMB (@lem5444153) (@lem5444152 q m)). Qed.
Lemma lem5444156 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444157 (n : nat) (m : nat) : (Peano.lt n m) = (term65 n m).
Proof. exact (@lem5444156 n m). Qed.
Lemma lem5444158 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5444159 (n : nat) (m : nat) : (term75 n m) = (term76 n m).
Proof. exact (MK_COMB (@lem5444158) (@lem5444157 n m)). Qed.
Lemma lem5444160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444161 (n : nat) (m : nat) : (term40 n m) = (term77 n m).
Proof. exact (MK_COMB (@lem5444160) (@lem5444159 n m)). Qed.
Lemma lem5444163 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444164 (q : nat) (p : nat) : (Peano.lt q p) = (term65 q p).
Proof. exact (@lem5444163 q p). Qed.
Lemma lem5444165 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5444166 (q : nat) (p : nat) : (term75 q p) = (term76 q p).
Proof. exact (MK_COMB (@lem5444165) (@lem5444164 q p)). Qed.
Lemma lem5444167 (n : nat) (m : nat) (q : nat) (p : nat) : (term39 n m q p) = (term78 n m q p).
Proof. exact (MK_COMB (@lem5444161 n m) (@lem5444166 q p)). Qed.
Lemma lem5444168 (n : nat) (m : nat) (q : nat) (p : nat) : (term42 n m q p) = (term79 n m q p).
Proof. exact (MK_COMB (@lem5444154 q m) (@lem5444167 n m q p)). Qed.
Lemma lem5444169 (n : nat) (m : nat) (q : nat) (p : nat) : (term46 n m q p) = (term80 n m q p).
Proof. exact (MK_COMB (@lem5444147 n p) (@lem5444168 n m q p)). Qed.
Lemma lem5444170 (n : nat) (m : nat) (q : nat) (p : nat) : (term52 n m q p) = (term81 n m q p).
Proof. exact (MK_COMB (@lem5444140 n q m p) (@lem5444169 n m q p)). Qed.
Lemma lem5444171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444172 (n : nat) (m : nat) (q : nat) (p : nat) : (term54 n m q p) = (term82 n m q p).
Proof. exact (MK_COMB (@lem5444171) (@lem5444170 n m q p)). Qed.
Lemma lem5444174 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444175 (n : nat) (q : nat) (m : nat) (p : nat) : (term18 n q m p) = (term66 n q m p).
Proof. exact (@lem5444174 (Nat.min n q) (Nat.max m p)). Qed.
Lemma lem5444177 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (EQ_MP (@lem2841369 m n) (@lem2841368 m n)). Qed.
Lemma lem5444178 (n : nat) (q : nat) : (term67 n q) = (term68 n q).
Proof. exact (@lem5444177 n q). Qed.
Lemma lem5444179 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem5444180 (n : nat) (q : nat) : (term69 n q) = (term70 n q).
Proof. exact (MK_COMB (@lem5444179) (@lem5444178 n q)). Qed.
Lemma lem5444182 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem5444183 (m : nat) (p : nat) : (term71 m p) = (term72 m p).
Proof. exact (@lem5444182 m p). Qed.
Lemma lem5444184 (n : nat) (q : nat) (m : nat) (p : nat) : (term66 n q m p) = (term73 n q m p).
Proof. exact (MK_COMB (@lem5444180 n q) (@lem5444183 m p)). Qed.
Lemma lem5444185 (n : nat) (q : nat) (m : nat) (p : nat) : (term18 n q m p) = (term73 n q m p).
Proof. exact (TRANS (@lem5444175 n q m p) (@lem5444184 n q m p)). Qed.
Lemma lem5444186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5444187 (n : nat) (q : nat) (m : nat) (p : nat) : (term83 n q m p) = (term84 n q m p).
Proof. exact (MK_COMB (@lem5444186) (@lem5444185 n q m p)). Qed.
Lemma lem5444188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444189 (n : nat) (q : nat) (m : nat) (p : nat) : (term85 n q m p) = (term86 n q m p).
Proof. exact (MK_COMB (@lem5444188) (@lem5444187 n q m p)). Qed.
Lemma lem5444191 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444192 (n : nat) (p : nat) : (Peano.lt n p) = (term65 n p).
Proof. exact (@lem5444191 n p). Qed.
Lemma lem5444193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444194 (n : nat) (p : nat) : (term87 n p) = (term88 n p).
Proof. exact (MK_COMB (@lem5444193) (@lem5444192 n p)). Qed.
Lemma lem5444196 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444197 (q : nat) (m : nat) : (Peano.lt q m) = (term65 q m).
Proof. exact (@lem5444196 q m). Qed.
Lemma lem5444198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444199 (q : nat) (m : nat) : (term87 q m) = (term88 q m).
Proof. exact (MK_COMB (@lem5444198) (@lem5444197 q m)). Qed.
Lemma lem5444201 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444202 (n : nat) (m : nat) : (Peano.lt n m) = (term65 n m).
Proof. exact (@lem5444201 n m). Qed.
Lemma lem5444203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444204 (n : nat) (m : nat) : (term87 n m) = (term88 n m).
Proof. exact (MK_COMB (@lem5444203) (@lem5444202 n m)). Qed.
Lemma lem5444206 (m : nat) (n : nat) : (Peano.lt m n) = (term65 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5444207 (q : nat) (p : nat) : (Peano.lt q p) = (term65 q p).
Proof. exact (@lem5444206 q p). Qed.
Lemma lem5444208 (n : nat) (m : nat) (q : nat) (p : nat) : (term44 n m q p) = (term89 n m q p).
Proof. exact (MK_COMB (@lem5444204 n m) (@lem5444207 q p)). Qed.
Lemma lem5444209 (n : nat) (m : nat) (q : nat) (p : nat) : (term48 n m q p) = (term90 n m q p).
Proof. exact (MK_COMB (@lem5444199 q m) (@lem5444208 n m q p)). Qed.
Lemma lem5444210 (n : nat) (m : nat) (q : nat) (p : nat) : (term21 n m q p) = (term91 n m q p).
Proof. exact (MK_COMB (@lem5444194 n p) (@lem5444209 n m q p)). Qed.
Lemma lem5444211 (n : nat) (m : nat) (q : nat) (p : nat) : (term49 n m q p) = (term92 n m q p).
Proof. exact (MK_COMB (@lem5444189 n q m p) (@lem5444210 n m q p)). Qed.
Lemma lem5444212 (n : nat) (m : nat) (q : nat) (p : nat) : (term56 n m q p) = (term93 n m q p).
Proof. exact (MK_COMB (@lem5444172 n m q p) (@lem5444211 n m q p)). Qed.
Lemma lem5444213 (n : nat) (m : nat) (p : nat) : (term57 n m p) = (term94 n m p).
Proof. exact (fun_ext (fun q : nat => @lem5444212 n m q p)). Qed.
Lemma lem5444214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444215 (n : nat) (m : nat) (p : nat) : (term58 n m p) = (term95 n m p).
Proof. exact (MK_COMB (@lem5444214) (@lem5444213 n m p)). Qed.
Lemma lem5444216 (n : nat) (m : nat) : (term59 n m) = (term96 n m).
Proof. exact (fun_ext (fun p : nat => @lem5444215 n m p)). Qed.
Lemma lem5444217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444218 (n : nat) (m : nat) : (term60 n m) = (term97 n m).
Proof. exact (MK_COMB (@lem5444217) (@lem5444216 n m)). Qed.
Lemma lem5444219 (m : nat) : (term61 m) = (term98 m).
Proof. exact (fun_ext (fun n : nat => @lem5444218 n m)). Qed.
Lemma lem5444220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444221 (m : nat) : (term62 m) = (term99 m).
Proof. exact (MK_COMB (@lem5444220) (@lem5444219 m)). Qed.
Lemma lem5444222 : term63 = term100.
Proof. exact (fun_ext (fun m : nat => @lem5444221 m)). Qed.
Lemma lem5444223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5444224 : term64 = term101.
Proof. exact (MK_COMB (@lem5444223) (@lem5444222)). Qed.
Lemma lem5444225 : term37 = term101.
Proof. exact (TRANS (@lem5444125) (@lem5444224)). Qed.
Lemma lem5444226 (m : nat) : term102 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5444227 (m : nat) : (term102 m) = (term103 m).
Proof. exact (eq_refl (term102 m)). Qed.
Lemma lem5444228 (m : nat) : term103 m.
Proof. exact (EQ_MP (@lem5444227 m) (@lem5444226 m)). Qed.
Lemma lem5444229 (n : nat) : term102 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5444230 (n : nat) : (term102 n) = (term103 n).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem5444231 (n : nat) : term103 n.
Proof. exact (EQ_MP (@lem5444230 n) (@lem5444229 n)). Qed.
Lemma lem5444232 (p : nat) : term102 p.
Proof. exact (@lem2307535 p). Qed.
Lemma lem5444233 (p : nat) : (term102 p) = (term103 p).
Proof. exact (eq_refl (term102 p)). Qed.
Lemma lem5444234 (p : nat) : term103 p.
Proof. exact (EQ_MP (@lem5444233 p) (@lem5444232 p)). Qed.
Lemma lem5444235 (q : nat) : term102 q.
Proof. exact (@lem2307535 q). Qed.
Lemma lem5444236 (q : nat) : (term102 q) = (term103 q).
Proof. exact (eq_refl (term102 q)). Qed.
Lemma lem5444237 (q : nat) : term103 q.
Proof. exact (EQ_MP (@lem5444236 q) (@lem5444235 q)). Qed.
Lemma lem5444238 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term104 _70519 _70518 _70521 _70520) = (term105 _70519 _70518 _70521 _70520).
Proof. exact (@lem2318604 (term105 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444277 (_70519 : int) (_70520 : int) : (term106 _70519 _70520) = (int_lt _70519 _70520).
Proof. exact (@lem16933 (int_lt _70519 _70520)). Qed.
Lemma lem5444280 (_70521 : int) (_70518 : int) : (term106 _70521 _70518) = (int_lt _70521 _70518).
Proof. exact (@lem16933 (int_lt _70521 _70518)). Qed.
Lemma lem5444283 (_70519 : int) (_70518 : int) : (term106 _70519 _70518) = (int_lt _70519 _70518).
Proof. exact (@lem16933 (int_lt _70519 _70518)). Qed.
Lemma lem5444286 (_70521 : int) (_70520 : int) : (term106 _70521 _70520) = (int_lt _70521 _70520).
Proof. exact (@lem16933 (int_lt _70521 _70520)). Qed.
Lemma lem5444287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444288 (_70519 : int) (_70518 : int) : (term107 _70519 _70518) = (term108 _70519 _70518).
Proof. exact (MK_COMB (@lem5444287) (@lem5444283 _70519 _70518)). Qed.
Lemma lem5444289 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term109 _70519 _70518 _70521 _70520) = (term110 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444288 _70519 _70518) (@lem5444286 _70521 _70520)). Qed.
Lemma lem5444290 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term111 _70519 _70518 _70521 _70520) = (term109 _70519 _70518 _70521 _70520).
Proof. exact (@lem17045 (term112 _70519 _70518) (term112 _70521 _70520)). Qed.
Lemma lem5444291 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term111 _70519 _70518 _70521 _70520) = (term110 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444290 _70519 _70518 _70521 _70520) (@lem5444289 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444293 (_70521 : int) (_70518 : int) : (term107 _70521 _70518) = (term108 _70521 _70518).
Proof. exact (MK_COMB (@lem5444292) (@lem5444280 _70521 _70518)). Qed.
Lemma lem5444294 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term113 _70519 _70518 _70521 _70520) = (term114 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444293 _70521 _70518) (@lem5444291 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444295 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term115 _70519 _70518 _70521 _70520) = (term113 _70519 _70518 _70521 _70520).
Proof. exact (@lem17045 (term112 _70521 _70518) (term116 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444296 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term115 _70519 _70518 _70521 _70520) = (term114 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444295 _70519 _70518 _70521 _70520) (@lem5444294 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444298 (_70519 : int) (_70520 : int) : (term107 _70519 _70520) = (term108 _70519 _70520).
Proof. exact (MK_COMB (@lem5444297) (@lem5444277 _70519 _70520)). Qed.
Lemma lem5444299 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term117 _70519 _70518 _70521 _70520) = (term118 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444298 _70519 _70520) (@lem5444296 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444300 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term119 _70519 _70518 _70521 _70520) = (term117 _70519 _70518 _70521 _70520).
Proof. exact (@lem17045 (term112 _70519 _70520) (term120 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444301 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term119 _70519 _70518 _70521 _70520) = (term118 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444300 _70519 _70518 _70521 _70520) (@lem5444299 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444303 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term121 _70519 _70521 _70518 _70520) = (term121 _70519 _70521 _70518 _70520).
Proof. exact (eq_refl (term121 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5444304 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term122 _70519 _70518 _70521 _70520) = (term123 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444303 _70519 _70521 _70518 _70520) (@lem5444301 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444305 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term124 _70519 _70518 _70521 _70520) = (term122 _70519 _70518 _70521 _70520).
Proof. exact (@lem17160 (term125 _70519 _70521 _70518 _70520) (term126 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444306 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term124 _70519 _70518 _70521 _70520) = (term123 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444305 _70519 _70518 _70521 _70520) (@lem5444304 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444309 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term127 _70519 _70521 _70518 _70520) = (term125 _70519 _70521 _70518 _70520).
Proof. exact (@lem16933 (term125 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5444318 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term128 _70519 _70518 _70521 _70520) = (term116 _70519 _70518 _70521 _70520).
Proof. exact (@lem17160 (int_lt _70519 _70518) (int_lt _70521 _70520)). Qed.
Lemma lem5444320 (_70521 : int) (_70518 : int) : (term129 _70521 _70518) = (term129 _70521 _70518).
Proof. exact (eq_refl (term129 _70521 _70518)). Qed.
Lemma lem5444321 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term130 _70519 _70518 _70521 _70520) = (term120 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444320 _70521 _70518) (@lem5444318 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444322 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term131 _70519 _70518 _70521 _70520) = (term130 _70519 _70518 _70521 _70520).
Proof. exact (@lem17160 (int_lt _70521 _70518) (term110 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444323 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term131 _70519 _70518 _70521 _70520) = (term120 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444322 _70519 _70518 _70521 _70520) (@lem5444321 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444325 (_70519 : int) (_70520 : int) : (term129 _70519 _70520) = (term129 _70519 _70520).
Proof. exact (eq_refl (term129 _70519 _70520)). Qed.
Lemma lem5444326 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term132 _70519 _70518 _70521 _70520) = (term126 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444325 _70519 _70520) (@lem5444323 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444327 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term133 _70519 _70518 _70521 _70520) = (term132 _70519 _70518 _70521 _70520).
Proof. exact (@lem17160 (int_lt _70519 _70520) (term114 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444328 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term133 _70519 _70518 _70521 _70520) = (term126 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444327 _70519 _70518 _70521 _70520) (@lem5444326 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444330 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term134 _70519 _70521 _70518 _70520) = (term135 _70519 _70521 _70518 _70520).
Proof. exact (MK_COMB (@lem5444329) (@lem5444309 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5444331 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term136 _70519 _70518 _70521 _70520) = (term137 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444330 _70519 _70521 _70518 _70520) (@lem5444328 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444332 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term138 _70519 _70518 _70521 _70520) = (term136 _70519 _70518 _70521 _70520).
Proof. exact (@lem17160 (term139 _70519 _70521 _70518 _70520) (term118 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444333 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term138 _70519 _70518 _70521 _70520) = (term137 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444332 _70519 _70518 _70521 _70520) (@lem5444331 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444335 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term140 _70519 _70518 _70521 _70520) = (term141 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444334) (@lem5444306 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444336 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term142 _70519 _70518 _70521 _70520) = (term143 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444335 _70519 _70518 _70521 _70520) (@lem5444333 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444337 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term144 _70519 _70518 _70521 _70520) = (term142 _70519 _70518 _70521 _70520).
Proof. exact (@lem17045 (term145 _70519 _70518 _70521 _70520) (term146 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444338 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term144 _70519 _70518 _70521 _70520) = (term143 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444337 _70519 _70518 _70521 _70520) (@lem5444336 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444340 (_70521 : int) : (term147 _70521) = (term147 _70521).
Proof. exact (eq_refl (term147 _70521)). Qed.
Lemma lem5444341 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term148 _70519 _70518 _70521 _70520) = (term149 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444340 _70521) (@lem5444338 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444342 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term150 _70519 _70518 _70521 _70520) = (term148 _70519 _70518 _70521 _70520).
Proof. exact (@lem17362 (term151 _70521) (term152 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444343 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term150 _70519 _70518 _70521 _70520) = (term149 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444342 _70519 _70518 _70521 _70520) (@lem5444341 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444345 (_70520 : int) : (term147 _70520) = (term147 _70520).
Proof. exact (eq_refl (term147 _70520)). Qed.
Lemma lem5444346 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term153 _70519 _70518 _70521 _70520) = (term154 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444345 _70520) (@lem5444343 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444347 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term155 _70519 _70518 _70521 _70520) = (term153 _70519 _70518 _70521 _70520).
Proof. exact (@lem17362 (term151 _70520) (term156 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444348 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term155 _70519 _70518 _70521 _70520) = (term154 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444347 _70519 _70518 _70521 _70520) (@lem5444346 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444350 (_70519 : int) : (term147 _70519) = (term147 _70519).
Proof. exact (eq_refl (term147 _70519)). Qed.
Lemma lem5444351 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term157 _70519 _70518 _70521 _70520) = (term158 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444350 _70519) (@lem5444348 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444352 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term159 _70519 _70518 _70521 _70520) = (term157 _70519 _70518 _70521 _70520).
Proof. exact (@lem17362 (term151 _70519) (term160 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444353 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term159 _70519 _70518 _70521 _70520) = (term158 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444352 _70519 _70518 _70521 _70520) (@lem5444351 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444355 (_70518 : int) : (term147 _70518) = (term147 _70518).
Proof. exact (eq_refl (term147 _70518)). Qed.
Lemma lem5444356 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term161 _70519 _70518 _70521 _70520) = (term162 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444355 _70518) (@lem5444353 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444357 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term163 _70519 _70518 _70521 _70520) = (term161 _70519 _70518 _70521 _70520).
Proof. exact (@lem17362 (term151 _70518) (term164 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444423 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term163 _70519 _70518 _70521 _70520) = (term162 _70519 _70518 _70521 _70520).
Proof. exact (TRANS (@lem5444357 _70519 _70518 _70521 _70520) (@lem5444356 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444426 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444427 (_70518 : int) : (term151 _70518) = (term166 _70518).
Proof. exact (@lem5444426 term167 _70518). Qed.
Lemma lem5444429 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444430 : term169 = term170.
Proof. exact (@lem5444429 (NUMERAL 0)). Qed.
Lemma lem5444431 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444432 : term171 = term172.
Proof. exact (MK_COMB (@lem5444431) (@lem5444430)). Qed.
Lemma lem5444433 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5444434 (_70518 : int) : (term166 _70518) = (term173 _70518).
Proof. exact (MK_COMB (@lem5444432) (@lem5444433 _70518)). Qed.
Lemma lem5444436 (_70518 : int) : (term151 _70518) = (term173 _70518).
Proof. exact (TRANS (@lem5444427 _70518) (@lem5444434 _70518)). Qed.
Lemma lem5444439 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444440 (_70519 : int) : (term151 _70519) = (term166 _70519).
Proof. exact (@lem5444439 term167 _70519). Qed.
Lemma lem5444442 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444443 : term169 = term170.
Proof. exact (@lem5444442 (NUMERAL 0)). Qed.
Lemma lem5444444 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444445 : term171 = term172.
Proof. exact (MK_COMB (@lem5444444) (@lem5444443)). Qed.
Lemma lem5444446 (_70519 : int) : (real_of_int _70519) = (real_of_int _70519).
Proof. exact (eq_refl (real_of_int _70519)). Qed.
Lemma lem5444447 (_70519 : int) : (term166 _70519) = (term173 _70519).
Proof. exact (MK_COMB (@lem5444445) (@lem5444446 _70519)). Qed.
Lemma lem5444449 (_70519 : int) : (term151 _70519) = (term173 _70519).
Proof. exact (TRANS (@lem5444440 _70519) (@lem5444447 _70519)). Qed.
Lemma lem5444452 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444453 (_70520 : int) : (term151 _70520) = (term166 _70520).
Proof. exact (@lem5444452 term167 _70520). Qed.
Lemma lem5444455 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444456 : term169 = term170.
Proof. exact (@lem5444455 (NUMERAL 0)). Qed.
Lemma lem5444457 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444458 : term171 = term172.
Proof. exact (MK_COMB (@lem5444457) (@lem5444456)). Qed.
Lemma lem5444459 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5444460 (_70520 : int) : (term166 _70520) = (term173 _70520).
Proof. exact (MK_COMB (@lem5444458) (@lem5444459 _70520)). Qed.
Lemma lem5444462 (_70520 : int) : (term151 _70520) = (term173 _70520).
Proof. exact (TRANS (@lem5444453 _70520) (@lem5444460 _70520)). Qed.
Lemma lem5444465 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444466 (_70521 : int) : (term151 _70521) = (term166 _70521).
Proof. exact (@lem5444465 term167 _70521). Qed.
Lemma lem5444468 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444469 : term169 = term170.
Proof. exact (@lem5444468 (NUMERAL 0)). Qed.
Lemma lem5444470 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444471 : term171 = term172.
Proof. exact (MK_COMB (@lem5444470) (@lem5444469)). Qed.
Lemma lem5444472 (_70521 : int) : (real_of_int _70521) = (real_of_int _70521).
Proof. exact (eq_refl (real_of_int _70521)). Qed.
Lemma lem5444473 (_70521 : int) : (term166 _70521) = (term173 _70521).
Proof. exact (MK_COMB (@lem5444471) (@lem5444472 _70521)). Qed.
Lemma lem5444475 (_70521 : int) : (term151 _70521) = (term173 _70521).
Proof. exact (TRANS (@lem5444466 _70521) (@lem5444473 _70521)). Qed.
Lemma lem5444477 (y : int) (x : int) : (term112 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5444478 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term139 _70519 _70521 _70518 _70520) = (term174 _70518 _70520 _70519 _70521).
Proof. exact (@lem5444477 (int_max _70518 _70520) (int_min _70519 _70521)). Qed.
Lemma lem5444480 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444481 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term174 _70518 _70520 _70519 _70521) = (term175 _70518 _70520 _70519 _70521).
Proof. exact (@lem5444480 (int_max _70518 _70520) (int_min _70519 _70521)). Qed.
Lemma lem5444483 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem5444484 (_70518 : int) (_70520 : int) : (term176 _70518 _70520) = (term177 _70518 _70520).
Proof. exact (@lem5444483 _70518 _70520). Qed.
Lemma lem5444485 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444486 (_70518 : int) (_70520 : int) : (term178 _70518 _70520) = (term179 _70518 _70520).
Proof. exact (MK_COMB (@lem5444485) (@lem5444484 _70518 _70520)). Qed.
Lemma lem5444488 (x : int) (y : int) : (term180 x y) = (term181 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem5444489 (_70519 : int) (_70521 : int) : (term180 _70519 _70521) = (term181 _70519 _70521).
Proof. exact (@lem5444488 _70519 _70521). Qed.
Lemma lem5444490 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term175 _70518 _70520 _70519 _70521) = (term182 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5444486 _70518 _70520) (@lem5444489 _70519 _70521)). Qed.
Lemma lem5444491 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term174 _70518 _70520 _70519 _70521) = (term182 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5444481 _70518 _70520 _70519 _70521) (@lem5444490 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5444492 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term139 _70519 _70521 _70518 _70520) = (term182 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5444478 _70518 _70520 _70519 _70521) (@lem5444491 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5444494 (x : int) (y : int) : (int_lt x y) = (term183 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5444495 (_70519 : int) (_70520 : int) : (int_lt _70519 _70520) = (term183 _70519 _70520).
Proof. exact (@lem5444494 _70519 _70520). Qed.
Lemma lem5444497 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444498 (_70519 : int) (_70520 : int) : (term183 _70519 _70520) = (term184 _70519 _70520).
Proof. exact (@lem5444497 (term185 _70519) _70520). Qed.
Lemma lem5444500 (x : int) (y : int) : (term186 x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5444501 (_70519 : int) : (term188 _70519) = (term189 _70519).
Proof. exact (@lem5444500 _70519 term190). Qed.
Lemma lem5444503 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444504 : term191 = term192.
Proof. exact (@lem5444503 term193). Qed.
Lemma lem5444505 (_70519 : int) : (term194 _70519) = (term194 _70519).
Proof. exact (eq_refl (term194 _70519)). Qed.
Lemma lem5444506 (_70519 : int) : (term189 _70519) = (term195 _70519).
Proof. exact (MK_COMB (@lem5444505 _70519) (@lem5444504)). Qed.
Lemma lem5444507 (_70519 : int) : (term188 _70519) = (term195 _70519).
Proof. exact (TRANS (@lem5444501 _70519) (@lem5444506 _70519)). Qed.
Lemma lem5444508 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444509 (_70519 : int) : (term196 _70519) = (term197 _70519).
Proof. exact (MK_COMB (@lem5444508) (@lem5444507 _70519)). Qed.
Lemma lem5444510 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5444511 (_70519 : int) (_70520 : int) : (term184 _70519 _70520) = (term198 _70519 _70520).
Proof. exact (MK_COMB (@lem5444509 _70519) (@lem5444510 _70520)). Qed.
Lemma lem5444512 (_70519 : int) (_70520 : int) : (term183 _70519 _70520) = (term198 _70519 _70520).
Proof. exact (TRANS (@lem5444498 _70519 _70520) (@lem5444511 _70519 _70520)). Qed.
Lemma lem5444513 (_70519 : int) (_70520 : int) : (int_lt _70519 _70520) = (term198 _70519 _70520).
Proof. exact (TRANS (@lem5444495 _70519 _70520) (@lem5444512 _70519 _70520)). Qed.
Lemma lem5444515 (x : int) (y : int) : (int_lt x y) = (term183 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5444516 (_70521 : int) (_70518 : int) : (int_lt _70521 _70518) = (term183 _70521 _70518).
Proof. exact (@lem5444515 _70521 _70518). Qed.
Lemma lem5444518 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444519 (_70521 : int) (_70518 : int) : (term183 _70521 _70518) = (term184 _70521 _70518).
Proof. exact (@lem5444518 (term185 _70521) _70518). Qed.
Lemma lem5444521 (x : int) (y : int) : (term186 x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5444522 (_70521 : int) : (term188 _70521) = (term189 _70521).
Proof. exact (@lem5444521 _70521 term190). Qed.
Lemma lem5444524 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444525 : term191 = term192.
Proof. exact (@lem5444524 term193). Qed.
Lemma lem5444526 (_70521 : int) : (term194 _70521) = (term194 _70521).
Proof. exact (eq_refl (term194 _70521)). Qed.
Lemma lem5444527 (_70521 : int) : (term189 _70521) = (term195 _70521).
Proof. exact (MK_COMB (@lem5444526 _70521) (@lem5444525)). Qed.
Lemma lem5444528 (_70521 : int) : (term188 _70521) = (term195 _70521).
Proof. exact (TRANS (@lem5444522 _70521) (@lem5444527 _70521)). Qed.
Lemma lem5444529 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444530 (_70521 : int) : (term196 _70521) = (term197 _70521).
Proof. exact (MK_COMB (@lem5444529) (@lem5444528 _70521)). Qed.
Lemma lem5444531 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5444532 (_70521 : int) (_70518 : int) : (term184 _70521 _70518) = (term198 _70521 _70518).
Proof. exact (MK_COMB (@lem5444530 _70521) (@lem5444531 _70518)). Qed.
Lemma lem5444533 (_70521 : int) (_70518 : int) : (term183 _70521 _70518) = (term198 _70521 _70518).
Proof. exact (TRANS (@lem5444519 _70521 _70518) (@lem5444532 _70521 _70518)). Qed.
Lemma lem5444534 (_70521 : int) (_70518 : int) : (int_lt _70521 _70518) = (term198 _70521 _70518).
Proof. exact (TRANS (@lem5444516 _70521 _70518) (@lem5444533 _70521 _70518)). Qed.
Lemma lem5444536 (x : int) (y : int) : (int_lt x y) = (term183 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5444537 (_70519 : int) (_70518 : int) : (int_lt _70519 _70518) = (term183 _70519 _70518).
Proof. exact (@lem5444536 _70519 _70518). Qed.
Lemma lem5444539 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444540 (_70519 : int) (_70518 : int) : (term183 _70519 _70518) = (term184 _70519 _70518).
Proof. exact (@lem5444539 (term185 _70519) _70518). Qed.
Lemma lem5444542 (x : int) (y : int) : (term186 x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5444543 (_70519 : int) : (term188 _70519) = (term189 _70519).
Proof. exact (@lem5444542 _70519 term190). Qed.
Lemma lem5444545 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444546 : term191 = term192.
Proof. exact (@lem5444545 term193). Qed.
Lemma lem5444547 (_70519 : int) : (term194 _70519) = (term194 _70519).
Proof. exact (eq_refl (term194 _70519)). Qed.
Lemma lem5444548 (_70519 : int) : (term189 _70519) = (term195 _70519).
Proof. exact (MK_COMB (@lem5444547 _70519) (@lem5444546)). Qed.
Lemma lem5444549 (_70519 : int) : (term188 _70519) = (term195 _70519).
Proof. exact (TRANS (@lem5444543 _70519) (@lem5444548 _70519)). Qed.
Lemma lem5444550 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444551 (_70519 : int) : (term196 _70519) = (term197 _70519).
Proof. exact (MK_COMB (@lem5444550) (@lem5444549 _70519)). Qed.
Lemma lem5444552 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5444553 (_70519 : int) (_70518 : int) : (term184 _70519 _70518) = (term198 _70519 _70518).
Proof. exact (MK_COMB (@lem5444551 _70519) (@lem5444552 _70518)). Qed.
Lemma lem5444554 (_70519 : int) (_70518 : int) : (term183 _70519 _70518) = (term198 _70519 _70518).
Proof. exact (TRANS (@lem5444540 _70519 _70518) (@lem5444553 _70519 _70518)). Qed.
Lemma lem5444555 (_70519 : int) (_70518 : int) : (int_lt _70519 _70518) = (term198 _70519 _70518).
Proof. exact (TRANS (@lem5444537 _70519 _70518) (@lem5444554 _70519 _70518)). Qed.
Lemma lem5444557 (x : int) (y : int) : (int_lt x y) = (term183 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5444558 (_70521 : int) (_70520 : int) : (int_lt _70521 _70520) = (term183 _70521 _70520).
Proof. exact (@lem5444557 _70521 _70520). Qed.
Lemma lem5444560 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444561 (_70521 : int) (_70520 : int) : (term183 _70521 _70520) = (term184 _70521 _70520).
Proof. exact (@lem5444560 (term185 _70521) _70520). Qed.
Lemma lem5444563 (x : int) (y : int) : (term186 x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5444564 (_70521 : int) : (term188 _70521) = (term189 _70521).
Proof. exact (@lem5444563 _70521 term190). Qed.
Lemma lem5444566 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444567 : term191 = term192.
Proof. exact (@lem5444566 term193). Qed.
Lemma lem5444568 (_70521 : int) : (term194 _70521) = (term194 _70521).
Proof. exact (eq_refl (term194 _70521)). Qed.
Lemma lem5444569 (_70521 : int) : (term189 _70521) = (term195 _70521).
Proof. exact (MK_COMB (@lem5444568 _70521) (@lem5444567)). Qed.
Lemma lem5444570 (_70521 : int) : (term188 _70521) = (term195 _70521).
Proof. exact (TRANS (@lem5444564 _70521) (@lem5444569 _70521)). Qed.
Lemma lem5444571 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444572 (_70521 : int) : (term196 _70521) = (term197 _70521).
Proof. exact (MK_COMB (@lem5444571) (@lem5444570 _70521)). Qed.
Lemma lem5444573 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5444574 (_70521 : int) (_70520 : int) : (term184 _70521 _70520) = (term198 _70521 _70520).
Proof. exact (MK_COMB (@lem5444572 _70521) (@lem5444573 _70520)). Qed.
Lemma lem5444575 (_70521 : int) (_70520 : int) : (term183 _70521 _70520) = (term198 _70521 _70520).
Proof. exact (TRANS (@lem5444561 _70521 _70520) (@lem5444574 _70521 _70520)). Qed.
Lemma lem5444576 (_70521 : int) (_70520 : int) : (int_lt _70521 _70520) = (term198 _70521 _70520).
Proof. exact (TRANS (@lem5444558 _70521 _70520) (@lem5444575 _70521 _70520)). Qed.
Lemma lem5444577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444578 (_70519 : int) (_70518 : int) : (term108 _70519 _70518) = (term199 _70519 _70518).
Proof. exact (MK_COMB (@lem5444577) (@lem5444555 _70519 _70518)). Qed.
Lemma lem5444579 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term110 _70519 _70518 _70521 _70520) = (term200 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444578 _70519 _70518) (@lem5444576 _70521 _70520)). Qed.
Lemma lem5444580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444581 (_70521 : int) (_70518 : int) : (term108 _70521 _70518) = (term199 _70521 _70518).
Proof. exact (MK_COMB (@lem5444580) (@lem5444534 _70521 _70518)). Qed.
Lemma lem5444582 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term114 _70519 _70518 _70521 _70520) = (term201 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444581 _70521 _70518) (@lem5444579 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444584 (_70519 : int) (_70520 : int) : (term108 _70519 _70520) = (term199 _70519 _70520).
Proof. exact (MK_COMB (@lem5444583) (@lem5444513 _70519 _70520)). Qed.
Lemma lem5444585 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term118 _70519 _70518 _70521 _70520) = (term202 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444584 _70519 _70520) (@lem5444582 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444587 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term121 _70519 _70521 _70518 _70520) = (term203 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5444586) (@lem5444492 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5444588 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term123 _70519 _70518 _70521 _70520) = (term204 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444587 _70518 _70520 _70519 _70521) (@lem5444585 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444590 (x : int) (y : int) : (int_lt x y) = (term183 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5444591 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term125 _70519 _70521 _70518 _70520) = (term205 _70519 _70521 _70518 _70520).
Proof. exact (@lem5444590 (int_min _70519 _70521) (int_max _70518 _70520)). Qed.
Lemma lem5444593 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444594 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term205 _70519 _70521 _70518 _70520) = (term206 _70519 _70521 _70518 _70520).
Proof. exact (@lem5444593 (term207 _70519 _70521) (int_max _70518 _70520)). Qed.
Lemma lem5444596 (x : int) (y : int) : (term186 x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5444597 (_70519 : int) (_70521 : int) : (term208 _70519 _70521) = (term209 _70519 _70521).
Proof. exact (@lem5444596 (int_min _70519 _70521) term190). Qed.
Lemma lem5444599 (x : int) (y : int) : (term180 x y) = (term181 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem5444600 (_70519 : int) (_70521 : int) : (term180 _70519 _70521) = (term181 _70519 _70521).
Proof. exact (@lem5444599 _70519 _70521). Qed.
Lemma lem5444601 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5444602 (_70519 : int) (_70521 : int) : (term210 _70519 _70521) = (term211 _70519 _70521).
Proof. exact (MK_COMB (@lem5444601) (@lem5444600 _70519 _70521)). Qed.
Lemma lem5444604 (n : nat) : (term168 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5444605 : term191 = term192.
Proof. exact (@lem5444604 term193). Qed.
Lemma lem5444606 (_70519 : int) (_70521 : int) : (term209 _70519 _70521) = (term212 _70519 _70521).
Proof. exact (MK_COMB (@lem5444602 _70519 _70521) (@lem5444605)). Qed.
Lemma lem5444607 (_70519 : int) (_70521 : int) : (term208 _70519 _70521) = (term212 _70519 _70521).
Proof. exact (TRANS (@lem5444597 _70519 _70521) (@lem5444606 _70519 _70521)). Qed.
Lemma lem5444608 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5444609 (_70519 : int) (_70521 : int) : (term213 _70519 _70521) = (term214 _70519 _70521).
Proof. exact (MK_COMB (@lem5444608) (@lem5444607 _70519 _70521)). Qed.
Lemma lem5444611 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem5444612 (_70518 : int) (_70520 : int) : (term176 _70518 _70520) = (term177 _70518 _70520).
Proof. exact (@lem5444611 _70518 _70520). Qed.
Lemma lem5444613 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term206 _70519 _70521 _70518 _70520) = (term215 _70519 _70521 _70518 _70520).
Proof. exact (MK_COMB (@lem5444609 _70519 _70521) (@lem5444612 _70518 _70520)). Qed.
Lemma lem5444614 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term205 _70519 _70521 _70518 _70520) = (term215 _70519 _70521 _70518 _70520).
Proof. exact (TRANS (@lem5444594 _70519 _70521 _70518 _70520) (@lem5444613 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5444615 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term125 _70519 _70521 _70518 _70520) = (term215 _70519 _70521 _70518 _70520).
Proof. exact (TRANS (@lem5444591 _70519 _70521 _70518 _70520) (@lem5444614 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5444617 (y : int) (x : int) : (term112 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5444618 (_70520 : int) (_70519 : int) : (term112 _70519 _70520) = (int_le _70520 _70519).
Proof. exact (@lem5444617 _70520 _70519). Qed.
Lemma lem5444620 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444621 (_70520 : int) (_70519 : int) : (int_le _70520 _70519) = (term165 _70520 _70519).
Proof. exact (@lem5444620 _70520 _70519). Qed.
Lemma lem5444622 (_70520 : int) (_70519 : int) : (term112 _70519 _70520) = (term165 _70520 _70519).
Proof. exact (TRANS (@lem5444618 _70520 _70519) (@lem5444621 _70520 _70519)). Qed.
Lemma lem5444624 (y : int) (x : int) : (term112 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5444625 (_70518 : int) (_70521 : int) : (term112 _70521 _70518) = (int_le _70518 _70521).
Proof. exact (@lem5444624 _70518 _70521). Qed.
Lemma lem5444627 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444628 (_70518 : int) (_70521 : int) : (int_le _70518 _70521) = (term165 _70518 _70521).
Proof. exact (@lem5444627 _70518 _70521). Qed.
Lemma lem5444629 (_70518 : int) (_70521 : int) : (term112 _70521 _70518) = (term165 _70518 _70521).
Proof. exact (TRANS (@lem5444625 _70518 _70521) (@lem5444628 _70518 _70521)). Qed.
Lemma lem5444631 (y : int) (x : int) : (term112 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5444632 (_70518 : int) (_70519 : int) : (term112 _70519 _70518) = (int_le _70518 _70519).
Proof. exact (@lem5444631 _70518 _70519). Qed.
Lemma lem5444634 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444635 (_70518 : int) (_70519 : int) : (int_le _70518 _70519) = (term165 _70518 _70519).
Proof. exact (@lem5444634 _70518 _70519). Qed.
Lemma lem5444636 (_70518 : int) (_70519 : int) : (term112 _70519 _70518) = (term165 _70518 _70519).
Proof. exact (TRANS (@lem5444632 _70518 _70519) (@lem5444635 _70518 _70519)). Qed.
Lemma lem5444638 (y : int) (x : int) : (term112 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5444639 (_70520 : int) (_70521 : int) : (term112 _70521 _70520) = (int_le _70520 _70521).
Proof. exact (@lem5444638 _70520 _70521). Qed.
Lemma lem5444641 (x : int) (y : int) : (int_le x y) = (term165 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5444642 (_70520 : int) (_70521 : int) : (int_le _70520 _70521) = (term165 _70520 _70521).
Proof. exact (@lem5444641 _70520 _70521). Qed.
Lemma lem5444643 (_70520 : int) (_70521 : int) : (term112 _70521 _70520) = (term165 _70520 _70521).
Proof. exact (TRANS (@lem5444639 _70520 _70521) (@lem5444642 _70520 _70521)). Qed.
Lemma lem5444644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444645 (_70518 : int) (_70519 : int) : (term129 _70519 _70518) = (term216 _70518 _70519).
Proof. exact (MK_COMB (@lem5444644) (@lem5444636 _70518 _70519)). Qed.
Lemma lem5444646 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term116 _70519 _70518 _70521 _70520) = (term217 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444645 _70518 _70519) (@lem5444643 _70520 _70521)). Qed.
Lemma lem5444647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444648 (_70518 : int) (_70521 : int) : (term129 _70521 _70518) = (term216 _70518 _70521).
Proof. exact (MK_COMB (@lem5444647) (@lem5444629 _70518 _70521)). Qed.
Lemma lem5444649 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term120 _70519 _70518 _70521 _70520) = (term218 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444648 _70518 _70521) (@lem5444646 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444651 (_70520 : int) (_70519 : int) : (term129 _70519 _70520) = (term216 _70520 _70519).
Proof. exact (MK_COMB (@lem5444650) (@lem5444622 _70520 _70519)). Qed.
Lemma lem5444652 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term126 _70519 _70518 _70521 _70520) = (term219 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444651 _70520 _70519) (@lem5444649 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444654 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term135 _70519 _70521 _70518 _70520) = (term220 _70519 _70521 _70518 _70520).
Proof. exact (MK_COMB (@lem5444653) (@lem5444615 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5444655 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term137 _70519 _70518 _70521 _70520) = (term221 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444654 _70519 _70521 _70518 _70520) (@lem5444652 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5444657 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term141 _70519 _70518 _70521 _70520) = (term222 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5444656) (@lem5444588 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5444658 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term143 _70519 _70518 _70521 _70520) = (term223 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444657 _70519 _70518 _70521 _70520) (@lem5444655 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444660 (_70521 : int) : (term147 _70521) = (term224 _70521).
Proof. exact (MK_COMB (@lem5444659) (@lem5444475 _70521)). Qed.
Lemma lem5444661 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term149 _70519 _70518 _70521 _70520) = (term225 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444660 _70521) (@lem5444658 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444663 (_70520 : int) : (term147 _70520) = (term224 _70520).
Proof. exact (MK_COMB (@lem5444662) (@lem5444462 _70520)). Qed.
Lemma lem5444664 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term154 _70519 _70518 _70521 _70520) = (term226 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444663 _70520) (@lem5444661 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444666 (_70519 : int) : (term147 _70519) = (term224 _70519).
Proof. exact (MK_COMB (@lem5444665) (@lem5444449 _70519)). Qed.
Lemma lem5444667 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term158 _70519 _70518 _70521 _70520) = (term227 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444666 _70519) (@lem5444664 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5444669 (_70518 : int) : (term147 _70518) = (term224 _70518).
Proof. exact (MK_COMB (@lem5444668) (@lem5444436 _70518)). Qed.
Lemma lem5444670 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term162 _70519 _70518 _70521 _70520) = (term228 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5444669 _70518) (@lem5444667 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444671 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term163 _70519 _70518 _70521 _70520) = (term228 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5444423 _70519 _70518 _70521 _70520) (@lem5444670 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444675 (t : Prop) : (term229 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5444811 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term230 _70518 _70519 _70520 _70521) = (term228 _70518 _70519 _70520 _70521).
Proof. exact (@lem5444675 (term228 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5444812 (_70518 : int) : (term173 _70518) = (term231 _70518).
Proof. exact (@lem1988287 (real_of_int _70518) term170). Qed.
Lemma lem5444818 (_70518 : int) : (term232 _70518) = (term233 _70518).
Proof. exact (@lem1982792 (real_of_int _70518) term170). Qed.
Lemma lem5444820 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5444821 : term170 = term235.
Proof. exact (@lem5444820 (NUMERAL 0)). Qed.
Lemma lem5444823 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5444824 : term238 = term239.
Proof. exact (@lem5444823 term193). Qed.
Lemma lem5444825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5444826 : term240 = term241.
Proof. exact (MK_COMB (@lem5444825) (@lem5444824)). Qed.
Lemma lem5444827 : term242 = term243.
Proof. exact (MK_COMB (@lem5444826) (@lem5444821)). Qed.
Lemma lem5444828 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5444830 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5444831 : term247 = term248.
Proof. exact (@lem5444830 term193 term193). Qed.
Lemma lem5444832 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5444833 : term250 = term193.
Proof. exact (EQ_MP (@lem5444832) (@lem940073)). Qed.
Lemma lem5444834 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5444835 : term248 = term192.
Proof. exact (MK_COMB (@lem5444834) (@lem5444833)). Qed.
Lemma lem5444836 : term247 = term192.
Proof. exact (TRANS (@lem5444831) (@lem5444835)). Qed.
Lemma lem5444838 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5444839 : term242 = term170.
Proof. exact (@lem5444838 term193). Qed.
Lemma lem5444840 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5444841 : term252 = term253.
Proof. exact (MK_COMB (@lem5444840) (@lem5444839)). Qed.
Lemma lem5444842 : term244 = term235.
Proof. exact (MK_COMB (@lem5444841) (@lem5444836)). Qed.
Lemma lem5444843 : term243 = term235.
Proof. exact (TRANS (@lem5444828) (@lem5444842)). Qed.
Lemma lem5444844 : term242 = term235.
Proof. exact (TRANS (@lem5444827) (@lem5444843)). Qed.
Lemma lem5444846 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5444847 : term235 = term170.
Proof. exact (@lem5444846 term170). Qed.
Lemma lem5444848 : term242 = term170.
Proof. exact (TRANS (@lem5444844) (@lem5444847)). Qed.
Lemma lem5444849 (_70518 : int) : (term194 _70518) = (term194 _70518).
Proof. exact (eq_refl (term194 _70518)). Qed.
Lemma lem5444850 (_70518 : int) : (term233 _70518) = (term255 _70518).
Proof. exact (MK_COMB (@lem5444849 _70518) (@lem5444848)). Qed.
Lemma lem5444851 (_70518 : int) : (term255 _70518) = (real_of_int _70518).
Proof. exact (@lem1982723 (real_of_int _70518)). Qed.
Lemma lem5444852 (_70518 : int) : (term233 _70518) = (real_of_int _70518).
Proof. exact (TRANS (@lem5444850 _70518) (@lem5444851 _70518)). Qed.
Lemma lem5444854 (_70518 : int) : (term232 _70518) = (real_of_int _70518).
Proof. exact (TRANS (@lem5444818 _70518) (@lem5444852 _70518)). Qed.
Lemma lem5444855 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5444856 (_70518 : int) : (term256 _70518) = (term257 _70518).
Proof. exact (MK_COMB (@lem5444855) (@lem5444854 _70518)). Qed.
Lemma lem5444857 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5444858 (_70518 : int) : (term231 _70518) = (term258 _70518).
Proof. exact (MK_COMB (@lem5444856 _70518) (@lem5444857)). Qed.
Lemma lem5444859 (_70518 : int) : (term173 _70518) = (term258 _70518).
Proof. exact (TRANS (@lem5444812 _70518) (@lem5444858 _70518)). Qed.
Lemma lem5444860 (_70519 : int) : (term173 _70519) = (term231 _70519).
Proof. exact (@lem1988287 (real_of_int _70519) term170). Qed.
Lemma lem5444866 (_70519 : int) : (term232 _70519) = (term233 _70519).
Proof. exact (@lem1982792 (real_of_int _70519) term170). Qed.
Lemma lem5444868 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5444869 : term170 = term235.
Proof. exact (@lem5444868 (NUMERAL 0)). Qed.
Lemma lem5444871 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5444872 : term238 = term239.
Proof. exact (@lem5444871 term193). Qed.
Lemma lem5444873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5444874 : term240 = term241.
Proof. exact (MK_COMB (@lem5444873) (@lem5444872)). Qed.
Lemma lem5444875 : term242 = term243.
Proof. exact (MK_COMB (@lem5444874) (@lem5444869)). Qed.
Lemma lem5444876 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5444878 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5444879 : term247 = term248.
Proof. exact (@lem5444878 term193 term193). Qed.
Lemma lem5444880 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5444881 : term250 = term193.
Proof. exact (EQ_MP (@lem5444880) (@lem940073)). Qed.
Lemma lem5444882 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5444883 : term248 = term192.
Proof. exact (MK_COMB (@lem5444882) (@lem5444881)). Qed.
Lemma lem5444884 : term247 = term192.
Proof. exact (TRANS (@lem5444879) (@lem5444883)). Qed.
Lemma lem5444886 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5444887 : term242 = term170.
Proof. exact (@lem5444886 term193). Qed.
Lemma lem5444888 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5444889 : term252 = term253.
Proof. exact (MK_COMB (@lem5444888) (@lem5444887)). Qed.
Lemma lem5444890 : term244 = term235.
Proof. exact (MK_COMB (@lem5444889) (@lem5444884)). Qed.
Lemma lem5444891 : term243 = term235.
Proof. exact (TRANS (@lem5444876) (@lem5444890)). Qed.
Lemma lem5444892 : term242 = term235.
Proof. exact (TRANS (@lem5444875) (@lem5444891)). Qed.
Lemma lem5444894 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5444895 : term235 = term170.
Proof. exact (@lem5444894 term170). Qed.
Lemma lem5444896 : term242 = term170.
Proof. exact (TRANS (@lem5444892) (@lem5444895)). Qed.
Lemma lem5444897 (_70519 : int) : (term194 _70519) = (term194 _70519).
Proof. exact (eq_refl (term194 _70519)). Qed.
Lemma lem5444898 (_70519 : int) : (term233 _70519) = (term255 _70519).
Proof. exact (MK_COMB (@lem5444897 _70519) (@lem5444896)). Qed.
Lemma lem5444899 (_70519 : int) : (term255 _70519) = (real_of_int _70519).
Proof. exact (@lem1982723 (real_of_int _70519)). Qed.
Lemma lem5444900 (_70519 : int) : (term233 _70519) = (real_of_int _70519).
Proof. exact (TRANS (@lem5444898 _70519) (@lem5444899 _70519)). Qed.
Lemma lem5444902 (_70519 : int) : (term232 _70519) = (real_of_int _70519).
Proof. exact (TRANS (@lem5444866 _70519) (@lem5444900 _70519)). Qed.
Lemma lem5444903 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5444904 (_70519 : int) : (term256 _70519) = (term257 _70519).
Proof. exact (MK_COMB (@lem5444903) (@lem5444902 _70519)). Qed.
Lemma lem5444905 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5444906 (_70519 : int) : (term231 _70519) = (term258 _70519).
Proof. exact (MK_COMB (@lem5444904 _70519) (@lem5444905)). Qed.
Lemma lem5444907 (_70519 : int) : (term173 _70519) = (term258 _70519).
Proof. exact (TRANS (@lem5444860 _70519) (@lem5444906 _70519)). Qed.
Lemma lem5444908 (_70520 : int) : (term173 _70520) = (term231 _70520).
Proof. exact (@lem1988287 (real_of_int _70520) term170). Qed.
Lemma lem5444914 (_70520 : int) : (term232 _70520) = (term233 _70520).
Proof. exact (@lem1982792 (real_of_int _70520) term170). Qed.
Lemma lem5444916 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5444917 : term170 = term235.
Proof. exact (@lem5444916 (NUMERAL 0)). Qed.
Lemma lem5444919 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5444920 : term238 = term239.
Proof. exact (@lem5444919 term193). Qed.
Lemma lem5444921 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5444922 : term240 = term241.
Proof. exact (MK_COMB (@lem5444921) (@lem5444920)). Qed.
Lemma lem5444923 : term242 = term243.
Proof. exact (MK_COMB (@lem5444922) (@lem5444917)). Qed.
Lemma lem5444924 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5444926 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5444927 : term247 = term248.
Proof. exact (@lem5444926 term193 term193). Qed.
Lemma lem5444928 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5444929 : term250 = term193.
Proof. exact (EQ_MP (@lem5444928) (@lem940073)). Qed.
Lemma lem5444930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5444931 : term248 = term192.
Proof. exact (MK_COMB (@lem5444930) (@lem5444929)). Qed.
Lemma lem5444932 : term247 = term192.
Proof. exact (TRANS (@lem5444927) (@lem5444931)). Qed.
Lemma lem5444934 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5444935 : term242 = term170.
Proof. exact (@lem5444934 term193). Qed.
Lemma lem5444936 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5444937 : term252 = term253.
Proof. exact (MK_COMB (@lem5444936) (@lem5444935)). Qed.
Lemma lem5444938 : term244 = term235.
Proof. exact (MK_COMB (@lem5444937) (@lem5444932)). Qed.
Lemma lem5444939 : term243 = term235.
Proof. exact (TRANS (@lem5444924) (@lem5444938)). Qed.
Lemma lem5444940 : term242 = term235.
Proof. exact (TRANS (@lem5444923) (@lem5444939)). Qed.
Lemma lem5444942 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5444943 : term235 = term170.
Proof. exact (@lem5444942 term170). Qed.
Lemma lem5444944 : term242 = term170.
Proof. exact (TRANS (@lem5444940) (@lem5444943)). Qed.
Lemma lem5444945 (_70520 : int) : (term194 _70520) = (term194 _70520).
Proof. exact (eq_refl (term194 _70520)). Qed.
Lemma lem5444946 (_70520 : int) : (term233 _70520) = (term255 _70520).
Proof. exact (MK_COMB (@lem5444945 _70520) (@lem5444944)). Qed.
Lemma lem5444947 (_70520 : int) : (term255 _70520) = (real_of_int _70520).
Proof. exact (@lem1982723 (real_of_int _70520)). Qed.
Lemma lem5444948 (_70520 : int) : (term233 _70520) = (real_of_int _70520).
Proof. exact (TRANS (@lem5444946 _70520) (@lem5444947 _70520)). Qed.
Lemma lem5444950 (_70520 : int) : (term232 _70520) = (real_of_int _70520).
Proof. exact (TRANS (@lem5444914 _70520) (@lem5444948 _70520)). Qed.
Lemma lem5444951 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5444952 (_70520 : int) : (term256 _70520) = (term257 _70520).
Proof. exact (MK_COMB (@lem5444951) (@lem5444950 _70520)). Qed.
Lemma lem5444953 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5444954 (_70520 : int) : (term231 _70520) = (term258 _70520).
Proof. exact (MK_COMB (@lem5444952 _70520) (@lem5444953)). Qed.
Lemma lem5444955 (_70520 : int) : (term173 _70520) = (term258 _70520).
Proof. exact (TRANS (@lem5444908 _70520) (@lem5444954 _70520)). Qed.
Lemma lem5444956 (_70521 : int) : (term173 _70521) = (term231 _70521).
Proof. exact (@lem1988287 (real_of_int _70521) term170). Qed.
Lemma lem5444962 (_70521 : int) : (term232 _70521) = (term233 _70521).
Proof. exact (@lem1982792 (real_of_int _70521) term170). Qed.
Lemma lem5444964 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5444965 : term170 = term235.
Proof. exact (@lem5444964 (NUMERAL 0)). Qed.
Lemma lem5444967 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5444968 : term238 = term239.
Proof. exact (@lem5444967 term193). Qed.
Lemma lem5444969 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5444970 : term240 = term241.
Proof. exact (MK_COMB (@lem5444969) (@lem5444968)). Qed.
Lemma lem5444971 : term242 = term243.
Proof. exact (MK_COMB (@lem5444970) (@lem5444965)). Qed.
Lemma lem5444972 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5444974 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5444975 : term247 = term248.
Proof. exact (@lem5444974 term193 term193). Qed.
Lemma lem5444976 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5444977 : term250 = term193.
Proof. exact (EQ_MP (@lem5444976) (@lem940073)). Qed.
Lemma lem5444978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5444979 : term248 = term192.
Proof. exact (MK_COMB (@lem5444978) (@lem5444977)). Qed.
Lemma lem5444980 : term247 = term192.
Proof. exact (TRANS (@lem5444975) (@lem5444979)). Qed.
Lemma lem5444982 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5444983 : term242 = term170.
Proof. exact (@lem5444982 term193). Qed.
Lemma lem5444984 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5444985 : term252 = term253.
Proof. exact (MK_COMB (@lem5444984) (@lem5444983)). Qed.
Lemma lem5444986 : term244 = term235.
Proof. exact (MK_COMB (@lem5444985) (@lem5444980)). Qed.
Lemma lem5444987 : term243 = term235.
Proof. exact (TRANS (@lem5444972) (@lem5444986)). Qed.
Lemma lem5444988 : term242 = term235.
Proof. exact (TRANS (@lem5444971) (@lem5444987)). Qed.
Lemma lem5444990 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5444991 : term235 = term170.
Proof. exact (@lem5444990 term170). Qed.
Lemma lem5444992 : term242 = term170.
Proof. exact (TRANS (@lem5444988) (@lem5444991)). Qed.
Lemma lem5444993 (_70521 : int) : (term194 _70521) = (term194 _70521).
Proof. exact (eq_refl (term194 _70521)). Qed.
Lemma lem5444994 (_70521 : int) : (term233 _70521) = (term255 _70521).
Proof. exact (MK_COMB (@lem5444993 _70521) (@lem5444992)). Qed.
Lemma lem5444995 (_70521 : int) : (term255 _70521) = (real_of_int _70521).
Proof. exact (@lem1982723 (real_of_int _70521)). Qed.
Lemma lem5444996 (_70521 : int) : (term233 _70521) = (real_of_int _70521).
Proof. exact (TRANS (@lem5444994 _70521) (@lem5444995 _70521)). Qed.
Lemma lem5444998 (_70521 : int) : (term232 _70521) = (real_of_int _70521).
Proof. exact (TRANS (@lem5444962 _70521) (@lem5444996 _70521)). Qed.
Lemma lem5444999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445000 (_70521 : int) : (term256 _70521) = (term257 _70521).
Proof. exact (MK_COMB (@lem5444999) (@lem5444998 _70521)). Qed.
Lemma lem5445001 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445002 (_70521 : int) : (term231 _70521) = (term258 _70521).
Proof. exact (MK_COMB (@lem5445000 _70521) (@lem5445001)). Qed.
Lemma lem5445003 (_70521 : int) : (term173 _70521) = (term258 _70521).
Proof. exact (TRANS (@lem5444956 _70521) (@lem5445002 _70521)). Qed.
Lemma lem5445004 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term182 _70518 _70520 _70519 _70521) = (term259 _70519 _70521 _70518 _70520).
Proof. exact (@lem1988287 (term181 _70519 _70521) (term177 _70518 _70520)). Qed.
Lemma lem5445018 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term260 _70519 _70521 _70518 _70520) = (term261 _70519 _70521 _70518 _70520).
Proof. exact (@lem1982792 (term181 _70519 _70521) (term177 _70518 _70520)). Qed.
Lemma lem5445023 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term261 _70519 _70521 _70518 _70520) = (term262 _70518 _70520 _70519 _70521).
Proof. exact (@lem1982761 (term263 _70518 _70520) (term181 _70519 _70521)). Qed.
Lemma lem5445025 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term260 _70519 _70521 _70518 _70520) = (term262 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445018 _70519 _70521 _70518 _70520) (@lem5445023 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445026 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445027 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term264 _70519 _70521 _70518 _70520) = (term265 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445026) (@lem5445025 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445028 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445029 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term259 _70519 _70521 _70518 _70520) = (term266 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445027 _70518 _70520 _70519 _70521) (@lem5445028)). Qed.
Lemma lem5445030 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term182 _70518 _70520 _70519 _70521) = (term266 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445004 _70519 _70521 _70518 _70520) (@lem5445029 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445031 (_70520 : int) (_70519 : int) : (term198 _70519 _70520) = (term267 _70520 _70519).
Proof. exact (@lem1988287 (real_of_int _70520) (term195 _70519)). Qed.
Lemma lem5445043 (_70520 : int) (_70519 : int) : (term268 _70520 _70519) = (term269 _70520 _70519).
Proof. exact (@lem1982792 (real_of_int _70520) (term195 _70519)). Qed.
Lemma lem5445044 (_70519 : int) : (term270 _70519) = (term271 _70519).
Proof. exact (@lem1982781 (real_of_int _70519) term238 term192). Qed.
Lemma lem5445046 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5445047 : term192 = term272.
Proof. exact (@lem5445046 term193). Qed.
Lemma lem5445049 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5445050 : term238 = term239.
Proof. exact (@lem5445049 term193). Qed.
Lemma lem5445051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5445052 : term240 = term241.
Proof. exact (MK_COMB (@lem5445051) (@lem5445050)). Qed.
Lemma lem5445053 : term273 = term274.
Proof. exact (MK_COMB (@lem5445052) (@lem5445047)). Qed.
Lemma lem5445054 : term274 = term275.
Proof. exact (@lem1981613 term238 term192 term192 term192). Qed.
Lemma lem5445056 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5445057 : term247 = term248.
Proof. exact (@lem5445056 term193 term193). Qed.
Lemma lem5445058 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445059 : term250 = term193.
Proof. exact (EQ_MP (@lem5445058) (@lem940073)). Qed.
Lemma lem5445060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445061 : term248 = term192.
Proof. exact (MK_COMB (@lem5445060) (@lem5445059)). Qed.
Lemma lem5445062 : term247 = term192.
Proof. exact (TRANS (@lem5445057) (@lem5445061)). Qed.
Lemma lem5445064 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5445065 : term273 = term278.
Proof. exact (@lem5445064 term193 term193). Qed.
Lemma lem5445066 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445067 : term250 = term193.
Proof. exact (EQ_MP (@lem5445066) (@lem940073)). Qed.
Lemma lem5445068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445069 : term248 = term192.
Proof. exact (MK_COMB (@lem5445068) (@lem5445067)). Qed.
Lemma lem5445070 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5445071 : term278 = term238.
Proof. exact (MK_COMB (@lem5445070) (@lem5445069)). Qed.
Lemma lem5445072 : term273 = term238.
Proof. exact (TRANS (@lem5445065) (@lem5445071)). Qed.
Lemma lem5445073 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5445074 : term279 = term280.
Proof. exact (MK_COMB (@lem5445073) (@lem5445072)). Qed.
Lemma lem5445075 : term275 = term239.
Proof. exact (MK_COMB (@lem5445074) (@lem5445062)). Qed.
Lemma lem5445076 : term274 = term239.
Proof. exact (TRANS (@lem5445054) (@lem5445075)). Qed.
Lemma lem5445077 : term273 = term239.
Proof. exact (TRANS (@lem5445053) (@lem5445076)). Qed.
Lemma lem5445079 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5445080 : term239 = term238.
Proof. exact (@lem5445079 term238). Qed.
Lemma lem5445081 : term273 = term238.
Proof. exact (TRANS (@lem5445077) (@lem5445080)). Qed.
Lemma lem5445084 (_70519 : int) : (term281 _70519) = (term281 _70519).
Proof. exact (eq_refl (term281 _70519)). Qed.
Lemma lem5445085 (_70519 : int) : (term271 _70519) = (term282 _70519).
Proof. exact (MK_COMB (@lem5445084 _70519) (@lem5445081)). Qed.
Lemma lem5445086 (_70519 : int) : (term270 _70519) = (term282 _70519).
Proof. exact (TRANS (@lem5445044 _70519) (@lem5445085 _70519)). Qed.
Lemma lem5445087 (_70520 : int) : (term194 _70520) = (term194 _70520).
Proof. exact (eq_refl (term194 _70520)). Qed.
Lemma lem5445088 (_70520 : int) (_70519 : int) : (term269 _70520 _70519) = (term283 _70520 _70519).
Proof. exact (MK_COMB (@lem5445087 _70520) (@lem5445086 _70519)). Qed.
Lemma lem5445093 (_70519 : int) (_70520 : int) : (term283 _70520 _70519) = (term284 _70519 _70520).
Proof. exact (@lem1982757 (term285 _70519) (real_of_int _70520) term238). Qed.
Lemma lem5445094 (_70519 : int) (_70520 : int) : (term269 _70520 _70519) = (term284 _70519 _70520).
Proof. exact (TRANS (@lem5445088 _70520 _70519) (@lem5445093 _70519 _70520)). Qed.
Lemma lem5445096 (_70519 : int) (_70520 : int) : (term268 _70520 _70519) = (term284 _70519 _70520).
Proof. exact (TRANS (@lem5445043 _70520 _70519) (@lem5445094 _70519 _70520)). Qed.
Lemma lem5445097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445098 (_70519 : int) (_70520 : int) : (term286 _70520 _70519) = (term287 _70519 _70520).
Proof. exact (MK_COMB (@lem5445097) (@lem5445096 _70519 _70520)). Qed.
Lemma lem5445099 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445100 (_70519 : int) (_70520 : int) : (term267 _70520 _70519) = (term288 _70519 _70520).
Proof. exact (MK_COMB (@lem5445098 _70519 _70520) (@lem5445099)). Qed.
Lemma lem5445101 (_70519 : int) (_70520 : int) : (term198 _70519 _70520) = (term288 _70519 _70520).
Proof. exact (TRANS (@lem5445031 _70520 _70519) (@lem5445100 _70519 _70520)). Qed.
Lemma lem5445102 (_70518 : int) (_70521 : int) : (term198 _70521 _70518) = (term267 _70518 _70521).
Proof. exact (@lem1988287 (real_of_int _70518) (term195 _70521)). Qed.
Lemma lem5445114 (_70518 : int) (_70521 : int) : (term268 _70518 _70521) = (term269 _70518 _70521).
Proof. exact (@lem1982792 (real_of_int _70518) (term195 _70521)). Qed.
Lemma lem5445115 (_70521 : int) : (term270 _70521) = (term271 _70521).
Proof. exact (@lem1982781 (real_of_int _70521) term238 term192). Qed.
Lemma lem5445117 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5445118 : term192 = term272.
Proof. exact (@lem5445117 term193). Qed.
Lemma lem5445120 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5445121 : term238 = term239.
Proof. exact (@lem5445120 term193). Qed.
Lemma lem5445122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5445123 : term240 = term241.
Proof. exact (MK_COMB (@lem5445122) (@lem5445121)). Qed.
Lemma lem5445124 : term273 = term274.
Proof. exact (MK_COMB (@lem5445123) (@lem5445118)). Qed.
Lemma lem5445125 : term274 = term275.
Proof. exact (@lem1981613 term238 term192 term192 term192). Qed.
Lemma lem5445127 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5445128 : term247 = term248.
Proof. exact (@lem5445127 term193 term193). Qed.
Lemma lem5445129 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445130 : term250 = term193.
Proof. exact (EQ_MP (@lem5445129) (@lem940073)). Qed.
Lemma lem5445131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445132 : term248 = term192.
Proof. exact (MK_COMB (@lem5445131) (@lem5445130)). Qed.
Lemma lem5445133 : term247 = term192.
Proof. exact (TRANS (@lem5445128) (@lem5445132)). Qed.
Lemma lem5445135 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5445136 : term273 = term278.
Proof. exact (@lem5445135 term193 term193). Qed.
Lemma lem5445137 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445138 : term250 = term193.
Proof. exact (EQ_MP (@lem5445137) (@lem940073)). Qed.
Lemma lem5445139 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445140 : term248 = term192.
Proof. exact (MK_COMB (@lem5445139) (@lem5445138)). Qed.
Lemma lem5445141 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5445142 : term278 = term238.
Proof. exact (MK_COMB (@lem5445141) (@lem5445140)). Qed.
Lemma lem5445143 : term273 = term238.
Proof. exact (TRANS (@lem5445136) (@lem5445142)). Qed.
Lemma lem5445144 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5445145 : term279 = term280.
Proof. exact (MK_COMB (@lem5445144) (@lem5445143)). Qed.
Lemma lem5445146 : term275 = term239.
Proof. exact (MK_COMB (@lem5445145) (@lem5445133)). Qed.
Lemma lem5445147 : term274 = term239.
Proof. exact (TRANS (@lem5445125) (@lem5445146)). Qed.
Lemma lem5445148 : term273 = term239.
Proof. exact (TRANS (@lem5445124) (@lem5445147)). Qed.
Lemma lem5445150 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5445151 : term239 = term238.
Proof. exact (@lem5445150 term238). Qed.
Lemma lem5445152 : term273 = term238.
Proof. exact (TRANS (@lem5445148) (@lem5445151)). Qed.
Lemma lem5445155 (_70521 : int) : (term281 _70521) = (term281 _70521).
Proof. exact (eq_refl (term281 _70521)). Qed.
Lemma lem5445156 (_70521 : int) : (term271 _70521) = (term282 _70521).
Proof. exact (MK_COMB (@lem5445155 _70521) (@lem5445152)). Qed.
Lemma lem5445157 (_70521 : int) : (term270 _70521) = (term282 _70521).
Proof. exact (TRANS (@lem5445115 _70521) (@lem5445156 _70521)). Qed.
Lemma lem5445158 (_70518 : int) : (term194 _70518) = (term194 _70518).
Proof. exact (eq_refl (term194 _70518)). Qed.
Lemma lem5445161 (_70518 : int) (_70521 : int) : (term269 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (MK_COMB (@lem5445158 _70518) (@lem5445157 _70521)). Qed.
Lemma lem5445163 (_70518 : int) (_70521 : int) : (term268 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (TRANS (@lem5445114 _70518 _70521) (@lem5445161 _70518 _70521)). Qed.
Lemma lem5445164 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445165 (_70518 : int) (_70521 : int) : (term286 _70518 _70521) = (term289 _70518 _70521).
Proof. exact (MK_COMB (@lem5445164) (@lem5445163 _70518 _70521)). Qed.
Lemma lem5445166 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445167 (_70518 : int) (_70521 : int) : (term267 _70518 _70521) = (term290 _70518 _70521).
Proof. exact (MK_COMB (@lem5445165 _70518 _70521) (@lem5445166)). Qed.
Lemma lem5445168 (_70518 : int) (_70521 : int) : (term198 _70521 _70518) = (term290 _70518 _70521).
Proof. exact (TRANS (@lem5445102 _70518 _70521) (@lem5445167 _70518 _70521)). Qed.
Lemma lem5445169 (_70518 : int) (_70519 : int) : (term198 _70519 _70518) = (term267 _70518 _70519).
Proof. exact (@lem1988287 (real_of_int _70518) (term195 _70519)). Qed.
Lemma lem5445181 (_70518 : int) (_70519 : int) : (term268 _70518 _70519) = (term269 _70518 _70519).
Proof. exact (@lem1982792 (real_of_int _70518) (term195 _70519)). Qed.
Lemma lem5445182 (_70519 : int) : (term270 _70519) = (term271 _70519).
Proof. exact (@lem1982781 (real_of_int _70519) term238 term192). Qed.
Lemma lem5445184 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5445185 : term192 = term272.
Proof. exact (@lem5445184 term193). Qed.
Lemma lem5445187 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5445188 : term238 = term239.
Proof. exact (@lem5445187 term193). Qed.
Lemma lem5445189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5445190 : term240 = term241.
Proof. exact (MK_COMB (@lem5445189) (@lem5445188)). Qed.
Lemma lem5445191 : term273 = term274.
Proof. exact (MK_COMB (@lem5445190) (@lem5445185)). Qed.
Lemma lem5445192 : term274 = term275.
Proof. exact (@lem1981613 term238 term192 term192 term192). Qed.
Lemma lem5445194 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5445195 : term247 = term248.
Proof. exact (@lem5445194 term193 term193). Qed.
Lemma lem5445196 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445197 : term250 = term193.
Proof. exact (EQ_MP (@lem5445196) (@lem940073)). Qed.
Lemma lem5445198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445199 : term248 = term192.
Proof. exact (MK_COMB (@lem5445198) (@lem5445197)). Qed.
Lemma lem5445200 : term247 = term192.
Proof. exact (TRANS (@lem5445195) (@lem5445199)). Qed.
Lemma lem5445202 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5445203 : term273 = term278.
Proof. exact (@lem5445202 term193 term193). Qed.
Lemma lem5445204 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445205 : term250 = term193.
Proof. exact (EQ_MP (@lem5445204) (@lem940073)). Qed.
Lemma lem5445206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445207 : term248 = term192.
Proof. exact (MK_COMB (@lem5445206) (@lem5445205)). Qed.
Lemma lem5445208 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5445209 : term278 = term238.
Proof. exact (MK_COMB (@lem5445208) (@lem5445207)). Qed.
Lemma lem5445210 : term273 = term238.
Proof. exact (TRANS (@lem5445203) (@lem5445209)). Qed.
Lemma lem5445211 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5445212 : term279 = term280.
Proof. exact (MK_COMB (@lem5445211) (@lem5445210)). Qed.
Lemma lem5445213 : term275 = term239.
Proof. exact (MK_COMB (@lem5445212) (@lem5445200)). Qed.
Lemma lem5445214 : term274 = term239.
Proof. exact (TRANS (@lem5445192) (@lem5445213)). Qed.
Lemma lem5445215 : term273 = term239.
Proof. exact (TRANS (@lem5445191) (@lem5445214)). Qed.
Lemma lem5445217 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5445218 : term239 = term238.
Proof. exact (@lem5445217 term238). Qed.
Lemma lem5445219 : term273 = term238.
Proof. exact (TRANS (@lem5445215) (@lem5445218)). Qed.
Lemma lem5445222 (_70519 : int) : (term281 _70519) = (term281 _70519).
Proof. exact (eq_refl (term281 _70519)). Qed.
Lemma lem5445223 (_70519 : int) : (term271 _70519) = (term282 _70519).
Proof. exact (MK_COMB (@lem5445222 _70519) (@lem5445219)). Qed.
Lemma lem5445224 (_70519 : int) : (term270 _70519) = (term282 _70519).
Proof. exact (TRANS (@lem5445182 _70519) (@lem5445223 _70519)). Qed.
Lemma lem5445225 (_70518 : int) : (term194 _70518) = (term194 _70518).
Proof. exact (eq_refl (term194 _70518)). Qed.
Lemma lem5445228 (_70518 : int) (_70519 : int) : (term269 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (MK_COMB (@lem5445225 _70518) (@lem5445224 _70519)). Qed.
Lemma lem5445230 (_70518 : int) (_70519 : int) : (term268 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (TRANS (@lem5445181 _70518 _70519) (@lem5445228 _70518 _70519)). Qed.
Lemma lem5445231 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445232 (_70518 : int) (_70519 : int) : (term286 _70518 _70519) = (term289 _70518 _70519).
Proof. exact (MK_COMB (@lem5445231) (@lem5445230 _70518 _70519)). Qed.
Lemma lem5445233 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445234 (_70518 : int) (_70519 : int) : (term267 _70518 _70519) = (term290 _70518 _70519).
Proof. exact (MK_COMB (@lem5445232 _70518 _70519) (@lem5445233)). Qed.
Lemma lem5445235 (_70518 : int) (_70519 : int) : (term198 _70519 _70518) = (term290 _70518 _70519).
Proof. exact (TRANS (@lem5445169 _70518 _70519) (@lem5445234 _70518 _70519)). Qed.
Lemma lem5445236 (_70520 : int) (_70521 : int) : (term198 _70521 _70520) = (term267 _70520 _70521).
Proof. exact (@lem1988287 (real_of_int _70520) (term195 _70521)). Qed.
Lemma lem5445248 (_70520 : int) (_70521 : int) : (term268 _70520 _70521) = (term269 _70520 _70521).
Proof. exact (@lem1982792 (real_of_int _70520) (term195 _70521)). Qed.
Lemma lem5445249 (_70521 : int) : (term270 _70521) = (term271 _70521).
Proof. exact (@lem1982781 (real_of_int _70521) term238 term192). Qed.
Lemma lem5445251 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5445252 : term192 = term272.
Proof. exact (@lem5445251 term193). Qed.
Lemma lem5445254 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5445255 : term238 = term239.
Proof. exact (@lem5445254 term193). Qed.
Lemma lem5445256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5445257 : term240 = term241.
Proof. exact (MK_COMB (@lem5445256) (@lem5445255)). Qed.
Lemma lem5445258 : term273 = term274.
Proof. exact (MK_COMB (@lem5445257) (@lem5445252)). Qed.
Lemma lem5445259 : term274 = term275.
Proof. exact (@lem1981613 term238 term192 term192 term192). Qed.
Lemma lem5445261 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5445262 : term247 = term248.
Proof. exact (@lem5445261 term193 term193). Qed.
Lemma lem5445263 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445264 : term250 = term193.
Proof. exact (EQ_MP (@lem5445263) (@lem940073)). Qed.
Lemma lem5445265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445266 : term248 = term192.
Proof. exact (MK_COMB (@lem5445265) (@lem5445264)). Qed.
Lemma lem5445267 : term247 = term192.
Proof. exact (TRANS (@lem5445262) (@lem5445266)). Qed.
Lemma lem5445269 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5445270 : term273 = term278.
Proof. exact (@lem5445269 term193 term193). Qed.
Lemma lem5445271 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445272 : term250 = term193.
Proof. exact (EQ_MP (@lem5445271) (@lem940073)). Qed.
Lemma lem5445273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445274 : term248 = term192.
Proof. exact (MK_COMB (@lem5445273) (@lem5445272)). Qed.
Lemma lem5445275 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5445276 : term278 = term238.
Proof. exact (MK_COMB (@lem5445275) (@lem5445274)). Qed.
Lemma lem5445277 : term273 = term238.
Proof. exact (TRANS (@lem5445270) (@lem5445276)). Qed.
Lemma lem5445278 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5445279 : term279 = term280.
Proof. exact (MK_COMB (@lem5445278) (@lem5445277)). Qed.
Lemma lem5445280 : term275 = term239.
Proof. exact (MK_COMB (@lem5445279) (@lem5445267)). Qed.
Lemma lem5445281 : term274 = term239.
Proof. exact (TRANS (@lem5445259) (@lem5445280)). Qed.
Lemma lem5445282 : term273 = term239.
Proof. exact (TRANS (@lem5445258) (@lem5445281)). Qed.
Lemma lem5445284 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5445285 : term239 = term238.
Proof. exact (@lem5445284 term238). Qed.
Lemma lem5445286 : term273 = term238.
Proof. exact (TRANS (@lem5445282) (@lem5445285)). Qed.
Lemma lem5445289 (_70521 : int) : (term281 _70521) = (term281 _70521).
Proof. exact (eq_refl (term281 _70521)). Qed.
Lemma lem5445290 (_70521 : int) : (term271 _70521) = (term282 _70521).
Proof. exact (MK_COMB (@lem5445289 _70521) (@lem5445286)). Qed.
Lemma lem5445291 (_70521 : int) : (term270 _70521) = (term282 _70521).
Proof. exact (TRANS (@lem5445249 _70521) (@lem5445290 _70521)). Qed.
Lemma lem5445292 (_70520 : int) : (term194 _70520) = (term194 _70520).
Proof. exact (eq_refl (term194 _70520)). Qed.
Lemma lem5445295 (_70520 : int) (_70521 : int) : (term269 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (MK_COMB (@lem5445292 _70520) (@lem5445291 _70521)). Qed.
Lemma lem5445297 (_70520 : int) (_70521 : int) : (term268 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (TRANS (@lem5445248 _70520 _70521) (@lem5445295 _70520 _70521)). Qed.
Lemma lem5445298 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445299 (_70520 : int) (_70521 : int) : (term286 _70520 _70521) = (term289 _70520 _70521).
Proof. exact (MK_COMB (@lem5445298) (@lem5445297 _70520 _70521)). Qed.
Lemma lem5445300 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445301 (_70520 : int) (_70521 : int) : (term267 _70520 _70521) = (term290 _70520 _70521).
Proof. exact (MK_COMB (@lem5445299 _70520 _70521) (@lem5445300)). Qed.
Lemma lem5445302 (_70520 : int) (_70521 : int) : (term198 _70521 _70520) = (term290 _70520 _70521).
Proof. exact (TRANS (@lem5445236 _70520 _70521) (@lem5445301 _70520 _70521)). Qed.
Lemma lem5445303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445304 (_70518 : int) (_70519 : int) : (term199 _70519 _70518) = (term291 _70518 _70519).
Proof. exact (MK_COMB (@lem5445303) (@lem5445235 _70518 _70519)). Qed.
Lemma lem5445305 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term200 _70519 _70518 _70521 _70520) = (term292 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445304 _70518 _70519) (@lem5445302 _70520 _70521)). Qed.
Lemma lem5445306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445307 (_70518 : int) (_70521 : int) : (term199 _70521 _70518) = (term291 _70518 _70521).
Proof. exact (MK_COMB (@lem5445306) (@lem5445168 _70518 _70521)). Qed.
Lemma lem5445308 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term201 _70519 _70518 _70521 _70520) = (term293 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445307 _70518 _70521) (@lem5445305 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445310 (_70519 : int) (_70520 : int) : (term199 _70519 _70520) = (term294 _70519 _70520).
Proof. exact (MK_COMB (@lem5445309) (@lem5445101 _70519 _70520)). Qed.
Lemma lem5445311 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term202 _70519 _70518 _70521 _70520) = (term295 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445310 _70519 _70520) (@lem5445308 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445313 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term203 _70518 _70520 _70519 _70521) = (term296 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445312) (@lem5445030 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445314 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term204 _70519 _70518 _70521 _70520) = (term297 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445313 _70518 _70520 _70519 _70521) (@lem5445311 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445315 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term215 _70519 _70521 _70518 _70520) = (term298 _70518 _70520 _70519 _70521).
Proof. exact (@lem1988287 (term177 _70518 _70520) (term212 _70519 _70521)). Qed.
Lemma lem5445335 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term299 _70518 _70520 _70519 _70521) = (term300 _70518 _70520 _70519 _70521).
Proof. exact (@lem1982792 (term177 _70518 _70520) (term212 _70519 _70521)). Qed.
Lemma lem5445336 (_70519 : int) (_70521 : int) : (term301 _70519 _70521) = (term302 _70519 _70521).
Proof. exact (@lem1982781 (term181 _70519 _70521) term238 term192). Qed.
Lemma lem5445338 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5445339 : term192 = term272.
Proof. exact (@lem5445338 term193). Qed.
Lemma lem5445341 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5445342 : term238 = term239.
Proof. exact (@lem5445341 term193). Qed.
Lemma lem5445343 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5445344 : term240 = term241.
Proof. exact (MK_COMB (@lem5445343) (@lem5445342)). Qed.
Lemma lem5445345 : term273 = term274.
Proof. exact (MK_COMB (@lem5445344) (@lem5445339)). Qed.
Lemma lem5445346 : term274 = term275.
Proof. exact (@lem1981613 term238 term192 term192 term192). Qed.
Lemma lem5445348 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5445349 : term247 = term248.
Proof. exact (@lem5445348 term193 term193). Qed.
Lemma lem5445350 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445351 : term250 = term193.
Proof. exact (EQ_MP (@lem5445350) (@lem940073)). Qed.
Lemma lem5445352 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445353 : term248 = term192.
Proof. exact (MK_COMB (@lem5445352) (@lem5445351)). Qed.
Lemma lem5445354 : term247 = term192.
Proof. exact (TRANS (@lem5445349) (@lem5445353)). Qed.
Lemma lem5445356 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5445357 : term273 = term278.
Proof. exact (@lem5445356 term193 term193). Qed.
Lemma lem5445358 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5445359 : term250 = term193.
Proof. exact (EQ_MP (@lem5445358) (@lem940073)). Qed.
Lemma lem5445360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5445361 : term248 = term192.
Proof. exact (MK_COMB (@lem5445360) (@lem5445359)). Qed.
Lemma lem5445362 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5445363 : term278 = term238.
Proof. exact (MK_COMB (@lem5445362) (@lem5445361)). Qed.
Lemma lem5445364 : term273 = term238.
Proof. exact (TRANS (@lem5445357) (@lem5445363)). Qed.
Lemma lem5445365 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5445366 : term279 = term280.
Proof. exact (MK_COMB (@lem5445365) (@lem5445364)). Qed.
Lemma lem5445367 : term275 = term239.
Proof. exact (MK_COMB (@lem5445366) (@lem5445354)). Qed.
Lemma lem5445368 : term274 = term239.
Proof. exact (TRANS (@lem5445346) (@lem5445367)). Qed.
Lemma lem5445369 : term273 = term239.
Proof. exact (TRANS (@lem5445345) (@lem5445368)). Qed.
Lemma lem5445371 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5445372 : term239 = term238.
Proof. exact (@lem5445371 term238). Qed.
Lemma lem5445373 : term273 = term238.
Proof. exact (TRANS (@lem5445369) (@lem5445372)). Qed.
Lemma lem5445376 (_70519 : int) (_70521 : int) : (term303 _70519 _70521) = (term303 _70519 _70521).
Proof. exact (eq_refl (term303 _70519 _70521)). Qed.
Lemma lem5445377 (_70519 : int) (_70521 : int) : (term302 _70519 _70521) = (term304 _70519 _70521).
Proof. exact (MK_COMB (@lem5445376 _70519 _70521) (@lem5445373)). Qed.
Lemma lem5445378 (_70519 : int) (_70521 : int) : (term301 _70519 _70521) = (term304 _70519 _70521).
Proof. exact (TRANS (@lem5445336 _70519 _70521) (@lem5445377 _70519 _70521)). Qed.
Lemma lem5445379 (_70518 : int) (_70520 : int) : (term305 _70518 _70520) = (term305 _70518 _70520).
Proof. exact (eq_refl (term305 _70518 _70520)). Qed.
Lemma lem5445382 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term300 _70518 _70520 _70519 _70521) = (term306 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445379 _70518 _70520) (@lem5445378 _70519 _70521)). Qed.
Lemma lem5445384 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term299 _70518 _70520 _70519 _70521) = (term306 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445335 _70518 _70520 _70519 _70521) (@lem5445382 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445385 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445386 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term307 _70518 _70520 _70519 _70521) = (term308 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445385) (@lem5445384 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445387 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445388 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term298 _70518 _70520 _70519 _70521) = (term309 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445386 _70518 _70520 _70519 _70521) (@lem5445387)). Qed.
Lemma lem5445389 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term215 _70519 _70521 _70518 _70520) = (term309 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445315 _70518 _70520 _70519 _70521) (@lem5445388 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445390 (_70519 : int) (_70520 : int) : (term165 _70520 _70519) = (term310 _70519 _70520).
Proof. exact (@lem1988287 (real_of_int _70519) (real_of_int _70520)). Qed.
Lemma lem5445403 (_70519 : int) (_70520 : int) : (term311 _70519 _70520) = (term312 _70519 _70520).
Proof. exact (@lem1982792 (real_of_int _70519) (real_of_int _70520)). Qed.
Lemma lem5445404 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445405 (_70519 : int) (_70520 : int) : (term313 _70519 _70520) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5445404) (@lem5445403 _70519 _70520)). Qed.
Lemma lem5445406 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445407 (_70519 : int) (_70520 : int) : (term310 _70519 _70520) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5445405 _70519 _70520) (@lem5445406)). Qed.
Lemma lem5445408 (_70519 : int) (_70520 : int) : (term165 _70520 _70519) = (term315 _70519 _70520).
Proof. exact (TRANS (@lem5445390 _70519 _70520) (@lem5445407 _70519 _70520)). Qed.
Lemma lem5445409 (_70521 : int) (_70518 : int) : (term165 _70518 _70521) = (term310 _70521 _70518).
Proof. exact (@lem1988287 (real_of_int _70521) (real_of_int _70518)). Qed.
Lemma lem5445415 (_70521 : int) (_70518 : int) : (term311 _70521 _70518) = (term312 _70521 _70518).
Proof. exact (@lem1982792 (real_of_int _70521) (real_of_int _70518)). Qed.
Lemma lem5445420 (_70518 : int) (_70521 : int) : (term312 _70521 _70518) = (term316 _70518 _70521).
Proof. exact (@lem1982761 (term285 _70518) (real_of_int _70521)). Qed.
Lemma lem5445422 (_70518 : int) (_70521 : int) : (term311 _70521 _70518) = (term316 _70518 _70521).
Proof. exact (TRANS (@lem5445415 _70521 _70518) (@lem5445420 _70518 _70521)). Qed.
Lemma lem5445423 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445424 (_70518 : int) (_70521 : int) : (term313 _70521 _70518) = (term317 _70518 _70521).
Proof. exact (MK_COMB (@lem5445423) (@lem5445422 _70518 _70521)). Qed.
Lemma lem5445425 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445426 (_70518 : int) (_70521 : int) : (term310 _70521 _70518) = (term318 _70518 _70521).
Proof. exact (MK_COMB (@lem5445424 _70518 _70521) (@lem5445425)). Qed.
Lemma lem5445427 (_70518 : int) (_70521 : int) : (term165 _70518 _70521) = (term318 _70518 _70521).
Proof. exact (TRANS (@lem5445409 _70521 _70518) (@lem5445426 _70518 _70521)). Qed.
Lemma lem5445428 (_70519 : int) (_70518 : int) : (term165 _70518 _70519) = (term310 _70519 _70518).
Proof. exact (@lem1988287 (real_of_int _70519) (real_of_int _70518)). Qed.
Lemma lem5445434 (_70519 : int) (_70518 : int) : (term311 _70519 _70518) = (term312 _70519 _70518).
Proof. exact (@lem1982792 (real_of_int _70519) (real_of_int _70518)). Qed.
Lemma lem5445439 (_70518 : int) (_70519 : int) : (term312 _70519 _70518) = (term316 _70518 _70519).
Proof. exact (@lem1982761 (term285 _70518) (real_of_int _70519)). Qed.
Lemma lem5445441 (_70518 : int) (_70519 : int) : (term311 _70519 _70518) = (term316 _70518 _70519).
Proof. exact (TRANS (@lem5445434 _70519 _70518) (@lem5445439 _70518 _70519)). Qed.
Lemma lem5445442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445443 (_70518 : int) (_70519 : int) : (term313 _70519 _70518) = (term317 _70518 _70519).
Proof. exact (MK_COMB (@lem5445442) (@lem5445441 _70518 _70519)). Qed.
Lemma lem5445444 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445445 (_70518 : int) (_70519 : int) : (term310 _70519 _70518) = (term318 _70518 _70519).
Proof. exact (MK_COMB (@lem5445443 _70518 _70519) (@lem5445444)). Qed.
Lemma lem5445446 (_70518 : int) (_70519 : int) : (term165 _70518 _70519) = (term318 _70518 _70519).
Proof. exact (TRANS (@lem5445428 _70519 _70518) (@lem5445445 _70518 _70519)). Qed.
Lemma lem5445447 (_70521 : int) (_70520 : int) : (term165 _70520 _70521) = (term310 _70521 _70520).
Proof. exact (@lem1988287 (real_of_int _70521) (real_of_int _70520)). Qed.
Lemma lem5445453 (_70521 : int) (_70520 : int) : (term311 _70521 _70520) = (term312 _70521 _70520).
Proof. exact (@lem1982792 (real_of_int _70521) (real_of_int _70520)). Qed.
Lemma lem5445458 (_70520 : int) (_70521 : int) : (term312 _70521 _70520) = (term316 _70520 _70521).
Proof. exact (@lem1982761 (term285 _70520) (real_of_int _70521)). Qed.
Lemma lem5445460 (_70520 : int) (_70521 : int) : (term311 _70521 _70520) = (term316 _70520 _70521).
Proof. exact (TRANS (@lem5445453 _70521 _70520) (@lem5445458 _70520 _70521)). Qed.
Lemma lem5445461 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445462 (_70520 : int) (_70521 : int) : (term313 _70521 _70520) = (term317 _70520 _70521).
Proof. exact (MK_COMB (@lem5445461) (@lem5445460 _70520 _70521)). Qed.
Lemma lem5445463 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445464 (_70520 : int) (_70521 : int) : (term310 _70521 _70520) = (term318 _70520 _70521).
Proof. exact (MK_COMB (@lem5445462 _70520 _70521) (@lem5445463)). Qed.
Lemma lem5445465 (_70520 : int) (_70521 : int) : (term165 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (TRANS (@lem5445447 _70521 _70520) (@lem5445464 _70520 _70521)). Qed.
Lemma lem5445466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445467 (_70518 : int) (_70519 : int) : (term216 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5445466) (@lem5445446 _70518 _70519)). Qed.
Lemma lem5445468 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term217 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445467 _70518 _70519) (@lem5445465 _70520 _70521)). Qed.
Lemma lem5445469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445470 (_70518 : int) (_70521 : int) : (term216 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5445469) (@lem5445427 _70518 _70521)). Qed.
Lemma lem5445471 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term218 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445470 _70518 _70521) (@lem5445468 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445473 (_70519 : int) (_70520 : int) : (term216 _70520 _70519) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5445472) (@lem5445408 _70519 _70520)). Qed.
Lemma lem5445474 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term219 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445473 _70519 _70520) (@lem5445471 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445476 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term220 _70519 _70521 _70518 _70520) = (term324 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445475) (@lem5445389 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445477 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term221 _70518 _70519 _70520 _70521) = (term325 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445476 _70518 _70520 _70519 _70521) (@lem5445474 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445479 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term222 _70519 _70518 _70521 _70520) = (term326 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445478) (@lem5445314 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445480 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term223 _70518 _70519 _70520 _70521) = (term327 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445479 _70518 _70519 _70520 _70521) (@lem5445477 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445482 (_70521 : int) : (term224 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5445481) (@lem5445003 _70521)). Qed.
Lemma lem5445483 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term225 _70518 _70519 _70520 _70521) = (term329 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445482 _70521) (@lem5445480 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445485 (_70520 : int) : (term224 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5445484) (@lem5444955 _70520)). Qed.
Lemma lem5445486 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term226 _70518 _70519 _70520 _70521) = (term330 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445485 _70520) (@lem5445483 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445488 (_70519 : int) : (term224 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5445487) (@lem5444907 _70519)). Qed.
Lemma lem5445489 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term227 _70518 _70519 _70520 _70521) = (term331 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445488 _70519) (@lem5445486 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445491 (_70518 : int) : (term224 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5445490) (@lem5444859 _70518)). Qed.
Lemma lem5445492 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term228 _70518 _70519 _70520 _70521) = (term332 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445491 _70518) (@lem5445489 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445499 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term230 _70518 _70519 _70520 _70521) = (term332 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5444811 _70518 _70519 _70520 _70521) (@lem5445492 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445524 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term325 _70518 _70519 _70520 _70521) = (term325 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term325 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445542 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term297 _70518 _70519 _70520 _70521) = (term333 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term288 _70519 _70520) (term266 _70518 _70520 _70519 _70521) (term293 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445543 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term334 _70518 _70519 _70520 _70521) = (term335 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term290 _70518 _70521) (term266 _70518 _70520 _70519 _70521) (term292 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445550 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term336 _70518 _70519 _70520 _70521) = (term337 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term290 _70518 _70519) (term266 _70518 _70520 _70519 _70521) (term290 _70520 _70521)). Qed.
Lemma lem5445553 (_70520 : int) (_70519 : int) (_70518 : int) (_70521 : int) : (term338 _70520 _70519 _70518 _70521) = (term338 _70520 _70519 _70518 _70521).
Proof. exact (eq_refl (term338 _70520 _70519 _70518 _70521)). Qed.
Lemma lem5445554 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term335 _70518 _70519 _70520 _70521) = (term339 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445553 _70520 _70519 _70518 _70521) (@lem5445550 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445555 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term334 _70518 _70519 _70520 _70521) = (term339 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445543 _70518 _70519 _70520 _70521) (@lem5445554 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445558 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term340 _70518 _70521 _70519 _70520) = (term340 _70518 _70521 _70519 _70520).
Proof. exact (eq_refl (term340 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445559 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term333 _70518 _70519 _70520 _70521) = (term341 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445558 _70518 _70521 _70519 _70520) (@lem5445555 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445561 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term297 _70518 _70519 _70520 _70521) = (term341 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445542 _70518 _70519 _70520 _70521) (@lem5445559 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445563 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term326 _70518 _70519 _70520 _70521) = (term342 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445562) (@lem5445561 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445564 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term327 _70518 _70519 _70520 _70521) = (term343 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445563 _70518 _70519 _70520 _70521) (@lem5445524 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445567 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (eq_refl (term328 _70521)). Qed.
Lemma lem5445568 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term329 _70518 _70519 _70520 _70521) = (term344 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445567 _70521) (@lem5445564 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445569 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term344 _70518 _70519 _70520 _70521) = (term345 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term341 _70518 _70519 _70520 _70521) (term258 _70521) (term325 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445570 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term346 _70518 _70519 _70520 _70521) = (term346 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term346 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445571 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term347 _70518 _70519 _70520 _70521) = (term348 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term349 _70518 _70521 _70519 _70520) (term258 _70521) (term339 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445572 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term350 _70518 _70519 _70520 _70521) = (term351 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term352 _70520 _70519 _70518 _70521) (term258 _70521) (term337 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445579 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term353 _70518 _70519 _70520 _70521) = (term354 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term355 _70520 _70521 _70518 _70519) (term258 _70521) (term356 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445582 (_70520 : int) (_70519 : int) (_70518 : int) (_70521 : int) : (term357 _70520 _70519 _70518 _70521) = (term357 _70520 _70519 _70518 _70521).
Proof. exact (eq_refl (term357 _70520 _70519 _70518 _70521)). Qed.
Lemma lem5445583 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term351 _70518 _70519 _70520 _70521) = (term358 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445582 _70520 _70519 _70518 _70521) (@lem5445579 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445584 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term350 _70518 _70519 _70520 _70521) = (term358 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445572 _70518 _70519 _70520 _70521) (@lem5445583 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445587 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term359 _70518 _70521 _70519 _70520) = (term359 _70518 _70521 _70519 _70520).
Proof. exact (eq_refl (term359 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445588 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term348 _70518 _70519 _70520 _70521) = (term360 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445587 _70518 _70521 _70519 _70520) (@lem5445584 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445589 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term347 _70518 _70519 _70520 _70521) = (term360 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445571 _70518 _70519 _70520 _70521) (@lem5445588 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445591 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term361 _70518 _70519 _70520 _70521) = (term362 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445590) (@lem5445589 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445592 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term345 _70518 _70519 _70520 _70521) = (term363 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445591 _70518 _70519 _70520 _70521) (@lem5445570 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445593 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term344 _70518 _70519 _70520 _70521) = (term363 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445569 _70518 _70519 _70520 _70521) (@lem5445592 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445594 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term329 _70518 _70519 _70520 _70521) = (term363 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445568 _70518 _70519 _70520 _70521) (@lem5445593 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445597 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (eq_refl (term328 _70520)). Qed.
Lemma lem5445598 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term330 _70518 _70519 _70520 _70521) = (term364 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445597 _70520) (@lem5445594 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445599 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term364 _70518 _70519 _70520 _70521) = (term365 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term360 _70518 _70519 _70520 _70521) (term258 _70520) (term346 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445600 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term366 _70518 _70519 _70520 _70521) = (term366 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term366 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445601 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term367 _70518 _70519 _70520 _70521) = (term368 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term369 _70518 _70521 _70519 _70520) (term258 _70520) (term358 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445602 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term370 _70518 _70519 _70520 _70521) = (term371 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term372 _70520 _70519 _70518 _70521) (term258 _70520) (term354 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445609 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term373 _70518 _70519 _70520 _70521) = (term374 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term375 _70520 _70521 _70518 _70519) (term258 _70520) (term376 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445612 (_70520 : int) (_70519 : int) (_70518 : int) (_70521 : int) : (term377 _70520 _70519 _70518 _70521) = (term377 _70520 _70519 _70518 _70521).
Proof. exact (eq_refl (term377 _70520 _70519 _70518 _70521)). Qed.
Lemma lem5445613 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term371 _70518 _70519 _70520 _70521) = (term378 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445612 _70520 _70519 _70518 _70521) (@lem5445609 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445614 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term370 _70518 _70519 _70520 _70521) = (term378 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445602 _70518 _70519 _70520 _70521) (@lem5445613 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445617 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term379 _70518 _70521 _70519 _70520) = (term379 _70518 _70521 _70519 _70520).
Proof. exact (eq_refl (term379 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445618 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term368 _70518 _70519 _70520 _70521) = (term380 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445617 _70518 _70521 _70519 _70520) (@lem5445614 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445619 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term367 _70518 _70519 _70520 _70521) = (term380 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445601 _70518 _70519 _70520 _70521) (@lem5445618 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445621 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term381 _70518 _70519 _70520 _70521) = (term382 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445620) (@lem5445619 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445622 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term365 _70518 _70519 _70520 _70521) = (term383 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445621 _70518 _70519 _70520 _70521) (@lem5445600 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445623 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term364 _70518 _70519 _70520 _70521) = (term383 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445599 _70518 _70519 _70520 _70521) (@lem5445622 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445624 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term330 _70518 _70519 _70520 _70521) = (term383 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445598 _70518 _70519 _70520 _70521) (@lem5445623 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445627 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (eq_refl (term328 _70519)). Qed.
Lemma lem5445628 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term331 _70518 _70519 _70520 _70521) = (term384 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445627 _70519) (@lem5445624 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445629 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term384 _70518 _70519 _70520 _70521) = (term385 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term380 _70518 _70519 _70520 _70521) (term258 _70519) (term366 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445630 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term386 _70518 _70519 _70520 _70521) = (term386 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term386 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445631 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term387 _70518 _70519 _70520 _70521) = (term388 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term389 _70518 _70521 _70519 _70520) (term258 _70519) (term378 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445632 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term390 _70518 _70519 _70520 _70521) = (term391 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term392 _70520 _70519 _70518 _70521) (term258 _70519) (term374 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445639 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term393 _70518 _70519 _70520 _70521) = (term394 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term395 _70520 _70521 _70518 _70519) (term258 _70519) (term396 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445642 (_70520 : int) (_70519 : int) (_70518 : int) (_70521 : int) : (term397 _70520 _70519 _70518 _70521) = (term397 _70520 _70519 _70518 _70521).
Proof. exact (eq_refl (term397 _70520 _70519 _70518 _70521)). Qed.
Lemma lem5445643 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term391 _70518 _70519 _70520 _70521) = (term398 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445642 _70520 _70519 _70518 _70521) (@lem5445639 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445644 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term390 _70518 _70519 _70520 _70521) = (term398 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445632 _70518 _70519 _70520 _70521) (@lem5445643 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445647 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term399 _70518 _70521 _70519 _70520) = (term399 _70518 _70521 _70519 _70520).
Proof. exact (eq_refl (term399 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445648 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term388 _70518 _70519 _70520 _70521) = (term400 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445647 _70518 _70521 _70519 _70520) (@lem5445644 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445649 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term387 _70518 _70519 _70520 _70521) = (term400 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445631 _70518 _70519 _70520 _70521) (@lem5445648 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445651 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term401 _70518 _70519 _70520 _70521) = (term402 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445650) (@lem5445649 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445652 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term385 _70518 _70519 _70520 _70521) = (term403 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445651 _70518 _70519 _70520 _70521) (@lem5445630 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445653 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term384 _70518 _70519 _70520 _70521) = (term403 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445629 _70518 _70519 _70520 _70521) (@lem5445652 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445654 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term331 _70518 _70519 _70520 _70521) = (term403 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445628 _70518 _70519 _70520 _70521) (@lem5445653 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445657 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (eq_refl (term328 _70518)). Qed.
Lemma lem5445658 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term332 _70518 _70519 _70520 _70521) = (term404 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445657 _70518) (@lem5445654 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445659 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term404 _70518 _70519 _70520 _70521) = (term405 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term400 _70518 _70519 _70520 _70521) (term258 _70518) (term386 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445660 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term406 _70518 _70519 _70520 _70521) = (term406 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term406 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445661 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term407 _70518 _70519 _70520 _70521) = (term408 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term409 _70518 _70521 _70519 _70520) (term258 _70518) (term398 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445662 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term410 _70518 _70519 _70520 _70521) = (term411 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term412 _70520 _70519 _70518 _70521) (term258 _70518) (term394 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445669 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term413 _70518 _70519 _70520 _70521) = (term414 _70518 _70519 _70520 _70521).
Proof. exact (@lem19158 (term415 _70520 _70521 _70518 _70519) (term258 _70518) (term416 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445672 (_70520 : int) (_70519 : int) (_70518 : int) (_70521 : int) : (term417 _70520 _70519 _70518 _70521) = (term417 _70520 _70519 _70518 _70521).
Proof. exact (eq_refl (term417 _70520 _70519 _70518 _70521)). Qed.
Lemma lem5445673 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term411 _70518 _70519 _70520 _70521) = (term418 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445672 _70520 _70519 _70518 _70521) (@lem5445669 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445674 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term410 _70518 _70519 _70520 _70521) = (term418 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445662 _70518 _70519 _70520 _70521) (@lem5445673 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445677 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term419 _70518 _70521 _70519 _70520) = (term419 _70518 _70521 _70519 _70520).
Proof. exact (eq_refl (term419 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445678 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term408 _70518 _70519 _70520 _70521) = (term420 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445677 _70518 _70521 _70519 _70520) (@lem5445674 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445679 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term407 _70518 _70519 _70520 _70521) = (term420 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445661 _70518 _70519 _70520 _70521) (@lem5445678 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5445681 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term421 _70518 _70519 _70520 _70521) = (term422 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445680) (@lem5445679 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445682 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term405 _70518 _70519 _70520 _70521) = (term423 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445681 _70518 _70519 _70520 _70521) (@lem5445660 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445683 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term404 _70518 _70519 _70520 _70521) = (term423 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445659 _70518 _70519 _70520 _70521) (@lem5445682 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445684 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term332 _70518 _70519 _70520 _70521) = (term423 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445658 _70518 _70519 _70520 _70521) (@lem5445683 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445685 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term230 _70518 _70519 _70520 _70521) = (term423 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445499 _70518 _70519 _70520 _70521) (@lem5445684 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445687 (x : real) (a : real) (y : real) (r : real) : (term424 x y a r) = (term425 x a y r).
Proof. exact (proj1 (@lem1482685 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445688 (_70518 : int) (_70519 : int) (_70521 : int) (_70520 : int) : (term266 _70518 _70520 _70519 _70521) = (term426 _70518 _70519 _70521 _70520).
Proof. exact (@lem5445687 (real_of_int _70518) (term181 _70519 _70521) (real_of_int _70520) term170). Qed.
Lemma lem5445705 (_70520 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70520) = (term428 _70520 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70520) (term181 _70519 _70521)). Qed.
Lemma lem5445706 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445707 (_70520 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70520) = (term430 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445706) (@lem5445705 _70520 _70519 _70521)). Qed.
Lemma lem5445708 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445709 (_70520 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70520) = (term432 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445707 _70520 _70519 _70521) (@lem5445708)). Qed.
Lemma lem5445726 (_70518 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70518) = (term428 _70518 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70518) (term181 _70519 _70521)). Qed.
Lemma lem5445727 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445728 (_70518 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70518) = (term430 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5445727) (@lem5445726 _70518 _70519 _70521)). Qed.
Lemma lem5445729 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445730 (_70518 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70518) = (term432 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5445728 _70518 _70519 _70521) (@lem5445729)). Qed.
Lemma lem5445731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445732 (_70518 : int) (_70519 : int) (_70521 : int) : (term433 _70519 _70521 _70518) = (term434 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5445731) (@lem5445730 _70518 _70519 _70521)). Qed.
Lemma lem5445733 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term426 _70518 _70519 _70521 _70520) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445732 _70518 _70519 _70521) (@lem5445709 _70520 _70519 _70521)). Qed.
Lemma lem5445734 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445688 _70518 _70519 _70521 _70520) (@lem5445733 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445736 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445775 (_70519 : int) (_70518 : int) (_70521 : int) : (term432 _70518 _70519 _70521) = (term438 _70519 _70518 _70521).
Proof. exact (@lem5445736 (real_of_int _70519) (term285 _70518) (real_of_int _70521) term170). Qed.
Lemma lem5445776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445777 (_70519 : int) (_70518 : int) (_70521 : int) : (term434 _70518 _70519 _70521) = (term439 _70519 _70518 _70521).
Proof. exact (MK_COMB (@lem5445776) (@lem5445775 _70519 _70518 _70521)). Qed.
Lemma lem5445779 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445780 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term438 _70519 _70520 _70521).
Proof. exact (@lem5445779 (real_of_int _70519) (term285 _70520) (real_of_int _70521) term170). Qed.
Lemma lem5445797 (_70520 : int) (_70521 : int) : (term318 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (eq_refl (term318 _70520 _70521)). Qed.
Lemma lem5445810 (_70519 : int) (_70520 : int) : (term316 _70520 _70519) = (term312 _70519 _70520).
Proof. exact (@lem1982761 (real_of_int _70519) (term285 _70520)). Qed.
Lemma lem5445811 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445812 (_70519 : int) (_70520 : int) : (term317 _70520 _70519) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5445811) (@lem5445810 _70519 _70520)). Qed.
Lemma lem5445813 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445814 (_70519 : int) (_70520 : int) : (term318 _70520 _70519) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5445812 _70519 _70520) (@lem5445813)). Qed.
Lemma lem5445815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445816 (_70519 : int) (_70520 : int) : (term319 _70520 _70519) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5445815) (@lem5445814 _70519 _70520)). Qed.
Lemma lem5445817 (_70519 : int) (_70520 : int) (_70521 : int) : (term438 _70519 _70520 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445816 _70519 _70520) (@lem5445797 _70520 _70521)). Qed.
Lemma lem5445818 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445780 _70519 _70520 _70521) (@lem5445817 _70519 _70520 _70521)). Qed.
Lemma lem5445819 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term435 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445777 _70519 _70518 _70521) (@lem5445818 _70519 _70520 _70521)). Qed.
Lemma lem5445820 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445734 _70518 _70520 _70519 _70521) (@lem5445819 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445822 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term296 _70518 _70520 _70519 _70521) = (term442 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445821) (@lem5445820 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445823 (_70519 : int) (_70520 : int) : (term288 _70519 _70520) = (term288 _70519 _70520).
Proof. exact (eq_refl (term288 _70519 _70520)). Qed.
Lemma lem5445824 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term349 _70518 _70521 _70519 _70520) = (term443 _70518 _70521 _70519 _70520).
Proof. exact (MK_COMB (@lem5445822 _70518 _70519 _70520 _70521) (@lem5445823 _70519 _70520)). Qed.
Lemma lem5445825 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (eq_refl (term328 _70521)). Qed.
Lemma lem5445826 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term369 _70518 _70521 _70519 _70520) = (term444 _70518 _70521 _70519 _70520).
Proof. exact (MK_COMB (@lem5445825 _70521) (@lem5445824 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445827 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (eq_refl (term328 _70520)). Qed.
Lemma lem5445828 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term389 _70518 _70521 _70519 _70520) = (term445 _70518 _70521 _70519 _70520).
Proof. exact (MK_COMB (@lem5445827 _70520) (@lem5445826 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445829 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (eq_refl (term328 _70519)). Qed.
Lemma lem5445830 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term409 _70518 _70521 _70519 _70520) = (term446 _70518 _70521 _70519 _70520).
Proof. exact (MK_COMB (@lem5445829 _70519) (@lem5445828 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445831 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (eq_refl (term328 _70518)). Qed.
Lemma lem5445834 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term447 _70518 _70521 _70519 _70520) = (term448 _70518 _70521 _70519 _70520).
Proof. exact (MK_COMB (@lem5445831 _70518) (@lem5445830 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5445836 (x : real) (a : real) (y : real) (r : real) : (term424 x y a r) = (term425 x a y r).
Proof. exact (proj1 (@lem1482685 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445837 (_70518 : int) (_70519 : int) (_70521 : int) (_70520 : int) : (term266 _70518 _70520 _70519 _70521) = (term426 _70518 _70519 _70521 _70520).
Proof. exact (@lem5445836 (real_of_int _70518) (term181 _70519 _70521) (real_of_int _70520) term170). Qed.
Lemma lem5445854 (_70520 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70520) = (term428 _70520 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70520) (term181 _70519 _70521)). Qed.
Lemma lem5445855 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445856 (_70520 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70520) = (term430 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445855) (@lem5445854 _70520 _70519 _70521)). Qed.
Lemma lem5445857 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445858 (_70520 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70520) = (term432 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445856 _70520 _70519 _70521) (@lem5445857)). Qed.
Lemma lem5445875 (_70518 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70518) = (term428 _70518 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70518) (term181 _70519 _70521)). Qed.
Lemma lem5445876 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445877 (_70518 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70518) = (term430 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5445876) (@lem5445875 _70518 _70519 _70521)). Qed.
Lemma lem5445878 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445879 (_70518 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70518) = (term432 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5445877 _70518 _70519 _70521) (@lem5445878)). Qed.
Lemma lem5445880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445881 (_70518 : int) (_70519 : int) (_70521 : int) : (term433 _70519 _70521 _70518) = (term434 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5445880) (@lem5445879 _70518 _70519 _70521)). Qed.
Lemma lem5445882 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term426 _70518 _70519 _70521 _70520) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5445881 _70518 _70519 _70521) (@lem5445858 _70520 _70519 _70521)). Qed.
Lemma lem5445883 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445837 _70518 _70519 _70521 _70520) (@lem5445882 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5445885 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445924 (_70519 : int) (_70518 : int) (_70521 : int) : (term432 _70518 _70519 _70521) = (term438 _70519 _70518 _70521).
Proof. exact (@lem5445885 (real_of_int _70519) (term285 _70518) (real_of_int _70521) term170). Qed.
Lemma lem5445925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445926 (_70519 : int) (_70518 : int) (_70521 : int) : (term434 _70518 _70519 _70521) = (term439 _70519 _70518 _70521).
Proof. exact (MK_COMB (@lem5445925) (@lem5445924 _70519 _70518 _70521)). Qed.
Lemma lem5445928 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445929 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term438 _70519 _70520 _70521).
Proof. exact (@lem5445928 (real_of_int _70519) (term285 _70520) (real_of_int _70521) term170). Qed.
Lemma lem5445946 (_70520 : int) (_70521 : int) : (term318 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (eq_refl (term318 _70520 _70521)). Qed.
Lemma lem5445959 (_70519 : int) (_70520 : int) : (term316 _70520 _70519) = (term312 _70519 _70520).
Proof. exact (@lem1982761 (real_of_int _70519) (term285 _70520)). Qed.
Lemma lem5445960 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5445961 (_70519 : int) (_70520 : int) : (term317 _70520 _70519) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5445960) (@lem5445959 _70519 _70520)). Qed.
Lemma lem5445962 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5445963 (_70519 : int) (_70520 : int) : (term318 _70520 _70519) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5445961 _70519 _70520) (@lem5445962)). Qed.
Lemma lem5445964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445965 (_70519 : int) (_70520 : int) : (term319 _70520 _70519) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5445964) (@lem5445963 _70519 _70520)). Qed.
Lemma lem5445966 (_70519 : int) (_70520 : int) (_70521 : int) : (term438 _70519 _70520 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445965 _70519 _70520) (@lem5445946 _70520 _70521)). Qed.
Lemma lem5445967 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445929 _70519 _70520 _70521) (@lem5445966 _70519 _70520 _70521)). Qed.
Lemma lem5445968 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term435 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445926 _70519 _70518 _70521) (@lem5445967 _70519 _70520 _70521)). Qed.
Lemma lem5445969 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5445883 _70518 _70520 _70519 _70521) (@lem5445968 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5445971 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term296 _70518 _70520 _70519 _70521) = (term442 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5445970) (@lem5445969 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5445972 (_70518 : int) (_70521 : int) : (term290 _70518 _70521) = (term290 _70518 _70521).
Proof. exact (eq_refl (term290 _70518 _70521)). Qed.
Lemma lem5445973 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) : (term352 _70520 _70519 _70518 _70521) = (term449 _70519 _70520 _70518 _70521).
Proof. exact (MK_COMB (@lem5445971 _70518 _70519 _70520 _70521) (@lem5445972 _70518 _70521)). Qed.
Lemma lem5445974 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (eq_refl (term328 _70521)). Qed.
Lemma lem5445975 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) : (term372 _70520 _70519 _70518 _70521) = (term450 _70519 _70520 _70518 _70521).
Proof. exact (MK_COMB (@lem5445974 _70521) (@lem5445973 _70519 _70520 _70518 _70521)). Qed.
Lemma lem5445976 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (eq_refl (term328 _70520)). Qed.
Lemma lem5445977 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) : (term392 _70520 _70519 _70518 _70521) = (term451 _70519 _70520 _70518 _70521).
Proof. exact (MK_COMB (@lem5445976 _70520) (@lem5445975 _70519 _70520 _70518 _70521)). Qed.
Lemma lem5445978 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (eq_refl (term328 _70519)). Qed.
Lemma lem5445979 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) : (term412 _70520 _70519 _70518 _70521) = (term452 _70519 _70520 _70518 _70521).
Proof. exact (MK_COMB (@lem5445978 _70519) (@lem5445977 _70519 _70520 _70518 _70521)). Qed.
Lemma lem5445980 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (eq_refl (term328 _70518)). Qed.
Lemma lem5445983 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) : (term453 _70520 _70519 _70518 _70521) = (term454 _70519 _70520 _70518 _70521).
Proof. exact (MK_COMB (@lem5445980 _70518) (@lem5445979 _70519 _70520 _70518 _70521)). Qed.
Lemma lem5445985 (x : real) (a : real) (y : real) (r : real) : (term424 x y a r) = (term425 x a y r).
Proof. exact (proj1 (@lem1482685 x a (@el real) y (@el real) r)). Qed.
Lemma lem5445986 (_70518 : int) (_70519 : int) (_70521 : int) (_70520 : int) : (term266 _70518 _70520 _70519 _70521) = (term426 _70518 _70519 _70521 _70520).
Proof. exact (@lem5445985 (real_of_int _70518) (term181 _70519 _70521) (real_of_int _70520) term170). Qed.
Lemma lem5446003 (_70520 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70520) = (term428 _70520 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70520) (term181 _70519 _70521)). Qed.
Lemma lem5446004 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446005 (_70520 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70520) = (term430 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446004) (@lem5446003 _70520 _70519 _70521)). Qed.
Lemma lem5446006 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446007 (_70520 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70520) = (term432 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446005 _70520 _70519 _70521) (@lem5446006)). Qed.
Lemma lem5446024 (_70518 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70518) = (term428 _70518 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70518) (term181 _70519 _70521)). Qed.
Lemma lem5446025 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446026 (_70518 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70518) = (term430 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446025) (@lem5446024 _70518 _70519 _70521)). Qed.
Lemma lem5446027 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446028 (_70518 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70518) = (term432 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446026 _70518 _70519 _70521) (@lem5446027)). Qed.
Lemma lem5446029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446030 (_70518 : int) (_70519 : int) (_70521 : int) : (term433 _70519 _70521 _70518) = (term434 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446029) (@lem5446028 _70518 _70519 _70521)). Qed.
Lemma lem5446031 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term426 _70518 _70519 _70521 _70520) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446030 _70518 _70519 _70521) (@lem5446007 _70520 _70519 _70521)). Qed.
Lemma lem5446032 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5445986 _70518 _70519 _70521 _70520) (@lem5446031 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5446034 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5446073 (_70519 : int) (_70518 : int) (_70521 : int) : (term432 _70518 _70519 _70521) = (term438 _70519 _70518 _70521).
Proof. exact (@lem5446034 (real_of_int _70519) (term285 _70518) (real_of_int _70521) term170). Qed.
Lemma lem5446074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446075 (_70519 : int) (_70518 : int) (_70521 : int) : (term434 _70518 _70519 _70521) = (term439 _70519 _70518 _70521).
Proof. exact (MK_COMB (@lem5446074) (@lem5446073 _70519 _70518 _70521)). Qed.
Lemma lem5446077 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5446078 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term438 _70519 _70520 _70521).
Proof. exact (@lem5446077 (real_of_int _70519) (term285 _70520) (real_of_int _70521) term170). Qed.
Lemma lem5446095 (_70520 : int) (_70521 : int) : (term318 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (eq_refl (term318 _70520 _70521)). Qed.
Lemma lem5446108 (_70519 : int) (_70520 : int) : (term316 _70520 _70519) = (term312 _70519 _70520).
Proof. exact (@lem1982761 (real_of_int _70519) (term285 _70520)). Qed.
Lemma lem5446109 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446110 (_70519 : int) (_70520 : int) : (term317 _70520 _70519) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5446109) (@lem5446108 _70519 _70520)). Qed.
Lemma lem5446111 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446112 (_70519 : int) (_70520 : int) : (term318 _70520 _70519) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5446110 _70519 _70520) (@lem5446111)). Qed.
Lemma lem5446113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446114 (_70519 : int) (_70520 : int) : (term319 _70520 _70519) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5446113) (@lem5446112 _70519 _70520)). Qed.
Lemma lem5446115 (_70519 : int) (_70520 : int) (_70521 : int) : (term438 _70519 _70520 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446114 _70519 _70520) (@lem5446095 _70520 _70521)). Qed.
Lemma lem5446116 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446078 _70519 _70520 _70521) (@lem5446115 _70519 _70520 _70521)). Qed.
Lemma lem5446117 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term435 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446075 _70519 _70518 _70521) (@lem5446116 _70519 _70520 _70521)). Qed.
Lemma lem5446118 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446032 _70518 _70520 _70519 _70521) (@lem5446117 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446120 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term296 _70518 _70520 _70519 _70521) = (term442 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446119) (@lem5446118 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446121 (_70518 : int) (_70519 : int) : (term290 _70518 _70519) = (term290 _70518 _70519).
Proof. exact (eq_refl (term290 _70518 _70519)). Qed.
Lemma lem5446122 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) : (term355 _70520 _70521 _70518 _70519) = (term455 _70520 _70521 _70518 _70519).
Proof. exact (MK_COMB (@lem5446120 _70518 _70519 _70520 _70521) (@lem5446121 _70518 _70519)). Qed.
Lemma lem5446123 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (eq_refl (term328 _70521)). Qed.
Lemma lem5446124 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) : (term375 _70520 _70521 _70518 _70519) = (term456 _70520 _70521 _70518 _70519).
Proof. exact (MK_COMB (@lem5446123 _70521) (@lem5446122 _70520 _70521 _70518 _70519)). Qed.
Lemma lem5446125 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (eq_refl (term328 _70520)). Qed.
Lemma lem5446126 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) : (term395 _70520 _70521 _70518 _70519) = (term457 _70520 _70521 _70518 _70519).
Proof. exact (MK_COMB (@lem5446125 _70520) (@lem5446124 _70520 _70521 _70518 _70519)). Qed.
Lemma lem5446127 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (eq_refl (term328 _70519)). Qed.
Lemma lem5446128 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) : (term415 _70520 _70521 _70518 _70519) = (term458 _70520 _70521 _70518 _70519).
Proof. exact (MK_COMB (@lem5446127 _70519) (@lem5446126 _70520 _70521 _70518 _70519)). Qed.
Lemma lem5446129 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (eq_refl (term328 _70518)). Qed.
Lemma lem5446132 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) : (term459 _70520 _70521 _70518 _70519) = (term460 _70520 _70521 _70518 _70519).
Proof. exact (MK_COMB (@lem5446129 _70518) (@lem5446128 _70520 _70521 _70518 _70519)). Qed.
Lemma lem5446134 (x : real) (a : real) (y : real) (r : real) : (term424 x y a r) = (term425 x a y r).
Proof. exact (proj1 (@lem1482685 x a (@el real) y (@el real) r)). Qed.
Lemma lem5446135 (_70518 : int) (_70519 : int) (_70521 : int) (_70520 : int) : (term266 _70518 _70520 _70519 _70521) = (term426 _70518 _70519 _70521 _70520).
Proof. exact (@lem5446134 (real_of_int _70518) (term181 _70519 _70521) (real_of_int _70520) term170). Qed.
Lemma lem5446152 (_70520 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70520) = (term428 _70520 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70520) (term181 _70519 _70521)). Qed.
Lemma lem5446153 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446154 (_70520 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70520) = (term430 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446153) (@lem5446152 _70520 _70519 _70521)). Qed.
Lemma lem5446155 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446156 (_70520 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70520) = (term432 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446154 _70520 _70519 _70521) (@lem5446155)). Qed.
Lemma lem5446173 (_70518 : int) (_70519 : int) (_70521 : int) : (term427 _70519 _70521 _70518) = (term428 _70518 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70518) (term181 _70519 _70521)). Qed.
Lemma lem5446174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446175 (_70518 : int) (_70519 : int) (_70521 : int) : (term429 _70519 _70521 _70518) = (term430 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446174) (@lem5446173 _70518 _70519 _70521)). Qed.
Lemma lem5446176 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446177 (_70518 : int) (_70519 : int) (_70521 : int) : (term431 _70519 _70521 _70518) = (term432 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446175 _70518 _70519 _70521) (@lem5446176)). Qed.
Lemma lem5446178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446179 (_70518 : int) (_70519 : int) (_70521 : int) : (term433 _70519 _70521 _70518) = (term434 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446178) (@lem5446177 _70518 _70519 _70521)). Qed.
Lemma lem5446180 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term426 _70518 _70519 _70521 _70520) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446179 _70518 _70519 _70521) (@lem5446156 _70520 _70519 _70521)). Qed.
Lemma lem5446181 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term435 _70518 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5446135 _70518 _70519 _70521 _70520) (@lem5446180 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5446183 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5446222 (_70519 : int) (_70518 : int) (_70521 : int) : (term432 _70518 _70519 _70521) = (term438 _70519 _70518 _70521).
Proof. exact (@lem5446183 (real_of_int _70519) (term285 _70518) (real_of_int _70521) term170). Qed.
Lemma lem5446223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446224 (_70519 : int) (_70518 : int) (_70521 : int) : (term434 _70518 _70519 _70521) = (term439 _70519 _70518 _70521).
Proof. exact (MK_COMB (@lem5446223) (@lem5446222 _70519 _70518 _70521)). Qed.
Lemma lem5446226 (x : real) (a : real) (y : real) (r : real) : (term436 a x y r) = (term437 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5446227 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term438 _70519 _70520 _70521).
Proof. exact (@lem5446226 (real_of_int _70519) (term285 _70520) (real_of_int _70521) term170). Qed.
Lemma lem5446244 (_70520 : int) (_70521 : int) : (term318 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (eq_refl (term318 _70520 _70521)). Qed.
Lemma lem5446257 (_70519 : int) (_70520 : int) : (term316 _70520 _70519) = (term312 _70519 _70520).
Proof. exact (@lem1982761 (real_of_int _70519) (term285 _70520)). Qed.
Lemma lem5446258 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446259 (_70519 : int) (_70520 : int) : (term317 _70520 _70519) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5446258) (@lem5446257 _70519 _70520)). Qed.
Lemma lem5446260 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446261 (_70519 : int) (_70520 : int) : (term318 _70520 _70519) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5446259 _70519 _70520) (@lem5446260)). Qed.
Lemma lem5446262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446263 (_70519 : int) (_70520 : int) : (term319 _70520 _70519) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5446262) (@lem5446261 _70519 _70520)). Qed.
Lemma lem5446264 (_70519 : int) (_70520 : int) (_70521 : int) : (term438 _70519 _70520 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446263 _70519 _70520) (@lem5446244 _70520 _70521)). Qed.
Lemma lem5446265 (_70519 : int) (_70520 : int) (_70521 : int) : (term432 _70520 _70519 _70521) = (term440 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446227 _70519 _70520 _70521) (@lem5446264 _70519 _70520 _70521)). Qed.
Lemma lem5446266 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term435 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446224 _70519 _70518 _70521) (@lem5446265 _70519 _70520 _70521)). Qed.
Lemma lem5446267 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term266 _70518 _70520 _70519 _70521) = (term441 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446181 _70518 _70520 _70519 _70521) (@lem5446266 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446269 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term296 _70518 _70520 _70519 _70521) = (term442 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446268) (@lem5446267 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446270 (_70520 : int) (_70521 : int) : (term290 _70520 _70521) = (term290 _70520 _70521).
Proof. exact (eq_refl (term290 _70520 _70521)). Qed.
Lemma lem5446271 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term356 _70518 _70519 _70520 _70521) = (term461 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446269 _70518 _70519 _70520 _70521) (@lem5446270 _70520 _70521)). Qed.
Lemma lem5446272 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (eq_refl (term328 _70521)). Qed.
Lemma lem5446273 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term376 _70518 _70519 _70520 _70521) = (term462 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446272 _70521) (@lem5446271 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446274 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (eq_refl (term328 _70520)). Qed.
Lemma lem5446275 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term396 _70518 _70519 _70520 _70521) = (term463 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446274 _70520) (@lem5446273 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446276 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (eq_refl (term328 _70519)). Qed.
Lemma lem5446277 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term416 _70518 _70519 _70520 _70521) = (term464 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446276 _70519) (@lem5446275 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446278 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (eq_refl (term328 _70518)). Qed.
Lemma lem5446281 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term465 _70518 _70519 _70520 _70521) = (term466 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446278 _70518) (@lem5446277 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5446283 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) : (term467 _70520 _70521 _70518 _70519) = (term468 _70520 _70521 _70518 _70519).
Proof. exact (MK_COMB (@lem5446282) (@lem5446132 _70520 _70521 _70518 _70519)). Qed.
Lemma lem5446284 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term414 _70518 _70519 _70520 _70521) = (term469 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446283 _70520 _70521 _70518 _70519) (@lem5446281 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446285 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5446286 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) : (term417 _70520 _70519 _70518 _70521) = (term470 _70519 _70520 _70518 _70521).
Proof. exact (MK_COMB (@lem5446285) (@lem5445983 _70519 _70520 _70518 _70521)). Qed.
Lemma lem5446287 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term418 _70518 _70519 _70520 _70521) = (term471 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446286 _70519 _70520 _70518 _70521) (@lem5446284 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5446289 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) : (term419 _70518 _70521 _70519 _70520) = (term472 _70518 _70521 _70519 _70520).
Proof. exact (MK_COMB (@lem5446288) (@lem5445834 _70518 _70521 _70519 _70520)). Qed.
Lemma lem5446290 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term420 _70518 _70519 _70520 _70521) = (term473 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446289 _70518 _70521 _70519 _70520) (@lem5446287 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446292 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term474 _70519 _70521 _70518 _70520) = (term406 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term474 _70519 _70521 _70518 _70520)). Qed.
Lemma lem5446293 (_70519 : int) (_70521 : int) (_70518 : int) (_70520 : int) : (term406 _70518 _70519 _70520 _70521) = (term474 _70519 _70521 _70518 _70520).
Proof. exact (SYM (@lem5446292 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446294 (_70519 : int) (_70520 : int) (_70521 : int) (_70518 : int) : (term474 _70519 _70521 _70518 _70520) = (term475 _70519 _70520 _70521 _70518).
Proof. exact (@lem1483205 (real_of_int _70520) (term476 _70518 _70519 _70520 _70521) (real_of_int _70518)). Qed.
Lemma lem5446295 (_70519 : int) (_70520 : int) (_70521 : int) (_70518 : int) : (term406 _70518 _70519 _70520 _70521) = (term475 _70519 _70520 _70521 _70518).
Proof. exact (TRANS (@lem5446293 _70519 _70521 _70518 _70520) (@lem5446294 _70519 _70520 _70521 _70518)). Qed.
Lemma lem5446296 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term477 _70519 _70520 _70521 _70518) = (term478 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term477 _70519 _70520 _70521 _70518)). Qed.
Lemma lem5446297 (_70518 : int) (_70520 : int) : (term479 _70518 _70520) = (term479 _70518 _70520).
Proof. exact (eq_refl (term479 _70518 _70520)). Qed.
Lemma lem5446298 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term480 _70519 _70520 _70521 _70518) = (term481 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446297 _70518 _70520) (@lem5446296 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446299 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term482 _70518 _70519 _70521 _70520) = (term483 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term482 _70518 _70519 _70521 _70520)). Qed.
Lemma lem5446300 (_70520 : int) (_70518 : int) : (term484 _70520 _70518) = (term484 _70520 _70518).
Proof. exact (eq_refl (term484 _70520 _70518)). Qed.
Lemma lem5446301 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term485 _70518 _70519 _70521 _70520) = (term486 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446300 _70520 _70518) (@lem5446299 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5446303 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term487 _70518 _70519 _70521 _70520) = (term488 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446302) (@lem5446301 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446304 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term475 _70519 _70520 _70521 _70518) = (term489 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446303 _70518 _70519 _70520 _70521) (@lem5446298 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446305 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term490 _70518 _70519 _70520 _70521) = (term490 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term490 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446306 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : ((term406 _70518 _70519 _70520 _70521) = (term475 _70519 _70520 _70521 _70518)) = ((term406 _70518 _70519 _70520 _70521) = (term489 _70518 _70519 _70520 _70521)).
Proof. exact (MK_COMB (@lem5446305 _70518 _70519 _70520 _70521) (@lem5446304 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446307 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term406 _70518 _70519 _70520 _70521) = (term489 _70518 _70519 _70520 _70521).
Proof. exact (EQ_MP (@lem5446306 _70518 _70519 _70520 _70521) (@lem5446295 _70519 _70520 _70521 _70518)). Qed.
Lemma lem5446308 (_70520 : int) (_70518 : int) : (term491 _70520 _70518) = (term310 _70520 _70518).
Proof. exact (@lem1988291 (real_of_int _70520) (real_of_int _70518)). Qed.
Lemma lem5446314 (_70520 : int) (_70518 : int) : (term311 _70520 _70518) = (term312 _70520 _70518).
Proof. exact (@lem1982792 (real_of_int _70520) (real_of_int _70518)). Qed.
Lemma lem5446319 (_70518 : int) (_70520 : int) : (term312 _70520 _70518) = (term316 _70518 _70520).
Proof. exact (@lem1982761 (term285 _70518) (real_of_int _70520)). Qed.
Lemma lem5446321 (_70518 : int) (_70520 : int) : (term311 _70520 _70518) = (term316 _70518 _70520).
Proof. exact (TRANS (@lem5446314 _70520 _70518) (@lem5446319 _70518 _70520)). Qed.
Lemma lem5446322 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446323 (_70518 : int) (_70520 : int) : (term313 _70520 _70518) = (term317 _70518 _70520).
Proof. exact (MK_COMB (@lem5446322) (@lem5446321 _70518 _70520)). Qed.
Lemma lem5446324 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446325 (_70518 : int) (_70520 : int) : (term310 _70520 _70518) = (term318 _70518 _70520).
Proof. exact (MK_COMB (@lem5446323 _70518 _70520) (@lem5446324)). Qed.
Lemma lem5446326 (_70518 : int) (_70520 : int) : (term491 _70520 _70518) = (term318 _70518 _70520).
Proof. exact (TRANS (@lem5446308 _70520 _70518) (@lem5446325 _70518 _70520)). Qed.
Lemma lem5446327 (_70518 : int) : (term258 _70518) = (term231 _70518).
Proof. exact (@lem1988291 (real_of_int _70518) term170). Qed.
Lemma lem5446333 (_70518 : int) : (term232 _70518) = (term233 _70518).
Proof. exact (@lem1982792 (real_of_int _70518) term170). Qed.
Lemma lem5446335 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446336 : term170 = term235.
Proof. exact (@lem5446335 (NUMERAL 0)). Qed.
Lemma lem5446338 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446339 : term238 = term239.
Proof. exact (@lem5446338 term193). Qed.
Lemma lem5446340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446341 : term240 = term241.
Proof. exact (MK_COMB (@lem5446340) (@lem5446339)). Qed.
Lemma lem5446342 : term242 = term243.
Proof. exact (MK_COMB (@lem5446341) (@lem5446336)). Qed.
Lemma lem5446343 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446345 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446346 : term247 = term248.
Proof. exact (@lem5446345 term193 term193). Qed.
Lemma lem5446347 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446348 : term250 = term193.
Proof. exact (EQ_MP (@lem5446347) (@lem940073)). Qed.
Lemma lem5446349 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446350 : term248 = term192.
Proof. exact (MK_COMB (@lem5446349) (@lem5446348)). Qed.
Lemma lem5446351 : term247 = term192.
Proof. exact (TRANS (@lem5446346) (@lem5446350)). Qed.
Lemma lem5446353 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446354 : term242 = term170.
Proof. exact (@lem5446353 term193). Qed.
Lemma lem5446355 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446356 : term252 = term253.
Proof. exact (MK_COMB (@lem5446355) (@lem5446354)). Qed.
Lemma lem5446357 : term244 = term235.
Proof. exact (MK_COMB (@lem5446356) (@lem5446351)). Qed.
Lemma lem5446358 : term243 = term235.
Proof. exact (TRANS (@lem5446343) (@lem5446357)). Qed.
Lemma lem5446359 : term242 = term235.
Proof. exact (TRANS (@lem5446342) (@lem5446358)). Qed.
Lemma lem5446361 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446362 : term235 = term170.
Proof. exact (@lem5446361 term170). Qed.
Lemma lem5446363 : term242 = term170.
Proof. exact (TRANS (@lem5446359) (@lem5446362)). Qed.
Lemma lem5446364 (_70518 : int) : (term194 _70518) = (term194 _70518).
Proof. exact (eq_refl (term194 _70518)). Qed.
Lemma lem5446365 (_70518 : int) : (term233 _70518) = (term255 _70518).
Proof. exact (MK_COMB (@lem5446364 _70518) (@lem5446363)). Qed.
Lemma lem5446366 (_70518 : int) : (term255 _70518) = (real_of_int _70518).
Proof. exact (@lem1982723 (real_of_int _70518)). Qed.
Lemma lem5446367 (_70518 : int) : (term233 _70518) = (real_of_int _70518).
Proof. exact (TRANS (@lem5446365 _70518) (@lem5446366 _70518)). Qed.
Lemma lem5446369 (_70518 : int) : (term232 _70518) = (real_of_int _70518).
Proof. exact (TRANS (@lem5446333 _70518) (@lem5446367 _70518)). Qed.
Lemma lem5446370 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446371 (_70518 : int) : (term256 _70518) = (term257 _70518).
Proof. exact (MK_COMB (@lem5446370) (@lem5446369 _70518)). Qed.
Lemma lem5446372 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446373 (_70518 : int) : (term231 _70518) = (term258 _70518).
Proof. exact (MK_COMB (@lem5446371 _70518) (@lem5446372)). Qed.
Lemma lem5446374 (_70518 : int) : (term258 _70518) = (term258 _70518).
Proof. exact (TRANS (@lem5446327 _70518) (@lem5446373 _70518)). Qed.
Lemma lem5446375 (_70519 : int) : (term258 _70519) = (term231 _70519).
Proof. exact (@lem1988291 (real_of_int _70519) term170). Qed.
Lemma lem5446381 (_70519 : int) : (term232 _70519) = (term233 _70519).
Proof. exact (@lem1982792 (real_of_int _70519) term170). Qed.
Lemma lem5446383 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446384 : term170 = term235.
Proof. exact (@lem5446383 (NUMERAL 0)). Qed.
Lemma lem5446386 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446387 : term238 = term239.
Proof. exact (@lem5446386 term193). Qed.
Lemma lem5446388 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446389 : term240 = term241.
Proof. exact (MK_COMB (@lem5446388) (@lem5446387)). Qed.
Lemma lem5446390 : term242 = term243.
Proof. exact (MK_COMB (@lem5446389) (@lem5446384)). Qed.
Lemma lem5446391 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446393 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446394 : term247 = term248.
Proof. exact (@lem5446393 term193 term193). Qed.
Lemma lem5446395 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446396 : term250 = term193.
Proof. exact (EQ_MP (@lem5446395) (@lem940073)). Qed.
Lemma lem5446397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446398 : term248 = term192.
Proof. exact (MK_COMB (@lem5446397) (@lem5446396)). Qed.
Lemma lem5446399 : term247 = term192.
Proof. exact (TRANS (@lem5446394) (@lem5446398)). Qed.
Lemma lem5446401 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446402 : term242 = term170.
Proof. exact (@lem5446401 term193). Qed.
Lemma lem5446403 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446404 : term252 = term253.
Proof. exact (MK_COMB (@lem5446403) (@lem5446402)). Qed.
Lemma lem5446405 : term244 = term235.
Proof. exact (MK_COMB (@lem5446404) (@lem5446399)). Qed.
Lemma lem5446406 : term243 = term235.
Proof. exact (TRANS (@lem5446391) (@lem5446405)). Qed.
Lemma lem5446407 : term242 = term235.
Proof. exact (TRANS (@lem5446390) (@lem5446406)). Qed.
Lemma lem5446409 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446410 : term235 = term170.
Proof. exact (@lem5446409 term170). Qed.
Lemma lem5446411 : term242 = term170.
Proof. exact (TRANS (@lem5446407) (@lem5446410)). Qed.
Lemma lem5446412 (_70519 : int) : (term194 _70519) = (term194 _70519).
Proof. exact (eq_refl (term194 _70519)). Qed.
Lemma lem5446413 (_70519 : int) : (term233 _70519) = (term255 _70519).
Proof. exact (MK_COMB (@lem5446412 _70519) (@lem5446411)). Qed.
Lemma lem5446414 (_70519 : int) : (term255 _70519) = (real_of_int _70519).
Proof. exact (@lem1982723 (real_of_int _70519)). Qed.
Lemma lem5446415 (_70519 : int) : (term233 _70519) = (real_of_int _70519).
Proof. exact (TRANS (@lem5446413 _70519) (@lem5446414 _70519)). Qed.
Lemma lem5446417 (_70519 : int) : (term232 _70519) = (real_of_int _70519).
Proof. exact (TRANS (@lem5446381 _70519) (@lem5446415 _70519)). Qed.
Lemma lem5446418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446419 (_70519 : int) : (term256 _70519) = (term257 _70519).
Proof. exact (MK_COMB (@lem5446418) (@lem5446417 _70519)). Qed.
Lemma lem5446420 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446421 (_70519 : int) : (term231 _70519) = (term258 _70519).
Proof. exact (MK_COMB (@lem5446419 _70519) (@lem5446420)). Qed.
Lemma lem5446422 (_70519 : int) : (term258 _70519) = (term258 _70519).
Proof. exact (TRANS (@lem5446375 _70519) (@lem5446421 _70519)). Qed.
Lemma lem5446423 (_70520 : int) : (term258 _70520) = (term231 _70520).
Proof. exact (@lem1988291 (real_of_int _70520) term170). Qed.
Lemma lem5446429 (_70520 : int) : (term232 _70520) = (term233 _70520).
Proof. exact (@lem1982792 (real_of_int _70520) term170). Qed.
Lemma lem5446431 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446432 : term170 = term235.
Proof. exact (@lem5446431 (NUMERAL 0)). Qed.
Lemma lem5446434 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446435 : term238 = term239.
Proof. exact (@lem5446434 term193). Qed.
Lemma lem5446436 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446437 : term240 = term241.
Proof. exact (MK_COMB (@lem5446436) (@lem5446435)). Qed.
Lemma lem5446438 : term242 = term243.
Proof. exact (MK_COMB (@lem5446437) (@lem5446432)). Qed.
Lemma lem5446439 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446441 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446442 : term247 = term248.
Proof. exact (@lem5446441 term193 term193). Qed.
Lemma lem5446443 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446444 : term250 = term193.
Proof. exact (EQ_MP (@lem5446443) (@lem940073)). Qed.
Lemma lem5446445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446446 : term248 = term192.
Proof. exact (MK_COMB (@lem5446445) (@lem5446444)). Qed.
Lemma lem5446447 : term247 = term192.
Proof. exact (TRANS (@lem5446442) (@lem5446446)). Qed.
Lemma lem5446449 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446450 : term242 = term170.
Proof. exact (@lem5446449 term193). Qed.
Lemma lem5446451 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446452 : term252 = term253.
Proof. exact (MK_COMB (@lem5446451) (@lem5446450)). Qed.
Lemma lem5446453 : term244 = term235.
Proof. exact (MK_COMB (@lem5446452) (@lem5446447)). Qed.
Lemma lem5446454 : term243 = term235.
Proof. exact (TRANS (@lem5446439) (@lem5446453)). Qed.
Lemma lem5446455 : term242 = term235.
Proof. exact (TRANS (@lem5446438) (@lem5446454)). Qed.
Lemma lem5446457 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446458 : term235 = term170.
Proof. exact (@lem5446457 term170). Qed.
Lemma lem5446459 : term242 = term170.
Proof. exact (TRANS (@lem5446455) (@lem5446458)). Qed.
Lemma lem5446460 (_70520 : int) : (term194 _70520) = (term194 _70520).
Proof. exact (eq_refl (term194 _70520)). Qed.
Lemma lem5446461 (_70520 : int) : (term233 _70520) = (term255 _70520).
Proof. exact (MK_COMB (@lem5446460 _70520) (@lem5446459)). Qed.
Lemma lem5446462 (_70520 : int) : (term255 _70520) = (real_of_int _70520).
Proof. exact (@lem1982723 (real_of_int _70520)). Qed.
Lemma lem5446463 (_70520 : int) : (term233 _70520) = (real_of_int _70520).
Proof. exact (TRANS (@lem5446461 _70520) (@lem5446462 _70520)). Qed.
Lemma lem5446465 (_70520 : int) : (term232 _70520) = (real_of_int _70520).
Proof. exact (TRANS (@lem5446429 _70520) (@lem5446463 _70520)). Qed.
Lemma lem5446466 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446467 (_70520 : int) : (term256 _70520) = (term257 _70520).
Proof. exact (MK_COMB (@lem5446466) (@lem5446465 _70520)). Qed.
Lemma lem5446468 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446469 (_70520 : int) : (term231 _70520) = (term258 _70520).
Proof. exact (MK_COMB (@lem5446467 _70520) (@lem5446468)). Qed.
Lemma lem5446470 (_70520 : int) : (term258 _70520) = (term258 _70520).
Proof. exact (TRANS (@lem5446423 _70520) (@lem5446469 _70520)). Qed.
Lemma lem5446471 (_70521 : int) : (term258 _70521) = (term231 _70521).
Proof. exact (@lem1988291 (real_of_int _70521) term170). Qed.
Lemma lem5446477 (_70521 : int) : (term232 _70521) = (term233 _70521).
Proof. exact (@lem1982792 (real_of_int _70521) term170). Qed.
Lemma lem5446479 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446480 : term170 = term235.
Proof. exact (@lem5446479 (NUMERAL 0)). Qed.
Lemma lem5446482 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446483 : term238 = term239.
Proof. exact (@lem5446482 term193). Qed.
Lemma lem5446484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446485 : term240 = term241.
Proof. exact (MK_COMB (@lem5446484) (@lem5446483)). Qed.
Lemma lem5446486 : term242 = term243.
Proof. exact (MK_COMB (@lem5446485) (@lem5446480)). Qed.
Lemma lem5446487 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446489 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446490 : term247 = term248.
Proof. exact (@lem5446489 term193 term193). Qed.
Lemma lem5446491 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446492 : term250 = term193.
Proof. exact (EQ_MP (@lem5446491) (@lem940073)). Qed.
Lemma lem5446493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446494 : term248 = term192.
Proof. exact (MK_COMB (@lem5446493) (@lem5446492)). Qed.
Lemma lem5446495 : term247 = term192.
Proof. exact (TRANS (@lem5446490) (@lem5446494)). Qed.
Lemma lem5446497 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446498 : term242 = term170.
Proof. exact (@lem5446497 term193). Qed.
Lemma lem5446499 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446500 : term252 = term253.
Proof. exact (MK_COMB (@lem5446499) (@lem5446498)). Qed.
Lemma lem5446501 : term244 = term235.
Proof. exact (MK_COMB (@lem5446500) (@lem5446495)). Qed.
Lemma lem5446502 : term243 = term235.
Proof. exact (TRANS (@lem5446487) (@lem5446501)). Qed.
Lemma lem5446503 : term242 = term235.
Proof. exact (TRANS (@lem5446486) (@lem5446502)). Qed.
Lemma lem5446505 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446506 : term235 = term170.
Proof. exact (@lem5446505 term170). Qed.
Lemma lem5446507 : term242 = term170.
Proof. exact (TRANS (@lem5446503) (@lem5446506)). Qed.
Lemma lem5446508 (_70521 : int) : (term194 _70521) = (term194 _70521).
Proof. exact (eq_refl (term194 _70521)). Qed.
Lemma lem5446509 (_70521 : int) : (term233 _70521) = (term255 _70521).
Proof. exact (MK_COMB (@lem5446508 _70521) (@lem5446507)). Qed.
Lemma lem5446510 (_70521 : int) : (term255 _70521) = (real_of_int _70521).
Proof. exact (@lem1982723 (real_of_int _70521)). Qed.
Lemma lem5446511 (_70521 : int) : (term233 _70521) = (real_of_int _70521).
Proof. exact (TRANS (@lem5446509 _70521) (@lem5446510 _70521)). Qed.
Lemma lem5446513 (_70521 : int) : (term232 _70521) = (real_of_int _70521).
Proof. exact (TRANS (@lem5446477 _70521) (@lem5446511 _70521)). Qed.
Lemma lem5446514 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446515 (_70521 : int) : (term256 _70521) = (term257 _70521).
Proof. exact (MK_COMB (@lem5446514) (@lem5446513 _70521)). Qed.
Lemma lem5446516 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446517 (_70521 : int) : (term231 _70521) = (term258 _70521).
Proof. exact (MK_COMB (@lem5446515 _70521) (@lem5446516)). Qed.
Lemma lem5446518 (_70521 : int) : (term258 _70521) = (term258 _70521).
Proof. exact (TRANS (@lem5446471 _70521) (@lem5446517 _70521)). Qed.
Lemma lem5446519 (_70520 : int) (_70519 : int) (_70521 : int) : (term492 _70520 _70519 _70521) = (term493 _70520 _70519 _70521).
Proof. exact (@lem1988291 (term494 _70520 _70519 _70521) term170). Qed.
Lemma lem5446547 (_70520 : int) (_70519 : int) (_70521 : int) : (term495 _70520 _70519 _70521) = (term496 _70520 _70519 _70521).
Proof. exact (@lem1982792 (term494 _70520 _70519 _70521) term170). Qed.
Lemma lem5446549 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446550 : term170 = term235.
Proof. exact (@lem5446549 (NUMERAL 0)). Qed.
Lemma lem5446552 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446553 : term238 = term239.
Proof. exact (@lem5446552 term193). Qed.
Lemma lem5446554 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446555 : term240 = term241.
Proof. exact (MK_COMB (@lem5446554) (@lem5446553)). Qed.
Lemma lem5446556 : term242 = term243.
Proof. exact (MK_COMB (@lem5446555) (@lem5446550)). Qed.
Lemma lem5446557 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446559 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446560 : term247 = term248.
Proof. exact (@lem5446559 term193 term193). Qed.
Lemma lem5446561 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446562 : term250 = term193.
Proof. exact (EQ_MP (@lem5446561) (@lem940073)). Qed.
Lemma lem5446563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446564 : term248 = term192.
Proof. exact (MK_COMB (@lem5446563) (@lem5446562)). Qed.
Lemma lem5446565 : term247 = term192.
Proof. exact (TRANS (@lem5446560) (@lem5446564)). Qed.
Lemma lem5446567 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446568 : term242 = term170.
Proof. exact (@lem5446567 term193). Qed.
Lemma lem5446569 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446570 : term252 = term253.
Proof. exact (MK_COMB (@lem5446569) (@lem5446568)). Qed.
Lemma lem5446571 : term244 = term235.
Proof. exact (MK_COMB (@lem5446570) (@lem5446565)). Qed.
Lemma lem5446572 : term243 = term235.
Proof. exact (TRANS (@lem5446557) (@lem5446571)). Qed.
Lemma lem5446573 : term242 = term235.
Proof. exact (TRANS (@lem5446556) (@lem5446572)). Qed.
Lemma lem5446575 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446576 : term235 = term170.
Proof. exact (@lem5446575 term170). Qed.
Lemma lem5446577 : term242 = term170.
Proof. exact (TRANS (@lem5446573) (@lem5446576)). Qed.
Lemma lem5446578 (_70520 : int) (_70519 : int) (_70521 : int) : (term497 _70520 _70519 _70521) = (term497 _70520 _70519 _70521).
Proof. exact (eq_refl (term497 _70520 _70519 _70521)). Qed.
Lemma lem5446579 (_70520 : int) (_70519 : int) (_70521 : int) : (term496 _70520 _70519 _70521) = (term498 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446578 _70520 _70519 _70521) (@lem5446577)). Qed.
Lemma lem5446580 (_70520 : int) (_70519 : int) (_70521 : int) : (term498 _70520 _70519 _70521) = (term494 _70520 _70519 _70521).
Proof. exact (@lem1982723 (term494 _70520 _70519 _70521)). Qed.
Lemma lem5446581 (_70520 : int) (_70519 : int) (_70521 : int) : (term496 _70520 _70519 _70521) = (term494 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5446579 _70520 _70519 _70521) (@lem5446580 _70520 _70519 _70521)). Qed.
Lemma lem5446583 (_70520 : int) (_70519 : int) (_70521 : int) : (term495 _70520 _70519 _70521) = (term494 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5446547 _70520 _70519 _70521) (@lem5446581 _70520 _70519 _70521)). Qed.
Lemma lem5446584 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446585 (_70520 : int) (_70519 : int) (_70521 : int) : (term499 _70520 _70519 _70521) = (term500 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446584) (@lem5446583 _70520 _70519 _70521)). Qed.
Lemma lem5446586 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446587 (_70520 : int) (_70519 : int) (_70521 : int) : (term493 _70520 _70519 _70521) = (term492 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446585 _70520 _70519 _70521) (@lem5446586)). Qed.
Lemma lem5446588 (_70520 : int) (_70519 : int) (_70521 : int) : (term492 _70520 _70519 _70521) = (term492 _70520 _70519 _70521).
Proof. exact (TRANS (@lem5446519 _70520 _70519 _70521) (@lem5446587 _70520 _70519 _70521)). Qed.
Lemma lem5446589 (_70519 : int) (_70520 : int) : (term315 _70519 _70520) = (term501 _70519 _70520).
Proof. exact (@lem1988291 (term312 _70519 _70520) term170). Qed.
Lemma lem5446607 (_70519 : int) (_70520 : int) : (term502 _70519 _70520) = (term503 _70519 _70520).
Proof. exact (@lem1982792 (term312 _70519 _70520) term170). Qed.
Lemma lem5446609 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446610 : term170 = term235.
Proof. exact (@lem5446609 (NUMERAL 0)). Qed.
Lemma lem5446612 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446613 : term238 = term239.
Proof. exact (@lem5446612 term193). Qed.
Lemma lem5446614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446615 : term240 = term241.
Proof. exact (MK_COMB (@lem5446614) (@lem5446613)). Qed.
Lemma lem5446616 : term242 = term243.
Proof. exact (MK_COMB (@lem5446615) (@lem5446610)). Qed.
Lemma lem5446617 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446619 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446620 : term247 = term248.
Proof. exact (@lem5446619 term193 term193). Qed.
Lemma lem5446621 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446622 : term250 = term193.
Proof. exact (EQ_MP (@lem5446621) (@lem940073)). Qed.
Lemma lem5446623 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446624 : term248 = term192.
Proof. exact (MK_COMB (@lem5446623) (@lem5446622)). Qed.
Lemma lem5446625 : term247 = term192.
Proof. exact (TRANS (@lem5446620) (@lem5446624)). Qed.
Lemma lem5446627 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446628 : term242 = term170.
Proof. exact (@lem5446627 term193). Qed.
Lemma lem5446629 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446630 : term252 = term253.
Proof. exact (MK_COMB (@lem5446629) (@lem5446628)). Qed.
Lemma lem5446631 : term244 = term235.
Proof. exact (MK_COMB (@lem5446630) (@lem5446625)). Qed.
Lemma lem5446632 : term243 = term235.
Proof. exact (TRANS (@lem5446617) (@lem5446631)). Qed.
Lemma lem5446633 : term242 = term235.
Proof. exact (TRANS (@lem5446616) (@lem5446632)). Qed.
Lemma lem5446635 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446636 : term235 = term170.
Proof. exact (@lem5446635 term170). Qed.
Lemma lem5446637 : term242 = term170.
Proof. exact (TRANS (@lem5446633) (@lem5446636)). Qed.
Lemma lem5446638 (_70519 : int) (_70520 : int) : (term504 _70519 _70520) = (term504 _70519 _70520).
Proof. exact (eq_refl (term504 _70519 _70520)). Qed.
Lemma lem5446639 (_70519 : int) (_70520 : int) : (term503 _70519 _70520) = (term505 _70519 _70520).
Proof. exact (MK_COMB (@lem5446638 _70519 _70520) (@lem5446637)). Qed.
Lemma lem5446640 (_70519 : int) (_70520 : int) : (term505 _70519 _70520) = (term312 _70519 _70520).
Proof. exact (@lem1982723 (term312 _70519 _70520)). Qed.
Lemma lem5446641 (_70519 : int) (_70520 : int) : (term503 _70519 _70520) = (term312 _70519 _70520).
Proof. exact (TRANS (@lem5446639 _70519 _70520) (@lem5446640 _70519 _70520)). Qed.
Lemma lem5446643 (_70519 : int) (_70520 : int) : (term502 _70519 _70520) = (term312 _70519 _70520).
Proof. exact (TRANS (@lem5446607 _70519 _70520) (@lem5446641 _70519 _70520)). Qed.
Lemma lem5446644 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446645 (_70519 : int) (_70520 : int) : (term506 _70519 _70520) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5446644) (@lem5446643 _70519 _70520)). Qed.
Lemma lem5446646 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446647 (_70519 : int) (_70520 : int) : (term501 _70519 _70520) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5446645 _70519 _70520) (@lem5446646)). Qed.
Lemma lem5446648 (_70519 : int) (_70520 : int) : (term315 _70519 _70520) = (term315 _70519 _70520).
Proof. exact (TRANS (@lem5446589 _70519 _70520) (@lem5446647 _70519 _70520)). Qed.
Lemma lem5446649 (_70518 : int) (_70521 : int) : (term318 _70518 _70521) = (term507 _70518 _70521).
Proof. exact (@lem1988291 (term316 _70518 _70521) term170). Qed.
Lemma lem5446667 (_70518 : int) (_70521 : int) : (term508 _70518 _70521) = (term509 _70518 _70521).
Proof. exact (@lem1982792 (term316 _70518 _70521) term170). Qed.
Lemma lem5446669 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446670 : term170 = term235.
Proof. exact (@lem5446669 (NUMERAL 0)). Qed.
Lemma lem5446672 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446673 : term238 = term239.
Proof. exact (@lem5446672 term193). Qed.
Lemma lem5446674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446675 : term240 = term241.
Proof. exact (MK_COMB (@lem5446674) (@lem5446673)). Qed.
Lemma lem5446676 : term242 = term243.
Proof. exact (MK_COMB (@lem5446675) (@lem5446670)). Qed.
Lemma lem5446677 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446679 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446680 : term247 = term248.
Proof. exact (@lem5446679 term193 term193). Qed.
Lemma lem5446681 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446682 : term250 = term193.
Proof. exact (EQ_MP (@lem5446681) (@lem940073)). Qed.
Lemma lem5446683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446684 : term248 = term192.
Proof. exact (MK_COMB (@lem5446683) (@lem5446682)). Qed.
Lemma lem5446685 : term247 = term192.
Proof. exact (TRANS (@lem5446680) (@lem5446684)). Qed.
Lemma lem5446687 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446688 : term242 = term170.
Proof. exact (@lem5446687 term193). Qed.
Lemma lem5446689 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446690 : term252 = term253.
Proof. exact (MK_COMB (@lem5446689) (@lem5446688)). Qed.
Lemma lem5446691 : term244 = term235.
Proof. exact (MK_COMB (@lem5446690) (@lem5446685)). Qed.
Lemma lem5446692 : term243 = term235.
Proof. exact (TRANS (@lem5446677) (@lem5446691)). Qed.
Lemma lem5446693 : term242 = term235.
Proof. exact (TRANS (@lem5446676) (@lem5446692)). Qed.
Lemma lem5446695 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446696 : term235 = term170.
Proof. exact (@lem5446695 term170). Qed.
Lemma lem5446697 : term242 = term170.
Proof. exact (TRANS (@lem5446693) (@lem5446696)). Qed.
Lemma lem5446698 (_70518 : int) (_70521 : int) : (term510 _70518 _70521) = (term510 _70518 _70521).
Proof. exact (eq_refl (term510 _70518 _70521)). Qed.
Lemma lem5446699 (_70518 : int) (_70521 : int) : (term509 _70518 _70521) = (term511 _70518 _70521).
Proof. exact (MK_COMB (@lem5446698 _70518 _70521) (@lem5446697)). Qed.
Lemma lem5446700 (_70518 : int) (_70521 : int) : (term511 _70518 _70521) = (term316 _70518 _70521).
Proof. exact (@lem1982723 (term316 _70518 _70521)). Qed.
Lemma lem5446701 (_70518 : int) (_70521 : int) : (term509 _70518 _70521) = (term316 _70518 _70521).
Proof. exact (TRANS (@lem5446699 _70518 _70521) (@lem5446700 _70518 _70521)). Qed.
Lemma lem5446703 (_70518 : int) (_70521 : int) : (term508 _70518 _70521) = (term316 _70518 _70521).
Proof. exact (TRANS (@lem5446667 _70518 _70521) (@lem5446701 _70518 _70521)). Qed.
Lemma lem5446704 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446705 (_70518 : int) (_70521 : int) : (term512 _70518 _70521) = (term317 _70518 _70521).
Proof. exact (MK_COMB (@lem5446704) (@lem5446703 _70518 _70521)). Qed.
Lemma lem5446706 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446707 (_70518 : int) (_70521 : int) : (term507 _70518 _70521) = (term318 _70518 _70521).
Proof. exact (MK_COMB (@lem5446705 _70518 _70521) (@lem5446706)). Qed.
Lemma lem5446708 (_70518 : int) (_70521 : int) : (term318 _70518 _70521) = (term318 _70518 _70521).
Proof. exact (TRANS (@lem5446649 _70518 _70521) (@lem5446707 _70518 _70521)). Qed.
Lemma lem5446709 (_70518 : int) (_70519 : int) : (term318 _70518 _70519) = (term507 _70518 _70519).
Proof. exact (@lem1988291 (term316 _70518 _70519) term170). Qed.
Lemma lem5446727 (_70518 : int) (_70519 : int) : (term508 _70518 _70519) = (term509 _70518 _70519).
Proof. exact (@lem1982792 (term316 _70518 _70519) term170). Qed.
Lemma lem5446729 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446730 : term170 = term235.
Proof. exact (@lem5446729 (NUMERAL 0)). Qed.
Lemma lem5446732 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446733 : term238 = term239.
Proof. exact (@lem5446732 term193). Qed.
Lemma lem5446734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446735 : term240 = term241.
Proof. exact (MK_COMB (@lem5446734) (@lem5446733)). Qed.
Lemma lem5446736 : term242 = term243.
Proof. exact (MK_COMB (@lem5446735) (@lem5446730)). Qed.
Lemma lem5446737 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446739 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446740 : term247 = term248.
Proof. exact (@lem5446739 term193 term193). Qed.
Lemma lem5446741 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446742 : term250 = term193.
Proof. exact (EQ_MP (@lem5446741) (@lem940073)). Qed.
Lemma lem5446743 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446744 : term248 = term192.
Proof. exact (MK_COMB (@lem5446743) (@lem5446742)). Qed.
Lemma lem5446745 : term247 = term192.
Proof. exact (TRANS (@lem5446740) (@lem5446744)). Qed.
Lemma lem5446747 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446748 : term242 = term170.
Proof. exact (@lem5446747 term193). Qed.
Lemma lem5446749 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446750 : term252 = term253.
Proof. exact (MK_COMB (@lem5446749) (@lem5446748)). Qed.
Lemma lem5446751 : term244 = term235.
Proof. exact (MK_COMB (@lem5446750) (@lem5446745)). Qed.
Lemma lem5446752 : term243 = term235.
Proof. exact (TRANS (@lem5446737) (@lem5446751)). Qed.
Lemma lem5446753 : term242 = term235.
Proof. exact (TRANS (@lem5446736) (@lem5446752)). Qed.
Lemma lem5446755 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446756 : term235 = term170.
Proof. exact (@lem5446755 term170). Qed.
Lemma lem5446757 : term242 = term170.
Proof. exact (TRANS (@lem5446753) (@lem5446756)). Qed.
Lemma lem5446758 (_70518 : int) (_70519 : int) : (term510 _70518 _70519) = (term510 _70518 _70519).
Proof. exact (eq_refl (term510 _70518 _70519)). Qed.
Lemma lem5446759 (_70518 : int) (_70519 : int) : (term509 _70518 _70519) = (term511 _70518 _70519).
Proof. exact (MK_COMB (@lem5446758 _70518 _70519) (@lem5446757)). Qed.
Lemma lem5446760 (_70518 : int) (_70519 : int) : (term511 _70518 _70519) = (term316 _70518 _70519).
Proof. exact (@lem1982723 (term316 _70518 _70519)). Qed.
Lemma lem5446761 (_70518 : int) (_70519 : int) : (term509 _70518 _70519) = (term316 _70518 _70519).
Proof. exact (TRANS (@lem5446759 _70518 _70519) (@lem5446760 _70518 _70519)). Qed.
Lemma lem5446763 (_70518 : int) (_70519 : int) : (term508 _70518 _70519) = (term316 _70518 _70519).
Proof. exact (TRANS (@lem5446727 _70518 _70519) (@lem5446761 _70518 _70519)). Qed.
Lemma lem5446764 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446765 (_70518 : int) (_70519 : int) : (term512 _70518 _70519) = (term317 _70518 _70519).
Proof. exact (MK_COMB (@lem5446764) (@lem5446763 _70518 _70519)). Qed.
Lemma lem5446766 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446767 (_70518 : int) (_70519 : int) : (term507 _70518 _70519) = (term318 _70518 _70519).
Proof. exact (MK_COMB (@lem5446765 _70518 _70519) (@lem5446766)). Qed.
Lemma lem5446768 (_70518 : int) (_70519 : int) : (term318 _70518 _70519) = (term318 _70518 _70519).
Proof. exact (TRANS (@lem5446709 _70518 _70519) (@lem5446767 _70518 _70519)). Qed.
Lemma lem5446769 (_70520 : int) (_70521 : int) : (term318 _70520 _70521) = (term507 _70520 _70521).
Proof. exact (@lem1988291 (term316 _70520 _70521) term170). Qed.
Lemma lem5446787 (_70520 : int) (_70521 : int) : (term508 _70520 _70521) = (term509 _70520 _70521).
Proof. exact (@lem1982792 (term316 _70520 _70521) term170). Qed.
Lemma lem5446789 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446790 : term170 = term235.
Proof. exact (@lem5446789 (NUMERAL 0)). Qed.
Lemma lem5446792 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446793 : term238 = term239.
Proof. exact (@lem5446792 term193). Qed.
Lemma lem5446794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446795 : term240 = term241.
Proof. exact (MK_COMB (@lem5446794) (@lem5446793)). Qed.
Lemma lem5446796 : term242 = term243.
Proof. exact (MK_COMB (@lem5446795) (@lem5446790)). Qed.
Lemma lem5446797 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446799 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446800 : term247 = term248.
Proof. exact (@lem5446799 term193 term193). Qed.
Lemma lem5446801 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446802 : term250 = term193.
Proof. exact (EQ_MP (@lem5446801) (@lem940073)). Qed.
Lemma lem5446803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446804 : term248 = term192.
Proof. exact (MK_COMB (@lem5446803) (@lem5446802)). Qed.
Lemma lem5446805 : term247 = term192.
Proof. exact (TRANS (@lem5446800) (@lem5446804)). Qed.
Lemma lem5446807 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446808 : term242 = term170.
Proof. exact (@lem5446807 term193). Qed.
Lemma lem5446809 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446810 : term252 = term253.
Proof. exact (MK_COMB (@lem5446809) (@lem5446808)). Qed.
Lemma lem5446811 : term244 = term235.
Proof. exact (MK_COMB (@lem5446810) (@lem5446805)). Qed.
Lemma lem5446812 : term243 = term235.
Proof. exact (TRANS (@lem5446797) (@lem5446811)). Qed.
Lemma lem5446813 : term242 = term235.
Proof. exact (TRANS (@lem5446796) (@lem5446812)). Qed.
Lemma lem5446815 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446816 : term235 = term170.
Proof. exact (@lem5446815 term170). Qed.
Lemma lem5446817 : term242 = term170.
Proof. exact (TRANS (@lem5446813) (@lem5446816)). Qed.
Lemma lem5446818 (_70520 : int) (_70521 : int) : (term510 _70520 _70521) = (term510 _70520 _70521).
Proof. exact (eq_refl (term510 _70520 _70521)). Qed.
Lemma lem5446819 (_70520 : int) (_70521 : int) : (term509 _70520 _70521) = (term511 _70520 _70521).
Proof. exact (MK_COMB (@lem5446818 _70520 _70521) (@lem5446817)). Qed.
Lemma lem5446820 (_70520 : int) (_70521 : int) : (term511 _70520 _70521) = (term316 _70520 _70521).
Proof. exact (@lem1982723 (term316 _70520 _70521)). Qed.
Lemma lem5446821 (_70520 : int) (_70521 : int) : (term509 _70520 _70521) = (term316 _70520 _70521).
Proof. exact (TRANS (@lem5446819 _70520 _70521) (@lem5446820 _70520 _70521)). Qed.
Lemma lem5446823 (_70520 : int) (_70521 : int) : (term508 _70520 _70521) = (term316 _70520 _70521).
Proof. exact (TRANS (@lem5446787 _70520 _70521) (@lem5446821 _70520 _70521)). Qed.
Lemma lem5446824 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446825 (_70520 : int) (_70521 : int) : (term512 _70520 _70521) = (term317 _70520 _70521).
Proof. exact (MK_COMB (@lem5446824) (@lem5446823 _70520 _70521)). Qed.
Lemma lem5446826 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446827 (_70520 : int) (_70521 : int) : (term507 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (MK_COMB (@lem5446825 _70520 _70521) (@lem5446826)). Qed.
Lemma lem5446828 (_70520 : int) (_70521 : int) : (term318 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (TRANS (@lem5446769 _70520 _70521) (@lem5446827 _70520 _70521)). Qed.
Lemma lem5446829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446830 (_70518 : int) (_70519 : int) : (term319 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5446829) (@lem5446768 _70518 _70519)). Qed.
Lemma lem5446831 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term320 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446830 _70518 _70519) (@lem5446828 _70520 _70521)). Qed.
Lemma lem5446832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446833 (_70518 : int) (_70521 : int) : (term319 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5446832) (@lem5446708 _70518 _70521)). Qed.
Lemma lem5446834 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term321 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446833 _70518 _70521) (@lem5446831 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446836 (_70519 : int) (_70520 : int) : (term322 _70519 _70520) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5446835) (@lem5446648 _70519 _70520)). Qed.
Lemma lem5446837 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term323 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446836 _70519 _70520) (@lem5446834 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446839 (_70520 : int) (_70519 : int) (_70521 : int) : (term513 _70520 _70519 _70521) = (term513 _70520 _70519 _70521).
Proof. exact (MK_COMB (@lem5446838) (@lem5446588 _70520 _70519 _70521)). Qed.
Lemma lem5446840 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term514 _70518 _70519 _70520 _70521) = (term514 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446839 _70520 _70519 _70521) (@lem5446837 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446842 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5446841) (@lem5446518 _70521)). Qed.
Lemma lem5446843 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term515 _70518 _70519 _70520 _70521) = (term515 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446842 _70521) (@lem5446840 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446845 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5446844) (@lem5446470 _70520)). Qed.
Lemma lem5446846 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term516 _70518 _70519 _70520 _70521) = (term516 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446845 _70520) (@lem5446843 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446848 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5446847) (@lem5446422 _70519)). Qed.
Lemma lem5446849 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term517 _70518 _70519 _70520 _70521) = (term517 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446848 _70519) (@lem5446846 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446851 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5446850) (@lem5446374 _70518)). Qed.
Lemma lem5446852 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term483 _70518 _70519 _70520 _70521) = (term483 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446851 _70518) (@lem5446849 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446854 (_70518 : int) (_70520 : int) : (term484 _70520 _70518) = (term319 _70518 _70520).
Proof. exact (MK_COMB (@lem5446853) (@lem5446326 _70518 _70520)). Qed.
Lemma lem5446855 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term486 _70518 _70519 _70520 _70521) = (term518 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446854 _70518 _70520) (@lem5446852 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446856 (_70518 : int) (_70520 : int) : (term519 _70518 _70520) = (term520 _70518 _70520).
Proof. exact (@lem1988289 (real_of_int _70518) (real_of_int _70520)). Qed.
Lemma lem5446869 (_70518 : int) (_70520 : int) : (term311 _70518 _70520) = (term312 _70518 _70520).
Proof. exact (@lem1982792 (real_of_int _70518) (real_of_int _70520)). Qed.
Lemma lem5446870 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5446871 (_70518 : int) (_70520 : int) : (term521 _70518 _70520) = (term522 _70518 _70520).
Proof. exact (MK_COMB (@lem5446870) (@lem5446869 _70518 _70520)). Qed.
Lemma lem5446872 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446873 (_70518 : int) (_70520 : int) : (term520 _70518 _70520) = (term523 _70518 _70520).
Proof. exact (MK_COMB (@lem5446871 _70518 _70520) (@lem5446872)). Qed.
Lemma lem5446874 (_70518 : int) (_70520 : int) : (term519 _70518 _70520) = (term523 _70518 _70520).
Proof. exact (TRANS (@lem5446856 _70518 _70520) (@lem5446873 _70518 _70520)). Qed.
Lemma lem5446875 (_70518 : int) (_70519 : int) (_70521 : int) : (term492 _70518 _70519 _70521) = (term493 _70518 _70519 _70521).
Proof. exact (@lem1988291 (term494 _70518 _70519 _70521) term170). Qed.
Lemma lem5446903 (_70518 : int) (_70519 : int) (_70521 : int) : (term495 _70518 _70519 _70521) = (term496 _70518 _70519 _70521).
Proof. exact (@lem1982792 (term494 _70518 _70519 _70521) term170). Qed.
Lemma lem5446905 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5446906 : term170 = term235.
Proof. exact (@lem5446905 (NUMERAL 0)). Qed.
Lemma lem5446908 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5446909 : term238 = term239.
Proof. exact (@lem5446908 term193). Qed.
Lemma lem5446910 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5446911 : term240 = term241.
Proof. exact (MK_COMB (@lem5446910) (@lem5446909)). Qed.
Lemma lem5446912 : term242 = term243.
Proof. exact (MK_COMB (@lem5446911) (@lem5446906)). Qed.
Lemma lem5446913 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5446915 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5446916 : term247 = term248.
Proof. exact (@lem5446915 term193 term193). Qed.
Lemma lem5446917 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5446918 : term250 = term193.
Proof. exact (EQ_MP (@lem5446917) (@lem940073)). Qed.
Lemma lem5446919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5446920 : term248 = term192.
Proof. exact (MK_COMB (@lem5446919) (@lem5446918)). Qed.
Lemma lem5446921 : term247 = term192.
Proof. exact (TRANS (@lem5446916) (@lem5446920)). Qed.
Lemma lem5446923 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5446924 : term242 = term170.
Proof. exact (@lem5446923 term193). Qed.
Lemma lem5446925 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5446926 : term252 = term253.
Proof. exact (MK_COMB (@lem5446925) (@lem5446924)). Qed.
Lemma lem5446927 : term244 = term235.
Proof. exact (MK_COMB (@lem5446926) (@lem5446921)). Qed.
Lemma lem5446928 : term243 = term235.
Proof. exact (TRANS (@lem5446913) (@lem5446927)). Qed.
Lemma lem5446929 : term242 = term235.
Proof. exact (TRANS (@lem5446912) (@lem5446928)). Qed.
Lemma lem5446931 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5446932 : term235 = term170.
Proof. exact (@lem5446931 term170). Qed.
Lemma lem5446933 : term242 = term170.
Proof. exact (TRANS (@lem5446929) (@lem5446932)). Qed.
Lemma lem5446934 (_70518 : int) (_70519 : int) (_70521 : int) : (term497 _70518 _70519 _70521) = (term497 _70518 _70519 _70521).
Proof. exact (eq_refl (term497 _70518 _70519 _70521)). Qed.
Lemma lem5446935 (_70518 : int) (_70519 : int) (_70521 : int) : (term496 _70518 _70519 _70521) = (term498 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446934 _70518 _70519 _70521) (@lem5446933)). Qed.
Lemma lem5446936 (_70518 : int) (_70519 : int) (_70521 : int) : (term498 _70518 _70519 _70521) = (term494 _70518 _70519 _70521).
Proof. exact (@lem1982723 (term494 _70518 _70519 _70521)). Qed.
Lemma lem5446937 (_70518 : int) (_70519 : int) (_70521 : int) : (term496 _70518 _70519 _70521) = (term494 _70518 _70519 _70521).
Proof. exact (TRANS (@lem5446935 _70518 _70519 _70521) (@lem5446936 _70518 _70519 _70521)). Qed.
Lemma lem5446939 (_70518 : int) (_70519 : int) (_70521 : int) : (term495 _70518 _70519 _70521) = (term494 _70518 _70519 _70521).
Proof. exact (TRANS (@lem5446903 _70518 _70519 _70521) (@lem5446937 _70518 _70519 _70521)). Qed.
Lemma lem5446940 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5446941 (_70518 : int) (_70519 : int) (_70521 : int) : (term499 _70518 _70519 _70521) = (term500 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446940) (@lem5446939 _70518 _70519 _70521)). Qed.
Lemma lem5446942 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5446943 (_70518 : int) (_70519 : int) (_70521 : int) : (term493 _70518 _70519 _70521) = (term492 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446941 _70518 _70519 _70521) (@lem5446942)). Qed.
Lemma lem5446944 (_70518 : int) (_70519 : int) (_70521 : int) : (term492 _70518 _70519 _70521) = (term492 _70518 _70519 _70521).
Proof. exact (TRANS (@lem5446875 _70518 _70519 _70521) (@lem5446943 _70518 _70519 _70521)). Qed.
Lemma lem5446945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446946 (_70518 : int) (_70519 : int) : (term319 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5446945) (@lem5446768 _70518 _70519)). Qed.
Lemma lem5446947 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term320 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446946 _70518 _70519) (@lem5446828 _70520 _70521)). Qed.
Lemma lem5446948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446949 (_70518 : int) (_70521 : int) : (term319 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5446948) (@lem5446708 _70518 _70521)). Qed.
Lemma lem5446950 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term321 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446949 _70518 _70521) (@lem5446947 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446952 (_70519 : int) (_70520 : int) : (term322 _70519 _70520) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5446951) (@lem5446648 _70519 _70520)). Qed.
Lemma lem5446953 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term323 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446952 _70519 _70520) (@lem5446950 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446955 (_70518 : int) (_70519 : int) (_70521 : int) : (term513 _70518 _70519 _70521) = (term513 _70518 _70519 _70521).
Proof. exact (MK_COMB (@lem5446954) (@lem5446944 _70518 _70519 _70521)). Qed.
Lemma lem5446956 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term524 _70518 _70519 _70520 _70521) = (term524 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446955 _70518 _70519 _70521) (@lem5446953 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446958 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5446957) (@lem5446518 _70521)). Qed.
Lemma lem5446959 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term525 _70518 _70519 _70520 _70521) = (term525 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446958 _70521) (@lem5446956 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446961 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5446960) (@lem5446470 _70520)). Qed.
Lemma lem5446962 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term526 _70518 _70519 _70520 _70521) = (term526 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446961 _70520) (@lem5446959 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446964 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5446963) (@lem5446422 _70519)). Qed.
Lemma lem5446965 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term527 _70518 _70519 _70520 _70521) = (term527 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446964 _70519) (@lem5446962 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446967 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5446966) (@lem5446374 _70518)). Qed.
Lemma lem5446968 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term478 _70518 _70519 _70520 _70521) = (term478 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446967 _70518) (@lem5446965 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5446970 (_70518 : int) (_70520 : int) : (term479 _70518 _70520) = (term528 _70518 _70520).
Proof. exact (MK_COMB (@lem5446969) (@lem5446874 _70518 _70520)). Qed.
Lemma lem5446971 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term481 _70518 _70519 _70520 _70521) = (term529 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446970 _70518 _70520) (@lem5446968 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5446973 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term488 _70518 _70519 _70520 _70521) = (term530 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446972) (@lem5446855 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446974 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term489 _70518 _70519 _70520 _70521) = (term531 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446973 _70518 _70519 _70520 _70521) (@lem5446971 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446975 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term406 _70518 _70519 _70520 _70521) = (term531 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446307 _70518 _70519 _70520 _70521) (@lem5446974 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446977 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term532 _70518 _70520 _70519 _70521) = (term529 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term532 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5446978 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term529 _70518 _70519 _70520 _70521) = (term532 _70518 _70520 _70519 _70521).
Proof. exact (SYM (@lem5446977 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446979 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term532 _70518 _70520 _70519 _70521) = (term533 _70518 _70519 _70520 _70521).
Proof. exact (@lem1483429 (real_of_int _70519) (term534 _70518 _70519 _70520 _70521) (real_of_int _70521)). Qed.
Lemma lem5446980 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term529 _70518 _70519 _70520 _70521) = (term533 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446978 _70518 _70520 _70519 _70521) (@lem5446979 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446981 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term535 _70518 _70519 _70520 _70521) = (term536 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term535 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446982 (_70519 : int) (_70521 : int) : (term479 _70519 _70521) = (term479 _70519 _70521).
Proof. exact (eq_refl (term479 _70519 _70521)). Qed.
Lemma lem5446983 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term537 _70518 _70519 _70520 _70521) = (term538 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446982 _70519 _70521) (@lem5446981 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446984 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term539 _70518 _70520 _70521 _70519) = (term540 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term539 _70518 _70520 _70521 _70519)). Qed.
Lemma lem5446985 (_70521 : int) (_70519 : int) : (term484 _70521 _70519) = (term484 _70521 _70519).
Proof. exact (eq_refl (term484 _70521 _70519)). Qed.
Lemma lem5446986 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term541 _70518 _70520 _70521 _70519) = (term542 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446985 _70521 _70519) (@lem5446984 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5446988 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term543 _70518 _70520 _70521 _70519) = (term544 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446987) (@lem5446986 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446989 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term533 _70518 _70519 _70520 _70521) = (term545 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5446988 _70518 _70519 _70520 _70521) (@lem5446983 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446990 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term546 _70518 _70519 _70520 _70521) = (term546 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term546 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446991 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : ((term529 _70518 _70519 _70520 _70521) = (term533 _70518 _70519 _70520 _70521)) = ((term529 _70518 _70519 _70520 _70521) = (term545 _70518 _70519 _70520 _70521)).
Proof. exact (MK_COMB (@lem5446990 _70518 _70519 _70520 _70521) (@lem5446989 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446992 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term529 _70518 _70519 _70520 _70521) = (term545 _70518 _70519 _70520 _70521).
Proof. exact (EQ_MP (@lem5446991 _70518 _70519 _70520 _70521) (@lem5446980 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5446993 (_70521 : int) (_70519 : int) : (term491 _70521 _70519) = (term310 _70521 _70519).
Proof. exact (@lem1988291 (real_of_int _70521) (real_of_int _70519)). Qed.
Lemma lem5446999 (_70521 : int) (_70519 : int) : (term311 _70521 _70519) = (term312 _70521 _70519).
Proof. exact (@lem1982792 (real_of_int _70521) (real_of_int _70519)). Qed.
Lemma lem5447004 (_70519 : int) (_70521 : int) : (term312 _70521 _70519) = (term316 _70519 _70521).
Proof. exact (@lem1982761 (term285 _70519) (real_of_int _70521)). Qed.
Lemma lem5447006 (_70519 : int) (_70521 : int) : (term311 _70521 _70519) = (term316 _70519 _70521).
Proof. exact (TRANS (@lem5446999 _70521 _70519) (@lem5447004 _70519 _70521)). Qed.
Lemma lem5447007 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447008 (_70519 : int) (_70521 : int) : (term313 _70521 _70519) = (term317 _70519 _70521).
Proof. exact (MK_COMB (@lem5447007) (@lem5447006 _70519 _70521)). Qed.
Lemma lem5447009 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447010 (_70519 : int) (_70521 : int) : (term310 _70521 _70519) = (term318 _70519 _70521).
Proof. exact (MK_COMB (@lem5447008 _70519 _70521) (@lem5447009)). Qed.
Lemma lem5447011 (_70519 : int) (_70521 : int) : (term491 _70521 _70519) = (term318 _70519 _70521).
Proof. exact (TRANS (@lem5446993 _70521 _70519) (@lem5447010 _70519 _70521)). Qed.
Lemma lem5447012 (_70518 : int) (_70520 : int) : (term523 _70518 _70520) = (term547 _70518 _70520).
Proof. exact (@lem1988289 (term312 _70518 _70520) term170). Qed.
Lemma lem5447030 (_70518 : int) (_70520 : int) : (term502 _70518 _70520) = (term503 _70518 _70520).
Proof. exact (@lem1982792 (term312 _70518 _70520) term170). Qed.
Lemma lem5447032 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447033 : term170 = term235.
Proof. exact (@lem5447032 (NUMERAL 0)). Qed.
Lemma lem5447035 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447036 : term238 = term239.
Proof. exact (@lem5447035 term193). Qed.
Lemma lem5447037 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447038 : term240 = term241.
Proof. exact (MK_COMB (@lem5447037) (@lem5447036)). Qed.
Lemma lem5447039 : term242 = term243.
Proof. exact (MK_COMB (@lem5447038) (@lem5447033)). Qed.
Lemma lem5447040 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5447042 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447043 : term247 = term248.
Proof. exact (@lem5447042 term193 term193). Qed.
Lemma lem5447044 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447045 : term250 = term193.
Proof. exact (EQ_MP (@lem5447044) (@lem940073)). Qed.
Lemma lem5447046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447047 : term248 = term192.
Proof. exact (MK_COMB (@lem5447046) (@lem5447045)). Qed.
Lemma lem5447048 : term247 = term192.
Proof. exact (TRANS (@lem5447043) (@lem5447047)). Qed.
Lemma lem5447050 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5447051 : term242 = term170.
Proof. exact (@lem5447050 term193). Qed.
Lemma lem5447052 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5447053 : term252 = term253.
Proof. exact (MK_COMB (@lem5447052) (@lem5447051)). Qed.
Lemma lem5447054 : term244 = term235.
Proof. exact (MK_COMB (@lem5447053) (@lem5447048)). Qed.
Lemma lem5447055 : term243 = term235.
Proof. exact (TRANS (@lem5447040) (@lem5447054)). Qed.
Lemma lem5447056 : term242 = term235.
Proof. exact (TRANS (@lem5447039) (@lem5447055)). Qed.
Lemma lem5447058 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5447059 : term235 = term170.
Proof. exact (@lem5447058 term170). Qed.
Lemma lem5447060 : term242 = term170.
Proof. exact (TRANS (@lem5447056) (@lem5447059)). Qed.
Lemma lem5447061 (_70518 : int) (_70520 : int) : (term504 _70518 _70520) = (term504 _70518 _70520).
Proof. exact (eq_refl (term504 _70518 _70520)). Qed.
Lemma lem5447062 (_70518 : int) (_70520 : int) : (term503 _70518 _70520) = (term505 _70518 _70520).
Proof. exact (MK_COMB (@lem5447061 _70518 _70520) (@lem5447060)). Qed.
Lemma lem5447063 (_70518 : int) (_70520 : int) : (term505 _70518 _70520) = (term312 _70518 _70520).
Proof. exact (@lem1982723 (term312 _70518 _70520)). Qed.
Lemma lem5447064 (_70518 : int) (_70520 : int) : (term503 _70518 _70520) = (term312 _70518 _70520).
Proof. exact (TRANS (@lem5447062 _70518 _70520) (@lem5447063 _70518 _70520)). Qed.
Lemma lem5447066 (_70518 : int) (_70520 : int) : (term502 _70518 _70520) = (term312 _70518 _70520).
Proof. exact (TRANS (@lem5447030 _70518 _70520) (@lem5447064 _70518 _70520)). Qed.
Lemma lem5447067 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5447068 (_70518 : int) (_70520 : int) : (term548 _70518 _70520) = (term522 _70518 _70520).
Proof. exact (MK_COMB (@lem5447067) (@lem5447066 _70518 _70520)). Qed.
Lemma lem5447069 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447070 (_70518 : int) (_70520 : int) : (term547 _70518 _70520) = (term523 _70518 _70520).
Proof. exact (MK_COMB (@lem5447068 _70518 _70520) (@lem5447069)). Qed.
Lemma lem5447071 (_70518 : int) (_70520 : int) : (term523 _70518 _70520) = (term523 _70518 _70520).
Proof. exact (TRANS (@lem5447012 _70518 _70520) (@lem5447070 _70518 _70520)). Qed.
Lemma lem5447072 (_70518 : int) (_70519 : int) : (term290 _70518 _70519) = (term549 _70518 _70519).
Proof. exact (@lem1988291 (term283 _70518 _70519) term170). Qed.
Lemma lem5447096 (_70518 : int) (_70519 : int) : (term550 _70518 _70519) = (term551 _70518 _70519).
Proof. exact (@lem1982792 (term283 _70518 _70519) term170). Qed.
Lemma lem5447098 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447099 : term170 = term235.
Proof. exact (@lem5447098 (NUMERAL 0)). Qed.
Lemma lem5447101 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447102 : term238 = term239.
Proof. exact (@lem5447101 term193). Qed.
Lemma lem5447103 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447104 : term240 = term241.
Proof. exact (MK_COMB (@lem5447103) (@lem5447102)). Qed.
Lemma lem5447105 : term242 = term243.
Proof. exact (MK_COMB (@lem5447104) (@lem5447099)). Qed.
Lemma lem5447106 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5447108 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447109 : term247 = term248.
Proof. exact (@lem5447108 term193 term193). Qed.
Lemma lem5447110 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447111 : term250 = term193.
Proof. exact (EQ_MP (@lem5447110) (@lem940073)). Qed.
Lemma lem5447112 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447113 : term248 = term192.
Proof. exact (MK_COMB (@lem5447112) (@lem5447111)). Qed.
Lemma lem5447114 : term247 = term192.
Proof. exact (TRANS (@lem5447109) (@lem5447113)). Qed.
Lemma lem5447116 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5447117 : term242 = term170.
Proof. exact (@lem5447116 term193). Qed.
Lemma lem5447118 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5447119 : term252 = term253.
Proof. exact (MK_COMB (@lem5447118) (@lem5447117)). Qed.
Lemma lem5447120 : term244 = term235.
Proof. exact (MK_COMB (@lem5447119) (@lem5447114)). Qed.
Lemma lem5447121 : term243 = term235.
Proof. exact (TRANS (@lem5447106) (@lem5447120)). Qed.
Lemma lem5447122 : term242 = term235.
Proof. exact (TRANS (@lem5447105) (@lem5447121)). Qed.
Lemma lem5447124 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5447125 : term235 = term170.
Proof. exact (@lem5447124 term170). Qed.
Lemma lem5447126 : term242 = term170.
Proof. exact (TRANS (@lem5447122) (@lem5447125)). Qed.
Lemma lem5447127 (_70518 : int) (_70519 : int) : (term552 _70518 _70519) = (term552 _70518 _70519).
Proof. exact (eq_refl (term552 _70518 _70519)). Qed.
Lemma lem5447128 (_70518 : int) (_70519 : int) : (term551 _70518 _70519) = (term553 _70518 _70519).
Proof. exact (MK_COMB (@lem5447127 _70518 _70519) (@lem5447126)). Qed.
Lemma lem5447129 (_70518 : int) (_70519 : int) : (term553 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (@lem1982723 (term283 _70518 _70519)). Qed.
Lemma lem5447130 (_70518 : int) (_70519 : int) : (term551 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (TRANS (@lem5447128 _70518 _70519) (@lem5447129 _70518 _70519)). Qed.
Lemma lem5447132 (_70518 : int) (_70519 : int) : (term550 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (TRANS (@lem5447096 _70518 _70519) (@lem5447130 _70518 _70519)). Qed.
Lemma lem5447133 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447134 (_70518 : int) (_70519 : int) : (term554 _70518 _70519) = (term289 _70518 _70519).
Proof. exact (MK_COMB (@lem5447133) (@lem5447132 _70518 _70519)). Qed.
Lemma lem5447135 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447136 (_70518 : int) (_70519 : int) : (term549 _70518 _70519) = (term290 _70518 _70519).
Proof. exact (MK_COMB (@lem5447134 _70518 _70519) (@lem5447135)). Qed.
Lemma lem5447137 (_70518 : int) (_70519 : int) : (term290 _70518 _70519) = (term290 _70518 _70519).
Proof. exact (TRANS (@lem5447072 _70518 _70519) (@lem5447136 _70518 _70519)). Qed.
Lemma lem5447138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447139 (_70518 : int) (_70519 : int) : (term319 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5447138) (@lem5446768 _70518 _70519)). Qed.
Lemma lem5447140 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term320 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447139 _70518 _70519) (@lem5446828 _70520 _70521)). Qed.
Lemma lem5447141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447142 (_70518 : int) (_70521 : int) : (term319 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5447141) (@lem5446708 _70518 _70521)). Qed.
Lemma lem5447143 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term321 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447142 _70518 _70521) (@lem5447140 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447145 (_70519 : int) (_70520 : int) : (term322 _70519 _70520) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5447144) (@lem5446648 _70519 _70520)). Qed.
Lemma lem5447146 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term323 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447145 _70519 _70520) (@lem5447143 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447148 (_70518 : int) (_70519 : int) : (term555 _70518 _70519) = (term555 _70518 _70519).
Proof. exact (MK_COMB (@lem5447147) (@lem5447137 _70518 _70519)). Qed.
Lemma lem5447149 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term556 _70518 _70519 _70520 _70521) = (term556 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447148 _70518 _70519) (@lem5447146 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447151 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5447150) (@lem5446518 _70521)). Qed.
Lemma lem5447152 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term557 _70518 _70519 _70520 _70521) = (term557 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447151 _70521) (@lem5447149 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447154 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5447153) (@lem5446470 _70520)). Qed.
Lemma lem5447155 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term558 _70518 _70519 _70520 _70521) = (term558 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447154 _70520) (@lem5447152 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447157 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5447156) (@lem5446422 _70519)). Qed.
Lemma lem5447158 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term559 _70518 _70519 _70520 _70521) = (term559 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447157 _70519) (@lem5447155 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447160 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5447159) (@lem5446374 _70518)). Qed.
Lemma lem5447161 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term560 _70518 _70519 _70520 _70521) = (term560 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447160 _70518) (@lem5447158 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447163 (_70518 : int) (_70520 : int) : (term528 _70518 _70520) = (term528 _70518 _70520).
Proof. exact (MK_COMB (@lem5447162) (@lem5447071 _70518 _70520)). Qed.
Lemma lem5447164 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term540 _70518 _70519 _70520 _70521) = (term540 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447163 _70518 _70520) (@lem5447161 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447166 (_70519 : int) (_70521 : int) : (term484 _70521 _70519) = (term319 _70519 _70521).
Proof. exact (MK_COMB (@lem5447165) (@lem5447011 _70519 _70521)). Qed.
Lemma lem5447167 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term542 _70518 _70519 _70520 _70521) = (term561 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447166 _70519 _70521) (@lem5447164 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447168 (_70519 : int) (_70521 : int) : (term519 _70519 _70521) = (term520 _70519 _70521).
Proof. exact (@lem1988289 (real_of_int _70519) (real_of_int _70521)). Qed.
Lemma lem5447181 (_70519 : int) (_70521 : int) : (term311 _70519 _70521) = (term312 _70519 _70521).
Proof. exact (@lem1982792 (real_of_int _70519) (real_of_int _70521)). Qed.
Lemma lem5447182 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5447183 (_70519 : int) (_70521 : int) : (term521 _70519 _70521) = (term522 _70519 _70521).
Proof. exact (MK_COMB (@lem5447182) (@lem5447181 _70519 _70521)). Qed.
Lemma lem5447184 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447185 (_70519 : int) (_70521 : int) : (term520 _70519 _70521) = (term523 _70519 _70521).
Proof. exact (MK_COMB (@lem5447183 _70519 _70521) (@lem5447184)). Qed.
Lemma lem5447186 (_70519 : int) (_70521 : int) : (term519 _70519 _70521) = (term523 _70519 _70521).
Proof. exact (TRANS (@lem5447168 _70519 _70521) (@lem5447185 _70519 _70521)). Qed.
Lemma lem5447187 (_70518 : int) (_70521 : int) : (term290 _70518 _70521) = (term549 _70518 _70521).
Proof. exact (@lem1988291 (term283 _70518 _70521) term170). Qed.
Lemma lem5447211 (_70518 : int) (_70521 : int) : (term550 _70518 _70521) = (term551 _70518 _70521).
Proof. exact (@lem1982792 (term283 _70518 _70521) term170). Qed.
Lemma lem5447213 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447214 : term170 = term235.
Proof. exact (@lem5447213 (NUMERAL 0)). Qed.
Lemma lem5447216 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447217 : term238 = term239.
Proof. exact (@lem5447216 term193). Qed.
Lemma lem5447218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447219 : term240 = term241.
Proof. exact (MK_COMB (@lem5447218) (@lem5447217)). Qed.
Lemma lem5447220 : term242 = term243.
Proof. exact (MK_COMB (@lem5447219) (@lem5447214)). Qed.
Lemma lem5447221 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5447223 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447224 : term247 = term248.
Proof. exact (@lem5447223 term193 term193). Qed.
Lemma lem5447225 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447226 : term250 = term193.
Proof. exact (EQ_MP (@lem5447225) (@lem940073)). Qed.
Lemma lem5447227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447228 : term248 = term192.
Proof. exact (MK_COMB (@lem5447227) (@lem5447226)). Qed.
Lemma lem5447229 : term247 = term192.
Proof. exact (TRANS (@lem5447224) (@lem5447228)). Qed.
Lemma lem5447231 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5447232 : term242 = term170.
Proof. exact (@lem5447231 term193). Qed.
Lemma lem5447233 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5447234 : term252 = term253.
Proof. exact (MK_COMB (@lem5447233) (@lem5447232)). Qed.
Lemma lem5447235 : term244 = term235.
Proof. exact (MK_COMB (@lem5447234) (@lem5447229)). Qed.
Lemma lem5447236 : term243 = term235.
Proof. exact (TRANS (@lem5447221) (@lem5447235)). Qed.
Lemma lem5447237 : term242 = term235.
Proof. exact (TRANS (@lem5447220) (@lem5447236)). Qed.
Lemma lem5447239 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5447240 : term235 = term170.
Proof. exact (@lem5447239 term170). Qed.
Lemma lem5447241 : term242 = term170.
Proof. exact (TRANS (@lem5447237) (@lem5447240)). Qed.
Lemma lem5447242 (_70518 : int) (_70521 : int) : (term552 _70518 _70521) = (term552 _70518 _70521).
Proof. exact (eq_refl (term552 _70518 _70521)). Qed.
Lemma lem5447243 (_70518 : int) (_70521 : int) : (term551 _70518 _70521) = (term553 _70518 _70521).
Proof. exact (MK_COMB (@lem5447242 _70518 _70521) (@lem5447241)). Qed.
Lemma lem5447244 (_70518 : int) (_70521 : int) : (term553 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (@lem1982723 (term283 _70518 _70521)). Qed.
Lemma lem5447245 (_70518 : int) (_70521 : int) : (term551 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (TRANS (@lem5447243 _70518 _70521) (@lem5447244 _70518 _70521)). Qed.
Lemma lem5447247 (_70518 : int) (_70521 : int) : (term550 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (TRANS (@lem5447211 _70518 _70521) (@lem5447245 _70518 _70521)). Qed.
Lemma lem5447248 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447249 (_70518 : int) (_70521 : int) : (term554 _70518 _70521) = (term289 _70518 _70521).
Proof. exact (MK_COMB (@lem5447248) (@lem5447247 _70518 _70521)). Qed.
Lemma lem5447250 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447251 (_70518 : int) (_70521 : int) : (term549 _70518 _70521) = (term290 _70518 _70521).
Proof. exact (MK_COMB (@lem5447249 _70518 _70521) (@lem5447250)). Qed.
Lemma lem5447252 (_70518 : int) (_70521 : int) : (term290 _70518 _70521) = (term290 _70518 _70521).
Proof. exact (TRANS (@lem5447187 _70518 _70521) (@lem5447251 _70518 _70521)). Qed.
Lemma lem5447253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447254 (_70518 : int) (_70519 : int) : (term319 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5447253) (@lem5446768 _70518 _70519)). Qed.
Lemma lem5447255 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term320 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447254 _70518 _70519) (@lem5446828 _70520 _70521)). Qed.
Lemma lem5447256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447257 (_70518 : int) (_70521 : int) : (term319 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5447256) (@lem5446708 _70518 _70521)). Qed.
Lemma lem5447258 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term321 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447257 _70518 _70521) (@lem5447255 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447260 (_70519 : int) (_70520 : int) : (term322 _70519 _70520) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5447259) (@lem5446648 _70519 _70520)). Qed.
Lemma lem5447261 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term323 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447260 _70519 _70520) (@lem5447258 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447263 (_70518 : int) (_70521 : int) : (term555 _70518 _70521) = (term555 _70518 _70521).
Proof. exact (MK_COMB (@lem5447262) (@lem5447252 _70518 _70521)). Qed.
Lemma lem5447264 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term562 _70518 _70519 _70520 _70521) = (term562 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447263 _70518 _70521) (@lem5447261 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447266 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5447265) (@lem5446518 _70521)). Qed.
Lemma lem5447267 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term563 _70518 _70519 _70520 _70521) = (term563 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447266 _70521) (@lem5447264 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447269 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5447268) (@lem5446470 _70520)). Qed.
Lemma lem5447270 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term564 _70518 _70519 _70520 _70521) = (term564 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447269 _70520) (@lem5447267 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447272 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5447271) (@lem5446422 _70519)). Qed.
Lemma lem5447273 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term565 _70518 _70519 _70520 _70521) = (term565 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447272 _70519) (@lem5447270 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447275 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5447274) (@lem5446374 _70518)). Qed.
Lemma lem5447276 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term566 _70518 _70519 _70520 _70521) = (term566 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447275 _70518) (@lem5447273 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447278 (_70518 : int) (_70520 : int) : (term528 _70518 _70520) = (term528 _70518 _70520).
Proof. exact (MK_COMB (@lem5447277) (@lem5447071 _70518 _70520)). Qed.
Lemma lem5447279 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term536 _70518 _70519 _70520 _70521) = (term536 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447278 _70518 _70520) (@lem5447276 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447281 (_70519 : int) (_70521 : int) : (term479 _70519 _70521) = (term528 _70519 _70521).
Proof. exact (MK_COMB (@lem5447280) (@lem5447186 _70519 _70521)). Qed.
Lemma lem5447282 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term538 _70518 _70519 _70520 _70521) = (term567 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447281 _70519 _70521) (@lem5447279 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5447284 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term544 _70518 _70519 _70520 _70521) = (term568 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447283) (@lem5447167 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447285 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term545 _70518 _70519 _70520 _70521) = (term569 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447284 _70518 _70519 _70520 _70521) (@lem5447282 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447297 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term529 _70518 _70519 _70520 _70521) = (term569 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446992 _70518 _70519 _70520 _70521) (@lem5447285 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447299 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term570 _70518 _70520 _70519 _70521) = (term518 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term570 _70518 _70520 _70519 _70521)). Qed.
Lemma lem5447300 (_70518 : int) (_70520 : int) (_70519 : int) (_70521 : int) : (term518 _70518 _70519 _70520 _70521) = (term570 _70518 _70520 _70519 _70521).
Proof. exact (SYM (@lem5447299 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447301 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term570 _70518 _70520 _70519 _70521) = (term571 _70518 _70519 _70520 _70521).
Proof. exact (@lem1483429 (real_of_int _70519) (term572 _70518 _70519 _70520 _70521) (real_of_int _70521)). Qed.
Lemma lem5447302 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term518 _70518 _70519 _70520 _70521) = (term571 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5447300 _70518 _70520 _70519 _70521) (@lem5447301 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447303 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term573 _70518 _70519 _70520 _70521) = (term574 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term573 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447304 (_70519 : int) (_70521 : int) : (term479 _70519 _70521) = (term479 _70519 _70521).
Proof. exact (eq_refl (term479 _70519 _70521)). Qed.
Lemma lem5447305 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term575 _70518 _70519 _70520 _70521) = (term576 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447304 _70519 _70521) (@lem5447303 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447306 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term577 _70518 _70520 _70521 _70519) = (term578 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term577 _70518 _70520 _70521 _70519)). Qed.
Lemma lem5447307 (_70521 : int) (_70519 : int) : (term484 _70521 _70519) = (term484 _70521 _70519).
Proof. exact (eq_refl (term484 _70521 _70519)). Qed.
Lemma lem5447308 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term579 _70518 _70520 _70521 _70519) = (term580 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447307 _70521 _70519) (@lem5447306 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5447310 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term581 _70518 _70520 _70521 _70519) = (term582 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447309) (@lem5447308 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447311 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term571 _70518 _70519 _70520 _70521) = (term583 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447310 _70518 _70519 _70520 _70521) (@lem5447305 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447312 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term584 _70518 _70519 _70520 _70521) = (term584 _70518 _70519 _70520 _70521).
Proof. exact (eq_refl (term584 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447313 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : ((term518 _70518 _70519 _70520 _70521) = (term571 _70518 _70519 _70520 _70521)) = ((term518 _70518 _70519 _70520 _70521) = (term583 _70518 _70519 _70520 _70521)).
Proof. exact (MK_COMB (@lem5447312 _70518 _70519 _70520 _70521) (@lem5447311 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447314 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term518 _70518 _70519 _70520 _70521) = (term583 _70518 _70519 _70520 _70521).
Proof. exact (EQ_MP (@lem5447313 _70518 _70519 _70520 _70521) (@lem5447302 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447315 (_70518 : int) (_70520 : int) : (term318 _70518 _70520) = (term507 _70518 _70520).
Proof. exact (@lem1988291 (term316 _70518 _70520) term170). Qed.
Lemma lem5447333 (_70518 : int) (_70520 : int) : (term508 _70518 _70520) = (term509 _70518 _70520).
Proof. exact (@lem1982792 (term316 _70518 _70520) term170). Qed.
Lemma lem5447335 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447336 : term170 = term235.
Proof. exact (@lem5447335 (NUMERAL 0)). Qed.
Lemma lem5447338 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447339 : term238 = term239.
Proof. exact (@lem5447338 term193). Qed.
Lemma lem5447340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447341 : term240 = term241.
Proof. exact (MK_COMB (@lem5447340) (@lem5447339)). Qed.
Lemma lem5447342 : term242 = term243.
Proof. exact (MK_COMB (@lem5447341) (@lem5447336)). Qed.
Lemma lem5447343 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5447345 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447346 : term247 = term248.
Proof. exact (@lem5447345 term193 term193). Qed.
Lemma lem5447347 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447348 : term250 = term193.
Proof. exact (EQ_MP (@lem5447347) (@lem940073)). Qed.
Lemma lem5447349 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447350 : term248 = term192.
Proof. exact (MK_COMB (@lem5447349) (@lem5447348)). Qed.
Lemma lem5447351 : term247 = term192.
Proof. exact (TRANS (@lem5447346) (@lem5447350)). Qed.
Lemma lem5447353 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5447354 : term242 = term170.
Proof. exact (@lem5447353 term193). Qed.
Lemma lem5447355 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5447356 : term252 = term253.
Proof. exact (MK_COMB (@lem5447355) (@lem5447354)). Qed.
Lemma lem5447357 : term244 = term235.
Proof. exact (MK_COMB (@lem5447356) (@lem5447351)). Qed.
Lemma lem5447358 : term243 = term235.
Proof. exact (TRANS (@lem5447343) (@lem5447357)). Qed.
Lemma lem5447359 : term242 = term235.
Proof. exact (TRANS (@lem5447342) (@lem5447358)). Qed.
Lemma lem5447361 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5447362 : term235 = term170.
Proof. exact (@lem5447361 term170). Qed.
Lemma lem5447363 : term242 = term170.
Proof. exact (TRANS (@lem5447359) (@lem5447362)). Qed.
Lemma lem5447364 (_70518 : int) (_70520 : int) : (term510 _70518 _70520) = (term510 _70518 _70520).
Proof. exact (eq_refl (term510 _70518 _70520)). Qed.
Lemma lem5447365 (_70518 : int) (_70520 : int) : (term509 _70518 _70520) = (term511 _70518 _70520).
Proof. exact (MK_COMB (@lem5447364 _70518 _70520) (@lem5447363)). Qed.
Lemma lem5447366 (_70518 : int) (_70520 : int) : (term511 _70518 _70520) = (term316 _70518 _70520).
Proof. exact (@lem1982723 (term316 _70518 _70520)). Qed.
Lemma lem5447367 (_70518 : int) (_70520 : int) : (term509 _70518 _70520) = (term316 _70518 _70520).
Proof. exact (TRANS (@lem5447365 _70518 _70520) (@lem5447366 _70518 _70520)). Qed.
Lemma lem5447369 (_70518 : int) (_70520 : int) : (term508 _70518 _70520) = (term316 _70518 _70520).
Proof. exact (TRANS (@lem5447333 _70518 _70520) (@lem5447367 _70518 _70520)). Qed.
Lemma lem5447370 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447371 (_70518 : int) (_70520 : int) : (term512 _70518 _70520) = (term317 _70518 _70520).
Proof. exact (MK_COMB (@lem5447370) (@lem5447369 _70518 _70520)). Qed.
Lemma lem5447372 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447373 (_70518 : int) (_70520 : int) : (term507 _70518 _70520) = (term318 _70518 _70520).
Proof. exact (MK_COMB (@lem5447371 _70518 _70520) (@lem5447372)). Qed.
Lemma lem5447374 (_70518 : int) (_70520 : int) : (term318 _70518 _70520) = (term318 _70518 _70520).
Proof. exact (TRANS (@lem5447315 _70518 _70520) (@lem5447373 _70518 _70520)). Qed.
Lemma lem5447375 (_70520 : int) (_70519 : int) : (term290 _70520 _70519) = (term549 _70520 _70519).
Proof. exact (@lem1988291 (term283 _70520 _70519) term170). Qed.
Lemma lem5447376 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447399 (_70519 : int) (_70520 : int) : (term283 _70520 _70519) = (term284 _70519 _70520).
Proof. exact (@lem1982757 (term285 _70519) (real_of_int _70520) term238). Qed.
Lemma lem5447400 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5447401 (_70519 : int) (_70520 : int) : (term585 _70520 _70519) = (term586 _70519 _70520).
Proof. exact (MK_COMB (@lem5447400) (@lem5447399 _70519 _70520)). Qed.
Lemma lem5447402 (_70519 : int) (_70520 : int) : (term550 _70520 _70519) = (term587 _70519 _70520).
Proof. exact (MK_COMB (@lem5447401 _70519 _70520) (@lem5447376)). Qed.
Lemma lem5447403 (_70519 : int) (_70520 : int) : (term587 _70519 _70520) = (term588 _70519 _70520).
Proof. exact (@lem1982792 (term284 _70519 _70520) term170). Qed.
Lemma lem5447405 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447406 : term170 = term235.
Proof. exact (@lem5447405 (NUMERAL 0)). Qed.
Lemma lem5447408 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447409 : term238 = term239.
Proof. exact (@lem5447408 term193). Qed.
Lemma lem5447410 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447411 : term240 = term241.
Proof. exact (MK_COMB (@lem5447410) (@lem5447409)). Qed.
Lemma lem5447412 : term242 = term243.
Proof. exact (MK_COMB (@lem5447411) (@lem5447406)). Qed.
Lemma lem5447413 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5447415 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447416 : term247 = term248.
Proof. exact (@lem5447415 term193 term193). Qed.
Lemma lem5447417 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447418 : term250 = term193.
Proof. exact (EQ_MP (@lem5447417) (@lem940073)). Qed.
Lemma lem5447419 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447420 : term248 = term192.
Proof. exact (MK_COMB (@lem5447419) (@lem5447418)). Qed.
Lemma lem5447421 : term247 = term192.
Proof. exact (TRANS (@lem5447416) (@lem5447420)). Qed.
Lemma lem5447423 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5447424 : term242 = term170.
Proof. exact (@lem5447423 term193). Qed.
Lemma lem5447425 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5447426 : term252 = term253.
Proof. exact (MK_COMB (@lem5447425) (@lem5447424)). Qed.
Lemma lem5447427 : term244 = term235.
Proof. exact (MK_COMB (@lem5447426) (@lem5447421)). Qed.
Lemma lem5447428 : term243 = term235.
Proof. exact (TRANS (@lem5447413) (@lem5447427)). Qed.
Lemma lem5447429 : term242 = term235.
Proof. exact (TRANS (@lem5447412) (@lem5447428)). Qed.
Lemma lem5447431 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5447432 : term235 = term170.
Proof. exact (@lem5447431 term170). Qed.
Lemma lem5447433 : term242 = term170.
Proof. exact (TRANS (@lem5447429) (@lem5447432)). Qed.
Lemma lem5447434 (_70519 : int) (_70520 : int) : (term589 _70519 _70520) = (term589 _70519 _70520).
Proof. exact (eq_refl (term589 _70519 _70520)). Qed.
Lemma lem5447435 (_70519 : int) (_70520 : int) : (term588 _70519 _70520) = (term590 _70519 _70520).
Proof. exact (MK_COMB (@lem5447434 _70519 _70520) (@lem5447433)). Qed.
Lemma lem5447436 (_70519 : int) (_70520 : int) : (term590 _70519 _70520) = (term284 _70519 _70520).
Proof. exact (@lem1982723 (term284 _70519 _70520)). Qed.
Lemma lem5447437 (_70519 : int) (_70520 : int) : (term588 _70519 _70520) = (term284 _70519 _70520).
Proof. exact (TRANS (@lem5447435 _70519 _70520) (@lem5447436 _70519 _70520)). Qed.
Lemma lem5447438 (_70519 : int) (_70520 : int) : (term587 _70519 _70520) = (term284 _70519 _70520).
Proof. exact (TRANS (@lem5447403 _70519 _70520) (@lem5447437 _70519 _70520)). Qed.
Lemma lem5447439 (_70519 : int) (_70520 : int) : (term550 _70520 _70519) = (term284 _70519 _70520).
Proof. exact (TRANS (@lem5447402 _70519 _70520) (@lem5447438 _70519 _70520)). Qed.
Lemma lem5447440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447441 (_70519 : int) (_70520 : int) : (term554 _70520 _70519) = (term287 _70519 _70520).
Proof. exact (MK_COMB (@lem5447440) (@lem5447439 _70519 _70520)). Qed.
Lemma lem5447442 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447443 (_70519 : int) (_70520 : int) : (term549 _70520 _70519) = (term288 _70519 _70520).
Proof. exact (MK_COMB (@lem5447441 _70519 _70520) (@lem5447442)). Qed.
Lemma lem5447444 (_70519 : int) (_70520 : int) : (term290 _70520 _70519) = (term288 _70519 _70520).
Proof. exact (TRANS (@lem5447375 _70520 _70519) (@lem5447443 _70519 _70520)). Qed.
Lemma lem5447445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447446 (_70518 : int) (_70519 : int) : (term319 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5447445) (@lem5446768 _70518 _70519)). Qed.
Lemma lem5447447 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term320 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447446 _70518 _70519) (@lem5446828 _70520 _70521)). Qed.
Lemma lem5447448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447449 (_70518 : int) (_70521 : int) : (term319 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5447448) (@lem5446708 _70518 _70521)). Qed.
Lemma lem5447450 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term321 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447449 _70518 _70521) (@lem5447447 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447452 (_70519 : int) (_70520 : int) : (term322 _70519 _70520) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5447451) (@lem5446648 _70519 _70520)). Qed.
Lemma lem5447453 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term323 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447452 _70519 _70520) (@lem5447450 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447455 (_70519 : int) (_70520 : int) : (term555 _70520 _70519) = (term591 _70519 _70520).
Proof. exact (MK_COMB (@lem5447454) (@lem5447444 _70519 _70520)). Qed.
Lemma lem5447456 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term592 _70518 _70519 _70520 _70521) = (term593 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447455 _70519 _70520) (@lem5447453 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447458 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5447457) (@lem5446518 _70521)). Qed.
Lemma lem5447459 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term594 _70518 _70519 _70520 _70521) = (term595 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447458 _70521) (@lem5447456 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447461 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5447460) (@lem5446470 _70520)). Qed.
Lemma lem5447462 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term596 _70518 _70519 _70520 _70521) = (term597 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447461 _70520) (@lem5447459 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447464 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5447463) (@lem5446422 _70519)). Qed.
Lemma lem5447465 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term598 _70518 _70519 _70520 _70521) = (term599 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447464 _70519) (@lem5447462 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447467 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5447466) (@lem5446374 _70518)). Qed.
Lemma lem5447468 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term600 _70518 _70519 _70520 _70521) = (term601 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447467 _70518) (@lem5447465 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447470 (_70518 : int) (_70520 : int) : (term319 _70518 _70520) = (term319 _70518 _70520).
Proof. exact (MK_COMB (@lem5447469) (@lem5447374 _70518 _70520)). Qed.
Lemma lem5447471 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term578 _70518 _70519 _70520 _70521) = (term602 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447470 _70518 _70520) (@lem5447468 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447473 (_70519 : int) (_70521 : int) : (term484 _70521 _70519) = (term319 _70519 _70521).
Proof. exact (MK_COMB (@lem5447472) (@lem5447011 _70519 _70521)). Qed.
Lemma lem5447474 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term580 _70518 _70519 _70520 _70521) = (term603 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447473 _70519 _70521) (@lem5447471 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447475 (_70520 : int) (_70521 : int) : (term290 _70520 _70521) = (term549 _70520 _70521).
Proof. exact (@lem1988291 (term283 _70520 _70521) term170). Qed.
Lemma lem5447499 (_70520 : int) (_70521 : int) : (term550 _70520 _70521) = (term551 _70520 _70521).
Proof. exact (@lem1982792 (term283 _70520 _70521) term170). Qed.
Lemma lem5447501 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447502 : term170 = term235.
Proof. exact (@lem5447501 (NUMERAL 0)). Qed.
Lemma lem5447504 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447505 : term238 = term239.
Proof. exact (@lem5447504 term193). Qed.
Lemma lem5447506 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447507 : term240 = term241.
Proof. exact (MK_COMB (@lem5447506) (@lem5447505)). Qed.
Lemma lem5447508 : term242 = term243.
Proof. exact (MK_COMB (@lem5447507) (@lem5447502)). Qed.
Lemma lem5447509 : term243 = term244.
Proof. exact (@lem1981613 term238 term170 term192 term192). Qed.
Lemma lem5447511 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447512 : term247 = term248.
Proof. exact (@lem5447511 term193 term193). Qed.
Lemma lem5447513 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447514 : term250 = term193.
Proof. exact (EQ_MP (@lem5447513) (@lem940073)). Qed.
Lemma lem5447515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447516 : term248 = term192.
Proof. exact (MK_COMB (@lem5447515) (@lem5447514)). Qed.
Lemma lem5447517 : term247 = term192.
Proof. exact (TRANS (@lem5447512) (@lem5447516)). Qed.
Lemma lem5447519 (x : nat) : (term251 x) = term170.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5447520 : term242 = term170.
Proof. exact (@lem5447519 term193). Qed.
Lemma lem5447521 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5447522 : term252 = term253.
Proof. exact (MK_COMB (@lem5447521) (@lem5447520)). Qed.
Lemma lem5447523 : term244 = term235.
Proof. exact (MK_COMB (@lem5447522) (@lem5447517)). Qed.
Lemma lem5447524 : term243 = term235.
Proof. exact (TRANS (@lem5447509) (@lem5447523)). Qed.
Lemma lem5447525 : term242 = term235.
Proof. exact (TRANS (@lem5447508) (@lem5447524)). Qed.
Lemma lem5447527 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5447528 : term235 = term170.
Proof. exact (@lem5447527 term170). Qed.
Lemma lem5447529 : term242 = term170.
Proof. exact (TRANS (@lem5447525) (@lem5447528)). Qed.
Lemma lem5447530 (_70520 : int) (_70521 : int) : (term552 _70520 _70521) = (term552 _70520 _70521).
Proof. exact (eq_refl (term552 _70520 _70521)). Qed.
Lemma lem5447531 (_70520 : int) (_70521 : int) : (term551 _70520 _70521) = (term553 _70520 _70521).
Proof. exact (MK_COMB (@lem5447530 _70520 _70521) (@lem5447529)). Qed.
Lemma lem5447532 (_70520 : int) (_70521 : int) : (term553 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (@lem1982723 (term283 _70520 _70521)). Qed.
Lemma lem5447533 (_70520 : int) (_70521 : int) : (term551 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (TRANS (@lem5447531 _70520 _70521) (@lem5447532 _70520 _70521)). Qed.
Lemma lem5447535 (_70520 : int) (_70521 : int) : (term550 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (TRANS (@lem5447499 _70520 _70521) (@lem5447533 _70520 _70521)). Qed.
Lemma lem5447536 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447537 (_70520 : int) (_70521 : int) : (term554 _70520 _70521) = (term289 _70520 _70521).
Proof. exact (MK_COMB (@lem5447536) (@lem5447535 _70520 _70521)). Qed.
Lemma lem5447538 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447539 (_70520 : int) (_70521 : int) : (term549 _70520 _70521) = (term290 _70520 _70521).
Proof. exact (MK_COMB (@lem5447537 _70520 _70521) (@lem5447538)). Qed.
Lemma lem5447540 (_70520 : int) (_70521 : int) : (term290 _70520 _70521) = (term290 _70520 _70521).
Proof. exact (TRANS (@lem5447475 _70520 _70521) (@lem5447539 _70520 _70521)). Qed.
Lemma lem5447541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447542 (_70518 : int) (_70519 : int) : (term319 _70518 _70519) = (term319 _70518 _70519).
Proof. exact (MK_COMB (@lem5447541) (@lem5446768 _70518 _70519)). Qed.
Lemma lem5447543 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term320 _70518 _70519 _70520 _70521) = (term320 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447542 _70518 _70519) (@lem5446828 _70520 _70521)). Qed.
Lemma lem5447544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447545 (_70518 : int) (_70521 : int) : (term319 _70518 _70521) = (term319 _70518 _70521).
Proof. exact (MK_COMB (@lem5447544) (@lem5446708 _70518 _70521)). Qed.
Lemma lem5447546 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term321 _70518 _70519 _70520 _70521) = (term321 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447545 _70518 _70521) (@lem5447543 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447548 (_70519 : int) (_70520 : int) : (term322 _70519 _70520) = (term322 _70519 _70520).
Proof. exact (MK_COMB (@lem5447547) (@lem5446648 _70519 _70520)). Qed.
Lemma lem5447549 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term323 _70518 _70519 _70520 _70521) = (term323 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447548 _70519 _70520) (@lem5447546 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447551 (_70520 : int) (_70521 : int) : (term555 _70520 _70521) = (term555 _70520 _70521).
Proof. exact (MK_COMB (@lem5447550) (@lem5447540 _70520 _70521)). Qed.
Lemma lem5447552 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term604 _70518 _70519 _70520 _70521) = (term604 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447551 _70520 _70521) (@lem5447549 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447554 (_70521 : int) : (term328 _70521) = (term328 _70521).
Proof. exact (MK_COMB (@lem5447553) (@lem5446518 _70521)). Qed.
Lemma lem5447555 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term605 _70518 _70519 _70520 _70521) = (term605 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447554 _70521) (@lem5447552 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447557 (_70520 : int) : (term328 _70520) = (term328 _70520).
Proof. exact (MK_COMB (@lem5447556) (@lem5446470 _70520)). Qed.
Lemma lem5447558 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term606 _70518 _70519 _70520 _70521) = (term606 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447557 _70520) (@lem5447555 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447560 (_70519 : int) : (term328 _70519) = (term328 _70519).
Proof. exact (MK_COMB (@lem5447559) (@lem5446422 _70519)). Qed.
Lemma lem5447561 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term607 _70518 _70519 _70520 _70521) = (term607 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447560 _70519) (@lem5447558 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447563 (_70518 : int) : (term328 _70518) = (term328 _70518).
Proof. exact (MK_COMB (@lem5447562) (@lem5446374 _70518)). Qed.
Lemma lem5447564 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term608 _70518 _70519 _70520 _70521) = (term608 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447563 _70518) (@lem5447561 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447566 (_70518 : int) (_70520 : int) : (term319 _70518 _70520) = (term319 _70518 _70520).
Proof. exact (MK_COMB (@lem5447565) (@lem5447374 _70518 _70520)). Qed.
Lemma lem5447567 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term574 _70518 _70519 _70520 _70521) = (term574 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447566 _70518 _70520) (@lem5447564 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5447569 (_70519 : int) (_70521 : int) : (term479 _70519 _70521) = (term528 _70519 _70521).
Proof. exact (MK_COMB (@lem5447568) (@lem5447186 _70519 _70521)). Qed.
Lemma lem5447570 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term576 _70518 _70519 _70520 _70521) = (term609 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447569 _70519 _70521) (@lem5447567 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5447572 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term582 _70518 _70519 _70520 _70521) = (term610 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447571) (@lem5447474 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447573 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term583 _70518 _70519 _70520 _70521) = (term611 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447572 _70518 _70519 _70520 _70521) (@lem5447570 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447585 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term518 _70518 _70519 _70520 _70521) = (term611 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5447314 _70518 _70519 _70520 _70521) (@lem5447573 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5447587 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term530 _70518 _70519 _70520 _70521) = (term612 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447586) (@lem5447585 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447588 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term531 _70518 _70519 _70520 _70521) = (term613 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447587 _70518 _70519 _70520 _70521) (@lem5447297 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447590 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term406 _70518 _70519 _70520 _70521) = (term613 _70518 _70519 _70520 _70521).
Proof. exact (TRANS (@lem5446975 _70518 _70519 _70520 _70521) (@lem5447588 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5447592 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term422 _70518 _70519 _70520 _70521) = (term614 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447591) (@lem5446290 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447593 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : (term423 _70518 _70519 _70520 _70521) = (term615 _70518 _70519 _70520 _70521).
Proof. exact (MK_COMB (@lem5447592 _70518 _70519 _70520 _70521) (@lem5447590 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5447594 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term615 _70518 _70519 _70520 _70521) : term615 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5447595 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term473 _70518 _70519 _70520 _70521) : term473 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5447596 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term448 _70518 _70521 _70519 _70520.
Proof. exact (h1). Qed.
Lemma lem5447597 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term446 _70518 _70521 _70519 _70520.
Proof. exact (proj2 (@lem5447596 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447599 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term445 _70518 _70521 _70519 _70520.
Proof. exact (proj2 (@lem5447597 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447601 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term444 _70518 _70521 _70519 _70520.
Proof. exact (proj2 (@lem5447599 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447603 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term443 _70518 _70521 _70519 _70520.
Proof. exact (proj2 (@lem5447601 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447605 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term288 _70519 _70520.
Proof. exact (proj2 (@lem5447603 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447606 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term441 _70518 _70519 _70520 _70521.
Proof. exact (proj1 (@lem5447603 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447607 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term440 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5447606 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447612 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term315 _70519 _70520.
Proof. exact (proj1 (@lem5447607 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447614 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5447615 : term616 = term617.
Proof. exact (@lem5447614 term170 term192). Qed.
Lemma lem5447617 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447618 : term192 = term272.
Proof. exact (@lem5447617 term193). Qed.
Lemma lem5447620 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447621 : term170 = term235.
Proof. exact (@lem5447620 (NUMERAL 0)). Qed.
Lemma lem5447622 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5447623 : term618 = term619.
Proof. exact (MK_COMB (@lem5447622) (@lem5447621)). Qed.
Lemma lem5447624 : term617 = term620.
Proof. exact (MK_COMB (@lem5447623) (@lem5447618)). Qed.
Lemma lem5447625 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5447627 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447628 : term617 = term623.
Proof. exact (@lem5447627 (NUMERAL 0) term193). Qed.
Lemma lem5447629 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447630 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447631 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447630 h1) (fun h1 : term623 = True => @lem5447629)). Qed.
Lemma lem5447632 : term623 = True.
Proof. exact (EQ_MP (@lem5447631) (@lem5447629)). Qed.
Lemma lem5447633 : term617 = True.
Proof. exact (TRANS (@lem5447628) (@lem5447632)). Qed.
Lemma lem5447634 : True = term617.
Proof. exact (SYM (@lem5447633)). Qed.
Lemma lem5447635 : term617.
Proof. exact (EQ_MP (@lem5447634) (@lem0)). Qed.
Lemma lem5447636 : term625.
Proof. exact (@lem5447625 (@lem5447635)). Qed.
Lemma lem5447638 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447639 : term617 = term623.
Proof. exact (@lem5447638 (NUMERAL 0) term193). Qed.
Lemma lem5447640 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447641 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447642 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447641 h1) (fun h1 : term623 = True => @lem5447640)). Qed.
Lemma lem5447643 : term623 = True.
Proof. exact (EQ_MP (@lem5447642) (@lem5447640)). Qed.
Lemma lem5447644 : term617 = True.
Proof. exact (TRANS (@lem5447639) (@lem5447643)). Qed.
Lemma lem5447645 : True = term617.
Proof. exact (SYM (@lem5447644)). Qed.
Lemma lem5447646 : term617.
Proof. exact (EQ_MP (@lem5447645) (@lem0)). Qed.
Lemma lem5447647 : term620 = term626.
Proof. exact (@lem5447636 (@lem5447646)). Qed.
Lemma lem5447649 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447650 : term247 = term248.
Proof. exact (@lem5447649 term193 term193). Qed.
Lemma lem5447651 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447652 : term250 = term193.
Proof. exact (EQ_MP (@lem5447651) (@lem940073)). Qed.
Lemma lem5447653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447654 : term248 = term192.
Proof. exact (MK_COMB (@lem5447653) (@lem5447652)). Qed.
Lemma lem5447655 : term247 = term192.
Proof. exact (TRANS (@lem5447650) (@lem5447654)). Qed.
Lemma lem5447657 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5447658 : term628 = term170.
Proof. exact (@lem5447657 term193). Qed.
Lemma lem5447659 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5447660 : term629 = term618.
Proof. exact (MK_COMB (@lem5447659) (@lem5447658)). Qed.
Lemma lem5447661 : term626 = term617.
Proof. exact (MK_COMB (@lem5447660) (@lem5447655)). Qed.
Lemma lem5447663 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447664 : term617 = term623.
Proof. exact (@lem5447663 (NUMERAL 0) term193). Qed.
Lemma lem5447665 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447666 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447667 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447666 h1) (fun h1 : term623 = True => @lem5447665)). Qed.
Lemma lem5447668 : term623 = True.
Proof. exact (EQ_MP (@lem5447667) (@lem5447665)). Qed.
Lemma lem5447669 : term617 = True.
Proof. exact (TRANS (@lem5447664) (@lem5447668)). Qed.
Lemma lem5447670 : term626 = True.
Proof. exact (TRANS (@lem5447661) (@lem5447669)). Qed.
Lemma lem5447671 : term620 = True.
Proof. exact (TRANS (@lem5447647) (@lem5447670)). Qed.
Lemma lem5447672 : term617 = True.
Proof. exact (TRANS (@lem5447624) (@lem5447671)). Qed.
Lemma lem5447673 : term616 = True.
Proof. exact (TRANS (@lem5447615) (@lem5447672)). Qed.
Lemma lem5447674 : True = term616.
Proof. exact (SYM (@lem5447673)). Qed.
Lemma lem5447675 : term616.
Proof. exact (EQ_MP (@lem5447674) (@lem0)). Qed.
Lemma lem5447676 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term630 _70519 _70520.
Proof. exact (conj (@lem5447675) (@lem5447605 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447678 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5447679 (_70519 : int) (_70520 : int) : term632 _70519 _70520.
Proof. exact (@lem5447678 term192 (term284 _70519 _70520)). Qed.
Lemma lem5447680 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term633 _70519 _70520.
Proof. exact (@lem5447679 _70519 _70520 (@lem5447676 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447681 (_70519 : int) (_70520 : int) : (term634 _70519 _70520) = (term284 _70519 _70520).
Proof. exact (@lem1982733 (term284 _70519 _70520)). Qed.
Lemma lem5447682 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447683 (_70519 : int) (_70520 : int) : (term635 _70519 _70520) = (term287 _70519 _70520).
Proof. exact (MK_COMB (@lem5447682) (@lem5447681 _70519 _70520)). Qed.
Lemma lem5447684 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447685 (_70519 : int) (_70520 : int) : (term633 _70519 _70520) = (term288 _70519 _70520).
Proof. exact (MK_COMB (@lem5447683 _70519 _70520) (@lem5447684)). Qed.
Lemma lem5447686 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term288 _70519 _70520.
Proof. exact (EQ_MP (@lem5447685 _70519 _70520) (@lem5447680 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447688 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5447689 : term616 = term617.
Proof. exact (@lem5447688 term170 term192). Qed.
Lemma lem5447691 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447692 : term192 = term272.
Proof. exact (@lem5447691 term193). Qed.
Lemma lem5447694 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447695 : term170 = term235.
Proof. exact (@lem5447694 (NUMERAL 0)). Qed.
Lemma lem5447696 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5447697 : term618 = term619.
Proof. exact (MK_COMB (@lem5447696) (@lem5447695)). Qed.
Lemma lem5447698 : term617 = term620.
Proof. exact (MK_COMB (@lem5447697) (@lem5447692)). Qed.
Lemma lem5447699 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5447701 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447702 : term617 = term623.
Proof. exact (@lem5447701 (NUMERAL 0) term193). Qed.
Lemma lem5447703 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447704 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447705 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447704 h1) (fun h1 : term623 = True => @lem5447703)). Qed.
Lemma lem5447706 : term623 = True.
Proof. exact (EQ_MP (@lem5447705) (@lem5447703)). Qed.
Lemma lem5447707 : term617 = True.
Proof. exact (TRANS (@lem5447702) (@lem5447706)). Qed.
Lemma lem5447708 : True = term617.
Proof. exact (SYM (@lem5447707)). Qed.
Lemma lem5447709 : term617.
Proof. exact (EQ_MP (@lem5447708) (@lem0)). Qed.
Lemma lem5447710 : term625.
Proof. exact (@lem5447699 (@lem5447709)). Qed.
Lemma lem5447712 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447713 : term617 = term623.
Proof. exact (@lem5447712 (NUMERAL 0) term193). Qed.
Lemma lem5447714 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447715 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447716 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447715 h1) (fun h1 : term623 = True => @lem5447714)). Qed.
Lemma lem5447717 : term623 = True.
Proof. exact (EQ_MP (@lem5447716) (@lem5447714)). Qed.
Lemma lem5447718 : term617 = True.
Proof. exact (TRANS (@lem5447713) (@lem5447717)). Qed.
Lemma lem5447719 : True = term617.
Proof. exact (SYM (@lem5447718)). Qed.
Lemma lem5447720 : term617.
Proof. exact (EQ_MP (@lem5447719) (@lem0)). Qed.
Lemma lem5447721 : term620 = term626.
Proof. exact (@lem5447710 (@lem5447720)). Qed.
Lemma lem5447723 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447724 : term247 = term248.
Proof. exact (@lem5447723 term193 term193). Qed.
Lemma lem5447725 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447726 : term250 = term193.
Proof. exact (EQ_MP (@lem5447725) (@lem940073)). Qed.
Lemma lem5447727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447728 : term248 = term192.
Proof. exact (MK_COMB (@lem5447727) (@lem5447726)). Qed.
Lemma lem5447729 : term247 = term192.
Proof. exact (TRANS (@lem5447724) (@lem5447728)). Qed.
Lemma lem5447731 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5447732 : term628 = term170.
Proof. exact (@lem5447731 term193). Qed.
Lemma lem5447733 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5447734 : term629 = term618.
Proof. exact (MK_COMB (@lem5447733) (@lem5447732)). Qed.
Lemma lem5447735 : term626 = term617.
Proof. exact (MK_COMB (@lem5447734) (@lem5447729)). Qed.
Lemma lem5447737 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447738 : term617 = term623.
Proof. exact (@lem5447737 (NUMERAL 0) term193). Qed.
Lemma lem5447739 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447740 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447741 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447740 h1) (fun h1 : term623 = True => @lem5447739)). Qed.
Lemma lem5447742 : term623 = True.
Proof. exact (EQ_MP (@lem5447741) (@lem5447739)). Qed.
Lemma lem5447743 : term617 = True.
Proof. exact (TRANS (@lem5447738) (@lem5447742)). Qed.
Lemma lem5447744 : term626 = True.
Proof. exact (TRANS (@lem5447735) (@lem5447743)). Qed.
Lemma lem5447745 : term620 = True.
Proof. exact (TRANS (@lem5447721) (@lem5447744)). Qed.
Lemma lem5447746 : term617 = True.
Proof. exact (TRANS (@lem5447698) (@lem5447745)). Qed.
Lemma lem5447747 : term616 = True.
Proof. exact (TRANS (@lem5447689) (@lem5447746)). Qed.
Lemma lem5447748 : True = term616.
Proof. exact (SYM (@lem5447747)). Qed.
Lemma lem5447749 : term616.
Proof. exact (EQ_MP (@lem5447748) (@lem0)). Qed.
Lemma lem5447750 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term636 _70519 _70520.
Proof. exact (conj (@lem5447749) (@lem5447612 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447752 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5447753 (_70519 : int) (_70520 : int) : term637 _70519 _70520.
Proof. exact (@lem5447752 term192 (term312 _70519 _70520)). Qed.
Lemma lem5447754 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term638 _70519 _70520.
Proof. exact (@lem5447753 _70519 _70520 (@lem5447750 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447755 (_70519 : int) (_70520 : int) : (term639 _70519 _70520) = (term312 _70519 _70520).
Proof. exact (@lem1982733 (term312 _70519 _70520)). Qed.
Lemma lem5447756 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447757 (_70519 : int) (_70520 : int) : (term640 _70519 _70520) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5447756) (@lem5447755 _70519 _70520)). Qed.
Lemma lem5447758 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447759 (_70519 : int) (_70520 : int) : (term638 _70519 _70520) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5447757 _70519 _70520) (@lem5447758)). Qed.
Lemma lem5447760 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term315 _70519 _70520.
Proof. exact (EQ_MP (@lem5447759 _70519 _70520) (@lem5447754 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447761 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term641 _70519 _70520.
Proof. exact (conj (@lem5447760 _70518 _70521 _70519 _70520 h1) (@lem5447686 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447763 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5447764 (_70519 : int) (_70520 : int) : term643 _70519 _70520.
Proof. exact (@lem5447763 (term312 _70519 _70520) (term284 _70519 _70520)). Qed.
Lemma lem5447765 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term644 _70519 _70520.
Proof. exact (@lem5447764 _70519 _70520 (@lem5447761 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447766 (_70519 : int) (_70520 : int) : (term645 _70519 _70520) = (term646 _70519 _70520).
Proof. exact (@lem1982753 (real_of_int _70519) (term285 _70519) (term285 _70520) (term647 _70520)). Qed.
Lemma lem5447767 (_70519 : int) : (term648 _70519) = (term649 _70519).
Proof. exact (@lem1982715 term238 (real_of_int _70519)). Qed.
Lemma lem5447769 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447770 : term192 = term272.
Proof. exact (@lem5447769 term193). Qed.
Lemma lem5447772 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447773 : term238 = term239.
Proof. exact (@lem5447772 term193). Qed.
Lemma lem5447774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5447775 : term650 = term651.
Proof. exact (MK_COMB (@lem5447774) (@lem5447773)). Qed.
Lemma lem5447776 : term652 = term653.
Proof. exact (MK_COMB (@lem5447775) (@lem5447770)). Qed.
Lemma lem5447777 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5447779 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447780 : term617 = term623.
Proof. exact (@lem5447779 (NUMERAL 0) term193). Qed.
Lemma lem5447781 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447782 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447783 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447782 h1) (fun h1 : term623 = True => @lem5447781)). Qed.
Lemma lem5447784 : term623 = True.
Proof. exact (EQ_MP (@lem5447783) (@lem5447781)). Qed.
Lemma lem5447785 : term617 = True.
Proof. exact (TRANS (@lem5447780) (@lem5447784)). Qed.
Lemma lem5447786 : True = term617.
Proof. exact (SYM (@lem5447785)). Qed.
Lemma lem5447787 : term617.
Proof. exact (EQ_MP (@lem5447786) (@lem0)). Qed.
Lemma lem5447788 : term655.
Proof. exact (@lem5447777 (@lem5447787)). Qed.
Lemma lem5447790 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447791 : term617 = term623.
Proof. exact (@lem5447790 (NUMERAL 0) term193). Qed.
Lemma lem5447792 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447793 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447794 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447793 h1) (fun h1 : term623 = True => @lem5447792)). Qed.
Lemma lem5447795 : term623 = True.
Proof. exact (EQ_MP (@lem5447794) (@lem5447792)). Qed.
Lemma lem5447796 : term617 = True.
Proof. exact (TRANS (@lem5447791) (@lem5447795)). Qed.
Lemma lem5447797 : True = term617.
Proof. exact (SYM (@lem5447796)). Qed.
Lemma lem5447798 : term617.
Proof. exact (EQ_MP (@lem5447797) (@lem0)). Qed.
Lemma lem5447799 : term656.
Proof. exact (@lem5447788 (@lem5447798)). Qed.
Lemma lem5447801 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447802 : term617 = term623.
Proof. exact (@lem5447801 (NUMERAL 0) term193). Qed.
Lemma lem5447803 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447804 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447805 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447804 h1) (fun h1 : term623 = True => @lem5447803)). Qed.
Lemma lem5447806 : term623 = True.
Proof. exact (EQ_MP (@lem5447805) (@lem5447803)). Qed.
Lemma lem5447807 : term617 = True.
Proof. exact (TRANS (@lem5447802) (@lem5447806)). Qed.
Lemma lem5447808 : True = term617.
Proof. exact (SYM (@lem5447807)). Qed.
Lemma lem5447809 : term617.
Proof. exact (EQ_MP (@lem5447808) (@lem0)). Qed.
Lemma lem5447810 : term657.
Proof. exact (@lem5447799 (@lem5447809)). Qed.
Lemma lem5447812 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447813 : term247 = term248.
Proof. exact (@lem5447812 term193 term193). Qed.
Lemma lem5447814 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447815 : term250 = term193.
Proof. exact (EQ_MP (@lem5447814) (@lem940073)). Qed.
Lemma lem5447816 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447817 : term248 = term192.
Proof. exact (MK_COMB (@lem5447816) (@lem5447815)). Qed.
Lemma lem5447818 : term247 = term192.
Proof. exact (TRANS (@lem5447813) (@lem5447817)). Qed.
Lemma lem5447820 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5447821 : term273 = term278.
Proof. exact (@lem5447820 term193 term193). Qed.
Lemma lem5447822 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447823 : term250 = term193.
Proof. exact (EQ_MP (@lem5447822) (@lem940073)). Qed.
Lemma lem5447824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447825 : term248 = term192.
Proof. exact (MK_COMB (@lem5447824) (@lem5447823)). Qed.
Lemma lem5447826 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5447827 : term278 = term238.
Proof. exact (MK_COMB (@lem5447826) (@lem5447825)). Qed.
Lemma lem5447828 : term273 = term238.
Proof. exact (TRANS (@lem5447821) (@lem5447827)). Qed.
Lemma lem5447829 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5447830 : term658 = term650.
Proof. exact (MK_COMB (@lem5447829) (@lem5447828)). Qed.
Lemma lem5447831 : term659 = term652.
Proof. exact (MK_COMB (@lem5447830) (@lem5447818)). Qed.
Lemma lem5447833 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5447834 : term652 = term170.
Proof. exact (@lem5447833 term193). Qed.
Lemma lem5447835 : term659 = term170.
Proof. exact (TRANS (@lem5447831) (@lem5447834)). Qed.
Lemma lem5447836 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447837 : term661 = term662.
Proof. exact (MK_COMB (@lem5447836) (@lem5447835)). Qed.
Lemma lem5447838 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5447839 : term663 = term628.
Proof. exact (MK_COMB (@lem5447837) (@lem5447838)). Qed.
Lemma lem5447841 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5447842 : term628 = term170.
Proof. exact (@lem5447841 term193). Qed.
Lemma lem5447843 : term663 = term170.
Proof. exact (TRANS (@lem5447839) (@lem5447842)). Qed.
Lemma lem5447845 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447846 : term247 = term248.
Proof. exact (@lem5447845 term193 term193). Qed.
Lemma lem5447847 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447848 : term250 = term193.
Proof. exact (EQ_MP (@lem5447847) (@lem940073)). Qed.
Lemma lem5447849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447850 : term248 = term192.
Proof. exact (MK_COMB (@lem5447849) (@lem5447848)). Qed.
Lemma lem5447851 : term247 = term192.
Proof. exact (TRANS (@lem5447846) (@lem5447850)). Qed.
Lemma lem5447852 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5447853 : term664 = term628.
Proof. exact (MK_COMB (@lem5447852) (@lem5447851)). Qed.
Lemma lem5447855 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5447856 : term628 = term170.
Proof. exact (@lem5447855 term193). Qed.
Lemma lem5447857 : term664 = term170.
Proof. exact (TRANS (@lem5447853) (@lem5447856)). Qed.
Lemma lem5447858 : term170 = term664.
Proof. exact (SYM (@lem5447857)). Qed.
Lemma lem5447859 : term663 = term664.
Proof. exact (TRANS (@lem5447843) (@lem5447858)). Qed.
Lemma lem5447860 : term653 = term235.
Proof. exact (@lem5447810 (@lem5447859)). Qed.
Lemma lem5447861 : term652 = term235.
Proof. exact (TRANS (@lem5447776) (@lem5447860)). Qed.
Lemma lem5447863 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5447864 : term235 = term170.
Proof. exact (@lem5447863 term170). Qed.
Lemma lem5447865 : term652 = term170.
Proof. exact (TRANS (@lem5447861) (@lem5447864)). Qed.
Lemma lem5447866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447867 : term665 = term662.
Proof. exact (MK_COMB (@lem5447866) (@lem5447865)). Qed.
Lemma lem5447868 (_70519 : int) : (real_of_int _70519) = (real_of_int _70519).
Proof. exact (eq_refl (real_of_int _70519)). Qed.
Lemma lem5447869 (_70519 : int) : (term649 _70519) = (term666 _70519).
Proof. exact (MK_COMB (@lem5447867) (@lem5447868 _70519)). Qed.
Lemma lem5447870 (_70519 : int) : (term648 _70519) = (term666 _70519).
Proof. exact (TRANS (@lem5447767 _70519) (@lem5447869 _70519)). Qed.
Lemma lem5447871 (_70519 : int) : (term666 _70519) = term170.
Proof. exact (@lem1982719 (real_of_int _70519)). Qed.
Lemma lem5447872 (_70519 : int) : (term648 _70519) = term170.
Proof. exact (TRANS (@lem5447870 _70519) (@lem5447871 _70519)). Qed.
Lemma lem5447873 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5447874 (_70519 : int) : (term667 _70519) = term668.
Proof. exact (MK_COMB (@lem5447873) (@lem5447872 _70519)). Qed.
Lemma lem5447875 (_70520 : int) : (term669 _70520) = (term670 _70520).
Proof. exact (@lem1982763 (term285 _70520) (real_of_int _70520) term238). Qed.
Lemma lem5447876 (_70520 : int) : (term671 _70520) = (term649 _70520).
Proof. exact (@lem1982713 term238 (real_of_int _70520)). Qed.
Lemma lem5447878 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5447879 : term192 = term272.
Proof. exact (@lem5447878 term193). Qed.
Lemma lem5447881 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5447882 : term238 = term239.
Proof. exact (@lem5447881 term193). Qed.
Lemma lem5447883 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5447884 : term650 = term651.
Proof. exact (MK_COMB (@lem5447883) (@lem5447882)). Qed.
Lemma lem5447885 : term652 = term653.
Proof. exact (MK_COMB (@lem5447884) (@lem5447879)). Qed.
Lemma lem5447886 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5447888 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447889 : term617 = term623.
Proof. exact (@lem5447888 (NUMERAL 0) term193). Qed.
Lemma lem5447890 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447891 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447892 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447891 h1) (fun h1 : term623 = True => @lem5447890)). Qed.
Lemma lem5447893 : term623 = True.
Proof. exact (EQ_MP (@lem5447892) (@lem5447890)). Qed.
Lemma lem5447894 : term617 = True.
Proof. exact (TRANS (@lem5447889) (@lem5447893)). Qed.
Lemma lem5447895 : True = term617.
Proof. exact (SYM (@lem5447894)). Qed.
Lemma lem5447896 : term617.
Proof. exact (EQ_MP (@lem5447895) (@lem0)). Qed.
Lemma lem5447897 : term655.
Proof. exact (@lem5447886 (@lem5447896)). Qed.
Lemma lem5447899 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447900 : term617 = term623.
Proof. exact (@lem5447899 (NUMERAL 0) term193). Qed.
Lemma lem5447901 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447902 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447903 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447902 h1) (fun h1 : term623 = True => @lem5447901)). Qed.
Lemma lem5447904 : term623 = True.
Proof. exact (EQ_MP (@lem5447903) (@lem5447901)). Qed.
Lemma lem5447905 : term617 = True.
Proof. exact (TRANS (@lem5447900) (@lem5447904)). Qed.
Lemma lem5447906 : True = term617.
Proof. exact (SYM (@lem5447905)). Qed.
Lemma lem5447907 : term617.
Proof. exact (EQ_MP (@lem5447906) (@lem0)). Qed.
Lemma lem5447908 : term656.
Proof. exact (@lem5447897 (@lem5447907)). Qed.
Lemma lem5447910 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5447911 : term617 = term623.
Proof. exact (@lem5447910 (NUMERAL 0) term193). Qed.
Lemma lem5447912 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5447913 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5447914 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5447913 h1) (fun h1 : term623 = True => @lem5447912)). Qed.
Lemma lem5447915 : term623 = True.
Proof. exact (EQ_MP (@lem5447914) (@lem5447912)). Qed.
Lemma lem5447916 : term617 = True.
Proof. exact (TRANS (@lem5447911) (@lem5447915)). Qed.
Lemma lem5447917 : True = term617.
Proof. exact (SYM (@lem5447916)). Qed.
Lemma lem5447918 : term617.
Proof. exact (EQ_MP (@lem5447917) (@lem0)). Qed.
Lemma lem5447919 : term657.
Proof. exact (@lem5447908 (@lem5447918)). Qed.
Lemma lem5447921 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447922 : term247 = term248.
Proof. exact (@lem5447921 term193 term193). Qed.
Lemma lem5447923 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447924 : term250 = term193.
Proof. exact (EQ_MP (@lem5447923) (@lem940073)). Qed.
Lemma lem5447925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447926 : term248 = term192.
Proof. exact (MK_COMB (@lem5447925) (@lem5447924)). Qed.
Lemma lem5447927 : term247 = term192.
Proof. exact (TRANS (@lem5447922) (@lem5447926)). Qed.
Lemma lem5447929 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5447930 : term273 = term278.
Proof. exact (@lem5447929 term193 term193). Qed.
Lemma lem5447931 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447932 : term250 = term193.
Proof. exact (EQ_MP (@lem5447931) (@lem940073)). Qed.
Lemma lem5447933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447934 : term248 = term192.
Proof. exact (MK_COMB (@lem5447933) (@lem5447932)). Qed.
Lemma lem5447935 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5447936 : term278 = term238.
Proof. exact (MK_COMB (@lem5447935) (@lem5447934)). Qed.
Lemma lem5447937 : term273 = term238.
Proof. exact (TRANS (@lem5447930) (@lem5447936)). Qed.
Lemma lem5447938 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5447939 : term658 = term650.
Proof. exact (MK_COMB (@lem5447938) (@lem5447937)). Qed.
Lemma lem5447940 : term659 = term652.
Proof. exact (MK_COMB (@lem5447939) (@lem5447927)). Qed.
Lemma lem5447942 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5447943 : term652 = term170.
Proof. exact (@lem5447942 term193). Qed.
Lemma lem5447944 : term659 = term170.
Proof. exact (TRANS (@lem5447940) (@lem5447943)). Qed.
Lemma lem5447945 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447946 : term661 = term662.
Proof. exact (MK_COMB (@lem5447945) (@lem5447944)). Qed.
Lemma lem5447947 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5447948 : term663 = term628.
Proof. exact (MK_COMB (@lem5447946) (@lem5447947)). Qed.
Lemma lem5447950 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5447951 : term628 = term170.
Proof. exact (@lem5447950 term193). Qed.
Lemma lem5447952 : term663 = term170.
Proof. exact (TRANS (@lem5447948) (@lem5447951)). Qed.
Lemma lem5447954 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5447955 : term247 = term248.
Proof. exact (@lem5447954 term193 term193). Qed.
Lemma lem5447956 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5447957 : term250 = term193.
Proof. exact (EQ_MP (@lem5447956) (@lem940073)). Qed.
Lemma lem5447958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5447959 : term248 = term192.
Proof. exact (MK_COMB (@lem5447958) (@lem5447957)). Qed.
Lemma lem5447960 : term247 = term192.
Proof. exact (TRANS (@lem5447955) (@lem5447959)). Qed.
Lemma lem5447961 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5447962 : term664 = term628.
Proof. exact (MK_COMB (@lem5447961) (@lem5447960)). Qed.
Lemma lem5447964 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5447965 : term628 = term170.
Proof. exact (@lem5447964 term193). Qed.
Lemma lem5447966 : term664 = term170.
Proof. exact (TRANS (@lem5447962) (@lem5447965)). Qed.
Lemma lem5447967 : term170 = term664.
Proof. exact (SYM (@lem5447966)). Qed.
Lemma lem5447968 : term663 = term664.
Proof. exact (TRANS (@lem5447952) (@lem5447967)). Qed.
Lemma lem5447969 : term653 = term235.
Proof. exact (@lem5447919 (@lem5447968)). Qed.
Lemma lem5447970 : term652 = term235.
Proof. exact (TRANS (@lem5447885) (@lem5447969)). Qed.
Lemma lem5447972 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5447973 : term235 = term170.
Proof. exact (@lem5447972 term170). Qed.
Lemma lem5447974 : term652 = term170.
Proof. exact (TRANS (@lem5447970) (@lem5447973)). Qed.
Lemma lem5447975 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5447976 : term665 = term662.
Proof. exact (MK_COMB (@lem5447975) (@lem5447974)). Qed.
Lemma lem5447977 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5447978 (_70520 : int) : (term649 _70520) = (term666 _70520).
Proof. exact (MK_COMB (@lem5447976) (@lem5447977 _70520)). Qed.
Lemma lem5447979 (_70520 : int) : (term671 _70520) = (term666 _70520).
Proof. exact (TRANS (@lem5447876 _70520) (@lem5447978 _70520)). Qed.
Lemma lem5447980 (_70520 : int) : (term666 _70520) = term170.
Proof. exact (@lem1982719 (real_of_int _70520)). Qed.
Lemma lem5447981 (_70520 : int) : (term671 _70520) = term170.
Proof. exact (TRANS (@lem5447979 _70520) (@lem5447980 _70520)). Qed.
Lemma lem5447982 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5447983 (_70520 : int) : (term672 _70520) = term668.
Proof. exact (MK_COMB (@lem5447982) (@lem5447981 _70520)). Qed.
Lemma lem5447984 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5447985 (_70520 : int) : (term670 _70520) = term673.
Proof. exact (MK_COMB (@lem5447983 _70520) (@lem5447984)). Qed.
Lemma lem5447986 (_70520 : int) : (term669 _70520) = term673.
Proof. exact (TRANS (@lem5447875 _70520) (@lem5447985 _70520)). Qed.
Lemma lem5447987 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5447988 (_70520 : int) : (term669 _70520) = term238.
Proof. exact (TRANS (@lem5447986 _70520) (@lem5447987)). Qed.
Lemma lem5447989 (_70519 : int) (_70520 : int) : (term646 _70519 _70520) = term673.
Proof. exact (MK_COMB (@lem5447874 _70519) (@lem5447988 _70520)). Qed.
Lemma lem5447990 (_70519 : int) (_70520 : int) : (term645 _70519 _70520) = term673.
Proof. exact (TRANS (@lem5447766 _70519 _70520) (@lem5447989 _70519 _70520)). Qed.
Lemma lem5447991 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5447992 (_70519 : int) (_70520 : int) : (term645 _70519 _70520) = term238.
Proof. exact (TRANS (@lem5447990 _70519 _70520) (@lem5447991)). Qed.
Lemma lem5447993 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5447994 (_70519 : int) (_70520 : int) : (term674 _70519 _70520) = term675.
Proof. exact (MK_COMB (@lem5447993) (@lem5447992 _70519 _70520)). Qed.
Lemma lem5447995 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5447996 (_70519 : int) (_70520 : int) : (term644 _70519 _70520) = term676.
Proof. exact (MK_COMB (@lem5447994 _70519 _70520) (@lem5447995)). Qed.
Lemma lem5447997 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : term676.
Proof. exact (EQ_MP (@lem5447996 _70519 _70520) (@lem5447765 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5447999 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5448000 : term676 = term677.
Proof. exact (@lem5447999 term170 term238). Qed.
Lemma lem5448002 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448003 : term238 = term239.
Proof. exact (@lem5448002 term193). Qed.
Lemma lem5448005 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448006 : term170 = term235.
Proof. exact (@lem5448005 (NUMERAL 0)). Qed.
Lemma lem5448007 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5448008 : term172 = term678.
Proof. exact (MK_COMB (@lem5448007) (@lem5448006)). Qed.
Lemma lem5448009 : term677 = term679.
Proof. exact (MK_COMB (@lem5448008) (@lem5448003)). Qed.
Lemma lem5448010 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5448012 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448013 : term617 = term623.
Proof. exact (@lem5448012 (NUMERAL 0) term193). Qed.
Lemma lem5448014 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448015 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448016 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448015 h1) (fun h1 : term623 = True => @lem5448014)). Qed.
Lemma lem5448017 : term623 = True.
Proof. exact (EQ_MP (@lem5448016) (@lem5448014)). Qed.
Lemma lem5448018 : term617 = True.
Proof. exact (TRANS (@lem5448013) (@lem5448017)). Qed.
Lemma lem5448019 : True = term617.
Proof. exact (SYM (@lem5448018)). Qed.
Lemma lem5448020 : term617.
Proof. exact (EQ_MP (@lem5448019) (@lem0)). Qed.
Lemma lem5448021 : term681.
Proof. exact (@lem5448010 (@lem5448020)). Qed.
Lemma lem5448023 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448024 : term617 = term623.
Proof. exact (@lem5448023 (NUMERAL 0) term193). Qed.
Lemma lem5448025 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448026 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448027 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448026 h1) (fun h1 : term623 = True => @lem5448025)). Qed.
Lemma lem5448028 : term623 = True.
Proof. exact (EQ_MP (@lem5448027) (@lem5448025)). Qed.
Lemma lem5448029 : term617 = True.
Proof. exact (TRANS (@lem5448024) (@lem5448028)). Qed.
Lemma lem5448030 : True = term617.
Proof. exact (SYM (@lem5448029)). Qed.
Lemma lem5448031 : term617.
Proof. exact (EQ_MP (@lem5448030) (@lem0)). Qed.
Lemma lem5448032 : term679 = term682.
Proof. exact (@lem5448021 (@lem5448031)). Qed.
Lemma lem5448034 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448035 : term273 = term278.
Proof. exact (@lem5448034 term193 term193). Qed.
Lemma lem5448036 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448037 : term250 = term193.
Proof. exact (EQ_MP (@lem5448036) (@lem940073)). Qed.
Lemma lem5448038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448039 : term248 = term192.
Proof. exact (MK_COMB (@lem5448038) (@lem5448037)). Qed.
Lemma lem5448040 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448041 : term278 = term238.
Proof. exact (MK_COMB (@lem5448040) (@lem5448039)). Qed.
Lemma lem5448042 : term273 = term238.
Proof. exact (TRANS (@lem5448035) (@lem5448041)). Qed.
Lemma lem5448044 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448045 : term628 = term170.
Proof. exact (@lem5448044 term193). Qed.
Lemma lem5448046 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5448047 : term683 = term172.
Proof. exact (MK_COMB (@lem5448046) (@lem5448045)). Qed.
Lemma lem5448048 : term682 = term677.
Proof. exact (MK_COMB (@lem5448047) (@lem5448042)). Qed.
Lemma lem5448050 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5448051 : term677 = term686.
Proof. exact (@lem5448050 (NUMERAL 0) term193). Qed.
Lemma lem5448052 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448053 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5448054 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448053 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5448052)). Qed.
Lemma lem5448055 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5448054) (@lem5448052)). Qed.
Lemma lem5448056 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5448057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5448058 : term687 = (and True).
Proof. exact (MK_COMB (@lem5448057) (@lem5448056)). Qed.
Lemma lem5448059 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5448058) (@lem5448055)). Qed.
Lemma lem5448061 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5448062 : term686 = False.
Proof. exact (TRANS (@lem5448059) (@lem5448061)). Qed.
Lemma lem5448063 : term677 = False.
Proof. exact (TRANS (@lem5448051) (@lem5448062)). Qed.
Lemma lem5448064 : term682 = False.
Proof. exact (TRANS (@lem5448048) (@lem5448063)). Qed.
Lemma lem5448065 : term679 = False.
Proof. exact (TRANS (@lem5448032) (@lem5448064)). Qed.
Lemma lem5448066 : term677 = False.
Proof. exact (TRANS (@lem5448009) (@lem5448065)). Qed.
Lemma lem5448067 : term676 = False.
Proof. exact (TRANS (@lem5448000) (@lem5448066)). Qed.
Lemma lem5448068 (_70518 : int) (_70521 : int) (_70519 : int) (_70520 : int) (h1 : term448 _70518 _70521 _70519 _70520) : False.
Proof. exact (EQ_MP (@lem5448067) (@lem5447997 _70518 _70521 _70519 _70520 h1)). Qed.
Lemma lem5448069 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term471 _70518 _70519 _70520 _70521) : term471 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5448070 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term454 _70519 _70520 _70518 _70521.
Proof. exact (h1). Qed.
Lemma lem5448071 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term452 _70519 _70520 _70518 _70521.
Proof. exact (proj2 (@lem5448070 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448073 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term451 _70519 _70520 _70518 _70521.
Proof. exact (proj2 (@lem5448071 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448075 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term450 _70519 _70520 _70518 _70521.
Proof. exact (proj2 (@lem5448073 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448077 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term449 _70519 _70520 _70518 _70521.
Proof. exact (proj2 (@lem5448075 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448079 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term290 _70518 _70521.
Proof. exact (proj2 (@lem5448077 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448080 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term441 _70518 _70519 _70520 _70521.
Proof. exact (proj1 (@lem5448077 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448082 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term438 _70519 _70518 _70521.
Proof. exact (proj1 (@lem5448080 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448083 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term318 _70518 _70521.
Proof. exact (proj2 (@lem5448082 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448088 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5448089 : term616 = term617.
Proof. exact (@lem5448088 term170 term192). Qed.
Lemma lem5448091 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448092 : term192 = term272.
Proof. exact (@lem5448091 term193). Qed.
Lemma lem5448094 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448095 : term170 = term235.
Proof. exact (@lem5448094 (NUMERAL 0)). Qed.
Lemma lem5448096 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448097 : term618 = term619.
Proof. exact (MK_COMB (@lem5448096) (@lem5448095)). Qed.
Lemma lem5448098 : term617 = term620.
Proof. exact (MK_COMB (@lem5448097) (@lem5448092)). Qed.
Lemma lem5448099 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5448101 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448102 : term617 = term623.
Proof. exact (@lem5448101 (NUMERAL 0) term193). Qed.
Lemma lem5448103 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448104 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448105 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448104 h1) (fun h1 : term623 = True => @lem5448103)). Qed.
Lemma lem5448106 : term623 = True.
Proof. exact (EQ_MP (@lem5448105) (@lem5448103)). Qed.
Lemma lem5448107 : term617 = True.
Proof. exact (TRANS (@lem5448102) (@lem5448106)). Qed.
Lemma lem5448108 : True = term617.
Proof. exact (SYM (@lem5448107)). Qed.
Lemma lem5448109 : term617.
Proof. exact (EQ_MP (@lem5448108) (@lem0)). Qed.
Lemma lem5448110 : term625.
Proof. exact (@lem5448099 (@lem5448109)). Qed.
Lemma lem5448112 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448113 : term617 = term623.
Proof. exact (@lem5448112 (NUMERAL 0) term193). Qed.
Lemma lem5448114 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448115 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448116 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448115 h1) (fun h1 : term623 = True => @lem5448114)). Qed.
Lemma lem5448117 : term623 = True.
Proof. exact (EQ_MP (@lem5448116) (@lem5448114)). Qed.
Lemma lem5448118 : term617 = True.
Proof. exact (TRANS (@lem5448113) (@lem5448117)). Qed.
Lemma lem5448119 : True = term617.
Proof. exact (SYM (@lem5448118)). Qed.
Lemma lem5448120 : term617.
Proof. exact (EQ_MP (@lem5448119) (@lem0)). Qed.
Lemma lem5448121 : term620 = term626.
Proof. exact (@lem5448110 (@lem5448120)). Qed.
Lemma lem5448123 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448124 : term247 = term248.
Proof. exact (@lem5448123 term193 term193). Qed.
Lemma lem5448125 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448126 : term250 = term193.
Proof. exact (EQ_MP (@lem5448125) (@lem940073)). Qed.
Lemma lem5448127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448128 : term248 = term192.
Proof. exact (MK_COMB (@lem5448127) (@lem5448126)). Qed.
Lemma lem5448129 : term247 = term192.
Proof. exact (TRANS (@lem5448124) (@lem5448128)). Qed.
Lemma lem5448131 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448132 : term628 = term170.
Proof. exact (@lem5448131 term193). Qed.
Lemma lem5448133 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448134 : term629 = term618.
Proof. exact (MK_COMB (@lem5448133) (@lem5448132)). Qed.
Lemma lem5448135 : term626 = term617.
Proof. exact (MK_COMB (@lem5448134) (@lem5448129)). Qed.
Lemma lem5448137 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448138 : term617 = term623.
Proof. exact (@lem5448137 (NUMERAL 0) term193). Qed.
Lemma lem5448139 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448140 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448141 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448140 h1) (fun h1 : term623 = True => @lem5448139)). Qed.
Lemma lem5448142 : term623 = True.
Proof. exact (EQ_MP (@lem5448141) (@lem5448139)). Qed.
Lemma lem5448143 : term617 = True.
Proof. exact (TRANS (@lem5448138) (@lem5448142)). Qed.
Lemma lem5448144 : term626 = True.
Proof. exact (TRANS (@lem5448135) (@lem5448143)). Qed.
Lemma lem5448145 : term620 = True.
Proof. exact (TRANS (@lem5448121) (@lem5448144)). Qed.
Lemma lem5448146 : term617 = True.
Proof. exact (TRANS (@lem5448098) (@lem5448145)). Qed.
Lemma lem5448147 : term616 = True.
Proof. exact (TRANS (@lem5448089) (@lem5448146)). Qed.
Lemma lem5448148 : True = term616.
Proof. exact (SYM (@lem5448147)). Qed.
Lemma lem5448149 : term616.
Proof. exact (EQ_MP (@lem5448148) (@lem0)). Qed.
Lemma lem5448150 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term688 _70518 _70521.
Proof. exact (conj (@lem5448149) (@lem5448079 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448152 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5448153 (_70518 : int) (_70521 : int) : term689 _70518 _70521.
Proof. exact (@lem5448152 term192 (term283 _70518 _70521)). Qed.
Lemma lem5448154 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term690 _70518 _70521.
Proof. exact (@lem5448153 _70518 _70521 (@lem5448150 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448155 (_70518 : int) (_70521 : int) : (term691 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (@lem1982733 (term283 _70518 _70521)). Qed.
Lemma lem5448156 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5448157 (_70518 : int) (_70521 : int) : (term692 _70518 _70521) = (term289 _70518 _70521).
Proof. exact (MK_COMB (@lem5448156) (@lem5448155 _70518 _70521)). Qed.
Lemma lem5448158 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5448159 (_70518 : int) (_70521 : int) : (term690 _70518 _70521) = (term290 _70518 _70521).
Proof. exact (MK_COMB (@lem5448157 _70518 _70521) (@lem5448158)). Qed.
Lemma lem5448160 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term290 _70518 _70521.
Proof. exact (EQ_MP (@lem5448159 _70518 _70521) (@lem5448154 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448162 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5448163 : term616 = term617.
Proof. exact (@lem5448162 term170 term192). Qed.
Lemma lem5448165 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448166 : term192 = term272.
Proof. exact (@lem5448165 term193). Qed.
Lemma lem5448168 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448169 : term170 = term235.
Proof. exact (@lem5448168 (NUMERAL 0)). Qed.
Lemma lem5448170 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448171 : term618 = term619.
Proof. exact (MK_COMB (@lem5448170) (@lem5448169)). Qed.
Lemma lem5448172 : term617 = term620.
Proof. exact (MK_COMB (@lem5448171) (@lem5448166)). Qed.
Lemma lem5448173 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5448175 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448176 : term617 = term623.
Proof. exact (@lem5448175 (NUMERAL 0) term193). Qed.
Lemma lem5448177 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448178 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448179 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448178 h1) (fun h1 : term623 = True => @lem5448177)). Qed.
Lemma lem5448180 : term623 = True.
Proof. exact (EQ_MP (@lem5448179) (@lem5448177)). Qed.
Lemma lem5448181 : term617 = True.
Proof. exact (TRANS (@lem5448176) (@lem5448180)). Qed.
Lemma lem5448182 : True = term617.
Proof. exact (SYM (@lem5448181)). Qed.
Lemma lem5448183 : term617.
Proof. exact (EQ_MP (@lem5448182) (@lem0)). Qed.
Lemma lem5448184 : term625.
Proof. exact (@lem5448173 (@lem5448183)). Qed.
Lemma lem5448186 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448187 : term617 = term623.
Proof. exact (@lem5448186 (NUMERAL 0) term193). Qed.
Lemma lem5448188 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448189 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448190 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448189 h1) (fun h1 : term623 = True => @lem5448188)). Qed.
Lemma lem5448191 : term623 = True.
Proof. exact (EQ_MP (@lem5448190) (@lem5448188)). Qed.
Lemma lem5448192 : term617 = True.
Proof. exact (TRANS (@lem5448187) (@lem5448191)). Qed.
Lemma lem5448193 : True = term617.
Proof. exact (SYM (@lem5448192)). Qed.
Lemma lem5448194 : term617.
Proof. exact (EQ_MP (@lem5448193) (@lem0)). Qed.
Lemma lem5448195 : term620 = term626.
Proof. exact (@lem5448184 (@lem5448194)). Qed.
Lemma lem5448197 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448198 : term247 = term248.
Proof. exact (@lem5448197 term193 term193). Qed.
Lemma lem5448199 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448200 : term250 = term193.
Proof. exact (EQ_MP (@lem5448199) (@lem940073)). Qed.
Lemma lem5448201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448202 : term248 = term192.
Proof. exact (MK_COMB (@lem5448201) (@lem5448200)). Qed.
Lemma lem5448203 : term247 = term192.
Proof. exact (TRANS (@lem5448198) (@lem5448202)). Qed.
Lemma lem5448205 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448206 : term628 = term170.
Proof. exact (@lem5448205 term193). Qed.
Lemma lem5448207 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448208 : term629 = term618.
Proof. exact (MK_COMB (@lem5448207) (@lem5448206)). Qed.
Lemma lem5448209 : term626 = term617.
Proof. exact (MK_COMB (@lem5448208) (@lem5448203)). Qed.
Lemma lem5448211 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448212 : term617 = term623.
Proof. exact (@lem5448211 (NUMERAL 0) term193). Qed.
Lemma lem5448213 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448214 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448215 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448214 h1) (fun h1 : term623 = True => @lem5448213)). Qed.
Lemma lem5448216 : term623 = True.
Proof. exact (EQ_MP (@lem5448215) (@lem5448213)). Qed.
Lemma lem5448217 : term617 = True.
Proof. exact (TRANS (@lem5448212) (@lem5448216)). Qed.
Lemma lem5448218 : term626 = True.
Proof. exact (TRANS (@lem5448209) (@lem5448217)). Qed.
Lemma lem5448219 : term620 = True.
Proof. exact (TRANS (@lem5448195) (@lem5448218)). Qed.
Lemma lem5448220 : term617 = True.
Proof. exact (TRANS (@lem5448172) (@lem5448219)). Qed.
Lemma lem5448221 : term616 = True.
Proof. exact (TRANS (@lem5448163) (@lem5448220)). Qed.
Lemma lem5448222 : True = term616.
Proof. exact (SYM (@lem5448221)). Qed.
Lemma lem5448223 : term616.
Proof. exact (EQ_MP (@lem5448222) (@lem0)). Qed.
Lemma lem5448224 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term693 _70518 _70521.
Proof. exact (conj (@lem5448223) (@lem5448083 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448226 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5448227 (_70518 : int) (_70521 : int) : term694 _70518 _70521.
Proof. exact (@lem5448226 term192 (term316 _70518 _70521)). Qed.
Lemma lem5448228 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term695 _70518 _70521.
Proof. exact (@lem5448227 _70518 _70521 (@lem5448224 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448229 (_70518 : int) (_70521 : int) : (term696 _70518 _70521) = (term316 _70518 _70521).
Proof. exact (@lem1982733 (term316 _70518 _70521)). Qed.
Lemma lem5448230 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5448231 (_70518 : int) (_70521 : int) : (term697 _70518 _70521) = (term317 _70518 _70521).
Proof. exact (MK_COMB (@lem5448230) (@lem5448229 _70518 _70521)). Qed.
Lemma lem5448232 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5448233 (_70518 : int) (_70521 : int) : (term695 _70518 _70521) = (term318 _70518 _70521).
Proof. exact (MK_COMB (@lem5448231 _70518 _70521) (@lem5448232)). Qed.
Lemma lem5448234 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term318 _70518 _70521.
Proof. exact (EQ_MP (@lem5448233 _70518 _70521) (@lem5448228 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448235 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term698 _70518 _70521.
Proof. exact (conj (@lem5448234 _70519 _70520 _70518 _70521 h1) (@lem5448160 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448237 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5448238 (_70518 : int) (_70521 : int) : term699 _70518 _70521.
Proof. exact (@lem5448237 (term316 _70518 _70521) (term283 _70518 _70521)). Qed.
Lemma lem5448239 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term700 _70518 _70521.
Proof. exact (@lem5448238 _70518 _70521 (@lem5448235 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448240 (_70518 : int) (_70521 : int) : (term701 _70518 _70521) = (term702 _70518 _70521).
Proof. exact (@lem1982753 (term285 _70518) (real_of_int _70518) (real_of_int _70521) (term282 _70521)). Qed.
Lemma lem5448241 (_70518 : int) : (term671 _70518) = (term649 _70518).
Proof. exact (@lem1982713 term238 (real_of_int _70518)). Qed.
Lemma lem5448243 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448244 : term192 = term272.
Proof. exact (@lem5448243 term193). Qed.
Lemma lem5448246 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448247 : term238 = term239.
Proof. exact (@lem5448246 term193). Qed.
Lemma lem5448248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448249 : term650 = term651.
Proof. exact (MK_COMB (@lem5448248) (@lem5448247)). Qed.
Lemma lem5448250 : term652 = term653.
Proof. exact (MK_COMB (@lem5448249) (@lem5448244)). Qed.
Lemma lem5448251 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5448253 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448254 : term617 = term623.
Proof. exact (@lem5448253 (NUMERAL 0) term193). Qed.
Lemma lem5448255 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448256 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448257 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448256 h1) (fun h1 : term623 = True => @lem5448255)). Qed.
Lemma lem5448258 : term623 = True.
Proof. exact (EQ_MP (@lem5448257) (@lem5448255)). Qed.
Lemma lem5448259 : term617 = True.
Proof. exact (TRANS (@lem5448254) (@lem5448258)). Qed.
Lemma lem5448260 : True = term617.
Proof. exact (SYM (@lem5448259)). Qed.
Lemma lem5448261 : term617.
Proof. exact (EQ_MP (@lem5448260) (@lem0)). Qed.
Lemma lem5448262 : term655.
Proof. exact (@lem5448251 (@lem5448261)). Qed.
Lemma lem5448264 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448265 : term617 = term623.
Proof. exact (@lem5448264 (NUMERAL 0) term193). Qed.
Lemma lem5448266 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448267 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448268 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448267 h1) (fun h1 : term623 = True => @lem5448266)). Qed.
Lemma lem5448269 : term623 = True.
Proof. exact (EQ_MP (@lem5448268) (@lem5448266)). Qed.
Lemma lem5448270 : term617 = True.
Proof. exact (TRANS (@lem5448265) (@lem5448269)). Qed.
Lemma lem5448271 : True = term617.
Proof. exact (SYM (@lem5448270)). Qed.
Lemma lem5448272 : term617.
Proof. exact (EQ_MP (@lem5448271) (@lem0)). Qed.
Lemma lem5448273 : term656.
Proof. exact (@lem5448262 (@lem5448272)). Qed.
Lemma lem5448275 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448276 : term617 = term623.
Proof. exact (@lem5448275 (NUMERAL 0) term193). Qed.
Lemma lem5448277 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448278 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448279 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448278 h1) (fun h1 : term623 = True => @lem5448277)). Qed.
Lemma lem5448280 : term623 = True.
Proof. exact (EQ_MP (@lem5448279) (@lem5448277)). Qed.
Lemma lem5448281 : term617 = True.
Proof. exact (TRANS (@lem5448276) (@lem5448280)). Qed.
Lemma lem5448282 : True = term617.
Proof. exact (SYM (@lem5448281)). Qed.
Lemma lem5448283 : term617.
Proof. exact (EQ_MP (@lem5448282) (@lem0)). Qed.
Lemma lem5448284 : term657.
Proof. exact (@lem5448273 (@lem5448283)). Qed.
Lemma lem5448286 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448287 : term247 = term248.
Proof. exact (@lem5448286 term193 term193). Qed.
Lemma lem5448288 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448289 : term250 = term193.
Proof. exact (EQ_MP (@lem5448288) (@lem940073)). Qed.
Lemma lem5448290 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448291 : term248 = term192.
Proof. exact (MK_COMB (@lem5448290) (@lem5448289)). Qed.
Lemma lem5448292 : term247 = term192.
Proof. exact (TRANS (@lem5448287) (@lem5448291)). Qed.
Lemma lem5448294 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448295 : term273 = term278.
Proof. exact (@lem5448294 term193 term193). Qed.
Lemma lem5448296 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448297 : term250 = term193.
Proof. exact (EQ_MP (@lem5448296) (@lem940073)). Qed.
Lemma lem5448298 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448299 : term248 = term192.
Proof. exact (MK_COMB (@lem5448298) (@lem5448297)). Qed.
Lemma lem5448300 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448301 : term278 = term238.
Proof. exact (MK_COMB (@lem5448300) (@lem5448299)). Qed.
Lemma lem5448302 : term273 = term238.
Proof. exact (TRANS (@lem5448295) (@lem5448301)). Qed.
Lemma lem5448303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448304 : term658 = term650.
Proof. exact (MK_COMB (@lem5448303) (@lem5448302)). Qed.
Lemma lem5448305 : term659 = term652.
Proof. exact (MK_COMB (@lem5448304) (@lem5448292)). Qed.
Lemma lem5448307 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5448308 : term652 = term170.
Proof. exact (@lem5448307 term193). Qed.
Lemma lem5448309 : term659 = term170.
Proof. exact (TRANS (@lem5448305) (@lem5448308)). Qed.
Lemma lem5448310 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448311 : term661 = term662.
Proof. exact (MK_COMB (@lem5448310) (@lem5448309)). Qed.
Lemma lem5448312 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5448313 : term663 = term628.
Proof. exact (MK_COMB (@lem5448311) (@lem5448312)). Qed.
Lemma lem5448315 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448316 : term628 = term170.
Proof. exact (@lem5448315 term193). Qed.
Lemma lem5448317 : term663 = term170.
Proof. exact (TRANS (@lem5448313) (@lem5448316)). Qed.
Lemma lem5448319 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448320 : term247 = term248.
Proof. exact (@lem5448319 term193 term193). Qed.
Lemma lem5448321 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448322 : term250 = term193.
Proof. exact (EQ_MP (@lem5448321) (@lem940073)). Qed.
Lemma lem5448323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448324 : term248 = term192.
Proof. exact (MK_COMB (@lem5448323) (@lem5448322)). Qed.
Lemma lem5448325 : term247 = term192.
Proof. exact (TRANS (@lem5448320) (@lem5448324)). Qed.
Lemma lem5448326 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5448327 : term664 = term628.
Proof. exact (MK_COMB (@lem5448326) (@lem5448325)). Qed.
Lemma lem5448329 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448330 : term628 = term170.
Proof. exact (@lem5448329 term193). Qed.
Lemma lem5448331 : term664 = term170.
Proof. exact (TRANS (@lem5448327) (@lem5448330)). Qed.
Lemma lem5448332 : term170 = term664.
Proof. exact (SYM (@lem5448331)). Qed.
Lemma lem5448333 : term663 = term664.
Proof. exact (TRANS (@lem5448317) (@lem5448332)). Qed.
Lemma lem5448334 : term653 = term235.
Proof. exact (@lem5448284 (@lem5448333)). Qed.
Lemma lem5448335 : term652 = term235.
Proof. exact (TRANS (@lem5448250) (@lem5448334)). Qed.
Lemma lem5448337 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5448338 : term235 = term170.
Proof. exact (@lem5448337 term170). Qed.
Lemma lem5448339 : term652 = term170.
Proof. exact (TRANS (@lem5448335) (@lem5448338)). Qed.
Lemma lem5448340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448341 : term665 = term662.
Proof. exact (MK_COMB (@lem5448340) (@lem5448339)). Qed.
Lemma lem5448342 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5448343 (_70518 : int) : (term649 _70518) = (term666 _70518).
Proof. exact (MK_COMB (@lem5448341) (@lem5448342 _70518)). Qed.
Lemma lem5448344 (_70518 : int) : (term671 _70518) = (term666 _70518).
Proof. exact (TRANS (@lem5448241 _70518) (@lem5448343 _70518)). Qed.
Lemma lem5448345 (_70518 : int) : (term666 _70518) = term170.
Proof. exact (@lem1982719 (real_of_int _70518)). Qed.
Lemma lem5448346 (_70518 : int) : (term671 _70518) = term170.
Proof. exact (TRANS (@lem5448344 _70518) (@lem5448345 _70518)). Qed.
Lemma lem5448347 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448348 (_70518 : int) : (term672 _70518) = term668.
Proof. exact (MK_COMB (@lem5448347) (@lem5448346 _70518)). Qed.
Lemma lem5448349 (_70521 : int) : (term703 _70521) = (term704 _70521).
Proof. exact (@lem1982763 (real_of_int _70521) (term285 _70521) term238). Qed.
Lemma lem5448350 (_70521 : int) : (term648 _70521) = (term649 _70521).
Proof. exact (@lem1982715 term238 (real_of_int _70521)). Qed.
Lemma lem5448352 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448353 : term192 = term272.
Proof. exact (@lem5448352 term193). Qed.
Lemma lem5448355 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448356 : term238 = term239.
Proof. exact (@lem5448355 term193). Qed.
Lemma lem5448357 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448358 : term650 = term651.
Proof. exact (MK_COMB (@lem5448357) (@lem5448356)). Qed.
Lemma lem5448359 : term652 = term653.
Proof. exact (MK_COMB (@lem5448358) (@lem5448353)). Qed.
Lemma lem5448360 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5448362 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448363 : term617 = term623.
Proof. exact (@lem5448362 (NUMERAL 0) term193). Qed.
Lemma lem5448364 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448365 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448366 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448365 h1) (fun h1 : term623 = True => @lem5448364)). Qed.
Lemma lem5448367 : term623 = True.
Proof. exact (EQ_MP (@lem5448366) (@lem5448364)). Qed.
Lemma lem5448368 : term617 = True.
Proof. exact (TRANS (@lem5448363) (@lem5448367)). Qed.
Lemma lem5448369 : True = term617.
Proof. exact (SYM (@lem5448368)). Qed.
Lemma lem5448370 : term617.
Proof. exact (EQ_MP (@lem5448369) (@lem0)). Qed.
Lemma lem5448371 : term655.
Proof. exact (@lem5448360 (@lem5448370)). Qed.
Lemma lem5448373 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448374 : term617 = term623.
Proof. exact (@lem5448373 (NUMERAL 0) term193). Qed.
Lemma lem5448375 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448376 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448377 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448376 h1) (fun h1 : term623 = True => @lem5448375)). Qed.
Lemma lem5448378 : term623 = True.
Proof. exact (EQ_MP (@lem5448377) (@lem5448375)). Qed.
Lemma lem5448379 : term617 = True.
Proof. exact (TRANS (@lem5448374) (@lem5448378)). Qed.
Lemma lem5448380 : True = term617.
Proof. exact (SYM (@lem5448379)). Qed.
Lemma lem5448381 : term617.
Proof. exact (EQ_MP (@lem5448380) (@lem0)). Qed.
Lemma lem5448382 : term656.
Proof. exact (@lem5448371 (@lem5448381)). Qed.
Lemma lem5448384 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448385 : term617 = term623.
Proof. exact (@lem5448384 (NUMERAL 0) term193). Qed.
Lemma lem5448386 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448387 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448388 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448387 h1) (fun h1 : term623 = True => @lem5448386)). Qed.
Lemma lem5448389 : term623 = True.
Proof. exact (EQ_MP (@lem5448388) (@lem5448386)). Qed.
Lemma lem5448390 : term617 = True.
Proof. exact (TRANS (@lem5448385) (@lem5448389)). Qed.
Lemma lem5448391 : True = term617.
Proof. exact (SYM (@lem5448390)). Qed.
Lemma lem5448392 : term617.
Proof. exact (EQ_MP (@lem5448391) (@lem0)). Qed.
Lemma lem5448393 : term657.
Proof. exact (@lem5448382 (@lem5448392)). Qed.
Lemma lem5448395 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448396 : term247 = term248.
Proof. exact (@lem5448395 term193 term193). Qed.
Lemma lem5448397 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448398 : term250 = term193.
Proof. exact (EQ_MP (@lem5448397) (@lem940073)). Qed.
Lemma lem5448399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448400 : term248 = term192.
Proof. exact (MK_COMB (@lem5448399) (@lem5448398)). Qed.
Lemma lem5448401 : term247 = term192.
Proof. exact (TRANS (@lem5448396) (@lem5448400)). Qed.
Lemma lem5448403 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448404 : term273 = term278.
Proof. exact (@lem5448403 term193 term193). Qed.
Lemma lem5448405 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448406 : term250 = term193.
Proof. exact (EQ_MP (@lem5448405) (@lem940073)). Qed.
Lemma lem5448407 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448408 : term248 = term192.
Proof. exact (MK_COMB (@lem5448407) (@lem5448406)). Qed.
Lemma lem5448409 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448410 : term278 = term238.
Proof. exact (MK_COMB (@lem5448409) (@lem5448408)). Qed.
Lemma lem5448411 : term273 = term238.
Proof. exact (TRANS (@lem5448404) (@lem5448410)). Qed.
Lemma lem5448412 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448413 : term658 = term650.
Proof. exact (MK_COMB (@lem5448412) (@lem5448411)). Qed.
Lemma lem5448414 : term659 = term652.
Proof. exact (MK_COMB (@lem5448413) (@lem5448401)). Qed.
Lemma lem5448416 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5448417 : term652 = term170.
Proof. exact (@lem5448416 term193). Qed.
Lemma lem5448418 : term659 = term170.
Proof. exact (TRANS (@lem5448414) (@lem5448417)). Qed.
Lemma lem5448419 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448420 : term661 = term662.
Proof. exact (MK_COMB (@lem5448419) (@lem5448418)). Qed.
Lemma lem5448421 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5448422 : term663 = term628.
Proof. exact (MK_COMB (@lem5448420) (@lem5448421)). Qed.
Lemma lem5448424 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448425 : term628 = term170.
Proof. exact (@lem5448424 term193). Qed.
Lemma lem5448426 : term663 = term170.
Proof. exact (TRANS (@lem5448422) (@lem5448425)). Qed.
Lemma lem5448428 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448429 : term247 = term248.
Proof. exact (@lem5448428 term193 term193). Qed.
Lemma lem5448430 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448431 : term250 = term193.
Proof. exact (EQ_MP (@lem5448430) (@lem940073)). Qed.
Lemma lem5448432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448433 : term248 = term192.
Proof. exact (MK_COMB (@lem5448432) (@lem5448431)). Qed.
Lemma lem5448434 : term247 = term192.
Proof. exact (TRANS (@lem5448429) (@lem5448433)). Qed.
Lemma lem5448435 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5448436 : term664 = term628.
Proof. exact (MK_COMB (@lem5448435) (@lem5448434)). Qed.
Lemma lem5448438 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448439 : term628 = term170.
Proof. exact (@lem5448438 term193). Qed.
Lemma lem5448440 : term664 = term170.
Proof. exact (TRANS (@lem5448436) (@lem5448439)). Qed.
Lemma lem5448441 : term170 = term664.
Proof. exact (SYM (@lem5448440)). Qed.
Lemma lem5448442 : term663 = term664.
Proof. exact (TRANS (@lem5448426) (@lem5448441)). Qed.
Lemma lem5448443 : term653 = term235.
Proof. exact (@lem5448393 (@lem5448442)). Qed.
Lemma lem5448444 : term652 = term235.
Proof. exact (TRANS (@lem5448359) (@lem5448443)). Qed.
Lemma lem5448446 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5448447 : term235 = term170.
Proof. exact (@lem5448446 term170). Qed.
Lemma lem5448448 : term652 = term170.
Proof. exact (TRANS (@lem5448444) (@lem5448447)). Qed.
Lemma lem5448449 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448450 : term665 = term662.
Proof. exact (MK_COMB (@lem5448449) (@lem5448448)). Qed.
Lemma lem5448451 (_70521 : int) : (real_of_int _70521) = (real_of_int _70521).
Proof. exact (eq_refl (real_of_int _70521)). Qed.
Lemma lem5448452 (_70521 : int) : (term649 _70521) = (term666 _70521).
Proof. exact (MK_COMB (@lem5448450) (@lem5448451 _70521)). Qed.
Lemma lem5448453 (_70521 : int) : (term648 _70521) = (term666 _70521).
Proof. exact (TRANS (@lem5448350 _70521) (@lem5448452 _70521)). Qed.
Lemma lem5448454 (_70521 : int) : (term666 _70521) = term170.
Proof. exact (@lem1982719 (real_of_int _70521)). Qed.
Lemma lem5448455 (_70521 : int) : (term648 _70521) = term170.
Proof. exact (TRANS (@lem5448453 _70521) (@lem5448454 _70521)). Qed.
Lemma lem5448456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448457 (_70521 : int) : (term667 _70521) = term668.
Proof. exact (MK_COMB (@lem5448456) (@lem5448455 _70521)). Qed.
Lemma lem5448458 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5448459 (_70521 : int) : (term704 _70521) = term673.
Proof. exact (MK_COMB (@lem5448457 _70521) (@lem5448458)). Qed.
Lemma lem5448460 (_70521 : int) : (term703 _70521) = term673.
Proof. exact (TRANS (@lem5448349 _70521) (@lem5448459 _70521)). Qed.
Lemma lem5448461 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5448462 (_70521 : int) : (term703 _70521) = term238.
Proof. exact (TRANS (@lem5448460 _70521) (@lem5448461)). Qed.
Lemma lem5448463 (_70518 : int) (_70521 : int) : (term702 _70518 _70521) = term673.
Proof. exact (MK_COMB (@lem5448348 _70518) (@lem5448462 _70521)). Qed.
Lemma lem5448464 (_70518 : int) (_70521 : int) : (term701 _70518 _70521) = term673.
Proof. exact (TRANS (@lem5448240 _70518 _70521) (@lem5448463 _70518 _70521)). Qed.
Lemma lem5448465 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5448466 (_70518 : int) (_70521 : int) : (term701 _70518 _70521) = term238.
Proof. exact (TRANS (@lem5448464 _70518 _70521) (@lem5448465)). Qed.
Lemma lem5448467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5448468 (_70518 : int) (_70521 : int) : (term705 _70518 _70521) = term675.
Proof. exact (MK_COMB (@lem5448467) (@lem5448466 _70518 _70521)). Qed.
Lemma lem5448469 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5448470 (_70518 : int) (_70521 : int) : (term700 _70518 _70521) = term676.
Proof. exact (MK_COMB (@lem5448468 _70518 _70521) (@lem5448469)). Qed.
Lemma lem5448471 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : term676.
Proof. exact (EQ_MP (@lem5448470 _70518 _70521) (@lem5448239 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448473 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5448474 : term676 = term677.
Proof. exact (@lem5448473 term170 term238). Qed.
Lemma lem5448476 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448477 : term238 = term239.
Proof. exact (@lem5448476 term193). Qed.
Lemma lem5448479 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448480 : term170 = term235.
Proof. exact (@lem5448479 (NUMERAL 0)). Qed.
Lemma lem5448481 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5448482 : term172 = term678.
Proof. exact (MK_COMB (@lem5448481) (@lem5448480)). Qed.
Lemma lem5448483 : term677 = term679.
Proof. exact (MK_COMB (@lem5448482) (@lem5448477)). Qed.
Lemma lem5448484 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5448486 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448487 : term617 = term623.
Proof. exact (@lem5448486 (NUMERAL 0) term193). Qed.
Lemma lem5448488 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448489 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448490 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448489 h1) (fun h1 : term623 = True => @lem5448488)). Qed.
Lemma lem5448491 : term623 = True.
Proof. exact (EQ_MP (@lem5448490) (@lem5448488)). Qed.
Lemma lem5448492 : term617 = True.
Proof. exact (TRANS (@lem5448487) (@lem5448491)). Qed.
Lemma lem5448493 : True = term617.
Proof. exact (SYM (@lem5448492)). Qed.
Lemma lem5448494 : term617.
Proof. exact (EQ_MP (@lem5448493) (@lem0)). Qed.
Lemma lem5448495 : term681.
Proof. exact (@lem5448484 (@lem5448494)). Qed.
Lemma lem5448497 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448498 : term617 = term623.
Proof. exact (@lem5448497 (NUMERAL 0) term193). Qed.
Lemma lem5448499 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448500 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448501 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448500 h1) (fun h1 : term623 = True => @lem5448499)). Qed.
Lemma lem5448502 : term623 = True.
Proof. exact (EQ_MP (@lem5448501) (@lem5448499)). Qed.
Lemma lem5448503 : term617 = True.
Proof. exact (TRANS (@lem5448498) (@lem5448502)). Qed.
Lemma lem5448504 : True = term617.
Proof. exact (SYM (@lem5448503)). Qed.
Lemma lem5448505 : term617.
Proof. exact (EQ_MP (@lem5448504) (@lem0)). Qed.
Lemma lem5448506 : term679 = term682.
Proof. exact (@lem5448495 (@lem5448505)). Qed.
Lemma lem5448508 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448509 : term273 = term278.
Proof. exact (@lem5448508 term193 term193). Qed.
Lemma lem5448510 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448511 : term250 = term193.
Proof. exact (EQ_MP (@lem5448510) (@lem940073)). Qed.
Lemma lem5448512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448513 : term248 = term192.
Proof. exact (MK_COMB (@lem5448512) (@lem5448511)). Qed.
Lemma lem5448514 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448515 : term278 = term238.
Proof. exact (MK_COMB (@lem5448514) (@lem5448513)). Qed.
Lemma lem5448516 : term273 = term238.
Proof. exact (TRANS (@lem5448509) (@lem5448515)). Qed.
Lemma lem5448518 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448519 : term628 = term170.
Proof. exact (@lem5448518 term193). Qed.
Lemma lem5448520 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5448521 : term683 = term172.
Proof. exact (MK_COMB (@lem5448520) (@lem5448519)). Qed.
Lemma lem5448522 : term682 = term677.
Proof. exact (MK_COMB (@lem5448521) (@lem5448516)). Qed.
Lemma lem5448524 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5448525 : term677 = term686.
Proof. exact (@lem5448524 (NUMERAL 0) term193). Qed.
Lemma lem5448526 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448527 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5448528 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448527 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5448526)). Qed.
Lemma lem5448529 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5448528) (@lem5448526)). Qed.
Lemma lem5448530 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5448531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5448532 : term687 = (and True).
Proof. exact (MK_COMB (@lem5448531) (@lem5448530)). Qed.
Lemma lem5448533 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5448532) (@lem5448529)). Qed.
Lemma lem5448535 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5448536 : term686 = False.
Proof. exact (TRANS (@lem5448533) (@lem5448535)). Qed.
Lemma lem5448537 : term677 = False.
Proof. exact (TRANS (@lem5448525) (@lem5448536)). Qed.
Lemma lem5448538 : term682 = False.
Proof. exact (TRANS (@lem5448522) (@lem5448537)). Qed.
Lemma lem5448539 : term679 = False.
Proof. exact (TRANS (@lem5448506) (@lem5448538)). Qed.
Lemma lem5448540 : term677 = False.
Proof. exact (TRANS (@lem5448483) (@lem5448539)). Qed.
Lemma lem5448541 : term676 = False.
Proof. exact (TRANS (@lem5448474) (@lem5448540)). Qed.
Lemma lem5448542 (_70519 : int) (_70520 : int) (_70518 : int) (_70521 : int) (h1 : term454 _70519 _70520 _70518 _70521) : False.
Proof. exact (EQ_MP (@lem5448541) (@lem5448471 _70519 _70520 _70518 _70521 h1)). Qed.
Lemma lem5448543 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term469 _70518 _70519 _70520 _70521) : term469 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5448544 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term460 _70520 _70521 _70518 _70519.
Proof. exact (h1). Qed.
Lemma lem5448545 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term458 _70520 _70521 _70518 _70519.
Proof. exact (proj2 (@lem5448544 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448547 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term457 _70520 _70521 _70518 _70519.
Proof. exact (proj2 (@lem5448545 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448549 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term456 _70520 _70521 _70518 _70519.
Proof. exact (proj2 (@lem5448547 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448551 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term455 _70520 _70521 _70518 _70519.
Proof. exact (proj2 (@lem5448549 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448553 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term290 _70518 _70519.
Proof. exact (proj2 (@lem5448551 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448554 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term441 _70518 _70519 _70520 _70521.
Proof. exact (proj1 (@lem5448551 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448556 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term438 _70519 _70518 _70521.
Proof. exact (proj1 (@lem5448554 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448558 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term318 _70518 _70519.
Proof. exact (proj1 (@lem5448556 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448562 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5448563 : term616 = term617.
Proof. exact (@lem5448562 term170 term192). Qed.
Lemma lem5448565 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448566 : term192 = term272.
Proof. exact (@lem5448565 term193). Qed.
Lemma lem5448568 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448569 : term170 = term235.
Proof. exact (@lem5448568 (NUMERAL 0)). Qed.
Lemma lem5448570 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448571 : term618 = term619.
Proof. exact (MK_COMB (@lem5448570) (@lem5448569)). Qed.
Lemma lem5448572 : term617 = term620.
Proof. exact (MK_COMB (@lem5448571) (@lem5448566)). Qed.
Lemma lem5448573 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5448575 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448576 : term617 = term623.
Proof. exact (@lem5448575 (NUMERAL 0) term193). Qed.
Lemma lem5448577 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448578 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448579 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448578 h1) (fun h1 : term623 = True => @lem5448577)). Qed.
Lemma lem5448580 : term623 = True.
Proof. exact (EQ_MP (@lem5448579) (@lem5448577)). Qed.
Lemma lem5448581 : term617 = True.
Proof. exact (TRANS (@lem5448576) (@lem5448580)). Qed.
Lemma lem5448582 : True = term617.
Proof. exact (SYM (@lem5448581)). Qed.
Lemma lem5448583 : term617.
Proof. exact (EQ_MP (@lem5448582) (@lem0)). Qed.
Lemma lem5448584 : term625.
Proof. exact (@lem5448573 (@lem5448583)). Qed.
Lemma lem5448586 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448587 : term617 = term623.
Proof. exact (@lem5448586 (NUMERAL 0) term193). Qed.
Lemma lem5448588 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448589 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448590 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448589 h1) (fun h1 : term623 = True => @lem5448588)). Qed.
Lemma lem5448591 : term623 = True.
Proof. exact (EQ_MP (@lem5448590) (@lem5448588)). Qed.
Lemma lem5448592 : term617 = True.
Proof. exact (TRANS (@lem5448587) (@lem5448591)). Qed.
Lemma lem5448593 : True = term617.
Proof. exact (SYM (@lem5448592)). Qed.
Lemma lem5448594 : term617.
Proof. exact (EQ_MP (@lem5448593) (@lem0)). Qed.
Lemma lem5448595 : term620 = term626.
Proof. exact (@lem5448584 (@lem5448594)). Qed.
Lemma lem5448597 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448598 : term247 = term248.
Proof. exact (@lem5448597 term193 term193). Qed.
Lemma lem5448599 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448600 : term250 = term193.
Proof. exact (EQ_MP (@lem5448599) (@lem940073)). Qed.
Lemma lem5448601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448602 : term248 = term192.
Proof. exact (MK_COMB (@lem5448601) (@lem5448600)). Qed.
Lemma lem5448603 : term247 = term192.
Proof. exact (TRANS (@lem5448598) (@lem5448602)). Qed.
Lemma lem5448605 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448606 : term628 = term170.
Proof. exact (@lem5448605 term193). Qed.
Lemma lem5448607 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448608 : term629 = term618.
Proof. exact (MK_COMB (@lem5448607) (@lem5448606)). Qed.
Lemma lem5448609 : term626 = term617.
Proof. exact (MK_COMB (@lem5448608) (@lem5448603)). Qed.
Lemma lem5448611 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448612 : term617 = term623.
Proof. exact (@lem5448611 (NUMERAL 0) term193). Qed.
Lemma lem5448613 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448614 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448615 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448614 h1) (fun h1 : term623 = True => @lem5448613)). Qed.
Lemma lem5448616 : term623 = True.
Proof. exact (EQ_MP (@lem5448615) (@lem5448613)). Qed.
Lemma lem5448617 : term617 = True.
Proof. exact (TRANS (@lem5448612) (@lem5448616)). Qed.
Lemma lem5448618 : term626 = True.
Proof. exact (TRANS (@lem5448609) (@lem5448617)). Qed.
Lemma lem5448619 : term620 = True.
Proof. exact (TRANS (@lem5448595) (@lem5448618)). Qed.
Lemma lem5448620 : term617 = True.
Proof. exact (TRANS (@lem5448572) (@lem5448619)). Qed.
Lemma lem5448621 : term616 = True.
Proof. exact (TRANS (@lem5448563) (@lem5448620)). Qed.
Lemma lem5448622 : True = term616.
Proof. exact (SYM (@lem5448621)). Qed.
Lemma lem5448623 : term616.
Proof. exact (EQ_MP (@lem5448622) (@lem0)). Qed.
Lemma lem5448624 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term688 _70518 _70519.
Proof. exact (conj (@lem5448623) (@lem5448553 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448626 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5448627 (_70518 : int) (_70519 : int) : term689 _70518 _70519.
Proof. exact (@lem5448626 term192 (term283 _70518 _70519)). Qed.
Lemma lem5448628 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term690 _70518 _70519.
Proof. exact (@lem5448627 _70518 _70519 (@lem5448624 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448629 (_70518 : int) (_70519 : int) : (term691 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (@lem1982733 (term283 _70518 _70519)). Qed.
Lemma lem5448630 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5448631 (_70518 : int) (_70519 : int) : (term692 _70518 _70519) = (term289 _70518 _70519).
Proof. exact (MK_COMB (@lem5448630) (@lem5448629 _70518 _70519)). Qed.
Lemma lem5448632 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5448633 (_70518 : int) (_70519 : int) : (term690 _70518 _70519) = (term290 _70518 _70519).
Proof. exact (MK_COMB (@lem5448631 _70518 _70519) (@lem5448632)). Qed.
Lemma lem5448634 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term290 _70518 _70519.
Proof. exact (EQ_MP (@lem5448633 _70518 _70519) (@lem5448628 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448636 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5448637 : term616 = term617.
Proof. exact (@lem5448636 term170 term192). Qed.
Lemma lem5448639 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448640 : term192 = term272.
Proof. exact (@lem5448639 term193). Qed.
Lemma lem5448642 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448643 : term170 = term235.
Proof. exact (@lem5448642 (NUMERAL 0)). Qed.
Lemma lem5448644 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448645 : term618 = term619.
Proof. exact (MK_COMB (@lem5448644) (@lem5448643)). Qed.
Lemma lem5448646 : term617 = term620.
Proof. exact (MK_COMB (@lem5448645) (@lem5448640)). Qed.
Lemma lem5448647 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5448649 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448650 : term617 = term623.
Proof. exact (@lem5448649 (NUMERAL 0) term193). Qed.
Lemma lem5448651 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448652 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448653 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448652 h1) (fun h1 : term623 = True => @lem5448651)). Qed.
Lemma lem5448654 : term623 = True.
Proof. exact (EQ_MP (@lem5448653) (@lem5448651)). Qed.
Lemma lem5448655 : term617 = True.
Proof. exact (TRANS (@lem5448650) (@lem5448654)). Qed.
Lemma lem5448656 : True = term617.
Proof. exact (SYM (@lem5448655)). Qed.
Lemma lem5448657 : term617.
Proof. exact (EQ_MP (@lem5448656) (@lem0)). Qed.
Lemma lem5448658 : term625.
Proof. exact (@lem5448647 (@lem5448657)). Qed.
Lemma lem5448660 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448661 : term617 = term623.
Proof. exact (@lem5448660 (NUMERAL 0) term193). Qed.
Lemma lem5448662 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448663 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448664 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448663 h1) (fun h1 : term623 = True => @lem5448662)). Qed.
Lemma lem5448665 : term623 = True.
Proof. exact (EQ_MP (@lem5448664) (@lem5448662)). Qed.
Lemma lem5448666 : term617 = True.
Proof. exact (TRANS (@lem5448661) (@lem5448665)). Qed.
Lemma lem5448667 : True = term617.
Proof. exact (SYM (@lem5448666)). Qed.
Lemma lem5448668 : term617.
Proof. exact (EQ_MP (@lem5448667) (@lem0)). Qed.
Lemma lem5448669 : term620 = term626.
Proof. exact (@lem5448658 (@lem5448668)). Qed.
Lemma lem5448671 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448672 : term247 = term248.
Proof. exact (@lem5448671 term193 term193). Qed.
Lemma lem5448673 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448674 : term250 = term193.
Proof. exact (EQ_MP (@lem5448673) (@lem940073)). Qed.
Lemma lem5448675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448676 : term248 = term192.
Proof. exact (MK_COMB (@lem5448675) (@lem5448674)). Qed.
Lemma lem5448677 : term247 = term192.
Proof. exact (TRANS (@lem5448672) (@lem5448676)). Qed.
Lemma lem5448679 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448680 : term628 = term170.
Proof. exact (@lem5448679 term193). Qed.
Lemma lem5448681 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5448682 : term629 = term618.
Proof. exact (MK_COMB (@lem5448681) (@lem5448680)). Qed.
Lemma lem5448683 : term626 = term617.
Proof. exact (MK_COMB (@lem5448682) (@lem5448677)). Qed.
Lemma lem5448685 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448686 : term617 = term623.
Proof. exact (@lem5448685 (NUMERAL 0) term193). Qed.
Lemma lem5448687 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448688 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448689 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448688 h1) (fun h1 : term623 = True => @lem5448687)). Qed.
Lemma lem5448690 : term623 = True.
Proof. exact (EQ_MP (@lem5448689) (@lem5448687)). Qed.
Lemma lem5448691 : term617 = True.
Proof. exact (TRANS (@lem5448686) (@lem5448690)). Qed.
Lemma lem5448692 : term626 = True.
Proof. exact (TRANS (@lem5448683) (@lem5448691)). Qed.
Lemma lem5448693 : term620 = True.
Proof. exact (TRANS (@lem5448669) (@lem5448692)). Qed.
Lemma lem5448694 : term617 = True.
Proof. exact (TRANS (@lem5448646) (@lem5448693)). Qed.
Lemma lem5448695 : term616 = True.
Proof. exact (TRANS (@lem5448637) (@lem5448694)). Qed.
Lemma lem5448696 : True = term616.
Proof. exact (SYM (@lem5448695)). Qed.
Lemma lem5448697 : term616.
Proof. exact (EQ_MP (@lem5448696) (@lem0)). Qed.
Lemma lem5448698 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term693 _70518 _70519.
Proof. exact (conj (@lem5448697) (@lem5448558 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448700 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5448701 (_70518 : int) (_70519 : int) : term694 _70518 _70519.
Proof. exact (@lem5448700 term192 (term316 _70518 _70519)). Qed.
Lemma lem5448702 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term695 _70518 _70519.
Proof. exact (@lem5448701 _70518 _70519 (@lem5448698 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448703 (_70518 : int) (_70519 : int) : (term696 _70518 _70519) = (term316 _70518 _70519).
Proof. exact (@lem1982733 (term316 _70518 _70519)). Qed.
Lemma lem5448704 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5448705 (_70518 : int) (_70519 : int) : (term697 _70518 _70519) = (term317 _70518 _70519).
Proof. exact (MK_COMB (@lem5448704) (@lem5448703 _70518 _70519)). Qed.
Lemma lem5448706 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5448707 (_70518 : int) (_70519 : int) : (term695 _70518 _70519) = (term318 _70518 _70519).
Proof. exact (MK_COMB (@lem5448705 _70518 _70519) (@lem5448706)). Qed.
Lemma lem5448708 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term318 _70518 _70519.
Proof. exact (EQ_MP (@lem5448707 _70518 _70519) (@lem5448702 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448709 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term698 _70518 _70519.
Proof. exact (conj (@lem5448708 _70520 _70521 _70518 _70519 h1) (@lem5448634 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448711 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5448712 (_70518 : int) (_70519 : int) : term699 _70518 _70519.
Proof. exact (@lem5448711 (term316 _70518 _70519) (term283 _70518 _70519)). Qed.
Lemma lem5448713 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term700 _70518 _70519.
Proof. exact (@lem5448712 _70518 _70519 (@lem5448709 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448714 (_70518 : int) (_70519 : int) : (term701 _70518 _70519) = (term702 _70518 _70519).
Proof. exact (@lem1982753 (term285 _70518) (real_of_int _70518) (real_of_int _70519) (term282 _70519)). Qed.
Lemma lem5448715 (_70518 : int) : (term671 _70518) = (term649 _70518).
Proof. exact (@lem1982713 term238 (real_of_int _70518)). Qed.
Lemma lem5448717 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448718 : term192 = term272.
Proof. exact (@lem5448717 term193). Qed.
Lemma lem5448720 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448721 : term238 = term239.
Proof. exact (@lem5448720 term193). Qed.
Lemma lem5448722 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448723 : term650 = term651.
Proof. exact (MK_COMB (@lem5448722) (@lem5448721)). Qed.
Lemma lem5448724 : term652 = term653.
Proof. exact (MK_COMB (@lem5448723) (@lem5448718)). Qed.
Lemma lem5448725 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5448727 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448728 : term617 = term623.
Proof. exact (@lem5448727 (NUMERAL 0) term193). Qed.
Lemma lem5448729 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448730 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448731 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448730 h1) (fun h1 : term623 = True => @lem5448729)). Qed.
Lemma lem5448732 : term623 = True.
Proof. exact (EQ_MP (@lem5448731) (@lem5448729)). Qed.
Lemma lem5448733 : term617 = True.
Proof. exact (TRANS (@lem5448728) (@lem5448732)). Qed.
Lemma lem5448734 : True = term617.
Proof. exact (SYM (@lem5448733)). Qed.
Lemma lem5448735 : term617.
Proof. exact (EQ_MP (@lem5448734) (@lem0)). Qed.
Lemma lem5448736 : term655.
Proof. exact (@lem5448725 (@lem5448735)). Qed.
Lemma lem5448738 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448739 : term617 = term623.
Proof. exact (@lem5448738 (NUMERAL 0) term193). Qed.
Lemma lem5448740 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448741 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448742 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448741 h1) (fun h1 : term623 = True => @lem5448740)). Qed.
Lemma lem5448743 : term623 = True.
Proof. exact (EQ_MP (@lem5448742) (@lem5448740)). Qed.
Lemma lem5448744 : term617 = True.
Proof. exact (TRANS (@lem5448739) (@lem5448743)). Qed.
Lemma lem5448745 : True = term617.
Proof. exact (SYM (@lem5448744)). Qed.
Lemma lem5448746 : term617.
Proof. exact (EQ_MP (@lem5448745) (@lem0)). Qed.
Lemma lem5448747 : term656.
Proof. exact (@lem5448736 (@lem5448746)). Qed.
Lemma lem5448749 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448750 : term617 = term623.
Proof. exact (@lem5448749 (NUMERAL 0) term193). Qed.
Lemma lem5448751 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448752 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448753 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448752 h1) (fun h1 : term623 = True => @lem5448751)). Qed.
Lemma lem5448754 : term623 = True.
Proof. exact (EQ_MP (@lem5448753) (@lem5448751)). Qed.
Lemma lem5448755 : term617 = True.
Proof. exact (TRANS (@lem5448750) (@lem5448754)). Qed.
Lemma lem5448756 : True = term617.
Proof. exact (SYM (@lem5448755)). Qed.
Lemma lem5448757 : term617.
Proof. exact (EQ_MP (@lem5448756) (@lem0)). Qed.
Lemma lem5448758 : term657.
Proof. exact (@lem5448747 (@lem5448757)). Qed.
Lemma lem5448760 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448761 : term247 = term248.
Proof. exact (@lem5448760 term193 term193). Qed.
Lemma lem5448762 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448763 : term250 = term193.
Proof. exact (EQ_MP (@lem5448762) (@lem940073)). Qed.
Lemma lem5448764 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448765 : term248 = term192.
Proof. exact (MK_COMB (@lem5448764) (@lem5448763)). Qed.
Lemma lem5448766 : term247 = term192.
Proof. exact (TRANS (@lem5448761) (@lem5448765)). Qed.
Lemma lem5448768 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448769 : term273 = term278.
Proof. exact (@lem5448768 term193 term193). Qed.
Lemma lem5448770 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448771 : term250 = term193.
Proof. exact (EQ_MP (@lem5448770) (@lem940073)). Qed.
Lemma lem5448772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448773 : term248 = term192.
Proof. exact (MK_COMB (@lem5448772) (@lem5448771)). Qed.
Lemma lem5448774 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448775 : term278 = term238.
Proof. exact (MK_COMB (@lem5448774) (@lem5448773)). Qed.
Lemma lem5448776 : term273 = term238.
Proof. exact (TRANS (@lem5448769) (@lem5448775)). Qed.
Lemma lem5448777 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448778 : term658 = term650.
Proof. exact (MK_COMB (@lem5448777) (@lem5448776)). Qed.
Lemma lem5448779 : term659 = term652.
Proof. exact (MK_COMB (@lem5448778) (@lem5448766)). Qed.
Lemma lem5448781 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5448782 : term652 = term170.
Proof. exact (@lem5448781 term193). Qed.
Lemma lem5448783 : term659 = term170.
Proof. exact (TRANS (@lem5448779) (@lem5448782)). Qed.
Lemma lem5448784 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448785 : term661 = term662.
Proof. exact (MK_COMB (@lem5448784) (@lem5448783)). Qed.
Lemma lem5448786 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5448787 : term663 = term628.
Proof. exact (MK_COMB (@lem5448785) (@lem5448786)). Qed.
Lemma lem5448789 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448790 : term628 = term170.
Proof. exact (@lem5448789 term193). Qed.
Lemma lem5448791 : term663 = term170.
Proof. exact (TRANS (@lem5448787) (@lem5448790)). Qed.
Lemma lem5448793 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448794 : term247 = term248.
Proof. exact (@lem5448793 term193 term193). Qed.
Lemma lem5448795 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448796 : term250 = term193.
Proof. exact (EQ_MP (@lem5448795) (@lem940073)). Qed.
Lemma lem5448797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448798 : term248 = term192.
Proof. exact (MK_COMB (@lem5448797) (@lem5448796)). Qed.
Lemma lem5448799 : term247 = term192.
Proof. exact (TRANS (@lem5448794) (@lem5448798)). Qed.
Lemma lem5448800 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5448801 : term664 = term628.
Proof. exact (MK_COMB (@lem5448800) (@lem5448799)). Qed.
Lemma lem5448803 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448804 : term628 = term170.
Proof. exact (@lem5448803 term193). Qed.
Lemma lem5448805 : term664 = term170.
Proof. exact (TRANS (@lem5448801) (@lem5448804)). Qed.
Lemma lem5448806 : term170 = term664.
Proof. exact (SYM (@lem5448805)). Qed.
Lemma lem5448807 : term663 = term664.
Proof. exact (TRANS (@lem5448791) (@lem5448806)). Qed.
Lemma lem5448808 : term653 = term235.
Proof. exact (@lem5448758 (@lem5448807)). Qed.
Lemma lem5448809 : term652 = term235.
Proof. exact (TRANS (@lem5448724) (@lem5448808)). Qed.
Lemma lem5448811 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5448812 : term235 = term170.
Proof. exact (@lem5448811 term170). Qed.
Lemma lem5448813 : term652 = term170.
Proof. exact (TRANS (@lem5448809) (@lem5448812)). Qed.
Lemma lem5448814 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448815 : term665 = term662.
Proof. exact (MK_COMB (@lem5448814) (@lem5448813)). Qed.
Lemma lem5448816 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5448817 (_70518 : int) : (term649 _70518) = (term666 _70518).
Proof. exact (MK_COMB (@lem5448815) (@lem5448816 _70518)). Qed.
Lemma lem5448818 (_70518 : int) : (term671 _70518) = (term666 _70518).
Proof. exact (TRANS (@lem5448715 _70518) (@lem5448817 _70518)). Qed.
Lemma lem5448819 (_70518 : int) : (term666 _70518) = term170.
Proof. exact (@lem1982719 (real_of_int _70518)). Qed.
Lemma lem5448820 (_70518 : int) : (term671 _70518) = term170.
Proof. exact (TRANS (@lem5448818 _70518) (@lem5448819 _70518)). Qed.
Lemma lem5448821 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448822 (_70518 : int) : (term672 _70518) = term668.
Proof. exact (MK_COMB (@lem5448821) (@lem5448820 _70518)). Qed.
Lemma lem5448823 (_70519 : int) : (term703 _70519) = (term704 _70519).
Proof. exact (@lem1982763 (real_of_int _70519) (term285 _70519) term238). Qed.
Lemma lem5448824 (_70519 : int) : (term648 _70519) = (term649 _70519).
Proof. exact (@lem1982715 term238 (real_of_int _70519)). Qed.
Lemma lem5448826 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448827 : term192 = term272.
Proof. exact (@lem5448826 term193). Qed.
Lemma lem5448829 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448830 : term238 = term239.
Proof. exact (@lem5448829 term193). Qed.
Lemma lem5448831 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448832 : term650 = term651.
Proof. exact (MK_COMB (@lem5448831) (@lem5448830)). Qed.
Lemma lem5448833 : term652 = term653.
Proof. exact (MK_COMB (@lem5448832) (@lem5448827)). Qed.
Lemma lem5448834 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5448836 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448837 : term617 = term623.
Proof. exact (@lem5448836 (NUMERAL 0) term193). Qed.
Lemma lem5448838 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448839 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448840 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448839 h1) (fun h1 : term623 = True => @lem5448838)). Qed.
Lemma lem5448841 : term623 = True.
Proof. exact (EQ_MP (@lem5448840) (@lem5448838)). Qed.
Lemma lem5448842 : term617 = True.
Proof. exact (TRANS (@lem5448837) (@lem5448841)). Qed.
Lemma lem5448843 : True = term617.
Proof. exact (SYM (@lem5448842)). Qed.
Lemma lem5448844 : term617.
Proof. exact (EQ_MP (@lem5448843) (@lem0)). Qed.
Lemma lem5448845 : term655.
Proof. exact (@lem5448834 (@lem5448844)). Qed.
Lemma lem5448847 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448848 : term617 = term623.
Proof. exact (@lem5448847 (NUMERAL 0) term193). Qed.
Lemma lem5448849 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448850 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448851 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448850 h1) (fun h1 : term623 = True => @lem5448849)). Qed.
Lemma lem5448852 : term623 = True.
Proof. exact (EQ_MP (@lem5448851) (@lem5448849)). Qed.
Lemma lem5448853 : term617 = True.
Proof. exact (TRANS (@lem5448848) (@lem5448852)). Qed.
Lemma lem5448854 : True = term617.
Proof. exact (SYM (@lem5448853)). Qed.
Lemma lem5448855 : term617.
Proof. exact (EQ_MP (@lem5448854) (@lem0)). Qed.
Lemma lem5448856 : term656.
Proof. exact (@lem5448845 (@lem5448855)). Qed.
Lemma lem5448858 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448859 : term617 = term623.
Proof. exact (@lem5448858 (NUMERAL 0) term193). Qed.
Lemma lem5448860 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448861 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448862 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448861 h1) (fun h1 : term623 = True => @lem5448860)). Qed.
Lemma lem5448863 : term623 = True.
Proof. exact (EQ_MP (@lem5448862) (@lem5448860)). Qed.
Lemma lem5448864 : term617 = True.
Proof. exact (TRANS (@lem5448859) (@lem5448863)). Qed.
Lemma lem5448865 : True = term617.
Proof. exact (SYM (@lem5448864)). Qed.
Lemma lem5448866 : term617.
Proof. exact (EQ_MP (@lem5448865) (@lem0)). Qed.
Lemma lem5448867 : term657.
Proof. exact (@lem5448856 (@lem5448866)). Qed.
Lemma lem5448869 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448870 : term247 = term248.
Proof. exact (@lem5448869 term193 term193). Qed.
Lemma lem5448871 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448872 : term250 = term193.
Proof. exact (EQ_MP (@lem5448871) (@lem940073)). Qed.
Lemma lem5448873 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448874 : term248 = term192.
Proof. exact (MK_COMB (@lem5448873) (@lem5448872)). Qed.
Lemma lem5448875 : term247 = term192.
Proof. exact (TRANS (@lem5448870) (@lem5448874)). Qed.
Lemma lem5448877 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448878 : term273 = term278.
Proof. exact (@lem5448877 term193 term193). Qed.
Lemma lem5448879 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448880 : term250 = term193.
Proof. exact (EQ_MP (@lem5448879) (@lem940073)). Qed.
Lemma lem5448881 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448882 : term248 = term192.
Proof. exact (MK_COMB (@lem5448881) (@lem5448880)). Qed.
Lemma lem5448883 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448884 : term278 = term238.
Proof. exact (MK_COMB (@lem5448883) (@lem5448882)). Qed.
Lemma lem5448885 : term273 = term238.
Proof. exact (TRANS (@lem5448878) (@lem5448884)). Qed.
Lemma lem5448886 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448887 : term658 = term650.
Proof. exact (MK_COMB (@lem5448886) (@lem5448885)). Qed.
Lemma lem5448888 : term659 = term652.
Proof. exact (MK_COMB (@lem5448887) (@lem5448875)). Qed.
Lemma lem5448890 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5448891 : term652 = term170.
Proof. exact (@lem5448890 term193). Qed.
Lemma lem5448892 : term659 = term170.
Proof. exact (TRANS (@lem5448888) (@lem5448891)). Qed.
Lemma lem5448893 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448894 : term661 = term662.
Proof. exact (MK_COMB (@lem5448893) (@lem5448892)). Qed.
Lemma lem5448895 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5448896 : term663 = term628.
Proof. exact (MK_COMB (@lem5448894) (@lem5448895)). Qed.
Lemma lem5448898 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448899 : term628 = term170.
Proof. exact (@lem5448898 term193). Qed.
Lemma lem5448900 : term663 = term170.
Proof. exact (TRANS (@lem5448896) (@lem5448899)). Qed.
Lemma lem5448902 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5448903 : term247 = term248.
Proof. exact (@lem5448902 term193 term193). Qed.
Lemma lem5448904 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448905 : term250 = term193.
Proof. exact (EQ_MP (@lem5448904) (@lem940073)). Qed.
Lemma lem5448906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448907 : term248 = term192.
Proof. exact (MK_COMB (@lem5448906) (@lem5448905)). Qed.
Lemma lem5448908 : term247 = term192.
Proof. exact (TRANS (@lem5448903) (@lem5448907)). Qed.
Lemma lem5448909 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5448910 : term664 = term628.
Proof. exact (MK_COMB (@lem5448909) (@lem5448908)). Qed.
Lemma lem5448912 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448913 : term628 = term170.
Proof. exact (@lem5448912 term193). Qed.
Lemma lem5448914 : term664 = term170.
Proof. exact (TRANS (@lem5448910) (@lem5448913)). Qed.
Lemma lem5448915 : term170 = term664.
Proof. exact (SYM (@lem5448914)). Qed.
Lemma lem5448916 : term663 = term664.
Proof. exact (TRANS (@lem5448900) (@lem5448915)). Qed.
Lemma lem5448917 : term653 = term235.
Proof. exact (@lem5448867 (@lem5448916)). Qed.
Lemma lem5448918 : term652 = term235.
Proof. exact (TRANS (@lem5448833) (@lem5448917)). Qed.
Lemma lem5448920 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5448921 : term235 = term170.
Proof. exact (@lem5448920 term170). Qed.
Lemma lem5448922 : term652 = term170.
Proof. exact (TRANS (@lem5448918) (@lem5448921)). Qed.
Lemma lem5448923 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5448924 : term665 = term662.
Proof. exact (MK_COMB (@lem5448923) (@lem5448922)). Qed.
Lemma lem5448925 (_70519 : int) : (real_of_int _70519) = (real_of_int _70519).
Proof. exact (eq_refl (real_of_int _70519)). Qed.
Lemma lem5448926 (_70519 : int) : (term649 _70519) = (term666 _70519).
Proof. exact (MK_COMB (@lem5448924) (@lem5448925 _70519)). Qed.
Lemma lem5448927 (_70519 : int) : (term648 _70519) = (term666 _70519).
Proof. exact (TRANS (@lem5448824 _70519) (@lem5448926 _70519)). Qed.
Lemma lem5448928 (_70519 : int) : (term666 _70519) = term170.
Proof. exact (@lem1982719 (real_of_int _70519)). Qed.
Lemma lem5448929 (_70519 : int) : (term648 _70519) = term170.
Proof. exact (TRANS (@lem5448927 _70519) (@lem5448928 _70519)). Qed.
Lemma lem5448930 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5448931 (_70519 : int) : (term667 _70519) = term668.
Proof. exact (MK_COMB (@lem5448930) (@lem5448929 _70519)). Qed.
Lemma lem5448932 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5448933 (_70519 : int) : (term704 _70519) = term673.
Proof. exact (MK_COMB (@lem5448931 _70519) (@lem5448932)). Qed.
Lemma lem5448934 (_70519 : int) : (term703 _70519) = term673.
Proof. exact (TRANS (@lem5448823 _70519) (@lem5448933 _70519)). Qed.
Lemma lem5448935 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5448936 (_70519 : int) : (term703 _70519) = term238.
Proof. exact (TRANS (@lem5448934 _70519) (@lem5448935)). Qed.
Lemma lem5448937 (_70518 : int) (_70519 : int) : (term702 _70518 _70519) = term673.
Proof. exact (MK_COMB (@lem5448822 _70518) (@lem5448936 _70519)). Qed.
Lemma lem5448938 (_70518 : int) (_70519 : int) : (term701 _70518 _70519) = term673.
Proof. exact (TRANS (@lem5448714 _70518 _70519) (@lem5448937 _70518 _70519)). Qed.
Lemma lem5448939 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5448940 (_70518 : int) (_70519 : int) : (term701 _70518 _70519) = term238.
Proof. exact (TRANS (@lem5448938 _70518 _70519) (@lem5448939)). Qed.
Lemma lem5448941 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5448942 (_70518 : int) (_70519 : int) : (term705 _70518 _70519) = term675.
Proof. exact (MK_COMB (@lem5448941) (@lem5448940 _70518 _70519)). Qed.
Lemma lem5448943 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5448944 (_70518 : int) (_70519 : int) : (term700 _70518 _70519) = term676.
Proof. exact (MK_COMB (@lem5448942 _70518 _70519) (@lem5448943)). Qed.
Lemma lem5448945 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : term676.
Proof. exact (EQ_MP (@lem5448944 _70518 _70519) (@lem5448713 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5448947 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5448948 : term676 = term677.
Proof. exact (@lem5448947 term170 term238). Qed.
Lemma lem5448950 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5448951 : term238 = term239.
Proof. exact (@lem5448950 term193). Qed.
Lemma lem5448953 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5448954 : term170 = term235.
Proof. exact (@lem5448953 (NUMERAL 0)). Qed.
Lemma lem5448955 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5448956 : term172 = term678.
Proof. exact (MK_COMB (@lem5448955) (@lem5448954)). Qed.
Lemma lem5448957 : term677 = term679.
Proof. exact (MK_COMB (@lem5448956) (@lem5448951)). Qed.
Lemma lem5448958 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5448960 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448961 : term617 = term623.
Proof. exact (@lem5448960 (NUMERAL 0) term193). Qed.
Lemma lem5448962 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448963 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448964 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448963 h1) (fun h1 : term623 = True => @lem5448962)). Qed.
Lemma lem5448965 : term623 = True.
Proof. exact (EQ_MP (@lem5448964) (@lem5448962)). Qed.
Lemma lem5448966 : term617 = True.
Proof. exact (TRANS (@lem5448961) (@lem5448965)). Qed.
Lemma lem5448967 : True = term617.
Proof. exact (SYM (@lem5448966)). Qed.
Lemma lem5448968 : term617.
Proof. exact (EQ_MP (@lem5448967) (@lem0)). Qed.
Lemma lem5448969 : term681.
Proof. exact (@lem5448958 (@lem5448968)). Qed.
Lemma lem5448971 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5448972 : term617 = term623.
Proof. exact (@lem5448971 (NUMERAL 0) term193). Qed.
Lemma lem5448973 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5448974 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5448975 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5448974 h1) (fun h1 : term623 = True => @lem5448973)). Qed.
Lemma lem5448976 : term623 = True.
Proof. exact (EQ_MP (@lem5448975) (@lem5448973)). Qed.
Lemma lem5448977 : term617 = True.
Proof. exact (TRANS (@lem5448972) (@lem5448976)). Qed.
Lemma lem5448978 : True = term617.
Proof. exact (SYM (@lem5448977)). Qed.
Lemma lem5448979 : term617.
Proof. exact (EQ_MP (@lem5448978) (@lem0)). Qed.
Lemma lem5448980 : term679 = term682.
Proof. exact (@lem5448969 (@lem5448979)). Qed.
Lemma lem5448982 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5448983 : term273 = term278.
Proof. exact (@lem5448982 term193 term193). Qed.
Lemma lem5448984 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5448985 : term250 = term193.
Proof. exact (EQ_MP (@lem5448984) (@lem940073)). Qed.
Lemma lem5448986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5448987 : term248 = term192.
Proof. exact (MK_COMB (@lem5448986) (@lem5448985)). Qed.
Lemma lem5448988 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5448989 : term278 = term238.
Proof. exact (MK_COMB (@lem5448988) (@lem5448987)). Qed.
Lemma lem5448990 : term273 = term238.
Proof. exact (TRANS (@lem5448983) (@lem5448989)). Qed.
Lemma lem5448992 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5448993 : term628 = term170.
Proof. exact (@lem5448992 term193). Qed.
Lemma lem5448994 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5448995 : term683 = term172.
Proof. exact (MK_COMB (@lem5448994) (@lem5448993)). Qed.
Lemma lem5448996 : term682 = term677.
Proof. exact (MK_COMB (@lem5448995) (@lem5448990)). Qed.
Lemma lem5448998 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5448999 : term677 = term686.
Proof. exact (@lem5448998 (NUMERAL 0) term193). Qed.
Lemma lem5449000 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449001 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5449002 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449001 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5449000)). Qed.
Lemma lem5449003 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5449002) (@lem5449000)). Qed.
Lemma lem5449004 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5449005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5449006 : term687 = (and True).
Proof. exact (MK_COMB (@lem5449005) (@lem5449004)). Qed.
Lemma lem5449007 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5449006) (@lem5449003)). Qed.
Lemma lem5449009 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5449010 : term686 = False.
Proof. exact (TRANS (@lem5449007) (@lem5449009)). Qed.
Lemma lem5449011 : term677 = False.
Proof. exact (TRANS (@lem5448999) (@lem5449010)). Qed.
Lemma lem5449012 : term682 = False.
Proof. exact (TRANS (@lem5448996) (@lem5449011)). Qed.
Lemma lem5449013 : term679 = False.
Proof. exact (TRANS (@lem5448980) (@lem5449012)). Qed.
Lemma lem5449014 : term677 = False.
Proof. exact (TRANS (@lem5448957) (@lem5449013)). Qed.
Lemma lem5449015 : term676 = False.
Proof. exact (TRANS (@lem5448948) (@lem5449014)). Qed.
Lemma lem5449016 (_70520 : int) (_70521 : int) (_70518 : int) (_70519 : int) (h1 : term460 _70520 _70521 _70518 _70519) : False.
Proof. exact (EQ_MP (@lem5449015) (@lem5448945 _70520 _70521 _70518 _70519 h1)). Qed.
Lemma lem5449017 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term466 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5449018 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term464 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449017 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449020 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term463 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449018 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449022 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term462 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449020 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449024 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term461 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449022 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449026 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term290 _70520 _70521.
Proof. exact (proj2 (@lem5449024 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449027 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term441 _70518 _70519 _70520 _70521.
Proof. exact (proj1 (@lem5449024 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449028 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term440 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449027 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449032 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term318 _70520 _70521.
Proof. exact (proj2 (@lem5449028 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449035 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5449036 : term616 = term617.
Proof. exact (@lem5449035 term170 term192). Qed.
Lemma lem5449038 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449039 : term192 = term272.
Proof. exact (@lem5449038 term193). Qed.
Lemma lem5449041 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449042 : term170 = term235.
Proof. exact (@lem5449041 (NUMERAL 0)). Qed.
Lemma lem5449043 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449044 : term618 = term619.
Proof. exact (MK_COMB (@lem5449043) (@lem5449042)). Qed.
Lemma lem5449045 : term617 = term620.
Proof. exact (MK_COMB (@lem5449044) (@lem5449039)). Qed.
Lemma lem5449046 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5449048 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449049 : term617 = term623.
Proof. exact (@lem5449048 (NUMERAL 0) term193). Qed.
Lemma lem5449050 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449051 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449052 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449051 h1) (fun h1 : term623 = True => @lem5449050)). Qed.
Lemma lem5449053 : term623 = True.
Proof. exact (EQ_MP (@lem5449052) (@lem5449050)). Qed.
Lemma lem5449054 : term617 = True.
Proof. exact (TRANS (@lem5449049) (@lem5449053)). Qed.
Lemma lem5449055 : True = term617.
Proof. exact (SYM (@lem5449054)). Qed.
Lemma lem5449056 : term617.
Proof. exact (EQ_MP (@lem5449055) (@lem0)). Qed.
Lemma lem5449057 : term625.
Proof. exact (@lem5449046 (@lem5449056)). Qed.
Lemma lem5449059 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449060 : term617 = term623.
Proof. exact (@lem5449059 (NUMERAL 0) term193). Qed.
Lemma lem5449061 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449062 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449063 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449062 h1) (fun h1 : term623 = True => @lem5449061)). Qed.
Lemma lem5449064 : term623 = True.
Proof. exact (EQ_MP (@lem5449063) (@lem5449061)). Qed.
Lemma lem5449065 : term617 = True.
Proof. exact (TRANS (@lem5449060) (@lem5449064)). Qed.
Lemma lem5449066 : True = term617.
Proof. exact (SYM (@lem5449065)). Qed.
Lemma lem5449067 : term617.
Proof. exact (EQ_MP (@lem5449066) (@lem0)). Qed.
Lemma lem5449068 : term620 = term626.
Proof. exact (@lem5449057 (@lem5449067)). Qed.
Lemma lem5449070 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449071 : term247 = term248.
Proof. exact (@lem5449070 term193 term193). Qed.
Lemma lem5449072 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449073 : term250 = term193.
Proof. exact (EQ_MP (@lem5449072) (@lem940073)). Qed.
Lemma lem5449074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449075 : term248 = term192.
Proof. exact (MK_COMB (@lem5449074) (@lem5449073)). Qed.
Lemma lem5449076 : term247 = term192.
Proof. exact (TRANS (@lem5449071) (@lem5449075)). Qed.
Lemma lem5449078 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449079 : term628 = term170.
Proof. exact (@lem5449078 term193). Qed.
Lemma lem5449080 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449081 : term629 = term618.
Proof. exact (MK_COMB (@lem5449080) (@lem5449079)). Qed.
Lemma lem5449082 : term626 = term617.
Proof. exact (MK_COMB (@lem5449081) (@lem5449076)). Qed.
Lemma lem5449084 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449085 : term617 = term623.
Proof. exact (@lem5449084 (NUMERAL 0) term193). Qed.
Lemma lem5449086 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449087 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449088 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449087 h1) (fun h1 : term623 = True => @lem5449086)). Qed.
Lemma lem5449089 : term623 = True.
Proof. exact (EQ_MP (@lem5449088) (@lem5449086)). Qed.
Lemma lem5449090 : term617 = True.
Proof. exact (TRANS (@lem5449085) (@lem5449089)). Qed.
Lemma lem5449091 : term626 = True.
Proof. exact (TRANS (@lem5449082) (@lem5449090)). Qed.
Lemma lem5449092 : term620 = True.
Proof. exact (TRANS (@lem5449068) (@lem5449091)). Qed.
Lemma lem5449093 : term617 = True.
Proof. exact (TRANS (@lem5449045) (@lem5449092)). Qed.
Lemma lem5449094 : term616 = True.
Proof. exact (TRANS (@lem5449036) (@lem5449093)). Qed.
Lemma lem5449095 : True = term616.
Proof. exact (SYM (@lem5449094)). Qed.
Lemma lem5449096 : term616.
Proof. exact (EQ_MP (@lem5449095) (@lem0)). Qed.
Lemma lem5449097 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term688 _70520 _70521.
Proof. exact (conj (@lem5449096) (@lem5449026 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449099 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5449100 (_70520 : int) (_70521 : int) : term689 _70520 _70521.
Proof. exact (@lem5449099 term192 (term283 _70520 _70521)). Qed.
Lemma lem5449101 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term690 _70520 _70521.
Proof. exact (@lem5449100 _70520 _70521 (@lem5449097 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449102 (_70520 : int) (_70521 : int) : (term691 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (@lem1982733 (term283 _70520 _70521)). Qed.
Lemma lem5449103 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5449104 (_70520 : int) (_70521 : int) : (term692 _70520 _70521) = (term289 _70520 _70521).
Proof. exact (MK_COMB (@lem5449103) (@lem5449102 _70520 _70521)). Qed.
Lemma lem5449105 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5449106 (_70520 : int) (_70521 : int) : (term690 _70520 _70521) = (term290 _70520 _70521).
Proof. exact (MK_COMB (@lem5449104 _70520 _70521) (@lem5449105)). Qed.
Lemma lem5449107 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term290 _70520 _70521.
Proof. exact (EQ_MP (@lem5449106 _70520 _70521) (@lem5449101 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449109 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5449110 : term616 = term617.
Proof. exact (@lem5449109 term170 term192). Qed.
Lemma lem5449112 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449113 : term192 = term272.
Proof. exact (@lem5449112 term193). Qed.
Lemma lem5449115 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449116 : term170 = term235.
Proof. exact (@lem5449115 (NUMERAL 0)). Qed.
Lemma lem5449117 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449118 : term618 = term619.
Proof. exact (MK_COMB (@lem5449117) (@lem5449116)). Qed.
Lemma lem5449119 : term617 = term620.
Proof. exact (MK_COMB (@lem5449118) (@lem5449113)). Qed.
Lemma lem5449120 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5449122 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449123 : term617 = term623.
Proof. exact (@lem5449122 (NUMERAL 0) term193). Qed.
Lemma lem5449124 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449125 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449126 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449125 h1) (fun h1 : term623 = True => @lem5449124)). Qed.
Lemma lem5449127 : term623 = True.
Proof. exact (EQ_MP (@lem5449126) (@lem5449124)). Qed.
Lemma lem5449128 : term617 = True.
Proof. exact (TRANS (@lem5449123) (@lem5449127)). Qed.
Lemma lem5449129 : True = term617.
Proof. exact (SYM (@lem5449128)). Qed.
Lemma lem5449130 : term617.
Proof. exact (EQ_MP (@lem5449129) (@lem0)). Qed.
Lemma lem5449131 : term625.
Proof. exact (@lem5449120 (@lem5449130)). Qed.
Lemma lem5449133 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449134 : term617 = term623.
Proof. exact (@lem5449133 (NUMERAL 0) term193). Qed.
Lemma lem5449135 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449136 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449137 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449136 h1) (fun h1 : term623 = True => @lem5449135)). Qed.
Lemma lem5449138 : term623 = True.
Proof. exact (EQ_MP (@lem5449137) (@lem5449135)). Qed.
Lemma lem5449139 : term617 = True.
Proof. exact (TRANS (@lem5449134) (@lem5449138)). Qed.
Lemma lem5449140 : True = term617.
Proof. exact (SYM (@lem5449139)). Qed.
Lemma lem5449141 : term617.
Proof. exact (EQ_MP (@lem5449140) (@lem0)). Qed.
Lemma lem5449142 : term620 = term626.
Proof. exact (@lem5449131 (@lem5449141)). Qed.
Lemma lem5449144 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449145 : term247 = term248.
Proof. exact (@lem5449144 term193 term193). Qed.
Lemma lem5449146 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449147 : term250 = term193.
Proof. exact (EQ_MP (@lem5449146) (@lem940073)). Qed.
Lemma lem5449148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449149 : term248 = term192.
Proof. exact (MK_COMB (@lem5449148) (@lem5449147)). Qed.
Lemma lem5449150 : term247 = term192.
Proof. exact (TRANS (@lem5449145) (@lem5449149)). Qed.
Lemma lem5449152 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449153 : term628 = term170.
Proof. exact (@lem5449152 term193). Qed.
Lemma lem5449154 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449155 : term629 = term618.
Proof. exact (MK_COMB (@lem5449154) (@lem5449153)). Qed.
Lemma lem5449156 : term626 = term617.
Proof. exact (MK_COMB (@lem5449155) (@lem5449150)). Qed.
Lemma lem5449158 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449159 : term617 = term623.
Proof. exact (@lem5449158 (NUMERAL 0) term193). Qed.
Lemma lem5449160 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449161 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449162 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449161 h1) (fun h1 : term623 = True => @lem5449160)). Qed.
Lemma lem5449163 : term623 = True.
Proof. exact (EQ_MP (@lem5449162) (@lem5449160)). Qed.
Lemma lem5449164 : term617 = True.
Proof. exact (TRANS (@lem5449159) (@lem5449163)). Qed.
Lemma lem5449165 : term626 = True.
Proof. exact (TRANS (@lem5449156) (@lem5449164)). Qed.
Lemma lem5449166 : term620 = True.
Proof. exact (TRANS (@lem5449142) (@lem5449165)). Qed.
Lemma lem5449167 : term617 = True.
Proof. exact (TRANS (@lem5449119) (@lem5449166)). Qed.
Lemma lem5449168 : term616 = True.
Proof. exact (TRANS (@lem5449110) (@lem5449167)). Qed.
Lemma lem5449169 : True = term616.
Proof. exact (SYM (@lem5449168)). Qed.
Lemma lem5449170 : term616.
Proof. exact (EQ_MP (@lem5449169) (@lem0)). Qed.
Lemma lem5449171 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term693 _70520 _70521.
Proof. exact (conj (@lem5449170) (@lem5449032 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449173 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5449174 (_70520 : int) (_70521 : int) : term694 _70520 _70521.
Proof. exact (@lem5449173 term192 (term316 _70520 _70521)). Qed.
Lemma lem5449175 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term695 _70520 _70521.
Proof. exact (@lem5449174 _70520 _70521 (@lem5449171 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449176 (_70520 : int) (_70521 : int) : (term696 _70520 _70521) = (term316 _70520 _70521).
Proof. exact (@lem1982733 (term316 _70520 _70521)). Qed.
Lemma lem5449177 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5449178 (_70520 : int) (_70521 : int) : (term697 _70520 _70521) = (term317 _70520 _70521).
Proof. exact (MK_COMB (@lem5449177) (@lem5449176 _70520 _70521)). Qed.
Lemma lem5449179 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5449180 (_70520 : int) (_70521 : int) : (term695 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (MK_COMB (@lem5449178 _70520 _70521) (@lem5449179)). Qed.
Lemma lem5449181 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term318 _70520 _70521.
Proof. exact (EQ_MP (@lem5449180 _70520 _70521) (@lem5449175 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449182 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term698 _70520 _70521.
Proof. exact (conj (@lem5449181 _70518 _70519 _70520 _70521 h1) (@lem5449107 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449184 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5449185 (_70520 : int) (_70521 : int) : term699 _70520 _70521.
Proof. exact (@lem5449184 (term316 _70520 _70521) (term283 _70520 _70521)). Qed.
Lemma lem5449186 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term700 _70520 _70521.
Proof. exact (@lem5449185 _70520 _70521 (@lem5449182 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449187 (_70520 : int) (_70521 : int) : (term701 _70520 _70521) = (term702 _70520 _70521).
Proof. exact (@lem1982753 (term285 _70520) (real_of_int _70520) (real_of_int _70521) (term282 _70521)). Qed.
Lemma lem5449188 (_70520 : int) : (term671 _70520) = (term649 _70520).
Proof. exact (@lem1982713 term238 (real_of_int _70520)). Qed.
Lemma lem5449190 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449191 : term192 = term272.
Proof. exact (@lem5449190 term193). Qed.
Lemma lem5449193 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5449194 : term238 = term239.
Proof. exact (@lem5449193 term193). Qed.
Lemma lem5449195 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449196 : term650 = term651.
Proof. exact (MK_COMB (@lem5449195) (@lem5449194)). Qed.
Lemma lem5449197 : term652 = term653.
Proof. exact (MK_COMB (@lem5449196) (@lem5449191)). Qed.
Lemma lem5449198 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5449200 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449201 : term617 = term623.
Proof. exact (@lem5449200 (NUMERAL 0) term193). Qed.
Lemma lem5449202 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449203 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449204 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449203 h1) (fun h1 : term623 = True => @lem5449202)). Qed.
Lemma lem5449205 : term623 = True.
Proof. exact (EQ_MP (@lem5449204) (@lem5449202)). Qed.
Lemma lem5449206 : term617 = True.
Proof. exact (TRANS (@lem5449201) (@lem5449205)). Qed.
Lemma lem5449207 : True = term617.
Proof. exact (SYM (@lem5449206)). Qed.
Lemma lem5449208 : term617.
Proof. exact (EQ_MP (@lem5449207) (@lem0)). Qed.
Lemma lem5449209 : term655.
Proof. exact (@lem5449198 (@lem5449208)). Qed.
Lemma lem5449211 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449212 : term617 = term623.
Proof. exact (@lem5449211 (NUMERAL 0) term193). Qed.
Lemma lem5449213 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449214 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449215 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449214 h1) (fun h1 : term623 = True => @lem5449213)). Qed.
Lemma lem5449216 : term623 = True.
Proof. exact (EQ_MP (@lem5449215) (@lem5449213)). Qed.
Lemma lem5449217 : term617 = True.
Proof. exact (TRANS (@lem5449212) (@lem5449216)). Qed.
Lemma lem5449218 : True = term617.
Proof. exact (SYM (@lem5449217)). Qed.
Lemma lem5449219 : term617.
Proof. exact (EQ_MP (@lem5449218) (@lem0)). Qed.
Lemma lem5449220 : term656.
Proof. exact (@lem5449209 (@lem5449219)). Qed.
Lemma lem5449222 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449223 : term617 = term623.
Proof. exact (@lem5449222 (NUMERAL 0) term193). Qed.
Lemma lem5449224 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449225 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449226 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449225 h1) (fun h1 : term623 = True => @lem5449224)). Qed.
Lemma lem5449227 : term623 = True.
Proof. exact (EQ_MP (@lem5449226) (@lem5449224)). Qed.
Lemma lem5449228 : term617 = True.
Proof. exact (TRANS (@lem5449223) (@lem5449227)). Qed.
Lemma lem5449229 : True = term617.
Proof. exact (SYM (@lem5449228)). Qed.
Lemma lem5449230 : term617.
Proof. exact (EQ_MP (@lem5449229) (@lem0)). Qed.
Lemma lem5449231 : term657.
Proof. exact (@lem5449220 (@lem5449230)). Qed.
Lemma lem5449233 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449234 : term247 = term248.
Proof. exact (@lem5449233 term193 term193). Qed.
Lemma lem5449235 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449236 : term250 = term193.
Proof. exact (EQ_MP (@lem5449235) (@lem940073)). Qed.
Lemma lem5449237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449238 : term248 = term192.
Proof. exact (MK_COMB (@lem5449237) (@lem5449236)). Qed.
Lemma lem5449239 : term247 = term192.
Proof. exact (TRANS (@lem5449234) (@lem5449238)). Qed.
Lemma lem5449241 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5449242 : term273 = term278.
Proof. exact (@lem5449241 term193 term193). Qed.
Lemma lem5449243 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449244 : term250 = term193.
Proof. exact (EQ_MP (@lem5449243) (@lem940073)). Qed.
Lemma lem5449245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449246 : term248 = term192.
Proof. exact (MK_COMB (@lem5449245) (@lem5449244)). Qed.
Lemma lem5449247 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5449248 : term278 = term238.
Proof. exact (MK_COMB (@lem5449247) (@lem5449246)). Qed.
Lemma lem5449249 : term273 = term238.
Proof. exact (TRANS (@lem5449242) (@lem5449248)). Qed.
Lemma lem5449250 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449251 : term658 = term650.
Proof. exact (MK_COMB (@lem5449250) (@lem5449249)). Qed.
Lemma lem5449252 : term659 = term652.
Proof. exact (MK_COMB (@lem5449251) (@lem5449239)). Qed.
Lemma lem5449254 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5449255 : term652 = term170.
Proof. exact (@lem5449254 term193). Qed.
Lemma lem5449256 : term659 = term170.
Proof. exact (TRANS (@lem5449252) (@lem5449255)). Qed.
Lemma lem5449257 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449258 : term661 = term662.
Proof. exact (MK_COMB (@lem5449257) (@lem5449256)). Qed.
Lemma lem5449259 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5449260 : term663 = term628.
Proof. exact (MK_COMB (@lem5449258) (@lem5449259)). Qed.
Lemma lem5449262 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449263 : term628 = term170.
Proof. exact (@lem5449262 term193). Qed.
Lemma lem5449264 : term663 = term170.
Proof. exact (TRANS (@lem5449260) (@lem5449263)). Qed.
Lemma lem5449266 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449267 : term247 = term248.
Proof. exact (@lem5449266 term193 term193). Qed.
Lemma lem5449268 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449269 : term250 = term193.
Proof. exact (EQ_MP (@lem5449268) (@lem940073)). Qed.
Lemma lem5449270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449271 : term248 = term192.
Proof. exact (MK_COMB (@lem5449270) (@lem5449269)). Qed.
Lemma lem5449272 : term247 = term192.
Proof. exact (TRANS (@lem5449267) (@lem5449271)). Qed.
Lemma lem5449273 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5449274 : term664 = term628.
Proof. exact (MK_COMB (@lem5449273) (@lem5449272)). Qed.
Lemma lem5449276 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449277 : term628 = term170.
Proof. exact (@lem5449276 term193). Qed.
Lemma lem5449278 : term664 = term170.
Proof. exact (TRANS (@lem5449274) (@lem5449277)). Qed.
Lemma lem5449279 : term170 = term664.
Proof. exact (SYM (@lem5449278)). Qed.
Lemma lem5449280 : term663 = term664.
Proof. exact (TRANS (@lem5449264) (@lem5449279)). Qed.
Lemma lem5449281 : term653 = term235.
Proof. exact (@lem5449231 (@lem5449280)). Qed.
Lemma lem5449282 : term652 = term235.
Proof. exact (TRANS (@lem5449197) (@lem5449281)). Qed.
Lemma lem5449284 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5449285 : term235 = term170.
Proof. exact (@lem5449284 term170). Qed.
Lemma lem5449286 : term652 = term170.
Proof. exact (TRANS (@lem5449282) (@lem5449285)). Qed.
Lemma lem5449287 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449288 : term665 = term662.
Proof. exact (MK_COMB (@lem5449287) (@lem5449286)). Qed.
Lemma lem5449289 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5449290 (_70520 : int) : (term649 _70520) = (term666 _70520).
Proof. exact (MK_COMB (@lem5449288) (@lem5449289 _70520)). Qed.
Lemma lem5449291 (_70520 : int) : (term671 _70520) = (term666 _70520).
Proof. exact (TRANS (@lem5449188 _70520) (@lem5449290 _70520)). Qed.
Lemma lem5449292 (_70520 : int) : (term666 _70520) = term170.
Proof. exact (@lem1982719 (real_of_int _70520)). Qed.
Lemma lem5449293 (_70520 : int) : (term671 _70520) = term170.
Proof. exact (TRANS (@lem5449291 _70520) (@lem5449292 _70520)). Qed.
Lemma lem5449294 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449295 (_70520 : int) : (term672 _70520) = term668.
Proof. exact (MK_COMB (@lem5449294) (@lem5449293 _70520)). Qed.
Lemma lem5449296 (_70521 : int) : (term703 _70521) = (term704 _70521).
Proof. exact (@lem1982763 (real_of_int _70521) (term285 _70521) term238). Qed.
Lemma lem5449297 (_70521 : int) : (term648 _70521) = (term649 _70521).
Proof. exact (@lem1982715 term238 (real_of_int _70521)). Qed.
Lemma lem5449299 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449300 : term192 = term272.
Proof. exact (@lem5449299 term193). Qed.
Lemma lem5449302 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5449303 : term238 = term239.
Proof. exact (@lem5449302 term193). Qed.
Lemma lem5449304 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449305 : term650 = term651.
Proof. exact (MK_COMB (@lem5449304) (@lem5449303)). Qed.
Lemma lem5449306 : term652 = term653.
Proof. exact (MK_COMB (@lem5449305) (@lem5449300)). Qed.
Lemma lem5449307 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5449309 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449310 : term617 = term623.
Proof. exact (@lem5449309 (NUMERAL 0) term193). Qed.
Lemma lem5449311 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449312 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449313 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449312 h1) (fun h1 : term623 = True => @lem5449311)). Qed.
Lemma lem5449314 : term623 = True.
Proof. exact (EQ_MP (@lem5449313) (@lem5449311)). Qed.
Lemma lem5449315 : term617 = True.
Proof. exact (TRANS (@lem5449310) (@lem5449314)). Qed.
Lemma lem5449316 : True = term617.
Proof. exact (SYM (@lem5449315)). Qed.
Lemma lem5449317 : term617.
Proof. exact (EQ_MP (@lem5449316) (@lem0)). Qed.
Lemma lem5449318 : term655.
Proof. exact (@lem5449307 (@lem5449317)). Qed.
Lemma lem5449320 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449321 : term617 = term623.
Proof. exact (@lem5449320 (NUMERAL 0) term193). Qed.
Lemma lem5449322 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449323 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449324 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449323 h1) (fun h1 : term623 = True => @lem5449322)). Qed.
Lemma lem5449325 : term623 = True.
Proof. exact (EQ_MP (@lem5449324) (@lem5449322)). Qed.
Lemma lem5449326 : term617 = True.
Proof. exact (TRANS (@lem5449321) (@lem5449325)). Qed.
Lemma lem5449327 : True = term617.
Proof. exact (SYM (@lem5449326)). Qed.
Lemma lem5449328 : term617.
Proof. exact (EQ_MP (@lem5449327) (@lem0)). Qed.
Lemma lem5449329 : term656.
Proof. exact (@lem5449318 (@lem5449328)). Qed.
Lemma lem5449331 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449332 : term617 = term623.
Proof. exact (@lem5449331 (NUMERAL 0) term193). Qed.
Lemma lem5449333 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449334 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449335 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449334 h1) (fun h1 : term623 = True => @lem5449333)). Qed.
Lemma lem5449336 : term623 = True.
Proof. exact (EQ_MP (@lem5449335) (@lem5449333)). Qed.
Lemma lem5449337 : term617 = True.
Proof. exact (TRANS (@lem5449332) (@lem5449336)). Qed.
Lemma lem5449338 : True = term617.
Proof. exact (SYM (@lem5449337)). Qed.
Lemma lem5449339 : term617.
Proof. exact (EQ_MP (@lem5449338) (@lem0)). Qed.
Lemma lem5449340 : term657.
Proof. exact (@lem5449329 (@lem5449339)). Qed.
Lemma lem5449342 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449343 : term247 = term248.
Proof. exact (@lem5449342 term193 term193). Qed.
Lemma lem5449344 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449345 : term250 = term193.
Proof. exact (EQ_MP (@lem5449344) (@lem940073)). Qed.
Lemma lem5449346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449347 : term248 = term192.
Proof. exact (MK_COMB (@lem5449346) (@lem5449345)). Qed.
Lemma lem5449348 : term247 = term192.
Proof. exact (TRANS (@lem5449343) (@lem5449347)). Qed.
Lemma lem5449350 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5449351 : term273 = term278.
Proof. exact (@lem5449350 term193 term193). Qed.
Lemma lem5449352 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449353 : term250 = term193.
Proof. exact (EQ_MP (@lem5449352) (@lem940073)). Qed.
Lemma lem5449354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449355 : term248 = term192.
Proof. exact (MK_COMB (@lem5449354) (@lem5449353)). Qed.
Lemma lem5449356 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5449357 : term278 = term238.
Proof. exact (MK_COMB (@lem5449356) (@lem5449355)). Qed.
Lemma lem5449358 : term273 = term238.
Proof. exact (TRANS (@lem5449351) (@lem5449357)). Qed.
Lemma lem5449359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449360 : term658 = term650.
Proof. exact (MK_COMB (@lem5449359) (@lem5449358)). Qed.
Lemma lem5449361 : term659 = term652.
Proof. exact (MK_COMB (@lem5449360) (@lem5449348)). Qed.
Lemma lem5449363 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5449364 : term652 = term170.
Proof. exact (@lem5449363 term193). Qed.
Lemma lem5449365 : term659 = term170.
Proof. exact (TRANS (@lem5449361) (@lem5449364)). Qed.
Lemma lem5449366 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449367 : term661 = term662.
Proof. exact (MK_COMB (@lem5449366) (@lem5449365)). Qed.
Lemma lem5449368 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5449369 : term663 = term628.
Proof. exact (MK_COMB (@lem5449367) (@lem5449368)). Qed.
Lemma lem5449371 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449372 : term628 = term170.
Proof. exact (@lem5449371 term193). Qed.
Lemma lem5449373 : term663 = term170.
Proof. exact (TRANS (@lem5449369) (@lem5449372)). Qed.
Lemma lem5449375 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449376 : term247 = term248.
Proof. exact (@lem5449375 term193 term193). Qed.
Lemma lem5449377 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449378 : term250 = term193.
Proof. exact (EQ_MP (@lem5449377) (@lem940073)). Qed.
Lemma lem5449379 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449380 : term248 = term192.
Proof. exact (MK_COMB (@lem5449379) (@lem5449378)). Qed.
Lemma lem5449381 : term247 = term192.
Proof. exact (TRANS (@lem5449376) (@lem5449380)). Qed.
Lemma lem5449382 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5449383 : term664 = term628.
Proof. exact (MK_COMB (@lem5449382) (@lem5449381)). Qed.
Lemma lem5449385 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449386 : term628 = term170.
Proof. exact (@lem5449385 term193). Qed.
Lemma lem5449387 : term664 = term170.
Proof. exact (TRANS (@lem5449383) (@lem5449386)). Qed.
Lemma lem5449388 : term170 = term664.
Proof. exact (SYM (@lem5449387)). Qed.
Lemma lem5449389 : term663 = term664.
Proof. exact (TRANS (@lem5449373) (@lem5449388)). Qed.
Lemma lem5449390 : term653 = term235.
Proof. exact (@lem5449340 (@lem5449389)). Qed.
Lemma lem5449391 : term652 = term235.
Proof. exact (TRANS (@lem5449306) (@lem5449390)). Qed.
Lemma lem5449393 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5449394 : term235 = term170.
Proof. exact (@lem5449393 term170). Qed.
Lemma lem5449395 : term652 = term170.
Proof. exact (TRANS (@lem5449391) (@lem5449394)). Qed.
Lemma lem5449396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449397 : term665 = term662.
Proof. exact (MK_COMB (@lem5449396) (@lem5449395)). Qed.
Lemma lem5449398 (_70521 : int) : (real_of_int _70521) = (real_of_int _70521).
Proof. exact (eq_refl (real_of_int _70521)). Qed.
Lemma lem5449399 (_70521 : int) : (term649 _70521) = (term666 _70521).
Proof. exact (MK_COMB (@lem5449397) (@lem5449398 _70521)). Qed.
Lemma lem5449400 (_70521 : int) : (term648 _70521) = (term666 _70521).
Proof. exact (TRANS (@lem5449297 _70521) (@lem5449399 _70521)). Qed.
Lemma lem5449401 (_70521 : int) : (term666 _70521) = term170.
Proof. exact (@lem1982719 (real_of_int _70521)). Qed.
Lemma lem5449402 (_70521 : int) : (term648 _70521) = term170.
Proof. exact (TRANS (@lem5449400 _70521) (@lem5449401 _70521)). Qed.
Lemma lem5449403 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449404 (_70521 : int) : (term667 _70521) = term668.
Proof. exact (MK_COMB (@lem5449403) (@lem5449402 _70521)). Qed.
Lemma lem5449405 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5449406 (_70521 : int) : (term704 _70521) = term673.
Proof. exact (MK_COMB (@lem5449404 _70521) (@lem5449405)). Qed.
Lemma lem5449407 (_70521 : int) : (term703 _70521) = term673.
Proof. exact (TRANS (@lem5449296 _70521) (@lem5449406 _70521)). Qed.
Lemma lem5449408 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5449409 (_70521 : int) : (term703 _70521) = term238.
Proof. exact (TRANS (@lem5449407 _70521) (@lem5449408)). Qed.
Lemma lem5449410 (_70520 : int) (_70521 : int) : (term702 _70520 _70521) = term673.
Proof. exact (MK_COMB (@lem5449295 _70520) (@lem5449409 _70521)). Qed.
Lemma lem5449411 (_70520 : int) (_70521 : int) : (term701 _70520 _70521) = term673.
Proof. exact (TRANS (@lem5449187 _70520 _70521) (@lem5449410 _70520 _70521)). Qed.
Lemma lem5449412 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5449413 (_70520 : int) (_70521 : int) : (term701 _70520 _70521) = term238.
Proof. exact (TRANS (@lem5449411 _70520 _70521) (@lem5449412)). Qed.
Lemma lem5449414 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5449415 (_70520 : int) (_70521 : int) : (term705 _70520 _70521) = term675.
Proof. exact (MK_COMB (@lem5449414) (@lem5449413 _70520 _70521)). Qed.
Lemma lem5449416 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5449417 (_70520 : int) (_70521 : int) : (term700 _70520 _70521) = term676.
Proof. exact (MK_COMB (@lem5449415 _70520 _70521) (@lem5449416)). Qed.
Lemma lem5449418 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : term676.
Proof. exact (EQ_MP (@lem5449417 _70520 _70521) (@lem5449186 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449420 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5449421 : term676 = term677.
Proof. exact (@lem5449420 term170 term238). Qed.
Lemma lem5449423 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5449424 : term238 = term239.
Proof. exact (@lem5449423 term193). Qed.
Lemma lem5449426 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449427 : term170 = term235.
Proof. exact (@lem5449426 (NUMERAL 0)). Qed.
Lemma lem5449428 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5449429 : term172 = term678.
Proof. exact (MK_COMB (@lem5449428) (@lem5449427)). Qed.
Lemma lem5449430 : term677 = term679.
Proof. exact (MK_COMB (@lem5449429) (@lem5449424)). Qed.
Lemma lem5449431 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5449433 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449434 : term617 = term623.
Proof. exact (@lem5449433 (NUMERAL 0) term193). Qed.
Lemma lem5449435 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449436 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449437 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449436 h1) (fun h1 : term623 = True => @lem5449435)). Qed.
Lemma lem5449438 : term623 = True.
Proof. exact (EQ_MP (@lem5449437) (@lem5449435)). Qed.
Lemma lem5449439 : term617 = True.
Proof. exact (TRANS (@lem5449434) (@lem5449438)). Qed.
Lemma lem5449440 : True = term617.
Proof. exact (SYM (@lem5449439)). Qed.
Lemma lem5449441 : term617.
Proof. exact (EQ_MP (@lem5449440) (@lem0)). Qed.
Lemma lem5449442 : term681.
Proof. exact (@lem5449431 (@lem5449441)). Qed.
Lemma lem5449444 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449445 : term617 = term623.
Proof. exact (@lem5449444 (NUMERAL 0) term193). Qed.
Lemma lem5449446 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449447 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449448 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449447 h1) (fun h1 : term623 = True => @lem5449446)). Qed.
Lemma lem5449449 : term623 = True.
Proof. exact (EQ_MP (@lem5449448) (@lem5449446)). Qed.
Lemma lem5449450 : term617 = True.
Proof. exact (TRANS (@lem5449445) (@lem5449449)). Qed.
Lemma lem5449451 : True = term617.
Proof. exact (SYM (@lem5449450)). Qed.
Lemma lem5449452 : term617.
Proof. exact (EQ_MP (@lem5449451) (@lem0)). Qed.
Lemma lem5449453 : term679 = term682.
Proof. exact (@lem5449442 (@lem5449452)). Qed.
Lemma lem5449455 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5449456 : term273 = term278.
Proof. exact (@lem5449455 term193 term193). Qed.
Lemma lem5449457 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449458 : term250 = term193.
Proof. exact (EQ_MP (@lem5449457) (@lem940073)). Qed.
Lemma lem5449459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449460 : term248 = term192.
Proof. exact (MK_COMB (@lem5449459) (@lem5449458)). Qed.
Lemma lem5449461 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5449462 : term278 = term238.
Proof. exact (MK_COMB (@lem5449461) (@lem5449460)). Qed.
Lemma lem5449463 : term273 = term238.
Proof. exact (TRANS (@lem5449456) (@lem5449462)). Qed.
Lemma lem5449465 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449466 : term628 = term170.
Proof. exact (@lem5449465 term193). Qed.
Lemma lem5449467 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5449468 : term683 = term172.
Proof. exact (MK_COMB (@lem5449467) (@lem5449466)). Qed.
Lemma lem5449469 : term682 = term677.
Proof. exact (MK_COMB (@lem5449468) (@lem5449463)). Qed.
Lemma lem5449471 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5449472 : term677 = term686.
Proof. exact (@lem5449471 (NUMERAL 0) term193). Qed.
Lemma lem5449473 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449474 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5449475 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449474 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5449473)). Qed.
Lemma lem5449476 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5449475) (@lem5449473)). Qed.
Lemma lem5449477 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5449478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5449479 : term687 = (and True).
Proof. exact (MK_COMB (@lem5449478) (@lem5449477)). Qed.
Lemma lem5449480 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5449479) (@lem5449476)). Qed.
Lemma lem5449482 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5449483 : term686 = False.
Proof. exact (TRANS (@lem5449480) (@lem5449482)). Qed.
Lemma lem5449484 : term677 = False.
Proof. exact (TRANS (@lem5449472) (@lem5449483)). Qed.
Lemma lem5449485 : term682 = False.
Proof. exact (TRANS (@lem5449469) (@lem5449484)). Qed.
Lemma lem5449486 : term679 = False.
Proof. exact (TRANS (@lem5449453) (@lem5449485)). Qed.
Lemma lem5449487 : term677 = False.
Proof. exact (TRANS (@lem5449430) (@lem5449486)). Qed.
Lemma lem5449488 : term676 = False.
Proof. exact (TRANS (@lem5449421) (@lem5449487)). Qed.
Lemma lem5449489 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term466 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5449488) (@lem5449418 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449490 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term469 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5448543 _70518 _70519 _70520 _70521 h1) (fun h0 : term460 _70520 _70521 _70518 _70519 => @lem5449016 _70520 _70521 _70518 _70519 h0) (fun h0 : term466 _70518 _70519 _70520 _70521 => @lem5449489 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5449491 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term471 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5448069 _70518 _70519 _70520 _70521 h1) (fun h0 : term454 _70519 _70520 _70518 _70521 => @lem5448542 _70519 _70520 _70518 _70521 h0) (fun h0 : term469 _70518 _70519 _70520 _70521 => @lem5449490 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5449492 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term473 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5447595 _70518 _70519 _70520 _70521 h1) (fun h0 : term448 _70518 _70521 _70519 _70520 => @lem5448068 _70518 _70521 _70519 _70520 h0) (fun h0 : term471 _70518 _70519 _70520 _70521 => @lem5449491 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5449493 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term613 _70518 _70519 _70520 _70521) : term613 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5449494 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term611 _70518 _70519 _70520 _70521) : term611 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5449495 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term603 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5449496 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term602 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449495 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449498 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term601 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449496 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449500 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term599 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449498 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449502 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term597 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449500 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449504 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term595 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449502 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449506 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term593 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449504 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449508 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term323 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449506 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449509 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term288 _70519 _70520.
Proof. exact (proj1 (@lem5449506 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449511 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term315 _70519 _70520.
Proof. exact (proj1 (@lem5449508 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449517 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5449518 : term616 = term617.
Proof. exact (@lem5449517 term170 term192). Qed.
Lemma lem5449520 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449521 : term192 = term272.
Proof. exact (@lem5449520 term193). Qed.
Lemma lem5449523 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449524 : term170 = term235.
Proof. exact (@lem5449523 (NUMERAL 0)). Qed.
Lemma lem5449525 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449526 : term618 = term619.
Proof. exact (MK_COMB (@lem5449525) (@lem5449524)). Qed.
Lemma lem5449527 : term617 = term620.
Proof. exact (MK_COMB (@lem5449526) (@lem5449521)). Qed.
Lemma lem5449528 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5449530 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449531 : term617 = term623.
Proof. exact (@lem5449530 (NUMERAL 0) term193). Qed.
Lemma lem5449532 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449533 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449534 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449533 h1) (fun h1 : term623 = True => @lem5449532)). Qed.
Lemma lem5449535 : term623 = True.
Proof. exact (EQ_MP (@lem5449534) (@lem5449532)). Qed.
Lemma lem5449536 : term617 = True.
Proof. exact (TRANS (@lem5449531) (@lem5449535)). Qed.
Lemma lem5449537 : True = term617.
Proof. exact (SYM (@lem5449536)). Qed.
Lemma lem5449538 : term617.
Proof. exact (EQ_MP (@lem5449537) (@lem0)). Qed.
Lemma lem5449539 : term625.
Proof. exact (@lem5449528 (@lem5449538)). Qed.
Lemma lem5449541 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449542 : term617 = term623.
Proof. exact (@lem5449541 (NUMERAL 0) term193). Qed.
Lemma lem5449543 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449544 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449545 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449544 h1) (fun h1 : term623 = True => @lem5449543)). Qed.
Lemma lem5449546 : term623 = True.
Proof. exact (EQ_MP (@lem5449545) (@lem5449543)). Qed.
Lemma lem5449547 : term617 = True.
Proof. exact (TRANS (@lem5449542) (@lem5449546)). Qed.
Lemma lem5449548 : True = term617.
Proof. exact (SYM (@lem5449547)). Qed.
Lemma lem5449549 : term617.
Proof. exact (EQ_MP (@lem5449548) (@lem0)). Qed.
Lemma lem5449550 : term620 = term626.
Proof. exact (@lem5449539 (@lem5449549)). Qed.
Lemma lem5449552 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449553 : term247 = term248.
Proof. exact (@lem5449552 term193 term193). Qed.
Lemma lem5449554 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449555 : term250 = term193.
Proof. exact (EQ_MP (@lem5449554) (@lem940073)). Qed.
Lemma lem5449556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449557 : term248 = term192.
Proof. exact (MK_COMB (@lem5449556) (@lem5449555)). Qed.
Lemma lem5449558 : term247 = term192.
Proof. exact (TRANS (@lem5449553) (@lem5449557)). Qed.
Lemma lem5449560 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449561 : term628 = term170.
Proof. exact (@lem5449560 term193). Qed.
Lemma lem5449562 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449563 : term629 = term618.
Proof. exact (MK_COMB (@lem5449562) (@lem5449561)). Qed.
Lemma lem5449564 : term626 = term617.
Proof. exact (MK_COMB (@lem5449563) (@lem5449558)). Qed.
Lemma lem5449566 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449567 : term617 = term623.
Proof. exact (@lem5449566 (NUMERAL 0) term193). Qed.
Lemma lem5449568 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449569 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449570 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449569 h1) (fun h1 : term623 = True => @lem5449568)). Qed.
Lemma lem5449571 : term623 = True.
Proof. exact (EQ_MP (@lem5449570) (@lem5449568)). Qed.
Lemma lem5449572 : term617 = True.
Proof. exact (TRANS (@lem5449567) (@lem5449571)). Qed.
Lemma lem5449573 : term626 = True.
Proof. exact (TRANS (@lem5449564) (@lem5449572)). Qed.
Lemma lem5449574 : term620 = True.
Proof. exact (TRANS (@lem5449550) (@lem5449573)). Qed.
Lemma lem5449575 : term617 = True.
Proof. exact (TRANS (@lem5449527) (@lem5449574)). Qed.
Lemma lem5449576 : term616 = True.
Proof. exact (TRANS (@lem5449518) (@lem5449575)). Qed.
Lemma lem5449577 : True = term616.
Proof. exact (SYM (@lem5449576)). Qed.
Lemma lem5449578 : term616.
Proof. exact (EQ_MP (@lem5449577) (@lem0)). Qed.
Lemma lem5449579 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term636 _70519 _70520.
Proof. exact (conj (@lem5449578) (@lem5449511 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449581 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5449582 (_70519 : int) (_70520 : int) : term637 _70519 _70520.
Proof. exact (@lem5449581 term192 (term312 _70519 _70520)). Qed.
Lemma lem5449583 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term638 _70519 _70520.
Proof. exact (@lem5449582 _70519 _70520 (@lem5449579 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449584 (_70519 : int) (_70520 : int) : (term639 _70519 _70520) = (term312 _70519 _70520).
Proof. exact (@lem1982733 (term312 _70519 _70520)). Qed.
Lemma lem5449585 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5449586 (_70519 : int) (_70520 : int) : (term640 _70519 _70520) = (term314 _70519 _70520).
Proof. exact (MK_COMB (@lem5449585) (@lem5449584 _70519 _70520)). Qed.
Lemma lem5449587 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5449588 (_70519 : int) (_70520 : int) : (term638 _70519 _70520) = (term315 _70519 _70520).
Proof. exact (MK_COMB (@lem5449586 _70519 _70520) (@lem5449587)). Qed.
Lemma lem5449589 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term315 _70519 _70520.
Proof. exact (EQ_MP (@lem5449588 _70519 _70520) (@lem5449583 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449591 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5449592 : term616 = term617.
Proof. exact (@lem5449591 term170 term192). Qed.
Lemma lem5449594 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449595 : term192 = term272.
Proof. exact (@lem5449594 term193). Qed.
Lemma lem5449597 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449598 : term170 = term235.
Proof. exact (@lem5449597 (NUMERAL 0)). Qed.
Lemma lem5449599 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449600 : term618 = term619.
Proof. exact (MK_COMB (@lem5449599) (@lem5449598)). Qed.
Lemma lem5449601 : term617 = term620.
Proof. exact (MK_COMB (@lem5449600) (@lem5449595)). Qed.
Lemma lem5449602 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5449604 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449605 : term617 = term623.
Proof. exact (@lem5449604 (NUMERAL 0) term193). Qed.
Lemma lem5449606 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449607 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449608 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449607 h1) (fun h1 : term623 = True => @lem5449606)). Qed.
Lemma lem5449609 : term623 = True.
Proof. exact (EQ_MP (@lem5449608) (@lem5449606)). Qed.
Lemma lem5449610 : term617 = True.
Proof. exact (TRANS (@lem5449605) (@lem5449609)). Qed.
Lemma lem5449611 : True = term617.
Proof. exact (SYM (@lem5449610)). Qed.
Lemma lem5449612 : term617.
Proof. exact (EQ_MP (@lem5449611) (@lem0)). Qed.
Lemma lem5449613 : term625.
Proof. exact (@lem5449602 (@lem5449612)). Qed.
Lemma lem5449615 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449616 : term617 = term623.
Proof. exact (@lem5449615 (NUMERAL 0) term193). Qed.
Lemma lem5449617 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449618 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449619 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449618 h1) (fun h1 : term623 = True => @lem5449617)). Qed.
Lemma lem5449620 : term623 = True.
Proof. exact (EQ_MP (@lem5449619) (@lem5449617)). Qed.
Lemma lem5449621 : term617 = True.
Proof. exact (TRANS (@lem5449616) (@lem5449620)). Qed.
Lemma lem5449622 : True = term617.
Proof. exact (SYM (@lem5449621)). Qed.
Lemma lem5449623 : term617.
Proof. exact (EQ_MP (@lem5449622) (@lem0)). Qed.
Lemma lem5449624 : term620 = term626.
Proof. exact (@lem5449613 (@lem5449623)). Qed.
Lemma lem5449626 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449627 : term247 = term248.
Proof. exact (@lem5449626 term193 term193). Qed.
Lemma lem5449628 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449629 : term250 = term193.
Proof. exact (EQ_MP (@lem5449628) (@lem940073)). Qed.
Lemma lem5449630 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449631 : term248 = term192.
Proof. exact (MK_COMB (@lem5449630) (@lem5449629)). Qed.
Lemma lem5449632 : term247 = term192.
Proof. exact (TRANS (@lem5449627) (@lem5449631)). Qed.
Lemma lem5449634 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449635 : term628 = term170.
Proof. exact (@lem5449634 term193). Qed.
Lemma lem5449636 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5449637 : term629 = term618.
Proof. exact (MK_COMB (@lem5449636) (@lem5449635)). Qed.
Lemma lem5449638 : term626 = term617.
Proof. exact (MK_COMB (@lem5449637) (@lem5449632)). Qed.
Lemma lem5449640 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449641 : term617 = term623.
Proof. exact (@lem5449640 (NUMERAL 0) term193). Qed.
Lemma lem5449642 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449643 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449644 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449643 h1) (fun h1 : term623 = True => @lem5449642)). Qed.
Lemma lem5449645 : term623 = True.
Proof. exact (EQ_MP (@lem5449644) (@lem5449642)). Qed.
Lemma lem5449646 : term617 = True.
Proof. exact (TRANS (@lem5449641) (@lem5449645)). Qed.
Lemma lem5449647 : term626 = True.
Proof. exact (TRANS (@lem5449638) (@lem5449646)). Qed.
Lemma lem5449648 : term620 = True.
Proof. exact (TRANS (@lem5449624) (@lem5449647)). Qed.
Lemma lem5449649 : term617 = True.
Proof. exact (TRANS (@lem5449601) (@lem5449648)). Qed.
Lemma lem5449650 : term616 = True.
Proof. exact (TRANS (@lem5449592) (@lem5449649)). Qed.
Lemma lem5449651 : True = term616.
Proof. exact (SYM (@lem5449650)). Qed.
Lemma lem5449652 : term616.
Proof. exact (EQ_MP (@lem5449651) (@lem0)). Qed.
Lemma lem5449653 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term630 _70519 _70520.
Proof. exact (conj (@lem5449652) (@lem5449509 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449655 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5449656 (_70519 : int) (_70520 : int) : term632 _70519 _70520.
Proof. exact (@lem5449655 term192 (term284 _70519 _70520)). Qed.
Lemma lem5449657 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term633 _70519 _70520.
Proof. exact (@lem5449656 _70519 _70520 (@lem5449653 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449658 (_70519 : int) (_70520 : int) : (term634 _70519 _70520) = (term284 _70519 _70520).
Proof. exact (@lem1982733 (term284 _70519 _70520)). Qed.
Lemma lem5449659 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5449660 (_70519 : int) (_70520 : int) : (term635 _70519 _70520) = (term287 _70519 _70520).
Proof. exact (MK_COMB (@lem5449659) (@lem5449658 _70519 _70520)). Qed.
Lemma lem5449661 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5449662 (_70519 : int) (_70520 : int) : (term633 _70519 _70520) = (term288 _70519 _70520).
Proof. exact (MK_COMB (@lem5449660 _70519 _70520) (@lem5449661)). Qed.
Lemma lem5449663 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term288 _70519 _70520.
Proof. exact (EQ_MP (@lem5449662 _70519 _70520) (@lem5449657 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449664 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term706 _70519 _70520.
Proof. exact (conj (@lem5449663 _70518 _70519 _70520 _70521 h1) (@lem5449589 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449666 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5449667 (_70519 : int) (_70520 : int) : term707 _70519 _70520.
Proof. exact (@lem5449666 (term284 _70519 _70520) (term312 _70519 _70520)). Qed.
Lemma lem5449668 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term708 _70519 _70520.
Proof. exact (@lem5449667 _70519 _70520 (@lem5449664 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449669 (_70519 : int) (_70520 : int) : (term709 _70519 _70520) = (term710 _70519 _70520).
Proof. exact (@lem1982753 (term285 _70519) (real_of_int _70519) (term647 _70520) (term285 _70520)). Qed.
Lemma lem5449670 (_70519 : int) : (term671 _70519) = (term649 _70519).
Proof. exact (@lem1982713 term238 (real_of_int _70519)). Qed.
Lemma lem5449672 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449673 : term192 = term272.
Proof. exact (@lem5449672 term193). Qed.
Lemma lem5449675 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5449676 : term238 = term239.
Proof. exact (@lem5449675 term193). Qed.
Lemma lem5449677 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449678 : term650 = term651.
Proof. exact (MK_COMB (@lem5449677) (@lem5449676)). Qed.
Lemma lem5449679 : term652 = term653.
Proof. exact (MK_COMB (@lem5449678) (@lem5449673)). Qed.
Lemma lem5449680 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5449682 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449683 : term617 = term623.
Proof. exact (@lem5449682 (NUMERAL 0) term193). Qed.
Lemma lem5449684 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449685 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449686 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449685 h1) (fun h1 : term623 = True => @lem5449684)). Qed.
Lemma lem5449687 : term623 = True.
Proof. exact (EQ_MP (@lem5449686) (@lem5449684)). Qed.
Lemma lem5449688 : term617 = True.
Proof. exact (TRANS (@lem5449683) (@lem5449687)). Qed.
Lemma lem5449689 : True = term617.
Proof. exact (SYM (@lem5449688)). Qed.
Lemma lem5449690 : term617.
Proof. exact (EQ_MP (@lem5449689) (@lem0)). Qed.
Lemma lem5449691 : term655.
Proof. exact (@lem5449680 (@lem5449690)). Qed.
Lemma lem5449693 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449694 : term617 = term623.
Proof. exact (@lem5449693 (NUMERAL 0) term193). Qed.
Lemma lem5449695 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449696 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449697 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449696 h1) (fun h1 : term623 = True => @lem5449695)). Qed.
Lemma lem5449698 : term623 = True.
Proof. exact (EQ_MP (@lem5449697) (@lem5449695)). Qed.
Lemma lem5449699 : term617 = True.
Proof. exact (TRANS (@lem5449694) (@lem5449698)). Qed.
Lemma lem5449700 : True = term617.
Proof. exact (SYM (@lem5449699)). Qed.
Lemma lem5449701 : term617.
Proof. exact (EQ_MP (@lem5449700) (@lem0)). Qed.
Lemma lem5449702 : term656.
Proof. exact (@lem5449691 (@lem5449701)). Qed.
Lemma lem5449704 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449705 : term617 = term623.
Proof. exact (@lem5449704 (NUMERAL 0) term193). Qed.
Lemma lem5449706 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449707 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449708 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449707 h1) (fun h1 : term623 = True => @lem5449706)). Qed.
Lemma lem5449709 : term623 = True.
Proof. exact (EQ_MP (@lem5449708) (@lem5449706)). Qed.
Lemma lem5449710 : term617 = True.
Proof. exact (TRANS (@lem5449705) (@lem5449709)). Qed.
Lemma lem5449711 : True = term617.
Proof. exact (SYM (@lem5449710)). Qed.
Lemma lem5449712 : term617.
Proof. exact (EQ_MP (@lem5449711) (@lem0)). Qed.
Lemma lem5449713 : term657.
Proof. exact (@lem5449702 (@lem5449712)). Qed.
Lemma lem5449715 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449716 : term247 = term248.
Proof. exact (@lem5449715 term193 term193). Qed.
Lemma lem5449717 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449718 : term250 = term193.
Proof. exact (EQ_MP (@lem5449717) (@lem940073)). Qed.
Lemma lem5449719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449720 : term248 = term192.
Proof. exact (MK_COMB (@lem5449719) (@lem5449718)). Qed.
Lemma lem5449721 : term247 = term192.
Proof. exact (TRANS (@lem5449716) (@lem5449720)). Qed.
Lemma lem5449723 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5449724 : term273 = term278.
Proof. exact (@lem5449723 term193 term193). Qed.
Lemma lem5449725 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449726 : term250 = term193.
Proof. exact (EQ_MP (@lem5449725) (@lem940073)). Qed.
Lemma lem5449727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449728 : term248 = term192.
Proof. exact (MK_COMB (@lem5449727) (@lem5449726)). Qed.
Lemma lem5449729 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5449730 : term278 = term238.
Proof. exact (MK_COMB (@lem5449729) (@lem5449728)). Qed.
Lemma lem5449731 : term273 = term238.
Proof. exact (TRANS (@lem5449724) (@lem5449730)). Qed.
Lemma lem5449732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449733 : term658 = term650.
Proof. exact (MK_COMB (@lem5449732) (@lem5449731)). Qed.
Lemma lem5449734 : term659 = term652.
Proof. exact (MK_COMB (@lem5449733) (@lem5449721)). Qed.
Lemma lem5449736 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5449737 : term652 = term170.
Proof. exact (@lem5449736 term193). Qed.
Lemma lem5449738 : term659 = term170.
Proof. exact (TRANS (@lem5449734) (@lem5449737)). Qed.
Lemma lem5449739 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449740 : term661 = term662.
Proof. exact (MK_COMB (@lem5449739) (@lem5449738)). Qed.
Lemma lem5449741 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5449742 : term663 = term628.
Proof. exact (MK_COMB (@lem5449740) (@lem5449741)). Qed.
Lemma lem5449744 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449745 : term628 = term170.
Proof. exact (@lem5449744 term193). Qed.
Lemma lem5449746 : term663 = term170.
Proof. exact (TRANS (@lem5449742) (@lem5449745)). Qed.
Lemma lem5449748 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449749 : term247 = term248.
Proof. exact (@lem5449748 term193 term193). Qed.
Lemma lem5449750 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449751 : term250 = term193.
Proof. exact (EQ_MP (@lem5449750) (@lem940073)). Qed.
Lemma lem5449752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449753 : term248 = term192.
Proof. exact (MK_COMB (@lem5449752) (@lem5449751)). Qed.
Lemma lem5449754 : term247 = term192.
Proof. exact (TRANS (@lem5449749) (@lem5449753)). Qed.
Lemma lem5449755 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5449756 : term664 = term628.
Proof. exact (MK_COMB (@lem5449755) (@lem5449754)). Qed.
Lemma lem5449758 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449759 : term628 = term170.
Proof. exact (@lem5449758 term193). Qed.
Lemma lem5449760 : term664 = term170.
Proof. exact (TRANS (@lem5449756) (@lem5449759)). Qed.
Lemma lem5449761 : term170 = term664.
Proof. exact (SYM (@lem5449760)). Qed.
Lemma lem5449762 : term663 = term664.
Proof. exact (TRANS (@lem5449746) (@lem5449761)). Qed.
Lemma lem5449763 : term653 = term235.
Proof. exact (@lem5449713 (@lem5449762)). Qed.
Lemma lem5449764 : term652 = term235.
Proof. exact (TRANS (@lem5449679) (@lem5449763)). Qed.
Lemma lem5449766 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5449767 : term235 = term170.
Proof. exact (@lem5449766 term170). Qed.
Lemma lem5449768 : term652 = term170.
Proof. exact (TRANS (@lem5449764) (@lem5449767)). Qed.
Lemma lem5449769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449770 : term665 = term662.
Proof. exact (MK_COMB (@lem5449769) (@lem5449768)). Qed.
Lemma lem5449771 (_70519 : int) : (real_of_int _70519) = (real_of_int _70519).
Proof. exact (eq_refl (real_of_int _70519)). Qed.
Lemma lem5449772 (_70519 : int) : (term649 _70519) = (term666 _70519).
Proof. exact (MK_COMB (@lem5449770) (@lem5449771 _70519)). Qed.
Lemma lem5449773 (_70519 : int) : (term671 _70519) = (term666 _70519).
Proof. exact (TRANS (@lem5449670 _70519) (@lem5449772 _70519)). Qed.
Lemma lem5449774 (_70519 : int) : (term666 _70519) = term170.
Proof. exact (@lem1982719 (real_of_int _70519)). Qed.
Lemma lem5449775 (_70519 : int) : (term671 _70519) = term170.
Proof. exact (TRANS (@lem5449773 _70519) (@lem5449774 _70519)). Qed.
Lemma lem5449776 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449777 (_70519 : int) : (term672 _70519) = term668.
Proof. exact (MK_COMB (@lem5449776) (@lem5449775 _70519)). Qed.
Lemma lem5449778 (_70520 : int) : (term711 _70520) = (term704 _70520).
Proof. exact (@lem1982759 (real_of_int _70520) (term285 _70520) term238). Qed.
Lemma lem5449779 (_70520 : int) : (term648 _70520) = (term649 _70520).
Proof. exact (@lem1982715 term238 (real_of_int _70520)). Qed.
Lemma lem5449781 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449782 : term192 = term272.
Proof. exact (@lem5449781 term193). Qed.
Lemma lem5449784 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5449785 : term238 = term239.
Proof. exact (@lem5449784 term193). Qed.
Lemma lem5449786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449787 : term650 = term651.
Proof. exact (MK_COMB (@lem5449786) (@lem5449785)). Qed.
Lemma lem5449788 : term652 = term653.
Proof. exact (MK_COMB (@lem5449787) (@lem5449782)). Qed.
Lemma lem5449789 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5449791 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449792 : term617 = term623.
Proof. exact (@lem5449791 (NUMERAL 0) term193). Qed.
Lemma lem5449793 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449794 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449795 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449794 h1) (fun h1 : term623 = True => @lem5449793)). Qed.
Lemma lem5449796 : term623 = True.
Proof. exact (EQ_MP (@lem5449795) (@lem5449793)). Qed.
Lemma lem5449797 : term617 = True.
Proof. exact (TRANS (@lem5449792) (@lem5449796)). Qed.
Lemma lem5449798 : True = term617.
Proof. exact (SYM (@lem5449797)). Qed.
Lemma lem5449799 : term617.
Proof. exact (EQ_MP (@lem5449798) (@lem0)). Qed.
Lemma lem5449800 : term655.
Proof. exact (@lem5449789 (@lem5449799)). Qed.
Lemma lem5449802 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449803 : term617 = term623.
Proof. exact (@lem5449802 (NUMERAL 0) term193). Qed.
Lemma lem5449804 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449805 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449806 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449805 h1) (fun h1 : term623 = True => @lem5449804)). Qed.
Lemma lem5449807 : term623 = True.
Proof. exact (EQ_MP (@lem5449806) (@lem5449804)). Qed.
Lemma lem5449808 : term617 = True.
Proof. exact (TRANS (@lem5449803) (@lem5449807)). Qed.
Lemma lem5449809 : True = term617.
Proof. exact (SYM (@lem5449808)). Qed.
Lemma lem5449810 : term617.
Proof. exact (EQ_MP (@lem5449809) (@lem0)). Qed.
Lemma lem5449811 : term656.
Proof. exact (@lem5449800 (@lem5449810)). Qed.
Lemma lem5449813 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449814 : term617 = term623.
Proof. exact (@lem5449813 (NUMERAL 0) term193). Qed.
Lemma lem5449815 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449816 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449817 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449816 h1) (fun h1 : term623 = True => @lem5449815)). Qed.
Lemma lem5449818 : term623 = True.
Proof. exact (EQ_MP (@lem5449817) (@lem5449815)). Qed.
Lemma lem5449819 : term617 = True.
Proof. exact (TRANS (@lem5449814) (@lem5449818)). Qed.
Lemma lem5449820 : True = term617.
Proof. exact (SYM (@lem5449819)). Qed.
Lemma lem5449821 : term617.
Proof. exact (EQ_MP (@lem5449820) (@lem0)). Qed.
Lemma lem5449822 : term657.
Proof. exact (@lem5449811 (@lem5449821)). Qed.
Lemma lem5449824 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449825 : term247 = term248.
Proof. exact (@lem5449824 term193 term193). Qed.
Lemma lem5449826 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449827 : term250 = term193.
Proof. exact (EQ_MP (@lem5449826) (@lem940073)). Qed.
Lemma lem5449828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449829 : term248 = term192.
Proof. exact (MK_COMB (@lem5449828) (@lem5449827)). Qed.
Lemma lem5449830 : term247 = term192.
Proof. exact (TRANS (@lem5449825) (@lem5449829)). Qed.
Lemma lem5449832 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5449833 : term273 = term278.
Proof. exact (@lem5449832 term193 term193). Qed.
Lemma lem5449834 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449835 : term250 = term193.
Proof. exact (EQ_MP (@lem5449834) (@lem940073)). Qed.
Lemma lem5449836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449837 : term248 = term192.
Proof. exact (MK_COMB (@lem5449836) (@lem5449835)). Qed.
Lemma lem5449838 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5449839 : term278 = term238.
Proof. exact (MK_COMB (@lem5449838) (@lem5449837)). Qed.
Lemma lem5449840 : term273 = term238.
Proof. exact (TRANS (@lem5449833) (@lem5449839)). Qed.
Lemma lem5449841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449842 : term658 = term650.
Proof. exact (MK_COMB (@lem5449841) (@lem5449840)). Qed.
Lemma lem5449843 : term659 = term652.
Proof. exact (MK_COMB (@lem5449842) (@lem5449830)). Qed.
Lemma lem5449845 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5449846 : term652 = term170.
Proof. exact (@lem5449845 term193). Qed.
Lemma lem5449847 : term659 = term170.
Proof. exact (TRANS (@lem5449843) (@lem5449846)). Qed.
Lemma lem5449848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449849 : term661 = term662.
Proof. exact (MK_COMB (@lem5449848) (@lem5449847)). Qed.
Lemma lem5449850 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5449851 : term663 = term628.
Proof. exact (MK_COMB (@lem5449849) (@lem5449850)). Qed.
Lemma lem5449853 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449854 : term628 = term170.
Proof. exact (@lem5449853 term193). Qed.
Lemma lem5449855 : term663 = term170.
Proof. exact (TRANS (@lem5449851) (@lem5449854)). Qed.
Lemma lem5449857 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5449858 : term247 = term248.
Proof. exact (@lem5449857 term193 term193). Qed.
Lemma lem5449859 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449860 : term250 = term193.
Proof. exact (EQ_MP (@lem5449859) (@lem940073)). Qed.
Lemma lem5449861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449862 : term248 = term192.
Proof. exact (MK_COMB (@lem5449861) (@lem5449860)). Qed.
Lemma lem5449863 : term247 = term192.
Proof. exact (TRANS (@lem5449858) (@lem5449862)). Qed.
Lemma lem5449864 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5449865 : term664 = term628.
Proof. exact (MK_COMB (@lem5449864) (@lem5449863)). Qed.
Lemma lem5449867 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449868 : term628 = term170.
Proof. exact (@lem5449867 term193). Qed.
Lemma lem5449869 : term664 = term170.
Proof. exact (TRANS (@lem5449865) (@lem5449868)). Qed.
Lemma lem5449870 : term170 = term664.
Proof. exact (SYM (@lem5449869)). Qed.
Lemma lem5449871 : term663 = term664.
Proof. exact (TRANS (@lem5449855) (@lem5449870)). Qed.
Lemma lem5449872 : term653 = term235.
Proof. exact (@lem5449822 (@lem5449871)). Qed.
Lemma lem5449873 : term652 = term235.
Proof. exact (TRANS (@lem5449788) (@lem5449872)). Qed.
Lemma lem5449875 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5449876 : term235 = term170.
Proof. exact (@lem5449875 term170). Qed.
Lemma lem5449877 : term652 = term170.
Proof. exact (TRANS (@lem5449873) (@lem5449876)). Qed.
Lemma lem5449878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5449879 : term665 = term662.
Proof. exact (MK_COMB (@lem5449878) (@lem5449877)). Qed.
Lemma lem5449880 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5449881 (_70520 : int) : (term649 _70520) = (term666 _70520).
Proof. exact (MK_COMB (@lem5449879) (@lem5449880 _70520)). Qed.
Lemma lem5449882 (_70520 : int) : (term648 _70520) = (term666 _70520).
Proof. exact (TRANS (@lem5449779 _70520) (@lem5449881 _70520)). Qed.
Lemma lem5449883 (_70520 : int) : (term666 _70520) = term170.
Proof. exact (@lem1982719 (real_of_int _70520)). Qed.
Lemma lem5449884 (_70520 : int) : (term648 _70520) = term170.
Proof. exact (TRANS (@lem5449882 _70520) (@lem5449883 _70520)). Qed.
Lemma lem5449885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5449886 (_70520 : int) : (term667 _70520) = term668.
Proof. exact (MK_COMB (@lem5449885) (@lem5449884 _70520)). Qed.
Lemma lem5449887 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5449888 (_70520 : int) : (term704 _70520) = term673.
Proof. exact (MK_COMB (@lem5449886 _70520) (@lem5449887)). Qed.
Lemma lem5449889 (_70520 : int) : (term711 _70520) = term673.
Proof. exact (TRANS (@lem5449778 _70520) (@lem5449888 _70520)). Qed.
Lemma lem5449890 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5449891 (_70520 : int) : (term711 _70520) = term238.
Proof. exact (TRANS (@lem5449889 _70520) (@lem5449890)). Qed.
Lemma lem5449892 (_70519 : int) (_70520 : int) : (term710 _70519 _70520) = term673.
Proof. exact (MK_COMB (@lem5449777 _70519) (@lem5449891 _70520)). Qed.
Lemma lem5449893 (_70519 : int) (_70520 : int) : (term709 _70519 _70520) = term673.
Proof. exact (TRANS (@lem5449669 _70519 _70520) (@lem5449892 _70519 _70520)). Qed.
Lemma lem5449894 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5449895 (_70519 : int) (_70520 : int) : (term709 _70519 _70520) = term238.
Proof. exact (TRANS (@lem5449893 _70519 _70520) (@lem5449894)). Qed.
Lemma lem5449896 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5449897 (_70519 : int) (_70520 : int) : (term712 _70519 _70520) = term675.
Proof. exact (MK_COMB (@lem5449896) (@lem5449895 _70519 _70520)). Qed.
Lemma lem5449898 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5449899 (_70519 : int) (_70520 : int) : (term708 _70519 _70520) = term676.
Proof. exact (MK_COMB (@lem5449897 _70519 _70520) (@lem5449898)). Qed.
Lemma lem5449900 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : term676.
Proof. exact (EQ_MP (@lem5449899 _70519 _70520) (@lem5449668 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449902 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5449903 : term676 = term677.
Proof. exact (@lem5449902 term170 term238). Qed.
Lemma lem5449905 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5449906 : term238 = term239.
Proof. exact (@lem5449905 term193). Qed.
Lemma lem5449908 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449909 : term170 = term235.
Proof. exact (@lem5449908 (NUMERAL 0)). Qed.
Lemma lem5449910 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5449911 : term172 = term678.
Proof. exact (MK_COMB (@lem5449910) (@lem5449909)). Qed.
Lemma lem5449912 : term677 = term679.
Proof. exact (MK_COMB (@lem5449911) (@lem5449906)). Qed.
Lemma lem5449913 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5449915 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449916 : term617 = term623.
Proof. exact (@lem5449915 (NUMERAL 0) term193). Qed.
Lemma lem5449917 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449918 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449919 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449918 h1) (fun h1 : term623 = True => @lem5449917)). Qed.
Lemma lem5449920 : term623 = True.
Proof. exact (EQ_MP (@lem5449919) (@lem5449917)). Qed.
Lemma lem5449921 : term617 = True.
Proof. exact (TRANS (@lem5449916) (@lem5449920)). Qed.
Lemma lem5449922 : True = term617.
Proof. exact (SYM (@lem5449921)). Qed.
Lemma lem5449923 : term617.
Proof. exact (EQ_MP (@lem5449922) (@lem0)). Qed.
Lemma lem5449924 : term681.
Proof. exact (@lem5449913 (@lem5449923)). Qed.
Lemma lem5449926 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5449927 : term617 = term623.
Proof. exact (@lem5449926 (NUMERAL 0) term193). Qed.
Lemma lem5449928 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449929 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5449930 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449929 h1) (fun h1 : term623 = True => @lem5449928)). Qed.
Lemma lem5449931 : term623 = True.
Proof. exact (EQ_MP (@lem5449930) (@lem5449928)). Qed.
Lemma lem5449932 : term617 = True.
Proof. exact (TRANS (@lem5449927) (@lem5449931)). Qed.
Lemma lem5449933 : True = term617.
Proof. exact (SYM (@lem5449932)). Qed.
Lemma lem5449934 : term617.
Proof. exact (EQ_MP (@lem5449933) (@lem0)). Qed.
Lemma lem5449935 : term679 = term682.
Proof. exact (@lem5449924 (@lem5449934)). Qed.
Lemma lem5449937 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5449938 : term273 = term278.
Proof. exact (@lem5449937 term193 term193). Qed.
Lemma lem5449939 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5449940 : term250 = term193.
Proof. exact (EQ_MP (@lem5449939) (@lem940073)). Qed.
Lemma lem5449941 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5449942 : term248 = term192.
Proof. exact (MK_COMB (@lem5449941) (@lem5449940)). Qed.
Lemma lem5449943 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5449944 : term278 = term238.
Proof. exact (MK_COMB (@lem5449943) (@lem5449942)). Qed.
Lemma lem5449945 : term273 = term238.
Proof. exact (TRANS (@lem5449938) (@lem5449944)). Qed.
Lemma lem5449947 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5449948 : term628 = term170.
Proof. exact (@lem5449947 term193). Qed.
Lemma lem5449949 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5449950 : term683 = term172.
Proof. exact (MK_COMB (@lem5449949) (@lem5449948)). Qed.
Lemma lem5449951 : term682 = term677.
Proof. exact (MK_COMB (@lem5449950) (@lem5449945)). Qed.
Lemma lem5449953 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5449954 : term677 = term686.
Proof. exact (@lem5449953 (NUMERAL 0) term193). Qed.
Lemma lem5449955 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5449956 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5449957 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5449956 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5449955)). Qed.
Lemma lem5449958 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5449957) (@lem5449955)). Qed.
Lemma lem5449959 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5449960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5449961 : term687 = (and True).
Proof. exact (MK_COMB (@lem5449960) (@lem5449959)). Qed.
Lemma lem5449962 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5449961) (@lem5449958)). Qed.
Lemma lem5449964 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5449965 : term686 = False.
Proof. exact (TRANS (@lem5449962) (@lem5449964)). Qed.
Lemma lem5449966 : term677 = False.
Proof. exact (TRANS (@lem5449954) (@lem5449965)). Qed.
Lemma lem5449967 : term682 = False.
Proof. exact (TRANS (@lem5449951) (@lem5449966)). Qed.
Lemma lem5449968 : term679 = False.
Proof. exact (TRANS (@lem5449935) (@lem5449967)). Qed.
Lemma lem5449969 : term677 = False.
Proof. exact (TRANS (@lem5449912) (@lem5449968)). Qed.
Lemma lem5449970 : term676 = False.
Proof. exact (TRANS (@lem5449903) (@lem5449969)). Qed.
Lemma lem5449971 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term603 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5449970) (@lem5449900 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449972 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term609 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5449973 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term574 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449972 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449975 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term608 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449973 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449977 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term607 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449975 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449979 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term606 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449977 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449981 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term605 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449979 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449983 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term604 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449981 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449985 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term323 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449983 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449986 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term290 _70520 _70521.
Proof. exact (proj1 (@lem5449983 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449987 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term321 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449985 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449989 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term320 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5449987 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449991 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term318 _70520 _70521.
Proof. exact (proj2 (@lem5449989 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5449994 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5449995 : term616 = term617.
Proof. exact (@lem5449994 term170 term192). Qed.
Lemma lem5449997 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5449998 : term192 = term272.
Proof. exact (@lem5449997 term193). Qed.
Lemma lem5450000 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450001 : term170 = term235.
Proof. exact (@lem5450000 (NUMERAL 0)). Qed.
Lemma lem5450002 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450003 : term618 = term619.
Proof. exact (MK_COMB (@lem5450002) (@lem5450001)). Qed.
Lemma lem5450004 : term617 = term620.
Proof. exact (MK_COMB (@lem5450003) (@lem5449998)). Qed.
Lemma lem5450005 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5450007 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450008 : term617 = term623.
Proof. exact (@lem5450007 (NUMERAL 0) term193). Qed.
Lemma lem5450009 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450010 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450011 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450010 h1) (fun h1 : term623 = True => @lem5450009)). Qed.
Lemma lem5450012 : term623 = True.
Proof. exact (EQ_MP (@lem5450011) (@lem5450009)). Qed.
Lemma lem5450013 : term617 = True.
Proof. exact (TRANS (@lem5450008) (@lem5450012)). Qed.
Lemma lem5450014 : True = term617.
Proof. exact (SYM (@lem5450013)). Qed.
Lemma lem5450015 : term617.
Proof. exact (EQ_MP (@lem5450014) (@lem0)). Qed.
Lemma lem5450016 : term625.
Proof. exact (@lem5450005 (@lem5450015)). Qed.
Lemma lem5450018 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450019 : term617 = term623.
Proof. exact (@lem5450018 (NUMERAL 0) term193). Qed.
Lemma lem5450020 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450021 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450022 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450021 h1) (fun h1 : term623 = True => @lem5450020)). Qed.
Lemma lem5450023 : term623 = True.
Proof. exact (EQ_MP (@lem5450022) (@lem5450020)). Qed.
Lemma lem5450024 : term617 = True.
Proof. exact (TRANS (@lem5450019) (@lem5450023)). Qed.
Lemma lem5450025 : True = term617.
Proof. exact (SYM (@lem5450024)). Qed.
Lemma lem5450026 : term617.
Proof. exact (EQ_MP (@lem5450025) (@lem0)). Qed.
Lemma lem5450027 : term620 = term626.
Proof. exact (@lem5450016 (@lem5450026)). Qed.
Lemma lem5450029 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450030 : term247 = term248.
Proof. exact (@lem5450029 term193 term193). Qed.
Lemma lem5450031 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450032 : term250 = term193.
Proof. exact (EQ_MP (@lem5450031) (@lem940073)). Qed.
Lemma lem5450033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450034 : term248 = term192.
Proof. exact (MK_COMB (@lem5450033) (@lem5450032)). Qed.
Lemma lem5450035 : term247 = term192.
Proof. exact (TRANS (@lem5450030) (@lem5450034)). Qed.
Lemma lem5450037 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450038 : term628 = term170.
Proof. exact (@lem5450037 term193). Qed.
Lemma lem5450039 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450040 : term629 = term618.
Proof. exact (MK_COMB (@lem5450039) (@lem5450038)). Qed.
Lemma lem5450041 : term626 = term617.
Proof. exact (MK_COMB (@lem5450040) (@lem5450035)). Qed.
Lemma lem5450043 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450044 : term617 = term623.
Proof. exact (@lem5450043 (NUMERAL 0) term193). Qed.
Lemma lem5450045 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450046 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450047 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450046 h1) (fun h1 : term623 = True => @lem5450045)). Qed.
Lemma lem5450048 : term623 = True.
Proof. exact (EQ_MP (@lem5450047) (@lem5450045)). Qed.
Lemma lem5450049 : term617 = True.
Proof. exact (TRANS (@lem5450044) (@lem5450048)). Qed.
Lemma lem5450050 : term626 = True.
Proof. exact (TRANS (@lem5450041) (@lem5450049)). Qed.
Lemma lem5450051 : term620 = True.
Proof. exact (TRANS (@lem5450027) (@lem5450050)). Qed.
Lemma lem5450052 : term617 = True.
Proof. exact (TRANS (@lem5450004) (@lem5450051)). Qed.
Lemma lem5450053 : term616 = True.
Proof. exact (TRANS (@lem5449995) (@lem5450052)). Qed.
Lemma lem5450054 : True = term616.
Proof. exact (SYM (@lem5450053)). Qed.
Lemma lem5450055 : term616.
Proof. exact (EQ_MP (@lem5450054) (@lem0)). Qed.
Lemma lem5450056 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term693 _70520 _70521.
Proof. exact (conj (@lem5450055) (@lem5449991 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450058 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5450059 (_70520 : int) (_70521 : int) : term694 _70520 _70521.
Proof. exact (@lem5450058 term192 (term316 _70520 _70521)). Qed.
Lemma lem5450060 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term695 _70520 _70521.
Proof. exact (@lem5450059 _70520 _70521 (@lem5450056 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450061 (_70520 : int) (_70521 : int) : (term696 _70520 _70521) = (term316 _70520 _70521).
Proof. exact (@lem1982733 (term316 _70520 _70521)). Qed.
Lemma lem5450062 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5450063 (_70520 : int) (_70521 : int) : (term697 _70520 _70521) = (term317 _70520 _70521).
Proof. exact (MK_COMB (@lem5450062) (@lem5450061 _70520 _70521)). Qed.
Lemma lem5450064 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5450065 (_70520 : int) (_70521 : int) : (term695 _70520 _70521) = (term318 _70520 _70521).
Proof. exact (MK_COMB (@lem5450063 _70520 _70521) (@lem5450064)). Qed.
Lemma lem5450066 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term318 _70520 _70521.
Proof. exact (EQ_MP (@lem5450065 _70520 _70521) (@lem5450060 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450068 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5450069 : term616 = term617.
Proof. exact (@lem5450068 term170 term192). Qed.
Lemma lem5450071 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450072 : term192 = term272.
Proof. exact (@lem5450071 term193). Qed.
Lemma lem5450074 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450075 : term170 = term235.
Proof. exact (@lem5450074 (NUMERAL 0)). Qed.
Lemma lem5450076 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450077 : term618 = term619.
Proof. exact (MK_COMB (@lem5450076) (@lem5450075)). Qed.
Lemma lem5450078 : term617 = term620.
Proof. exact (MK_COMB (@lem5450077) (@lem5450072)). Qed.
Lemma lem5450079 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5450081 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450082 : term617 = term623.
Proof. exact (@lem5450081 (NUMERAL 0) term193). Qed.
Lemma lem5450083 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450084 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450085 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450084 h1) (fun h1 : term623 = True => @lem5450083)). Qed.
Lemma lem5450086 : term623 = True.
Proof. exact (EQ_MP (@lem5450085) (@lem5450083)). Qed.
Lemma lem5450087 : term617 = True.
Proof. exact (TRANS (@lem5450082) (@lem5450086)). Qed.
Lemma lem5450088 : True = term617.
Proof. exact (SYM (@lem5450087)). Qed.
Lemma lem5450089 : term617.
Proof. exact (EQ_MP (@lem5450088) (@lem0)). Qed.
Lemma lem5450090 : term625.
Proof. exact (@lem5450079 (@lem5450089)). Qed.
Lemma lem5450092 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450093 : term617 = term623.
Proof. exact (@lem5450092 (NUMERAL 0) term193). Qed.
Lemma lem5450094 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450095 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450096 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450095 h1) (fun h1 : term623 = True => @lem5450094)). Qed.
Lemma lem5450097 : term623 = True.
Proof. exact (EQ_MP (@lem5450096) (@lem5450094)). Qed.
Lemma lem5450098 : term617 = True.
Proof. exact (TRANS (@lem5450093) (@lem5450097)). Qed.
Lemma lem5450099 : True = term617.
Proof. exact (SYM (@lem5450098)). Qed.
Lemma lem5450100 : term617.
Proof. exact (EQ_MP (@lem5450099) (@lem0)). Qed.
Lemma lem5450101 : term620 = term626.
Proof. exact (@lem5450090 (@lem5450100)). Qed.
Lemma lem5450103 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450104 : term247 = term248.
Proof. exact (@lem5450103 term193 term193). Qed.
Lemma lem5450105 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450106 : term250 = term193.
Proof. exact (EQ_MP (@lem5450105) (@lem940073)). Qed.
Lemma lem5450107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450108 : term248 = term192.
Proof. exact (MK_COMB (@lem5450107) (@lem5450106)). Qed.
Lemma lem5450109 : term247 = term192.
Proof. exact (TRANS (@lem5450104) (@lem5450108)). Qed.
Lemma lem5450111 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450112 : term628 = term170.
Proof. exact (@lem5450111 term193). Qed.
Lemma lem5450113 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450114 : term629 = term618.
Proof. exact (MK_COMB (@lem5450113) (@lem5450112)). Qed.
Lemma lem5450115 : term626 = term617.
Proof. exact (MK_COMB (@lem5450114) (@lem5450109)). Qed.
Lemma lem5450117 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450118 : term617 = term623.
Proof. exact (@lem5450117 (NUMERAL 0) term193). Qed.
Lemma lem5450119 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450120 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450121 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450120 h1) (fun h1 : term623 = True => @lem5450119)). Qed.
Lemma lem5450122 : term623 = True.
Proof. exact (EQ_MP (@lem5450121) (@lem5450119)). Qed.
Lemma lem5450123 : term617 = True.
Proof. exact (TRANS (@lem5450118) (@lem5450122)). Qed.
Lemma lem5450124 : term626 = True.
Proof. exact (TRANS (@lem5450115) (@lem5450123)). Qed.
Lemma lem5450125 : term620 = True.
Proof. exact (TRANS (@lem5450101) (@lem5450124)). Qed.
Lemma lem5450126 : term617 = True.
Proof. exact (TRANS (@lem5450078) (@lem5450125)). Qed.
Lemma lem5450127 : term616 = True.
Proof. exact (TRANS (@lem5450069) (@lem5450126)). Qed.
Lemma lem5450128 : True = term616.
Proof. exact (SYM (@lem5450127)). Qed.
Lemma lem5450129 : term616.
Proof. exact (EQ_MP (@lem5450128) (@lem0)). Qed.
Lemma lem5450130 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term688 _70520 _70521.
Proof. exact (conj (@lem5450129) (@lem5449986 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450132 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5450133 (_70520 : int) (_70521 : int) : term689 _70520 _70521.
Proof. exact (@lem5450132 term192 (term283 _70520 _70521)). Qed.
Lemma lem5450134 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term690 _70520 _70521.
Proof. exact (@lem5450133 _70520 _70521 (@lem5450130 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450135 (_70520 : int) (_70521 : int) : (term691 _70520 _70521) = (term283 _70520 _70521).
Proof. exact (@lem1982733 (term283 _70520 _70521)). Qed.
Lemma lem5450136 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5450137 (_70520 : int) (_70521 : int) : (term692 _70520 _70521) = (term289 _70520 _70521).
Proof. exact (MK_COMB (@lem5450136) (@lem5450135 _70520 _70521)). Qed.
Lemma lem5450138 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5450139 (_70520 : int) (_70521 : int) : (term690 _70520 _70521) = (term290 _70520 _70521).
Proof. exact (MK_COMB (@lem5450137 _70520 _70521) (@lem5450138)). Qed.
Lemma lem5450140 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term290 _70520 _70521.
Proof. exact (EQ_MP (@lem5450139 _70520 _70521) (@lem5450134 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450141 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term713 _70520 _70521.
Proof. exact (conj (@lem5450140 _70518 _70519 _70520 _70521 h1) (@lem5450066 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450143 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5450144 (_70520 : int) (_70521 : int) : term714 _70520 _70521.
Proof. exact (@lem5450143 (term283 _70520 _70521) (term316 _70520 _70521)). Qed.
Lemma lem5450145 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term715 _70520 _70521.
Proof. exact (@lem5450144 _70520 _70521 (@lem5450141 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450146 (_70520 : int) (_70521 : int) : (term716 _70520 _70521) = (term717 _70520 _70521).
Proof. exact (@lem1982753 (real_of_int _70520) (term285 _70520) (term282 _70521) (real_of_int _70521)). Qed.
Lemma lem5450147 (_70520 : int) : (term648 _70520) = (term649 _70520).
Proof. exact (@lem1982715 term238 (real_of_int _70520)). Qed.
Lemma lem5450149 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450150 : term192 = term272.
Proof. exact (@lem5450149 term193). Qed.
Lemma lem5450152 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5450153 : term238 = term239.
Proof. exact (@lem5450152 term193). Qed.
Lemma lem5450154 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450155 : term650 = term651.
Proof. exact (MK_COMB (@lem5450154) (@lem5450153)). Qed.
Lemma lem5450156 : term652 = term653.
Proof. exact (MK_COMB (@lem5450155) (@lem5450150)). Qed.
Lemma lem5450157 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5450159 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450160 : term617 = term623.
Proof. exact (@lem5450159 (NUMERAL 0) term193). Qed.
Lemma lem5450161 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450162 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450163 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450162 h1) (fun h1 : term623 = True => @lem5450161)). Qed.
Lemma lem5450164 : term623 = True.
Proof. exact (EQ_MP (@lem5450163) (@lem5450161)). Qed.
Lemma lem5450165 : term617 = True.
Proof. exact (TRANS (@lem5450160) (@lem5450164)). Qed.
Lemma lem5450166 : True = term617.
Proof. exact (SYM (@lem5450165)). Qed.
Lemma lem5450167 : term617.
Proof. exact (EQ_MP (@lem5450166) (@lem0)). Qed.
Lemma lem5450168 : term655.
Proof. exact (@lem5450157 (@lem5450167)). Qed.
Lemma lem5450170 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450171 : term617 = term623.
Proof. exact (@lem5450170 (NUMERAL 0) term193). Qed.
Lemma lem5450172 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450173 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450174 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450173 h1) (fun h1 : term623 = True => @lem5450172)). Qed.
Lemma lem5450175 : term623 = True.
Proof. exact (EQ_MP (@lem5450174) (@lem5450172)). Qed.
Lemma lem5450176 : term617 = True.
Proof. exact (TRANS (@lem5450171) (@lem5450175)). Qed.
Lemma lem5450177 : True = term617.
Proof. exact (SYM (@lem5450176)). Qed.
Lemma lem5450178 : term617.
Proof. exact (EQ_MP (@lem5450177) (@lem0)). Qed.
Lemma lem5450179 : term656.
Proof. exact (@lem5450168 (@lem5450178)). Qed.
Lemma lem5450181 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450182 : term617 = term623.
Proof. exact (@lem5450181 (NUMERAL 0) term193). Qed.
Lemma lem5450183 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450184 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450185 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450184 h1) (fun h1 : term623 = True => @lem5450183)). Qed.
Lemma lem5450186 : term623 = True.
Proof. exact (EQ_MP (@lem5450185) (@lem5450183)). Qed.
Lemma lem5450187 : term617 = True.
Proof. exact (TRANS (@lem5450182) (@lem5450186)). Qed.
Lemma lem5450188 : True = term617.
Proof. exact (SYM (@lem5450187)). Qed.
Lemma lem5450189 : term617.
Proof. exact (EQ_MP (@lem5450188) (@lem0)). Qed.
Lemma lem5450190 : term657.
Proof. exact (@lem5450179 (@lem5450189)). Qed.
Lemma lem5450192 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450193 : term247 = term248.
Proof. exact (@lem5450192 term193 term193). Qed.
Lemma lem5450194 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450195 : term250 = term193.
Proof. exact (EQ_MP (@lem5450194) (@lem940073)). Qed.
Lemma lem5450196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450197 : term248 = term192.
Proof. exact (MK_COMB (@lem5450196) (@lem5450195)). Qed.
Lemma lem5450198 : term247 = term192.
Proof. exact (TRANS (@lem5450193) (@lem5450197)). Qed.
Lemma lem5450200 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5450201 : term273 = term278.
Proof. exact (@lem5450200 term193 term193). Qed.
Lemma lem5450202 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450203 : term250 = term193.
Proof. exact (EQ_MP (@lem5450202) (@lem940073)). Qed.
Lemma lem5450204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450205 : term248 = term192.
Proof. exact (MK_COMB (@lem5450204) (@lem5450203)). Qed.
Lemma lem5450206 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5450207 : term278 = term238.
Proof. exact (MK_COMB (@lem5450206) (@lem5450205)). Qed.
Lemma lem5450208 : term273 = term238.
Proof. exact (TRANS (@lem5450201) (@lem5450207)). Qed.
Lemma lem5450209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450210 : term658 = term650.
Proof. exact (MK_COMB (@lem5450209) (@lem5450208)). Qed.
Lemma lem5450211 : term659 = term652.
Proof. exact (MK_COMB (@lem5450210) (@lem5450198)). Qed.
Lemma lem5450213 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5450214 : term652 = term170.
Proof. exact (@lem5450213 term193). Qed.
Lemma lem5450215 : term659 = term170.
Proof. exact (TRANS (@lem5450211) (@lem5450214)). Qed.
Lemma lem5450216 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450217 : term661 = term662.
Proof. exact (MK_COMB (@lem5450216) (@lem5450215)). Qed.
Lemma lem5450218 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5450219 : term663 = term628.
Proof. exact (MK_COMB (@lem5450217) (@lem5450218)). Qed.
Lemma lem5450221 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450222 : term628 = term170.
Proof. exact (@lem5450221 term193). Qed.
Lemma lem5450223 : term663 = term170.
Proof. exact (TRANS (@lem5450219) (@lem5450222)). Qed.
Lemma lem5450225 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450226 : term247 = term248.
Proof. exact (@lem5450225 term193 term193). Qed.
Lemma lem5450227 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450228 : term250 = term193.
Proof. exact (EQ_MP (@lem5450227) (@lem940073)). Qed.
Lemma lem5450229 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450230 : term248 = term192.
Proof. exact (MK_COMB (@lem5450229) (@lem5450228)). Qed.
Lemma lem5450231 : term247 = term192.
Proof. exact (TRANS (@lem5450226) (@lem5450230)). Qed.
Lemma lem5450232 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5450233 : term664 = term628.
Proof. exact (MK_COMB (@lem5450232) (@lem5450231)). Qed.
Lemma lem5450235 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450236 : term628 = term170.
Proof. exact (@lem5450235 term193). Qed.
Lemma lem5450237 : term664 = term170.
Proof. exact (TRANS (@lem5450233) (@lem5450236)). Qed.
Lemma lem5450238 : term170 = term664.
Proof. exact (SYM (@lem5450237)). Qed.
Lemma lem5450239 : term663 = term664.
Proof. exact (TRANS (@lem5450223) (@lem5450238)). Qed.
Lemma lem5450240 : term653 = term235.
Proof. exact (@lem5450190 (@lem5450239)). Qed.
Lemma lem5450241 : term652 = term235.
Proof. exact (TRANS (@lem5450156) (@lem5450240)). Qed.
Lemma lem5450243 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5450244 : term235 = term170.
Proof. exact (@lem5450243 term170). Qed.
Lemma lem5450245 : term652 = term170.
Proof. exact (TRANS (@lem5450241) (@lem5450244)). Qed.
Lemma lem5450246 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450247 : term665 = term662.
Proof. exact (MK_COMB (@lem5450246) (@lem5450245)). Qed.
Lemma lem5450248 (_70520 : int) : (real_of_int _70520) = (real_of_int _70520).
Proof. exact (eq_refl (real_of_int _70520)). Qed.
Lemma lem5450249 (_70520 : int) : (term649 _70520) = (term666 _70520).
Proof. exact (MK_COMB (@lem5450247) (@lem5450248 _70520)). Qed.
Lemma lem5450250 (_70520 : int) : (term648 _70520) = (term666 _70520).
Proof. exact (TRANS (@lem5450147 _70520) (@lem5450249 _70520)). Qed.
Lemma lem5450251 (_70520 : int) : (term666 _70520) = term170.
Proof. exact (@lem1982719 (real_of_int _70520)). Qed.
Lemma lem5450252 (_70520 : int) : (term648 _70520) = term170.
Proof. exact (TRANS (@lem5450250 _70520) (@lem5450251 _70520)). Qed.
Lemma lem5450253 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450254 (_70520 : int) : (term667 _70520) = term668.
Proof. exact (MK_COMB (@lem5450253) (@lem5450252 _70520)). Qed.
Lemma lem5450255 (_70521 : int) : (term718 _70521) = (term670 _70521).
Proof. exact (@lem1982759 (term285 _70521) (real_of_int _70521) term238). Qed.
Lemma lem5450256 (_70521 : int) : (term671 _70521) = (term649 _70521).
Proof. exact (@lem1982713 term238 (real_of_int _70521)). Qed.
Lemma lem5450258 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450259 : term192 = term272.
Proof. exact (@lem5450258 term193). Qed.
Lemma lem5450261 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5450262 : term238 = term239.
Proof. exact (@lem5450261 term193). Qed.
Lemma lem5450263 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450264 : term650 = term651.
Proof. exact (MK_COMB (@lem5450263) (@lem5450262)). Qed.
Lemma lem5450265 : term652 = term653.
Proof. exact (MK_COMB (@lem5450264) (@lem5450259)). Qed.
Lemma lem5450266 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5450268 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450269 : term617 = term623.
Proof. exact (@lem5450268 (NUMERAL 0) term193). Qed.
Lemma lem5450270 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450271 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450272 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450271 h1) (fun h1 : term623 = True => @lem5450270)). Qed.
Lemma lem5450273 : term623 = True.
Proof. exact (EQ_MP (@lem5450272) (@lem5450270)). Qed.
Lemma lem5450274 : term617 = True.
Proof. exact (TRANS (@lem5450269) (@lem5450273)). Qed.
Lemma lem5450275 : True = term617.
Proof. exact (SYM (@lem5450274)). Qed.
Lemma lem5450276 : term617.
Proof. exact (EQ_MP (@lem5450275) (@lem0)). Qed.
Lemma lem5450277 : term655.
Proof. exact (@lem5450266 (@lem5450276)). Qed.
Lemma lem5450279 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450280 : term617 = term623.
Proof. exact (@lem5450279 (NUMERAL 0) term193). Qed.
Lemma lem5450281 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450282 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450283 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450282 h1) (fun h1 : term623 = True => @lem5450281)). Qed.
Lemma lem5450284 : term623 = True.
Proof. exact (EQ_MP (@lem5450283) (@lem5450281)). Qed.
Lemma lem5450285 : term617 = True.
Proof. exact (TRANS (@lem5450280) (@lem5450284)). Qed.
Lemma lem5450286 : True = term617.
Proof. exact (SYM (@lem5450285)). Qed.
Lemma lem5450287 : term617.
Proof. exact (EQ_MP (@lem5450286) (@lem0)). Qed.
Lemma lem5450288 : term656.
Proof. exact (@lem5450277 (@lem5450287)). Qed.
Lemma lem5450290 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450291 : term617 = term623.
Proof. exact (@lem5450290 (NUMERAL 0) term193). Qed.
Lemma lem5450292 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450293 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450294 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450293 h1) (fun h1 : term623 = True => @lem5450292)). Qed.
Lemma lem5450295 : term623 = True.
Proof. exact (EQ_MP (@lem5450294) (@lem5450292)). Qed.
Lemma lem5450296 : term617 = True.
Proof. exact (TRANS (@lem5450291) (@lem5450295)). Qed.
Lemma lem5450297 : True = term617.
Proof. exact (SYM (@lem5450296)). Qed.
Lemma lem5450298 : term617.
Proof. exact (EQ_MP (@lem5450297) (@lem0)). Qed.
Lemma lem5450299 : term657.
Proof. exact (@lem5450288 (@lem5450298)). Qed.
Lemma lem5450301 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450302 : term247 = term248.
Proof. exact (@lem5450301 term193 term193). Qed.
Lemma lem5450303 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450304 : term250 = term193.
Proof. exact (EQ_MP (@lem5450303) (@lem940073)). Qed.
Lemma lem5450305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450306 : term248 = term192.
Proof. exact (MK_COMB (@lem5450305) (@lem5450304)). Qed.
Lemma lem5450307 : term247 = term192.
Proof. exact (TRANS (@lem5450302) (@lem5450306)). Qed.
Lemma lem5450309 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5450310 : term273 = term278.
Proof. exact (@lem5450309 term193 term193). Qed.
Lemma lem5450311 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450312 : term250 = term193.
Proof. exact (EQ_MP (@lem5450311) (@lem940073)). Qed.
Lemma lem5450313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450314 : term248 = term192.
Proof. exact (MK_COMB (@lem5450313) (@lem5450312)). Qed.
Lemma lem5450315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5450316 : term278 = term238.
Proof. exact (MK_COMB (@lem5450315) (@lem5450314)). Qed.
Lemma lem5450317 : term273 = term238.
Proof. exact (TRANS (@lem5450310) (@lem5450316)). Qed.
Lemma lem5450318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450319 : term658 = term650.
Proof. exact (MK_COMB (@lem5450318) (@lem5450317)). Qed.
Lemma lem5450320 : term659 = term652.
Proof. exact (MK_COMB (@lem5450319) (@lem5450307)). Qed.
Lemma lem5450322 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5450323 : term652 = term170.
Proof. exact (@lem5450322 term193). Qed.
Lemma lem5450324 : term659 = term170.
Proof. exact (TRANS (@lem5450320) (@lem5450323)). Qed.
Lemma lem5450325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450326 : term661 = term662.
Proof. exact (MK_COMB (@lem5450325) (@lem5450324)). Qed.
Lemma lem5450327 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5450328 : term663 = term628.
Proof. exact (MK_COMB (@lem5450326) (@lem5450327)). Qed.
Lemma lem5450330 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450331 : term628 = term170.
Proof. exact (@lem5450330 term193). Qed.
Lemma lem5450332 : term663 = term170.
Proof. exact (TRANS (@lem5450328) (@lem5450331)). Qed.
Lemma lem5450334 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450335 : term247 = term248.
Proof. exact (@lem5450334 term193 term193). Qed.
Lemma lem5450336 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450337 : term250 = term193.
Proof. exact (EQ_MP (@lem5450336) (@lem940073)). Qed.
Lemma lem5450338 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450339 : term248 = term192.
Proof. exact (MK_COMB (@lem5450338) (@lem5450337)). Qed.
Lemma lem5450340 : term247 = term192.
Proof. exact (TRANS (@lem5450335) (@lem5450339)). Qed.
Lemma lem5450341 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5450342 : term664 = term628.
Proof. exact (MK_COMB (@lem5450341) (@lem5450340)). Qed.
Lemma lem5450344 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450345 : term628 = term170.
Proof. exact (@lem5450344 term193). Qed.
Lemma lem5450346 : term664 = term170.
Proof. exact (TRANS (@lem5450342) (@lem5450345)). Qed.
Lemma lem5450347 : term170 = term664.
Proof. exact (SYM (@lem5450346)). Qed.
Lemma lem5450348 : term663 = term664.
Proof. exact (TRANS (@lem5450332) (@lem5450347)). Qed.
Lemma lem5450349 : term653 = term235.
Proof. exact (@lem5450299 (@lem5450348)). Qed.
Lemma lem5450350 : term652 = term235.
Proof. exact (TRANS (@lem5450265) (@lem5450349)). Qed.
Lemma lem5450352 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5450353 : term235 = term170.
Proof. exact (@lem5450352 term170). Qed.
Lemma lem5450354 : term652 = term170.
Proof. exact (TRANS (@lem5450350) (@lem5450353)). Qed.
Lemma lem5450355 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450356 : term665 = term662.
Proof. exact (MK_COMB (@lem5450355) (@lem5450354)). Qed.
Lemma lem5450357 (_70521 : int) : (real_of_int _70521) = (real_of_int _70521).
Proof. exact (eq_refl (real_of_int _70521)). Qed.
Lemma lem5450358 (_70521 : int) : (term649 _70521) = (term666 _70521).
Proof. exact (MK_COMB (@lem5450356) (@lem5450357 _70521)). Qed.
Lemma lem5450359 (_70521 : int) : (term671 _70521) = (term666 _70521).
Proof. exact (TRANS (@lem5450256 _70521) (@lem5450358 _70521)). Qed.
Lemma lem5450360 (_70521 : int) : (term666 _70521) = term170.
Proof. exact (@lem1982719 (real_of_int _70521)). Qed.
Lemma lem5450361 (_70521 : int) : (term671 _70521) = term170.
Proof. exact (TRANS (@lem5450359 _70521) (@lem5450360 _70521)). Qed.
Lemma lem5450362 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450363 (_70521 : int) : (term672 _70521) = term668.
Proof. exact (MK_COMB (@lem5450362) (@lem5450361 _70521)). Qed.
Lemma lem5450364 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5450365 (_70521 : int) : (term670 _70521) = term673.
Proof. exact (MK_COMB (@lem5450363 _70521) (@lem5450364)). Qed.
Lemma lem5450366 (_70521 : int) : (term718 _70521) = term673.
Proof. exact (TRANS (@lem5450255 _70521) (@lem5450365 _70521)). Qed.
Lemma lem5450367 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5450368 (_70521 : int) : (term718 _70521) = term238.
Proof. exact (TRANS (@lem5450366 _70521) (@lem5450367)). Qed.
Lemma lem5450369 (_70520 : int) (_70521 : int) : (term717 _70520 _70521) = term673.
Proof. exact (MK_COMB (@lem5450254 _70520) (@lem5450368 _70521)). Qed.
Lemma lem5450370 (_70520 : int) (_70521 : int) : (term716 _70520 _70521) = term673.
Proof. exact (TRANS (@lem5450146 _70520 _70521) (@lem5450369 _70520 _70521)). Qed.
Lemma lem5450371 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5450372 (_70520 : int) (_70521 : int) : (term716 _70520 _70521) = term238.
Proof. exact (TRANS (@lem5450370 _70520 _70521) (@lem5450371)). Qed.
Lemma lem5450373 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5450374 (_70520 : int) (_70521 : int) : (term719 _70520 _70521) = term675.
Proof. exact (MK_COMB (@lem5450373) (@lem5450372 _70520 _70521)). Qed.
Lemma lem5450375 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5450376 (_70520 : int) (_70521 : int) : (term715 _70520 _70521) = term676.
Proof. exact (MK_COMB (@lem5450374 _70520 _70521) (@lem5450375)). Qed.
Lemma lem5450377 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : term676.
Proof. exact (EQ_MP (@lem5450376 _70520 _70521) (@lem5450145 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450379 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5450380 : term676 = term677.
Proof. exact (@lem5450379 term170 term238). Qed.
Lemma lem5450382 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5450383 : term238 = term239.
Proof. exact (@lem5450382 term193). Qed.
Lemma lem5450385 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450386 : term170 = term235.
Proof. exact (@lem5450385 (NUMERAL 0)). Qed.
Lemma lem5450387 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5450388 : term172 = term678.
Proof. exact (MK_COMB (@lem5450387) (@lem5450386)). Qed.
Lemma lem5450389 : term677 = term679.
Proof. exact (MK_COMB (@lem5450388) (@lem5450383)). Qed.
Lemma lem5450390 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5450392 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450393 : term617 = term623.
Proof. exact (@lem5450392 (NUMERAL 0) term193). Qed.
Lemma lem5450394 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450395 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450396 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450395 h1) (fun h1 : term623 = True => @lem5450394)). Qed.
Lemma lem5450397 : term623 = True.
Proof. exact (EQ_MP (@lem5450396) (@lem5450394)). Qed.
Lemma lem5450398 : term617 = True.
Proof. exact (TRANS (@lem5450393) (@lem5450397)). Qed.
Lemma lem5450399 : True = term617.
Proof. exact (SYM (@lem5450398)). Qed.
Lemma lem5450400 : term617.
Proof. exact (EQ_MP (@lem5450399) (@lem0)). Qed.
Lemma lem5450401 : term681.
Proof. exact (@lem5450390 (@lem5450400)). Qed.
Lemma lem5450403 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450404 : term617 = term623.
Proof. exact (@lem5450403 (NUMERAL 0) term193). Qed.
Lemma lem5450405 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450406 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450407 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450406 h1) (fun h1 : term623 = True => @lem5450405)). Qed.
Lemma lem5450408 : term623 = True.
Proof. exact (EQ_MP (@lem5450407) (@lem5450405)). Qed.
Lemma lem5450409 : term617 = True.
Proof. exact (TRANS (@lem5450404) (@lem5450408)). Qed.
Lemma lem5450410 : True = term617.
Proof. exact (SYM (@lem5450409)). Qed.
Lemma lem5450411 : term617.
Proof. exact (EQ_MP (@lem5450410) (@lem0)). Qed.
Lemma lem5450412 : term679 = term682.
Proof. exact (@lem5450401 (@lem5450411)). Qed.
Lemma lem5450414 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5450415 : term273 = term278.
Proof. exact (@lem5450414 term193 term193). Qed.
Lemma lem5450416 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450417 : term250 = term193.
Proof. exact (EQ_MP (@lem5450416) (@lem940073)). Qed.
Lemma lem5450418 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450419 : term248 = term192.
Proof. exact (MK_COMB (@lem5450418) (@lem5450417)). Qed.
Lemma lem5450420 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5450421 : term278 = term238.
Proof. exact (MK_COMB (@lem5450420) (@lem5450419)). Qed.
Lemma lem5450422 : term273 = term238.
Proof. exact (TRANS (@lem5450415) (@lem5450421)). Qed.
Lemma lem5450424 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450425 : term628 = term170.
Proof. exact (@lem5450424 term193). Qed.
Lemma lem5450426 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5450427 : term683 = term172.
Proof. exact (MK_COMB (@lem5450426) (@lem5450425)). Qed.
Lemma lem5450428 : term682 = term677.
Proof. exact (MK_COMB (@lem5450427) (@lem5450422)). Qed.
Lemma lem5450430 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5450431 : term677 = term686.
Proof. exact (@lem5450430 (NUMERAL 0) term193). Qed.
Lemma lem5450432 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450433 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5450434 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450433 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5450432)). Qed.
Lemma lem5450435 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5450434) (@lem5450432)). Qed.
Lemma lem5450436 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5450437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5450438 : term687 = (and True).
Proof. exact (MK_COMB (@lem5450437) (@lem5450436)). Qed.
Lemma lem5450439 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5450438) (@lem5450435)). Qed.
Lemma lem5450441 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5450442 : term686 = False.
Proof. exact (TRANS (@lem5450439) (@lem5450441)). Qed.
Lemma lem5450443 : term677 = False.
Proof. exact (TRANS (@lem5450431) (@lem5450442)). Qed.
Lemma lem5450444 : term682 = False.
Proof. exact (TRANS (@lem5450428) (@lem5450443)). Qed.
Lemma lem5450445 : term679 = False.
Proof. exact (TRANS (@lem5450412) (@lem5450444)). Qed.
Lemma lem5450446 : term677 = False.
Proof. exact (TRANS (@lem5450389) (@lem5450445)). Qed.
Lemma lem5450447 : term676 = False.
Proof. exact (TRANS (@lem5450380) (@lem5450446)). Qed.
Lemma lem5450448 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term609 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5450447) (@lem5450377 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450449 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term611 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5449494 _70518 _70519 _70520 _70521 h1) (fun h0 : term603 _70518 _70519 _70520 _70521 => @lem5449971 _70518 _70519 _70520 _70521 h0) (fun h0 : term609 _70518 _70519 _70520 _70521 => @lem5450448 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5450450 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term569 _70518 _70519 _70520 _70521) : term569 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5450451 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term561 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5450452 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term540 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450451 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450454 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term560 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450452 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450456 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term559 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450454 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450458 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term558 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450456 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450460 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term557 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450458 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450462 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term556 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450460 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450464 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term323 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450462 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450465 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term290 _70518 _70519.
Proof. exact (proj1 (@lem5450462 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450466 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term321 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450464 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450468 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term320 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450466 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450471 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term318 _70518 _70519.
Proof. exact (proj1 (@lem5450468 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450473 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5450474 : term616 = term617.
Proof. exact (@lem5450473 term170 term192). Qed.
Lemma lem5450476 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450477 : term192 = term272.
Proof. exact (@lem5450476 term193). Qed.
Lemma lem5450479 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450480 : term170 = term235.
Proof. exact (@lem5450479 (NUMERAL 0)). Qed.
Lemma lem5450481 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450482 : term618 = term619.
Proof. exact (MK_COMB (@lem5450481) (@lem5450480)). Qed.
Lemma lem5450483 : term617 = term620.
Proof. exact (MK_COMB (@lem5450482) (@lem5450477)). Qed.
Lemma lem5450484 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5450486 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450487 : term617 = term623.
Proof. exact (@lem5450486 (NUMERAL 0) term193). Qed.
Lemma lem5450488 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450489 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450490 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450489 h1) (fun h1 : term623 = True => @lem5450488)). Qed.
Lemma lem5450491 : term623 = True.
Proof. exact (EQ_MP (@lem5450490) (@lem5450488)). Qed.
Lemma lem5450492 : term617 = True.
Proof. exact (TRANS (@lem5450487) (@lem5450491)). Qed.
Lemma lem5450493 : True = term617.
Proof. exact (SYM (@lem5450492)). Qed.
Lemma lem5450494 : term617.
Proof. exact (EQ_MP (@lem5450493) (@lem0)). Qed.
Lemma lem5450495 : term625.
Proof. exact (@lem5450484 (@lem5450494)). Qed.
Lemma lem5450497 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450498 : term617 = term623.
Proof. exact (@lem5450497 (NUMERAL 0) term193). Qed.
Lemma lem5450499 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450500 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450501 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450500 h1) (fun h1 : term623 = True => @lem5450499)). Qed.
Lemma lem5450502 : term623 = True.
Proof. exact (EQ_MP (@lem5450501) (@lem5450499)). Qed.
Lemma lem5450503 : term617 = True.
Proof. exact (TRANS (@lem5450498) (@lem5450502)). Qed.
Lemma lem5450504 : True = term617.
Proof. exact (SYM (@lem5450503)). Qed.
Lemma lem5450505 : term617.
Proof. exact (EQ_MP (@lem5450504) (@lem0)). Qed.
Lemma lem5450506 : term620 = term626.
Proof. exact (@lem5450495 (@lem5450505)). Qed.
Lemma lem5450508 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450509 : term247 = term248.
Proof. exact (@lem5450508 term193 term193). Qed.
Lemma lem5450510 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450511 : term250 = term193.
Proof. exact (EQ_MP (@lem5450510) (@lem940073)). Qed.
Lemma lem5450512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450513 : term248 = term192.
Proof. exact (MK_COMB (@lem5450512) (@lem5450511)). Qed.
Lemma lem5450514 : term247 = term192.
Proof. exact (TRANS (@lem5450509) (@lem5450513)). Qed.
Lemma lem5450516 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450517 : term628 = term170.
Proof. exact (@lem5450516 term193). Qed.
Lemma lem5450518 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450519 : term629 = term618.
Proof. exact (MK_COMB (@lem5450518) (@lem5450517)). Qed.
Lemma lem5450520 : term626 = term617.
Proof. exact (MK_COMB (@lem5450519) (@lem5450514)). Qed.
Lemma lem5450522 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450523 : term617 = term623.
Proof. exact (@lem5450522 (NUMERAL 0) term193). Qed.
Lemma lem5450524 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450525 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450526 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450525 h1) (fun h1 : term623 = True => @lem5450524)). Qed.
Lemma lem5450527 : term623 = True.
Proof. exact (EQ_MP (@lem5450526) (@lem5450524)). Qed.
Lemma lem5450528 : term617 = True.
Proof. exact (TRANS (@lem5450523) (@lem5450527)). Qed.
Lemma lem5450529 : term626 = True.
Proof. exact (TRANS (@lem5450520) (@lem5450528)). Qed.
Lemma lem5450530 : term620 = True.
Proof. exact (TRANS (@lem5450506) (@lem5450529)). Qed.
Lemma lem5450531 : term617 = True.
Proof. exact (TRANS (@lem5450483) (@lem5450530)). Qed.
Lemma lem5450532 : term616 = True.
Proof. exact (TRANS (@lem5450474) (@lem5450531)). Qed.
Lemma lem5450533 : True = term616.
Proof. exact (SYM (@lem5450532)). Qed.
Lemma lem5450534 : term616.
Proof. exact (EQ_MP (@lem5450533) (@lem0)). Qed.
Lemma lem5450535 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term688 _70518 _70519.
Proof. exact (conj (@lem5450534) (@lem5450465 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450537 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5450538 (_70518 : int) (_70519 : int) : term689 _70518 _70519.
Proof. exact (@lem5450537 term192 (term283 _70518 _70519)). Qed.
Lemma lem5450539 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term690 _70518 _70519.
Proof. exact (@lem5450538 _70518 _70519 (@lem5450535 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450540 (_70518 : int) (_70519 : int) : (term691 _70518 _70519) = (term283 _70518 _70519).
Proof. exact (@lem1982733 (term283 _70518 _70519)). Qed.
Lemma lem5450541 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5450542 (_70518 : int) (_70519 : int) : (term692 _70518 _70519) = (term289 _70518 _70519).
Proof. exact (MK_COMB (@lem5450541) (@lem5450540 _70518 _70519)). Qed.
Lemma lem5450543 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5450544 (_70518 : int) (_70519 : int) : (term690 _70518 _70519) = (term290 _70518 _70519).
Proof. exact (MK_COMB (@lem5450542 _70518 _70519) (@lem5450543)). Qed.
Lemma lem5450545 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term290 _70518 _70519.
Proof. exact (EQ_MP (@lem5450544 _70518 _70519) (@lem5450539 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450547 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5450548 : term616 = term617.
Proof. exact (@lem5450547 term170 term192). Qed.
Lemma lem5450550 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450551 : term192 = term272.
Proof. exact (@lem5450550 term193). Qed.
Lemma lem5450553 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450554 : term170 = term235.
Proof. exact (@lem5450553 (NUMERAL 0)). Qed.
Lemma lem5450555 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450556 : term618 = term619.
Proof. exact (MK_COMB (@lem5450555) (@lem5450554)). Qed.
Lemma lem5450557 : term617 = term620.
Proof. exact (MK_COMB (@lem5450556) (@lem5450551)). Qed.
Lemma lem5450558 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5450560 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450561 : term617 = term623.
Proof. exact (@lem5450560 (NUMERAL 0) term193). Qed.
Lemma lem5450562 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450563 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450564 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450563 h1) (fun h1 : term623 = True => @lem5450562)). Qed.
Lemma lem5450565 : term623 = True.
Proof. exact (EQ_MP (@lem5450564) (@lem5450562)). Qed.
Lemma lem5450566 : term617 = True.
Proof. exact (TRANS (@lem5450561) (@lem5450565)). Qed.
Lemma lem5450567 : True = term617.
Proof. exact (SYM (@lem5450566)). Qed.
Lemma lem5450568 : term617.
Proof. exact (EQ_MP (@lem5450567) (@lem0)). Qed.
Lemma lem5450569 : term625.
Proof. exact (@lem5450558 (@lem5450568)). Qed.
Lemma lem5450571 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450572 : term617 = term623.
Proof. exact (@lem5450571 (NUMERAL 0) term193). Qed.
Lemma lem5450573 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450574 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450575 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450574 h1) (fun h1 : term623 = True => @lem5450573)). Qed.
Lemma lem5450576 : term623 = True.
Proof. exact (EQ_MP (@lem5450575) (@lem5450573)). Qed.
Lemma lem5450577 : term617 = True.
Proof. exact (TRANS (@lem5450572) (@lem5450576)). Qed.
Lemma lem5450578 : True = term617.
Proof. exact (SYM (@lem5450577)). Qed.
Lemma lem5450579 : term617.
Proof. exact (EQ_MP (@lem5450578) (@lem0)). Qed.
Lemma lem5450580 : term620 = term626.
Proof. exact (@lem5450569 (@lem5450579)). Qed.
Lemma lem5450582 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450583 : term247 = term248.
Proof. exact (@lem5450582 term193 term193). Qed.
Lemma lem5450584 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450585 : term250 = term193.
Proof. exact (EQ_MP (@lem5450584) (@lem940073)). Qed.
Lemma lem5450586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450587 : term248 = term192.
Proof. exact (MK_COMB (@lem5450586) (@lem5450585)). Qed.
Lemma lem5450588 : term247 = term192.
Proof. exact (TRANS (@lem5450583) (@lem5450587)). Qed.
Lemma lem5450590 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450591 : term628 = term170.
Proof. exact (@lem5450590 term193). Qed.
Lemma lem5450592 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450593 : term629 = term618.
Proof. exact (MK_COMB (@lem5450592) (@lem5450591)). Qed.
Lemma lem5450594 : term626 = term617.
Proof. exact (MK_COMB (@lem5450593) (@lem5450588)). Qed.
Lemma lem5450596 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450597 : term617 = term623.
Proof. exact (@lem5450596 (NUMERAL 0) term193). Qed.
Lemma lem5450598 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450599 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450600 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450599 h1) (fun h1 : term623 = True => @lem5450598)). Qed.
Lemma lem5450601 : term623 = True.
Proof. exact (EQ_MP (@lem5450600) (@lem5450598)). Qed.
Lemma lem5450602 : term617 = True.
Proof. exact (TRANS (@lem5450597) (@lem5450601)). Qed.
Lemma lem5450603 : term626 = True.
Proof. exact (TRANS (@lem5450594) (@lem5450602)). Qed.
Lemma lem5450604 : term620 = True.
Proof. exact (TRANS (@lem5450580) (@lem5450603)). Qed.
Lemma lem5450605 : term617 = True.
Proof. exact (TRANS (@lem5450557) (@lem5450604)). Qed.
Lemma lem5450606 : term616 = True.
Proof. exact (TRANS (@lem5450548) (@lem5450605)). Qed.
Lemma lem5450607 : True = term616.
Proof. exact (SYM (@lem5450606)). Qed.
Lemma lem5450608 : term616.
Proof. exact (EQ_MP (@lem5450607) (@lem0)). Qed.
Lemma lem5450609 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term693 _70518 _70519.
Proof. exact (conj (@lem5450608) (@lem5450471 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450611 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5450612 (_70518 : int) (_70519 : int) : term694 _70518 _70519.
Proof. exact (@lem5450611 term192 (term316 _70518 _70519)). Qed.
Lemma lem5450613 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term695 _70518 _70519.
Proof. exact (@lem5450612 _70518 _70519 (@lem5450609 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450614 (_70518 : int) (_70519 : int) : (term696 _70518 _70519) = (term316 _70518 _70519).
Proof. exact (@lem1982733 (term316 _70518 _70519)). Qed.
Lemma lem5450615 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5450616 (_70518 : int) (_70519 : int) : (term697 _70518 _70519) = (term317 _70518 _70519).
Proof. exact (MK_COMB (@lem5450615) (@lem5450614 _70518 _70519)). Qed.
Lemma lem5450617 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5450618 (_70518 : int) (_70519 : int) : (term695 _70518 _70519) = (term318 _70518 _70519).
Proof. exact (MK_COMB (@lem5450616 _70518 _70519) (@lem5450617)). Qed.
Lemma lem5450619 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term318 _70518 _70519.
Proof. exact (EQ_MP (@lem5450618 _70518 _70519) (@lem5450613 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450620 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term698 _70518 _70519.
Proof. exact (conj (@lem5450619 _70518 _70519 _70520 _70521 h1) (@lem5450545 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450622 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5450623 (_70518 : int) (_70519 : int) : term699 _70518 _70519.
Proof. exact (@lem5450622 (term316 _70518 _70519) (term283 _70518 _70519)). Qed.
Lemma lem5450624 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term700 _70518 _70519.
Proof. exact (@lem5450623 _70518 _70519 (@lem5450620 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450625 (_70518 : int) (_70519 : int) : (term701 _70518 _70519) = (term702 _70518 _70519).
Proof. exact (@lem1982753 (term285 _70518) (real_of_int _70518) (real_of_int _70519) (term282 _70519)). Qed.
Lemma lem5450626 (_70518 : int) : (term671 _70518) = (term649 _70518).
Proof. exact (@lem1982713 term238 (real_of_int _70518)). Qed.
Lemma lem5450628 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450629 : term192 = term272.
Proof. exact (@lem5450628 term193). Qed.
Lemma lem5450631 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5450632 : term238 = term239.
Proof. exact (@lem5450631 term193). Qed.
Lemma lem5450633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450634 : term650 = term651.
Proof. exact (MK_COMB (@lem5450633) (@lem5450632)). Qed.
Lemma lem5450635 : term652 = term653.
Proof. exact (MK_COMB (@lem5450634) (@lem5450629)). Qed.
Lemma lem5450636 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5450638 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450639 : term617 = term623.
Proof. exact (@lem5450638 (NUMERAL 0) term193). Qed.
Lemma lem5450640 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450641 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450642 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450641 h1) (fun h1 : term623 = True => @lem5450640)). Qed.
Lemma lem5450643 : term623 = True.
Proof. exact (EQ_MP (@lem5450642) (@lem5450640)). Qed.
Lemma lem5450644 : term617 = True.
Proof. exact (TRANS (@lem5450639) (@lem5450643)). Qed.
Lemma lem5450645 : True = term617.
Proof. exact (SYM (@lem5450644)). Qed.
Lemma lem5450646 : term617.
Proof. exact (EQ_MP (@lem5450645) (@lem0)). Qed.
Lemma lem5450647 : term655.
Proof. exact (@lem5450636 (@lem5450646)). Qed.
Lemma lem5450649 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450650 : term617 = term623.
Proof. exact (@lem5450649 (NUMERAL 0) term193). Qed.
Lemma lem5450651 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450652 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450653 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450652 h1) (fun h1 : term623 = True => @lem5450651)). Qed.
Lemma lem5450654 : term623 = True.
Proof. exact (EQ_MP (@lem5450653) (@lem5450651)). Qed.
Lemma lem5450655 : term617 = True.
Proof. exact (TRANS (@lem5450650) (@lem5450654)). Qed.
Lemma lem5450656 : True = term617.
Proof. exact (SYM (@lem5450655)). Qed.
Lemma lem5450657 : term617.
Proof. exact (EQ_MP (@lem5450656) (@lem0)). Qed.
Lemma lem5450658 : term656.
Proof. exact (@lem5450647 (@lem5450657)). Qed.
Lemma lem5450660 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450661 : term617 = term623.
Proof. exact (@lem5450660 (NUMERAL 0) term193). Qed.
Lemma lem5450662 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450663 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450664 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450663 h1) (fun h1 : term623 = True => @lem5450662)). Qed.
Lemma lem5450665 : term623 = True.
Proof. exact (EQ_MP (@lem5450664) (@lem5450662)). Qed.
Lemma lem5450666 : term617 = True.
Proof. exact (TRANS (@lem5450661) (@lem5450665)). Qed.
Lemma lem5450667 : True = term617.
Proof. exact (SYM (@lem5450666)). Qed.
Lemma lem5450668 : term617.
Proof. exact (EQ_MP (@lem5450667) (@lem0)). Qed.
Lemma lem5450669 : term657.
Proof. exact (@lem5450658 (@lem5450668)). Qed.
Lemma lem5450671 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450672 : term247 = term248.
Proof. exact (@lem5450671 term193 term193). Qed.
Lemma lem5450673 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450674 : term250 = term193.
Proof. exact (EQ_MP (@lem5450673) (@lem940073)). Qed.
Lemma lem5450675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450676 : term248 = term192.
Proof. exact (MK_COMB (@lem5450675) (@lem5450674)). Qed.
Lemma lem5450677 : term247 = term192.
Proof. exact (TRANS (@lem5450672) (@lem5450676)). Qed.
Lemma lem5450679 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5450680 : term273 = term278.
Proof. exact (@lem5450679 term193 term193). Qed.
Lemma lem5450681 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450682 : term250 = term193.
Proof. exact (EQ_MP (@lem5450681) (@lem940073)). Qed.
Lemma lem5450683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450684 : term248 = term192.
Proof. exact (MK_COMB (@lem5450683) (@lem5450682)). Qed.
Lemma lem5450685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5450686 : term278 = term238.
Proof. exact (MK_COMB (@lem5450685) (@lem5450684)). Qed.
Lemma lem5450687 : term273 = term238.
Proof. exact (TRANS (@lem5450680) (@lem5450686)). Qed.
Lemma lem5450688 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450689 : term658 = term650.
Proof. exact (MK_COMB (@lem5450688) (@lem5450687)). Qed.
Lemma lem5450690 : term659 = term652.
Proof. exact (MK_COMB (@lem5450689) (@lem5450677)). Qed.
Lemma lem5450692 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5450693 : term652 = term170.
Proof. exact (@lem5450692 term193). Qed.
Lemma lem5450694 : term659 = term170.
Proof. exact (TRANS (@lem5450690) (@lem5450693)). Qed.
Lemma lem5450695 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450696 : term661 = term662.
Proof. exact (MK_COMB (@lem5450695) (@lem5450694)). Qed.
Lemma lem5450697 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5450698 : term663 = term628.
Proof. exact (MK_COMB (@lem5450696) (@lem5450697)). Qed.
Lemma lem5450700 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450701 : term628 = term170.
Proof. exact (@lem5450700 term193). Qed.
Lemma lem5450702 : term663 = term170.
Proof. exact (TRANS (@lem5450698) (@lem5450701)). Qed.
Lemma lem5450704 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450705 : term247 = term248.
Proof. exact (@lem5450704 term193 term193). Qed.
Lemma lem5450706 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450707 : term250 = term193.
Proof. exact (EQ_MP (@lem5450706) (@lem940073)). Qed.
Lemma lem5450708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450709 : term248 = term192.
Proof. exact (MK_COMB (@lem5450708) (@lem5450707)). Qed.
Lemma lem5450710 : term247 = term192.
Proof. exact (TRANS (@lem5450705) (@lem5450709)). Qed.
Lemma lem5450711 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5450712 : term664 = term628.
Proof. exact (MK_COMB (@lem5450711) (@lem5450710)). Qed.
Lemma lem5450714 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450715 : term628 = term170.
Proof. exact (@lem5450714 term193). Qed.
Lemma lem5450716 : term664 = term170.
Proof. exact (TRANS (@lem5450712) (@lem5450715)). Qed.
Lemma lem5450717 : term170 = term664.
Proof. exact (SYM (@lem5450716)). Qed.
Lemma lem5450718 : term663 = term664.
Proof. exact (TRANS (@lem5450702) (@lem5450717)). Qed.
Lemma lem5450719 : term653 = term235.
Proof. exact (@lem5450669 (@lem5450718)). Qed.
Lemma lem5450720 : term652 = term235.
Proof. exact (TRANS (@lem5450635) (@lem5450719)). Qed.
Lemma lem5450722 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5450723 : term235 = term170.
Proof. exact (@lem5450722 term170). Qed.
Lemma lem5450724 : term652 = term170.
Proof. exact (TRANS (@lem5450720) (@lem5450723)). Qed.
Lemma lem5450725 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450726 : term665 = term662.
Proof. exact (MK_COMB (@lem5450725) (@lem5450724)). Qed.
Lemma lem5450727 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5450728 (_70518 : int) : (term649 _70518) = (term666 _70518).
Proof. exact (MK_COMB (@lem5450726) (@lem5450727 _70518)). Qed.
Lemma lem5450729 (_70518 : int) : (term671 _70518) = (term666 _70518).
Proof. exact (TRANS (@lem5450626 _70518) (@lem5450728 _70518)). Qed.
Lemma lem5450730 (_70518 : int) : (term666 _70518) = term170.
Proof. exact (@lem1982719 (real_of_int _70518)). Qed.
Lemma lem5450731 (_70518 : int) : (term671 _70518) = term170.
Proof. exact (TRANS (@lem5450729 _70518) (@lem5450730 _70518)). Qed.
Lemma lem5450732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450733 (_70518 : int) : (term672 _70518) = term668.
Proof. exact (MK_COMB (@lem5450732) (@lem5450731 _70518)). Qed.
Lemma lem5450734 (_70519 : int) : (term703 _70519) = (term704 _70519).
Proof. exact (@lem1982763 (real_of_int _70519) (term285 _70519) term238). Qed.
Lemma lem5450735 (_70519 : int) : (term648 _70519) = (term649 _70519).
Proof. exact (@lem1982715 term238 (real_of_int _70519)). Qed.
Lemma lem5450737 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450738 : term192 = term272.
Proof. exact (@lem5450737 term193). Qed.
Lemma lem5450740 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5450741 : term238 = term239.
Proof. exact (@lem5450740 term193). Qed.
Lemma lem5450742 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450743 : term650 = term651.
Proof. exact (MK_COMB (@lem5450742) (@lem5450741)). Qed.
Lemma lem5450744 : term652 = term653.
Proof. exact (MK_COMB (@lem5450743) (@lem5450738)). Qed.
Lemma lem5450745 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5450747 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450748 : term617 = term623.
Proof. exact (@lem5450747 (NUMERAL 0) term193). Qed.
Lemma lem5450749 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450750 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450751 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450750 h1) (fun h1 : term623 = True => @lem5450749)). Qed.
Lemma lem5450752 : term623 = True.
Proof. exact (EQ_MP (@lem5450751) (@lem5450749)). Qed.
Lemma lem5450753 : term617 = True.
Proof. exact (TRANS (@lem5450748) (@lem5450752)). Qed.
Lemma lem5450754 : True = term617.
Proof. exact (SYM (@lem5450753)). Qed.
Lemma lem5450755 : term617.
Proof. exact (EQ_MP (@lem5450754) (@lem0)). Qed.
Lemma lem5450756 : term655.
Proof. exact (@lem5450745 (@lem5450755)). Qed.
Lemma lem5450758 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450759 : term617 = term623.
Proof. exact (@lem5450758 (NUMERAL 0) term193). Qed.
Lemma lem5450760 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450761 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450762 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450761 h1) (fun h1 : term623 = True => @lem5450760)). Qed.
Lemma lem5450763 : term623 = True.
Proof. exact (EQ_MP (@lem5450762) (@lem5450760)). Qed.
Lemma lem5450764 : term617 = True.
Proof. exact (TRANS (@lem5450759) (@lem5450763)). Qed.
Lemma lem5450765 : True = term617.
Proof. exact (SYM (@lem5450764)). Qed.
Lemma lem5450766 : term617.
Proof. exact (EQ_MP (@lem5450765) (@lem0)). Qed.
Lemma lem5450767 : term656.
Proof. exact (@lem5450756 (@lem5450766)). Qed.
Lemma lem5450769 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450770 : term617 = term623.
Proof. exact (@lem5450769 (NUMERAL 0) term193). Qed.
Lemma lem5450771 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450772 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450773 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450772 h1) (fun h1 : term623 = True => @lem5450771)). Qed.
Lemma lem5450774 : term623 = True.
Proof. exact (EQ_MP (@lem5450773) (@lem5450771)). Qed.
Lemma lem5450775 : term617 = True.
Proof. exact (TRANS (@lem5450770) (@lem5450774)). Qed.
Lemma lem5450776 : True = term617.
Proof. exact (SYM (@lem5450775)). Qed.
Lemma lem5450777 : term617.
Proof. exact (EQ_MP (@lem5450776) (@lem0)). Qed.
Lemma lem5450778 : term657.
Proof. exact (@lem5450767 (@lem5450777)). Qed.
Lemma lem5450780 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450781 : term247 = term248.
Proof. exact (@lem5450780 term193 term193). Qed.
Lemma lem5450782 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450783 : term250 = term193.
Proof. exact (EQ_MP (@lem5450782) (@lem940073)). Qed.
Lemma lem5450784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450785 : term248 = term192.
Proof. exact (MK_COMB (@lem5450784) (@lem5450783)). Qed.
Lemma lem5450786 : term247 = term192.
Proof. exact (TRANS (@lem5450781) (@lem5450785)). Qed.
Lemma lem5450788 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5450789 : term273 = term278.
Proof. exact (@lem5450788 term193 term193). Qed.
Lemma lem5450790 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450791 : term250 = term193.
Proof. exact (EQ_MP (@lem5450790) (@lem940073)). Qed.
Lemma lem5450792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450793 : term248 = term192.
Proof. exact (MK_COMB (@lem5450792) (@lem5450791)). Qed.
Lemma lem5450794 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5450795 : term278 = term238.
Proof. exact (MK_COMB (@lem5450794) (@lem5450793)). Qed.
Lemma lem5450796 : term273 = term238.
Proof. exact (TRANS (@lem5450789) (@lem5450795)). Qed.
Lemma lem5450797 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450798 : term658 = term650.
Proof. exact (MK_COMB (@lem5450797) (@lem5450796)). Qed.
Lemma lem5450799 : term659 = term652.
Proof. exact (MK_COMB (@lem5450798) (@lem5450786)). Qed.
Lemma lem5450801 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5450802 : term652 = term170.
Proof. exact (@lem5450801 term193). Qed.
Lemma lem5450803 : term659 = term170.
Proof. exact (TRANS (@lem5450799) (@lem5450802)). Qed.
Lemma lem5450804 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450805 : term661 = term662.
Proof. exact (MK_COMB (@lem5450804) (@lem5450803)). Qed.
Lemma lem5450806 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5450807 : term663 = term628.
Proof. exact (MK_COMB (@lem5450805) (@lem5450806)). Qed.
Lemma lem5450809 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450810 : term628 = term170.
Proof. exact (@lem5450809 term193). Qed.
Lemma lem5450811 : term663 = term170.
Proof. exact (TRANS (@lem5450807) (@lem5450810)). Qed.
Lemma lem5450813 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450814 : term247 = term248.
Proof. exact (@lem5450813 term193 term193). Qed.
Lemma lem5450815 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450816 : term250 = term193.
Proof. exact (EQ_MP (@lem5450815) (@lem940073)). Qed.
Lemma lem5450817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450818 : term248 = term192.
Proof. exact (MK_COMB (@lem5450817) (@lem5450816)). Qed.
Lemma lem5450819 : term247 = term192.
Proof. exact (TRANS (@lem5450814) (@lem5450818)). Qed.
Lemma lem5450820 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5450821 : term664 = term628.
Proof. exact (MK_COMB (@lem5450820) (@lem5450819)). Qed.
Lemma lem5450823 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450824 : term628 = term170.
Proof. exact (@lem5450823 term193). Qed.
Lemma lem5450825 : term664 = term170.
Proof. exact (TRANS (@lem5450821) (@lem5450824)). Qed.
Lemma lem5450826 : term170 = term664.
Proof. exact (SYM (@lem5450825)). Qed.
Lemma lem5450827 : term663 = term664.
Proof. exact (TRANS (@lem5450811) (@lem5450826)). Qed.
Lemma lem5450828 : term653 = term235.
Proof. exact (@lem5450778 (@lem5450827)). Qed.
Lemma lem5450829 : term652 = term235.
Proof. exact (TRANS (@lem5450744) (@lem5450828)). Qed.
Lemma lem5450831 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5450832 : term235 = term170.
Proof. exact (@lem5450831 term170). Qed.
Lemma lem5450833 : term652 = term170.
Proof. exact (TRANS (@lem5450829) (@lem5450832)). Qed.
Lemma lem5450834 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5450835 : term665 = term662.
Proof. exact (MK_COMB (@lem5450834) (@lem5450833)). Qed.
Lemma lem5450836 (_70519 : int) : (real_of_int _70519) = (real_of_int _70519).
Proof. exact (eq_refl (real_of_int _70519)). Qed.
Lemma lem5450837 (_70519 : int) : (term649 _70519) = (term666 _70519).
Proof. exact (MK_COMB (@lem5450835) (@lem5450836 _70519)). Qed.
Lemma lem5450838 (_70519 : int) : (term648 _70519) = (term666 _70519).
Proof. exact (TRANS (@lem5450735 _70519) (@lem5450837 _70519)). Qed.
Lemma lem5450839 (_70519 : int) : (term666 _70519) = term170.
Proof. exact (@lem1982719 (real_of_int _70519)). Qed.
Lemma lem5450840 (_70519 : int) : (term648 _70519) = term170.
Proof. exact (TRANS (@lem5450838 _70519) (@lem5450839 _70519)). Qed.
Lemma lem5450841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5450842 (_70519 : int) : (term667 _70519) = term668.
Proof. exact (MK_COMB (@lem5450841) (@lem5450840 _70519)). Qed.
Lemma lem5450843 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5450844 (_70519 : int) : (term704 _70519) = term673.
Proof. exact (MK_COMB (@lem5450842 _70519) (@lem5450843)). Qed.
Lemma lem5450845 (_70519 : int) : (term703 _70519) = term673.
Proof. exact (TRANS (@lem5450734 _70519) (@lem5450844 _70519)). Qed.
Lemma lem5450846 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5450847 (_70519 : int) : (term703 _70519) = term238.
Proof. exact (TRANS (@lem5450845 _70519) (@lem5450846)). Qed.
Lemma lem5450848 (_70518 : int) (_70519 : int) : (term702 _70518 _70519) = term673.
Proof. exact (MK_COMB (@lem5450733 _70518) (@lem5450847 _70519)). Qed.
Lemma lem5450849 (_70518 : int) (_70519 : int) : (term701 _70518 _70519) = term673.
Proof. exact (TRANS (@lem5450625 _70518 _70519) (@lem5450848 _70518 _70519)). Qed.
Lemma lem5450850 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5450851 (_70518 : int) (_70519 : int) : (term701 _70518 _70519) = term238.
Proof. exact (TRANS (@lem5450849 _70518 _70519) (@lem5450850)). Qed.
Lemma lem5450852 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5450853 (_70518 : int) (_70519 : int) : (term705 _70518 _70519) = term675.
Proof. exact (MK_COMB (@lem5450852) (@lem5450851 _70518 _70519)). Qed.
Lemma lem5450854 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5450855 (_70518 : int) (_70519 : int) : (term700 _70518 _70519) = term676.
Proof. exact (MK_COMB (@lem5450853 _70518 _70519) (@lem5450854)). Qed.
Lemma lem5450856 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : term676.
Proof. exact (EQ_MP (@lem5450855 _70518 _70519) (@lem5450624 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450858 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5450859 : term676 = term677.
Proof. exact (@lem5450858 term170 term238). Qed.
Lemma lem5450861 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5450862 : term238 = term239.
Proof. exact (@lem5450861 term193). Qed.
Lemma lem5450864 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450865 : term170 = term235.
Proof. exact (@lem5450864 (NUMERAL 0)). Qed.
Lemma lem5450866 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5450867 : term172 = term678.
Proof. exact (MK_COMB (@lem5450866) (@lem5450865)). Qed.
Lemma lem5450868 : term677 = term679.
Proof. exact (MK_COMB (@lem5450867) (@lem5450862)). Qed.
Lemma lem5450869 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5450871 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450872 : term617 = term623.
Proof. exact (@lem5450871 (NUMERAL 0) term193). Qed.
Lemma lem5450873 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450874 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450875 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450874 h1) (fun h1 : term623 = True => @lem5450873)). Qed.
Lemma lem5450876 : term623 = True.
Proof. exact (EQ_MP (@lem5450875) (@lem5450873)). Qed.
Lemma lem5450877 : term617 = True.
Proof. exact (TRANS (@lem5450872) (@lem5450876)). Qed.
Lemma lem5450878 : True = term617.
Proof. exact (SYM (@lem5450877)). Qed.
Lemma lem5450879 : term617.
Proof. exact (EQ_MP (@lem5450878) (@lem0)). Qed.
Lemma lem5450880 : term681.
Proof. exact (@lem5450869 (@lem5450879)). Qed.
Lemma lem5450882 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450883 : term617 = term623.
Proof. exact (@lem5450882 (NUMERAL 0) term193). Qed.
Lemma lem5450884 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450885 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450886 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450885 h1) (fun h1 : term623 = True => @lem5450884)). Qed.
Lemma lem5450887 : term623 = True.
Proof. exact (EQ_MP (@lem5450886) (@lem5450884)). Qed.
Lemma lem5450888 : term617 = True.
Proof. exact (TRANS (@lem5450883) (@lem5450887)). Qed.
Lemma lem5450889 : True = term617.
Proof. exact (SYM (@lem5450888)). Qed.
Lemma lem5450890 : term617.
Proof. exact (EQ_MP (@lem5450889) (@lem0)). Qed.
Lemma lem5450891 : term679 = term682.
Proof. exact (@lem5450880 (@lem5450890)). Qed.
Lemma lem5450893 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5450894 : term273 = term278.
Proof. exact (@lem5450893 term193 term193). Qed.
Lemma lem5450895 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450896 : term250 = term193.
Proof. exact (EQ_MP (@lem5450895) (@lem940073)). Qed.
Lemma lem5450897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450898 : term248 = term192.
Proof. exact (MK_COMB (@lem5450897) (@lem5450896)). Qed.
Lemma lem5450899 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5450900 : term278 = term238.
Proof. exact (MK_COMB (@lem5450899) (@lem5450898)). Qed.
Lemma lem5450901 : term273 = term238.
Proof. exact (TRANS (@lem5450894) (@lem5450900)). Qed.
Lemma lem5450903 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450904 : term628 = term170.
Proof. exact (@lem5450903 term193). Qed.
Lemma lem5450905 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5450906 : term683 = term172.
Proof. exact (MK_COMB (@lem5450905) (@lem5450904)). Qed.
Lemma lem5450907 : term682 = term677.
Proof. exact (MK_COMB (@lem5450906) (@lem5450901)). Qed.
Lemma lem5450909 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5450910 : term677 = term686.
Proof. exact (@lem5450909 (NUMERAL 0) term193). Qed.
Lemma lem5450911 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450912 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5450913 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450912 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5450911)). Qed.
Lemma lem5450914 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5450913) (@lem5450911)). Qed.
Lemma lem5450915 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5450916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5450917 : term687 = (and True).
Proof. exact (MK_COMB (@lem5450916) (@lem5450915)). Qed.
Lemma lem5450918 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5450917) (@lem5450914)). Qed.
Lemma lem5450920 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5450921 : term686 = False.
Proof. exact (TRANS (@lem5450918) (@lem5450920)). Qed.
Lemma lem5450922 : term677 = False.
Proof. exact (TRANS (@lem5450910) (@lem5450921)). Qed.
Lemma lem5450923 : term682 = False.
Proof. exact (TRANS (@lem5450907) (@lem5450922)). Qed.
Lemma lem5450924 : term679 = False.
Proof. exact (TRANS (@lem5450891) (@lem5450923)). Qed.
Lemma lem5450925 : term677 = False.
Proof. exact (TRANS (@lem5450868) (@lem5450924)). Qed.
Lemma lem5450926 : term676 = False.
Proof. exact (TRANS (@lem5450859) (@lem5450925)). Qed.
Lemma lem5450927 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term561 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5450926) (@lem5450856 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450928 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term567 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5450929 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term536 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450928 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450931 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term566 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450929 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450933 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term565 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450931 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450935 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term564 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450933 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450937 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term563 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450935 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450939 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term562 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450937 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450941 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term323 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450939 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450942 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term290 _70518 _70521.
Proof. exact (proj1 (@lem5450939 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450943 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term321 _70518 _70519 _70520 _70521.
Proof. exact (proj2 (@lem5450941 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450946 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term318 _70518 _70521.
Proof. exact (proj1 (@lem5450943 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5450950 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5450951 : term616 = term617.
Proof. exact (@lem5450950 term170 term192). Qed.
Lemma lem5450953 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450954 : term192 = term272.
Proof. exact (@lem5450953 term193). Qed.
Lemma lem5450956 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5450957 : term170 = term235.
Proof. exact (@lem5450956 (NUMERAL 0)). Qed.
Lemma lem5450958 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450959 : term618 = term619.
Proof. exact (MK_COMB (@lem5450958) (@lem5450957)). Qed.
Lemma lem5450960 : term617 = term620.
Proof. exact (MK_COMB (@lem5450959) (@lem5450954)). Qed.
Lemma lem5450961 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5450963 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450964 : term617 = term623.
Proof. exact (@lem5450963 (NUMERAL 0) term193). Qed.
Lemma lem5450965 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450966 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450967 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450966 h1) (fun h1 : term623 = True => @lem5450965)). Qed.
Lemma lem5450968 : term623 = True.
Proof. exact (EQ_MP (@lem5450967) (@lem5450965)). Qed.
Lemma lem5450969 : term617 = True.
Proof. exact (TRANS (@lem5450964) (@lem5450968)). Qed.
Lemma lem5450970 : True = term617.
Proof. exact (SYM (@lem5450969)). Qed.
Lemma lem5450971 : term617.
Proof. exact (EQ_MP (@lem5450970) (@lem0)). Qed.
Lemma lem5450972 : term625.
Proof. exact (@lem5450961 (@lem5450971)). Qed.
Lemma lem5450974 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5450975 : term617 = term623.
Proof. exact (@lem5450974 (NUMERAL 0) term193). Qed.
Lemma lem5450976 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5450977 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5450978 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5450977 h1) (fun h1 : term623 = True => @lem5450976)). Qed.
Lemma lem5450979 : term623 = True.
Proof. exact (EQ_MP (@lem5450978) (@lem5450976)). Qed.
Lemma lem5450980 : term617 = True.
Proof. exact (TRANS (@lem5450975) (@lem5450979)). Qed.
Lemma lem5450981 : True = term617.
Proof. exact (SYM (@lem5450980)). Qed.
Lemma lem5450982 : term617.
Proof. exact (EQ_MP (@lem5450981) (@lem0)). Qed.
Lemma lem5450983 : term620 = term626.
Proof. exact (@lem5450972 (@lem5450982)). Qed.
Lemma lem5450985 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5450986 : term247 = term248.
Proof. exact (@lem5450985 term193 term193). Qed.
Lemma lem5450987 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5450988 : term250 = term193.
Proof. exact (EQ_MP (@lem5450987) (@lem940073)). Qed.
Lemma lem5450989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5450990 : term248 = term192.
Proof. exact (MK_COMB (@lem5450989) (@lem5450988)). Qed.
Lemma lem5450991 : term247 = term192.
Proof. exact (TRANS (@lem5450986) (@lem5450990)). Qed.
Lemma lem5450993 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5450994 : term628 = term170.
Proof. exact (@lem5450993 term193). Qed.
Lemma lem5450995 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5450996 : term629 = term618.
Proof. exact (MK_COMB (@lem5450995) (@lem5450994)). Qed.
Lemma lem5450997 : term626 = term617.
Proof. exact (MK_COMB (@lem5450996) (@lem5450991)). Qed.
Lemma lem5450999 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451000 : term617 = term623.
Proof. exact (@lem5450999 (NUMERAL 0) term193). Qed.
Lemma lem5451001 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451002 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451003 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451002 h1) (fun h1 : term623 = True => @lem5451001)). Qed.
Lemma lem5451004 : term623 = True.
Proof. exact (EQ_MP (@lem5451003) (@lem5451001)). Qed.
Lemma lem5451005 : term617 = True.
Proof. exact (TRANS (@lem5451000) (@lem5451004)). Qed.
Lemma lem5451006 : term626 = True.
Proof. exact (TRANS (@lem5450997) (@lem5451005)). Qed.
Lemma lem5451007 : term620 = True.
Proof. exact (TRANS (@lem5450983) (@lem5451006)). Qed.
Lemma lem5451008 : term617 = True.
Proof. exact (TRANS (@lem5450960) (@lem5451007)). Qed.
Lemma lem5451009 : term616 = True.
Proof. exact (TRANS (@lem5450951) (@lem5451008)). Qed.
Lemma lem5451010 : True = term616.
Proof. exact (SYM (@lem5451009)). Qed.
Lemma lem5451011 : term616.
Proof. exact (EQ_MP (@lem5451010) (@lem0)). Qed.
Lemma lem5451012 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term693 _70518 _70521.
Proof. exact (conj (@lem5451011) (@lem5450946 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451014 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5451015 (_70518 : int) (_70521 : int) : term694 _70518 _70521.
Proof. exact (@lem5451014 term192 (term316 _70518 _70521)). Qed.
Lemma lem5451016 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term695 _70518 _70521.
Proof. exact (@lem5451015 _70518 _70521 (@lem5451012 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451017 (_70518 : int) (_70521 : int) : (term696 _70518 _70521) = (term316 _70518 _70521).
Proof. exact (@lem1982733 (term316 _70518 _70521)). Qed.
Lemma lem5451018 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5451019 (_70518 : int) (_70521 : int) : (term697 _70518 _70521) = (term317 _70518 _70521).
Proof. exact (MK_COMB (@lem5451018) (@lem5451017 _70518 _70521)). Qed.
Lemma lem5451020 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5451021 (_70518 : int) (_70521 : int) : (term695 _70518 _70521) = (term318 _70518 _70521).
Proof. exact (MK_COMB (@lem5451019 _70518 _70521) (@lem5451020)). Qed.
Lemma lem5451022 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term318 _70518 _70521.
Proof. exact (EQ_MP (@lem5451021 _70518 _70521) (@lem5451016 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451024 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5451025 : term616 = term617.
Proof. exact (@lem5451024 term170 term192). Qed.
Lemma lem5451027 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5451028 : term192 = term272.
Proof. exact (@lem5451027 term193). Qed.
Lemma lem5451030 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5451031 : term170 = term235.
Proof. exact (@lem5451030 (NUMERAL 0)). Qed.
Lemma lem5451032 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5451033 : term618 = term619.
Proof. exact (MK_COMB (@lem5451032) (@lem5451031)). Qed.
Lemma lem5451034 : term617 = term620.
Proof. exact (MK_COMB (@lem5451033) (@lem5451028)). Qed.
Lemma lem5451035 : term621.
Proof. exact (@lem1980255 term170 term192 term192 term192). Qed.
Lemma lem5451037 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451038 : term617 = term623.
Proof. exact (@lem5451037 (NUMERAL 0) term193). Qed.
Lemma lem5451039 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451040 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451041 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451040 h1) (fun h1 : term623 = True => @lem5451039)). Qed.
Lemma lem5451042 : term623 = True.
Proof. exact (EQ_MP (@lem5451041) (@lem5451039)). Qed.
Lemma lem5451043 : term617 = True.
Proof. exact (TRANS (@lem5451038) (@lem5451042)). Qed.
Lemma lem5451044 : True = term617.
Proof. exact (SYM (@lem5451043)). Qed.
Lemma lem5451045 : term617.
Proof. exact (EQ_MP (@lem5451044) (@lem0)). Qed.
Lemma lem5451046 : term625.
Proof. exact (@lem5451035 (@lem5451045)). Qed.
Lemma lem5451048 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451049 : term617 = term623.
Proof. exact (@lem5451048 (NUMERAL 0) term193). Qed.
Lemma lem5451050 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451051 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451052 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451051 h1) (fun h1 : term623 = True => @lem5451050)). Qed.
Lemma lem5451053 : term623 = True.
Proof. exact (EQ_MP (@lem5451052) (@lem5451050)). Qed.
Lemma lem5451054 : term617 = True.
Proof. exact (TRANS (@lem5451049) (@lem5451053)). Qed.
Lemma lem5451055 : True = term617.
Proof. exact (SYM (@lem5451054)). Qed.
Lemma lem5451056 : term617.
Proof. exact (EQ_MP (@lem5451055) (@lem0)). Qed.
Lemma lem5451057 : term620 = term626.
Proof. exact (@lem5451046 (@lem5451056)). Qed.
Lemma lem5451059 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5451060 : term247 = term248.
Proof. exact (@lem5451059 term193 term193). Qed.
Lemma lem5451061 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451062 : term250 = term193.
Proof. exact (EQ_MP (@lem5451061) (@lem940073)). Qed.
Lemma lem5451063 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451064 : term248 = term192.
Proof. exact (MK_COMB (@lem5451063) (@lem5451062)). Qed.
Lemma lem5451065 : term247 = term192.
Proof. exact (TRANS (@lem5451060) (@lem5451064)). Qed.
Lemma lem5451067 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5451068 : term628 = term170.
Proof. exact (@lem5451067 term193). Qed.
Lemma lem5451069 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5451070 : term629 = term618.
Proof. exact (MK_COMB (@lem5451069) (@lem5451068)). Qed.
Lemma lem5451071 : term626 = term617.
Proof. exact (MK_COMB (@lem5451070) (@lem5451065)). Qed.
Lemma lem5451073 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451074 : term617 = term623.
Proof. exact (@lem5451073 (NUMERAL 0) term193). Qed.
Lemma lem5451075 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451076 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451077 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451076 h1) (fun h1 : term623 = True => @lem5451075)). Qed.
Lemma lem5451078 : term623 = True.
Proof. exact (EQ_MP (@lem5451077) (@lem5451075)). Qed.
Lemma lem5451079 : term617 = True.
Proof. exact (TRANS (@lem5451074) (@lem5451078)). Qed.
Lemma lem5451080 : term626 = True.
Proof. exact (TRANS (@lem5451071) (@lem5451079)). Qed.
Lemma lem5451081 : term620 = True.
Proof. exact (TRANS (@lem5451057) (@lem5451080)). Qed.
Lemma lem5451082 : term617 = True.
Proof. exact (TRANS (@lem5451034) (@lem5451081)). Qed.
Lemma lem5451083 : term616 = True.
Proof. exact (TRANS (@lem5451025) (@lem5451082)). Qed.
Lemma lem5451084 : True = term616.
Proof. exact (SYM (@lem5451083)). Qed.
Lemma lem5451085 : term616.
Proof. exact (EQ_MP (@lem5451084) (@lem0)). Qed.
Lemma lem5451086 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term688 _70518 _70521.
Proof. exact (conj (@lem5451085) (@lem5450942 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451088 (x : real) (y : real) : term631 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5451089 (_70518 : int) (_70521 : int) : term689 _70518 _70521.
Proof. exact (@lem5451088 term192 (term283 _70518 _70521)). Qed.
Lemma lem5451090 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term690 _70518 _70521.
Proof. exact (@lem5451089 _70518 _70521 (@lem5451086 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451091 (_70518 : int) (_70521 : int) : (term691 _70518 _70521) = (term283 _70518 _70521).
Proof. exact (@lem1982733 (term283 _70518 _70521)). Qed.
Lemma lem5451092 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5451093 (_70518 : int) (_70521 : int) : (term692 _70518 _70521) = (term289 _70518 _70521).
Proof. exact (MK_COMB (@lem5451092) (@lem5451091 _70518 _70521)). Qed.
Lemma lem5451094 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5451095 (_70518 : int) (_70521 : int) : (term690 _70518 _70521) = (term290 _70518 _70521).
Proof. exact (MK_COMB (@lem5451093 _70518 _70521) (@lem5451094)). Qed.
Lemma lem5451096 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term290 _70518 _70521.
Proof. exact (EQ_MP (@lem5451095 _70518 _70521) (@lem5451090 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451097 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term713 _70518 _70521.
Proof. exact (conj (@lem5451096 _70518 _70519 _70520 _70521 h1) (@lem5451022 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451099 (x : real) (y : real) : term642 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5451100 (_70518 : int) (_70521 : int) : term714 _70518 _70521.
Proof. exact (@lem5451099 (term283 _70518 _70521) (term316 _70518 _70521)). Qed.
Lemma lem5451101 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term715 _70518 _70521.
Proof. exact (@lem5451100 _70518 _70521 (@lem5451097 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451102 (_70518 : int) (_70521 : int) : (term716 _70518 _70521) = (term717 _70518 _70521).
Proof. exact (@lem1982753 (real_of_int _70518) (term285 _70518) (term282 _70521) (real_of_int _70521)). Qed.
Lemma lem5451103 (_70518 : int) : (term648 _70518) = (term649 _70518).
Proof. exact (@lem1982715 term238 (real_of_int _70518)). Qed.
Lemma lem5451105 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5451106 : term192 = term272.
Proof. exact (@lem5451105 term193). Qed.
Lemma lem5451108 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5451109 : term238 = term239.
Proof. exact (@lem5451108 term193). Qed.
Lemma lem5451110 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5451111 : term650 = term651.
Proof. exact (MK_COMB (@lem5451110) (@lem5451109)). Qed.
Lemma lem5451112 : term652 = term653.
Proof. exact (MK_COMB (@lem5451111) (@lem5451106)). Qed.
Lemma lem5451113 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5451115 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451116 : term617 = term623.
Proof. exact (@lem5451115 (NUMERAL 0) term193). Qed.
Lemma lem5451117 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451118 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451119 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451118 h1) (fun h1 : term623 = True => @lem5451117)). Qed.
Lemma lem5451120 : term623 = True.
Proof. exact (EQ_MP (@lem5451119) (@lem5451117)). Qed.
Lemma lem5451121 : term617 = True.
Proof. exact (TRANS (@lem5451116) (@lem5451120)). Qed.
Lemma lem5451122 : True = term617.
Proof. exact (SYM (@lem5451121)). Qed.
Lemma lem5451123 : term617.
Proof. exact (EQ_MP (@lem5451122) (@lem0)). Qed.
Lemma lem5451124 : term655.
Proof. exact (@lem5451113 (@lem5451123)). Qed.
Lemma lem5451126 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451127 : term617 = term623.
Proof. exact (@lem5451126 (NUMERAL 0) term193). Qed.
Lemma lem5451128 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451129 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451130 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451129 h1) (fun h1 : term623 = True => @lem5451128)). Qed.
Lemma lem5451131 : term623 = True.
Proof. exact (EQ_MP (@lem5451130) (@lem5451128)). Qed.
Lemma lem5451132 : term617 = True.
Proof. exact (TRANS (@lem5451127) (@lem5451131)). Qed.
Lemma lem5451133 : True = term617.
Proof. exact (SYM (@lem5451132)). Qed.
Lemma lem5451134 : term617.
Proof. exact (EQ_MP (@lem5451133) (@lem0)). Qed.
Lemma lem5451135 : term656.
Proof. exact (@lem5451124 (@lem5451134)). Qed.
Lemma lem5451137 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451138 : term617 = term623.
Proof. exact (@lem5451137 (NUMERAL 0) term193). Qed.
Lemma lem5451139 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451140 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451141 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451140 h1) (fun h1 : term623 = True => @lem5451139)). Qed.
Lemma lem5451142 : term623 = True.
Proof. exact (EQ_MP (@lem5451141) (@lem5451139)). Qed.
Lemma lem5451143 : term617 = True.
Proof. exact (TRANS (@lem5451138) (@lem5451142)). Qed.
Lemma lem5451144 : True = term617.
Proof. exact (SYM (@lem5451143)). Qed.
Lemma lem5451145 : term617.
Proof. exact (EQ_MP (@lem5451144) (@lem0)). Qed.
Lemma lem5451146 : term657.
Proof. exact (@lem5451135 (@lem5451145)). Qed.
Lemma lem5451148 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5451149 : term247 = term248.
Proof. exact (@lem5451148 term193 term193). Qed.
Lemma lem5451150 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451151 : term250 = term193.
Proof. exact (EQ_MP (@lem5451150) (@lem940073)). Qed.
Lemma lem5451152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451153 : term248 = term192.
Proof. exact (MK_COMB (@lem5451152) (@lem5451151)). Qed.
Lemma lem5451154 : term247 = term192.
Proof. exact (TRANS (@lem5451149) (@lem5451153)). Qed.
Lemma lem5451156 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5451157 : term273 = term278.
Proof. exact (@lem5451156 term193 term193). Qed.
Lemma lem5451158 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451159 : term250 = term193.
Proof. exact (EQ_MP (@lem5451158) (@lem940073)). Qed.
Lemma lem5451160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451161 : term248 = term192.
Proof. exact (MK_COMB (@lem5451160) (@lem5451159)). Qed.
Lemma lem5451162 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5451163 : term278 = term238.
Proof. exact (MK_COMB (@lem5451162) (@lem5451161)). Qed.
Lemma lem5451164 : term273 = term238.
Proof. exact (TRANS (@lem5451157) (@lem5451163)). Qed.
Lemma lem5451165 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5451166 : term658 = term650.
Proof. exact (MK_COMB (@lem5451165) (@lem5451164)). Qed.
Lemma lem5451167 : term659 = term652.
Proof. exact (MK_COMB (@lem5451166) (@lem5451154)). Qed.
Lemma lem5451169 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5451170 : term652 = term170.
Proof. exact (@lem5451169 term193). Qed.
Lemma lem5451171 : term659 = term170.
Proof. exact (TRANS (@lem5451167) (@lem5451170)). Qed.
Lemma lem5451172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5451173 : term661 = term662.
Proof. exact (MK_COMB (@lem5451172) (@lem5451171)). Qed.
Lemma lem5451174 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5451175 : term663 = term628.
Proof. exact (MK_COMB (@lem5451173) (@lem5451174)). Qed.
Lemma lem5451177 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5451178 : term628 = term170.
Proof. exact (@lem5451177 term193). Qed.
Lemma lem5451179 : term663 = term170.
Proof. exact (TRANS (@lem5451175) (@lem5451178)). Qed.
Lemma lem5451181 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5451182 : term247 = term248.
Proof. exact (@lem5451181 term193 term193). Qed.
Lemma lem5451183 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451184 : term250 = term193.
Proof. exact (EQ_MP (@lem5451183) (@lem940073)). Qed.
Lemma lem5451185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451186 : term248 = term192.
Proof. exact (MK_COMB (@lem5451185) (@lem5451184)). Qed.
Lemma lem5451187 : term247 = term192.
Proof. exact (TRANS (@lem5451182) (@lem5451186)). Qed.
Lemma lem5451188 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5451189 : term664 = term628.
Proof. exact (MK_COMB (@lem5451188) (@lem5451187)). Qed.
Lemma lem5451191 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5451192 : term628 = term170.
Proof. exact (@lem5451191 term193). Qed.
Lemma lem5451193 : term664 = term170.
Proof. exact (TRANS (@lem5451189) (@lem5451192)). Qed.
Lemma lem5451194 : term170 = term664.
Proof. exact (SYM (@lem5451193)). Qed.
Lemma lem5451195 : term663 = term664.
Proof. exact (TRANS (@lem5451179) (@lem5451194)). Qed.
Lemma lem5451196 : term653 = term235.
Proof. exact (@lem5451146 (@lem5451195)). Qed.
Lemma lem5451197 : term652 = term235.
Proof. exact (TRANS (@lem5451112) (@lem5451196)). Qed.
Lemma lem5451199 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5451200 : term235 = term170.
Proof. exact (@lem5451199 term170). Qed.
Lemma lem5451201 : term652 = term170.
Proof. exact (TRANS (@lem5451197) (@lem5451200)). Qed.
Lemma lem5451202 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5451203 : term665 = term662.
Proof. exact (MK_COMB (@lem5451202) (@lem5451201)). Qed.
Lemma lem5451204 (_70518 : int) : (real_of_int _70518) = (real_of_int _70518).
Proof. exact (eq_refl (real_of_int _70518)). Qed.
Lemma lem5451205 (_70518 : int) : (term649 _70518) = (term666 _70518).
Proof. exact (MK_COMB (@lem5451203) (@lem5451204 _70518)). Qed.
Lemma lem5451206 (_70518 : int) : (term648 _70518) = (term666 _70518).
Proof. exact (TRANS (@lem5451103 _70518) (@lem5451205 _70518)). Qed.
Lemma lem5451207 (_70518 : int) : (term666 _70518) = term170.
Proof. exact (@lem1982719 (real_of_int _70518)). Qed.
Lemma lem5451208 (_70518 : int) : (term648 _70518) = term170.
Proof. exact (TRANS (@lem5451206 _70518) (@lem5451207 _70518)). Qed.
Lemma lem5451209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5451210 (_70518 : int) : (term667 _70518) = term668.
Proof. exact (MK_COMB (@lem5451209) (@lem5451208 _70518)). Qed.
Lemma lem5451211 (_70521 : int) : (term718 _70521) = (term670 _70521).
Proof. exact (@lem1982759 (term285 _70521) (real_of_int _70521) term238). Qed.
Lemma lem5451212 (_70521 : int) : (term671 _70521) = (term649 _70521).
Proof. exact (@lem1982713 term238 (real_of_int _70521)). Qed.
Lemma lem5451214 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5451215 : term192 = term272.
Proof. exact (@lem5451214 term193). Qed.
Lemma lem5451217 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5451218 : term238 = term239.
Proof. exact (@lem5451217 term193). Qed.
Lemma lem5451219 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5451220 : term650 = term651.
Proof. exact (MK_COMB (@lem5451219) (@lem5451218)). Qed.
Lemma lem5451221 : term652 = term653.
Proof. exact (MK_COMB (@lem5451220) (@lem5451215)). Qed.
Lemma lem5451222 : term654.
Proof. exact (@lem1981473 term238 term192 term192 term192 term170 term192). Qed.
Lemma lem5451224 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451225 : term617 = term623.
Proof. exact (@lem5451224 (NUMERAL 0) term193). Qed.
Lemma lem5451226 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451227 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451228 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451227 h1) (fun h1 : term623 = True => @lem5451226)). Qed.
Lemma lem5451229 : term623 = True.
Proof. exact (EQ_MP (@lem5451228) (@lem5451226)). Qed.
Lemma lem5451230 : term617 = True.
Proof. exact (TRANS (@lem5451225) (@lem5451229)). Qed.
Lemma lem5451231 : True = term617.
Proof. exact (SYM (@lem5451230)). Qed.
Lemma lem5451232 : term617.
Proof. exact (EQ_MP (@lem5451231) (@lem0)). Qed.
Lemma lem5451233 : term655.
Proof. exact (@lem5451222 (@lem5451232)). Qed.
Lemma lem5451235 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451236 : term617 = term623.
Proof. exact (@lem5451235 (NUMERAL 0) term193). Qed.
Lemma lem5451237 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451238 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451239 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451238 h1) (fun h1 : term623 = True => @lem5451237)). Qed.
Lemma lem5451240 : term623 = True.
Proof. exact (EQ_MP (@lem5451239) (@lem5451237)). Qed.
Lemma lem5451241 : term617 = True.
Proof. exact (TRANS (@lem5451236) (@lem5451240)). Qed.
Lemma lem5451242 : True = term617.
Proof. exact (SYM (@lem5451241)). Qed.
Lemma lem5451243 : term617.
Proof. exact (EQ_MP (@lem5451242) (@lem0)). Qed.
Lemma lem5451244 : term656.
Proof. exact (@lem5451233 (@lem5451243)). Qed.
Lemma lem5451246 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451247 : term617 = term623.
Proof. exact (@lem5451246 (NUMERAL 0) term193). Qed.
Lemma lem5451248 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451249 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451250 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451249 h1) (fun h1 : term623 = True => @lem5451248)). Qed.
Lemma lem5451251 : term623 = True.
Proof. exact (EQ_MP (@lem5451250) (@lem5451248)). Qed.
Lemma lem5451252 : term617 = True.
Proof. exact (TRANS (@lem5451247) (@lem5451251)). Qed.
Lemma lem5451253 : True = term617.
Proof. exact (SYM (@lem5451252)). Qed.
Lemma lem5451254 : term617.
Proof. exact (EQ_MP (@lem5451253) (@lem0)). Qed.
Lemma lem5451255 : term657.
Proof. exact (@lem5451244 (@lem5451254)). Qed.
Lemma lem5451257 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5451258 : term247 = term248.
Proof. exact (@lem5451257 term193 term193). Qed.
Lemma lem5451259 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451260 : term250 = term193.
Proof. exact (EQ_MP (@lem5451259) (@lem940073)). Qed.
Lemma lem5451261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451262 : term248 = term192.
Proof. exact (MK_COMB (@lem5451261) (@lem5451260)). Qed.
Lemma lem5451263 : term247 = term192.
Proof. exact (TRANS (@lem5451258) (@lem5451262)). Qed.
Lemma lem5451265 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5451266 : term273 = term278.
Proof. exact (@lem5451265 term193 term193). Qed.
Lemma lem5451267 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451268 : term250 = term193.
Proof. exact (EQ_MP (@lem5451267) (@lem940073)). Qed.
Lemma lem5451269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451270 : term248 = term192.
Proof. exact (MK_COMB (@lem5451269) (@lem5451268)). Qed.
Lemma lem5451271 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5451272 : term278 = term238.
Proof. exact (MK_COMB (@lem5451271) (@lem5451270)). Qed.
Lemma lem5451273 : term273 = term238.
Proof. exact (TRANS (@lem5451266) (@lem5451272)). Qed.
Lemma lem5451274 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5451275 : term658 = term650.
Proof. exact (MK_COMB (@lem5451274) (@lem5451273)). Qed.
Lemma lem5451276 : term659 = term652.
Proof. exact (MK_COMB (@lem5451275) (@lem5451263)). Qed.
Lemma lem5451278 (m : nat) : (term660 m) = term170.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5451279 : term652 = term170.
Proof. exact (@lem5451278 term193). Qed.
Lemma lem5451280 : term659 = term170.
Proof. exact (TRANS (@lem5451276) (@lem5451279)). Qed.
Lemma lem5451281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5451282 : term661 = term662.
Proof. exact (MK_COMB (@lem5451281) (@lem5451280)). Qed.
Lemma lem5451283 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem5451284 : term663 = term628.
Proof. exact (MK_COMB (@lem5451282) (@lem5451283)). Qed.
Lemma lem5451286 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5451287 : term628 = term170.
Proof. exact (@lem5451286 term193). Qed.
Lemma lem5451288 : term663 = term170.
Proof. exact (TRANS (@lem5451284) (@lem5451287)). Qed.
Lemma lem5451290 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5451291 : term247 = term248.
Proof. exact (@lem5451290 term193 term193). Qed.
Lemma lem5451292 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451293 : term250 = term193.
Proof. exact (EQ_MP (@lem5451292) (@lem940073)). Qed.
Lemma lem5451294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451295 : term248 = term192.
Proof. exact (MK_COMB (@lem5451294) (@lem5451293)). Qed.
Lemma lem5451296 : term247 = term192.
Proof. exact (TRANS (@lem5451291) (@lem5451295)). Qed.
Lemma lem5451297 : term662 = term662.
Proof. exact (eq_refl term662). Qed.
Lemma lem5451298 : term664 = term628.
Proof. exact (MK_COMB (@lem5451297) (@lem5451296)). Qed.
Lemma lem5451300 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5451301 : term628 = term170.
Proof. exact (@lem5451300 term193). Qed.
Lemma lem5451302 : term664 = term170.
Proof. exact (TRANS (@lem5451298) (@lem5451301)). Qed.
Lemma lem5451303 : term170 = term664.
Proof. exact (SYM (@lem5451302)). Qed.
Lemma lem5451304 : term663 = term664.
Proof. exact (TRANS (@lem5451288) (@lem5451303)). Qed.
Lemma lem5451305 : term653 = term235.
Proof. exact (@lem5451255 (@lem5451304)). Qed.
Lemma lem5451306 : term652 = term235.
Proof. exact (TRANS (@lem5451221) (@lem5451305)). Qed.
Lemma lem5451308 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5451309 : term235 = term170.
Proof. exact (@lem5451308 term170). Qed.
Lemma lem5451310 : term652 = term170.
Proof. exact (TRANS (@lem5451306) (@lem5451309)). Qed.
Lemma lem5451311 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5451312 : term665 = term662.
Proof. exact (MK_COMB (@lem5451311) (@lem5451310)). Qed.
Lemma lem5451313 (_70521 : int) : (real_of_int _70521) = (real_of_int _70521).
Proof. exact (eq_refl (real_of_int _70521)). Qed.
Lemma lem5451314 (_70521 : int) : (term649 _70521) = (term666 _70521).
Proof. exact (MK_COMB (@lem5451312) (@lem5451313 _70521)). Qed.
Lemma lem5451315 (_70521 : int) : (term671 _70521) = (term666 _70521).
Proof. exact (TRANS (@lem5451212 _70521) (@lem5451314 _70521)). Qed.
Lemma lem5451316 (_70521 : int) : (term666 _70521) = term170.
Proof. exact (@lem1982719 (real_of_int _70521)). Qed.
Lemma lem5451317 (_70521 : int) : (term671 _70521) = term170.
Proof. exact (TRANS (@lem5451315 _70521) (@lem5451316 _70521)). Qed.
Lemma lem5451318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5451319 (_70521 : int) : (term672 _70521) = term668.
Proof. exact (MK_COMB (@lem5451318) (@lem5451317 _70521)). Qed.
Lemma lem5451320 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5451321 (_70521 : int) : (term670 _70521) = term673.
Proof. exact (MK_COMB (@lem5451319 _70521) (@lem5451320)). Qed.
Lemma lem5451322 (_70521 : int) : (term718 _70521) = term673.
Proof. exact (TRANS (@lem5451211 _70521) (@lem5451321 _70521)). Qed.
Lemma lem5451323 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5451324 (_70521 : int) : (term718 _70521) = term238.
Proof. exact (TRANS (@lem5451322 _70521) (@lem5451323)). Qed.
Lemma lem5451325 (_70518 : int) (_70521 : int) : (term717 _70518 _70521) = term673.
Proof. exact (MK_COMB (@lem5451210 _70518) (@lem5451324 _70521)). Qed.
Lemma lem5451326 (_70518 : int) (_70521 : int) : (term716 _70518 _70521) = term673.
Proof. exact (TRANS (@lem5451102 _70518 _70521) (@lem5451325 _70518 _70521)). Qed.
Lemma lem5451327 : term673 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem5451328 (_70518 : int) (_70521 : int) : (term716 _70518 _70521) = term238.
Proof. exact (TRANS (@lem5451326 _70518 _70521) (@lem5451327)). Qed.
Lemma lem5451329 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5451330 (_70518 : int) (_70521 : int) : (term719 _70518 _70521) = term675.
Proof. exact (MK_COMB (@lem5451329) (@lem5451328 _70518 _70521)). Qed.
Lemma lem5451331 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5451332 (_70518 : int) (_70521 : int) : (term715 _70518 _70521) = term676.
Proof. exact (MK_COMB (@lem5451330 _70518 _70521) (@lem5451331)). Qed.
Lemma lem5451333 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : term676.
Proof. exact (EQ_MP (@lem5451332 _70518 _70521) (@lem5451101 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451335 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5451336 : term676 = term677.
Proof. exact (@lem5451335 term170 term238). Qed.
Lemma lem5451338 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5451339 : term238 = term239.
Proof. exact (@lem5451338 term193). Qed.
Lemma lem5451341 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5451342 : term170 = term235.
Proof. exact (@lem5451341 (NUMERAL 0)). Qed.
Lemma lem5451343 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5451344 : term172 = term678.
Proof. exact (MK_COMB (@lem5451343) (@lem5451342)). Qed.
Lemma lem5451345 : term677 = term679.
Proof. exact (MK_COMB (@lem5451344) (@lem5451339)). Qed.
Lemma lem5451346 : term680.
Proof. exact (@lem1980026 term170 term192 term238 term192). Qed.
Lemma lem5451348 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451349 : term617 = term623.
Proof. exact (@lem5451348 (NUMERAL 0) term193). Qed.
Lemma lem5451350 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451351 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451352 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451351 h1) (fun h1 : term623 = True => @lem5451350)). Qed.
Lemma lem5451353 : term623 = True.
Proof. exact (EQ_MP (@lem5451352) (@lem5451350)). Qed.
Lemma lem5451354 : term617 = True.
Proof. exact (TRANS (@lem5451349) (@lem5451353)). Qed.
Lemma lem5451355 : True = term617.
Proof. exact (SYM (@lem5451354)). Qed.
Lemma lem5451356 : term617.
Proof. exact (EQ_MP (@lem5451355) (@lem0)). Qed.
Lemma lem5451357 : term681.
Proof. exact (@lem5451346 (@lem5451356)). Qed.
Lemma lem5451359 (m : nat) (n : nat) : (term622 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5451360 : term617 = term623.
Proof. exact (@lem5451359 (NUMERAL 0) term193). Qed.
Lemma lem5451361 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451362 (h1 : term624 = (BIT1 0)) : term623 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5451363 : (term624 = (BIT1 0)) = (term623 = True).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451362 h1) (fun h1 : term623 = True => @lem5451361)). Qed.
Lemma lem5451364 : term623 = True.
Proof. exact (EQ_MP (@lem5451363) (@lem5451361)). Qed.
Lemma lem5451365 : term617 = True.
Proof. exact (TRANS (@lem5451360) (@lem5451364)). Qed.
Lemma lem5451366 : True = term617.
Proof. exact (SYM (@lem5451365)). Qed.
Lemma lem5451367 : term617.
Proof. exact (EQ_MP (@lem5451366) (@lem0)). Qed.
Lemma lem5451368 : term679 = term682.
Proof. exact (@lem5451357 (@lem5451367)). Qed.
Lemma lem5451370 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5451371 : term273 = term278.
Proof. exact (@lem5451370 term193 term193). Qed.
Lemma lem5451372 : (term249 = (BIT1 0)) = (term250 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5451373 : term250 = term193.
Proof. exact (EQ_MP (@lem5451372) (@lem940073)). Qed.
Lemma lem5451374 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5451375 : term248 = term192.
Proof. exact (MK_COMB (@lem5451374) (@lem5451373)). Qed.
Lemma lem5451376 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5451377 : term278 = term238.
Proof. exact (MK_COMB (@lem5451376) (@lem5451375)). Qed.
Lemma lem5451378 : term273 = term238.
Proof. exact (TRANS (@lem5451371) (@lem5451377)). Qed.
Lemma lem5451380 (x : nat) : (term627 x) = term170.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5451381 : term628 = term170.
Proof. exact (@lem5451380 term193). Qed.
Lemma lem5451382 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5451383 : term683 = term172.
Proof. exact (MK_COMB (@lem5451382) (@lem5451381)). Qed.
Lemma lem5451384 : term682 = term677.
Proof. exact (MK_COMB (@lem5451383) (@lem5451378)). Qed.
Lemma lem5451386 (m : nat) (n : nat) : (term684 m n) = (term685 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5451387 : term677 = term686.
Proof. exact (@lem5451386 (NUMERAL 0) term193). Qed.
Lemma lem5451388 : term624 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5451389 (h1 : term624 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5451390 : (term624 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term624 = (BIT1 0) => @lem5451389 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem5451388)). Qed.
Lemma lem5451391 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5451390) (@lem5451388)). Qed.
Lemma lem5451392 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5451393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5451394 : term687 = (and True).
Proof. exact (MK_COMB (@lem5451393) (@lem5451392)). Qed.
Lemma lem5451395 : term686 = (True /\ False).
Proof. exact (MK_COMB (@lem5451394) (@lem5451391)). Qed.
Lemma lem5451397 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5451398 : term686 = False.
Proof. exact (TRANS (@lem5451395) (@lem5451397)). Qed.
Lemma lem5451399 : term677 = False.
Proof. exact (TRANS (@lem5451387) (@lem5451398)). Qed.
Lemma lem5451400 : term682 = False.
Proof. exact (TRANS (@lem5451384) (@lem5451399)). Qed.
Lemma lem5451401 : term679 = False.
Proof. exact (TRANS (@lem5451368) (@lem5451400)). Qed.
Lemma lem5451402 : term677 = False.
Proof. exact (TRANS (@lem5451345) (@lem5451401)). Qed.
Lemma lem5451403 : term676 = False.
Proof. exact (TRANS (@lem5451336) (@lem5451402)). Qed.
Lemma lem5451404 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term567 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5451403) (@lem5451333 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451405 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term569 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5450450 _70518 _70519 _70520 _70521 h1) (fun h0 : term561 _70518 _70519 _70520 _70521 => @lem5450927 _70518 _70519 _70520 _70521 h0) (fun h0 : term567 _70518 _70519 _70520 _70521 => @lem5451404 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5451406 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term613 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5449493 _70518 _70519 _70520 _70521 h1) (fun h0 : term611 _70518 _70519 _70520 _70521 => @lem5450449 _70518 _70519 _70520 _70521 h0) (fun h0 : term569 _70518 _70519 _70520 _70521 => @lem5451405 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5451407 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term615 _70518 _70519 _70520 _70521) : False.
Proof. exact (or_elim (@lem5447594 _70518 _70519 _70520 _70521 h1) (fun h0 : term473 _70518 _70519 _70520 _70521 => @lem5449492 _70518 _70519 _70520 _70521 h0) (fun h0 : term613 _70518 _70519 _70520 _70521 => @lem5451406 _70518 _70519 _70520 _70521 h0)). Qed.
Lemma lem5451408 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term423 _70518 _70519 _70520 _70521) : term423 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5451409 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term423 _70518 _70519 _70520 _70521) : term615 _70518 _70519 _70520 _70521.
Proof. exact (EQ_MP (@lem5447593 _70518 _70519 _70520 _70521) (@lem5451408 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451410 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term423 _70518 _70519 _70520 _70521) : (term615 _70518 _70519 _70520 _70521) = False.
Proof. exact (prop_ext (fun h2 : term615 _70518 _70519 _70520 _70521 => @lem5451407 _70518 _70519 _70520 _70521 h2) (fun h2 : False => @lem5451409 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451411 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term423 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5451410 _70518 _70519 _70520 _70521 h1) (@lem5451409 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451412 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term230 _70518 _70519 _70520 _70521) : term230 _70518 _70519 _70520 _70521.
Proof. exact (h1). Qed.
Lemma lem5451413 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term230 _70518 _70519 _70520 _70521) : term423 _70518 _70519 _70520 _70521.
Proof. exact (EQ_MP (@lem5445685 _70518 _70519 _70520 _70521) (@lem5451412 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451414 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term230 _70518 _70519 _70520 _70521) : (term423 _70518 _70519 _70520 _70521) = False.
Proof. exact (prop_ext (fun h2 : term423 _70518 _70519 _70520 _70521 => @lem5451411 _70518 _70519 _70520 _70521 h2) (fun h2 : False => @lem5451413 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451415 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) (h1 : term230 _70518 _70519 _70520 _70521) : False.
Proof. exact (EQ_MP (@lem5451414 _70518 _70519 _70520 _70521 h1) (@lem5451413 _70518 _70519 _70520 _70521 h1)). Qed.
Lemma lem5451416 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : term720 _70518 _70519 _70520 _70521.
Proof. exact (fun h0 : term230 _70518 _70519 _70520 _70521 => @lem5451415 _70518 _70519 _70520 _70521 h0). Qed.
Lemma lem5451417 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : term721 _70518 _70519 _70520 _70521.
Proof. exact (@lem1386578 (term722 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5451420 (_70518 : int) (_70519 : int) (_70520 : int) (_70521 : int) : term722 _70518 _70519 _70520 _70521.
Proof. exact (@lem5451417 _70518 _70519 _70520 _70521 (@lem5451416 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5451421 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term228 _70518 _70519 _70520 _70521) = (term163 _70519 _70518 _70521 _70520).
Proof. exact (SYM (@lem5444671 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5451422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5451423 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : (term722 _70518 _70519 _70520 _70521) = (term104 _70519 _70518 _70521 _70520).
Proof. exact (MK_COMB (@lem5451422) (@lem5451421 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5451424 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : term104 _70519 _70518 _70521 _70520.
Proof. exact (EQ_MP (@lem5451423 _70519 _70518 _70521 _70520) (@lem5451420 _70518 _70519 _70520 _70521)). Qed.
Lemma lem5451425 (_70519 : int) (_70518 : int) (_70521 : int) (_70520 : int) : term105 _70519 _70518 _70521 _70520.
Proof. exact (EQ_MP (@lem5444238 _70519 _70518 _70521 _70520) (@lem5451424 _70519 _70518 _70521 _70520)). Qed.
Lemma lem5451426 (n : nat) (m : nat) (q : nat) (p : nat) : term723 n m q p.
Proof. exact (@lem5451425 (int_of_num n) (int_of_num m) (int_of_num q) (int_of_num p)). Qed.
Lemma lem5451427 (n : nat) (m : nat) (q : nat) (p : nat) : term724 n m q p.
Proof. exact (@lem5451426 n m q p (@lem5444228 m)). Qed.
Lemma lem5451428 (n : nat) (m : nat) (q : nat) (p : nat) : term725 n m q p.
Proof. exact (@lem5451427 n m q p (@lem5444231 n)). Qed.
Lemma lem5451429 (n : nat) (m : nat) (q : nat) (p : nat) : term726 n m q p.
Proof. exact (@lem5451428 n m q p (@lem5444234 p)). Qed.
Lemma lem5451430 (n : nat) (m : nat) (q : nat) (p : nat) : term93 n m q p.
Proof. exact (@lem5451429 n m q p (@lem5444237 q)). Qed.
Lemma lem5451431 (n : nat) (m : nat) (p : nat) : term95 n m p.
Proof. exact (fun q : nat => @lem5451430 n m q p). Qed.
Lemma lem5451432 (n : nat) (m : nat) : term97 n m.
Proof. exact (fun p : nat => @lem5451431 n m p). Qed.
Lemma lem5451433 (m : nat) : term99 m.
Proof. exact (fun n : nat => @lem5451432 n m). Qed.
Lemma lem5451434 : term101.
Proof. exact (fun m : nat => @lem5451433 m). Qed.
Lemma lem5451435 : term101 = term37.
Proof. exact (SYM (@lem5444225)). Qed.
Lemma lem5451436 : term37.
Proof. exact (EQ_MP (@lem5451435) (@lem5451434)). Qed.
Lemma lem5451437 : term37 = (term37 = True).
Proof. exact (@lem7 term37). Qed.
Lemma lem5451438 : term37 = True.
Proof. exact (EQ_MP (@lem5451437) (@lem5451436)). Qed.
Lemma lem5451439 : True = term37.
Proof. exact (SYM (@lem5451438)). Qed.
Lemma lem5451440 : term37.
Proof. exact (EQ_MP (@lem5451439) (@lem0)). Qed.
Lemma lem5451441 : term36.
Proof. exact (EQ_MP (@lem5443856) (@lem5451440)). Qed.
