Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_RDIV_EQ_term_abbrevs.
Require Import ADD1_spec.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import DIV_MUL_LE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LET_TRANS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import LT_ADD_LCANCEL_spec.
Require Import LT_MULT_LCANCEL_spec.
Require Import LT_SUC_LE_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm19490_spec.
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
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem186866 (m : nat) (h1 : (S m) = (term0 m)) : (S m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem186867 (m : nat) (h1 : (S m) = (term0 m)) : (term0 m) = (S m).
Proof. exact (SYM (@lem186866 m h1)). Qed.
Lemma lem186868 (m : nat) (h1 : (term0 m) = (S m)) : (term0 m) = (S m).
Proof. exact (h1). Qed.
Lemma lem186869 (m : nat) (h1 : (term0 m) = (S m)) : (S m) = (term0 m).
Proof. exact (SYM (@lem186868 m h1)). Qed.
Lemma lem186870 (m : nat) : ((S m) = (term0 m)) = ((term0 m) = (S m)).
Proof. exact (prop_ext (fun h1 : (S m) = (term0 m) => @lem186867 m h1) (fun h1 : (term0 m) = (S m) => @lem186869 m h1)). Qed.
Lemma lem186871 : term1 = term2.
Proof. exact (fun_ext (fun m : nat => @lem186870 m)). Qed.
Lemma lem186872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186873 : term3 = term4.
Proof. exact (MK_COMB (@lem186872) (@lem186871)). Qed.
Lemma lem186874 : term4.
Proof. exact (EQ_MP (@lem186873) (@lem80621)). Qed.
Lemma lem186885 (m : nat) : term5 m.
Proof. exact (@lem101108 m). Qed.
Lemma lem186886 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem186887 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem186886 m) (@lem186885 m)). Qed.
Lemma lem186888 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem186887 m n). Qed.
Lemma lem186889 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem186890 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem186889 m n) (@lem186888 m n)). Qed.
Lemma lem186891 (m : nat) (n : nat) (p : nat) : term9 m n p.
Proof. exact (@lem186890 m n p). Qed.
Lemma lem186892 (m : nat) (n : nat) (p : nat) : (term9 m n p) = ((term10 n m p) = (Peano.lt n p)).
Proof. exact (eq_refl (term9 m n p)). Qed.
Lemma lem186894 : term11.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem186895 : term12.
Proof. exact (proj2 (@lem186894)). Qed.
Lemma lem186896 : term13.
Proof. exact (proj2 (@lem186895)). Qed.
Lemma lem186912 : term14.
Proof. exact (proj1 (@lem186896)). Qed.
Lemma lem186913 (m : nat) : term15 m.
Proof. exact (@lem186912 m). Qed.
Lemma lem186914 (m : nat) : (term15 m) = ((term16 m) = m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem186928 (m : nat) : term17 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem186929 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem186930 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem186929 m) (@lem186928 m)). Qed.
Lemma lem186931 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem186930 m n). Qed.
Lemma lem186932 (n : nat) (m : nat) : (term19 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem186934 (m : nat) : term20 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem186935 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem186936 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem186935 m) (@lem186934 m)). Qed.
Lemma lem186937 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem186936 m n). Qed.
Lemma lem186938 (n : nat) (m : nat) : (term22 m n) = (term23 n m).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem186939 (n : nat) (m : nat) : term23 n m.
Proof. exact (EQ_MP (@lem186938 n m) (@lem186937 m n)). Qed.
Lemma lem186940 (n : nat) (m : nat) (p : nat) : term24 n m p.
Proof. exact (@lem186939 n m p). Qed.
Lemma lem186941 (n : nat) (m : nat) (p : nat) : (term24 n m p) = ((term25 m n p) = (term26 n m p)).
Proof. exact (eq_refl (term24 n m p)). Qed.
Lemma lem186953 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem186954 (m : nat) (h1 : term27) : term28 m.
Proof. exact (@lem186953 h1 m). Qed.
Lemma lem186955 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem186956 (m : nat) (h1 : term27) : term29 m.
Proof. exact (EQ_MP (@lem186955 m) (@lem186954 m h1)). Qed.
Lemma lem186957 (m : nat) (n : nat) (h1 : term27) : term30 m n.
Proof. exact (@lem186956 m h1 n). Qed.
Lemma lem186958 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem186959 (n : nat) (m : nat) (h1 : term27) : term31 n m.
Proof. exact (EQ_MP (@lem186958 n m) (@lem186957 m n h1)). Qed.
Lemma lem186960 (n : nat) (m : nat) (p : nat) (h1 : term27) : term32 n m p.
Proof. exact (@lem186959 n m h1 p). Qed.
Lemma lem186961 (n : nat) (m : nat) (p : nat) : (term32 n m p) = (term33 n m p).
Proof. exact (eq_refl (term32 n m p)). Qed.
Lemma lem186962 (n : nat) (m : nat) (p : nat) (h1 : term27) : term33 n m p.
Proof. exact (EQ_MP (@lem186961 n m p) (@lem186960 n m p h1)). Qed.
Lemma lem186963 (m : nat) (n : nat) (p : nat) (h1 : term34 m n p) : term34 m n p.
Proof. exact (h1). Qed.
Lemma lem186964 (m : nat) (n : nat) (p : nat) (h1 : term27) (h2 : term34 m n p) : Peano.lt m p.
Proof. exact (@lem186962 n m p h1 (@lem186963 m n p h2)). Qed.
Lemma lem186965 (m : nat) (n : nat) (p : nat) (h1 : term34 m n p) : term35 m p.
Proof. exact (fun h0 : term27 => @lem186964 m n p h0 h1). Qed.
Lemma lem186966 (m : nat) (p : nat) (h1 : term36 m p) : term36 m p.
Proof. exact (h1). Qed.
Lemma lem186967 (m : nat) (p : nat) (h1 : term36 m p) : term35 m p.
Proof. exact (ex_elim (@lem186966 m p h1) (fun n : nat => fun h0 : term37 m p n => @lem186965 m n p h0)). Qed.
Lemma lem186968 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem186969 (m : nat) (p : nat) (h1 : term27) (h2 : term36 m p) : Peano.lt m p.
Proof. exact (@lem186967 m p h2 (@lem186968 h1)). Qed.
Lemma lem186970 (m : nat) (p : nat) (h1 : term27) : term38 m p.
Proof. exact (fun h0 : term36 m p => @lem186969 m p h1 h0). Qed.
Lemma lem186971 (m : nat) (h1 : term27) : term39 m.
Proof. exact (fun p : nat => @lem186970 m p h1). Qed.
Lemma lem186972 (h1 : term27) : term40.
Proof. exact (fun m : nat => @lem186971 m h1). Qed.
Lemma lem186973 : term41.
Proof. exact (fun h0 : term27 => @lem186972 h0). Qed.
Lemma lem186974 : term40.
Proof. exact (@lem186973 (@lem95173)). Qed.
Lemma lem186975 (m : nat) : term42 m.
Proof. exact (@lem186974 m). Qed.
Lemma lem186976 (m : nat) : (term42 m) = (term39 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem186977 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem186976 m) (@lem186975 m)). Qed.
Lemma lem186978 (m : nat) (p : nat) : term43 m p.
Proof. exact (@lem186977 m p). Qed.
Lemma lem186979 (m : nat) (p : nat) : (term43 m p) = (term38 m p).
Proof. exact (eq_refl (term43 m p)). Qed.
Lemma lem186981 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem186982 (m : nat) (h1 : term44) : term45 m.
Proof. exact (@lem186981 h1 m). Qed.
Lemma lem186983 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem186984 (m : nat) (h1 : term44) : term46 m.
Proof. exact (EQ_MP (@lem186983 m) (@lem186982 m h1)). Qed.
Lemma lem186985 (m : nat) (n : nat) (h1 : term44) : term47 m n.
Proof. exact (@lem186984 m h1 n). Qed.
Lemma lem186986 (n : nat) (m : nat) : (term47 m n) = (term48 n m).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem186987 (n : nat) (m : nat) (h1 : term44) : term48 n m.
Proof. exact (EQ_MP (@lem186986 n m) (@lem186985 m n h1)). Qed.
Lemma lem186988 (n : nat) (m : nat) (p : nat) (h1 : term44) : term49 n m p.
Proof. exact (@lem186987 n m h1 p). Qed.
Lemma lem186989 (n : nat) (m : nat) (p : nat) : (term49 n m p) = (term50 n m p).
Proof. exact (eq_refl (term49 n m p)). Qed.
Lemma lem186990 (n : nat) (m : nat) (p : nat) (h1 : term44) : term50 n m p.
Proof. exact (EQ_MP (@lem186989 n m p) (@lem186988 n m p h1)). Qed.
Lemma lem186991 (m : nat) (n : nat) (p : nat) (h1 : term51 m n p) : term51 m n p.
Proof. exact (h1). Qed.
Lemma lem186992 (m : nat) (n : nat) (p : nat) (h1 : term44) (h2 : term51 m n p) : Peano.le m p.
Proof. exact (@lem186990 n m p h1 (@lem186991 m n p h2)). Qed.
Lemma lem186993 (m : nat) (n : nat) (p : nat) (h1 : term51 m n p) : term52 m p.
Proof. exact (fun h0 : term44 => @lem186992 m n p h0 h1). Qed.
Lemma lem186994 (m : nat) (p : nat) (h1 : term53 m p) : term53 m p.
Proof. exact (h1). Qed.
Lemma lem186995 (m : nat) (p : nat) (h1 : term53 m p) : term52 m p.
Proof. exact (ex_elim (@lem186994 m p h1) (fun n : nat => fun h0 : term54 m p n => @lem186993 m n p h0)). Qed.
Lemma lem186996 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem186997 (m : nat) (p : nat) (h1 : term44) (h2 : term53 m p) : Peano.le m p.
Proof. exact (@lem186995 m p h2 (@lem186996 h1)). Qed.
Lemma lem186998 (m : nat) (p : nat) (h1 : term44) : term55 m p.
Proof. exact (fun h0 : term53 m p => @lem186997 m p h1 h0). Qed.
Lemma lem186999 (m : nat) (h1 : term44) : term56 m.
Proof. exact (fun p : nat => @lem186998 m p h1). Qed.
Lemma lem187000 (h1 : term44) : term57.
Proof. exact (fun m : nat => @lem186999 m h1). Qed.
Lemma lem187001 : term58.
Proof. exact (fun h0 : term44 => @lem187000 h0). Qed.
Lemma lem187002 : term57.
Proof. exact (@lem187001 (@lem93743)). Qed.
Lemma lem187003 (m : nat) : term59 m.
Proof. exact (@lem187002 m). Qed.
Lemma lem187004 (m : nat) : (term59 m) = (term56 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem187005 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem187004 m) (@lem187003 m)). Qed.
Lemma lem187006 (m : nat) (p : nat) : term60 m p.
Proof. exact (@lem187005 m p). Qed.
Lemma lem187007 (m : nat) (p : nat) : (term60 m p) = (term55 m p).
Proof. exact (eq_refl (term60 m p)). Qed.
Lemma lem187009 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem187010 (n : nat) (b : nat) (a : nat) (h1 : term62 n b a) : term62 n b a.
Proof. exact (h1). Qed.
Lemma lem187011 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (h1). Qed.
Lemma lem187013 (m : nat) (p : nat) : term55 m p.
Proof. exact (EQ_MP (@lem187007 m p) (@lem187006 m p)). Qed.
Lemma lem187014 (a : nat) (n : nat) (b : nat) : term64 a n b.
Proof. exact (@lem187013 (Nat.mul a n) b). Qed.
Lemma lem187015 (m : nat) : term65 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem187016 (m : nat) : (term65 m) = (term66 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem187017 (m : nat) : term66 m.
Proof. exact (EQ_MP (@lem187016 m) (@lem187015 m)). Qed.
Lemma lem187018 (m : nat) (n : nat) : term67 m n.
Proof. exact (@lem187017 m n). Qed.
Lemma lem187019 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem187020 (m : nat) (n : nat) : term68 m n.
Proof. exact (EQ_MP (@lem187019 m n) (@lem187018 m n)). Qed.
Lemma lem187021 (m : nat) (n : nat) (p : nat) : term69 m n p.
Proof. exact (@lem187020 m n p). Qed.
Lemma lem187022 (m : nat) (n : nat) (p : nat) : (term69 m n p) = ((term70 n m p) = (term71 m n p)).
Proof. exact (eq_refl (term69 m n p)). Qed.
Lemma lem187024 (m : nat) : term72 m.
Proof. exact (@lem178720 m). Qed.
Lemma lem187025 (m : nat) : (term72 m) = (term73 m).
Proof. exact (eq_refl (term72 m)). Qed.
Lemma lem187026 (m : nat) : term73 m.
Proof. exact (EQ_MP (@lem187025 m) (@lem187024 m)). Qed.
Lemma lem187027 (m : nat) (n : nat) : term74 m n.
Proof. exact (@lem187026 m n). Qed.
Lemma lem187028 (n : nat) (m : nat) : (term74 m n) = (term75 n m).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem187029 (n : nat) (m : nat) : term75 n m.
Proof. exact (EQ_MP (@lem187028 n m) (@lem187027 m n)). Qed.
Lemma lem187030 (n : nat) (m : nat) : (term75 n m) = ((term75 n m) = True).
Proof. exact (@lem7 (term75 n m)). Qed.
Lemma lem187032 (a : nat) : term76 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem187045 (n : nat) (b : nat) (a : nat) : (term62 n b a) = ((term62 n b a) = True).
Proof. exact (@lem7 (term62 n b a)). Qed.
Lemma lem187050 (m : nat) (n : nat) (p : nat) : (term70 n m p) = (term71 m n p).
Proof. exact (EQ_MP (@lem187022 m n p) (@lem187021 m n p)). Qed.
Lemma lem187051 (n : nat) (b : nat) (a : nat) : (term77 n b a) = (term78 n b a).
Proof. exact (@lem187050 a n (Nat.div b a)). Qed.
Lemma lem187055 (a : nat) (h1 : term61 a) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem187032 a (@lem187009 a h1)). Qed.
Lemma lem187056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem187057 (a : nat) (h1 : term61 a) : (term79 a) = (or False).
Proof. exact (MK_COMB (@lem187056) (@lem187055 a h1)). Qed.
Lemma lem187059 (n : nat) (b : nat) (a : nat) (h1 : term62 n b a) : (term62 n b a) = True.
Proof. exact (EQ_MP (@lem187045 n b a) (@lem187010 n b a h1)). Qed.
Lemma lem187060 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : (term78 n b a) = (False \/ True).
Proof. exact (MK_COMB (@lem187057 a h1) (@lem187059 n b a h2)). Qed.
Lemma lem187062 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem187063 : (False \/ True) = True.
Proof. exact (@lem187062 True). Qed.
Lemma lem187064 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : (term78 n b a) = True.
Proof. exact (TRANS (@lem187060 n b a h1 h2) (@lem187063)). Qed.
Lemma lem187065 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : (term77 n b a) = True.
Proof. exact (TRANS (@lem187051 n b a) (@lem187064 n b a h1 h2)). Qed.
Lemma lem187066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem187067 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : (term80 n b a) = (and True).
Proof. exact (MK_COMB (@lem187066) (@lem187065 n b a h1 h2)). Qed.
Lemma lem187069 (n : nat) (m : nat) : (term75 n m) = True.
Proof. exact (EQ_MP (@lem187030 n m) (@lem187029 n m)). Qed.
Lemma lem187070 (a : nat) (b : nat) : (term75 a b) = True.
Proof. exact (@lem187069 a b). Qed.
Lemma lem187071 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : (term81 n a b) = (True /\ True).
Proof. exact (MK_COMB (@lem187067 n b a h1 h2) (@lem187070 a b)). Qed.
Lemma lem187073 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem187074 : (True /\ True) = True.
Proof. exact (@lem187073 True). Qed.
Lemma lem187075 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : (term81 n a b) = True.
Proof. exact (TRANS (@lem187071 n b a h1 h2) (@lem187074)). Qed.
Lemma lem187076 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : True = (term81 n a b).
Proof. exact (SYM (@lem187075 n b a h1 h2)). Qed.
Lemma lem187077 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : term81 n a b.
Proof. exact (EQ_MP (@lem187076 n b a h1 h2) (@lem0)). Qed.
Lemma lem187078 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : term82 a n b.
Proof. exact (ex_intro (term83 a n b) (term84 b a) (@lem187077 n b a h1 h2)). Qed.
Lemma lem187079 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term62 n b a) : term63 a n b.
Proof. exact (@lem187014 a n b (@lem187078 n b a h1 h2)). Qed.
Lemma lem187080 (n : nat) (b : nat) (a : nat) (h1 : term85 n b a) : term85 n b a.
Proof. exact (h1). Qed.
Lemma lem187082 (m : nat) (p : nat) : term38 m p.
Proof. exact (EQ_MP (@lem186979 m p) (@lem186978 m p)). Qed.
Lemma lem187083 (n : nat) (b : nat) (a : nat) : term86 n b a.
Proof. exact (@lem187082 (Nat.mul a n) (term87 b a)). Qed.
Lemma lem187085 (p : Prop) : p = (term88 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem187086 (n : nat) (b : nat) (a : nat) : (term89 n b a) = (term90 n b a).
Proof. exact (@lem187085 (term89 n b a)). Qed.
Lemma lem187087 (n : nat) (b : nat) (a : nat) : (term90 n b a) = (term89 n b a).
Proof. exact (SYM (@lem187086 n b a)). Qed.
Lemma lem187088 (n : nat) (b : nat) (a : nat) (h1 : term91 n b a) : term91 n b a.
Proof. exact (h1). Qed.
Lemma lem187091 (n : nat) (b : nat) (a : nat) (h1 : term92 n b a) : term92 n b a.
Proof. exact (h1). Qed.
Lemma lem187092 (n : nat) (b : nat) (a : nat) : term93 n b a.
Proof. exact (fun h0 : term92 n b a => @lem187091 n b a h0). Qed.
Lemma lem187093 (n : nat) (b : nat) (a : nat) (h1 : term93 n b a) : term93 n b a.
Proof. exact (h1). Qed.
Lemma lem187094 (n : nat) (b : nat) (a : nat) (h1 : term92 n b a) : term92 n b a.
Proof. exact (h1). Qed.
Lemma lem187095 (n : nat) (b : nat) (a : nat) (h1 : term92 n b a) (h2 : term93 n b a) : term92 n b a.
Proof. exact (@lem187093 n b a h2 (@lem187094 n b a h1)). Qed.
Lemma lem187096 (n : nat) (b : nat) (a : nat) (h1 : term92 n b a) : term94 n b a.
Proof. exact (fun h0 : term93 n b a => @lem187095 n b a h1 h0). Qed.
Lemma lem187097 (n : nat) (b : nat) (a : nat) (h1 : term93 n b a) : term93 n b a.
Proof. exact (h1). Qed.
Lemma lem187098 (n : nat) (b : nat) (a : nat) (h1 : term92 n b a) (h2 : term93 n b a) : term92 n b a.
Proof. exact (@lem187096 n b a h1 (@lem187097 n b a h2)). Qed.
Lemma lem187099 (n : nat) (b : nat) (a : nat) (h1 : term93 n b a) : term93 n b a.
Proof. exact (fun h0 : term92 n b a => @lem187098 n b a h0 h1). Qed.
Lemma lem187100 (n : nat) (b : nat) (a : nat) : term95 n b a.
Proof. exact (fun h0 : term93 n b a => @lem187099 n b a h0). Qed.
Lemma lem187103 (n : nat) (b : nat) (a : nat) : term93 n b a.
Proof. exact (@lem187100 n b a (@lem187092 n b a)). Qed.
Lemma lem187123 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem187124 : term96 = term97.
Proof. exact (@lem187123 term98). Qed.
Lemma lem187137 (n : nat) (b : nat) (a : nat) : (term99 n b a) = (term99 n b a).
Proof. exact (eq_refl (term99 n b a)). Qed.
Lemma lem187138 (n : nat) (b : nat) (a : nat) : (term100 n b a) = (term101 n b a).
Proof. exact (MK_COMB (@lem187137 n b a) (@lem187124)). Qed.
Lemma lem187141 (a : nat) (n : nat) (b : nat) : (term102 a n b) = (term102 a n b).
Proof. exact (eq_refl (term102 a n b)). Qed.
Lemma lem187142 (n : nat) (b : nat) (a : nat) : (term103 n b a) = (term104 n b a).
Proof. exact (MK_COMB (@lem187141 a n b) (@lem187138 n b a)). Qed.
Lemma lem187145 (a : nat) : (term105 a) = (term105 a).
Proof. exact (eq_refl (term105 a)). Qed.
Lemma lem187146 (n : nat) (b : nat) (a : nat) : (term92 n b a) = (term106 n b a).
Proof. exact (MK_COMB (@lem187145 a) (@lem187142 n b a)). Qed.
Lemma lem187149 (b : nat) (a : nat) : (term107 b a) = (term108 b a).
Proof. exact (fun_ext (fun n : nat => @lem187146 n b a)). Qed.
Lemma lem187150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187151 (b : nat) (a : nat) : (term109 b a) = (term110 b a).
Proof. exact (MK_COMB (@lem187150) (@lem187149 b a)). Qed.
Lemma lem187156 (a : nat) : (term111 a) = (term112 a).
Proof. exact (fun_ext (fun b : nat => @lem187151 b a)). Qed.
Lemma lem187157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187158 (a : nat) : (term113 a) = (term114 a).
Proof. exact (MK_COMB (@lem187157) (@lem187156 a)). Qed.
Lemma lem187163 : term115 = term116.
Proof. exact (fun_ext (fun a : nat => @lem187158 a)). Qed.
Lemma lem187164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187173 : term117 = term118.
Proof. exact (MK_COMB (@lem187164) (@lem187163)). Qed.
Lemma lem187184 (m : nat) (n : nat) : (term119 m n) = (term119 m n).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem187185 (m : nat) : (term120 m) = (term120 m).
Proof. exact (fun_ext (fun n : nat => @lem187184 m n)). Qed.
Lemma lem187186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187187 (m : nat) : (term121 m) = (term121 m).
Proof. exact (MK_COMB (@lem187186) (@lem187185 m)). Qed.
Lemma lem187188 : term122 = term122.
Proof. exact (fun_ext (fun m : nat => @lem187187 m)). Qed.
Lemma lem187189 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187190 : term98 = term98.
Proof. exact (MK_COMB (@lem187189) (@lem187188)). Qed.
Lemma lem187191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem187192 : term97 = term97.
Proof. exact (MK_COMB (@lem187191) (@lem187190)). Qed.
Lemma lem187197 (n : nat) (b : nat) (a : nat) : (term99 n b a) = (term99 n b a).
Proof. exact (eq_refl (term99 n b a)). Qed.
Lemma lem187198 (n : nat) (b : nat) (a : nat) : (term101 n b a) = (term101 n b a).
Proof. exact (MK_COMB (@lem187197 n b a) (@lem187192)). Qed.
Lemma lem187201 (a : nat) (n : nat) (b : nat) : (term102 a n b) = (term102 a n b).
Proof. exact (eq_refl (term102 a n b)). Qed.
Lemma lem187202 (n : nat) (b : nat) (a : nat) : (term104 n b a) = (term104 n b a).
Proof. exact (MK_COMB (@lem187201 a n b) (@lem187198 n b a)). Qed.
Lemma lem187207 (a : nat) : (term105 a) = (term105 a).
Proof. exact (eq_refl (term105 a)). Qed.
Lemma lem187208 (n : nat) (b : nat) (a : nat) : (term106 n b a) = (term106 n b a).
Proof. exact (MK_COMB (@lem187207 a) (@lem187202 n b a)). Qed.
Lemma lem187209 (b : nat) (a : nat) : (term108 b a) = (term108 b a).
Proof. exact (fun_ext (fun n : nat => @lem187208 n b a)). Qed.
Lemma lem187210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187211 (b : nat) (a : nat) : (term110 b a) = (term110 b a).
Proof. exact (MK_COMB (@lem187210) (@lem187209 b a)). Qed.
Lemma lem187212 (a : nat) : (term112 a) = (term112 a).
Proof. exact (fun_ext (fun b : nat => @lem187211 b a)). Qed.
Lemma lem187213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187214 (a : nat) : (term114 a) = (term114 a).
Proof. exact (MK_COMB (@lem187213) (@lem187212 a)). Qed.
Lemma lem187215 : term116 = term116.
Proof. exact (fun_ext (fun a : nat => @lem187214 a)). Qed.
Lemma lem187216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187217 : term118 = term118.
Proof. exact (MK_COMB (@lem187216) (@lem187215)). Qed.
Lemma lem187260 : term117 = term118.
Proof. exact (TRANS (@lem187173) (@lem187217)). Qed.
Lemma lem187261 : term118 = term117.
Proof. exact (SYM (@lem187260)). Qed.
Lemma lem187265 (h1 : term98) : term98.
Proof. exact (h1). Qed.
Lemma lem187271 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem187277 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (h1). Qed.
Lemma lem187283 (n : nat) (b : nat) (a : nat) (h1 : term91 n b a) : term91 n b a.
Proof. exact (h1). Qed.
Lemma lem187286 (n : nat) : (term123 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem187291 (m : nat) (n : nat) : (term124 m n) = (term124 m n).
Proof. exact (eq_refl (term124 m n)). Qed.
Lemma lem187292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem187293 (n : nat) : (term125 n) = (term79 n).
Proof. exact (MK_COMB (@lem187292) (@lem187286 n)). Qed.
Lemma lem187294 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem187293 n) (@lem187291 m n)). Qed.
Lemma lem187295 (m : nat) (n : nat) : (term119 m n) = (term126 m n).
Proof. exact (@lem17265 (term61 n) (term124 m n)). Qed.
Lemma lem187296 (m : nat) (n : nat) : (term119 m n) = (term127 m n).
Proof. exact (TRANS (@lem187295 m n) (@lem187294 m n)). Qed.
Lemma lem187297 (m : nat) : (term120 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem187296 m n)). Qed.
Lemma lem187298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187299 (m : nat) : (term121 m) = (term129 m).
Proof. exact (MK_COMB (@lem187298) (@lem187297 m)). Qed.
Lemma lem187300 : term122 = term130.
Proof. exact (fun_ext (fun m : nat => @lem187299 m)). Qed.
Lemma lem187301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187358 : term98 = term131.
Proof. exact (MK_COMB (@lem187301) (@lem187300)). Qed.
Lemma lem187359 (h1 : term98) : term131.
Proof. exact (EQ_MP (@lem187358) (@lem187265 h1)). Qed.
Lemma lem187369 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem187379 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (h1). Qed.
Lemma lem187407 (n : nat) (b : nat) (a : nat) (h1 : term91 n b a) : term91 n b a.
Proof. exact (h1). Qed.
Lemma lem187450 (m : nat) (n : nat) : (term127 m n) = (term127 m n).
Proof. exact (eq_refl (term127 m n)). Qed.
Lemma lem187451 (m : nat) : (term128 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem187450 m n)). Qed.
Lemma lem187452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187453 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem187452) (@lem187451 m)). Qed.
Lemma lem187454 : term130 = term130.
Proof. exact (fun_ext (fun m : nat => @lem187453 m)). Qed.
Lemma lem187455 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187456 : term131 = term131.
Proof. exact (MK_COMB (@lem187455) (@lem187454)). Qed.
Lemma lem187457 (h1 : term98) : term131.
Proof. exact (EQ_MP (@lem187456) (@lem187359 h1)). Qed.
Lemma lem187461 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem187465 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (h1). Qed.
Lemma lem187469 (n : nat) (b : nat) (a : nat) (h1 : term91 n b a) : term91 n b a.
Proof. exact (h1). Qed.
Lemma lem187487 (m : nat) (n : nat) : (term127 m n) = (term132 m n).
Proof. exact (@lem19490 (m = (term133 m n)) (n = (NUMERAL 0)) (term134 m n)). Qed.
Lemma lem187488 (m : nat) : (term128 m) = (term135 m).
Proof. exact (fun_ext (fun n : nat => @lem187487 m n)). Qed.
Lemma lem187489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187490 (m : nat) : (term129 m) = (term136 m).
Proof. exact (MK_COMB (@lem187489) (@lem187488 m)). Qed.
Lemma lem187491 : term130 = term137.
Proof. exact (fun_ext (fun m : nat => @lem187490 m)). Qed.
Lemma lem187492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem187494 : term131 = term138.
Proof. exact (MK_COMB (@lem187492) (@lem187491)). Qed.
Lemma lem187495 (h1 : term98) : term138.
Proof. exact (EQ_MP (@lem187494) (@lem187457 h1)). Qed.
Lemma lem187496 (_3801 : nat) (h1 : term98) : term139 _3801.
Proof. exact (@lem187495 h1 _3801). Qed.
Lemma lem187497 (_3801 : nat) : (term139 _3801) = (term136 _3801).
Proof. exact (eq_refl (term139 _3801)). Qed.
Lemma lem187498 (_3801 : nat) (h1 : term98) : term136 _3801.
Proof. exact (EQ_MP (@lem187497 _3801) (@lem187496 _3801 h1)). Qed.
Lemma lem187499 (_3801 : nat) (_3802 : nat) (h1 : term98) : term140 _3801 _3802.
Proof. exact (@lem187498 _3801 h1 _3802). Qed.
Lemma lem187500 (_3801 : nat) (_3802 : nat) : (term140 _3801 _3802) = (term132 _3801 _3802).
Proof. exact (eq_refl (term140 _3801 _3802)). Qed.
Lemma lem187501 (_3801 : nat) (_3802 : nat) (h1 : term98) : term132 _3801 _3802.
Proof. exact (EQ_MP (@lem187500 _3801 _3802) (@lem187499 _3801 _3802 h1)). Qed.
Lemma lem187505 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem187507 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (h1). Qed.
Lemma lem187509 (n : nat) (b : nat) (a : nat) (h1 : term91 n b a) : term91 n b a.
Proof. exact (h1). Qed.
Lemma lem187515 (_3801 : nat) (_3802 : nat) (h1 : term98) : term141 _3801 _3802.
Proof. exact (proj1 (@lem187501 _3801 _3802 h1)). Qed.
Lemma lem187541 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem187542 (_3807 : nat) (_3809 : nat) (h1 : _3807 = _3809) : _3807 = _3809.
Proof. exact (h1). Qed.
Lemma lem187543 (_3808 : nat) (_3810 : nat) (h1 : _3808 = _3810) : _3808 = _3810.
Proof. exact (h1). Qed.
Lemma lem187544 (_3807 : nat) (_3809 : nat) (h1 : _3807 = _3809) : (Peano.le _3807) = (Peano.le _3809).
Proof. exact (MK_COMB (@lem187541) (@lem187542 _3807 _3809 h1)). Qed.
Lemma lem187545 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) (h1 : _3807 = _3809) (h2 : _3808 = _3810) : (Peano.le _3807 _3808) = (Peano.le _3809 _3810).
Proof. exact (MK_COMB (@lem187544 _3807 _3809 h1) (@lem187543 _3808 _3810 h2)). Qed.
Lemma lem187547 (b : Prop) (a : Prop) : term142 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem187548 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : term143 _3809 _3810 _3807 _3808.
Proof. exact (@lem187547 (Peano.le _3809 _3810) (Peano.le _3807 _3808)). Qed.
Lemma lem187549 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) (h1 : _3807 = _3809) (h2 : _3808 = _3810) : term144 _3809 _3810 _3807 _3808.
Proof. exact (@lem187548 _3809 _3810 _3807 _3808 (@lem187545 _3807 _3809 _3808 _3810 h1 h2)). Qed.
Lemma lem187550 (_3810 : nat) (_3808 : nat) (_3807 : nat) (_3809 : nat) (h1 : _3807 = _3809) : term145 _3809 _3810 _3807 _3808.
Proof. exact (fun h0 : _3808 = _3810 => @lem187549 _3807 _3809 _3808 _3810 h1 h0). Qed.
Lemma lem187552 (a : Prop) (b : Prop) : (a -> b) = (term146 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem187553 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term145 _3809 _3810 _3807 _3808) = (term147 _3809 _3810 _3807 _3808).
Proof. exact (@lem187552 (_3808 = _3810) (term144 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187554 (_3810 : nat) (_3808 : nat) (_3807 : nat) (_3809 : nat) (h1 : _3807 = _3809) : term147 _3809 _3810 _3807 _3808.
Proof. exact (EQ_MP (@lem187553 _3809 _3810 _3807 _3808) (@lem187550 _3810 _3808 _3807 _3809 h1)). Qed.
Lemma lem187555 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : term148 _3809 _3810 _3807 _3808.
Proof. exact (fun h0 : _3807 = _3809 => @lem187554 _3810 _3808 _3807 _3809 h0). Qed.
Lemma lem187557 (a : Prop) (b : Prop) : (a -> b) = (term146 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem187558 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term148 _3809 _3810 _3807 _3808) = (term149 _3809 _3810 _3807 _3808).
Proof. exact (@lem187557 (_3807 = _3809) (term147 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187559 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : term149 _3809 _3810 _3807 _3808.
Proof. exact (EQ_MP (@lem187558 _3809 _3810 _3807 _3808) (@lem187555 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187631 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem187632 (a : nat) (n : nat) : (Nat.mul a n) = (Nat.mul a n).
Proof. exact (@lem187631 (Nat.mul a n)). Qed.
Lemma lem187633 (a : nat) (n : nat) : term150 a n.
Proof. exact (fun h0 : term151 a n => @lem187632 a n). Qed.
Lemma lem187635 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem187636 (a : nat) (n : nat) : (term150 a n) = ((Nat.mul a n) = (Nat.mul a n)).
Proof. exact (@lem187635 ((Nat.mul a n) = (Nat.mul a n))). Qed.
Lemma lem187637 (a : nat) (n : nat) : (Nat.mul a n) = (Nat.mul a n).
Proof. exact (EQ_MP (@lem187636 a n) (@lem187633 a n)). Qed.
Lemma lem187639 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem187640 (a : nat) (h1 : term61 a) : term153 a.
Proof. exact (fun h0 : a = (NUMERAL 0) => @lem187639 a h1). Qed.
Lemma lem187642 (p : Prop) : (term154 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem187643 (a : nat) : (term153 a) = (term61 a).
Proof. exact (@lem187642 (a = (NUMERAL 0))). Qed.
Lemma lem187644 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (EQ_MP (@lem187643 a) (@lem187640 a h1)). Qed.
Lemma lem187650 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem187651 (_3801 : nat) (_3802 : nat) : (term141 _3801 _3802) = (term155 _3801 _3802).
Proof. exact (@lem187650 (_3801 = (term133 _3801 _3802)) (_3802 = (NUMERAL 0))). Qed.
Lemma lem187661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem187662 (_3801 : nat) (_3802 : nat) : (term156 _3801 _3802) = (term157 _3801 _3802).
Proof. exact (MK_COMB (@lem187661) (@lem187651 _3801 _3802)). Qed.
Lemma lem187672 (_3801 : nat) (_3802 : nat) : (term155 _3801 _3802) = (term155 _3801 _3802).
Proof. exact (eq_refl (term155 _3801 _3802)). Qed.
Lemma lem187673 (_3801 : nat) (_3802 : nat) : ((term141 _3801 _3802) = (term155 _3801 _3802)) = ((term155 _3801 _3802) = (term155 _3801 _3802)).
Proof. exact (MK_COMB (@lem187662 _3801 _3802) (@lem187672 _3801 _3802)). Qed.
Lemma lem187675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem187676 (x : Prop) : (x = x) = True.
Proof. exact (@lem187675 Prop x). Qed.
Lemma lem187677 (_3801 : nat) (_3802 : nat) : ((term155 _3801 _3802) = (term155 _3801 _3802)) = True.
Proof. exact (@lem187676 (term155 _3801 _3802)). Qed.
Lemma lem187678 (_3801 : nat) (_3802 : nat) : ((term141 _3801 _3802) = (term155 _3801 _3802)) = True.
Proof. exact (TRANS (@lem187673 _3801 _3802) (@lem187677 _3801 _3802)). Qed.
Lemma lem187679 (_3801 : nat) (_3802 : nat) : True = ((term141 _3801 _3802) = (term155 _3801 _3802)).
Proof. exact (SYM (@lem187678 _3801 _3802)). Qed.
Lemma lem187680 (_3801 : nat) (_3802 : nat) : (term141 _3801 _3802) = (term155 _3801 _3802).
Proof. exact (EQ_MP (@lem187679 _3801 _3802) (@lem0)). Qed.
Lemma lem187681 (_3801 : nat) (_3802 : nat) (h1 : term98) : term155 _3801 _3802.
Proof. exact (EQ_MP (@lem187680 _3801 _3802) (@lem187515 _3801 _3802 h1)). Qed.
Lemma lem187683 (b : Prop) (a : Prop) : (a \/ b) = (term158 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem187686 (_3801 : nat) (_3802 : nat) : (term155 _3801 _3802) = (term159 _3801 _3802).
Proof. exact (@lem187683 (_3802 = (NUMERAL 0)) (_3801 = (term133 _3801 _3802))). Qed.
Lemma lem187689 (_3801 : nat) (_3802 : nat) (h1 : term98) : term159 _3801 _3802.
Proof. exact (EQ_MP (@lem187686 _3801 _3802) (@lem187681 _3801 _3802 h1)). Qed.
Lemma lem187690 (_3801 : nat) (a : nat) (h1 : term98) : term159 _3801 a.
Proof. exact (@lem187689 _3801 a h1). Qed.
Lemma lem187693 (_3801 : nat) (a : nat) (h1 : term98) (h2 : term61 a) : _3801 = (term133 _3801 a).
Proof. exact (@lem187690 _3801 a h1 (@lem187644 a h2)). Qed.
Lemma lem187694 (b : nat) (a : nat) (h1 : term98) (h2 : term61 a) : b = (term133 b a).
Proof. exact (@lem187693 b a h1 h2). Qed.
Lemma lem187695 (b : nat) (a : nat) (h1 : term98) (h2 : term61 a) : term160 b a.
Proof. exact (fun h0 : term161 b a => @lem187694 b a h1 h2). Qed.
Lemma lem187697 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem187698 (b : nat) (a : nat) : (term160 b a) = (b = (term133 b a)).
Proof. exact (@lem187697 (b = (term133 b a))). Qed.
Lemma lem187699 (b : nat) (a : nat) (h1 : term98) (h2 : term61 a) : b = (term133 b a).
Proof. exact (EQ_MP (@lem187698 b a) (@lem187695 b a h1 h2)). Qed.
Lemma lem187701 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (h1). Qed.
Lemma lem187702 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term162 a n b.
Proof. exact (fun h0 : term163 a n b => @lem187701 a n b h1). Qed.
Lemma lem187704 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem187705 (a : nat) (n : nat) (b : nat) : (term162 a n b) = (term63 a n b).
Proof. exact (@lem187704 (term63 a n b)). Qed.
Lemma lem187706 (a : nat) (n : nat) (b : nat) (h1 : term63 a n b) : term63 a n b.
Proof. exact (EQ_MP (@lem187705 a n b) (@lem187702 a n b h1)). Qed.
Lemma lem187724 (q : Prop) (p : Prop) (r : Prop) : (term164 p q r) = (term164 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem187725 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term147 _3809 _3810 _3807 _3808) = (term165 _3809 _3810 _3807 _3808).
Proof. exact (@lem187724 (Peano.le _3809 _3810) (term166 _3808 _3810) (term167 _3807 _3808)). Qed.
Lemma lem187739 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem187740 (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term168 _3810 _3807 _3808) = (term169 _3807 _3808 _3810).
Proof. exact (@lem187739 (term167 _3807 _3808) (term166 _3808 _3810)). Qed.
Lemma lem187748 (_3809 : nat) (_3810 : nat) : (term170 _3809 _3810) = (term170 _3809 _3810).
Proof. exact (eq_refl (term170 _3809 _3810)). Qed.
Lemma lem187749 (_3809 : nat) (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term165 _3809 _3810 _3807 _3808) = (term171 _3809 _3807 _3808 _3810).
Proof. exact (MK_COMB (@lem187748 _3809 _3810) (@lem187740 _3807 _3808 _3810)). Qed.
Lemma lem187760 (_3809 : nat) (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term147 _3809 _3810 _3807 _3808) = (term171 _3809 _3807 _3808 _3810).
Proof. exact (TRANS (@lem187725 _3809 _3810 _3807 _3808) (@lem187749 _3809 _3807 _3808 _3810)). Qed.
Lemma lem187761 (_3807 : nat) (_3809 : nat) : (term172 _3807 _3809) = (term172 _3807 _3809).
Proof. exact (eq_refl (term172 _3807 _3809)). Qed.
Lemma lem187762 (_3809 : nat) (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term149 _3809 _3810 _3807 _3808) = (term173 _3809 _3807 _3808 _3810).
Proof. exact (MK_COMB (@lem187761 _3807 _3809) (@lem187760 _3809 _3807 _3808 _3810)). Qed.
Lemma lem187766 (q : Prop) (p : Prop) (r : Prop) : (term164 p q r) = (term164 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem187767 (_3809 : nat) (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term173 _3809 _3807 _3808 _3810) = (term174 _3809 _3807 _3808 _3810).
Proof. exact (@lem187766 (Peano.le _3809 _3810) (term166 _3807 _3809) (term169 _3807 _3808 _3810)). Qed.
Lemma lem187781 (q : Prop) (p : Prop) (r : Prop) : (term164 p q r) = (term164 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem187782 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term175 _3809 _3807 _3808 _3810) = (term176 _3807 _3809 _3808 _3810).
Proof. exact (@lem187781 (term167 _3807 _3808) (term166 _3807 _3809) (term166 _3808 _3810)). Qed.
Lemma lem187802 (_3809 : nat) (_3810 : nat) : (term170 _3809 _3810) = (term170 _3809 _3810).
Proof. exact (eq_refl (term170 _3809 _3810)). Qed.
Lemma lem187803 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term174 _3809 _3807 _3808 _3810) = (term177 _3807 _3809 _3808 _3810).
Proof. exact (MK_COMB (@lem187802 _3809 _3810) (@lem187782 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187814 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term173 _3809 _3807 _3808 _3810) = (term177 _3807 _3809 _3808 _3810).
Proof. exact (TRANS (@lem187767 _3809 _3807 _3808 _3810) (@lem187803 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187815 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term149 _3809 _3810 _3807 _3808) = (term177 _3807 _3809 _3808 _3810).
Proof. exact (TRANS (@lem187762 _3809 _3807 _3808 _3810) (@lem187814 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem187817 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term178 _3809 _3810 _3807 _3808) = (term179 _3807 _3809 _3808 _3810).
Proof. exact (MK_COMB (@lem187816) (@lem187815 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187843 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem187844 (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term168 _3810 _3807 _3808) = (term169 _3807 _3808 _3810).
Proof. exact (@lem187843 (term167 _3807 _3808) (term166 _3808 _3810)). Qed.
Lemma lem187852 (_3807 : nat) (_3809 : nat) : (term172 _3807 _3809) = (term172 _3807 _3809).
Proof. exact (eq_refl (term172 _3807 _3809)). Qed.
Lemma lem187853 (_3809 : nat) (_3807 : nat) (_3808 : nat) (_3810 : nat) : (term180 _3809 _3810 _3807 _3808) = (term175 _3809 _3807 _3808 _3810).
Proof. exact (MK_COMB (@lem187852 _3807 _3809) (@lem187844 _3807 _3808 _3810)). Qed.
Lemma lem187857 (q : Prop) (p : Prop) (r : Prop) : (term164 p q r) = (term164 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem187858 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term175 _3809 _3807 _3808 _3810) = (term176 _3807 _3809 _3808 _3810).
Proof. exact (@lem187857 (term167 _3807 _3808) (term166 _3807 _3809) (term166 _3808 _3810)). Qed.
Lemma lem187878 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term180 _3809 _3810 _3807 _3808) = (term176 _3807 _3809 _3808 _3810).
Proof. exact (TRANS (@lem187853 _3809 _3807 _3808 _3810) (@lem187858 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187879 (_3809 : nat) (_3810 : nat) : (term170 _3809 _3810) = (term170 _3809 _3810).
Proof. exact (eq_refl (term170 _3809 _3810)). Qed.
Lemma lem187880 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : (term181 _3809 _3810 _3807 _3808) = (term177 _3807 _3809 _3808 _3810).
Proof. exact (MK_COMB (@lem187879 _3809 _3810) (@lem187878 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187891 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : ((term149 _3809 _3810 _3807 _3808) = (term181 _3809 _3810 _3807 _3808)) = ((term177 _3807 _3809 _3808 _3810) = (term177 _3807 _3809 _3808 _3810)).
Proof. exact (MK_COMB (@lem187817 _3807 _3809 _3808 _3810) (@lem187880 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem187894 (x : Prop) : (x = x) = True.
Proof. exact (@lem187893 Prop x). Qed.
Lemma lem187895 (_3807 : nat) (_3809 : nat) (_3808 : nat) (_3810 : nat) : ((term177 _3807 _3809 _3808 _3810) = (term177 _3807 _3809 _3808 _3810)) = True.
Proof. exact (@lem187894 (term177 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187896 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : ((term149 _3809 _3810 _3807 _3808) = (term181 _3809 _3810 _3807 _3808)) = True.
Proof. exact (TRANS (@lem187891 _3807 _3809 _3808 _3810) (@lem187895 _3807 _3809 _3808 _3810)). Qed.
Lemma lem187897 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : True = ((term149 _3809 _3810 _3807 _3808) = (term181 _3809 _3810 _3807 _3808)).
Proof. exact (SYM (@lem187896 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187898 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term149 _3809 _3810 _3807 _3808) = (term181 _3809 _3810 _3807 _3808).
Proof. exact (EQ_MP (@lem187897 _3809 _3810 _3807 _3808) (@lem0)). Qed.
Lemma lem187899 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : term181 _3809 _3810 _3807 _3808.
Proof. exact (EQ_MP (@lem187898 _3809 _3810 _3807 _3808) (@lem187559 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187901 (b : Prop) (a : Prop) : (a \/ b) = (term158 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem187902 (_3807 : nat) (_3808 : nat) (_3809 : nat) (_3810 : nat) : (term181 _3809 _3810 _3807 _3808) = (term182 _3807 _3808 _3809 _3810).
Proof. exact (@lem187901 (term180 _3809 _3810 _3807 _3808) (Peano.le _3809 _3810)). Qed.
Lemma lem187904 (a : Prop) (b : Prop) : (term183 a b) = (term184 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem187905 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term185 _3809 _3810 _3807 _3808) = (term186 _3809 _3810 _3807 _3808).
Proof. exact (@lem187904 (term166 _3807 _3809) (term168 _3810 _3807 _3808)). Qed.
Lemma lem187907 (a : Prop) : (term187 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem187908 (_3807 : nat) (_3809 : nat) : (term188 _3807 _3809) = (_3807 = _3809).
Proof. exact (@lem187907 (_3807 = _3809)). Qed.
Lemma lem187909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem187910 (_3807 : nat) (_3809 : nat) : (term189 _3807 _3809) = (term190 _3807 _3809).
Proof. exact (MK_COMB (@lem187909) (@lem187908 _3807 _3809)). Qed.
Lemma lem187912 (a : Prop) (b : Prop) : (term183 a b) = (term184 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem187913 (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term191 _3810 _3807 _3808) = (term192 _3810 _3807 _3808).
Proof. exact (@lem187912 (term166 _3808 _3810) (term167 _3807 _3808)). Qed.
Lemma lem187915 (a : Prop) : (term187 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem187916 (_3808 : nat) (_3810 : nat) : (term188 _3808 _3810) = (_3808 = _3810).
Proof. exact (@lem187915 (_3808 = _3810)). Qed.
Lemma lem187917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem187918 (_3808 : nat) (_3810 : nat) : (term189 _3808 _3810) = (term190 _3808 _3810).
Proof. exact (MK_COMB (@lem187917) (@lem187916 _3808 _3810)). Qed.
Lemma lem187920 (a : Prop) : (term187 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem187921 (_3807 : nat) (_3808 : nat) : (term193 _3807 _3808) = (Peano.le _3807 _3808).
Proof. exact (@lem187920 (Peano.le _3807 _3808)). Qed.
Lemma lem187922 (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term192 _3810 _3807 _3808) = (term194 _3810 _3807 _3808).
Proof. exact (MK_COMB (@lem187918 _3808 _3810) (@lem187921 _3807 _3808)). Qed.
Lemma lem187923 (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term191 _3810 _3807 _3808) = (term194 _3810 _3807 _3808).
Proof. exact (TRANS (@lem187913 _3810 _3807 _3808) (@lem187922 _3810 _3807 _3808)). Qed.
Lemma lem187924 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term186 _3809 _3810 _3807 _3808) = (term195 _3809 _3810 _3807 _3808).
Proof. exact (MK_COMB (@lem187910 _3807 _3809) (@lem187923 _3810 _3807 _3808)). Qed.
Lemma lem187925 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term185 _3809 _3810 _3807 _3808) = (term195 _3809 _3810 _3807 _3808).
Proof. exact (TRANS (@lem187905 _3809 _3810 _3807 _3808) (@lem187924 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem187927 (_3809 : nat) (_3810 : nat) (_3807 : nat) (_3808 : nat) : (term196 _3809 _3810 _3807 _3808) = (term197 _3809 _3810 _3807 _3808).
Proof. exact (MK_COMB (@lem187926) (@lem187925 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187928 (_3809 : nat) (_3810 : nat) : (Peano.le _3809 _3810) = (Peano.le _3809 _3810).
Proof. exact (eq_refl (Peano.le _3809 _3810)). Qed.
Lemma lem187929 (_3807 : nat) (_3808 : nat) (_3809 : nat) (_3810 : nat) : (term182 _3807 _3808 _3809 _3810) = (term198 _3807 _3808 _3809 _3810).
Proof. exact (MK_COMB (@lem187927 _3809 _3810 _3807 _3808) (@lem187928 _3809 _3810)). Qed.
Lemma lem187930 (_3807 : nat) (_3808 : nat) (_3809 : nat) (_3810 : nat) : (term181 _3809 _3810 _3807 _3808) = (term198 _3807 _3808 _3809 _3810).
Proof. exact (TRANS (@lem187902 _3807 _3808 _3809 _3810) (@lem187929 _3807 _3808 _3809 _3810)). Qed.
Lemma lem187932 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term61 a) (h3 : term63 a n b) : term199 a n b.
Proof. exact (conj (@lem187699 b a h1 h2) (@lem187706 a n b h3)). Qed.
Lemma lem187933 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term61 a) (h3 : term63 a n b) : term200 a n b.
Proof. exact (conj (@lem187637 a n) (@lem187932 a n b h1 h2 h3)). Qed.
Lemma lem187935 (_3807 : nat) (_3808 : nat) (_3809 : nat) (_3810 : nat) : term198 _3807 _3808 _3809 _3810.
Proof. exact (EQ_MP (@lem187930 _3807 _3808 _3809 _3810) (@lem187899 _3809 _3810 _3807 _3808)). Qed.
Lemma lem187936 (n : nat) (b : nat) (a : nat) : term201 n b a.
Proof. exact (@lem187935 (Nat.mul a n) b (Nat.mul a n) (term133 b a)). Qed.
Lemma lem187939 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term61 a) (h3 : term63 a n b) : term89 n b a.
Proof. exact (@lem187936 n b a (@lem187933 a n b h1 h2 h3)). Qed.
Lemma lem187940 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term61 a) (h3 : term63 a n b) : term202 n b a.
Proof. exact (fun h0 : term91 n b a => @lem187939 a n b h1 h2 h3). Qed.
Lemma lem187942 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem187943 (n : nat) (b : nat) (a : nat) : (term202 n b a) = (term89 n b a).
Proof. exact (@lem187942 (term89 n b a)). Qed.
Lemma lem187944 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term61 a) (h3 : term63 a n b) : term89 n b a.
Proof. exact (EQ_MP (@lem187943 n b a) (@lem187940 a n b h1 h2 h3)). Qed.
Lemma lem187947 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem187949 (n : nat) (b : nat) (a : nat) : (term91 n b a) = (term203 n b a).
Proof. exact (@lem187947 (term89 n b a)). Qed.
Lemma lem187952 (n : nat) (b : nat) (a : nat) (h1 : term91 n b a) : term203 n b a.
Proof. exact (EQ_MP (@lem187949 n b a) (@lem187509 n b a h1)). Qed.
Lemma lem187955 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (@lem187952 n b a h2 (@lem187944 a n b h1 h3 h4)). Qed.
Lemma lem187956 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : term204.
Proof. exact (fun h0 : ~ False => @lem187955 a n b h1 h2 h3 h4). Qed.
Lemma lem187958 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem187959 : term204 = False.
Proof. exact (@lem187958 False). Qed.
Lemma lem187960 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187959) (@lem187956 a n b h1 h2 h3 h4)). Qed.
Lemma lem187961 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term91 n b a) = False.
Proof. exact (prop_ext (fun h5 : term91 n b a => @lem187960 a n b h1 h2 h3 h4) (fun h5 : False => @lem187509 n b a h2)). Qed.
Lemma lem187962 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187961 a n b h1 h2 h3 h4) (@lem187509 n b a h2)). Qed.
Lemma lem187963 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term63 a n b) = False.
Proof. exact (prop_ext (fun h5 : term63 a n b => @lem187962 a n b h1 h2 h3 h4) (fun h5 : False => @lem187507 a n b h4)). Qed.
Lemma lem187964 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187963 a n b h1 h2 h3 h4) (@lem187507 a n b h4)). Qed.
Lemma lem187965 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term61 a) = False.
Proof. exact (prop_ext (fun h5 : term61 a => @lem187964 a n b h1 h2 h3 h4) (fun h5 : False => @lem187505 a h3)). Qed.
Lemma lem187966 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187965 a n b h1 h2 h3 h4) (@lem187505 a h3)). Qed.
Lemma lem187967 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term91 n b a) = False.
Proof. exact (prop_ext (fun h5 : term91 n b a => @lem187966 a n b h1 h2 h3 h4) (fun h5 : False => @lem187469 n b a h2)). Qed.
Lemma lem187968 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187967 a n b h1 h2 h3 h4) (@lem187469 n b a h2)). Qed.
Lemma lem187969 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term63 a n b) = False.
Proof. exact (prop_ext (fun h5 : term63 a n b => @lem187968 a n b h1 h2 h3 h4) (fun h5 : False => @lem187465 a n b h4)). Qed.
Lemma lem187970 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187969 a n b h1 h2 h3 h4) (@lem187465 a n b h4)). Qed.
Lemma lem187971 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term61 a) = False.
Proof. exact (prop_ext (fun h5 : term61 a => @lem187970 a n b h1 h2 h3 h4) (fun h5 : False => @lem187461 a h3)). Qed.
Lemma lem187972 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187971 a n b h1 h2 h3 h4) (@lem187461 a h3)). Qed.
Lemma lem187973 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term91 n b a) = False.
Proof. exact (prop_ext (fun h5 : term91 n b a => @lem187972 a n b h1 h2 h3 h4) (fun h5 : False => @lem187469 n b a h2)). Qed.
Lemma lem187974 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187973 a n b h1 h2 h3 h4) (@lem187469 n b a h2)). Qed.
Lemma lem187975 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term63 a n b) = False.
Proof. exact (prop_ext (fun h5 : term63 a n b => @lem187974 a n b h1 h2 h3 h4) (fun h5 : False => @lem187465 a n b h4)). Qed.
Lemma lem187976 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187975 a n b h1 h2 h3 h4) (@lem187465 a n b h4)). Qed.
Lemma lem187977 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term61 a) = False.
Proof. exact (prop_ext (fun h5 : term61 a => @lem187976 a n b h1 h2 h3 h4) (fun h5 : False => @lem187461 a h3)). Qed.
Lemma lem187978 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187977 a n b h1 h2 h3 h4) (@lem187461 a h3)). Qed.
Lemma lem187979 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term91 n b a) = False.
Proof. exact (prop_ext (fun h5 : term91 n b a => @lem187978 a n b h1 h2 h3 h4) (fun h5 : False => @lem187407 n b a h2)). Qed.
Lemma lem187980 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187979 a n b h1 h2 h3 h4) (@lem187407 n b a h2)). Qed.
Lemma lem187981 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term63 a n b) = False.
Proof. exact (prop_ext (fun h5 : term63 a n b => @lem187980 a n b h1 h2 h3 h4) (fun h5 : False => @lem187379 a n b h4)). Qed.
Lemma lem187982 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187981 a n b h1 h2 h3 h4) (@lem187379 a n b h4)). Qed.
Lemma lem187983 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term61 a) = False.
Proof. exact (prop_ext (fun h5 : term61 a => @lem187982 a n b h1 h2 h3 h4) (fun h5 : False => @lem187369 a h3)). Qed.
Lemma lem187984 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187983 a n b h1 h2 h3 h4) (@lem187369 a h3)). Qed.
Lemma lem187985 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term91 n b a) = False.
Proof. exact (prop_ext (fun h5 : term91 n b a => @lem187984 a n b h1 h2 h3 h4) (fun h5 : False => @lem187283 n b a h2)). Qed.
Lemma lem187986 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187985 a n b h1 h2 h3 h4) (@lem187283 n b a h2)). Qed.
Lemma lem187987 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term63 a n b) = False.
Proof. exact (prop_ext (fun h5 : term63 a n b => @lem187986 a n b h1 h2 h3 h4) (fun h5 : False => @lem187277 a n b h4)). Qed.
Lemma lem187988 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187987 a n b h1 h2 h3 h4) (@lem187277 a n b h4)). Qed.
Lemma lem187989 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : (term61 a) = False.
Proof. exact (prop_ext (fun h5 : term61 a => @lem187988 a n b h1 h2 h3 h4) (fun h5 : False => @lem187271 a h3)). Qed.
Lemma lem187990 (a : nat) (n : nat) (b : nat) (h1 : term98) (h2 : term91 n b a) (h3 : term61 a) (h4 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem187989 a n b h1 h2 h3 h4) (@lem187271 a h3)). Qed.
Lemma lem187991 (a : nat) (n : nat) (b : nat) (h1 : term91 n b a) (h2 : term61 a) (h3 : term63 a n b) : term96.
Proof. exact (fun h0 : term98 => @lem187990 a n b h0 h1 h2 h3). Qed.
Lemma lem187992 : term96 = term97.
Proof. exact (@lem69 term98). Qed.
Lemma lem187993 (a : nat) (n : nat) (b : nat) (h1 : term91 n b a) (h2 : term61 a) (h3 : term63 a n b) : term97.
Proof. exact (EQ_MP (@lem187992) (@lem187991 a n b h1 h2 h3)). Qed.
Lemma lem187994 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term101 n b a.
Proof. exact (fun h0 : term91 n b a => @lem187993 a n b h0 h1 h2). Qed.
Lemma lem187995 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term104 n b a.
Proof. exact (fun h0 : term63 a n b => @lem187994 a n b h1 h0). Qed.
Lemma lem187996 (n : nat) (b : nat) (a : nat) : term106 n b a.
Proof. exact (fun h0 : term61 a => @lem187995 n b a h0). Qed.
Lemma lem188001 (b : nat) (a : nat) : term110 b a.
Proof. exact (fun n : nat => @lem187996 n b a). Qed.
Lemma lem188006 (a : nat) : term114 a.
Proof. exact (fun b : nat => @lem188001 b a). Qed.
Lemma lem188011 : term118.
Proof. exact (fun a : nat => @lem188006 a). Qed.
Lemma lem188012 : term117.
Proof. exact (EQ_MP (@lem187261) (@lem188011)). Qed.
Lemma lem188013 (a : nat) : term205 a.
Proof. exact (@lem188012 a). Qed.
Lemma lem188014 (a : nat) : (term205 a) = (term113 a).
Proof. exact (eq_refl (term205 a)). Qed.
Lemma lem188015 (a : nat) : term113 a.
Proof. exact (EQ_MP (@lem188014 a) (@lem188013 a)). Qed.
Lemma lem188016 (a : nat) (b : nat) : term206 a b.
Proof. exact (@lem188015 a b). Qed.
Lemma lem188017 (b : nat) (a : nat) : (term206 a b) = (term109 b a).
Proof. exact (eq_refl (term206 a b)). Qed.
Lemma lem188018 (b : nat) (a : nat) : term109 b a.
Proof. exact (EQ_MP (@lem188017 b a) (@lem188016 a b)). Qed.
Lemma lem188019 (b : nat) (a : nat) (n : nat) : term207 b a n.
Proof. exact (@lem188018 b a n). Qed.
Lemma lem188020 (n : nat) (b : nat) (a : nat) : (term207 b a n) = (term92 n b a).
Proof. exact (eq_refl (term207 b a n)). Qed.
Lemma lem188021 (n : nat) (b : nat) (a : nat) : term92 n b a.
Proof. exact (EQ_MP (@lem188020 n b a) (@lem188019 b a n)). Qed.
Lemma lem188023 (n : nat) (b : nat) (a : nat) : term92 n b a.
Proof. exact (@lem187103 n b a (@lem188021 n b a)). Qed.
Lemma lem188024 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term103 n b a.
Proof. exact (@lem188023 n b a (@lem187009 a h1)). Qed.
Lemma lem188025 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term100 n b a.
Proof. exact (@lem188024 n b a h1 (@lem187011 a n b h2)). Qed.
Lemma lem188026 (a : nat) (n : nat) (b : nat) (h1 : term91 n b a) (h2 : term61 a) (h3 : term63 a n b) : term96.
Proof. exact (@lem188025 a n b h2 h3 (@lem187088 n b a h1)). Qed.
Lemma lem188027 (a : nat) (n : nat) (b : nat) (h1 : term91 n b a) (h2 : term61 a) (h3 : term63 a n b) : False.
Proof. exact (@lem188026 a n b h1 h2 h3 (@lem157261)). Qed.
Lemma lem188028 (a : nat) (n : nat) (b : nat) (h1 : term91 n b a) (h2 : term61 a) (h3 : term63 a n b) : (term91 n b a) = False.
Proof. exact (prop_ext (fun h4 : term91 n b a => @lem188027 a n b h1 h2 h3) (fun h4 : False => @lem187088 n b a h1)). Qed.
Lemma lem188029 (a : nat) (n : nat) (b : nat) (h1 : term91 n b a) (h2 : term61 a) (h3 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem188028 a n b h1 h2 h3) (@lem187088 n b a h1)). Qed.
Lemma lem188030 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term90 n b a.
Proof. exact (fun h0 : term91 n b a => @lem188029 a n b h0 h1 h2). Qed.
Lemma lem188031 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term89 n b a.
Proof. exact (EQ_MP (@lem187087 n b a) (@lem188030 a n b h1 h2)). Qed.
Lemma lem188033 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem186932 n m) (@lem186931 m n)). Qed.
Lemma lem188034 (b : nat) (a : nat) : (term208 b a) = (term84 b a).
Proof. exact (@lem188033 a (Nat.div b a)). Qed.
Lemma lem188038 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem188039 (b : nat) (a : nat) : (term209 b a) = (term210 b a).
Proof. exact (MK_COMB (@lem188038) (@lem188034 b a)). Qed.
Lemma lem188043 (b : nat) (a : nat) : (Nat.modulo b a) = (Nat.modulo b a).
Proof. exact (eq_refl (Nat.modulo b a)). Qed.
Lemma lem188044 (b : nat) (a : nat) : (term133 b a) = (term211 b a).
Proof. exact (MK_COMB (@lem188039 b a) (@lem188043 b a)). Qed.
Lemma lem188048 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem188049 (b : nat) (a : nat) : (term212 b a) = (term213 b a).
Proof. exact (MK_COMB (@lem188048) (@lem188044 b a)). Qed.
Lemma lem188054 (n : nat) (m : nat) (p : nat) : (term25 m n p) = (term26 n m p).
Proof. exact (EQ_MP (@lem186941 n m p) (@lem186940 n m p)). Qed.
Lemma lem188055 (b : nat) (a : nat) : (term87 b a) = (term214 b a).
Proof. exact (@lem188054 (Nat.div b a) a term215). Qed.
Lemma lem188060 (m : nat) : (term16 m) = m.
Proof. exact (EQ_MP (@lem186914 m) (@lem186913 m)). Qed.
Lemma lem188061 (a : nat) : (term16 a) = a.
Proof. exact (@lem188060 a). Qed.
Lemma lem188062 (b : nat) (a : nat) : (term210 b a) = (term210 b a).
Proof. exact (eq_refl (term210 b a)). Qed.
Lemma lem188063 (b : nat) (a : nat) : (term214 b a) = (term216 b a).
Proof. exact (MK_COMB (@lem188062 b a) (@lem188061 a)). Qed.
Lemma lem188067 (b : nat) (a : nat) : (term87 b a) = (term216 b a).
Proof. exact (TRANS (@lem188055 b a) (@lem188063 b a)). Qed.
Lemma lem188068 (b : nat) (a : nat) : (term217 b a) = (term218 b a).
Proof. exact (MK_COMB (@lem188049 b a) (@lem188067 b a)). Qed.
Lemma lem188070 (m : nat) (n : nat) (p : nat) : (term10 n m p) = (Peano.lt n p).
Proof. exact (EQ_MP (@lem186892 m n p) (@lem186891 m n p)). Qed.
Lemma lem188071 (b : nat) (a : nat) : (term218 b a) = (term134 b a).
Proof. exact (@lem188070 (term84 b a) (Nat.modulo b a) a). Qed.
Lemma lem188072 (b : nat) (a : nat) : (term217 b a) = (term134 b a).
Proof. exact (TRANS (@lem188068 b a) (@lem188071 b a)). Qed.
Lemma lem188073 (b : nat) (a : nat) : (term134 b a) = (term217 b a).
Proof. exact (SYM (@lem188072 b a)). Qed.
Lemma lem188075 (p : Prop) : p = (term88 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem188076 (b : nat) (a : nat) : (term134 b a) = (term219 b a).
Proof. exact (@lem188075 (term134 b a)). Qed.
Lemma lem188077 (b : nat) (a : nat) : (term219 b a) = (term134 b a).
Proof. exact (SYM (@lem188076 b a)). Qed.
Lemma lem188078 (b : nat) (a : nat) (h1 : term220 b a) : term220 b a.
Proof. exact (h1). Qed.
Lemma lem188081 (n : nat) (b : nat) (a : nat) (h1 : term221 n b a) : term221 n b a.
Proof. exact (h1). Qed.
Lemma lem188082 (n : nat) (b : nat) (a : nat) : term222 n b a.
Proof. exact (fun h0 : term221 n b a => @lem188081 n b a h0). Qed.
Lemma lem188083 (n : nat) (b : nat) (a : nat) (h1 : term222 n b a) : term222 n b a.
Proof. exact (h1). Qed.
Lemma lem188084 (n : nat) (b : nat) (a : nat) (h1 : term221 n b a) : term221 n b a.
Proof. exact (h1). Qed.
Lemma lem188085 (n : nat) (b : nat) (a : nat) (h1 : term221 n b a) (h2 : term222 n b a) : term221 n b a.
Proof. exact (@lem188083 n b a h2 (@lem188084 n b a h1)). Qed.
Lemma lem188086 (n : nat) (b : nat) (a : nat) (h1 : term221 n b a) : term223 n b a.
Proof. exact (fun h0 : term222 n b a => @lem188085 n b a h1 h0). Qed.
Lemma lem188087 (n : nat) (b : nat) (a : nat) (h1 : term222 n b a) : term222 n b a.
Proof. exact (h1). Qed.
Lemma lem188088 (n : nat) (b : nat) (a : nat) (h1 : term221 n b a) (h2 : term222 n b a) : term221 n b a.
Proof. exact (@lem188086 n b a h1 (@lem188087 n b a h2)). Qed.
Lemma lem188089 (n : nat) (b : nat) (a : nat) (h1 : term222 n b a) : term222 n b a.
Proof. exact (fun h0 : term221 n b a => @lem188088 n b a h0 h1). Qed.
Lemma lem188090 (n : nat) (b : nat) (a : nat) : term224 n b a.
Proof. exact (fun h0 : term222 n b a => @lem188089 n b a h0). Qed.
Lemma lem188093 (n : nat) (b : nat) (a : nat) : term222 n b a.
Proof. exact (@lem188090 n b a (@lem188082 n b a)). Qed.
Lemma lem188113 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem188114 : term96 = term97.
Proof. exact (@lem188113 term98). Qed.
Lemma lem188127 (b : nat) (a : nat) : (term225 b a) = (term225 b a).
Proof. exact (eq_refl (term225 b a)). Qed.
Lemma lem188128 (b : nat) (a : nat) : (term226 b a) = (term227 b a).
Proof. exact (MK_COMB (@lem188127 b a) (@lem188114)). Qed.
Lemma lem188131 (a : nat) (n : nat) (b : nat) : (term102 a n b) = (term102 a n b).
Proof. exact (eq_refl (term102 a n b)). Qed.
Lemma lem188132 (n : nat) (b : nat) (a : nat) : (term228 n b a) = (term229 n b a).
Proof. exact (MK_COMB (@lem188131 a n b) (@lem188128 b a)). Qed.
Lemma lem188135 (a : nat) : (term105 a) = (term105 a).
Proof. exact (eq_refl (term105 a)). Qed.
Lemma lem188136 (n : nat) (b : nat) (a : nat) : (term221 n b a) = (term230 n b a).
Proof. exact (MK_COMB (@lem188135 a) (@lem188132 n b a)). Qed.
Lemma lem188139 (b : nat) (a : nat) : (term231 b a) = (term232 b a).
Proof. exact (fun_ext (fun n : nat => @lem188136 n b a)). Qed.
Lemma lem188140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188141 (b : nat) (a : nat) : (term233 b a) = (term234 b a).
Proof. exact (MK_COMB (@lem188140) (@lem188139 b a)). Qed.
Lemma lem188146 (a : nat) : (term235 a) = (term236 a).
Proof. exact (fun_ext (fun b : nat => @lem188141 b a)). Qed.
Lemma lem188147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188148 (a : nat) : (term237 a) = (term238 a).
Proof. exact (MK_COMB (@lem188147) (@lem188146 a)). Qed.
Lemma lem188153 : term239 = term240.
Proof. exact (fun_ext (fun a : nat => @lem188148 a)). Qed.
Lemma lem188154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188163 : term241 = term242.
Proof. exact (MK_COMB (@lem188154) (@lem188153)). Qed.
Lemma lem188174 (m : nat) (n : nat) : (term119 m n) = (term119 m n).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem188175 (m : nat) : (term120 m) = (term120 m).
Proof. exact (fun_ext (fun n : nat => @lem188174 m n)). Qed.
Lemma lem188176 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188177 (m : nat) : (term121 m) = (term121 m).
Proof. exact (MK_COMB (@lem188176) (@lem188175 m)). Qed.
Lemma lem188178 : term122 = term122.
Proof. exact (fun_ext (fun m : nat => @lem188177 m)). Qed.
Lemma lem188179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188180 : term98 = term98.
Proof. exact (MK_COMB (@lem188179) (@lem188178)). Qed.
Lemma lem188181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem188182 : term97 = term97.
Proof. exact (MK_COMB (@lem188181) (@lem188180)). Qed.
Lemma lem188187 (b : nat) (a : nat) : (term225 b a) = (term225 b a).
Proof. exact (eq_refl (term225 b a)). Qed.
Lemma lem188188 (b : nat) (a : nat) : (term227 b a) = (term227 b a).
Proof. exact (MK_COMB (@lem188187 b a) (@lem188182)). Qed.
Lemma lem188191 (a : nat) (n : nat) (b : nat) : (term102 a n b) = (term102 a n b).
Proof. exact (eq_refl (term102 a n b)). Qed.
Lemma lem188192 (n : nat) (b : nat) (a : nat) : (term229 n b a) = (term229 n b a).
Proof. exact (MK_COMB (@lem188191 a n b) (@lem188188 b a)). Qed.
Lemma lem188197 (a : nat) : (term105 a) = (term105 a).
Proof. exact (eq_refl (term105 a)). Qed.
Lemma lem188198 (n : nat) (b : nat) (a : nat) : (term230 n b a) = (term230 n b a).
Proof. exact (MK_COMB (@lem188197 a) (@lem188192 n b a)). Qed.
Lemma lem188199 (b : nat) (a : nat) : (term232 b a) = (term232 b a).
Proof. exact (fun_ext (fun n : nat => @lem188198 n b a)). Qed.
Lemma lem188200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188201 (b : nat) (a : nat) : (term234 b a) = (term234 b a).
Proof. exact (MK_COMB (@lem188200) (@lem188199 b a)). Qed.
Lemma lem188202 (a : nat) : (term236 a) = (term236 a).
Proof. exact (fun_ext (fun b : nat => @lem188201 b a)). Qed.
Lemma lem188203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188204 (a : nat) : (term238 a) = (term238 a).
Proof. exact (MK_COMB (@lem188203) (@lem188202 a)). Qed.
Lemma lem188205 : term240 = term240.
Proof. exact (fun_ext (fun a : nat => @lem188204 a)). Qed.
Lemma lem188206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188207 : term242 = term242.
Proof. exact (MK_COMB (@lem188206) (@lem188205)). Qed.
Lemma lem188250 : term241 = term242.
Proof. exact (TRANS (@lem188163) (@lem188207)). Qed.
Lemma lem188251 : term242 = term241.
Proof. exact (SYM (@lem188250)). Qed.
Lemma lem188255 (h1 : term98) : term98.
Proof. exact (h1). Qed.
Lemma lem188261 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem188273 (b : nat) (a : nat) (h1 : term220 b a) : term220 b a.
Proof. exact (h1). Qed.
Lemma lem188276 (n : nat) : (term123 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem188281 (m : nat) (n : nat) : (term124 m n) = (term124 m n).
Proof. exact (eq_refl (term124 m n)). Qed.
Lemma lem188282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem188283 (n : nat) : (term125 n) = (term79 n).
Proof. exact (MK_COMB (@lem188282) (@lem188276 n)). Qed.
Lemma lem188284 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem188283 n) (@lem188281 m n)). Qed.
Lemma lem188285 (m : nat) (n : nat) : (term119 m n) = (term126 m n).
Proof. exact (@lem17265 (term61 n) (term124 m n)). Qed.
Lemma lem188286 (m : nat) (n : nat) : (term119 m n) = (term127 m n).
Proof. exact (TRANS (@lem188285 m n) (@lem188284 m n)). Qed.
Lemma lem188287 (m : nat) : (term120 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem188286 m n)). Qed.
Lemma lem188288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188289 (m : nat) : (term121 m) = (term129 m).
Proof. exact (MK_COMB (@lem188288) (@lem188287 m)). Qed.
Lemma lem188290 : term122 = term130.
Proof. exact (fun_ext (fun m : nat => @lem188289 m)). Qed.
Lemma lem188291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188348 : term98 = term131.
Proof. exact (MK_COMB (@lem188291) (@lem188290)). Qed.
Lemma lem188349 (h1 : term98) : term131.
Proof. exact (EQ_MP (@lem188348) (@lem188255 h1)). Qed.
Lemma lem188359 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem188381 (b : nat) (a : nat) (h1 : term220 b a) : term220 b a.
Proof. exact (h1). Qed.
Lemma lem188424 (m : nat) (n : nat) : (term127 m n) = (term127 m n).
Proof. exact (eq_refl (term127 m n)). Qed.
Lemma lem188425 (m : nat) : (term128 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem188424 m n)). Qed.
Lemma lem188426 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188427 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem188426) (@lem188425 m)). Qed.
Lemma lem188428 : term130 = term130.
Proof. exact (fun_ext (fun m : nat => @lem188427 m)). Qed.
Lemma lem188429 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188430 : term131 = term131.
Proof. exact (MK_COMB (@lem188429) (@lem188428)). Qed.
Lemma lem188431 (h1 : term98) : term131.
Proof. exact (EQ_MP (@lem188430) (@lem188349 h1)). Qed.
Lemma lem188435 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem188443 (b : nat) (a : nat) (h1 : term220 b a) : term220 b a.
Proof. exact (h1). Qed.
Lemma lem188461 (m : nat) (n : nat) : (term127 m n) = (term132 m n).
Proof. exact (@lem19490 (m = (term133 m n)) (n = (NUMERAL 0)) (term134 m n)). Qed.
Lemma lem188462 (m : nat) : (term128 m) = (term135 m).
Proof. exact (fun_ext (fun n : nat => @lem188461 m n)). Qed.
Lemma lem188463 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188464 (m : nat) : (term129 m) = (term136 m).
Proof. exact (MK_COMB (@lem188463) (@lem188462 m)). Qed.
Lemma lem188465 : term130 = term137.
Proof. exact (fun_ext (fun m : nat => @lem188464 m)). Qed.
Lemma lem188466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188468 : term131 = term138.
Proof. exact (MK_COMB (@lem188466) (@lem188465)). Qed.
Lemma lem188469 (h1 : term98) : term138.
Proof. exact (EQ_MP (@lem188468) (@lem188431 h1)). Qed.
Lemma lem188470 (_3829 : nat) (h1 : term98) : term139 _3829.
Proof. exact (@lem188469 h1 _3829). Qed.
Lemma lem188471 (_3829 : nat) : (term139 _3829) = (term136 _3829).
Proof. exact (eq_refl (term139 _3829)). Qed.
Lemma lem188472 (_3829 : nat) (h1 : term98) : term136 _3829.
Proof. exact (EQ_MP (@lem188471 _3829) (@lem188470 _3829 h1)). Qed.
Lemma lem188473 (_3829 : nat) (_3830 : nat) (h1 : term98) : term140 _3829 _3830.
Proof. exact (@lem188472 _3829 h1 _3830). Qed.
Lemma lem188474 (_3829 : nat) (_3830 : nat) : (term140 _3829 _3830) = (term132 _3829 _3830).
Proof. exact (eq_refl (term140 _3829 _3830)). Qed.
Lemma lem188475 (_3829 : nat) (_3830 : nat) (h1 : term98) : term132 _3829 _3830.
Proof. exact (EQ_MP (@lem188474 _3829 _3830) (@lem188473 _3829 _3830 h1)). Qed.
Lemma lem188479 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem188483 (b : nat) (a : nat) (h1 : term220 b a) : term220 b a.
Proof. exact (h1). Qed.
Lemma lem188495 (_3829 : nat) (_3830 : nat) (h1 : term98) : term243 _3829 _3830.
Proof. exact (proj2 (@lem188475 _3829 _3830 h1)). Qed.
Lemma lem188605 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem188606 (a : nat) (h1 : term61 a) : term153 a.
Proof. exact (fun h0 : a = (NUMERAL 0) => @lem188605 a h1). Qed.
Lemma lem188608 (p : Prop) : (term154 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem188609 (a : nat) : (term153 a) = (term61 a).
Proof. exact (@lem188608 (a = (NUMERAL 0))). Qed.
Lemma lem188610 (a : nat) (h1 : term61 a) : term61 a.
Proof. exact (EQ_MP (@lem188609 a) (@lem188606 a h1)). Qed.
Lemma lem188616 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem188617 (_3829 : nat) (_3830 : nat) : (term243 _3829 _3830) = (term244 _3829 _3830).
Proof. exact (@lem188616 (term134 _3829 _3830) (_3830 = (NUMERAL 0))). Qed.
Lemma lem188625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem188626 (_3829 : nat) (_3830 : nat) : (term245 _3829 _3830) = (term246 _3829 _3830).
Proof. exact (MK_COMB (@lem188625) (@lem188617 _3829 _3830)). Qed.
Lemma lem188634 (_3829 : nat) (_3830 : nat) : (term244 _3829 _3830) = (term244 _3829 _3830).
Proof. exact (eq_refl (term244 _3829 _3830)). Qed.
Lemma lem188635 (_3829 : nat) (_3830 : nat) : ((term243 _3829 _3830) = (term244 _3829 _3830)) = ((term244 _3829 _3830) = (term244 _3829 _3830)).
Proof. exact (MK_COMB (@lem188626 _3829 _3830) (@lem188634 _3829 _3830)). Qed.
Lemma lem188637 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem188638 (x : Prop) : (x = x) = True.
Proof. exact (@lem188637 Prop x). Qed.
Lemma lem188639 (_3829 : nat) (_3830 : nat) : ((term244 _3829 _3830) = (term244 _3829 _3830)) = True.
Proof. exact (@lem188638 (term244 _3829 _3830)). Qed.
Lemma lem188640 (_3829 : nat) (_3830 : nat) : ((term243 _3829 _3830) = (term244 _3829 _3830)) = True.
Proof. exact (TRANS (@lem188635 _3829 _3830) (@lem188639 _3829 _3830)). Qed.
Lemma lem188641 (_3829 : nat) (_3830 : nat) : True = ((term243 _3829 _3830) = (term244 _3829 _3830)).
Proof. exact (SYM (@lem188640 _3829 _3830)). Qed.
Lemma lem188642 (_3829 : nat) (_3830 : nat) : (term243 _3829 _3830) = (term244 _3829 _3830).
Proof. exact (EQ_MP (@lem188641 _3829 _3830) (@lem0)). Qed.
Lemma lem188643 (_3829 : nat) (_3830 : nat) (h1 : term98) : term244 _3829 _3830.
Proof. exact (EQ_MP (@lem188642 _3829 _3830) (@lem188495 _3829 _3830 h1)). Qed.
Lemma lem188645 (b : Prop) (a : Prop) : (a \/ b) = (term158 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem188648 (_3829 : nat) (_3830 : nat) : (term244 _3829 _3830) = (term247 _3829 _3830).
Proof. exact (@lem188645 (_3830 = (NUMERAL 0)) (term134 _3829 _3830)). Qed.
Lemma lem188651 (_3829 : nat) (_3830 : nat) (h1 : term98) : term247 _3829 _3830.
Proof. exact (EQ_MP (@lem188648 _3829 _3830) (@lem188643 _3829 _3830 h1)). Qed.
Lemma lem188652 (_3829 : nat) (a : nat) (h1 : term98) : term247 _3829 a.
Proof. exact (@lem188651 _3829 a h1). Qed.
Lemma lem188655 (_3829 : nat) (a : nat) (h1 : term98) (h2 : term61 a) : term134 _3829 a.
Proof. exact (@lem188652 _3829 a h1 (@lem188610 a h2)). Qed.
Lemma lem188656 (b : nat) (a : nat) (h1 : term98) (h2 : term61 a) : term134 b a.
Proof. exact (@lem188655 b a h1 h2). Qed.
Lemma lem188657 (b : nat) (a : nat) (h1 : term98) (h2 : term61 a) : term248 b a.
Proof. exact (fun h0 : term220 b a => @lem188656 b a h1 h2). Qed.
Lemma lem188659 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem188660 (b : nat) (a : nat) : (term248 b a) = (term134 b a).
Proof. exact (@lem188659 (term134 b a)). Qed.
Lemma lem188661 (b : nat) (a : nat) (h1 : term98) (h2 : term61 a) : term134 b a.
Proof. exact (EQ_MP (@lem188660 b a) (@lem188657 b a h1 h2)). Qed.
Lemma lem188664 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem188666 (b : nat) (a : nat) : (term220 b a) = (term249 b a).
Proof. exact (@lem188664 (term134 b a)). Qed.
Lemma lem188669 (b : nat) (a : nat) (h1 : term220 b a) : term249 b a.
Proof. exact (EQ_MP (@lem188666 b a) (@lem188483 b a h1)). Qed.
Lemma lem188672 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (@lem188669 b a h2 (@lem188661 b a h1 h3)). Qed.
Lemma lem188673 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : term204.
Proof. exact (fun h0 : ~ False => @lem188672 b a h1 h2 h3). Qed.
Lemma lem188675 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem188676 : term204 = False.
Proof. exact (@lem188675 False). Qed.
Lemma lem188677 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188676) (@lem188673 b a h1 h2 h3)). Qed.
Lemma lem188678 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term220 b a) = False.
Proof. exact (prop_ext (fun h4 : term220 b a => @lem188677 b a h1 h2 h3) (fun h4 : False => @lem188483 b a h2)). Qed.
Lemma lem188679 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188678 b a h1 h2 h3) (@lem188483 b a h2)). Qed.
Lemma lem188680 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h4 : term61 a => @lem188679 b a h1 h2 h3) (fun h4 : False => @lem188479 a h3)). Qed.
Lemma lem188681 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188680 b a h1 h2 h3) (@lem188479 a h3)). Qed.
Lemma lem188682 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term220 b a) = False.
Proof. exact (prop_ext (fun h4 : term220 b a => @lem188681 b a h1 h2 h3) (fun h4 : False => @lem188443 b a h2)). Qed.
Lemma lem188683 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188682 b a h1 h2 h3) (@lem188443 b a h2)). Qed.
Lemma lem188684 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h4 : term61 a => @lem188683 b a h1 h2 h3) (fun h4 : False => @lem188435 a h3)). Qed.
Lemma lem188685 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188684 b a h1 h2 h3) (@lem188435 a h3)). Qed.
Lemma lem188686 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term220 b a) = False.
Proof. exact (prop_ext (fun h4 : term220 b a => @lem188685 b a h1 h2 h3) (fun h4 : False => @lem188443 b a h2)). Qed.
Lemma lem188687 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188686 b a h1 h2 h3) (@lem188443 b a h2)). Qed.
Lemma lem188688 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h4 : term61 a => @lem188687 b a h1 h2 h3) (fun h4 : False => @lem188435 a h3)). Qed.
Lemma lem188689 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188688 b a h1 h2 h3) (@lem188435 a h3)). Qed.
Lemma lem188690 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term220 b a) = False.
Proof. exact (prop_ext (fun h4 : term220 b a => @lem188689 b a h1 h2 h3) (fun h4 : False => @lem188381 b a h2)). Qed.
Lemma lem188691 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188690 b a h1 h2 h3) (@lem188381 b a h2)). Qed.
Lemma lem188692 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h4 : term61 a => @lem188691 b a h1 h2 h3) (fun h4 : False => @lem188359 a h3)). Qed.
Lemma lem188693 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188692 b a h1 h2 h3) (@lem188359 a h3)). Qed.
Lemma lem188694 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term220 b a) = False.
Proof. exact (prop_ext (fun h4 : term220 b a => @lem188693 b a h1 h2 h3) (fun h4 : False => @lem188273 b a h2)). Qed.
Lemma lem188695 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188694 b a h1 h2 h3) (@lem188273 b a h2)). Qed.
Lemma lem188696 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h4 : term61 a => @lem188695 b a h1 h2 h3) (fun h4 : False => @lem188261 a h3)). Qed.
Lemma lem188697 (b : nat) (a : nat) (h1 : term98) (h2 : term220 b a) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem188696 b a h1 h2 h3) (@lem188261 a h3)). Qed.
Lemma lem188698 (b : nat) (a : nat) (h1 : term220 b a) (h2 : term61 a) : term96.
Proof. exact (fun h0 : term98 => @lem188697 b a h0 h1 h2). Qed.
Lemma lem188699 : term96 = term97.
Proof. exact (@lem69 term98). Qed.
Lemma lem188700 (b : nat) (a : nat) (h1 : term220 b a) (h2 : term61 a) : term97.
Proof. exact (EQ_MP (@lem188699) (@lem188698 b a h1 h2)). Qed.
Lemma lem188701 (b : nat) (a : nat) (h1 : term61 a) : term227 b a.
Proof. exact (fun h0 : term220 b a => @lem188700 b a h0 h1). Qed.
Lemma lem188702 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term229 n b a.
Proof. exact (fun h0 : term63 a n b => @lem188701 b a h1). Qed.
Lemma lem188703 (n : nat) (b : nat) (a : nat) : term230 n b a.
Proof. exact (fun h0 : term61 a => @lem188702 n b a h0). Qed.
Lemma lem188708 (b : nat) (a : nat) : term234 b a.
Proof. exact (fun n : nat => @lem188703 n b a). Qed.
Lemma lem188713 (a : nat) : term238 a.
Proof. exact (fun b : nat => @lem188708 b a). Qed.
Lemma lem188718 : term242.
Proof. exact (fun a : nat => @lem188713 a). Qed.
Lemma lem188719 : term241.
Proof. exact (EQ_MP (@lem188251) (@lem188718)). Qed.
Lemma lem188720 (a : nat) : term250 a.
Proof. exact (@lem188719 a). Qed.
Lemma lem188721 (a : nat) : (term250 a) = (term237 a).
Proof. exact (eq_refl (term250 a)). Qed.
Lemma lem188722 (a : nat) : term237 a.
Proof. exact (EQ_MP (@lem188721 a) (@lem188720 a)). Qed.
Lemma lem188723 (a : nat) (b : nat) : term251 a b.
Proof. exact (@lem188722 a b). Qed.
Lemma lem188724 (b : nat) (a : nat) : (term251 a b) = (term233 b a).
Proof. exact (eq_refl (term251 a b)). Qed.
Lemma lem188725 (b : nat) (a : nat) : term233 b a.
Proof. exact (EQ_MP (@lem188724 b a) (@lem188723 a b)). Qed.
Lemma lem188726 (b : nat) (a : nat) (n : nat) : term252 b a n.
Proof. exact (@lem188725 b a n). Qed.
Lemma lem188727 (n : nat) (b : nat) (a : nat) : (term252 b a n) = (term221 n b a).
Proof. exact (eq_refl (term252 b a n)). Qed.
Lemma lem188728 (n : nat) (b : nat) (a : nat) : term221 n b a.
Proof. exact (EQ_MP (@lem188727 n b a) (@lem188726 b a n)). Qed.
Lemma lem188730 (n : nat) (b : nat) (a : nat) : term221 n b a.
Proof. exact (@lem188093 n b a (@lem188728 n b a)). Qed.
Lemma lem188731 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term228 n b a.
Proof. exact (@lem188730 n b a (@lem187009 a h1)). Qed.
Lemma lem188732 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term226 b a.
Proof. exact (@lem188731 n b a h1 (@lem187011 a n b h2)). Qed.
Lemma lem188733 (a : nat) (n : nat) (b : nat) (h1 : term220 b a) (h2 : term61 a) (h3 : term63 a n b) : term96.
Proof. exact (@lem188732 a n b h2 h3 (@lem188078 b a h1)). Qed.
Lemma lem188734 (a : nat) (n : nat) (b : nat) (h1 : term220 b a) (h2 : term61 a) (h3 : term63 a n b) : False.
Proof. exact (@lem188733 a n b h1 h2 h3 (@lem157261)). Qed.
Lemma lem188735 (a : nat) (n : nat) (b : nat) (h1 : term220 b a) (h2 : term61 a) (h3 : term63 a n b) : (term220 b a) = False.
Proof. exact (prop_ext (fun h4 : term220 b a => @lem188734 a n b h1 h2 h3) (fun h4 : False => @lem188078 b a h1)). Qed.
Lemma lem188736 (a : nat) (n : nat) (b : nat) (h1 : term220 b a) (h2 : term61 a) (h3 : term63 a n b) : False.
Proof. exact (EQ_MP (@lem188735 a n b h1 h2 h3) (@lem188078 b a h1)). Qed.
Lemma lem188737 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term219 b a.
Proof. exact (fun h0 : term220 b a => @lem188736 a n b h0 h1 h2). Qed.
Lemma lem188738 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term134 b a.
Proof. exact (EQ_MP (@lem188077 b a) (@lem188737 a n b h1 h2)). Qed.
Lemma lem188739 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term217 b a.
Proof. exact (EQ_MP (@lem188073 b a) (@lem188738 a n b h1 h2)). Qed.
Lemma lem188740 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term253 n b a.
Proof. exact (conj (@lem188031 a n b h1 h2) (@lem188739 a n b h1 h2)). Qed.
Lemma lem188741 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term254 n b a.
Proof. exact (ex_intro (term255 n b a) (term133 b a) (@lem188740 a n b h1 h2)). Qed.
Lemma lem188742 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term85 n b a.
Proof. exact (@lem187083 n b a (@lem188741 a n b h1 h2)). Qed.
Lemma lem188743 (m : nat) : term256 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem188744 (m : nat) : (term256 m) = (term257 m).
Proof. exact (eq_refl (term256 m)). Qed.
Lemma lem188745 (m : nat) : term257 m.
Proof. exact (EQ_MP (@lem188744 m) (@lem188743 m)). Qed.
Lemma lem188746 (m : nat) (n : nat) : term258 m n.
Proof. exact (@lem188745 m n). Qed.
Lemma lem188747 (m : nat) (n : nat) : (term258 m n) = ((term259 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term258 m n)). Qed.
Lemma lem188749 (m : nat) : term260 m.
Proof. exact (@lem186874 m). Qed.
Lemma lem188750 (m : nat) : (term260 m) = ((term0 m) = (S m)).
Proof. exact (eq_refl (term260 m)). Qed.
Lemma lem188752 (m : nat) : term261 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem188753 (m : nat) : (term261 m) = (term262 m).
Proof. exact (eq_refl (term261 m)). Qed.
Lemma lem188754 (m : nat) : term262 m.
Proof. exact (EQ_MP (@lem188753 m) (@lem188752 m)). Qed.
Lemma lem188755 (m : nat) (n : nat) : term263 m n.
Proof. exact (@lem188754 m n). Qed.
Lemma lem188756 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (eq_refl (term263 m n)). Qed.
Lemma lem188757 (m : nat) (n : nat) : term264 m n.
Proof. exact (EQ_MP (@lem188756 m n) (@lem188755 m n)). Qed.
Lemma lem188758 (m : nat) (n : nat) (p : nat) : term265 m n p.
Proof. exact (@lem188757 m n p). Qed.
Lemma lem188759 (m : nat) (n : nat) (p : nat) : (term265 m n p) = ((term266 n m p) = (term267 m n p)).
Proof. exact (eq_refl (term265 m n p)). Qed.
Lemma lem188761 (a : nat) : term76 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem188779 (m : nat) (n : nat) (p : nat) : (term266 n m p) = (term267 m n p).
Proof. exact (EQ_MP (@lem188759 m n p) (@lem188758 m n p)). Qed.
Lemma lem188780 (n : nat) (b : nat) (a : nat) : (term85 n b a) = (term268 n b a).
Proof. exact (@lem188779 a n (term269 b a)). Qed.
Lemma lem188784 (a : nat) (h1 : term61 a) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem188761 a (@lem187009 a h1)). Qed.
Lemma lem188785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem188786 (a : nat) (h1 : term61 a) : (term61 a) = (~ False).
Proof. exact (MK_COMB (@lem188785) (@lem188784 a h1)). Qed.
Lemma lem188788 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem188789 (a : nat) (h1 : term61 a) : (term61 a) = True.
Proof. exact (TRANS (@lem188786 a h1) (@lem188788)). Qed.
Lemma lem188790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem188791 (a : nat) (h1 : term61 a) : (term270 a) = (and True).
Proof. exact (MK_COMB (@lem188790) (@lem188789 a h1)). Qed.
Lemma lem188793 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem188750 m) (@lem188749 m)). Qed.
Lemma lem188794 (b : nat) (a : nat) : (term269 b a) = (term271 b a).
Proof. exact (@lem188793 (Nat.div b a)). Qed.
Lemma lem188795 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem188796 (n : nat) (b : nat) (a : nat) : (term272 n b a) = (term273 n b a).
Proof. exact (MK_COMB (@lem188795 n) (@lem188794 b a)). Qed.
Lemma lem188798 (m : nat) (n : nat) : (term259 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem188747 m n) (@lem188746 m n)). Qed.
Lemma lem188799 (n : nat) (b : nat) (a : nat) : (term273 n b a) = (term62 n b a).
Proof. exact (@lem188798 n (Nat.div b a)). Qed.
Lemma lem188800 (n : nat) (b : nat) (a : nat) : (term272 n b a) = (term62 n b a).
Proof. exact (TRANS (@lem188796 n b a) (@lem188799 n b a)). Qed.
Lemma lem188801 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term268 n b a) = (term274 n b a).
Proof. exact (MK_COMB (@lem188791 a h1) (@lem188800 n b a)). Qed.
Lemma lem188803 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem188804 (n : nat) (b : nat) (a : nat) : (term274 n b a) = (term62 n b a).
Proof. exact (@lem188803 (term62 n b a)). Qed.
Lemma lem188805 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term268 n b a) = (term62 n b a).
Proof. exact (TRANS (@lem188801 n b a h1) (@lem188804 n b a)). Qed.
Lemma lem188806 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term85 n b a) = (term62 n b a).
Proof. exact (TRANS (@lem188780 n b a) (@lem188805 n b a h1)). Qed.
Lemma lem188807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem188808 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term275 n b a) = (term276 n b a).
Proof. exact (MK_COMB (@lem188807) (@lem188806 n b a h1)). Qed.
Lemma lem188809 (n : nat) (b : nat) (a : nat) : (term62 n b a) = (term62 n b a).
Proof. exact (eq_refl (term62 n b a)). Qed.
Lemma lem188810 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term277 n b a) = (term278 n b a).
Proof. exact (MK_COMB (@lem188808 n b a h1) (@lem188809 n b a)). Qed.
Lemma lem188812 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem188813 (n : nat) (b : nat) (a : nat) : (term278 n b a) = True.
Proof. exact (@lem188812 (term62 n b a)). Qed.
Lemma lem188814 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term277 n b a) = True.
Proof. exact (TRANS (@lem188810 n b a h1) (@lem188813 n b a)). Qed.
Lemma lem188815 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : True = (term277 n b a).
Proof. exact (SYM (@lem188814 n b a h1)). Qed.
Lemma lem188816 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term277 n b a.
Proof. exact (EQ_MP (@lem188815 n b a h1) (@lem0)). Qed.
Lemma lem188817 (n : nat) (b : nat) (a : nat) (h1 : term61 a) (h2 : term85 n b a) : term62 n b a.
Proof. exact (@lem188816 n b a h1 (@lem187080 n b a h2)). Qed.
Lemma lem188818 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : (term85 n b a) = (term62 n b a).
Proof. exact (prop_ext (fun h3 : term85 n b a => @lem188817 n b a h1 h3) (fun h3 : term62 n b a => @lem188742 a n b h1 h2)). Qed.
Lemma lem188819 (a : nat) (n : nat) (b : nat) (h1 : term61 a) (h2 : term63 a n b) : term62 n b a.
Proof. exact (EQ_MP (@lem188818 a n b h1 h2) (@lem188742 a n b h1 h2)). Qed.
Lemma lem188820 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term279 n b a.
Proof. exact (fun h0 : term63 a n b => @lem188819 a n b h1 h0). Qed.
Lemma lem188821 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term280 a n b.
Proof. exact (fun h0 : term62 n b a => @lem187079 n b a h1 h0). Qed.
Lemma lem188822 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : term281 n b a.
Proof. exact (conj (@lem188821 n b a h1) (@lem188820 n b a h1)). Qed.
Lemma lem188823 (a : nat) (n : nat) (b : nat) : (term281 n b a) = ((term62 n b a) = (term63 a n b)).
Proof. exact (@lem32 (term62 n b a) (term63 a n b)). Qed.
Lemma lem188824 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term62 n b a) = (term63 a n b).
Proof. exact (EQ_MP (@lem188823 a n b) (@lem188822 n b a h1)). Qed.
Lemma lem188825 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term61 a) = ((term62 n b a) = (term63 a n b)).
Proof. exact (prop_ext (fun h2 : term61 a => @lem188824 n b a h1) (fun h2 : (term62 n b a) = (term63 a n b) => @lem187009 a h1)). Qed.
Lemma lem188826 (n : nat) (b : nat) (a : nat) (h1 : term61 a) : (term62 n b a) = (term63 a n b).
Proof. exact (EQ_MP (@lem188825 n b a h1) (@lem187009 a h1)). Qed.
Lemma lem188827 (a : nat) (n : nat) (b : nat) : term282 a n b.
Proof. exact (fun h0 : term61 a => @lem188826 n b a h0). Qed.
Lemma lem188832 (a : nat) (b : nat) : term283 a b.
Proof. exact (fun n : nat => @lem188827 a n b). Qed.
Lemma lem188837 (a : nat) : term284 a.
Proof. exact (fun b : nat => @lem188832 a b). Qed.
Lemma lem188842 : term285.
Proof. exact (fun a : nat => @lem188837 a). Qed.
