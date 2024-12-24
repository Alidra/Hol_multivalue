Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_MULT2_term_abbrevs.
Require Import LET_TRANS_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LT_IMP_LE_spec.
Require Import LT_MULT_LCANCEL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10568_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm89994_spec.
Lemma lem105971 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem105972 (m : nat) : term1 m.
Proof. exact (@lem105971 m). Qed.
Lemma lem105973 (m : nat) : (term1 m) = ((term2 m) = False).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem105975 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem105976 (m : nat) (h1 : term3) : term4 m.
Proof. exact (@lem105975 h1 m). Qed.
Lemma lem105977 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem105978 (m : nat) (h1 : term3) : term5 m.
Proof. exact (EQ_MP (@lem105977 m) (@lem105976 m h1)). Qed.
Lemma lem105979 (m : nat) (n : nat) (h1 : term3) : term6 m n.
Proof. exact (@lem105978 m h1 n). Qed.
Lemma lem105980 (n : nat) (m : nat) : (term6 m n) = (term7 n m).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem105981 (n : nat) (m : nat) (h1 : term3) : term7 n m.
Proof. exact (EQ_MP (@lem105980 n m) (@lem105979 m n h1)). Qed.
Lemma lem105982 (n : nat) (m : nat) (p : nat) (h1 : term3) : term8 n m p.
Proof. exact (@lem105981 n m h1 p). Qed.
Lemma lem105983 (n : nat) (m : nat) (p : nat) : (term8 n m p) = (term9 n m p).
Proof. exact (eq_refl (term8 n m p)). Qed.
Lemma lem105984 (n : nat) (m : nat) (p : nat) (h1 : term3) : term9 n m p.
Proof. exact (EQ_MP (@lem105983 n m p) (@lem105982 n m p h1)). Qed.
Lemma lem105985 (m : nat) (n : nat) (p : nat) (h1 : term10 m n p) : term10 m n p.
Proof. exact (h1). Qed.
Lemma lem105986 (m : nat) (n : nat) (p : nat) (h1 : term3) (h2 : term10 m n p) : Peano.lt m p.
Proof. exact (@lem105984 n m p h1 (@lem105985 m n p h2)). Qed.
Lemma lem105987 (m : nat) (n : nat) (p : nat) (h1 : term10 m n p) : term11 m p.
Proof. exact (fun h0 : term3 => @lem105986 m n p h0 h1). Qed.
Lemma lem105988 (m : nat) (p : nat) (h1 : term12 m p) : term12 m p.
Proof. exact (h1). Qed.
Lemma lem105989 (m : nat) (p : nat) (h1 : term12 m p) : term11 m p.
Proof. exact (ex_elim (@lem105988 m p h1) (fun n : nat => fun h0 : term13 m p n => @lem105987 m n p h0)). Qed.
Lemma lem105990 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem105991 (m : nat) (p : nat) (h1 : term3) (h2 : term12 m p) : Peano.lt m p.
Proof. exact (@lem105989 m p h2 (@lem105990 h1)). Qed.
Lemma lem105992 (m : nat) (p : nat) (h1 : term3) : term14 m p.
Proof. exact (fun h0 : term12 m p => @lem105991 m p h1 h0). Qed.
Lemma lem105993 (m : nat) (h1 : term3) : term15 m.
Proof. exact (fun p : nat => @lem105992 m p h1). Qed.
Lemma lem105994 (h1 : term3) : term16.
Proof. exact (fun m : nat => @lem105993 m h1). Qed.
Lemma lem105995 : term17.
Proof. exact (fun h0 : term3 => @lem105994 h0). Qed.
Lemma lem105996 : term16.
Proof. exact (@lem105995 (@lem95173)). Qed.
Lemma lem105997 (m : nat) : term18 m.
Proof. exact (@lem105996 m). Qed.
Lemma lem105998 (m : nat) : (term18 m) = (term15 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem105999 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem105998 m) (@lem105997 m)). Qed.
Lemma lem106000 (m : nat) (p : nat) : term19 m p.
Proof. exact (@lem105999 m p). Qed.
Lemma lem106001 (m : nat) (p : nat) : (term19 m p) = (term14 m p).
Proof. exact (eq_refl (term19 m p)). Qed.
Lemma lem106003 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term20 m n p q) : term20 m n p q.
Proof. exact (h1). Qed.
Lemma lem106004 (p : nat) (q : nat) (h1 : Peano.lt p q) : Peano.lt p q.
Proof. exact (h1). Qed.
Lemma lem106005 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem106007 (m : nat) (p : nat) : term14 m p.
Proof. exact (EQ_MP (@lem106001 m p) (@lem106000 m p)). Qed.
Lemma lem106008 (m : nat) (p : nat) (n : nat) (q : nat) : term21 m p n q.
Proof. exact (@lem106007 (Nat.mul m p) (Nat.mul n q)). Qed.
Lemma lem106009 (m : nat) : term22 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem106010 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem106011 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem106010 m) (@lem106009 m)). Qed.
Lemma lem106012 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem106011 m n). Qed.
Lemma lem106013 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem106014 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem106013 m n) (@lem106012 m n)). Qed.
Lemma lem106015 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (@lem106014 m n p). Qed.
Lemma lem106016 (m : nat) (n : nat) (p : nat) : (term26 m n p) = ((term27 n m p) = (term28 m n p)).
Proof. exact (eq_refl (term26 m n p)). Qed.
Lemma lem106018 (m : nat) : term29 m.
Proof. exact (@lem98439 m). Qed.
Lemma lem106019 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem106020 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem106019 m) (@lem106018 m)). Qed.
Lemma lem106021 (m : nat) (n : nat) : term31 m n.
Proof. exact (@lem106020 m n). Qed.
Lemma lem106022 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem106023 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem106022 m n) (@lem106021 m n)). Qed.
Lemma lem106024 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem106025 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem106023 m n (@lem106024 m n h1)). Qed.
Lemma lem106026 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem106027 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem106026 m n) (@lem106025 m n h1)). Qed.
Lemma lem106033 (m : nat) : term33 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem106034 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem106035 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem106034 m) (@lem106033 m)). Qed.
Lemma lem106036 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem106035 m n). Qed.
Lemma lem106037 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem106038 (m : nat) (n : nat) : term36 m n.
Proof. exact (EQ_MP (@lem106037 m n) (@lem106036 m n)). Qed.
Lemma lem106039 (m : nat) (n : nat) (p : nat) : term37 m n p.
Proof. exact (@lem106038 m n p). Qed.
Lemma lem106040 (m : nat) (n : nat) (p : nat) : (term37 m n p) = ((term38 m n p) = (term39 m n p)).
Proof. exact (eq_refl (term37 m n p)). Qed.
Lemma lem106042 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem106044 (p : nat) (q : nat) : (Peano.lt p q) = ((Peano.lt p q) = True).
Proof. exact (@lem7 (Peano.lt p q)). Qed.
Lemma lem106049 (m : nat) (n : nat) (p : nat) : (term38 m n p) = (term39 m n p).
Proof. exact (EQ_MP (@lem106040 m n p) (@lem106039 m n p)). Qed.
Lemma lem106053 (m : nat) (n : nat) : term40 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem106027 m n h0). Qed.
Lemma lem106055 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem106042 m n) (@lem106005 m n h1)). Qed.
Lemma lem106056 (m : nat) (n : nat) (h1 : Peano.lt m n) : True = (Peano.lt m n).
Proof. exact (SYM (@lem106055 m n h1)). Qed.
Lemma lem106057 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem106056 m n h1) (@lem0)). Qed.
Lemma lem106058 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.le m n) = True.
Proof. exact (@lem106053 m n (@lem106057 m n h1)). Qed.
Lemma lem106059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem106060 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term41 m n) = (or True).
Proof. exact (MK_COMB (@lem106059) (@lem106058 m n h1)). Qed.
Lemma lem106063 (p : nat) : (p = (NUMERAL 0)) = (p = (NUMERAL 0)).
Proof. exact (eq_refl (p = (NUMERAL 0))). Qed.
Lemma lem106064 (p : nat) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term39 m n p) = (term42 p).
Proof. exact (MK_COMB (@lem106060 m n h1) (@lem106063 p)). Qed.
Lemma lem106066 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem106067 (p : nat) : (term42 p) = True.
Proof. exact (@lem106066 (p = (NUMERAL 0))). Qed.
Lemma lem106068 (p : nat) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term39 m n p) = True.
Proof. exact (TRANS (@lem106064 p m n h1) (@lem106067 p)). Qed.
Lemma lem106069 (p : nat) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term38 m n p) = True.
Proof. exact (TRANS (@lem106049 m n p) (@lem106068 p m n h1)). Qed.
Lemma lem106070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106071 (p : nat) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term43 m n p) = (and True).
Proof. exact (MK_COMB (@lem106070) (@lem106069 p m n h1)). Qed.
Lemma lem106073 (m : nat) (n : nat) (p : nat) : (term27 n m p) = (term28 m n p).
Proof. exact (EQ_MP (@lem106016 m n p) (@lem106015 m n p)). Qed.
Lemma lem106074 (n : nat) (p : nat) (q : nat) : (term27 p n q) = (term28 n p q).
Proof. exact (@lem106073 n p q). Qed.
Lemma lem106080 (p : nat) (q : nat) (h1 : Peano.lt p q) : (Peano.lt p q) = True.
Proof. exact (EQ_MP (@lem106044 p q) (@lem106004 p q h1)). Qed.
Lemma lem106081 (n : nat) : (term44 n) = (term44 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem106082 (n : nat) (p : nat) (q : nat) (h1 : Peano.lt p q) : (term28 n p q) = (term45 n).
Proof. exact (MK_COMB (@lem106081 n) (@lem106080 p q h1)). Qed.
Lemma lem106084 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem106085 (n : nat) : (term45 n) = (term46 n).
Proof. exact (@lem106084 (term46 n)). Qed.
Lemma lem106088 (n : nat) (p : nat) (q : nat) (h1 : Peano.lt p q) : (term28 n p q) = (term46 n).
Proof. exact (TRANS (@lem106082 n p q h1) (@lem106085 n)). Qed.
Lemma lem106089 (n : nat) (p : nat) (q : nat) (h1 : Peano.lt p q) : (term27 p n q) = (term46 n).
Proof. exact (TRANS (@lem106074 n p q) (@lem106088 n p q h1)). Qed.
Lemma lem106090 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : (term47 m p n q) = (term48 n).
Proof. exact (MK_COMB (@lem106071 p m n h1) (@lem106089 n p q h2)). Qed.
Lemma lem106092 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem106093 (n : nat) : (term48 n) = (term46 n).
Proof. exact (@lem106092 (term46 n)). Qed.
Lemma lem106096 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : (term47 m p n q) = (term46 n).
Proof. exact (TRANS (@lem106090 m n p q h1 h2) (@lem106093 n)). Qed.
Lemma lem106097 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : (term46 n) = (term47 m p n q).
Proof. exact (SYM (@lem106096 m n p q h1 h2)). Qed.
Lemma lem106098 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (@lem10568 (term46 n) (Peano.lt m n)). Qed.
Lemma lem106099 (m : nat) (n : nat) : (term50 m n) = (term49 m n).
Proof. exact (SYM (@lem106098 m n)). Qed.
Lemma lem106103 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term51 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem106104 (p : Prop) (q : Prop) (p' : Prop) : term52 p q p'.
Proof. exact (fun q' : Prop => @lem106103 p q p' q'). Qed.
Lemma lem106105 (p : Prop) (q : Prop) : term53 p q.
Proof. exact (fun p' : Prop => @lem106104 p q p'). Qed.
Lemma lem106106 (m : nat) (n : nat) : term54 m n.
Proof. exact (@lem106105 (term55 n) (term56 m n)). Qed.
Lemma lem106107 (m : nat) (n : nat) (p' : Prop) : term57 m n p'.
Proof. exact (@lem106106 m n p'). Qed.
Lemma lem106108 (m : nat) (n : nat) (p' : Prop) : (term57 m n p') = (term58 m n p').
Proof. exact (eq_refl (term57 m n p')). Qed.
Lemma lem106109 (m : nat) (n : nat) (p' : Prop) : term58 m n p'.
Proof. exact (EQ_MP (@lem106108 m n p') (@lem106107 m n p')). Qed.
Lemma lem106110 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term59 m n p' q'.
Proof. exact (@lem106109 m n p' q'). Qed.
Lemma lem106111 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term59 m n p' q') = (term60 m n p' q').
Proof. exact (eq_refl (term59 m n p' q')). Qed.
Lemma lem106112 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term60 m n p' q'.
Proof. exact (EQ_MP (@lem106111 m n p' q') (@lem106110 m n p' q')). Qed.
Lemma lem106114 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem106115 (n : nat) : (term55 n) = (n = (NUMERAL 0)).
Proof. exact (@lem106114 (n = (NUMERAL 0))). Qed.
Lemma lem106118 (m : nat) (n : nat) (q' : Prop) : term62 m n q'.
Proof. exact (@lem106112 m n (n = (NUMERAL 0)) q'). Qed.
Lemma lem106119 (m : nat) (n : nat) (q' : Prop) : term63 m n q'.
Proof. exact (@lem106118 m n q' (@lem106115 n)). Qed.
Lemma lem106122 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem106123 (m : nat) : (Peano.lt m) = (Peano.lt m).
Proof. exact (eq_refl (Peano.lt m)). Qed.
Lemma lem106124 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt m n) = (term2 m).
Proof. exact (MK_COMB (@lem106123 m) (@lem106122 n h1)). Qed.
Lemma lem106126 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem105973 m) (@lem105972 m)). Qed.
Lemma lem106127 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt m n) = False.
Proof. exact (TRANS (@lem106124 m n h1) (@lem106126 m)). Qed.
Lemma lem106128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem106129 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term56 m n) = (~ False).
Proof. exact (MK_COMB (@lem106128) (@lem106127 m n h1)). Qed.
Lemma lem106131 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem106132 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term56 m n) = True.
Proof. exact (TRANS (@lem106129 m n h1) (@lem106131)). Qed.
Lemma lem106133 (m : nat) (n : nat) : term64 m n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem106132 m n h0). Qed.
Lemma lem106134 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem106119 m n True). Qed.
Lemma lem106135 (m : nat) (n : nat) : (term50 m n) = (term66 n).
Proof. exact (@lem106134 m n (@lem106133 m n)). Qed.
Lemma lem106139 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem106140 (n : nat) : (term66 n) = True.
Proof. exact (@lem106139 (n = (NUMERAL 0))). Qed.
Lemma lem106141 (m : nat) (n : nat) : (term50 m n) = True.
Proof. exact (TRANS (@lem106135 m n) (@lem106140 n)). Qed.
Lemma lem106142 (m : nat) (n : nat) : True = (term50 m n).
Proof. exact (SYM (@lem106141 m n)). Qed.
Lemma lem106143 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem106142 m n) (@lem0)). Qed.
Lemma lem106144 (m : nat) (n : nat) : term49 m n.
Proof. exact (EQ_MP (@lem106099 m n) (@lem106143 m n)). Qed.
Lemma lem106145 (m : nat) (n : nat) (h1 : Peano.lt m n) : term46 n.
Proof. exact (@lem106144 m n (@lem106005 m n h1)). Qed.
Lemma lem106146 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : term47 m p n q.
Proof. exact (EQ_MP (@lem106097 m n p q h1 h2) (@lem106145 m n h1)). Qed.
Lemma lem106147 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : term67 m p n q.
Proof. exact (ex_intro (term68 m p n q) (Nat.mul n p) (@lem106146 m n p q h1 h2)). Qed.
Lemma lem106148 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : term69 m p n q.
Proof. exact (@lem106008 m p n q (@lem106147 m n p q h1 h2)). Qed.
Lemma lem106149 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term20 m n p q) : Peano.lt p q.
Proof. exact (proj2 (@lem106003 m n p q h1)). Qed.
Lemma lem106150 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term20 m n p q) : Peano.lt m n.
Proof. exact (proj1 (@lem106003 m n p q h1)). Qed.
Lemma lem106151 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : (Peano.lt p q) = (term69 m p n q).
Proof. exact (prop_ext (fun h3 : Peano.lt p q => @lem106148 m n p q h1 h2) (fun h3 : term69 m p n q => @lem106004 p q h2)). Qed.
Lemma lem106152 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : term69 m p n q.
Proof. exact (EQ_MP (@lem106151 m n p q h1 h2) (@lem106004 p q h2)). Qed.
Lemma lem106153 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : (Peano.lt m n) = (term69 m p n q).
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem106152 m n p q h1 h2) (fun h3 : term69 m p n q => @lem106005 m n h1)). Qed.
Lemma lem106154 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : Peano.lt m n) (h2 : Peano.lt p q) : term69 m p n q.
Proof. exact (EQ_MP (@lem106153 m n p q h1 h2) (@lem106005 m n h1)). Qed.
Lemma lem106155 (p : nat) (q : nat) (m : nat) (n : nat) (h1 : term20 m n p q) (h2 : Peano.lt m n) : (Peano.lt p q) = (term69 m p n q).
Proof. exact (prop_ext (fun h3 : Peano.lt p q => @lem106154 m n p q h2 h3) (fun h3 : term69 m p n q => @lem106149 m n p q h1)). Qed.
Lemma lem106156 (p : nat) (q : nat) (m : nat) (n : nat) (h1 : term20 m n p q) (h2 : Peano.lt m n) : term69 m p n q.
Proof. exact (EQ_MP (@lem106155 p q m n h1 h2) (@lem106149 m n p q h1)). Qed.
Lemma lem106157 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term20 m n p q) : (Peano.lt m n) = (term69 m p n q).
Proof. exact (prop_ext (fun h2 : Peano.lt m n => @lem106156 p q m n h1 h2) (fun h2 : term69 m p n q => @lem106150 m n p q h1)). Qed.
Lemma lem106158 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term20 m n p q) : term69 m p n q.
Proof. exact (EQ_MP (@lem106157 m n p q h1) (@lem106150 m n p q h1)). Qed.
Lemma lem106159 (m : nat) (p : nat) (n : nat) (q : nat) : term70 m p n q.
Proof. exact (fun h0 : term20 m n p q => @lem106158 m n p q h0). Qed.
Lemma lem106164 (m : nat) (p : nat) (n : nat) : term71 m p n.
Proof. exact (fun q : nat => @lem106159 m p n q). Qed.
Lemma lem106169 (m : nat) (n : nat) : term72 m n.
Proof. exact (fun p : nat => @lem106164 m p n). Qed.
Lemma lem106174 (m : nat) : term73 m.
Proof. exact (fun n : nat => @lem106169 m n). Qed.
Lemma lem106179 : term74.
Proof. exact (fun m : nat => @lem106174 m). Qed.
