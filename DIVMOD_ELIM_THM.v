Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVMOD_ELIM_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIVISION_spec.
Require Import DIVMOD_UNIQ_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm155916_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem257918 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem257919 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem257920 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem257919 t1) (@lem257918 t1)). Qed.
Lemma lem257921 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem257920 t1 t2). Qed.
Lemma lem257922 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem257923 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem257922 t1 t2) (@lem257921 t1 t2)). Qed.
Lemma lem257924 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem257923 t1 t2 t3). Qed.
Lemma lem257925 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem257926 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem257925 t1 t2 t3) (@lem257924 t1 t2 t3)). Qed.
Lemma lem257927 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem257926 t1 t2 t3)). Qed.
Lemma lem257928 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem257929 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem257928 h1 m). Qed.
Lemma lem257930 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem257931 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem257930 m) (@lem257929 m h1)). Qed.
Lemma lem257932 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem257931 m h1 n). Qed.
Lemma lem257933 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem257934 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (EQ_MP (@lem257933 m n) (@lem257932 m n h1)). Qed.
Lemma lem257935 (n : nat) (h1 : term12 n) : term12 n.
Proof. exact (h1). Qed.
Lemma lem257936 (m : nat) (n : nat) (h1 : term7) (h2 : term12 n) : term13 m n.
Proof. exact (@lem257934 m n h1 (@lem257935 n h2)). Qed.
Lemma lem257937 (n : nat) (h1 : term7) (h2 : term12 n) : term14 n.
Proof. exact (fun m : nat => @lem257936 m n h1 h2). Qed.
Lemma lem257938 (n : nat) (h1 : term7) : term15 n.
Proof. exact (fun h0 : term12 n => @lem257937 n h1 h0). Qed.
Lemma lem257939 (h1 : term7) : term16.
Proof. exact (fun n : nat => @lem257938 n h1). Qed.
Lemma lem257940 : term17.
Proof. exact (fun h0 : term7 => @lem257939 h0). Qed.
Lemma lem257941 : term16.
Proof. exact (@lem257940 (@lem157261)). Qed.
Lemma lem257942 (n : nat) : term18 n.
Proof. exact (@lem257941 n). Qed.
Lemma lem257943 (n : nat) : (term18 n) = (term15 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem257945 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem257946 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem257947 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem257946 t1) (@lem257945 t1)). Qed.
Lemma lem257948 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem257947 t1 t2). Qed.
Lemma lem257949 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem257950 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem257949 t1 t2) (@lem257948 t1 t2)). Qed.
Lemma lem257951 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem257950 t1 t2 t3). Qed.
Lemma lem257952 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem257953 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem257952 t1 t2 t3) (@lem257951 t1 t2 t3)). Qed.
Lemma lem257954 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem257953 t1 t2 t3)). Qed.
Lemma lem257955 (n : nat) : term19 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem257956 (n : nat) : (term19 n) = (term20 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem257957 (n : nat) : term20 n.
Proof. exact (EQ_MP (@lem257956 n) (@lem257955 n)). Qed.
Lemma lem257958 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem257959 (n : nat) (h1 : term12 n) : term12 n.
Proof. exact (h1). Qed.
Lemma lem257963 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem257964 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem257965 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term21 m).
Proof. exact (MK_COMB (@lem257964 m) (@lem257963 n h1)). Qed.
Lemma lem257966 (P : type1605) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem257967 (P : type1605) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term22 P m n) = (term23 P m).
Proof. exact (MK_COMB (@lem257966 P) (@lem257965 m n h1)). Qed.
Lemma lem257969 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem257970 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem257971 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term24 m).
Proof. exact (MK_COMB (@lem257970 m) (@lem257969 n h1)). Qed.
Lemma lem257972 (P : type1605) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 P m n) = (term26 P m).
Proof. exact (MK_COMB (@lem257967 P m n h1) (@lem257971 m n h1)). Qed.
Lemma lem257973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem257974 (P : type1605) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term27 P m n) = (term28 P m).
Proof. exact (MK_COMB (@lem257973) (@lem257972 P m n h1)). Qed.
Lemma lem257992 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem257993 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem257994 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term29.
Proof. exact (MK_COMB (@lem257993) (@lem257992 n h1)). Qed.
Lemma lem257995 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem257996 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem257994 n h1) (@lem257995)). Qed.
Lemma lem257998 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem257999 (x : nat) : (x = x) = True.
Proof. exact (@lem257998 nat x). Qed.
Lemma lem258000 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem257999 (NUMERAL 0)). Qed.
Lemma lem258001 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem257996 n h1) (@lem258000)). Qed.
Lemma lem258002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258003 (n : nat) (h1 : n = (NUMERAL 0)) : (term30 n) = (and True).
Proof. exact (MK_COMB (@lem258002) (@lem258001 n h1)). Qed.
Lemma lem258010 (q : nat) (r : nat) (m : nat) : (term31 q r m) = (term31 q r m).
Proof. exact (eq_refl (term31 q r m)). Qed.
Lemma lem258011 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term32 n q r m) = (term33 q r m).
Proof. exact (MK_COMB (@lem258003 n h1) (@lem258010 q r m)). Qed.
Lemma lem258013 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem258014 (q : nat) (r : nat) (m : nat) : (term33 q r m) = (term31 q r m).
Proof. exact (@lem258013 (term31 q r m)). Qed.
Lemma lem258021 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term32 n q r m) = (term31 q r m).
Proof. exact (TRANS (@lem258011 q r m n h1) (@lem258014 q r m)). Qed.
Lemma lem258022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258023 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 n q r m) = (term35 q r m).
Proof. exact (MK_COMB (@lem258022) (@lem258021 q r m n h1)). Qed.
Lemma lem258029 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem258030 (q : nat) : (Nat.mul q) = (Nat.mul q).
Proof. exact (eq_refl (Nat.mul q)). Qed.
Lemma lem258031 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul q n) = (term36 q).
Proof. exact (MK_COMB (@lem258030 q) (@lem258029 n h1)). Qed.
Lemma lem258032 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem258033 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term37 q n) = (term38 q).
Proof. exact (MK_COMB (@lem258032) (@lem258031 q n h1)). Qed.
Lemma lem258034 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem258035 (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term39 q n r) = (term40 q r).
Proof. exact (MK_COMB (@lem258033 q n h1) (@lem258034 r)). Qed.
Lemma lem258036 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem258037 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (m = (term39 q n r)) = (m = (term40 q r)).
Proof. exact (MK_COMB (@lem258036 m) (@lem258035 q r n h1)). Qed.
Lemma lem258040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258041 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term41 m q n r) = (term42 m q r).
Proof. exact (MK_COMB (@lem258040) (@lem258037 m q r n h1)). Qed.
Lemma lem258043 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem258044 (r : nat) : (Peano.lt r) = (Peano.lt r).
Proof. exact (eq_refl (Peano.lt r)). Qed.
Lemma lem258045 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt r n) = (term43 r).
Proof. exact (MK_COMB (@lem258044 r) (@lem258043 n h1)). Qed.
Lemma lem258046 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term44 m q r n) = (term45 m q r).
Proof. exact (MK_COMB (@lem258041 m q r n h1) (@lem258045 r n h1)). Qed.
Lemma lem258049 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term46 m q r n) = (term47 m q r).
Proof. exact (MK_COMB (@lem258023 q r m n h1) (@lem258046 m q r n h1)). Qed.
Lemma lem258052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem258053 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term48 m q r n) = (term49 m q r).
Proof. exact (MK_COMB (@lem258052) (@lem258049 m q r n h1)). Qed.
Lemma lem258054 (P : type1605) (q : nat) (r : nat) : (P q r) = (P q r).
Proof. exact (eq_refl (P q r)). Qed.
Lemma lem258055 (m : nat) (P : type1605) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term50 m n P q r) = (term51 m P q r).
Proof. exact (MK_COMB (@lem258053 m q r n h1) (@lem258054 P q r)). Qed.
Lemma lem258058 (m : nat) (P : type1605) (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term52 m n P q) = (term53 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258055 m P q r n h1)). Qed.
Lemma lem258059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258060 (m : nat) (P : type1605) (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term54 m n P q) = (term55 m P q).
Proof. exact (MK_COMB (@lem258059) (@lem258058 m P q n h1)). Qed.
Lemma lem258065 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : (term56 m n P) = (term57 m P).
Proof. exact (fun_ext (fun q : nat => @lem258060 m P q n h1)). Qed.
Lemma lem258066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258067 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : (term58 m n P) = (term59 m P).
Proof. exact (MK_COMB (@lem258066) (@lem258065 m P n h1)). Qed.
Lemma lem258072 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : ((term25 P m n) = (term58 m n P)) = ((term26 P m) = (term59 m P)).
Proof. exact (MK_COMB (@lem257974 P m n h1) (@lem258067 m P n h1)). Qed.
Lemma lem258075 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : ((term26 P m) = (term59 m P)) = ((term25 P m n) = (term58 m n P)).
Proof. exact (SYM (@lem258072 m P n h1)). Qed.
Lemma lem258076 (n : nat) : term60 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem258106 (n : nat) (h1 : term12 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem258076 n (@lem257959 n h1)). Qed.
Lemma lem258107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258108 (n : nat) (h1 : term12 n) : (term30 n) = (and False).
Proof. exact (MK_COMB (@lem258107) (@lem258106 n h1)). Qed.
Lemma lem258115 (q : nat) (r : nat) (m : nat) : (term31 q r m) = (term31 q r m).
Proof. exact (eq_refl (term31 q r m)). Qed.
Lemma lem258116 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : term12 n) : (term32 n q r m) = (term61 q r m).
Proof. exact (MK_COMB (@lem258108 n h1) (@lem258115 q r m)). Qed.
Lemma lem258118 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem258119 (q : nat) (r : nat) (m : nat) : (term61 q r m) = False.
Proof. exact (@lem258118 (term31 q r m)). Qed.
Lemma lem258120 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : term12 n) : (term32 n q r m) = False.
Proof. exact (TRANS (@lem258116 q r m n h1) (@lem258119 q r m)). Qed.
Lemma lem258121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258122 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : term12 n) : (term34 n q r m) = (or False).
Proof. exact (MK_COMB (@lem258121) (@lem258120 q r m n h1)). Qed.
Lemma lem258127 (m : nat) (q : nat) (r : nat) (n : nat) : (term44 m q r n) = (term44 m q r n).
Proof. exact (eq_refl (term44 m q r n)). Qed.
Lemma lem258128 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term12 n) : (term46 m q r n) = (term62 m q r n).
Proof. exact (MK_COMB (@lem258122 q r m n h1) (@lem258127 m q r n)). Qed.
Lemma lem258130 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem258131 (m : nat) (q : nat) (r : nat) (n : nat) : (term62 m q r n) = (term44 m q r n).
Proof. exact (@lem258130 (term44 m q r n)). Qed.
Lemma lem258136 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term12 n) : (term46 m q r n) = (term44 m q r n).
Proof. exact (TRANS (@lem258128 m q r n h1) (@lem258131 m q r n)). Qed.
Lemma lem258137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem258138 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term12 n) : (term48 m q r n) = (term63 m q r n).
Proof. exact (MK_COMB (@lem258137) (@lem258136 m q r n h1)). Qed.
Lemma lem258139 (P : type1605) (q : nat) (r : nat) : (P q r) = (P q r).
Proof. exact (eq_refl (P q r)). Qed.
Lemma lem258140 (m : nat) (P : type1605) (q : nat) (r : nat) (n : nat) (h1 : term12 n) : (term50 m n P q r) = (term64 m n P q r).
Proof. exact (MK_COMB (@lem258138 m q r n h1) (@lem258139 P q r)). Qed.
Lemma lem258143 (m : nat) (P : type1605) (q : nat) (n : nat) (h1 : term12 n) : (term52 m n P q) = (term65 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem258140 m P q r n h1)). Qed.
Lemma lem258144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258145 (m : nat) (P : type1605) (q : nat) (n : nat) (h1 : term12 n) : (term54 m n P q) = (term66 m n P q).
Proof. exact (MK_COMB (@lem258144) (@lem258143 m P q n h1)). Qed.
Lemma lem258150 (m : nat) (P : type1605) (n : nat) (h1 : term12 n) : (term56 m n P) = (term67 m n P).
Proof. exact (fun_ext (fun q : nat => @lem258145 m P q n h1)). Qed.
Lemma lem258151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258152 (m : nat) (P : type1605) (n : nat) (h1 : term12 n) : (term58 m n P) = (term68 m n P).
Proof. exact (MK_COMB (@lem258151) (@lem258150 m P n h1)). Qed.
Lemma lem258157 (P : type1605) (m : nat) (n : nat) : (term27 P m n) = (term27 P m n).
Proof. exact (eq_refl (term27 P m n)). Qed.
Lemma lem258158 (m : nat) (P : type1605) (n : nat) (h1 : term12 n) : ((term25 P m n) = (term58 m n P)) = ((term25 P m n) = (term68 m n P)).
Proof. exact (MK_COMB (@lem258157 P m n) (@lem258152 m P n h1)). Qed.
Lemma lem258161 (m : nat) (P : type1605) (n : nat) (h1 : term12 n) : ((term25 P m n) = (term68 m n P)) = ((term25 P m n) = (term58 m n P)).
Proof. exact (SYM (@lem258158 m P n h1)). Qed.
Lemma lem258163 (p : Prop) : p = (term69 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem258164 (m : nat) (P : type1605) : ((term26 P m) = (term59 m P)) = (term70 m P).
Proof. exact (@lem258163 ((term26 P m) = (term59 m P))). Qed.
Lemma lem258165 (m : nat) (P : type1605) : (term70 m P) = ((term26 P m) = (term59 m P)).
Proof. exact (SYM (@lem258164 m P)). Qed.
Lemma lem258166 (m : nat) (P : type1605) (h1 : term71 m P) : term71 m P.
Proof. exact (h1). Qed.
Lemma lem258169 (n : nat) (m : nat) (P : type1605) (h1 : term72 n m P) : term72 n m P.
Proof. exact (h1). Qed.
Lemma lem258170 (n : nat) (m : nat) (P : type1605) : term73 n m P.
Proof. exact (fun h0 : term72 n m P => @lem258169 n m P h0). Qed.
Lemma lem258171 (n : nat) (m : nat) (P : type1605) (h1 : term73 n m P) : term73 n m P.
Proof. exact (h1). Qed.
Lemma lem258172 (n : nat) (m : nat) (P : type1605) (h1 : term72 n m P) : term72 n m P.
Proof. exact (h1). Qed.
Lemma lem258173 (n : nat) (m : nat) (P : type1605) (h1 : term72 n m P) (h2 : term73 n m P) : term72 n m P.
Proof. exact (@lem258171 n m P h2 (@lem258172 n m P h1)). Qed.
Lemma lem258174 (n : nat) (m : nat) (P : type1605) (h1 : term72 n m P) : term74 n m P.
Proof. exact (fun h0 : term73 n m P => @lem258173 n m P h1 h0). Qed.
Lemma lem258175 (n : nat) (m : nat) (P : type1605) (h1 : term73 n m P) : term73 n m P.
Proof. exact (h1). Qed.
Lemma lem258176 (n : nat) (m : nat) (P : type1605) (h1 : term72 n m P) (h2 : term73 n m P) : term72 n m P.
Proof. exact (@lem258174 n m P h1 (@lem258175 n m P h2)). Qed.
Lemma lem258177 (n : nat) (m : nat) (P : type1605) (h1 : term73 n m P) : term73 n m P.
Proof. exact (fun h0 : term72 n m P => @lem258176 n m P h0 h1). Qed.
Lemma lem258178 (n : nat) (m : nat) (P : type1605) : term75 n m P.
Proof. exact (fun h0 : term73 n m P => @lem258177 n m P h0). Qed.
Lemma lem258181 (n : nat) (m : nat) (P : type1605) : term73 n m P.
Proof. exact (@lem258178 n m P (@lem258170 n m P)). Qed.
Lemma lem258223 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem258224 (m : nat) : ((term43 m) = False) = (term76 m).
Proof. exact (@lem258223 (term43 m)). Qed.
Lemma lem258225 : term77 = term78.
Proof. exact (fun_ext (fun m : nat => @lem258224 m)). Qed.
Lemma lem258226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258227 : term79 = term80.
Proof. exact (MK_COMB (@lem258226) (@lem258225)). Qed.
Lemma lem258232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258233 : term81 = term82.
Proof. exact (MK_COMB (@lem258232) (@lem258227)). Qed.
Lemma lem258244 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem258245 : term84 = term85.
Proof. exact (MK_COMB (@lem258233) (@lem258244)). Qed.
Lemma lem258248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem258249 : term86 = term87.
Proof. exact (MK_COMB (@lem258248) (@lem258245)). Qed.
Lemma lem258251 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem258252 : term88 = term89.
Proof. exact (@lem258251 term90). Qed.
Lemma lem258265 : term91 = term92.
Proof. exact (MK_COMB (@lem258249) (@lem258252)). Qed.
Lemma lem258268 (m : nat) (P : type1605) : (term93 m P) = (term93 m P).
Proof. exact (eq_refl (term93 m P)). Qed.
Lemma lem258269 (m : nat) (P : type1605) : (term94 m P) = (term95 m P).
Proof. exact (MK_COMB (@lem258268 m P) (@lem258265)). Qed.
Lemma lem258272 (n : nat) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem258273 (n : nat) (m : nat) (P : type1605) : (term72 n m P) = (term97 n m P).
Proof. exact (MK_COMB (@lem258272 n) (@lem258269 m P)). Qed.
Lemma lem258276 (m : nat) (P : type1605) : (term98 m P) = (term99 m P).
Proof. exact (fun_ext (fun n : nat => @lem258273 n m P)). Qed.
Lemma lem258277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258278 (m : nat) (P : type1605) : (term100 m P) = (term101 m P).
Proof. exact (MK_COMB (@lem258277) (@lem258276 m P)). Qed.
Lemma lem258283 (P : type1605) : (term102 P) = (term103 P).
Proof. exact (fun_ext (fun m : nat => @lem258278 m P)). Qed.
Lemma lem258284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258285 (P : type1605) : (term104 P) = (term105 P).
Proof. exact (MK_COMB (@lem258284) (@lem258283 P)). Qed.
Lemma lem258290 : term106 = term107.
Proof. exact (fun_ext (fun P : type1605 => @lem258285 P)). Qed.
Lemma lem258291 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem258300 : term108 = term109.
Proof. exact (MK_COMB (@lem258291) (@lem258290)). Qed.
Lemma lem258304 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem258305 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem258306 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term110 n) = (@COND Prop False).
Proof. exact (MK_COMB (@lem258305) (@lem258304 n h1)). Qed.
Lemma lem258313 (n : nat) (m : nat) : (term111 n m) = (term111 n m).
Proof. exact (eq_refl (term111 n m)). Qed.
Lemma lem258314 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term112 n m) = (term113 n m).
Proof. exact (MK_COMB (@lem258306 n h1) (@lem258313 n m)). Qed.
Lemma lem258319 (m : nat) (n : nat) : (term13 m n) = (term13 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem258320 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term114 m n) = (term115 m n).
Proof. exact (MK_COMB (@lem258314 m n h1) (@lem258319 m n)). Qed.
Lemma lem258322 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem258323 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem258322 Prop t1 t2). Qed.
Lemma lem258324 (m : nat) (n : nat) : (term115 m n) = (term13 m n).
Proof. exact (@lem258323 (term111 n m) (term13 m n)). Qed.
Lemma lem258327 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term114 m n) = (term13 m n).
Proof. exact (TRANS (@lem258320 m n h1) (@lem258324 m n)). Qed.
Lemma lem258328 (m : nat) (n : nat) : term116 m n.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = False => @lem258327 m n h0). Qed.
Lemma lem258330 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem258331 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem258332 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term110 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem258331) (@lem258330 n h1)). Qed.
Lemma lem258339 (n : nat) (m : nat) : (term111 n m) = (term111 n m).
Proof. exact (eq_refl (term111 n m)). Qed.
Lemma lem258340 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term112 n m) = (term117 n m).
Proof. exact (MK_COMB (@lem258332 n h1) (@lem258339 n m)). Qed.
Lemma lem258345 (m : nat) (n : nat) : (term13 m n) = (term13 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem258346 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term114 m n) = (term118 m n).
Proof. exact (MK_COMB (@lem258340 m n h1) (@lem258345 m n)). Qed.
Lemma lem258348 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem258349 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem258348 Prop t2 t1). Qed.
Lemma lem258350 (n : nat) (m : nat) : (term118 m n) = (term111 n m).
Proof. exact (@lem258349 (term13 m n) (term111 n m)). Qed.
Lemma lem258353 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term114 m n) = (term111 n m).
Proof. exact (TRANS (@lem258346 m n h1) (@lem258350 n m)). Qed.
Lemma lem258354 (n : nat) (m : nat) : term119 n m.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = True => @lem258353 m n h0). Qed.
Lemma lem258355 (n : nat) (m : nat) : term120 n m.
Proof. exact (conj (@lem258328 m n) (@lem258354 n m)). Qed.
Lemma lem258357 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term121 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem258358 (m : nat) (n : nat) : term122 m n.
Proof. exact (@lem258357 (term114 m n) (term111 n m) (n = (NUMERAL 0)) (term13 m n)). Qed.
Lemma lem258399 (m : nat) (n : nat) : (term114 m n) = (term123 m n).
Proof. exact (@lem258358 m n (@lem258355 n m)). Qed.
Lemma lem258400 (m : nat) : (term124 m) = (term125 m).
Proof. exact (fun_ext (fun n : nat => @lem258399 m n)). Qed.
Lemma lem258401 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258402 (m : nat) : (term126 m) = (term127 m).
Proof. exact (MK_COMB (@lem258401) (@lem258400 m)). Qed.
Lemma lem258403 : term128 = term129.
Proof. exact (fun_ext (fun m : nat => @lem258402 m)). Qed.
Lemma lem258404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258405 : term90 = term130.
Proof. exact (MK_COMB (@lem258404) (@lem258403)). Qed.
Lemma lem258406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem258407 : term89 = term131.
Proof. exact (MK_COMB (@lem258406) (@lem258405)). Qed.
Lemma lem258416 (m : nat) (n : nat) : ((term132 m n) = (term133 m n)) = ((term132 m n) = (term133 m n)).
Proof. exact (eq_refl ((term132 m n) = (term133 m n))). Qed.
Lemma lem258417 (m : nat) : (term134 m) = (term134 m).
Proof. exact (fun_ext (fun n : nat => @lem258416 m n)). Qed.
Lemma lem258418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258419 (m : nat) : (term135 m) = (term135 m).
Proof. exact (MK_COMB (@lem258418) (@lem258417 m)). Qed.
Lemma lem258420 : term136 = term136.
Proof. exact (fun_ext (fun m : nat => @lem258419 m)). Qed.
Lemma lem258421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258422 : term83 = term83.
Proof. exact (MK_COMB (@lem258421) (@lem258420)). Qed.
Lemma lem258425 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem258426 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem258425 m)). Qed.
Lemma lem258427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258428 : term80 = term80.
Proof. exact (MK_COMB (@lem258427) (@lem258426)). Qed.
Lemma lem258429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258430 : term82 = term82.
Proof. exact (MK_COMB (@lem258429) (@lem258428)). Qed.
Lemma lem258431 : term85 = term85.
Proof. exact (MK_COMB (@lem258430) (@lem258422)). Qed.
Lemma lem258432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem258433 : term87 = term87.
Proof. exact (MK_COMB (@lem258432) (@lem258431)). Qed.
Lemma lem258434 : term92 = term137.
Proof. exact (MK_COMB (@lem258433) (@lem258407)). Qed.
Lemma lem258451 (m : nat) (P : type1605) (q : nat) (r : nat) : (term51 m P q r) = (term51 m P q r).
Proof. exact (eq_refl (term51 m P q r)). Qed.
Lemma lem258452 (m : nat) (P : type1605) (q : nat) : (term53 m P q) = (term53 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258451 m P q r)). Qed.
Lemma lem258453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258454 (m : nat) (P : type1605) (q : nat) : (term55 m P q) = (term55 m P q).
Proof. exact (MK_COMB (@lem258453) (@lem258452 m P q)). Qed.
Lemma lem258455 (m : nat) (P : type1605) : (term57 m P) = (term57 m P).
Proof. exact (fun_ext (fun q : nat => @lem258454 m P q)). Qed.
Lemma lem258456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258457 (m : nat) (P : type1605) : (term59 m P) = (term59 m P).
Proof. exact (MK_COMB (@lem258456) (@lem258455 m P)). Qed.
Lemma lem258460 (P : type1605) (m : nat) : (term28 P m) = (term28 P m).
Proof. exact (eq_refl (term28 P m)). Qed.
Lemma lem258461 (m : nat) (P : type1605) : ((term26 P m) = (term59 m P)) = ((term26 P m) = (term59 m P)).
Proof. exact (MK_COMB (@lem258460 P m) (@lem258457 m P)). Qed.
Lemma lem258462 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem258463 (m : nat) (P : type1605) : (term71 m P) = (term71 m P).
Proof. exact (MK_COMB (@lem258462) (@lem258461 m P)). Qed.
Lemma lem258464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem258465 (m : nat) (P : type1605) : (term93 m P) = (term93 m P).
Proof. exact (MK_COMB (@lem258464) (@lem258463 m P)). Qed.
Lemma lem258466 (m : nat) (P : type1605) : (term95 m P) = (term138 m P).
Proof. exact (MK_COMB (@lem258465 m P) (@lem258434)). Qed.
Lemma lem258469 (n : nat) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem258470 (n : nat) (m : nat) (P : type1605) : (term97 n m P) = (term139 n m P).
Proof. exact (MK_COMB (@lem258469 n) (@lem258466 m P)). Qed.
Lemma lem258471 (m : nat) (P : type1605) : (term99 m P) = (term140 m P).
Proof. exact (fun_ext (fun n : nat => @lem258470 n m P)). Qed.
Lemma lem258472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258473 (m : nat) (P : type1605) : (term101 m P) = (term141 m P).
Proof. exact (MK_COMB (@lem258472) (@lem258471 m P)). Qed.
Lemma lem258474 (P : type1605) : (term103 P) = (term142 P).
Proof. exact (fun_ext (fun m : nat => @lem258473 m P)). Qed.
Lemma lem258475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258476 (P : type1605) : (term105 P) = (term143 P).
Proof. exact (MK_COMB (@lem258475) (@lem258474 P)). Qed.
Lemma lem258477 : term107 = term144.
Proof. exact (fun_ext (fun P : type1605 => @lem258476 P)). Qed.
Lemma lem258478 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem258479 : term109 = term145.
Proof. exact (MK_COMB (@lem258478) (@lem258477)). Qed.
Lemma lem258570 : term108 = term145.
Proof. exact (TRANS (@lem258300) (@lem258479)). Qed.
Lemma lem258571 : term145 = term108.
Proof. exact (SYM (@lem258570)). Qed.
Lemma lem258573 (m : nat) (P : type1605) (h1 : term71 m P) : term71 m P.
Proof. exact (h1). Qed.
Lemma lem258574 (h1 : term85) : term85.
Proof. exact (h1). Qed.
Lemma lem258575 (h1 : term130) : term130.
Proof. exact (h1). Qed.
Lemma lem258592 (q : nat) (r : nat) (m : nat) : (term146 q r m) = (term147 q r m).
Proof. exact (@lem17045 (q = (NUMERAL 0)) (r = m)). Qed.
Lemma lem258604 (m : nat) (q : nat) (r : nat) : (term148 m q r) = (term149 m q r).
Proof. exact (@lem17045 (m = (term40 q r)) (term43 r)). Qed.
Lemma lem258608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258609 (q : nat) (r : nat) (m : nat) : (term150 q r m) = (term151 q r m).
Proof. exact (MK_COMB (@lem258608) (@lem258592 q r m)). Qed.
Lemma lem258610 (m : nat) (q : nat) (r : nat) : (term152 m q r) = (term153 m q r).
Proof. exact (MK_COMB (@lem258609 q r m) (@lem258604 m q r)). Qed.
Lemma lem258611 (m : nat) (q : nat) (r : nat) : (term154 m q r) = (term152 m q r).
Proof. exact (@lem17160 (term31 q r m) (term45 m q r)). Qed.
Lemma lem258612 (m : nat) (q : nat) (r : nat) : (term154 m q r) = (term153 m q r).
Proof. exact (TRANS (@lem258611 m q r) (@lem258610 m q r)). Qed.
Lemma lem258617 (P : type1605) (q : nat) (r : nat) : (P q r) = (P q r).
Proof. exact (eq_refl (P q r)). Qed.
Lemma lem258622 (m : nat) (P : type1605) (q : nat) (r : nat) : (term155 m P q r) = (term156 m P q r).
Proof. exact (@lem17362 (term47 m q r) (P q r)). Qed.
Lemma lem258623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258624 (m : nat) (q : nat) (r : nat) : (term157 m q r) = (term158 m q r).
Proof. exact (MK_COMB (@lem258623) (@lem258612 m q r)). Qed.
Lemma lem258625 (m : nat) (P : type1605) (q : nat) (r : nat) : (term159 m P q r) = (term160 m P q r).
Proof. exact (MK_COMB (@lem258624 m q r) (@lem258617 P q r)). Qed.
Lemma lem258626 (m : nat) (P : type1605) (q : nat) (r : nat) : (term51 m P q r) = (term159 m P q r).
Proof. exact (@lem17265 (term47 m q r) (P q r)). Qed.
Lemma lem258627 (m : nat) (P : type1605) (q : nat) (r : nat) : (term51 m P q r) = (term160 m P q r).
Proof. exact (TRANS (@lem258626 m P q r) (@lem258625 m P q r)). Qed.
Lemma lem258628 (P : nat -> Prop) : (term161 P) = (term162 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem258629 (m : nat) (P : type1605) (q : nat) : (term163 m P q) = (term164 m P q).
Proof. exact (@lem258628 (term53 m P q)). Qed.
Lemma lem258630 (m : nat) (P : type1605) (q : nat) (r : nat) : (term165 m P q r) = (term51 m P q r).
Proof. exact (eq_refl (term165 m P q r)). Qed.
Lemma lem258631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem258632 (m : nat) (P : type1605) (q : nat) (r : nat) : (term166 m P q r) = (term155 m P q r).
Proof. exact (MK_COMB (@lem258631) (@lem258630 m P q r)). Qed.
Lemma lem258633 (m : nat) (P : type1605) (q : nat) (r : nat) : (term166 m P q r) = (term156 m P q r).
Proof. exact (TRANS (@lem258632 m P q r) (@lem258622 m P q r)). Qed.
Lemma lem258634 (m : nat) (P : type1605) (q : nat) : (term167 m P q) = (term168 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258633 m P q r)). Qed.
Lemma lem258635 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258636 (m : nat) (P : type1605) (q : nat) : (term164 m P q) = (term169 m P q).
Proof. exact (MK_COMB (@lem258635) (@lem258634 m P q)). Qed.
Lemma lem258637 (m : nat) (P : type1605) (q : nat) : (term163 m P q) = (term169 m P q).
Proof. exact (TRANS (@lem258629 m P q) (@lem258636 m P q)). Qed.
Lemma lem258638 (m : nat) (P : type1605) (q : nat) : (term53 m P q) = (term170 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258627 m P q r)). Qed.
Lemma lem258639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258640 (m : nat) (P : type1605) (q : nat) : (term55 m P q) = (term171 m P q).
Proof. exact (MK_COMB (@lem258639) (@lem258638 m P q)). Qed.
Lemma lem258641 (P : nat -> Prop) : (term161 P) = (term162 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem258642 (m : nat) (P : type1605) : (term172 m P) = (term173 m P).
Proof. exact (@lem258641 (term57 m P)). Qed.
Lemma lem258643 (m : nat) (P : type1605) (q : nat) : (term174 m P q) = (term55 m P q).
Proof. exact (eq_refl (term174 m P q)). Qed.
Lemma lem258644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem258645 (m : nat) (P : type1605) (q : nat) : (term175 m P q) = (term163 m P q).
Proof. exact (MK_COMB (@lem258644) (@lem258643 m P q)). Qed.
Lemma lem258646 (m : nat) (P : type1605) (q : nat) : (term175 m P q) = (term169 m P q).
Proof. exact (TRANS (@lem258645 m P q) (@lem258637 m P q)). Qed.
Lemma lem258647 (m : nat) (P : type1605) : (term176 m P) = (term177 m P).
Proof. exact (fun_ext (fun q : nat => @lem258646 m P q)). Qed.
Lemma lem258648 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258649 (m : nat) (P : type1605) : (term173 m P) = (term178 m P).
Proof. exact (MK_COMB (@lem258648) (@lem258647 m P)). Qed.
Lemma lem258650 (m : nat) (P : type1605) : (term172 m P) = (term178 m P).
Proof. exact (TRANS (@lem258642 m P) (@lem258649 m P)). Qed.
Lemma lem258651 (m : nat) (P : type1605) : (term57 m P) = (term179 m P).
Proof. exact (fun_ext (fun q : nat => @lem258640 m P q)). Qed.
Lemma lem258652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258653 (m : nat) (P : type1605) : (term59 m P) = (term180 m P).
Proof. exact (MK_COMB (@lem258652) (@lem258651 m P)). Qed.
Lemma lem258655 (P : type1605) (m : nat) : (term181 P m) = (term181 P m).
Proof. exact (eq_refl (term181 P m)). Qed.
Lemma lem258656 (m : nat) (P : type1605) : (term182 m P) = (term183 m P).
Proof. exact (MK_COMB (@lem258655 P m) (@lem258653 m P)). Qed.
Lemma lem258658 (P : type1605) (m : nat) : (term184 P m) = (term184 P m).
Proof. exact (eq_refl (term184 P m)). Qed.
Lemma lem258659 (m : nat) (P : type1605) : (term185 m P) = (term186 m P).
Proof. exact (MK_COMB (@lem258658 P m) (@lem258650 m P)). Qed.
Lemma lem258660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258661 (m : nat) (P : type1605) : (term187 m P) = (term188 m P).
Proof. exact (MK_COMB (@lem258660) (@lem258659 m P)). Qed.
Lemma lem258662 (m : nat) (P : type1605) : (term189 m P) = (term190 m P).
Proof. exact (MK_COMB (@lem258661 m P) (@lem258656 m P)). Qed.
Lemma lem258663 (m : nat) (P : type1605) : (term71 m P) = (term189 m P).
Proof. exact (@lem17646 (term26 P m) (term59 m P)). Qed.
Lemma lem258664 (m : nat) (P : type1605) : (term71 m P) = (term190 m P).
Proof. exact (TRANS (@lem258663 m P) (@lem258662 m P)). Qed.
Lemma lem258771 {A : Type'} (P : Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem258772 (P : Prop) (Q : nat -> Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem258771 nat P Q). Qed.
Lemma lem258773 (m : nat) (P : type1605) : (term195 m P) = (term196 m P).
Proof. exact (@lem258772 (term26 P m) (term177 m P)). Qed.
Lemma lem258774 (m : nat) (P : type1605) (q : nat) : (term197 m P q) = (term169 m P q).
Proof. exact (eq_refl (term197 m P q)). Qed.
Lemma lem258775 (m : nat) (P : type1605) : (term198 m P) = (term177 m P).
Proof. exact (fun_ext (fun q : nat => @lem258774 m P q)). Qed.
Lemma lem258776 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258777 (m : nat) (P : type1605) : (term199 m P) = (term178 m P).
Proof. exact (MK_COMB (@lem258776) (@lem258775 m P)). Qed.
Lemma lem258778 (P : type1605) (m : nat) : (term184 P m) = (term184 P m).
Proof. exact (eq_refl (term184 P m)). Qed.
Lemma lem258779 (m : nat) (P : type1605) : (term195 m P) = (term186 m P).
Proof. exact (MK_COMB (@lem258778 P m) (@lem258777 m P)). Qed.
Lemma lem258780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem258781 (m : nat) (P : type1605) : (term200 m P) = (term201 m P).
Proof. exact (MK_COMB (@lem258780) (@lem258779 m P)). Qed.
Lemma lem258782 (m : nat) (P : type1605) (q : nat) : (term197 m P q) = (term169 m P q).
Proof. exact (eq_refl (term197 m P q)). Qed.
Lemma lem258783 (P : type1605) (m : nat) : (term184 P m) = (term184 P m).
Proof. exact (eq_refl (term184 P m)). Qed.
Lemma lem258784 (m : nat) (P : type1605) (q : nat) : (term202 m P q) = (term203 m P q).
Proof. exact (MK_COMB (@lem258783 P m) (@lem258782 m P q)). Qed.
Lemma lem258785 (m : nat) (P : type1605) : (term204 m P) = (term205 m P).
Proof. exact (fun_ext (fun q : nat => @lem258784 m P q)). Qed.
Lemma lem258786 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258787 (m : nat) (P : type1605) : (term196 m P) = (term206 m P).
Proof. exact (MK_COMB (@lem258786) (@lem258785 m P)). Qed.
Lemma lem258788 (m : nat) (P : type1605) : ((term195 m P) = (term196 m P)) = ((term186 m P) = (term206 m P)).
Proof. exact (MK_COMB (@lem258781 m P) (@lem258787 m P)). Qed.
Lemma lem258789 (m : nat) (P : type1605) : (term186 m P) = (term206 m P).
Proof. exact (EQ_MP (@lem258788 m P) (@lem258773 m P)). Qed.
Lemma lem258791 {A : Type'} (P : Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem258792 (P : Prop) (Q : nat -> Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem258791 nat P Q). Qed.
Lemma lem258793 (m : nat) (P : type1605) (q : nat) : (term207 m P q) = (term208 m P q).
Proof. exact (@lem258792 (term26 P m) (term168 m P q)). Qed.
Lemma lem258794 (m : nat) (P : type1605) (q : nat) (r : nat) : (term209 m P q r) = (term156 m P q r).
Proof. exact (eq_refl (term209 m P q r)). Qed.
Lemma lem258795 (m : nat) (P : type1605) (q : nat) : (term210 m P q) = (term168 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258794 m P q r)). Qed.
Lemma lem258796 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258797 (m : nat) (P : type1605) (q : nat) : (term211 m P q) = (term169 m P q).
Proof. exact (MK_COMB (@lem258796) (@lem258795 m P q)). Qed.
Lemma lem258798 (P : type1605) (m : nat) : (term184 P m) = (term184 P m).
Proof. exact (eq_refl (term184 P m)). Qed.
Lemma lem258799 (m : nat) (P : type1605) (q : nat) : (term207 m P q) = (term203 m P q).
Proof. exact (MK_COMB (@lem258798 P m) (@lem258797 m P q)). Qed.
Lemma lem258800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem258801 (m : nat) (P : type1605) (q : nat) : (term212 m P q) = (term213 m P q).
Proof. exact (MK_COMB (@lem258800) (@lem258799 m P q)). Qed.
Lemma lem258802 (m : nat) (P : type1605) (q : nat) (r : nat) : (term209 m P q r) = (term156 m P q r).
Proof. exact (eq_refl (term209 m P q r)). Qed.
Lemma lem258803 (P : type1605) (m : nat) : (term184 P m) = (term184 P m).
Proof. exact (eq_refl (term184 P m)). Qed.
Lemma lem258804 (m : nat) (P : type1605) (q : nat) (r : nat) : (term214 m P q r) = (term215 m P q r).
Proof. exact (MK_COMB (@lem258803 P m) (@lem258802 m P q r)). Qed.
Lemma lem258805 (m : nat) (P : type1605) (q : nat) : (term216 m P q) = (term217 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258804 m P q r)). Qed.
Lemma lem258806 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258807 (m : nat) (P : type1605) (q : nat) : (term208 m P q) = (term218 m P q).
Proof. exact (MK_COMB (@lem258806) (@lem258805 m P q)). Qed.
Lemma lem258808 (m : nat) (P : type1605) (q : nat) : ((term207 m P q) = (term208 m P q)) = ((term203 m P q) = (term218 m P q)).
Proof. exact (MK_COMB (@lem258801 m P q) (@lem258807 m P q)). Qed.
Lemma lem258809 (m : nat) (P : type1605) (q : nat) : (term203 m P q) = (term218 m P q).
Proof. exact (EQ_MP (@lem258808 m P q) (@lem258793 m P q)). Qed.
Lemma lem258810 (m : nat) (P : type1605) : (term205 m P) = (term219 m P).
Proof. exact (fun_ext (fun q : nat => @lem258809 m P q)). Qed.
Lemma lem258811 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258812 (m : nat) (P : type1605) : (term206 m P) = (term220 m P).
Proof. exact (MK_COMB (@lem258811) (@lem258810 m P)). Qed.
Lemma lem258813 (m : nat) (P : type1605) : (term186 m P) = (term220 m P).
Proof. exact (TRANS (@lem258789 m P) (@lem258812 m P)). Qed.
Lemma lem258814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258815 (m : nat) (P : type1605) : (term188 m P) = (term221 m P).
Proof. exact (MK_COMB (@lem258814) (@lem258813 m P)). Qed.
Lemma lem258816 (m : nat) (P : type1605) : (term183 m P) = (term183 m P).
Proof. exact (eq_refl (term183 m P)). Qed.
Lemma lem258817 (m : nat) (P : type1605) : (term190 m P) = (term222 m P).
Proof. exact (MK_COMB (@lem258815 m P) (@lem258816 m P)). Qed.
Lemma lem258819 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem258820 (P : nat -> Prop) (Q : Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem258819 nat P Q). Qed.
Lemma lem258821 (m : nat) (P : type1605) : (term227 m P) = (term228 m P).
Proof. exact (@lem258820 (term219 m P) (term183 m P)). Qed.
Lemma lem258822 (m : nat) (P : type1605) (q : nat) : (term229 m P q) = (term218 m P q).
Proof. exact (eq_refl (term229 m P q)). Qed.
Lemma lem258823 (m : nat) (P : type1605) : (term230 m P) = (term219 m P).
Proof. exact (fun_ext (fun q : nat => @lem258822 m P q)). Qed.
Lemma lem258824 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258825 (m : nat) (P : type1605) : (term231 m P) = (term220 m P).
Proof. exact (MK_COMB (@lem258824) (@lem258823 m P)). Qed.
Lemma lem258826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258827 (m : nat) (P : type1605) : (term232 m P) = (term221 m P).
Proof. exact (MK_COMB (@lem258826) (@lem258825 m P)). Qed.
Lemma lem258828 (m : nat) (P : type1605) : (term183 m P) = (term183 m P).
Proof. exact (eq_refl (term183 m P)). Qed.
Lemma lem258829 (m : nat) (P : type1605) : (term227 m P) = (term222 m P).
Proof. exact (MK_COMB (@lem258827 m P) (@lem258828 m P)). Qed.
Lemma lem258830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem258831 (m : nat) (P : type1605) : (term233 m P) = (term234 m P).
Proof. exact (MK_COMB (@lem258830) (@lem258829 m P)). Qed.
Lemma lem258832 (m : nat) (P : type1605) (q : nat) : (term229 m P q) = (term218 m P q).
Proof. exact (eq_refl (term229 m P q)). Qed.
Lemma lem258833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258834 (m : nat) (P : type1605) (q : nat) : (term235 m P q) = (term236 m P q).
Proof. exact (MK_COMB (@lem258833) (@lem258832 m P q)). Qed.
Lemma lem258835 (m : nat) (P : type1605) : (term183 m P) = (term183 m P).
Proof. exact (eq_refl (term183 m P)). Qed.
Lemma lem258836 (q : nat) (m : nat) (P : type1605) : (term237 q m P) = (term238 q m P).
Proof. exact (MK_COMB (@lem258834 m P q) (@lem258835 m P)). Qed.
Lemma lem258837 (m : nat) (P : type1605) : (term239 m P) = (term240 m P).
Proof. exact (fun_ext (fun q : nat => @lem258836 q m P)). Qed.
Lemma lem258838 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258839 (m : nat) (P : type1605) : (term228 m P) = (term241 m P).
Proof. exact (MK_COMB (@lem258838) (@lem258837 m P)). Qed.
Lemma lem258840 (m : nat) (P : type1605) : ((term227 m P) = (term228 m P)) = ((term222 m P) = (term241 m P)).
Proof. exact (MK_COMB (@lem258831 m P) (@lem258839 m P)). Qed.
Lemma lem258841 (m : nat) (P : type1605) : (term222 m P) = (term241 m P).
Proof. exact (EQ_MP (@lem258840 m P) (@lem258821 m P)). Qed.
Lemma lem258843 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem258844 (P : nat -> Prop) (Q : Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem258843 nat P Q). Qed.
Lemma lem258845 (q : nat) (m : nat) (P : type1605) : (term242 q m P) = (term243 q m P).
Proof. exact (@lem258844 (term217 m P q) (term183 m P)). Qed.
Lemma lem258846 (m : nat) (P : type1605) (q : nat) (r : nat) : (term244 m P q r) = (term215 m P q r).
Proof. exact (eq_refl (term244 m P q r)). Qed.
Lemma lem258847 (m : nat) (P : type1605) (q : nat) : (term245 m P q) = (term217 m P q).
Proof. exact (fun_ext (fun r : nat => @lem258846 m P q r)). Qed.
Lemma lem258848 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258849 (m : nat) (P : type1605) (q : nat) : (term246 m P q) = (term218 m P q).
Proof. exact (MK_COMB (@lem258848) (@lem258847 m P q)). Qed.
Lemma lem258850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258851 (m : nat) (P : type1605) (q : nat) : (term247 m P q) = (term236 m P q).
Proof. exact (MK_COMB (@lem258850) (@lem258849 m P q)). Qed.
Lemma lem258852 (m : nat) (P : type1605) : (term183 m P) = (term183 m P).
Proof. exact (eq_refl (term183 m P)). Qed.
Lemma lem258853 (q : nat) (m : nat) (P : type1605) : (term242 q m P) = (term238 q m P).
Proof. exact (MK_COMB (@lem258851 m P q) (@lem258852 m P)). Qed.
Lemma lem258854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem258855 (q : nat) (m : nat) (P : type1605) : (term248 q m P) = (term249 q m P).
Proof. exact (MK_COMB (@lem258854) (@lem258853 q m P)). Qed.
Lemma lem258856 (m : nat) (P : type1605) (q : nat) (r : nat) : (term244 m P q r) = (term215 m P q r).
Proof. exact (eq_refl (term244 m P q r)). Qed.
Lemma lem258857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem258858 (m : nat) (P : type1605) (q : nat) (r : nat) : (term250 m P q r) = (term251 m P q r).
Proof. exact (MK_COMB (@lem258857) (@lem258856 m P q r)). Qed.
Lemma lem258859 (m : nat) (P : type1605) : (term183 m P) = (term183 m P).
Proof. exact (eq_refl (term183 m P)). Qed.
Lemma lem258860 (q : nat) (r : nat) (m : nat) (P : type1605) : (term252 q r m P) = (term253 q r m P).
Proof. exact (MK_COMB (@lem258858 m P q r) (@lem258859 m P)). Qed.
Lemma lem258861 (q : nat) (m : nat) (P : type1605) : (term254 q m P) = (term255 q m P).
Proof. exact (fun_ext (fun r : nat => @lem258860 q r m P)). Qed.
Lemma lem258862 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258863 (q : nat) (m : nat) (P : type1605) : (term243 q m P) = (term256 q m P).
Proof. exact (MK_COMB (@lem258862) (@lem258861 q m P)). Qed.
Lemma lem258864 (q : nat) (m : nat) (P : type1605) : ((term242 q m P) = (term243 q m P)) = ((term238 q m P) = (term256 q m P)).
Proof. exact (MK_COMB (@lem258855 q m P) (@lem258863 q m P)). Qed.
Lemma lem258865 (q : nat) (m : nat) (P : type1605) : (term238 q m P) = (term256 q m P).
Proof. exact (EQ_MP (@lem258864 q m P) (@lem258845 q m P)). Qed.
Lemma lem258866 (m : nat) (P : type1605) : (term240 m P) = (term257 m P).
Proof. exact (fun_ext (fun q : nat => @lem258865 q m P)). Qed.
Lemma lem258867 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem258868 (m : nat) (P : type1605) : (term241 m P) = (term258 m P).
Proof. exact (MK_COMB (@lem258867) (@lem258866 m P)). Qed.
Lemma lem258869 (m : nat) (P : type1605) : (term222 m P) = (term258 m P).
Proof. exact (TRANS (@lem258841 m P) (@lem258868 m P)). Qed.
Lemma lem258871 (m : nat) (P : type1605) : (term190 m P) = (term258 m P).
Proof. exact (TRANS (@lem258817 m P) (@lem258869 m P)). Qed.
Lemma lem258872 (m : nat) (P : type1605) : (term71 m P) = (term258 m P).
Proof. exact (TRANS (@lem258664 m P) (@lem258871 m P)). Qed.
Lemma lem258873 (m : nat) (P : type1605) (h1 : term71 m P) : term258 m P.
Proof. exact (EQ_MP (@lem258872 m P) (@lem258573 m P h1)). Qed.
Lemma lem258874 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem258875 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem258874 m)). Qed.
Lemma lem258876 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258877 : term80 = term80.
Proof. exact (MK_COMB (@lem258876) (@lem258875)). Qed.
Lemma lem258888 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem258894 (m : nat) (n : nat) : (term261 m n) = (term261 m n).
Proof. exact (eq_refl (term261 m n)). Qed.
Lemma lem258896 (m : nat) (n : nat) : (term262 m n) = (term262 m n).
Proof. exact (eq_refl (term262 m n)). Qed.
Lemma lem258897 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (MK_COMB (@lem258896 m n) (@lem258888 m n)). Qed.
Lemma lem258898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258899 (m : nat) (n : nat) : (term265 m n) = (term266 m n).
Proof. exact (MK_COMB (@lem258898) (@lem258897 m n)). Qed.
Lemma lem258900 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (MK_COMB (@lem258899 m n) (@lem258894 m n)). Qed.
Lemma lem258901 (m : nat) (n : nat) : ((term132 m n) = (term133 m n)) = (term267 m n).
Proof. exact (@lem17784 (term132 m n) (term133 m n)). Qed.
Lemma lem258902 (m : nat) (n : nat) : ((term132 m n) = (term133 m n)) = (term268 m n).
Proof. exact (TRANS (@lem258901 m n) (@lem258900 m n)). Qed.
Lemma lem258903 (m : nat) : (term134 m) = (term269 m).
Proof. exact (fun_ext (fun n : nat => @lem258902 m n)). Qed.
Lemma lem258904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258905 (m : nat) : (term135 m) = (term270 m).
Proof. exact (MK_COMB (@lem258904) (@lem258903 m)). Qed.
Lemma lem258906 : term136 = term271.
Proof. exact (fun_ext (fun m : nat => @lem258905 m)). Qed.
Lemma lem258907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258908 : term83 = term272.
Proof. exact (MK_COMB (@lem258907) (@lem258906)). Qed.
Lemma lem258909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258910 : term82 = term82.
Proof. exact (MK_COMB (@lem258909) (@lem258877)). Qed.
Lemma lem258911 : term85 = term273.
Proof. exact (MK_COMB (@lem258910) (@lem258908)). Qed.
Lemma lem258921 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem258922 (P : nat -> Prop) (Q : nat -> Prop) : (term276 P Q) = (term277 P Q).
Proof. exact (@lem258921 nat P Q). Qed.
Lemma lem258923 (m : nat) : (term278 m) = (term279 m).
Proof. exact (@lem258922 (term280 m) (term281 m)). Qed.
Lemma lem258924 (m : nat) (n : nat) : (term282 m n) = (term264 m n).
Proof. exact (eq_refl (term282 m n)). Qed.
Lemma lem258925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258926 (m : nat) (n : nat) : (term283 m n) = (term266 m n).
Proof. exact (MK_COMB (@lem258925) (@lem258924 m n)). Qed.
Lemma lem258927 (m : nat) (n : nat) : (term284 m n) = (term261 m n).
Proof. exact (eq_refl (term284 m n)). Qed.
Lemma lem258928 (m : nat) (n : nat) : (term285 m n) = (term268 m n).
Proof. exact (MK_COMB (@lem258926 m n) (@lem258927 m n)). Qed.
Lemma lem258929 (m : nat) : (term286 m) = (term269 m).
Proof. exact (fun_ext (fun n : nat => @lem258928 m n)). Qed.
Lemma lem258930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258931 (m : nat) : (term278 m) = (term270 m).
Proof. exact (MK_COMB (@lem258930) (@lem258929 m)). Qed.
Lemma lem258932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem258933 (m : nat) : (term287 m) = (term288 m).
Proof. exact (MK_COMB (@lem258932) (@lem258931 m)). Qed.
Lemma lem258934 (m : nat) (n : nat) : (term282 m n) = (term264 m n).
Proof. exact (eq_refl (term282 m n)). Qed.
Lemma lem258935 (m : nat) : (term289 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem258934 m n)). Qed.
Lemma lem258936 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258937 (m : nat) : (term290 m) = (term291 m).
Proof. exact (MK_COMB (@lem258936) (@lem258935 m)). Qed.
Lemma lem258938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem258939 (m : nat) : (term292 m) = (term293 m).
Proof. exact (MK_COMB (@lem258938) (@lem258937 m)). Qed.
Lemma lem258940 (m : nat) (n : nat) : (term284 m n) = (term261 m n).
Proof. exact (eq_refl (term284 m n)). Qed.
Lemma lem258941 (m : nat) : (term294 m) = (term281 m).
Proof. exact (fun_ext (fun n : nat => @lem258940 m n)). Qed.
Lemma lem258942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem258943 (m : nat) : (term295 m) = (term296 m).
Proof. exact (MK_COMB (@lem258942) (@lem258941 m)). Qed.
Lemma lem258944 (m : nat) : (term279 m) = (term297 m).
Proof. exact (MK_COMB (@lem258939 m) (@lem258943 m)). Qed.
Lemma lem258945 (m : nat) : ((term278 m) = (term279 m)) = ((term270 m) = (term297 m)).
Proof. exact (MK_COMB (@lem258933 m) (@lem258944 m)). Qed.
Lemma lem258946 (m : nat) : (term270 m) = (term297 m).
Proof. exact (EQ_MP (@lem258945 m) (@lem258923 m)). Qed.
Lemma lem259043 : term271 = term298.
Proof. exact (fun_ext (fun m : nat => @lem258946 m)). Qed.
Lemma lem259044 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259045 : term272 = term299.
Proof. exact (MK_COMB (@lem259044) (@lem259043)). Qed.
Lemma lem259047 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem259048 (P : nat -> Prop) (Q : nat -> Prop) : (term276 P Q) = (term277 P Q).
Proof. exact (@lem259047 nat P Q). Qed.
Lemma lem259049 : term300 = term301.
Proof. exact (@lem259048 term302 term303). Qed.
Lemma lem259050 (m : nat) : (term304 m) = (term291 m).
Proof. exact (eq_refl (term304 m)). Qed.
Lemma lem259051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259052 (m : nat) : (term305 m) = (term293 m).
Proof. exact (MK_COMB (@lem259051) (@lem259050 m)). Qed.
Lemma lem259053 (m : nat) : (term306 m) = (term296 m).
Proof. exact (eq_refl (term306 m)). Qed.
Lemma lem259054 (m : nat) : (term307 m) = (term297 m).
Proof. exact (MK_COMB (@lem259052 m) (@lem259053 m)). Qed.
Lemma lem259055 : term308 = term298.
Proof. exact (fun_ext (fun m : nat => @lem259054 m)). Qed.
Lemma lem259056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259057 : term300 = term299.
Proof. exact (MK_COMB (@lem259056) (@lem259055)). Qed.
Lemma lem259058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem259059 : term309 = term310.
Proof. exact (MK_COMB (@lem259058) (@lem259057)). Qed.
Lemma lem259060 (m : nat) : (term304 m) = (term291 m).
Proof. exact (eq_refl (term304 m)). Qed.
Lemma lem259061 : term311 = term302.
Proof. exact (fun_ext (fun m : nat => @lem259060 m)). Qed.
Lemma lem259062 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259063 : term312 = term313.
Proof. exact (MK_COMB (@lem259062) (@lem259061)). Qed.
Lemma lem259064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259065 : term314 = term315.
Proof. exact (MK_COMB (@lem259064) (@lem259063)). Qed.
Lemma lem259066 (m : nat) : (term306 m) = (term296 m).
Proof. exact (eq_refl (term306 m)). Qed.
Lemma lem259067 : term316 = term303.
Proof. exact (fun_ext (fun m : nat => @lem259066 m)). Qed.
Lemma lem259068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259069 : term317 = term318.
Proof. exact (MK_COMB (@lem259068) (@lem259067)). Qed.
Lemma lem259070 : term301 = term319.
Proof. exact (MK_COMB (@lem259065) (@lem259069)). Qed.
Lemma lem259071 : (term300 = term301) = (term299 = term319).
Proof. exact (MK_COMB (@lem259059) (@lem259070)). Qed.
Lemma lem259072 : term299 = term319.
Proof. exact (EQ_MP (@lem259071) (@lem259049)). Qed.
Lemma lem259177 : term272 = term319.
Proof. exact (TRANS (@lem259045) (@lem259072)). Qed.
Lemma lem259178 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem259181 : term273 = term320.
Proof. exact (MK_COMB (@lem259178) (@lem259177)). Qed.
Lemma lem259182 : term85 = term320.
Proof. exact (TRANS (@lem258911) (@lem259181)). Qed.
Lemma lem259183 (h1 : term85) : term320.
Proof. exact (EQ_MP (@lem259182) (@lem258574 h1)). Qed.
Lemma lem259204 (m : nat) (n : nat) : (term123 m n) = (term123 m n).
Proof. exact (eq_refl (term123 m n)). Qed.
Lemma lem259205 (m : nat) : (term125 m) = (term125 m).
Proof. exact (fun_ext (fun n : nat => @lem259204 m n)). Qed.
Lemma lem259206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259207 (m : nat) : (term127 m) = (term127 m).
Proof. exact (MK_COMB (@lem259206) (@lem259205 m)). Qed.
Lemma lem259208 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem259207 m)). Qed.
Lemma lem259209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259210 : term130 = term130.
Proof. exact (MK_COMB (@lem259209) (@lem259208)). Qed.
Lemma lem259216 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem259217 (P : nat -> Prop) (Q : nat -> Prop) : (term276 P Q) = (term277 P Q).
Proof. exact (@lem259216 nat P Q). Qed.
Lemma lem259218 (m : nat) : (term321 m) = (term322 m).
Proof. exact (@lem259217 (term323 m) (term324 m)). Qed.
Lemma lem259219 (n : nat) (m : nat) : (term325 m n) = (term326 n m).
Proof. exact (eq_refl (term325 m n)). Qed.
Lemma lem259220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259221 (n : nat) (m : nat) : (term327 m n) = (term328 n m).
Proof. exact (MK_COMB (@lem259220) (@lem259219 n m)). Qed.
Lemma lem259222 (m : nat) (n : nat) : (term329 m n) = (term330 m n).
Proof. exact (eq_refl (term329 m n)). Qed.
Lemma lem259223 (m : nat) (n : nat) : (term331 m n) = (term123 m n).
Proof. exact (MK_COMB (@lem259221 n m) (@lem259222 m n)). Qed.
Lemma lem259224 (m : nat) : (term332 m) = (term125 m).
Proof. exact (fun_ext (fun n : nat => @lem259223 m n)). Qed.
Lemma lem259225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259226 (m : nat) : (term321 m) = (term127 m).
Proof. exact (MK_COMB (@lem259225) (@lem259224 m)). Qed.
Lemma lem259227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem259228 (m : nat) : (term333 m) = (term334 m).
Proof. exact (MK_COMB (@lem259227) (@lem259226 m)). Qed.
Lemma lem259229 (n : nat) (m : nat) : (term325 m n) = (term326 n m).
Proof. exact (eq_refl (term325 m n)). Qed.
Lemma lem259230 (m : nat) : (term335 m) = (term323 m).
Proof. exact (fun_ext (fun n : nat => @lem259229 n m)). Qed.
Lemma lem259231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259232 (m : nat) : (term336 m) = (term337 m).
Proof. exact (MK_COMB (@lem259231) (@lem259230 m)). Qed.
Lemma lem259233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259234 (m : nat) : (term338 m) = (term339 m).
Proof. exact (MK_COMB (@lem259233) (@lem259232 m)). Qed.
Lemma lem259235 (m : nat) (n : nat) : (term329 m n) = (term330 m n).
Proof. exact (eq_refl (term329 m n)). Qed.
Lemma lem259236 (m : nat) : (term340 m) = (term324 m).
Proof. exact (fun_ext (fun n : nat => @lem259235 m n)). Qed.
Lemma lem259237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259238 (m : nat) : (term341 m) = (term342 m).
Proof. exact (MK_COMB (@lem259237) (@lem259236 m)). Qed.
Lemma lem259239 (m : nat) : (term322 m) = (term343 m).
Proof. exact (MK_COMB (@lem259234 m) (@lem259238 m)). Qed.
Lemma lem259240 (m : nat) : ((term321 m) = (term322 m)) = ((term127 m) = (term343 m)).
Proof. exact (MK_COMB (@lem259228 m) (@lem259239 m)). Qed.
Lemma lem259241 (m : nat) : (term127 m) = (term343 m).
Proof. exact (EQ_MP (@lem259240 m) (@lem259218 m)). Qed.
Lemma lem259338 : term129 = term344.
Proof. exact (fun_ext (fun m : nat => @lem259241 m)). Qed.
Lemma lem259339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259340 : term130 = term345.
Proof. exact (MK_COMB (@lem259339) (@lem259338)). Qed.
Lemma lem259342 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem259343 (P : nat -> Prop) (Q : nat -> Prop) : (term276 P Q) = (term277 P Q).
Proof. exact (@lem259342 nat P Q). Qed.
Lemma lem259344 : term346 = term347.
Proof. exact (@lem259343 term348 term349). Qed.
Lemma lem259345 (m : nat) : (term350 m) = (term337 m).
Proof. exact (eq_refl (term350 m)). Qed.
Lemma lem259346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259347 (m : nat) : (term351 m) = (term339 m).
Proof. exact (MK_COMB (@lem259346) (@lem259345 m)). Qed.
Lemma lem259348 (m : nat) : (term352 m) = (term342 m).
Proof. exact (eq_refl (term352 m)). Qed.
Lemma lem259349 (m : nat) : (term353 m) = (term343 m).
Proof. exact (MK_COMB (@lem259347 m) (@lem259348 m)). Qed.
Lemma lem259350 : term354 = term344.
Proof. exact (fun_ext (fun m : nat => @lem259349 m)). Qed.
Lemma lem259351 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259352 : term346 = term345.
Proof. exact (MK_COMB (@lem259351) (@lem259350)). Qed.
Lemma lem259353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem259354 : term355 = term356.
Proof. exact (MK_COMB (@lem259353) (@lem259352)). Qed.
Lemma lem259355 (m : nat) : (term350 m) = (term337 m).
Proof. exact (eq_refl (term350 m)). Qed.
Lemma lem259356 : term357 = term348.
Proof. exact (fun_ext (fun m : nat => @lem259355 m)). Qed.
Lemma lem259357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259358 : term358 = term359.
Proof. exact (MK_COMB (@lem259357) (@lem259356)). Qed.
Lemma lem259359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259360 : term360 = term361.
Proof. exact (MK_COMB (@lem259359) (@lem259358)). Qed.
Lemma lem259361 (m : nat) : (term352 m) = (term342 m).
Proof. exact (eq_refl (term352 m)). Qed.
Lemma lem259362 : term362 = term349.
Proof. exact (fun_ext (fun m : nat => @lem259361 m)). Qed.
Lemma lem259363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259364 : term363 = term364.
Proof. exact (MK_COMB (@lem259363) (@lem259362)). Qed.
Lemma lem259365 : term347 = term365.
Proof. exact (MK_COMB (@lem259360) (@lem259364)). Qed.
Lemma lem259366 : (term346 = term347) = (term345 = term365).
Proof. exact (MK_COMB (@lem259354) (@lem259365)). Qed.
Lemma lem259367 : term345 = term365.
Proof. exact (EQ_MP (@lem259366) (@lem259344)). Qed.
Lemma lem259474 : term130 = term365.
Proof. exact (TRANS (@lem259340) (@lem259367)). Qed.
Lemma lem259475 : term130 = term365.
Proof. exact (TRANS (@lem259210) (@lem259474)). Qed.
Lemma lem259476 (h1 : term130) : term365.
Proof. exact (EQ_MP (@lem259475) (@lem258575 h1)). Qed.
Lemma lem259477 (q : nat) (m : nat) (P : type1605) (h1 : term256 q m P) : term256 q m P.
Proof. exact (h1). Qed.
Lemma lem259478 (q : nat) (r : nat) (m : nat) (P : type1605) (h1 : term253 q r m P) : term253 q r m P.
Proof. exact (h1). Qed.
Lemma lem259511 (m : nat) (n : nat) : (term261 m n) = (term261 m n).
Proof. exact (eq_refl (term261 m n)). Qed.
Lemma lem259512 (m : nat) : (term281 m) = (term281 m).
Proof. exact (fun_ext (fun n : nat => @lem259511 m n)). Qed.
Lemma lem259513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259514 (m : nat) : (term296 m) = (term296 m).
Proof. exact (MK_COMB (@lem259513) (@lem259512 m)). Qed.
Lemma lem259515 : term303 = term303.
Proof. exact (fun_ext (fun m : nat => @lem259514 m)). Qed.
Lemma lem259516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259517 : term318 = term318.
Proof. exact (MK_COMB (@lem259516) (@lem259515)). Qed.
Lemma lem259544 (m : nat) (n : nat) : (term264 m n) = (term264 m n).
Proof. exact (eq_refl (term264 m n)). Qed.
Lemma lem259545 (m : nat) : (term280 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem259544 m n)). Qed.
Lemma lem259546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259547 (m : nat) : (term291 m) = (term291 m).
Proof. exact (MK_COMB (@lem259546) (@lem259545 m)). Qed.
Lemma lem259548 : term302 = term302.
Proof. exact (fun_ext (fun m : nat => @lem259547 m)). Qed.
Lemma lem259549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259550 : term313 = term313.
Proof. exact (MK_COMB (@lem259549) (@lem259548)). Qed.
Lemma lem259551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259552 : term315 = term315.
Proof. exact (MK_COMB (@lem259551) (@lem259550)). Qed.
Lemma lem259553 : term319 = term319.
Proof. exact (MK_COMB (@lem259552) (@lem259517)). Qed.
Lemma lem259562 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem259563 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem259562 m)). Qed.
Lemma lem259564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259565 : term80 = term80.
Proof. exact (MK_COMB (@lem259564) (@lem259563)). Qed.
Lemma lem259566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259567 : term82 = term82.
Proof. exact (MK_COMB (@lem259566) (@lem259565)). Qed.
Lemma lem259568 : term320 = term320.
Proof. exact (MK_COMB (@lem259567) (@lem259553)). Qed.
Lemma lem259569 (h1 : term85) : term320.
Proof. exact (EQ_MP (@lem259568) (@lem259183 h1)). Qed.
Lemma lem259612 (m : nat) (n : nat) : (term330 m n) = (term330 m n).
Proof. exact (eq_refl (term330 m n)). Qed.
Lemma lem259613 (m : nat) : (term324 m) = (term324 m).
Proof. exact (fun_ext (fun n : nat => @lem259612 m n)). Qed.
Lemma lem259614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259615 (m : nat) : (term342 m) = (term342 m).
Proof. exact (MK_COMB (@lem259614) (@lem259613 m)). Qed.
Lemma lem259616 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem259615 m)). Qed.
Lemma lem259617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259618 : term364 = term364.
Proof. exact (MK_COMB (@lem259617) (@lem259616)). Qed.
Lemma lem259653 (n : nat) (m : nat) : (term326 n m) = (term326 n m).
Proof. exact (eq_refl (term326 n m)). Qed.
Lemma lem259654 (m : nat) : (term323 m) = (term323 m).
Proof. exact (fun_ext (fun n : nat => @lem259653 n m)). Qed.
Lemma lem259655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259656 (m : nat) : (term337 m) = (term337 m).
Proof. exact (MK_COMB (@lem259655) (@lem259654 m)). Qed.
Lemma lem259657 : term348 = term348.
Proof. exact (fun_ext (fun m : nat => @lem259656 m)). Qed.
Lemma lem259658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259659 : term359 = term359.
Proof. exact (MK_COMB (@lem259658) (@lem259657)). Qed.
Lemma lem259660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem259661 : term361 = term361.
Proof. exact (MK_COMB (@lem259660) (@lem259659)). Qed.
Lemma lem259662 : term365 = term365.
Proof. exact (MK_COMB (@lem259661) (@lem259618)). Qed.
Lemma lem259663 (h1 : term130) : term365.
Proof. exact (EQ_MP (@lem259662) (@lem259476 h1)). Qed.
Lemma lem259722 (m : nat) (P : type1605) (q : nat) (r : nat) : (term160 m P q r) = (term160 m P q r).
Proof. exact (eq_refl (term160 m P q r)). Qed.
Lemma lem259723 (m : nat) (P : type1605) (q : nat) : (term170 m P q) = (term170 m P q).
Proof. exact (fun_ext (fun r : nat => @lem259722 m P q r)). Qed.
Lemma lem259724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259725 (m : nat) (P : type1605) (q : nat) : (term171 m P q) = (term171 m P q).
Proof. exact (MK_COMB (@lem259724) (@lem259723 m P q)). Qed.
Lemma lem259726 (m : nat) (P : type1605) : (term179 m P) = (term179 m P).
Proof. exact (fun_ext (fun q : nat => @lem259725 m P q)). Qed.
Lemma lem259727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259728 (m : nat) (P : type1605) : (term180 m P) = (term180 m P).
Proof. exact (MK_COMB (@lem259727) (@lem259726 m P)). Qed.
Lemma lem259749 (P : type1605) (m : nat) : (term181 P m) = (term181 P m).
Proof. exact (eq_refl (term181 P m)). Qed.
Lemma lem259750 (m : nat) (P : type1605) : (term183 m P) = (term183 m P).
Proof. exact (MK_COMB (@lem259749 P m) (@lem259728 m P)). Qed.
Lemma lem259825 (m : nat) (P : type1605) (q : nat) (r : nat) : (term251 m P q r) = (term251 m P q r).
Proof. exact (eq_refl (term251 m P q r)). Qed.
Lemma lem259826 (q : nat) (r : nat) (m : nat) (P : type1605) : (term253 q r m P) = (term253 q r m P).
Proof. exact (MK_COMB (@lem259825 m P q r) (@lem259750 m P)). Qed.
Lemma lem259827 (q : nat) (r : nat) (m : nat) (P : type1605) (h1 : term253 q r m P) : term253 q r m P.
Proof. exact (EQ_MP (@lem259826 q r m P) (@lem259478 q r m P h1)). Qed.
Lemma lem259829 (h1 : term130) : term359.
Proof. exact (proj1 (@lem259663 h1)). Qed.
Lemma lem259831 (h1 : term85) : term80.
Proof. exact (proj1 (@lem259569 h1)). Qed.
Lemma lem259834 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term215 m P q r.
Proof. exact (h1). Qed.
Lemma lem259835 (m : nat) (P : type1605) (h1 : term183 m P) : term183 m P.
Proof. exact (h1). Qed.
Lemma lem259836 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term156 m P q r.
Proof. exact (proj2 (@lem259834 m P q r h1)). Qed.
Lemma lem259839 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term47 m q r.
Proof. exact (proj1 (@lem259836 m P q r h1)). Qed.
Lemma lem259840 (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : term31 q r m.
Proof. exact (h1). Qed.
Lemma lem259841 (m : nat) (q : nat) (r : nat) (h1 : term45 m q r) : term45 m q r.
Proof. exact (h1). Qed.
Lemma lem259846 (m : nat) (P : type1605) (h1 : term183 m P) : term180 m P.
Proof. exact (proj2 (@lem259835 m P h1)). Qed.
Lemma lem259869 (n : nat) (m : nat) : (term326 n m) = (term366 n m).
Proof. exact (@lem19490 ((Nat.div m n) = (NUMERAL 0)) (term12 n) ((Nat.modulo m n) = m)). Qed.
Lemma lem259870 (m : nat) : (term323 m) = (term367 m).
Proof. exact (fun_ext (fun n : nat => @lem259869 n m)). Qed.
Lemma lem259871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259872 (m : nat) : (term337 m) = (term368 m).
Proof. exact (MK_COMB (@lem259871) (@lem259870 m)). Qed.
Lemma lem259873 : term348 = term369.
Proof. exact (fun_ext (fun m : nat => @lem259872 m)). Qed.
Lemma lem259874 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem259876 : term359 = term370.
Proof. exact (MK_COMB (@lem259874) (@lem259873)). Qed.
Lemma lem259877 (h1 : term130) : term370.
Proof. exact (EQ_MP (@lem259876) (@lem259829 h1)). Qed.
Lemma lem260032 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem260033 : term78 = term78.
Proof. exact (fun_ext (fun m : nat => @lem260032 m)). Qed.
Lemma lem260034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem260036 : term80 = term80.
Proof. exact (MK_COMB (@lem260034) (@lem260033)). Qed.
Lemma lem260037 (h1 : term85) : term80.
Proof. exact (EQ_MP (@lem260036) (@lem259831 h1)). Qed.
Lemma lem260123 (n : nat) (m : nat) : (term326 n m) = (term366 n m).
Proof. exact (@lem19490 ((Nat.div m n) = (NUMERAL 0)) (term12 n) ((Nat.modulo m n) = m)). Qed.
Lemma lem260124 (m : nat) : (term323 m) = (term367 m).
Proof. exact (fun_ext (fun n : nat => @lem260123 n m)). Qed.
Lemma lem260125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem260126 (m : nat) : (term337 m) = (term368 m).
Proof. exact (MK_COMB (@lem260125) (@lem260124 m)). Qed.
Lemma lem260127 : term348 = term369.
Proof. exact (fun_ext (fun m : nat => @lem260126 m)). Qed.
Lemma lem260128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem260130 : term359 = term370.
Proof. exact (MK_COMB (@lem260128) (@lem260127)). Qed.
Lemma lem260131 (h1 : term130) : term370.
Proof. exact (EQ_MP (@lem260130) (@lem259829 h1)). Qed.
Lemma lem260246 (m : nat) (P : type1605) (q : nat) (r : nat) : (term160 m P q r) = (term371 m P q r).
Proof. exact (@lem19699 (term147 q r m) (term149 m q r) (P q r)). Qed.
Lemma lem260247 (m : nat) (P : type1605) (q : nat) : (term170 m P q) = (term372 m P q).
Proof. exact (fun_ext (fun r : nat => @lem260246 m P q r)). Qed.
Lemma lem260248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem260249 (m : nat) (P : type1605) (q : nat) : (term171 m P q) = (term373 m P q).
Proof. exact (MK_COMB (@lem260248) (@lem260247 m P q)). Qed.
Lemma lem260250 (m : nat) (P : type1605) : (term179 m P) = (term374 m P).
Proof. exact (fun_ext (fun q : nat => @lem260249 m P q)). Qed.
Lemma lem260251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem260253 (m : nat) (P : type1605) : (term180 m P) = (term375 m P).
Proof. exact (MK_COMB (@lem260251) (@lem260250 m P)). Qed.
Lemma lem260254 (m : nat) (P : type1605) (h1 : term183 m P) : term375 m P.
Proof. exact (EQ_MP (@lem260253 m P) (@lem259846 m P h1)). Qed.
Lemma lem260255 (_5532 : nat) (h1 : term130) : term376 _5532.
Proof. exact (@lem259877 h1 _5532). Qed.
Lemma lem260256 (_5532 : nat) : (term376 _5532) = (term368 _5532).
Proof. exact (eq_refl (term376 _5532)). Qed.
Lemma lem260257 (_5532 : nat) (h1 : term130) : term368 _5532.
Proof. exact (EQ_MP (@lem260256 _5532) (@lem260255 _5532 h1)). Qed.
Lemma lem260258 (_5532 : nat) (_5533 : nat) (h1 : term130) : term377 _5532 _5533.
Proof. exact (@lem260257 _5532 h1 _5533). Qed.
Lemma lem260259 (_5533 : nat) (_5532 : nat) : (term377 _5532 _5533) = (term366 _5533 _5532).
Proof. exact (eq_refl (term377 _5532 _5533)). Qed.
Lemma lem260260 (_5533 : nat) (_5532 : nat) (h1 : term130) : term366 _5533 _5532.
Proof. exact (EQ_MP (@lem260259 _5533 _5532) (@lem260258 _5532 _5533 h1)). Qed.
Lemma lem260294 (_5545 : nat) (h1 : term85) : term378 _5545.
Proof. exact (@lem260037 h1 _5545). Qed.
Lemma lem260295 (_5545 : nat) : (term378 _5545) = (term76 _5545).
Proof. exact (eq_refl (term378 _5545)). Qed.
Lemma lem260309 (_5550 : nat) (h1 : term130) : term376 _5550.
Proof. exact (@lem260131 h1 _5550). Qed.
Lemma lem260310 (_5550 : nat) : (term376 _5550) = (term368 _5550).
Proof. exact (eq_refl (term376 _5550)). Qed.
Lemma lem260311 (_5550 : nat) (h1 : term130) : term368 _5550.
Proof. exact (EQ_MP (@lem260310 _5550) (@lem260309 _5550 h1)). Qed.
Lemma lem260312 (_5550 : nat) (_5551 : nat) (h1 : term130) : term377 _5550 _5551.
Proof. exact (@lem260311 _5550 h1 _5551). Qed.
Lemma lem260313 (_5551 : nat) (_5550 : nat) : (term377 _5550 _5551) = (term366 _5551 _5550).
Proof. exact (eq_refl (term377 _5550 _5551)). Qed.
Lemma lem260314 (_5551 : nat) (_5550 : nat) (h1 : term130) : term366 _5551 _5550.
Proof. exact (EQ_MP (@lem260313 _5551 _5550) (@lem260312 _5550 _5551 h1)). Qed.
Lemma lem260336 (_5559 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term379 m P _5559.
Proof. exact (@lem260254 m P h1 _5559). Qed.
Lemma lem260337 (m : nat) (P : type1605) (_5559 : nat) : (term379 m P _5559) = (term373 m P _5559).
Proof. exact (eq_refl (term379 m P _5559)). Qed.
Lemma lem260338 (_5559 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term373 m P _5559.
Proof. exact (EQ_MP (@lem260337 m P _5559) (@lem260336 _5559 m P h1)). Qed.
Lemma lem260339 (_5559 : nat) (_5560 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term380 m P _5559 _5560.
Proof. exact (@lem260338 _5559 m P h1 _5560). Qed.
Lemma lem260340 (m : nat) (P : type1605) (_5559 : nat) (_5560 : nat) : (term380 m P _5559 _5560) = (term371 m P _5559 _5560).
Proof. exact (eq_refl (term380 m P _5559 _5560)). Qed.
Lemma lem260341 (_5559 : nat) (_5560 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term371 m P _5559 _5560.
Proof. exact (EQ_MP (@lem260340 m P _5559 _5560) (@lem260339 _5559 _5560 m P h1)). Qed.
Lemma lem260355 (_5559 : nat) (_5560 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term381 m P _5559 _5560.
Proof. exact (proj1 (@lem260341 _5559 _5560 m P h1)). Qed.
Lemma lem260379 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term382 P q r.
Proof. exact (proj2 (@lem259836 m P q r h1)). Qed.
Lemma lem260383 (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : r = m.
Proof. exact (proj2 (@lem259840 q r m h1)). Qed.
Lemma lem260504 (m : nat) (P : type1605) (_5559 : nat) (_5560 : nat) : (term381 m P _5559 _5560) = (term383 m P _5559 _5560).
Proof. exact (@lem257954 (term12 _5559) (term384 _5560 m) (P _5559 _5560)). Qed.
Lemma lem260624 (P : type1605) (q : nat) : (term385 P q) = (term385 P q).
Proof. exact (eq_refl (term385 P q)). Qed.
Lemma lem260625 (P : type1605) (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : (term386 P q r) = (term386 P q m).
Proof. exact (MK_COMB (@lem260624 P q) (@lem260383 q r m h1)). Qed.
Lemma lem260626 (P : type1605) (q : nat) (m : nat) : (term386 P q m) = (term382 P q m).
Proof. exact (eq_refl (term386 P q m)). Qed.
Lemma lem260627 (P : type1605) (q : nat) (r : nat) : (term387 P q r) = (term387 P q r).
Proof. exact (eq_refl (term387 P q r)). Qed.
Lemma lem260628 (r : nat) (P : type1605) (q : nat) (m : nat) : ((term386 P q r) = (term386 P q m)) = ((term386 P q r) = (term382 P q m)).
Proof. exact (MK_COMB (@lem260627 P q r) (@lem260626 P q m)). Qed.
Lemma lem260629 (P : type1605) (q : nat) (r : nat) : (term386 P q r) = (term382 P q r).
Proof. exact (eq_refl (term386 P q r)). Qed.
Lemma lem260630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem260631 (P : type1605) (q : nat) (r : nat) : (term387 P q r) = (term388 P q r).
Proof. exact (MK_COMB (@lem260630) (@lem260629 P q r)). Qed.
Lemma lem260632 (P : type1605) (q : nat) (m : nat) : (term382 P q m) = (term382 P q m).
Proof. exact (eq_refl (term382 P q m)). Qed.
Lemma lem260633 (r : nat) (P : type1605) (q : nat) (m : nat) : ((term386 P q r) = (term382 P q m)) = ((term382 P q r) = (term382 P q m)).
Proof. exact (MK_COMB (@lem260631 P q r) (@lem260632 P q m)). Qed.
Lemma lem260634 (r : nat) (P : type1605) (q : nat) (m : nat) : ((term386 P q r) = (term386 P q m)) = ((term382 P q r) = (term382 P q m)).
Proof. exact (TRANS (@lem260628 r P q m) (@lem260633 r P q m)). Qed.
Lemma lem260635 (P : type1605) (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : (term382 P q r) = (term382 P q m).
Proof. exact (EQ_MP (@lem260634 r P q m) (@lem260625 P q r m h1)). Qed.
Lemma lem260636 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term31 q r m) (h2 : term215 m P q r) : term382 P q m.
Proof. exact (EQ_MP (@lem260635 P q r m h1) (@lem260379 m P q r h2)). Qed.
Lemma lem260650 (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : q = (NUMERAL 0).
Proof. exact (proj1 (@lem259840 q r m h1)). Qed.
Lemma lem260805 (P : type1605) (m : nat) : (term389 P m) = (term389 P m).
Proof. exact (eq_refl (term389 P m)). Qed.
Lemma lem260806 (P : type1605) (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : (term390 P m q) = (term391 P m).
Proof. exact (MK_COMB (@lem260805 P m) (@lem260650 q r m h1)). Qed.
Lemma lem260807 (P : type1605) (m : nat) : (term391 P m) = (term392 P m).
Proof. exact (eq_refl (term391 P m)). Qed.
Lemma lem260808 (P : type1605) (m : nat) (q : nat) : (term393 P m q) = (term393 P m q).
Proof. exact (eq_refl (term393 P m q)). Qed.
Lemma lem260809 (q : nat) (P : type1605) (m : nat) : ((term390 P m q) = (term391 P m)) = ((term390 P m q) = (term392 P m)).
Proof. exact (MK_COMB (@lem260808 P m q) (@lem260807 P m)). Qed.
Lemma lem260810 (P : type1605) (q : nat) (m : nat) : (term390 P m q) = (term382 P q m).
Proof. exact (eq_refl (term390 P m q)). Qed.
Lemma lem260811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem260812 (P : type1605) (q : nat) (m : nat) : (term393 P m q) = (term388 P q m).
Proof. exact (MK_COMB (@lem260811) (@lem260810 P q m)). Qed.
Lemma lem260813 (P : type1605) (m : nat) : (term392 P m) = (term392 P m).
Proof. exact (eq_refl (term392 P m)). Qed.
Lemma lem260814 (q : nat) (P : type1605) (m : nat) : ((term390 P m q) = (term392 P m)) = ((term382 P q m) = (term392 P m)).
Proof. exact (MK_COMB (@lem260812 P q m) (@lem260813 P m)). Qed.
Lemma lem260815 (q : nat) (P : type1605) (m : nat) : ((term390 P m q) = (term391 P m)) = ((term382 P q m) = (term392 P m)).
Proof. exact (TRANS (@lem260809 q P m) (@lem260814 q P m)). Qed.
Lemma lem260816 (P : type1605) (q : nat) (r : nat) (m : nat) (h1 : term31 q r m) : (term382 P q m) = (term392 P m).
Proof. exact (EQ_MP (@lem260815 q P m) (@lem260806 P q r m h1)). Qed.
Lemma lem260971 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term31 q r m) (h2 : term215 m P q r) : term392 P m.
Proof. exact (EQ_MP (@lem260816 P q r m h1) (@lem260636 m P q r h1 h2)). Qed.
Lemma lem261041 (_5532 : nat) (_5533 : nat) (h1 : term130) : term394 _5532 _5533.
Proof. exact (proj1 (@lem260260 _5533 _5532 h1)). Qed.
Lemma lem261055 (_5533 : nat) (_5532 : nat) (h1 : term130) : term395 _5533 _5532.
Proof. exact (proj2 (@lem260260 _5533 _5532 h1)). Qed.
Lemma lem261264 (_5545 : nat) (h1 : term85) : term76 _5545.
Proof. exact (EQ_MP (@lem260295 _5545) (@lem260294 _5545 h1)). Qed.
Lemma lem261460 (m : nat) (P : type1605) (h1 : term183 m P) : term396 P m.
Proof. exact (proj1 (@lem259835 m P h1)). Qed.
Lemma lem261474 (_5559 : nat) (_5560 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term383 m P _5559 _5560.
Proof. exact (EQ_MP (@lem260504 m P _5559 _5560) (@lem260355 _5559 _5560 m P h1)). Qed.
Lemma lem261558 (_5550 : nat) (_5551 : nat) (h1 : term130) : term394 _5550 _5551.
Proof. exact (proj1 (@lem260314 _5551 _5550 h1)). Qed.
Lemma lem261572 (_5551 : nat) (_5550 : nat) (h1 : term130) : term395 _5551 _5550.
Proof. exact (proj2 (@lem260314 _5551 _5550 h1)). Qed.
Lemma lem261573 (P : type1605) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem261574 (_5707 : nat) (_5709 : nat) (h1 : _5707 = _5709) : _5707 = _5709.
Proof. exact (h1). Qed.
Lemma lem261575 (_5708 : nat) (_5710 : nat) (h1 : _5708 = _5710) : _5708 = _5710.
Proof. exact (h1). Qed.
Lemma lem261576 (P : type1605) (_5707 : nat) (_5709 : nat) (h1 : _5707 = _5709) : (P _5707) = (P _5709).
Proof. exact (MK_COMB (@lem261573 P) (@lem261574 _5707 _5709 h1)). Qed.
Lemma lem261577 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) (h1 : _5707 = _5709) (h2 : _5708 = _5710) : (P _5707 _5708) = (P _5709 _5710).
Proof. exact (MK_COMB (@lem261576 P _5707 _5709 h1) (@lem261575 _5708 _5710 h2)). Qed.
Lemma lem261579 (b : Prop) (a : Prop) : term397 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem261580 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : term398 _5709 _5710 P _5707 _5708.
Proof. exact (@lem261579 (P _5709 _5710) (P _5707 _5708)). Qed.
Lemma lem261581 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) (h1 : _5707 = _5709) (h2 : _5708 = _5710) : term399 _5709 _5710 P _5707 _5708.
Proof. exact (@lem261580 _5709 _5710 P _5707 _5708 (@lem261577 P _5707 _5709 _5708 _5710 h1 h2)). Qed.
Lemma lem261582 (_5710 : nat) (P : type1605) (_5708 : nat) (_5707 : nat) (_5709 : nat) (h1 : _5707 = _5709) : term400 _5709 _5710 P _5707 _5708.
Proof. exact (fun h0 : _5708 = _5710 => @lem261581 P _5707 _5709 _5708 _5710 h1 h0). Qed.
Lemma lem261584 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem261585 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term400 _5709 _5710 P _5707 _5708) = (term402 _5709 _5710 P _5707 _5708).
Proof. exact (@lem261584 (_5708 = _5710) (term399 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem261586 (_5710 : nat) (P : type1605) (_5708 : nat) (_5707 : nat) (_5709 : nat) (h1 : _5707 = _5709) : term402 _5709 _5710 P _5707 _5708.
Proof. exact (EQ_MP (@lem261585 _5709 _5710 P _5707 _5708) (@lem261582 _5710 P _5708 _5707 _5709 h1)). Qed.
Lemma lem261587 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : term403 _5709 _5710 P _5707 _5708.
Proof. exact (fun h0 : _5707 = _5709 => @lem261586 _5710 P _5708 _5707 _5709 h0). Qed.
Lemma lem261589 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem261590 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term403 _5709 _5710 P _5707 _5708) = (term404 _5709 _5710 P _5707 _5708).
Proof. exact (@lem261589 (_5707 = _5709) (term402 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem261591 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : term404 _5709 _5710 P _5707 _5708.
Proof. exact (EQ_MP (@lem261590 _5709 _5710 P _5707 _5708) (@lem261587 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem261690 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem261691 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem261690 (NUMERAL 0)). Qed.
Lemma lem261692 : term405.
Proof. exact (fun h0 : term406 => @lem261691). Qed.
Lemma lem261694 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem261695 : term405 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem261694 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem261696 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem261695) (@lem261692)). Qed.
Lemma lem261702 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem261703 (_5532 : nat) (_5533 : nat) : (term394 _5532 _5533) = (term408 _5532 _5533).
Proof. exact (@lem261702 ((Nat.div _5532 _5533) = (NUMERAL 0)) (term12 _5533)). Qed.
Lemma lem261713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem261714 (_5532 : nat) (_5533 : nat) : (term409 _5532 _5533) = (term410 _5532 _5533).
Proof. exact (MK_COMB (@lem261713) (@lem261703 _5532 _5533)). Qed.
Lemma lem261724 (_5532 : nat) (_5533 : nat) : (term408 _5532 _5533) = (term408 _5532 _5533).
Proof. exact (eq_refl (term408 _5532 _5533)). Qed.
Lemma lem261725 (_5532 : nat) (_5533 : nat) : ((term394 _5532 _5533) = (term408 _5532 _5533)) = ((term408 _5532 _5533) = (term408 _5532 _5533)).
Proof. exact (MK_COMB (@lem261714 _5532 _5533) (@lem261724 _5532 _5533)). Qed.
Lemma lem261727 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem261728 (x : Prop) : (x = x) = True.
Proof. exact (@lem261727 Prop x). Qed.
Lemma lem261729 (_5532 : nat) (_5533 : nat) : ((term408 _5532 _5533) = (term408 _5532 _5533)) = True.
Proof. exact (@lem261728 (term408 _5532 _5533)). Qed.
Lemma lem261730 (_5532 : nat) (_5533 : nat) : ((term394 _5532 _5533) = (term408 _5532 _5533)) = True.
Proof. exact (TRANS (@lem261725 _5532 _5533) (@lem261729 _5532 _5533)). Qed.
Lemma lem261731 (_5532 : nat) (_5533 : nat) : True = ((term394 _5532 _5533) = (term408 _5532 _5533)).
Proof. exact (SYM (@lem261730 _5532 _5533)). Qed.
Lemma lem261732 (_5532 : nat) (_5533 : nat) : (term394 _5532 _5533) = (term408 _5532 _5533).
Proof. exact (EQ_MP (@lem261731 _5532 _5533) (@lem0)). Qed.
Lemma lem261733 (_5532 : nat) (_5533 : nat) (h1 : term130) : term408 _5532 _5533.
Proof. exact (EQ_MP (@lem261732 _5532 _5533) (@lem261041 _5532 _5533 h1)). Qed.
Lemma lem261735 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem261736 (_5532 : nat) (_5533 : nat) : (term408 _5532 _5533) = (term412 _5532 _5533).
Proof. exact (@lem261735 (term12 _5533) ((Nat.div _5532 _5533) = (NUMERAL 0))). Qed.
Lemma lem261738 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem261739 (_5533 : nat) : (term414 _5533) = (_5533 = (NUMERAL 0)).
Proof. exact (@lem261738 (_5533 = (NUMERAL 0))). Qed.
Lemma lem261740 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem261741 (_5533 : nat) : (term415 _5533) = (term96 _5533).
Proof. exact (MK_COMB (@lem261740) (@lem261739 _5533)). Qed.
Lemma lem261742 (_5532 : nat) (_5533 : nat) : ((Nat.div _5532 _5533) = (NUMERAL 0)) = ((Nat.div _5532 _5533) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.div _5532 _5533) = (NUMERAL 0))). Qed.
Lemma lem261743 (_5532 : nat) (_5533 : nat) : (term412 _5532 _5533) = (term416 _5532 _5533).
Proof. exact (MK_COMB (@lem261741 _5533) (@lem261742 _5532 _5533)). Qed.
Lemma lem261744 (_5532 : nat) (_5533 : nat) : (term408 _5532 _5533) = (term416 _5532 _5533).
Proof. exact (TRANS (@lem261736 _5532 _5533) (@lem261743 _5532 _5533)). Qed.
Lemma lem261747 (_5532 : nat) (_5533 : nat) (h1 : term130) : term416 _5532 _5533.
Proof. exact (EQ_MP (@lem261744 _5532 _5533) (@lem261733 _5532 _5533 h1)). Qed.
Lemma lem261748 (_5532 : nat) (h1 : term130) : term417 _5532.
Proof. exact (@lem261747 _5532 (NUMERAL 0) h1). Qed.
Lemma lem261751 (_5532 : nat) (h1 : term130) : (term21 _5532) = (NUMERAL 0).
Proof. exact (@lem261748 _5532 h1 (@lem261696)). Qed.
Lemma lem261752 (m : nat) (h1 : term130) : (term21 m) = (NUMERAL 0).
Proof. exact (@lem261751 m h1). Qed.
Lemma lem261753 (m : nat) (h1 : term130) : term418 m.
Proof. exact (fun h0 : term419 m => @lem261752 m h1). Qed.
Lemma lem261755 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem261756 (m : nat) : (term418 m) = ((term21 m) = (NUMERAL 0)).
Proof. exact (@lem261755 ((term21 m) = (NUMERAL 0))). Qed.
Lemma lem261757 (m : nat) (h1 : term130) : (term21 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem261756 m) (@lem261753 m h1)). Qed.
Lemma lem261759 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem261760 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem261759 (NUMERAL 0)). Qed.
Lemma lem261761 : term405.
Proof. exact (fun h0 : term406 => @lem261760). Qed.
Lemma lem261763 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem261764 : term405 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem261763 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem261765 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem261764) (@lem261761)). Qed.
Lemma lem261771 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem261772 (_5532 : nat) (_5533 : nat) : (term395 _5533 _5532) = (term420 _5532 _5533).
Proof. exact (@lem261771 ((Nat.modulo _5532 _5533) = _5532) (term12 _5533)). Qed.
Lemma lem261782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem261783 (_5532 : nat) (_5533 : nat) : (term421 _5533 _5532) = (term422 _5532 _5533).
Proof. exact (MK_COMB (@lem261782) (@lem261772 _5532 _5533)). Qed.
Lemma lem261793 (_5532 : nat) (_5533 : nat) : (term420 _5532 _5533) = (term420 _5532 _5533).
Proof. exact (eq_refl (term420 _5532 _5533)). Qed.
Lemma lem261794 (_5532 : nat) (_5533 : nat) : ((term395 _5533 _5532) = (term420 _5532 _5533)) = ((term420 _5532 _5533) = (term420 _5532 _5533)).
Proof. exact (MK_COMB (@lem261783 _5532 _5533) (@lem261793 _5532 _5533)). Qed.
Lemma lem261796 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem261797 (x : Prop) : (x = x) = True.
Proof. exact (@lem261796 Prop x). Qed.
Lemma lem261798 (_5532 : nat) (_5533 : nat) : ((term420 _5532 _5533) = (term420 _5532 _5533)) = True.
Proof. exact (@lem261797 (term420 _5532 _5533)). Qed.
Lemma lem261799 (_5532 : nat) (_5533 : nat) : ((term395 _5533 _5532) = (term420 _5532 _5533)) = True.
Proof. exact (TRANS (@lem261794 _5532 _5533) (@lem261798 _5532 _5533)). Qed.
Lemma lem261800 (_5532 : nat) (_5533 : nat) : True = ((term395 _5533 _5532) = (term420 _5532 _5533)).
Proof. exact (SYM (@lem261799 _5532 _5533)). Qed.
Lemma lem261801 (_5532 : nat) (_5533 : nat) : (term395 _5533 _5532) = (term420 _5532 _5533).
Proof. exact (EQ_MP (@lem261800 _5532 _5533) (@lem0)). Qed.
Lemma lem261802 (_5532 : nat) (_5533 : nat) (h1 : term130) : term420 _5532 _5533.
Proof. exact (EQ_MP (@lem261801 _5532 _5533) (@lem261055 _5533 _5532 h1)). Qed.
Lemma lem261804 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem261805 (_5533 : nat) (_5532 : nat) : (term420 _5532 _5533) = (term423 _5533 _5532).
Proof. exact (@lem261804 (term12 _5533) ((Nat.modulo _5532 _5533) = _5532)). Qed.
Lemma lem261807 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem261808 (_5533 : nat) : (term414 _5533) = (_5533 = (NUMERAL 0)).
Proof. exact (@lem261807 (_5533 = (NUMERAL 0))). Qed.
Lemma lem261809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem261810 (_5533 : nat) : (term415 _5533) = (term96 _5533).
Proof. exact (MK_COMB (@lem261809) (@lem261808 _5533)). Qed.
Lemma lem261811 (_5533 : nat) (_5532 : nat) : ((Nat.modulo _5532 _5533) = _5532) = ((Nat.modulo _5532 _5533) = _5532).
Proof. exact (eq_refl ((Nat.modulo _5532 _5533) = _5532)). Qed.
Lemma lem261812 (_5533 : nat) (_5532 : nat) : (term423 _5533 _5532) = (term424 _5533 _5532).
Proof. exact (MK_COMB (@lem261810 _5533) (@lem261811 _5533 _5532)). Qed.
Lemma lem261813 (_5533 : nat) (_5532 : nat) : (term420 _5532 _5533) = (term424 _5533 _5532).
Proof. exact (TRANS (@lem261805 _5533 _5532) (@lem261812 _5533 _5532)). Qed.
Lemma lem261816 (_5533 : nat) (_5532 : nat) (h1 : term130) : term424 _5533 _5532.
Proof. exact (EQ_MP (@lem261813 _5533 _5532) (@lem261802 _5532 _5533 h1)). Qed.
Lemma lem261817 (_5532 : nat) (h1 : term130) : term425 _5532.
Proof. exact (@lem261816 (NUMERAL 0) _5532 h1). Qed.
Lemma lem261820 (_5532 : nat) (h1 : term130) : (term24 _5532) = _5532.
Proof. exact (@lem261817 _5532 h1 (@lem261765)). Qed.
Lemma lem261821 (m : nat) (h1 : term130) : (term24 m) = m.
Proof. exact (@lem261820 m h1). Qed.
Lemma lem261822 (m : nat) (h1 : term130) : term426 m.
Proof. exact (fun h0 : term427 m => @lem261821 m h1). Qed.
Lemma lem261824 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem261825 (m : nat) : (term426 m) = ((term24 m) = m).
Proof. exact (@lem261824 ((term24 m) = m)). Qed.
Lemma lem261826 (m : nat) (h1 : term130) : (term24 m) = m.
Proof. exact (EQ_MP (@lem261825 m) (@lem261822 m h1)). Qed.
Lemma lem261828 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term26 P m.
Proof. exact (proj1 (@lem259834 m P q r h1)). Qed.
Lemma lem261829 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term428 P m.
Proof. exact (fun h0 : term396 P m => @lem261828 m P q r h1). Qed.
Lemma lem261831 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem261832 (P : type1605) (m : nat) : (term428 P m) = (term26 P m).
Proof. exact (@lem261831 (term26 P m)). Qed.
Lemma lem261833 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term215 m P q r) : term26 P m.
Proof. exact (EQ_MP (@lem261832 P m) (@lem261829 m P q r h1)). Qed.
Lemma lem261851 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem261852 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term402 _5709 _5710 P _5707 _5708) = (term429 _5709 _5710 P _5707 _5708).
Proof. exact (@lem261851 (P _5709 _5710) (term384 _5708 _5710) (term382 P _5707 _5708)). Qed.
Lemma lem261866 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem261867 (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term430 _5710 P _5707 _5708) = (term431 P _5707 _5708 _5710).
Proof. exact (@lem261866 (term382 P _5707 _5708) (term384 _5708 _5710)). Qed.
Lemma lem261875 (P : type1605) (_5709 : nat) (_5710 : nat) : (term432 P _5709 _5710) = (term432 P _5709 _5710).
Proof. exact (eq_refl (term432 P _5709 _5710)). Qed.
Lemma lem261876 (_5709 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term429 _5709 _5710 P _5707 _5708) = (term433 _5709 P _5707 _5708 _5710).
Proof. exact (MK_COMB (@lem261875 P _5709 _5710) (@lem261867 P _5707 _5708 _5710)). Qed.
Lemma lem261887 (_5709 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term402 _5709 _5710 P _5707 _5708) = (term433 _5709 P _5707 _5708 _5710).
Proof. exact (TRANS (@lem261852 _5709 _5710 P _5707 _5708) (@lem261876 _5709 P _5707 _5708 _5710)). Qed.
Lemma lem261888 (_5707 : nat) (_5709 : nat) : (term434 _5707 _5709) = (term434 _5707 _5709).
Proof. exact (eq_refl (term434 _5707 _5709)). Qed.
Lemma lem261889 (_5709 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term404 _5709 _5710 P _5707 _5708) = (term435 _5709 P _5707 _5708 _5710).
Proof. exact (MK_COMB (@lem261888 _5707 _5709) (@lem261887 _5709 P _5707 _5708 _5710)). Qed.
Lemma lem261893 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem261894 (_5709 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term435 _5709 P _5707 _5708 _5710) = (term436 _5709 P _5707 _5708 _5710).
Proof. exact (@lem261893 (P _5709 _5710) (term384 _5707 _5709) (term431 P _5707 _5708 _5710)). Qed.
Lemma lem261908 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem261909 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term437 _5709 P _5707 _5708 _5710) = (term438 P _5707 _5709 _5708 _5710).
Proof. exact (@lem261908 (term382 P _5707 _5708) (term384 _5707 _5709) (term384 _5708 _5710)). Qed.
Lemma lem261929 (P : type1605) (_5709 : nat) (_5710 : nat) : (term432 P _5709 _5710) = (term432 P _5709 _5710).
Proof. exact (eq_refl (term432 P _5709 _5710)). Qed.
Lemma lem261930 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term436 _5709 P _5707 _5708 _5710) = (term439 P _5707 _5709 _5708 _5710).
Proof. exact (MK_COMB (@lem261929 P _5709 _5710) (@lem261909 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem261941 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term435 _5709 P _5707 _5708 _5710) = (term439 P _5707 _5709 _5708 _5710).
Proof. exact (TRANS (@lem261894 _5709 P _5707 _5708 _5710) (@lem261930 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem261942 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term404 _5709 _5710 P _5707 _5708) = (term439 P _5707 _5709 _5708 _5710).
Proof. exact (TRANS (@lem261889 _5709 P _5707 _5708 _5710) (@lem261941 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem261943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem261944 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term440 _5709 _5710 P _5707 _5708) = (term441 P _5707 _5709 _5708 _5710).
Proof. exact (MK_COMB (@lem261943) (@lem261942 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem261970 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem261971 (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term430 _5710 P _5707 _5708) = (term431 P _5707 _5708 _5710).
Proof. exact (@lem261970 (term382 P _5707 _5708) (term384 _5708 _5710)). Qed.
Lemma lem261979 (_5707 : nat) (_5709 : nat) : (term434 _5707 _5709) = (term434 _5707 _5709).
Proof. exact (eq_refl (term434 _5707 _5709)). Qed.
Lemma lem261980 (_5709 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) (_5710 : nat) : (term442 _5709 _5710 P _5707 _5708) = (term437 _5709 P _5707 _5708 _5710).
Proof. exact (MK_COMB (@lem261979 _5707 _5709) (@lem261971 P _5707 _5708 _5710)). Qed.
Lemma lem261984 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem261985 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term437 _5709 P _5707 _5708 _5710) = (term438 P _5707 _5709 _5708 _5710).
Proof. exact (@lem261984 (term382 P _5707 _5708) (term384 _5707 _5709) (term384 _5708 _5710)). Qed.
Lemma lem262005 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term442 _5709 _5710 P _5707 _5708) = (term438 P _5707 _5709 _5708 _5710).
Proof. exact (TRANS (@lem261980 _5709 P _5707 _5708 _5710) (@lem261985 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem262006 (P : type1605) (_5709 : nat) (_5710 : nat) : (term432 P _5709 _5710) = (term432 P _5709 _5710).
Proof. exact (eq_refl (term432 P _5709 _5710)). Qed.
Lemma lem262007 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : (term443 _5709 _5710 P _5707 _5708) = (term439 P _5707 _5709 _5708 _5710).
Proof. exact (MK_COMB (@lem262006 P _5709 _5710) (@lem262005 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem262018 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : ((term404 _5709 _5710 P _5707 _5708) = (term443 _5709 _5710 P _5707 _5708)) = ((term439 P _5707 _5709 _5708 _5710) = (term439 P _5707 _5709 _5708 _5710)).
Proof. exact (MK_COMB (@lem261944 P _5707 _5709 _5708 _5710) (@lem262007 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem262020 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem262021 (x : Prop) : (x = x) = True.
Proof. exact (@lem262020 Prop x). Qed.
Lemma lem262022 (P : type1605) (_5707 : nat) (_5709 : nat) (_5708 : nat) (_5710 : nat) : ((term439 P _5707 _5709 _5708 _5710) = (term439 P _5707 _5709 _5708 _5710)) = True.
Proof. exact (@lem262021 (term439 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem262023 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : ((term404 _5709 _5710 P _5707 _5708) = (term443 _5709 _5710 P _5707 _5708)) = True.
Proof. exact (TRANS (@lem262018 P _5707 _5709 _5708 _5710) (@lem262022 P _5707 _5709 _5708 _5710)). Qed.
Lemma lem262024 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : True = ((term404 _5709 _5710 P _5707 _5708) = (term443 _5709 _5710 P _5707 _5708)).
Proof. exact (SYM (@lem262023 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem262025 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term404 _5709 _5710 P _5707 _5708) = (term443 _5709 _5710 P _5707 _5708).
Proof. exact (EQ_MP (@lem262024 _5709 _5710 P _5707 _5708) (@lem0)). Qed.
Lemma lem262026 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : term443 _5709 _5710 P _5707 _5708.
Proof. exact (EQ_MP (@lem262025 _5709 _5710 P _5707 _5708) (@lem261591 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem262028 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem262029 (_5707 : nat) (_5708 : nat) (P : type1605) (_5709 : nat) (_5710 : nat) : (term443 _5709 _5710 P _5707 _5708) = (term444 _5707 _5708 P _5709 _5710).
Proof. exact (@lem262028 (term442 _5709 _5710 P _5707 _5708) (P _5709 _5710)). Qed.
Lemma lem262031 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem262032 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term447 _5709 _5710 P _5707 _5708) = (term448 _5709 _5710 P _5707 _5708).
Proof. exact (@lem262031 (term384 _5707 _5709) (term430 _5710 P _5707 _5708)). Qed.
Lemma lem262034 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262035 (_5707 : nat) (_5709 : nat) : (term449 _5707 _5709) = (_5707 = _5709).
Proof. exact (@lem262034 (_5707 = _5709)). Qed.
Lemma lem262036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262037 (_5707 : nat) (_5709 : nat) : (term450 _5707 _5709) = (term451 _5707 _5709).
Proof. exact (MK_COMB (@lem262036) (@lem262035 _5707 _5709)). Qed.
Lemma lem262039 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem262040 (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term452 _5710 P _5707 _5708) = (term453 _5710 P _5707 _5708).
Proof. exact (@lem262039 (term384 _5708 _5710) (term382 P _5707 _5708)). Qed.
Lemma lem262042 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262043 (_5708 : nat) (_5710 : nat) : (term449 _5708 _5710) = (_5708 = _5710).
Proof. exact (@lem262042 (_5708 = _5710)). Qed.
Lemma lem262044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262045 (_5708 : nat) (_5710 : nat) : (term450 _5708 _5710) = (term451 _5708 _5710).
Proof. exact (MK_COMB (@lem262044) (@lem262043 _5708 _5710)). Qed.
Lemma lem262047 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262048 (P : type1605) (_5707 : nat) (_5708 : nat) : (term454 P _5707 _5708) = (P _5707 _5708).
Proof. exact (@lem262047 (P _5707 _5708)). Qed.
Lemma lem262049 (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term453 _5710 P _5707 _5708) = (term455 _5710 P _5707 _5708).
Proof. exact (MK_COMB (@lem262045 _5708 _5710) (@lem262048 P _5707 _5708)). Qed.
Lemma lem262050 (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term452 _5710 P _5707 _5708) = (term455 _5710 P _5707 _5708).
Proof. exact (TRANS (@lem262040 _5710 P _5707 _5708) (@lem262049 _5710 P _5707 _5708)). Qed.
Lemma lem262051 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term448 _5709 _5710 P _5707 _5708) = (term456 _5709 _5710 P _5707 _5708).
Proof. exact (MK_COMB (@lem262037 _5707 _5709) (@lem262050 _5710 P _5707 _5708)). Qed.
Lemma lem262052 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term447 _5709 _5710 P _5707 _5708) = (term456 _5709 _5710 P _5707 _5708).
Proof. exact (TRANS (@lem262032 _5709 _5710 P _5707 _5708) (@lem262051 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem262053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262054 (_5709 : nat) (_5710 : nat) (P : type1605) (_5707 : nat) (_5708 : nat) : (term457 _5709 _5710 P _5707 _5708) = (term458 _5709 _5710 P _5707 _5708).
Proof. exact (MK_COMB (@lem262053) (@lem262052 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem262055 (P : type1605) (_5709 : nat) (_5710 : nat) : (P _5709 _5710) = (P _5709 _5710).
Proof. exact (eq_refl (P _5709 _5710)). Qed.
Lemma lem262056 (_5707 : nat) (_5708 : nat) (P : type1605) (_5709 : nat) (_5710 : nat) : (term444 _5707 _5708 P _5709 _5710) = (term459 _5707 _5708 P _5709 _5710).
Proof. exact (MK_COMB (@lem262054 _5709 _5710 P _5707 _5708) (@lem262055 P _5709 _5710)). Qed.
Lemma lem262057 (_5707 : nat) (_5708 : nat) (P : type1605) (_5709 : nat) (_5710 : nat) : (term443 _5709 _5710 P _5707 _5708) = (term459 _5707 _5708 P _5709 _5710).
Proof. exact (TRANS (@lem262029 _5707 _5708 P _5709 _5710) (@lem262056 _5707 _5708 P _5709 _5710)). Qed.
Lemma lem262059 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term215 m P q r) : term460 P m.
Proof. exact (conj (@lem261826 m h1) (@lem261833 m P q r h2)). Qed.
Lemma lem262060 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term215 m P q r) : term461 P m.
Proof. exact (conj (@lem261757 m h1) (@lem262059 m P q r h1 h2)). Qed.
Lemma lem262062 (_5707 : nat) (_5708 : nat) (P : type1605) (_5709 : nat) (_5710 : nat) : term459 _5707 _5708 P _5709 _5710.
Proof. exact (EQ_MP (@lem262057 _5707 _5708 P _5709 _5710) (@lem262026 _5709 _5710 P _5707 _5708)). Qed.
Lemma lem262063 (P : type1605) (m : nat) : term462 P m.
Proof. exact (@lem262062 (term21 m) (term24 m) P (NUMERAL 0) m). Qed.
Lemma lem262066 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term215 m P q r) : term463 P m.
Proof. exact (@lem262063 P m (@lem262060 m P q r h1 h2)). Qed.
Lemma lem262067 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term215 m P q r) : term464 P m.
Proof. exact (fun h0 : term392 P m => @lem262066 m P q r h1 h2). Qed.
Lemma lem262069 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262070 (P : type1605) (m : nat) : (term464 P m) = (term463 P m).
Proof. exact (@lem262069 (term463 P m)). Qed.
Lemma lem262071 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term215 m P q r) : term463 P m.
Proof. exact (EQ_MP (@lem262070 P m) (@lem262067 m P q r h1 h2)). Qed.
Lemma lem262074 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem262076 (P : type1605) (m : nat) : (term392 P m) = (term465 P m).
Proof. exact (@lem262074 (term463 P m)). Qed.
Lemma lem262079 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term31 q r m) (h2 : term215 m P q r) : term465 P m.
Proof. exact (EQ_MP (@lem262076 P m) (@lem260971 m P q r h1 h2)). Qed.
Lemma lem262082 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term31 q r m) (h3 : term215 m P q r) : False.
Proof. exact (@lem262079 m P q r h2 h3 (@lem262071 m P q r h1 h3)). Qed.
Lemma lem262083 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term31 q r m) (h3 : term215 m P q r) : term466.
Proof. exact (fun h0 : ~ False => @lem262082 m P q r h1 h2 h3). Qed.
Lemma lem262085 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262086 : term466 = False.
Proof. exact (@lem262085 False). Qed.
Lemma lem262205 (m : nat) (q : nat) (r : nat) (h1 : term45 m q r) : term43 r.
Proof. exact (proj2 (@lem259841 m q r h1)). Qed.
Lemma lem262206 (m : nat) (q : nat) (r : nat) (h1 : term45 m q r) : term467 r.
Proof. exact (fun h0 : term76 r => @lem262205 m q r h1). Qed.
Lemma lem262208 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262209 (r : nat) : (term467 r) = (term43 r).
Proof. exact (@lem262208 (term43 r)). Qed.
Lemma lem262210 (m : nat) (q : nat) (r : nat) (h1 : term45 m q r) : term43 r.
Proof. exact (EQ_MP (@lem262209 r) (@lem262206 m q r h1)). Qed.
Lemma lem262213 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem262215 (_5545 : nat) : (term76 _5545) = (term468 _5545).
Proof. exact (@lem262213 (term43 _5545)). Qed.
Lemma lem262218 (_5545 : nat) (h1 : term85) : term468 _5545.
Proof. exact (EQ_MP (@lem262215 _5545) (@lem261264 _5545 h1)). Qed.
Lemma lem262219 (r : nat) (h1 : term85) : term468 r.
Proof. exact (@lem262218 r h1). Qed.
Lemma lem262222 (m : nat) (q : nat) (r : nat) (h1 : term85) (h2 : term45 m q r) : False.
Proof. exact (@lem262219 r h1 (@lem262210 m q r h2)). Qed.
Lemma lem262223 (m : nat) (q : nat) (r : nat) (h1 : term85) (h2 : term45 m q r) : term466.
Proof. exact (fun h0 : ~ False => @lem262222 m q r h1 h2). Qed.
Lemma lem262225 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262226 : term466 = False.
Proof. exact (@lem262225 False). Qed.
Lemma lem262345 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem262346 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem262345 (NUMERAL 0)). Qed.
Lemma lem262347 : term405.
Proof. exact (fun h0 : term406 => @lem262346). Qed.
Lemma lem262349 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262350 : term405 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem262349 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem262351 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem262350) (@lem262347)). Qed.
Lemma lem262357 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem262358 (_5550 : nat) (_5551 : nat) : (term394 _5550 _5551) = (term408 _5550 _5551).
Proof. exact (@lem262357 ((Nat.div _5550 _5551) = (NUMERAL 0)) (term12 _5551)). Qed.
Lemma lem262368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem262369 (_5550 : nat) (_5551 : nat) : (term409 _5550 _5551) = (term410 _5550 _5551).
Proof. exact (MK_COMB (@lem262368) (@lem262358 _5550 _5551)). Qed.
Lemma lem262379 (_5550 : nat) (_5551 : nat) : (term408 _5550 _5551) = (term408 _5550 _5551).
Proof. exact (eq_refl (term408 _5550 _5551)). Qed.
Lemma lem262380 (_5550 : nat) (_5551 : nat) : ((term394 _5550 _5551) = (term408 _5550 _5551)) = ((term408 _5550 _5551) = (term408 _5550 _5551)).
Proof. exact (MK_COMB (@lem262369 _5550 _5551) (@lem262379 _5550 _5551)). Qed.
Lemma lem262382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem262383 (x : Prop) : (x = x) = True.
Proof. exact (@lem262382 Prop x). Qed.
Lemma lem262384 (_5550 : nat) (_5551 : nat) : ((term408 _5550 _5551) = (term408 _5550 _5551)) = True.
Proof. exact (@lem262383 (term408 _5550 _5551)). Qed.
Lemma lem262385 (_5550 : nat) (_5551 : nat) : ((term394 _5550 _5551) = (term408 _5550 _5551)) = True.
Proof. exact (TRANS (@lem262380 _5550 _5551) (@lem262384 _5550 _5551)). Qed.
Lemma lem262386 (_5550 : nat) (_5551 : nat) : True = ((term394 _5550 _5551) = (term408 _5550 _5551)).
Proof. exact (SYM (@lem262385 _5550 _5551)). Qed.
Lemma lem262387 (_5550 : nat) (_5551 : nat) : (term394 _5550 _5551) = (term408 _5550 _5551).
Proof. exact (EQ_MP (@lem262386 _5550 _5551) (@lem0)). Qed.
Lemma lem262388 (_5550 : nat) (_5551 : nat) (h1 : term130) : term408 _5550 _5551.
Proof. exact (EQ_MP (@lem262387 _5550 _5551) (@lem261558 _5550 _5551 h1)). Qed.
Lemma lem262390 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem262391 (_5550 : nat) (_5551 : nat) : (term408 _5550 _5551) = (term412 _5550 _5551).
Proof. exact (@lem262390 (term12 _5551) ((Nat.div _5550 _5551) = (NUMERAL 0))). Qed.
Lemma lem262393 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262394 (_5551 : nat) : (term414 _5551) = (_5551 = (NUMERAL 0)).
Proof. exact (@lem262393 (_5551 = (NUMERAL 0))). Qed.
Lemma lem262395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262396 (_5551 : nat) : (term415 _5551) = (term96 _5551).
Proof. exact (MK_COMB (@lem262395) (@lem262394 _5551)). Qed.
Lemma lem262397 (_5550 : nat) (_5551 : nat) : ((Nat.div _5550 _5551) = (NUMERAL 0)) = ((Nat.div _5550 _5551) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.div _5550 _5551) = (NUMERAL 0))). Qed.
Lemma lem262398 (_5550 : nat) (_5551 : nat) : (term412 _5550 _5551) = (term416 _5550 _5551).
Proof. exact (MK_COMB (@lem262396 _5551) (@lem262397 _5550 _5551)). Qed.
Lemma lem262399 (_5550 : nat) (_5551 : nat) : (term408 _5550 _5551) = (term416 _5550 _5551).
Proof. exact (TRANS (@lem262391 _5550 _5551) (@lem262398 _5550 _5551)). Qed.
Lemma lem262402 (_5550 : nat) (_5551 : nat) (h1 : term130) : term416 _5550 _5551.
Proof. exact (EQ_MP (@lem262399 _5550 _5551) (@lem262388 _5550 _5551 h1)). Qed.
Lemma lem262403 (_5550 : nat) (h1 : term130) : term417 _5550.
Proof. exact (@lem262402 _5550 (NUMERAL 0) h1). Qed.
Lemma lem262406 (_5550 : nat) (h1 : term130) : (term21 _5550) = (NUMERAL 0).
Proof. exact (@lem262403 _5550 h1 (@lem262351)). Qed.
Lemma lem262407 (m : nat) (h1 : term130) : (term21 m) = (NUMERAL 0).
Proof. exact (@lem262406 m h1). Qed.
Lemma lem262408 (m : nat) (h1 : term130) : term418 m.
Proof. exact (fun h0 : term419 m => @lem262407 m h1). Qed.
Lemma lem262410 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262411 (m : nat) : (term418 m) = ((term21 m) = (NUMERAL 0)).
Proof. exact (@lem262410 ((term21 m) = (NUMERAL 0))). Qed.
Lemma lem262412 (m : nat) (h1 : term130) : (term21 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem262411 m) (@lem262408 m h1)). Qed.
Lemma lem262414 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem262415 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem262414 (NUMERAL 0)). Qed.
Lemma lem262416 : term405.
Proof. exact (fun h0 : term406 => @lem262415). Qed.
Lemma lem262418 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262419 : term405 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem262418 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem262420 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem262419) (@lem262416)). Qed.
Lemma lem262426 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem262427 (_5550 : nat) (_5551 : nat) : (term395 _5551 _5550) = (term420 _5550 _5551).
Proof. exact (@lem262426 ((Nat.modulo _5550 _5551) = _5550) (term12 _5551)). Qed.
Lemma lem262437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem262438 (_5550 : nat) (_5551 : nat) : (term421 _5551 _5550) = (term422 _5550 _5551).
Proof. exact (MK_COMB (@lem262437) (@lem262427 _5550 _5551)). Qed.
Lemma lem262448 (_5550 : nat) (_5551 : nat) : (term420 _5550 _5551) = (term420 _5550 _5551).
Proof. exact (eq_refl (term420 _5550 _5551)). Qed.
Lemma lem262449 (_5550 : nat) (_5551 : nat) : ((term395 _5551 _5550) = (term420 _5550 _5551)) = ((term420 _5550 _5551) = (term420 _5550 _5551)).
Proof. exact (MK_COMB (@lem262438 _5550 _5551) (@lem262448 _5550 _5551)). Qed.
Lemma lem262451 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem262452 (x : Prop) : (x = x) = True.
Proof. exact (@lem262451 Prop x). Qed.
Lemma lem262453 (_5550 : nat) (_5551 : nat) : ((term420 _5550 _5551) = (term420 _5550 _5551)) = True.
Proof. exact (@lem262452 (term420 _5550 _5551)). Qed.
Lemma lem262454 (_5550 : nat) (_5551 : nat) : ((term395 _5551 _5550) = (term420 _5550 _5551)) = True.
Proof. exact (TRANS (@lem262449 _5550 _5551) (@lem262453 _5550 _5551)). Qed.
Lemma lem262455 (_5550 : nat) (_5551 : nat) : True = ((term395 _5551 _5550) = (term420 _5550 _5551)).
Proof. exact (SYM (@lem262454 _5550 _5551)). Qed.
Lemma lem262456 (_5550 : nat) (_5551 : nat) : (term395 _5551 _5550) = (term420 _5550 _5551).
Proof. exact (EQ_MP (@lem262455 _5550 _5551) (@lem0)). Qed.
Lemma lem262457 (_5550 : nat) (_5551 : nat) (h1 : term130) : term420 _5550 _5551.
Proof. exact (EQ_MP (@lem262456 _5550 _5551) (@lem261572 _5551 _5550 h1)). Qed.
Lemma lem262459 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem262460 (_5551 : nat) (_5550 : nat) : (term420 _5550 _5551) = (term423 _5551 _5550).
Proof. exact (@lem262459 (term12 _5551) ((Nat.modulo _5550 _5551) = _5550)). Qed.
Lemma lem262462 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262463 (_5551 : nat) : (term414 _5551) = (_5551 = (NUMERAL 0)).
Proof. exact (@lem262462 (_5551 = (NUMERAL 0))). Qed.
Lemma lem262464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262465 (_5551 : nat) : (term415 _5551) = (term96 _5551).
Proof. exact (MK_COMB (@lem262464) (@lem262463 _5551)). Qed.
Lemma lem262466 (_5551 : nat) (_5550 : nat) : ((Nat.modulo _5550 _5551) = _5550) = ((Nat.modulo _5550 _5551) = _5550).
Proof. exact (eq_refl ((Nat.modulo _5550 _5551) = _5550)). Qed.
Lemma lem262467 (_5551 : nat) (_5550 : nat) : (term423 _5551 _5550) = (term424 _5551 _5550).
Proof. exact (MK_COMB (@lem262465 _5551) (@lem262466 _5551 _5550)). Qed.
Lemma lem262468 (_5551 : nat) (_5550 : nat) : (term420 _5550 _5551) = (term424 _5551 _5550).
Proof. exact (TRANS (@lem262460 _5551 _5550) (@lem262467 _5551 _5550)). Qed.
Lemma lem262471 (_5551 : nat) (_5550 : nat) (h1 : term130) : term424 _5551 _5550.
Proof. exact (EQ_MP (@lem262468 _5551 _5550) (@lem262457 _5550 _5551 h1)). Qed.
Lemma lem262472 (_5550 : nat) (h1 : term130) : term425 _5550.
Proof. exact (@lem262471 (NUMERAL 0) _5550 h1). Qed.
Lemma lem262475 (_5550 : nat) (h1 : term130) : (term24 _5550) = _5550.
Proof. exact (@lem262472 _5550 h1 (@lem262420)). Qed.
Lemma lem262476 (m : nat) (h1 : term130) : (term24 m) = m.
Proof. exact (@lem262475 m h1). Qed.
Lemma lem262477 (m : nat) (h1 : term130) : term426 m.
Proof. exact (fun h0 : term427 m => @lem262476 m h1). Qed.
Lemma lem262479 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262480 (m : nat) : (term426 m) = ((term24 m) = m).
Proof. exact (@lem262479 ((term24 m) = m)). Qed.
Lemma lem262481 (m : nat) (h1 : term130) : (term24 m) = m.
Proof. exact (EQ_MP (@lem262480 m) (@lem262477 m h1)). Qed.
Lemma lem262499 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem262500 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term469 m P _5559 _5560) = (term470 P _5559 _5560 m).
Proof. exact (@lem262499 (P _5559 _5560) (term384 _5560 m)). Qed.
Lemma lem262508 (_5559 : nat) : (term471 _5559) = (term471 _5559).
Proof. exact (eq_refl (term471 _5559)). Qed.
Lemma lem262509 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term383 m P _5559 _5560) = (term472 P _5559 _5560 m).
Proof. exact (MK_COMB (@lem262508 _5559) (@lem262500 P _5559 _5560 m)). Qed.
Lemma lem262513 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem262514 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term472 P _5559 _5560 m) = (term473 P _5559 _5560 m).
Proof. exact (@lem262513 (P _5559 _5560) (term12 _5559) (term384 _5560 m)). Qed.
Lemma lem262534 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term383 m P _5559 _5560) = (term473 P _5559 _5560 m).
Proof. exact (TRANS (@lem262509 P _5559 _5560 m) (@lem262514 P _5559 _5560 m)). Qed.
Lemma lem262535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem262536 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term474 m P _5559 _5560) = (term475 P _5559 _5560 m).
Proof. exact (MK_COMB (@lem262535) (@lem262534 P _5559 _5560 m)). Qed.
Lemma lem262556 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term473 P _5559 _5560 m) = (term473 P _5559 _5560 m).
Proof. exact (eq_refl (term473 P _5559 _5560 m)). Qed.
Lemma lem262557 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : ((term383 m P _5559 _5560) = (term473 P _5559 _5560 m)) = ((term473 P _5559 _5560 m) = (term473 P _5559 _5560 m)).
Proof. exact (MK_COMB (@lem262536 P _5559 _5560 m) (@lem262556 P _5559 _5560 m)). Qed.
Lemma lem262559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem262560 (x : Prop) : (x = x) = True.
Proof. exact (@lem262559 Prop x). Qed.
Lemma lem262561 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : ((term473 P _5559 _5560 m) = (term473 P _5559 _5560 m)) = True.
Proof. exact (@lem262560 (term473 P _5559 _5560 m)). Qed.
Lemma lem262562 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : ((term383 m P _5559 _5560) = (term473 P _5559 _5560 m)) = True.
Proof. exact (TRANS (@lem262557 P _5559 _5560 m) (@lem262561 P _5559 _5560 m)). Qed.
Lemma lem262563 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : True = ((term383 m P _5559 _5560) = (term473 P _5559 _5560 m)).
Proof. exact (SYM (@lem262562 P _5559 _5560 m)). Qed.
Lemma lem262564 (P : type1605) (_5559 : nat) (_5560 : nat) (m : nat) : (term383 m P _5559 _5560) = (term473 P _5559 _5560 m).
Proof. exact (EQ_MP (@lem262563 P _5559 _5560 m) (@lem0)). Qed.
Lemma lem262565 (_5559 : nat) (_5560 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term473 P _5559 _5560 m.
Proof. exact (EQ_MP (@lem262564 P _5559 _5560 m) (@lem261474 _5559 _5560 m P h1)). Qed.
Lemma lem262567 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem262568 (m : nat) (P : type1605) (_5559 : nat) (_5560 : nat) : (term473 P _5559 _5560 m) = (term476 m P _5559 _5560).
Proof. exact (@lem262567 (term147 _5559 _5560 m) (P _5559 _5560)). Qed.
Lemma lem262570 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem262571 (_5559 : nat) (_5560 : nat) (m : nat) : (term477 _5559 _5560 m) = (term478 _5559 _5560 m).
Proof. exact (@lem262570 (term12 _5559) (term384 _5560 m)). Qed.
Lemma lem262573 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262574 (_5559 : nat) : (term414 _5559) = (_5559 = (NUMERAL 0)).
Proof. exact (@lem262573 (_5559 = (NUMERAL 0))). Qed.
Lemma lem262575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262576 (_5559 : nat) : (term479 _5559) = (term30 _5559).
Proof. exact (MK_COMB (@lem262575) (@lem262574 _5559)). Qed.
Lemma lem262578 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem262579 (_5560 : nat) (m : nat) : (term449 _5560 m) = (_5560 = m).
Proof. exact (@lem262578 (_5560 = m)). Qed.
Lemma lem262580 (_5559 : nat) (_5560 : nat) (m : nat) : (term478 _5559 _5560 m) = (term31 _5559 _5560 m).
Proof. exact (MK_COMB (@lem262576 _5559) (@lem262579 _5560 m)). Qed.
Lemma lem262581 (_5559 : nat) (_5560 : nat) (m : nat) : (term477 _5559 _5560 m) = (term31 _5559 _5560 m).
Proof. exact (TRANS (@lem262571 _5559 _5560 m) (@lem262580 _5559 _5560 m)). Qed.
Lemma lem262582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262583 (_5559 : nat) (_5560 : nat) (m : nat) : (term480 _5559 _5560 m) = (term481 _5559 _5560 m).
Proof. exact (MK_COMB (@lem262582) (@lem262581 _5559 _5560 m)). Qed.
Lemma lem262584 (P : type1605) (_5559 : nat) (_5560 : nat) : (P _5559 _5560) = (P _5559 _5560).
Proof. exact (eq_refl (P _5559 _5560)). Qed.
Lemma lem262585 (m : nat) (P : type1605) (_5559 : nat) (_5560 : nat) : (term476 m P _5559 _5560) = (term482 m P _5559 _5560).
Proof. exact (MK_COMB (@lem262583 _5559 _5560 m) (@lem262584 P _5559 _5560)). Qed.
Lemma lem262586 (m : nat) (P : type1605) (_5559 : nat) (_5560 : nat) : (term473 P _5559 _5560 m) = (term482 m P _5559 _5560).
Proof. exact (TRANS (@lem262568 m P _5559 _5560) (@lem262585 m P _5559 _5560)). Qed.
Lemma lem262588 (m : nat) (h1 : term130) : term483 m.
Proof. exact (conj (@lem262412 m h1) (@lem262481 m h1)). Qed.
Lemma lem262590 (_5559 : nat) (_5560 : nat) (m : nat) (P : type1605) (h1 : term183 m P) : term482 m P _5559 _5560.
Proof. exact (EQ_MP (@lem262586 m P _5559 _5560) (@lem262565 _5559 _5560 m P h1)). Qed.
Lemma lem262591 (m : nat) (P : type1605) (h1 : term183 m P) : term484 P m.
Proof. exact (@lem262590 (term21 m) (term24 m) m P h1). Qed.
Lemma lem262594 (m : nat) (P : type1605) (h1 : term130) (h2 : term183 m P) : term26 P m.
Proof. exact (@lem262591 m P h2 (@lem262588 m h1)). Qed.
Lemma lem262595 (m : nat) (P : type1605) (h1 : term130) (h2 : term183 m P) : term428 P m.
Proof. exact (fun h0 : term396 P m => @lem262594 m P h1 h2). Qed.
Lemma lem262597 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262598 (P : type1605) (m : nat) : (term428 P m) = (term26 P m).
Proof. exact (@lem262597 (term26 P m)). Qed.
Lemma lem262599 (m : nat) (P : type1605) (h1 : term130) (h2 : term183 m P) : term26 P m.
Proof. exact (EQ_MP (@lem262598 P m) (@lem262595 m P h1 h2)). Qed.
Lemma lem262602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem262604 (P : type1605) (m : nat) : (term396 P m) = (term485 P m).
Proof. exact (@lem262602 (term26 P m)). Qed.
Lemma lem262607 (m : nat) (P : type1605) (h1 : term183 m P) : term485 P m.
Proof. exact (EQ_MP (@lem262604 P m) (@lem261460 m P h1)). Qed.
Lemma lem262610 (m : nat) (P : type1605) (h1 : term130) (h2 : term183 m P) : False.
Proof. exact (@lem262607 m P h2 (@lem262599 m P h1 h2)). Qed.
Lemma lem262611 (m : nat) (P : type1605) (h1 : term130) (h2 : term183 m P) : term466.
Proof. exact (fun h0 : ~ False => @lem262610 m P h1 h2). Qed.
Lemma lem262613 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem262614 : term466 = False.
Proof. exact (@lem262613 False). Qed.
Lemma lem262616 (m : nat) (P : type1605) (h1 : term130) (h2 : term183 m P) : False.
Proof. exact (EQ_MP (@lem262614) (@lem262611 m P h1 h2)). Qed.
Lemma lem262618 (m : nat) (q : nat) (r : nat) (h1 : term85) (h2 : term45 m q r) : False.
Proof. exact (EQ_MP (@lem262226) (@lem262223 m q r h1 h2)). Qed.
Lemma lem262621 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term31 q r m) (h3 : term215 m P q r) : False.
Proof. exact (EQ_MP (@lem262086) (@lem262083 m P q r h1 h2 h3)). Qed.
Lemma lem262622 (m : nat) (P : type1605) (q : nat) (r : nat) (h1 : term130) (h2 : term85) (h3 : term215 m P q r) : False.
Proof. exact (or_elim (@lem259839 m P q r h3) (fun h0 : term31 q r m => @lem262621 m P q r h1 h0 h3) (fun h0 : term45 m q r => @lem262618 m q r h2 h0)). Qed.
Lemma lem262623 (q : nat) (r : nat) (m : nat) (P : type1605) (h1 : term130) (h2 : term85) (h3 : term253 q r m P) : False.
Proof. exact (or_elim (@lem259827 q r m P h3) (fun h0 : term215 m P q r => @lem262622 m P q r h1 h2 h0) (fun h0 : term183 m P => @lem262616 m P h1 h0)). Qed.
Lemma lem262624 (q : nat) (r : nat) (m : nat) (P : type1605) (h1 : term130) (h2 : term85) (h3 : term253 q r m P) : (term253 q r m P) = False.
Proof. exact (prop_ext (fun h4 : term253 q r m P => @lem262623 q r m P h1 h2 h3) (fun h4 : False => @lem259827 q r m P h3)). Qed.
Lemma lem262625 (q : nat) (r : nat) (m : nat) (P : type1605) (h1 : term130) (h2 : term85) (h3 : term253 q r m P) : False.
Proof. exact (EQ_MP (@lem262624 q r m P h1 h2 h3) (@lem259827 q r m P h3)). Qed.
Lemma lem262626 (q : nat) (m : nat) (P : type1605) (h1 : term130) (h2 : term256 q m P) (h3 : term85) : False.
Proof. exact (ex_elim (@lem259477 q m P h2) (fun r : nat => fun h0 : term255 q m P r => @lem262625 q r m P h1 h3 h0)). Qed.
Lemma lem262627 (m : nat) (P : type1605) (h1 : term130) (h2 : term71 m P) (h3 : term85) : False.
Proof. exact (ex_elim (@lem258873 m P h2) (fun q : nat => fun h0 : term257 m P q => @lem262626 q m P h1 h0 h3)). Qed.
Lemma lem262628 (m : nat) (P : type1605) (h1 : term71 m P) (h2 : term85) : term486.
Proof. exact (fun h0 : term130 => @lem262627 m P h0 h1 h2). Qed.
Lemma lem262629 : term486 = term131.
Proof. exact (@lem69 term130). Qed.
Lemma lem262630 (m : nat) (P : type1605) (h1 : term71 m P) (h2 : term85) : term131.
Proof. exact (EQ_MP (@lem262629) (@lem262628 m P h1 h2)). Qed.
Lemma lem262631 (m : nat) (P : type1605) (h1 : term71 m P) : term137.
Proof. exact (fun h0 : term85 => @lem262630 m P h1 h0). Qed.
Lemma lem262632 (m : nat) (P : type1605) : term138 m P.
Proof. exact (fun h0 : term71 m P => @lem262631 m P h0). Qed.
Lemma lem262633 (n : nat) (m : nat) (P : type1605) : term139 n m P.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem262632 m P). Qed.
Lemma lem262638 (m : nat) (P : type1605) : term141 m P.
Proof. exact (fun n : nat => @lem262633 n m P). Qed.
Lemma lem262643 (P : type1605) : term143 P.
Proof. exact (fun m : nat => @lem262638 m P). Qed.
Lemma lem262648 : term145.
Proof. exact (fun P : type1605 => @lem262643 P). Qed.
Lemma lem262649 : term108.
Proof. exact (EQ_MP (@lem258571) (@lem262648)). Qed.
Lemma lem262650 (P : type1605) : term487 P.
Proof. exact (@lem262649 P). Qed.
Lemma lem262651 (P : type1605) : (term487 P) = (term104 P).
Proof. exact (eq_refl (term487 P)). Qed.
Lemma lem262652 (P : type1605) : term104 P.
Proof. exact (EQ_MP (@lem262651 P) (@lem262650 P)). Qed.
Lemma lem262653 (P : type1605) (m : nat) : term488 P m.
Proof. exact (@lem262652 P m). Qed.
Lemma lem262654 (m : nat) (P : type1605) : (term488 P m) = (term100 m P).
Proof. exact (eq_refl (term488 P m)). Qed.
Lemma lem262655 (m : nat) (P : type1605) : term100 m P.
Proof. exact (EQ_MP (@lem262654 m P) (@lem262653 P m)). Qed.
Lemma lem262656 (m : nat) (P : type1605) (n : nat) : term489 m P n.
Proof. exact (@lem262655 m P n). Qed.
Lemma lem262657 (n : nat) (m : nat) (P : type1605) : (term489 m P n) = (term72 n m P).
Proof. exact (eq_refl (term489 m P n)). Qed.
Lemma lem262658 (n : nat) (m : nat) (P : type1605) : term72 n m P.
Proof. exact (EQ_MP (@lem262657 n m P) (@lem262656 m P n)). Qed.
Lemma lem262660 (n : nat) (m : nat) (P : type1605) : term72 n m P.
Proof. exact (@lem258181 n m P (@lem262658 n m P)). Qed.
Lemma lem262661 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : term94 m P.
Proof. exact (@lem262660 n m P (@lem257958 n h1)). Qed.
Lemma lem262662 (m : nat) (P : type1605) (n : nat) (h1 : term71 m P) (h2 : n = (NUMERAL 0)) : term91.
Proof. exact (@lem262661 m P n h2 (@lem258166 m P h1)). Qed.
Lemma lem262663 (m : nat) (P : type1605) (n : nat) (h1 : term71 m P) (h2 : n = (NUMERAL 0)) : term88.
Proof. exact (@lem262662 m P n h1 h2 (@lem89997)). Qed.
Lemma lem262664 (m : nat) (P : type1605) (n : nat) (h1 : term71 m P) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (@lem262663 m P n h1 h2 (@lem155916)). Qed.
Lemma lem262665 (m : nat) (P : type1605) (n : nat) (h1 : term71 m P) (h2 : n = (NUMERAL 0)) : (term71 m P) = False.
Proof. exact (prop_ext (fun h3 : term71 m P => @lem262664 m P n h1 h2) (fun h3 : False => @lem258166 m P h1)). Qed.
Lemma lem262666 (m : nat) (P : type1605) (n : nat) (h1 : term71 m P) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem262665 m P n h1 h2) (@lem258166 m P h1)). Qed.
Lemma lem262667 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : term70 m P.
Proof. exact (fun h0 : term71 m P => @lem262666 m P n h0 h1). Qed.
Lemma lem262668 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : (term26 P m) = (term59 m P).
Proof. exact (EQ_MP (@lem258165 m P) (@lem262667 m P n h1)). Qed.
Lemma lem262670 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem257943 n) (@lem257942 n)). Qed.
Lemma lem262671 (n : nat) (h1 : term12 n) : term14 n.
Proof. exact (@lem262670 n (@lem257959 n h1)). Qed.
Lemma lem262673 (p : Prop) : p = (term69 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem262674 (m : nat) (n : nat) (P : type1605) : (term490 m n P) = (term491 m n P).
Proof. exact (@lem262673 (term490 m n P)). Qed.
Lemma lem262675 (m : nat) (n : nat) (P : type1605) : (term491 m n P) = (term490 m n P).
Proof. exact (SYM (@lem262674 m n P)). Qed.
Lemma lem262676 (m : nat) (n : nat) (P : type1605) (h1 : term492 m n P) : term492 m n P.
Proof. exact (h1). Qed.
Lemma lem262679 (m : nat) (n : nat) (P : type1605) (h1 : term493 m n P) : term493 m n P.
Proof. exact (h1). Qed.
Lemma lem262680 (m : nat) (n : nat) (P : type1605) : term494 m n P.
Proof. exact (fun h0 : term493 m n P => @lem262679 m n P h0). Qed.
Lemma lem262681 (m : nat) (n : nat) (P : type1605) (h1 : term494 m n P) : term494 m n P.
Proof. exact (h1). Qed.
Lemma lem262682 (m : nat) (n : nat) (P : type1605) (h1 : term493 m n P) : term493 m n P.
Proof. exact (h1). Qed.
Lemma lem262683 (m : nat) (n : nat) (P : type1605) (h1 : term493 m n P) (h2 : term494 m n P) : term493 m n P.
Proof. exact (@lem262681 m n P h2 (@lem262682 m n P h1)). Qed.
Lemma lem262684 (m : nat) (n : nat) (P : type1605) (h1 : term493 m n P) : term495 m n P.
Proof. exact (fun h0 : term494 m n P => @lem262683 m n P h1 h0). Qed.
Lemma lem262685 (m : nat) (n : nat) (P : type1605) (h1 : term494 m n P) : term494 m n P.
Proof. exact (h1). Qed.
Lemma lem262686 (m : nat) (n : nat) (P : type1605) (h1 : term493 m n P) (h2 : term494 m n P) : term493 m n P.
Proof. exact (@lem262684 m n P h1 (@lem262685 m n P h2)). Qed.
Lemma lem262687 (m : nat) (n : nat) (P : type1605) (h1 : term494 m n P) : term494 m n P.
Proof. exact (fun h0 : term493 m n P => @lem262686 m n P h0 h1). Qed.
Lemma lem262688 (m : nat) (n : nat) (P : type1605) : term496 m n P.
Proof. exact (fun h0 : term494 m n P => @lem262687 m n P h0). Qed.
Lemma lem262691 (m : nat) (n : nat) (P : type1605) : term494 m n P.
Proof. exact (@lem262688 m n P (@lem262680 m n P)). Qed.
Lemma lem262709 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem262710 (P : nat -> Prop) (Q : nat -> Prop) : (term276 P Q) = (term277 P Q).
Proof. exact (@lem262709 nat P Q). Qed.
Lemma lem262711 (n : nat) : (term497 n) = (term498 n).
Proof. exact (@lem262710 (term499 n) (term500 n)). Qed.
Lemma lem262712 (m : nat) (n : nat) : (term501 n m) = (m = (term502 m n)).
Proof. exact (eq_refl (term501 n m)). Qed.
Lemma lem262713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262714 (m : nat) (n : nat) : (term503 n m) = (term504 m n).
Proof. exact (MK_COMB (@lem262713) (@lem262712 m n)). Qed.
Lemma lem262715 (m : nat) (n : nat) : (term505 n m) = (term506 m n).
Proof. exact (eq_refl (term505 n m)). Qed.
Lemma lem262716 (m : nat) (n : nat) : (term507 n m) = (term13 m n).
Proof. exact (MK_COMB (@lem262714 m n) (@lem262715 m n)). Qed.
Lemma lem262717 (n : nat) : (term508 n) = (term509 n).
Proof. exact (fun_ext (fun m : nat => @lem262716 m n)). Qed.
Lemma lem262718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262719 (n : nat) : (term497 n) = (term14 n).
Proof. exact (MK_COMB (@lem262718) (@lem262717 n)). Qed.
Lemma lem262720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem262721 (n : nat) : (term510 n) = (term511 n).
Proof. exact (MK_COMB (@lem262720) (@lem262719 n)). Qed.
Lemma lem262722 (m : nat) (n : nat) : (term501 n m) = (m = (term502 m n)).
Proof. exact (eq_refl (term501 n m)). Qed.
Lemma lem262723 (n : nat) : (term512 n) = (term499 n).
Proof. exact (fun_ext (fun m : nat => @lem262722 m n)). Qed.
Lemma lem262724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262725 (n : nat) : (term513 n) = (term514 n).
Proof. exact (MK_COMB (@lem262724) (@lem262723 n)). Qed.
Lemma lem262726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262727 (n : nat) : (term515 n) = (term516 n).
Proof. exact (MK_COMB (@lem262726) (@lem262725 n)). Qed.
Lemma lem262728 (m : nat) (n : nat) : (term505 n m) = (term506 m n).
Proof. exact (eq_refl (term505 n m)). Qed.
Lemma lem262729 (n : nat) : (term517 n) = (term500 n).
Proof. exact (fun_ext (fun m : nat => @lem262728 m n)). Qed.
Lemma lem262730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262731 (n : nat) : (term518 n) = (term519 n).
Proof. exact (MK_COMB (@lem262730) (@lem262729 n)). Qed.
Lemma lem262732 (n : nat) : (term498 n) = (term520 n).
Proof. exact (MK_COMB (@lem262727 n) (@lem262731 n)). Qed.
Lemma lem262733 (n : nat) : ((term497 n) = (term498 n)) = ((term14 n) = (term520 n)).
Proof. exact (MK_COMB (@lem262721 n) (@lem262732 n)). Qed.
Lemma lem262734 (n : nat) : (term14 n) = (term520 n).
Proof. exact (EQ_MP (@lem262733 n) (@lem262711 n)). Qed.
Lemma lem262745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262746 (n : nat) : (term521 n) = (term522 n).
Proof. exact (MK_COMB (@lem262745) (@lem262734 n)). Qed.
Lemma lem262759 (m : nat) (n : nat) (P : type1605) : ((term25 P m n) = (term68 m n P)) = ((term25 P m n) = (term68 m n P)).
Proof. exact (eq_refl ((term25 P m n) = (term68 m n P))). Qed.
Lemma lem262760 (m : nat) (n : nat) (P : type1605) : (term490 m n P) = (term523 m n P).
Proof. exact (MK_COMB (@lem262746 n) (@lem262759 m n P)). Qed.
Lemma lem262763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem262764 (m : nat) (n : nat) (P : type1605) : (term492 m n P) = (term524 m n P).
Proof. exact (MK_COMB (@lem262763) (@lem262760 m n P)). Qed.
Lemma lem262765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262766 (m : nat) (n : nat) (P : type1605) : (term525 m n P) = (term526 m n P).
Proof. exact (MK_COMB (@lem262765) (@lem262764 m n P)). Qed.
Lemma lem262768 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem262769 : term527 = term528.
Proof. exact (@lem262768 term529). Qed.
Lemma lem262792 (m : nat) (n : nat) (P : type1605) : (term493 m n P) = (term530 m n P).
Proof. exact (MK_COMB (@lem262766 m n P) (@lem262769)). Qed.
Lemma lem262795 (n : nat) (P : type1605) : (term531 n P) = (term532 n P).
Proof. exact (fun_ext (fun m : nat => @lem262792 m n P)). Qed.
Lemma lem262796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262797 (n : nat) (P : type1605) : (term533 n P) = (term534 n P).
Proof. exact (MK_COMB (@lem262796) (@lem262795 n P)). Qed.
Lemma lem262802 (P : type1605) : (term535 P) = (term536 P).
Proof. exact (fun_ext (fun n : nat => @lem262797 n P)). Qed.
Lemma lem262803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262804 (P : type1605) : (term537 P) = (term538 P).
Proof. exact (MK_COMB (@lem262803) (@lem262802 P)). Qed.
Lemma lem262809 : term539 = term540.
Proof. exact (fun_ext (fun P : type1605 => @lem262804 P)). Qed.
Lemma lem262810 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem262819 : term541 = term542.
Proof. exact (MK_COMB (@lem262810) (@lem262809)). Qed.
Lemma lem262832 (q : nat) (m : nat) (n : nat) (r : nat) : (term543 q m n r) = (term543 q m n r).
Proof. exact (eq_refl (term543 q m n r)). Qed.
Lemma lem262833 (q : nat) (m : nat) (n : nat) : (term544 q m n) = (term544 q m n).
Proof. exact (fun_ext (fun r : nat => @lem262832 q m n r)). Qed.
Lemma lem262834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262835 (q : nat) (m : nat) (n : nat) : (term545 q m n) = (term545 q m n).
Proof. exact (MK_COMB (@lem262834) (@lem262833 q m n)). Qed.
Lemma lem262836 (m : nat) (n : nat) : (term546 m n) = (term546 m n).
Proof. exact (fun_ext (fun q : nat => @lem262835 q m n)). Qed.
Lemma lem262837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262838 (m : nat) (n : nat) : (term547 m n) = (term547 m n).
Proof. exact (MK_COMB (@lem262837) (@lem262836 m n)). Qed.
Lemma lem262839 (m : nat) : (term548 m) = (term548 m).
Proof. exact (fun_ext (fun n : nat => @lem262838 m n)). Qed.
Lemma lem262840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262841 (m : nat) : (term549 m) = (term549 m).
Proof. exact (MK_COMB (@lem262840) (@lem262839 m)). Qed.
Lemma lem262842 : term550 = term550.
Proof. exact (fun_ext (fun m : nat => @lem262841 m)). Qed.
Lemma lem262843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262844 : term529 = term529.
Proof. exact (MK_COMB (@lem262843) (@lem262842)). Qed.
Lemma lem262845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem262846 : term528 = term528.
Proof. exact (MK_COMB (@lem262845) (@lem262844)). Qed.
Lemma lem262855 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term64 m n P q r) = (term64 m n P q r).
Proof. exact (eq_refl (term64 m n P q r)). Qed.
Lemma lem262856 (m : nat) (n : nat) (P : type1605) (q : nat) : (term65 m n P q) = (term65 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem262855 m n P q r)). Qed.
Lemma lem262857 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262858 (m : nat) (n : nat) (P : type1605) (q : nat) : (term66 m n P q) = (term66 m n P q).
Proof. exact (MK_COMB (@lem262857) (@lem262856 m n P q)). Qed.
Lemma lem262859 (m : nat) (n : nat) (P : type1605) : (term67 m n P) = (term67 m n P).
Proof. exact (fun_ext (fun q : nat => @lem262858 m n P q)). Qed.
Lemma lem262860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262861 (m : nat) (n : nat) (P : type1605) : (term68 m n P) = (term68 m n P).
Proof. exact (MK_COMB (@lem262860) (@lem262859 m n P)). Qed.
Lemma lem262864 (P : type1605) (m : nat) (n : nat) : (term27 P m n) = (term27 P m n).
Proof. exact (eq_refl (term27 P m n)). Qed.
Lemma lem262865 (m : nat) (n : nat) (P : type1605) : ((term25 P m n) = (term68 m n P)) = ((term25 P m n) = (term68 m n P)).
Proof. exact (MK_COMB (@lem262864 P m n) (@lem262861 m n P)). Qed.
Lemma lem262866 (m : nat) (n : nat) : (term506 m n) = (term506 m n).
Proof. exact (eq_refl (term506 m n)). Qed.
Lemma lem262867 (n : nat) : (term500 n) = (term500 n).
Proof. exact (fun_ext (fun m : nat => @lem262866 m n)). Qed.
Lemma lem262868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262869 (n : nat) : (term519 n) = (term519 n).
Proof. exact (MK_COMB (@lem262868) (@lem262867 n)). Qed.
Lemma lem262870 (m : nat) (n : nat) : (m = (term502 m n)) = (m = (term502 m n)).
Proof. exact (eq_refl (m = (term502 m n))). Qed.
Lemma lem262871 (n : nat) : (term499 n) = (term499 n).
Proof. exact (fun_ext (fun m : nat => @lem262870 m n)). Qed.
Lemma lem262872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262873 (n : nat) : (term514 n) = (term514 n).
Proof. exact (MK_COMB (@lem262872) (@lem262871 n)). Qed.
Lemma lem262874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262875 (n : nat) : (term516 n) = (term516 n).
Proof. exact (MK_COMB (@lem262874) (@lem262873 n)). Qed.
Lemma lem262876 (n : nat) : (term520 n) = (term520 n).
Proof. exact (MK_COMB (@lem262875 n) (@lem262869 n)). Qed.
Lemma lem262877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262878 (n : nat) : (term522 n) = (term522 n).
Proof. exact (MK_COMB (@lem262877) (@lem262876 n)). Qed.
Lemma lem262879 (m : nat) (n : nat) (P : type1605) : (term523 m n P) = (term523 m n P).
Proof. exact (MK_COMB (@lem262878 n) (@lem262865 m n P)). Qed.
Lemma lem262880 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem262881 (m : nat) (n : nat) (P : type1605) : (term524 m n P) = (term524 m n P).
Proof. exact (MK_COMB (@lem262880) (@lem262879 m n P)). Qed.
Lemma lem262882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem262883 (m : nat) (n : nat) (P : type1605) : (term526 m n P) = (term526 m n P).
Proof. exact (MK_COMB (@lem262882) (@lem262881 m n P)). Qed.
Lemma lem262884 (m : nat) (n : nat) (P : type1605) : (term530 m n P) = (term530 m n P).
Proof. exact (MK_COMB (@lem262883 m n P) (@lem262846)). Qed.
Lemma lem262885 (n : nat) (P : type1605) : (term532 n P) = (term532 n P).
Proof. exact (fun_ext (fun m : nat => @lem262884 m n P)). Qed.
Lemma lem262886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262887 (n : nat) (P : type1605) : (term534 n P) = (term534 n P).
Proof. exact (MK_COMB (@lem262886) (@lem262885 n P)). Qed.
Lemma lem262888 (P : type1605) : (term536 P) = (term536 P).
Proof. exact (fun_ext (fun n : nat => @lem262887 n P)). Qed.
Lemma lem262889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262890 (P : type1605) : (term538 P) = (term538 P).
Proof. exact (MK_COMB (@lem262889) (@lem262888 P)). Qed.
Lemma lem262891 : term540 = term540.
Proof. exact (fun_ext (fun P : type1605 => @lem262890 P)). Qed.
Lemma lem262892 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem262893 : term542 = term542.
Proof. exact (MK_COMB (@lem262892) (@lem262891)). Qed.
Lemma lem262978 : term541 = term542.
Proof. exact (TRANS (@lem262819) (@lem262893)). Qed.
Lemma lem262979 : term542 = term541.
Proof. exact (SYM (@lem262978)). Qed.
Lemma lem262980 (m : nat) (n : nat) (P : type1605) (h1 : term524 m n P) : term524 m n P.
Proof. exact (h1). Qed.
Lemma lem262981 (h1 : term529) : term529.
Proof. exact (h1). Qed.
Lemma lem262982 (m : nat) (n : nat) : (m = (term502 m n)) = (m = (term502 m n)).
Proof. exact (eq_refl (m = (term502 m n))). Qed.
Lemma lem262983 (n : nat) : (term499 n) = (term499 n).
Proof. exact (fun_ext (fun m : nat => @lem262982 m n)). Qed.
Lemma lem262984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262985 (n : nat) : (term514 n) = (term514 n).
Proof. exact (MK_COMB (@lem262984) (@lem262983 n)). Qed.
Lemma lem262986 (m : nat) (n : nat) : (term506 m n) = (term506 m n).
Proof. exact (eq_refl (term506 m n)). Qed.
Lemma lem262987 (n : nat) : (term500 n) = (term500 n).
Proof. exact (fun_ext (fun m : nat => @lem262986 m n)). Qed.
Lemma lem262988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem262989 (n : nat) : (term519 n) = (term519 n).
Proof. exact (MK_COMB (@lem262988) (@lem262987 n)). Qed.
Lemma lem262990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem262991 (n : nat) : (term516 n) = (term516 n).
Proof. exact (MK_COMB (@lem262990) (@lem262985 n)). Qed.
Lemma lem262992 (n : nat) : (term520 n) = (term520 n).
Proof. exact (MK_COMB (@lem262991 n) (@lem262989 n)). Qed.
Lemma lem263003 (m : nat) (q : nat) (r : nat) (n : nat) : (term551 m q r n) = (term552 m q r n).
Proof. exact (@lem17045 (m = (term39 q n r)) (Peano.lt r n)). Qed.
Lemma lem263008 (P : type1605) (q : nat) (r : nat) : (P q r) = (P q r).
Proof. exact (eq_refl (P q r)). Qed.
Lemma lem263013 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term553 m n P q r) = (term554 m n P q r).
Proof. exact (@lem17362 (term44 m q r n) (P q r)). Qed.
Lemma lem263014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263015 (m : nat) (q : nat) (r : nat) (n : nat) : (term555 m q r n) = (term556 m q r n).
Proof. exact (MK_COMB (@lem263014) (@lem263003 m q r n)). Qed.
Lemma lem263016 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term557 m n P q r) = (term558 m n P q r).
Proof. exact (MK_COMB (@lem263015 m q r n) (@lem263008 P q r)). Qed.
Lemma lem263017 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term64 m n P q r) = (term557 m n P q r).
Proof. exact (@lem17265 (term44 m q r n) (P q r)). Qed.
Lemma lem263018 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term64 m n P q r) = (term558 m n P q r).
Proof. exact (TRANS (@lem263017 m n P q r) (@lem263016 m n P q r)). Qed.
Lemma lem263019 (P : nat -> Prop) : (term161 P) = (term162 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem263020 (m : nat) (n : nat) (P : type1605) (q : nat) : (term559 m n P q) = (term560 m n P q).
Proof. exact (@lem263019 (term65 m n P q)). Qed.
Lemma lem263021 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term561 m n P q r) = (term64 m n P q r).
Proof. exact (eq_refl (term561 m n P q r)). Qed.
Lemma lem263022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem263023 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term562 m n P q r) = (term553 m n P q r).
Proof. exact (MK_COMB (@lem263022) (@lem263021 m n P q r)). Qed.
Lemma lem263024 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term562 m n P q r) = (term554 m n P q r).
Proof. exact (TRANS (@lem263023 m n P q r) (@lem263013 m n P q r)). Qed.
Lemma lem263025 (m : nat) (n : nat) (P : type1605) (q : nat) : (term563 m n P q) = (term564 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263024 m n P q r)). Qed.
Lemma lem263026 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263027 (m : nat) (n : nat) (P : type1605) (q : nat) : (term560 m n P q) = (term565 m n P q).
Proof. exact (MK_COMB (@lem263026) (@lem263025 m n P q)). Qed.
Lemma lem263028 (m : nat) (n : nat) (P : type1605) (q : nat) : (term559 m n P q) = (term565 m n P q).
Proof. exact (TRANS (@lem263020 m n P q) (@lem263027 m n P q)). Qed.
Lemma lem263029 (m : nat) (n : nat) (P : type1605) (q : nat) : (term65 m n P q) = (term566 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263018 m n P q r)). Qed.
Lemma lem263030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263031 (m : nat) (n : nat) (P : type1605) (q : nat) : (term66 m n P q) = (term567 m n P q).
Proof. exact (MK_COMB (@lem263030) (@lem263029 m n P q)). Qed.
Lemma lem263032 (P : nat -> Prop) : (term161 P) = (term162 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem263033 (m : nat) (n : nat) (P : type1605) : (term568 m n P) = (term569 m n P).
Proof. exact (@lem263032 (term67 m n P)). Qed.
Lemma lem263034 (m : nat) (n : nat) (P : type1605) (q : nat) : (term570 m n P q) = (term66 m n P q).
Proof. exact (eq_refl (term570 m n P q)). Qed.
Lemma lem263035 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem263036 (m : nat) (n : nat) (P : type1605) (q : nat) : (term571 m n P q) = (term559 m n P q).
Proof. exact (MK_COMB (@lem263035) (@lem263034 m n P q)). Qed.
Lemma lem263037 (m : nat) (n : nat) (P : type1605) (q : nat) : (term571 m n P q) = (term565 m n P q).
Proof. exact (TRANS (@lem263036 m n P q) (@lem263028 m n P q)). Qed.
Lemma lem263038 (m : nat) (n : nat) (P : type1605) : (term572 m n P) = (term573 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263037 m n P q)). Qed.
Lemma lem263039 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263040 (m : nat) (n : nat) (P : type1605) : (term569 m n P) = (term574 m n P).
Proof. exact (MK_COMB (@lem263039) (@lem263038 m n P)). Qed.
Lemma lem263041 (m : nat) (n : nat) (P : type1605) : (term568 m n P) = (term574 m n P).
Proof. exact (TRANS (@lem263033 m n P) (@lem263040 m n P)). Qed.
Lemma lem263042 (m : nat) (n : nat) (P : type1605) : (term67 m n P) = (term575 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263031 m n P q)). Qed.
Lemma lem263043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263044 (m : nat) (n : nat) (P : type1605) : (term68 m n P) = (term576 m n P).
Proof. exact (MK_COMB (@lem263043) (@lem263042 m n P)). Qed.
Lemma lem263046 (P : type1605) (m : nat) (n : nat) : (term577 P m n) = (term577 P m n).
Proof. exact (eq_refl (term577 P m n)). Qed.
Lemma lem263047 (m : nat) (n : nat) (P : type1605) : (term578 m n P) = (term579 m n P).
Proof. exact (MK_COMB (@lem263046 P m n) (@lem263044 m n P)). Qed.
Lemma lem263049 (P : type1605) (m : nat) (n : nat) : (term580 P m n) = (term580 P m n).
Proof. exact (eq_refl (term580 P m n)). Qed.
Lemma lem263050 (m : nat) (n : nat) (P : type1605) : (term581 m n P) = (term582 m n P).
Proof. exact (MK_COMB (@lem263049 P m n) (@lem263041 m n P)). Qed.
Lemma lem263051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263052 (m : nat) (n : nat) (P : type1605) : (term583 m n P) = (term584 m n P).
Proof. exact (MK_COMB (@lem263051) (@lem263050 m n P)). Qed.
Lemma lem263053 (m : nat) (n : nat) (P : type1605) : (term585 m n P) = (term586 m n P).
Proof. exact (MK_COMB (@lem263052 m n P) (@lem263047 m n P)). Qed.
Lemma lem263054 (m : nat) (n : nat) (P : type1605) : (term587 m n P) = (term585 m n P).
Proof. exact (@lem17646 (term25 P m n) (term68 m n P)). Qed.
Lemma lem263055 (m : nat) (n : nat) (P : type1605) : (term587 m n P) = (term586 m n P).
Proof. exact (TRANS (@lem263054 m n P) (@lem263053 m n P)). Qed.
Lemma lem263056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem263057 (n : nat) : (term588 n) = (term588 n).
Proof. exact (MK_COMB (@lem263056) (@lem262992 n)). Qed.
Lemma lem263058 (m : nat) (n : nat) (P : type1605) : (term589 m n P) = (term590 m n P).
Proof. exact (MK_COMB (@lem263057 n) (@lem263055 m n P)). Qed.
Lemma lem263059 (m : nat) (n : nat) (P : type1605) : (term524 m n P) = (term589 m n P).
Proof. exact (@lem17362 (term520 n) ((term25 P m n) = (term68 m n P))). Qed.
Lemma lem263060 (m : nat) (n : nat) (P : type1605) : (term524 m n P) = (term590 m n P).
Proof. exact (TRANS (@lem263059 m n P) (@lem263058 m n P)). Qed.
Lemma lem263175 {A : Type'} (P : Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem263176 (P : Prop) (Q : nat -> Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem263175 nat P Q). Qed.
Lemma lem263177 (m : nat) (n : nat) (P : type1605) : (term591 m n P) = (term592 m n P).
Proof. exact (@lem263176 (term25 P m n) (term573 m n P)). Qed.
Lemma lem263178 (m : nat) (n : nat) (P : type1605) (q : nat) : (term593 m n P q) = (term565 m n P q).
Proof. exact (eq_refl (term593 m n P q)). Qed.
Lemma lem263179 (m : nat) (n : nat) (P : type1605) : (term594 m n P) = (term573 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263178 m n P q)). Qed.
Lemma lem263180 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263181 (m : nat) (n : nat) (P : type1605) : (term595 m n P) = (term574 m n P).
Proof. exact (MK_COMB (@lem263180) (@lem263179 m n P)). Qed.
Lemma lem263182 (P : type1605) (m : nat) (n : nat) : (term580 P m n) = (term580 P m n).
Proof. exact (eq_refl (term580 P m n)). Qed.
Lemma lem263183 (m : nat) (n : nat) (P : type1605) : (term591 m n P) = (term582 m n P).
Proof. exact (MK_COMB (@lem263182 P m n) (@lem263181 m n P)). Qed.
Lemma lem263184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263185 (m : nat) (n : nat) (P : type1605) : (term596 m n P) = (term597 m n P).
Proof. exact (MK_COMB (@lem263184) (@lem263183 m n P)). Qed.
Lemma lem263186 (m : nat) (n : nat) (P : type1605) (q : nat) : (term593 m n P q) = (term565 m n P q).
Proof. exact (eq_refl (term593 m n P q)). Qed.
Lemma lem263187 (P : type1605) (m : nat) (n : nat) : (term580 P m n) = (term580 P m n).
Proof. exact (eq_refl (term580 P m n)). Qed.
Lemma lem263188 (m : nat) (n : nat) (P : type1605) (q : nat) : (term598 m n P q) = (term599 m n P q).
Proof. exact (MK_COMB (@lem263187 P m n) (@lem263186 m n P q)). Qed.
Lemma lem263189 (m : nat) (n : nat) (P : type1605) : (term600 m n P) = (term601 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263188 m n P q)). Qed.
Lemma lem263190 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263191 (m : nat) (n : nat) (P : type1605) : (term592 m n P) = (term602 m n P).
Proof. exact (MK_COMB (@lem263190) (@lem263189 m n P)). Qed.
Lemma lem263192 (m : nat) (n : nat) (P : type1605) : ((term591 m n P) = (term592 m n P)) = ((term582 m n P) = (term602 m n P)).
Proof. exact (MK_COMB (@lem263185 m n P) (@lem263191 m n P)). Qed.
Lemma lem263193 (m : nat) (n : nat) (P : type1605) : (term582 m n P) = (term602 m n P).
Proof. exact (EQ_MP (@lem263192 m n P) (@lem263177 m n P)). Qed.
Lemma lem263195 {A : Type'} (P : Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem263196 (P : Prop) (Q : nat -> Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem263195 nat P Q). Qed.
Lemma lem263197 (m : nat) (n : nat) (P : type1605) (q : nat) : (term603 m n P q) = (term604 m n P q).
Proof. exact (@lem263196 (term25 P m n) (term564 m n P q)). Qed.
Lemma lem263198 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term605 m n P q r) = (term554 m n P q r).
Proof. exact (eq_refl (term605 m n P q r)). Qed.
Lemma lem263199 (m : nat) (n : nat) (P : type1605) (q : nat) : (term606 m n P q) = (term564 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263198 m n P q r)). Qed.
Lemma lem263200 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263201 (m : nat) (n : nat) (P : type1605) (q : nat) : (term607 m n P q) = (term565 m n P q).
Proof. exact (MK_COMB (@lem263200) (@lem263199 m n P q)). Qed.
Lemma lem263202 (P : type1605) (m : nat) (n : nat) : (term580 P m n) = (term580 P m n).
Proof. exact (eq_refl (term580 P m n)). Qed.
Lemma lem263203 (m : nat) (n : nat) (P : type1605) (q : nat) : (term603 m n P q) = (term599 m n P q).
Proof. exact (MK_COMB (@lem263202 P m n) (@lem263201 m n P q)). Qed.
Lemma lem263204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263205 (m : nat) (n : nat) (P : type1605) (q : nat) : (term608 m n P q) = (term609 m n P q).
Proof. exact (MK_COMB (@lem263204) (@lem263203 m n P q)). Qed.
Lemma lem263206 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term605 m n P q r) = (term554 m n P q r).
Proof. exact (eq_refl (term605 m n P q r)). Qed.
Lemma lem263207 (P : type1605) (m : nat) (n : nat) : (term580 P m n) = (term580 P m n).
Proof. exact (eq_refl (term580 P m n)). Qed.
Lemma lem263208 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term610 m n P q r) = (term611 m n P q r).
Proof. exact (MK_COMB (@lem263207 P m n) (@lem263206 m n P q r)). Qed.
Lemma lem263209 (m : nat) (n : nat) (P : type1605) (q : nat) : (term612 m n P q) = (term613 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263208 m n P q r)). Qed.
Lemma lem263210 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263211 (m : nat) (n : nat) (P : type1605) (q : nat) : (term604 m n P q) = (term614 m n P q).
Proof. exact (MK_COMB (@lem263210) (@lem263209 m n P q)). Qed.
Lemma lem263212 (m : nat) (n : nat) (P : type1605) (q : nat) : ((term603 m n P q) = (term604 m n P q)) = ((term599 m n P q) = (term614 m n P q)).
Proof. exact (MK_COMB (@lem263205 m n P q) (@lem263211 m n P q)). Qed.
Lemma lem263213 (m : nat) (n : nat) (P : type1605) (q : nat) : (term599 m n P q) = (term614 m n P q).
Proof. exact (EQ_MP (@lem263212 m n P q) (@lem263197 m n P q)). Qed.
Lemma lem263214 (m : nat) (n : nat) (P : type1605) : (term601 m n P) = (term615 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263213 m n P q)). Qed.
Lemma lem263215 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263216 (m : nat) (n : nat) (P : type1605) : (term602 m n P) = (term616 m n P).
Proof. exact (MK_COMB (@lem263215) (@lem263214 m n P)). Qed.
Lemma lem263217 (m : nat) (n : nat) (P : type1605) : (term582 m n P) = (term616 m n P).
Proof. exact (TRANS (@lem263193 m n P) (@lem263216 m n P)). Qed.
Lemma lem263218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263219 (m : nat) (n : nat) (P : type1605) : (term584 m n P) = (term617 m n P).
Proof. exact (MK_COMB (@lem263218) (@lem263217 m n P)). Qed.
Lemma lem263220 (m : nat) (n : nat) (P : type1605) : (term579 m n P) = (term579 m n P).
Proof. exact (eq_refl (term579 m n P)). Qed.
Lemma lem263221 (m : nat) (n : nat) (P : type1605) : (term586 m n P) = (term618 m n P).
Proof. exact (MK_COMB (@lem263219 m n P) (@lem263220 m n P)). Qed.
Lemma lem263223 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem263224 (P : nat -> Prop) (Q : Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem263223 nat P Q). Qed.
Lemma lem263225 (m : nat) (n : nat) (P : type1605) : (term619 m n P) = (term620 m n P).
Proof. exact (@lem263224 (term615 m n P) (term579 m n P)). Qed.
Lemma lem263226 (m : nat) (n : nat) (P : type1605) (q : nat) : (term621 m n P q) = (term614 m n P q).
Proof. exact (eq_refl (term621 m n P q)). Qed.
Lemma lem263227 (m : nat) (n : nat) (P : type1605) : (term622 m n P) = (term615 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263226 m n P q)). Qed.
Lemma lem263228 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263229 (m : nat) (n : nat) (P : type1605) : (term623 m n P) = (term616 m n P).
Proof. exact (MK_COMB (@lem263228) (@lem263227 m n P)). Qed.
Lemma lem263230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263231 (m : nat) (n : nat) (P : type1605) : (term624 m n P) = (term617 m n P).
Proof. exact (MK_COMB (@lem263230) (@lem263229 m n P)). Qed.
Lemma lem263232 (m : nat) (n : nat) (P : type1605) : (term579 m n P) = (term579 m n P).
Proof. exact (eq_refl (term579 m n P)). Qed.
Lemma lem263233 (m : nat) (n : nat) (P : type1605) : (term619 m n P) = (term618 m n P).
Proof. exact (MK_COMB (@lem263231 m n P) (@lem263232 m n P)). Qed.
Lemma lem263234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263235 (m : nat) (n : nat) (P : type1605) : (term625 m n P) = (term626 m n P).
Proof. exact (MK_COMB (@lem263234) (@lem263233 m n P)). Qed.
Lemma lem263236 (m : nat) (n : nat) (P : type1605) (q : nat) : (term621 m n P q) = (term614 m n P q).
Proof. exact (eq_refl (term621 m n P q)). Qed.
Lemma lem263237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263238 (m : nat) (n : nat) (P : type1605) (q : nat) : (term627 m n P q) = (term628 m n P q).
Proof. exact (MK_COMB (@lem263237) (@lem263236 m n P q)). Qed.
Lemma lem263239 (m : nat) (n : nat) (P : type1605) : (term579 m n P) = (term579 m n P).
Proof. exact (eq_refl (term579 m n P)). Qed.
Lemma lem263240 (q : nat) (m : nat) (n : nat) (P : type1605) : (term629 q m n P) = (term630 q m n P).
Proof. exact (MK_COMB (@lem263238 m n P q) (@lem263239 m n P)). Qed.
Lemma lem263241 (m : nat) (n : nat) (P : type1605) : (term631 m n P) = (term632 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263240 q m n P)). Qed.
Lemma lem263242 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263243 (m : nat) (n : nat) (P : type1605) : (term620 m n P) = (term633 m n P).
Proof. exact (MK_COMB (@lem263242) (@lem263241 m n P)). Qed.
Lemma lem263244 (m : nat) (n : nat) (P : type1605) : ((term619 m n P) = (term620 m n P)) = ((term618 m n P) = (term633 m n P)).
Proof. exact (MK_COMB (@lem263235 m n P) (@lem263243 m n P)). Qed.
Lemma lem263245 (m : nat) (n : nat) (P : type1605) : (term618 m n P) = (term633 m n P).
Proof. exact (EQ_MP (@lem263244 m n P) (@lem263225 m n P)). Qed.
Lemma lem263247 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem263248 (P : nat -> Prop) (Q : Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem263247 nat P Q). Qed.
Lemma lem263249 (q : nat) (m : nat) (n : nat) (P : type1605) : (term634 q m n P) = (term635 q m n P).
Proof. exact (@lem263248 (term613 m n P q) (term579 m n P)). Qed.
Lemma lem263250 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term636 m n P q r) = (term611 m n P q r).
Proof. exact (eq_refl (term636 m n P q r)). Qed.
Lemma lem263251 (m : nat) (n : nat) (P : type1605) (q : nat) : (term637 m n P q) = (term613 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263250 m n P q r)). Qed.
Lemma lem263252 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263253 (m : nat) (n : nat) (P : type1605) (q : nat) : (term638 m n P q) = (term614 m n P q).
Proof. exact (MK_COMB (@lem263252) (@lem263251 m n P q)). Qed.
Lemma lem263254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263255 (m : nat) (n : nat) (P : type1605) (q : nat) : (term639 m n P q) = (term628 m n P q).
Proof. exact (MK_COMB (@lem263254) (@lem263253 m n P q)). Qed.
Lemma lem263256 (m : nat) (n : nat) (P : type1605) : (term579 m n P) = (term579 m n P).
Proof. exact (eq_refl (term579 m n P)). Qed.
Lemma lem263257 (q : nat) (m : nat) (n : nat) (P : type1605) : (term634 q m n P) = (term630 q m n P).
Proof. exact (MK_COMB (@lem263255 m n P q) (@lem263256 m n P)). Qed.
Lemma lem263258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263259 (q : nat) (m : nat) (n : nat) (P : type1605) : (term640 q m n P) = (term641 q m n P).
Proof. exact (MK_COMB (@lem263258) (@lem263257 q m n P)). Qed.
Lemma lem263260 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term636 m n P q r) = (term611 m n P q r).
Proof. exact (eq_refl (term636 m n P q r)). Qed.
Lemma lem263261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263262 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term642 m n P q r) = (term643 m n P q r).
Proof. exact (MK_COMB (@lem263261) (@lem263260 m n P q r)). Qed.
Lemma lem263263 (m : nat) (n : nat) (P : type1605) : (term579 m n P) = (term579 m n P).
Proof. exact (eq_refl (term579 m n P)). Qed.
Lemma lem263264 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) : (term644 q r m n P) = (term645 q r m n P).
Proof. exact (MK_COMB (@lem263262 m n P q r) (@lem263263 m n P)). Qed.
Lemma lem263265 (q : nat) (m : nat) (n : nat) (P : type1605) : (term646 q m n P) = (term647 q m n P).
Proof. exact (fun_ext (fun r : nat => @lem263264 q r m n P)). Qed.
Lemma lem263266 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263267 (q : nat) (m : nat) (n : nat) (P : type1605) : (term635 q m n P) = (term648 q m n P).
Proof. exact (MK_COMB (@lem263266) (@lem263265 q m n P)). Qed.
Lemma lem263268 (q : nat) (m : nat) (n : nat) (P : type1605) : ((term634 q m n P) = (term635 q m n P)) = ((term630 q m n P) = (term648 q m n P)).
Proof. exact (MK_COMB (@lem263259 q m n P) (@lem263267 q m n P)). Qed.
Lemma lem263269 (q : nat) (m : nat) (n : nat) (P : type1605) : (term630 q m n P) = (term648 q m n P).
Proof. exact (EQ_MP (@lem263268 q m n P) (@lem263249 q m n P)). Qed.
Lemma lem263270 (m : nat) (n : nat) (P : type1605) : (term632 m n P) = (term649 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263269 q m n P)). Qed.
Lemma lem263271 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263272 (m : nat) (n : nat) (P : type1605) : (term633 m n P) = (term650 m n P).
Proof. exact (MK_COMB (@lem263271) (@lem263270 m n P)). Qed.
Lemma lem263273 (m : nat) (n : nat) (P : type1605) : (term618 m n P) = (term650 m n P).
Proof. exact (TRANS (@lem263245 m n P) (@lem263272 m n P)). Qed.
Lemma lem263274 (m : nat) (n : nat) (P : type1605) : (term586 m n P) = (term650 m n P).
Proof. exact (TRANS (@lem263221 m n P) (@lem263273 m n P)). Qed.
Lemma lem263275 (n : nat) : (term588 n) = (term588 n).
Proof. exact (eq_refl (term588 n)). Qed.
Lemma lem263276 (m : nat) (n : nat) (P : type1605) : (term590 m n P) = (term651 m n P).
Proof. exact (MK_COMB (@lem263275 n) (@lem263274 m n P)). Qed.
Lemma lem263278 {A : Type'} (P : Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem263279 (P : Prop) (Q : nat -> Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem263278 nat P Q). Qed.
Lemma lem263280 (m : nat) (n : nat) (P : type1605) : (term652 m n P) = (term653 m n P).
Proof. exact (@lem263279 (term520 n) (term649 m n P)). Qed.
Lemma lem263281 (q : nat) (m : nat) (n : nat) (P : type1605) : (term654 m n P q) = (term648 q m n P).
Proof. exact (eq_refl (term654 m n P q)). Qed.
Lemma lem263282 (m : nat) (n : nat) (P : type1605) : (term655 m n P) = (term649 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263281 q m n P)). Qed.
Lemma lem263283 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263284 (m : nat) (n : nat) (P : type1605) : (term656 m n P) = (term650 m n P).
Proof. exact (MK_COMB (@lem263283) (@lem263282 m n P)). Qed.
Lemma lem263285 (n : nat) : (term588 n) = (term588 n).
Proof. exact (eq_refl (term588 n)). Qed.
Lemma lem263286 (m : nat) (n : nat) (P : type1605) : (term652 m n P) = (term651 m n P).
Proof. exact (MK_COMB (@lem263285 n) (@lem263284 m n P)). Qed.
Lemma lem263287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263288 (m : nat) (n : nat) (P : type1605) : (term657 m n P) = (term658 m n P).
Proof. exact (MK_COMB (@lem263287) (@lem263286 m n P)). Qed.
Lemma lem263289 (q : nat) (m : nat) (n : nat) (P : type1605) : (term654 m n P q) = (term648 q m n P).
Proof. exact (eq_refl (term654 m n P q)). Qed.
Lemma lem263290 (n : nat) : (term588 n) = (term588 n).
Proof. exact (eq_refl (term588 n)). Qed.
Lemma lem263291 (q : nat) (m : nat) (n : nat) (P : type1605) : (term659 m n P q) = (term660 q m n P).
Proof. exact (MK_COMB (@lem263290 n) (@lem263289 q m n P)). Qed.
Lemma lem263292 (m : nat) (n : nat) (P : type1605) : (term661 m n P) = (term662 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263291 q m n P)). Qed.
Lemma lem263293 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263294 (m : nat) (n : nat) (P : type1605) : (term653 m n P) = (term663 m n P).
Proof. exact (MK_COMB (@lem263293) (@lem263292 m n P)). Qed.
Lemma lem263295 (m : nat) (n : nat) (P : type1605) : ((term652 m n P) = (term653 m n P)) = ((term651 m n P) = (term663 m n P)).
Proof. exact (MK_COMB (@lem263288 m n P) (@lem263294 m n P)). Qed.
Lemma lem263296 (m : nat) (n : nat) (P : type1605) : (term651 m n P) = (term663 m n P).
Proof. exact (EQ_MP (@lem263295 m n P) (@lem263280 m n P)). Qed.
Lemma lem263298 {A : Type'} (P : Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem263299 (P : Prop) (Q : nat -> Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem263298 nat P Q). Qed.
Lemma lem263300 (q : nat) (m : nat) (n : nat) (P : type1605) : (term664 q m n P) = (term665 q m n P).
Proof. exact (@lem263299 (term520 n) (term647 q m n P)). Qed.
Lemma lem263301 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) : (term666 q m n P r) = (term645 q r m n P).
Proof. exact (eq_refl (term666 q m n P r)). Qed.
Lemma lem263302 (q : nat) (m : nat) (n : nat) (P : type1605) : (term667 q m n P) = (term647 q m n P).
Proof. exact (fun_ext (fun r : nat => @lem263301 q r m n P)). Qed.
Lemma lem263303 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263304 (q : nat) (m : nat) (n : nat) (P : type1605) : (term668 q m n P) = (term648 q m n P).
Proof. exact (MK_COMB (@lem263303) (@lem263302 q m n P)). Qed.
Lemma lem263305 (n : nat) : (term588 n) = (term588 n).
Proof. exact (eq_refl (term588 n)). Qed.
Lemma lem263306 (q : nat) (m : nat) (n : nat) (P : type1605) : (term664 q m n P) = (term660 q m n P).
Proof. exact (MK_COMB (@lem263305 n) (@lem263304 q m n P)). Qed.
Lemma lem263307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263308 (q : nat) (m : nat) (n : nat) (P : type1605) : (term669 q m n P) = (term670 q m n P).
Proof. exact (MK_COMB (@lem263307) (@lem263306 q m n P)). Qed.
Lemma lem263309 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) : (term666 q m n P r) = (term645 q r m n P).
Proof. exact (eq_refl (term666 q m n P r)). Qed.
Lemma lem263310 (n : nat) : (term588 n) = (term588 n).
Proof. exact (eq_refl (term588 n)). Qed.
Lemma lem263311 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) : (term671 q m n P r) = (term672 q r m n P).
Proof. exact (MK_COMB (@lem263310 n) (@lem263309 q r m n P)). Qed.
Lemma lem263312 (q : nat) (m : nat) (n : nat) (P : type1605) : (term673 q m n P) = (term674 q m n P).
Proof. exact (fun_ext (fun r : nat => @lem263311 q r m n P)). Qed.
Lemma lem263313 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263314 (q : nat) (m : nat) (n : nat) (P : type1605) : (term665 q m n P) = (term675 q m n P).
Proof. exact (MK_COMB (@lem263313) (@lem263312 q m n P)). Qed.
Lemma lem263315 (q : nat) (m : nat) (n : nat) (P : type1605) : ((term664 q m n P) = (term665 q m n P)) = ((term660 q m n P) = (term675 q m n P)).
Proof. exact (MK_COMB (@lem263308 q m n P) (@lem263314 q m n P)). Qed.
Lemma lem263316 (q : nat) (m : nat) (n : nat) (P : type1605) : (term660 q m n P) = (term675 q m n P).
Proof. exact (EQ_MP (@lem263315 q m n P) (@lem263300 q m n P)). Qed.
Lemma lem263317 (m : nat) (n : nat) (P : type1605) : (term662 m n P) = (term676 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263316 q m n P)). Qed.
Lemma lem263318 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem263319 (m : nat) (n : nat) (P : type1605) : (term663 m n P) = (term677 m n P).
Proof. exact (MK_COMB (@lem263318) (@lem263317 m n P)). Qed.
Lemma lem263320 (m : nat) (n : nat) (P : type1605) : (term651 m n P) = (term677 m n P).
Proof. exact (TRANS (@lem263296 m n P) (@lem263319 m n P)). Qed.
Lemma lem263322 (m : nat) (n : nat) (P : type1605) : (term590 m n P) = (term677 m n P).
Proof. exact (TRANS (@lem263276 m n P) (@lem263320 m n P)). Qed.
Lemma lem263323 (m : nat) (n : nat) (P : type1605) : (term524 m n P) = (term677 m n P).
Proof. exact (TRANS (@lem263060 m n P) (@lem263322 m n P)). Qed.
Lemma lem263324 (m : nat) (n : nat) (P : type1605) (h1 : term524 m n P) : term677 m n P.
Proof. exact (EQ_MP (@lem263323 m n P) (@lem262980 m n P h1)). Qed.
Lemma lem263331 (m : nat) (q : nat) (r : nat) (n : nat) : (term551 m q r n) = (term552 m q r n).
Proof. exact (@lem17045 (m = (term39 q n r)) (Peano.lt r n)). Qed.
Lemma lem263336 (q : nat) (m : nat) (n : nat) (r : nat) : (term678 q m n r) = (term678 q m n r).
Proof. exact (eq_refl (term678 q m n r)). Qed.
Lemma lem263337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem263338 (m : nat) (q : nat) (r : nat) (n : nat) : (term555 m q r n) = (term556 m q r n).
Proof. exact (MK_COMB (@lem263337) (@lem263331 m q r n)). Qed.
Lemma lem263339 (q : nat) (m : nat) (n : nat) (r : nat) : (term679 q m n r) = (term680 q m n r).
Proof. exact (MK_COMB (@lem263338 m q r n) (@lem263336 q m n r)). Qed.
Lemma lem263340 (q : nat) (m : nat) (n : nat) (r : nat) : (term543 q m n r) = (term679 q m n r).
Proof. exact (@lem17265 (term44 m q r n) (term678 q m n r)). Qed.
Lemma lem263341 (q : nat) (m : nat) (n : nat) (r : nat) : (term543 q m n r) = (term680 q m n r).
Proof. exact (TRANS (@lem263340 q m n r) (@lem263339 q m n r)). Qed.
Lemma lem263342 (q : nat) (m : nat) (n : nat) : (term544 q m n) = (term681 q m n).
Proof. exact (fun_ext (fun r : nat => @lem263341 q m n r)). Qed.
Lemma lem263343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263344 (q : nat) (m : nat) (n : nat) : (term545 q m n) = (term682 q m n).
Proof. exact (MK_COMB (@lem263343) (@lem263342 q m n)). Qed.
Lemma lem263345 (m : nat) (n : nat) : (term546 m n) = (term683 m n).
Proof. exact (fun_ext (fun q : nat => @lem263344 q m n)). Qed.
Lemma lem263346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263347 (m : nat) (n : nat) : (term547 m n) = (term684 m n).
Proof. exact (MK_COMB (@lem263346) (@lem263345 m n)). Qed.
Lemma lem263348 (m : nat) : (term548 m) = (term685 m).
Proof. exact (fun_ext (fun n : nat => @lem263347 m n)). Qed.
Lemma lem263349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263350 (m : nat) : (term549 m) = (term686 m).
Proof. exact (MK_COMB (@lem263349) (@lem263348 m)). Qed.
Lemma lem263351 : term550 = term687.
Proof. exact (fun_ext (fun m : nat => @lem263350 m)). Qed.
Lemma lem263352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263417 : term529 = term688.
Proof. exact (MK_COMB (@lem263352) (@lem263351)). Qed.
Lemma lem263418 (h1 : term529) : term688.
Proof. exact (EQ_MP (@lem263417) (@lem262981 h1)). Qed.
Lemma lem263419 (q : nat) (m : nat) (n : nat) (P : type1605) (h1 : term675 q m n P) : term675 q m n P.
Proof. exact (h1). Qed.
Lemma lem263420 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term672 q r m n P.
Proof. exact (h1). Qed.
Lemma lem263469 (q : nat) (m : nat) (n : nat) (r : nat) : (term680 q m n r) = (term680 q m n r).
Proof. exact (eq_refl (term680 q m n r)). Qed.
Lemma lem263470 (q : nat) (m : nat) (n : nat) : (term681 q m n) = (term681 q m n).
Proof. exact (fun_ext (fun r : nat => @lem263469 q m n r)). Qed.
Lemma lem263471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263472 (q : nat) (m : nat) (n : nat) : (term682 q m n) = (term682 q m n).
Proof. exact (MK_COMB (@lem263471) (@lem263470 q m n)). Qed.
Lemma lem263473 (m : nat) (n : nat) : (term683 m n) = (term683 m n).
Proof. exact (fun_ext (fun q : nat => @lem263472 q m n)). Qed.
Lemma lem263474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263475 (m : nat) (n : nat) : (term684 m n) = (term684 m n).
Proof. exact (MK_COMB (@lem263474) (@lem263473 m n)). Qed.
Lemma lem263476 (m : nat) : (term685 m) = (term685 m).
Proof. exact (fun_ext (fun n : nat => @lem263475 m n)). Qed.
Lemma lem263477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263478 (m : nat) : (term686 m) = (term686 m).
Proof. exact (MK_COMB (@lem263477) (@lem263476 m)). Qed.
Lemma lem263479 : term687 = term687.
Proof. exact (fun_ext (fun m : nat => @lem263478 m)). Qed.
Lemma lem263480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263481 : term688 = term688.
Proof. exact (MK_COMB (@lem263480) (@lem263479)). Qed.
Lemma lem263482 (h1 : term529) : term688.
Proof. exact (EQ_MP (@lem263481) (@lem263418 h1)). Qed.
Lemma lem263515 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term558 m n P q r) = (term558 m n P q r).
Proof. exact (eq_refl (term558 m n P q r)). Qed.
Lemma lem263516 (m : nat) (n : nat) (P : type1605) (q : nat) : (term566 m n P q) = (term566 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263515 m n P q r)). Qed.
Lemma lem263517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263518 (m : nat) (n : nat) (P : type1605) (q : nat) : (term567 m n P q) = (term567 m n P q).
Proof. exact (MK_COMB (@lem263517) (@lem263516 m n P q)). Qed.
Lemma lem263519 (m : nat) (n : nat) (P : type1605) : (term575 m n P) = (term575 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263518 m n P q)). Qed.
Lemma lem263520 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263521 (m : nat) (n : nat) (P : type1605) : (term576 m n P) = (term576 m n P).
Proof. exact (MK_COMB (@lem263520) (@lem263519 m n P)). Qed.
Lemma lem263538 (P : type1605) (m : nat) (n : nat) : (term577 P m n) = (term577 P m n).
Proof. exact (eq_refl (term577 P m n)). Qed.
Lemma lem263539 (m : nat) (n : nat) (P : type1605) : (term579 m n P) = (term579 m n P).
Proof. exact (MK_COMB (@lem263538 P m n) (@lem263521 m n P)). Qed.
Lemma lem263588 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term643 m n P q r) = (term643 m n P q r).
Proof. exact (eq_refl (term643 m n P q r)). Qed.
Lemma lem263589 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) : (term645 q r m n P) = (term645 q r m n P).
Proof. exact (MK_COMB (@lem263588 m n P q r) (@lem263539 m n P)). Qed.
Lemma lem263598 (m : nat) (n : nat) : (term506 m n) = (term506 m n).
Proof. exact (eq_refl (term506 m n)). Qed.
Lemma lem263599 (n : nat) : (term500 n) = (term500 n).
Proof. exact (fun_ext (fun m : nat => @lem263598 m n)). Qed.
Lemma lem263600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263601 (n : nat) : (term519 n) = (term519 n).
Proof. exact (MK_COMB (@lem263600) (@lem263599 n)). Qed.
Lemma lem263622 (m : nat) (n : nat) : (m = (term502 m n)) = (m = (term502 m n)).
Proof. exact (eq_refl (m = (term502 m n))). Qed.
Lemma lem263623 (n : nat) : (term499 n) = (term499 n).
Proof. exact (fun_ext (fun m : nat => @lem263622 m n)). Qed.
Lemma lem263624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263625 (n : nat) : (term514 n) = (term514 n).
Proof. exact (MK_COMB (@lem263624) (@lem263623 n)). Qed.
Lemma lem263626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem263627 (n : nat) : (term516 n) = (term516 n).
Proof. exact (MK_COMB (@lem263626) (@lem263625 n)). Qed.
Lemma lem263628 (n : nat) : (term520 n) = (term520 n).
Proof. exact (MK_COMB (@lem263627 n) (@lem263601 n)). Qed.
Lemma lem263629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem263630 (n : nat) : (term588 n) = (term588 n).
Proof. exact (MK_COMB (@lem263629) (@lem263628 n)). Qed.
Lemma lem263631 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) : (term672 q r m n P) = (term672 q r m n P).
Proof. exact (MK_COMB (@lem263630 n) (@lem263589 q r m n P)). Qed.
Lemma lem263632 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term672 q r m n P.
Proof. exact (EQ_MP (@lem263631 q r m n P) (@lem263420 q r m n P h1)). Qed.
Lemma lem263633 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term645 q r m n P.
Proof. exact (proj2 (@lem263632 q r m n P h1)). Qed.
Lemma lem263634 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term520 n.
Proof. exact (proj1 (@lem263632 q r m n P h1)). Qed.
Lemma lem263635 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term519 n.
Proof. exact (proj2 (@lem263634 q r m n P h1)). Qed.
Lemma lem263636 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term514 n.
Proof. exact (proj1 (@lem263634 q r m n P h1)). Qed.
Lemma lem263637 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term611 m n P q r.
Proof. exact (h1). Qed.
Lemma lem263638 (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term579 m n P.
Proof. exact (h1). Qed.
Lemma lem263639 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term554 m n P q r.
Proof. exact (proj2 (@lem263637 m n P q r h1)). Qed.
Lemma lem263642 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term44 m q r n.
Proof. exact (proj1 (@lem263639 m n P q r h1)). Qed.
Lemma lem263645 (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term576 m n P.
Proof. exact (proj2 (@lem263638 m n P h1)). Qed.
Lemma lem263670 (q : nat) (m : nat) (n : nat) (r : nat) : (term680 q m n r) = (term689 q m n r).
Proof. exact (@lem19490 ((Nat.div m n) = q) (term552 m q r n) ((Nat.modulo m n) = r)). Qed.
Lemma lem263671 (q : nat) (m : nat) (n : nat) : (term681 q m n) = (term690 q m n).
Proof. exact (fun_ext (fun r : nat => @lem263670 q m n r)). Qed.
Lemma lem263672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263673 (q : nat) (m : nat) (n : nat) : (term682 q m n) = (term691 q m n).
Proof. exact (MK_COMB (@lem263672) (@lem263671 q m n)). Qed.
Lemma lem263674 (m : nat) (n : nat) : (term683 m n) = (term692 m n).
Proof. exact (fun_ext (fun q : nat => @lem263673 q m n)). Qed.
Lemma lem263675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263676 (m : nat) (n : nat) : (term684 m n) = (term693 m n).
Proof. exact (MK_COMB (@lem263675) (@lem263674 m n)). Qed.
Lemma lem263677 (m : nat) : (term685 m) = (term694 m).
Proof. exact (fun_ext (fun n : nat => @lem263676 m n)). Qed.
Lemma lem263678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263679 (m : nat) : (term686 m) = (term695 m).
Proof. exact (MK_COMB (@lem263678) (@lem263677 m)). Qed.
Lemma lem263680 : term687 = term696.
Proof. exact (fun_ext (fun m : nat => @lem263679 m)). Qed.
Lemma lem263681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263683 : term688 = term697.
Proof. exact (MK_COMB (@lem263681) (@lem263680)). Qed.
Lemma lem263684 (h1 : term529) : term697.
Proof. exact (EQ_MP (@lem263683) (@lem263482 h1)). Qed.
Lemma lem263754 (m : nat) (n : nat) : (m = (term502 m n)) = (m = (term502 m n)).
Proof. exact (eq_refl (m = (term502 m n))). Qed.
Lemma lem263755 (n : nat) : (term499 n) = (term499 n).
Proof. exact (fun_ext (fun m : nat => @lem263754 m n)). Qed.
Lemma lem263756 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263758 (n : nat) : (term514 n) = (term514 n).
Proof. exact (MK_COMB (@lem263756) (@lem263755 n)). Qed.
Lemma lem263759 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term514 n.
Proof. exact (EQ_MP (@lem263758 n) (@lem263636 q r m n P h1)). Qed.
Lemma lem263761 (m : nat) (n : nat) : (term506 m n) = (term506 m n).
Proof. exact (eq_refl (term506 m n)). Qed.
Lemma lem263762 (n : nat) : (term500 n) = (term500 n).
Proof. exact (fun_ext (fun m : nat => @lem263761 m n)). Qed.
Lemma lem263763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263765 (n : nat) : (term519 n) = (term519 n).
Proof. exact (MK_COMB (@lem263763) (@lem263762 n)). Qed.
Lemma lem263766 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term519 n.
Proof. exact (EQ_MP (@lem263765 n) (@lem263635 q r m n P h1)). Qed.
Lemma lem263784 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term558 m n P q r) = (term558 m n P q r).
Proof. exact (eq_refl (term558 m n P q r)). Qed.
Lemma lem263785 (m : nat) (n : nat) (P : type1605) (q : nat) : (term566 m n P q) = (term566 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem263784 m n P q r)). Qed.
Lemma lem263786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263787 (m : nat) (n : nat) (P : type1605) (q : nat) : (term567 m n P q) = (term567 m n P q).
Proof. exact (MK_COMB (@lem263786) (@lem263785 m n P q)). Qed.
Lemma lem263788 (m : nat) (n : nat) (P : type1605) : (term575 m n P) = (term575 m n P).
Proof. exact (fun_ext (fun q : nat => @lem263787 m n P q)). Qed.
Lemma lem263789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem263791 (m : nat) (n : nat) (P : type1605) : (term576 m n P) = (term576 m n P).
Proof. exact (MK_COMB (@lem263789) (@lem263788 m n P)). Qed.
Lemma lem263792 (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term576 m n P.
Proof. exact (EQ_MP (@lem263791 m n P) (@lem263645 m n P h1)). Qed.
Lemma lem263793 (_5791 : nat) (h1 : term529) : term698 _5791.
Proof. exact (@lem263684 h1 _5791). Qed.
Lemma lem263794 (_5791 : nat) : (term698 _5791) = (term695 _5791).
Proof. exact (eq_refl (term698 _5791)). Qed.
Lemma lem263795 (_5791 : nat) (h1 : term529) : term695 _5791.
Proof. exact (EQ_MP (@lem263794 _5791) (@lem263793 _5791 h1)). Qed.
Lemma lem263796 (_5791 : nat) (_5792 : nat) (h1 : term529) : term699 _5791 _5792.
Proof. exact (@lem263795 _5791 h1 _5792). Qed.
Lemma lem263797 (_5791 : nat) (_5792 : nat) : (term699 _5791 _5792) = (term693 _5791 _5792).
Proof. exact (eq_refl (term699 _5791 _5792)). Qed.
Lemma lem263798 (_5791 : nat) (_5792 : nat) (h1 : term529) : term693 _5791 _5792.
Proof. exact (EQ_MP (@lem263797 _5791 _5792) (@lem263796 _5791 _5792 h1)). Qed.
Lemma lem263799 (_5791 : nat) (_5792 : nat) (_5793 : nat) (h1 : term529) : term700 _5791 _5792 _5793.
Proof. exact (@lem263798 _5791 _5792 h1 _5793). Qed.
Lemma lem263800 (_5793 : nat) (_5791 : nat) (_5792 : nat) : (term700 _5791 _5792 _5793) = (term691 _5793 _5791 _5792).
Proof. exact (eq_refl (term700 _5791 _5792 _5793)). Qed.
Lemma lem263801 (_5793 : nat) (_5791 : nat) (_5792 : nat) (h1 : term529) : term691 _5793 _5791 _5792.
Proof. exact (EQ_MP (@lem263800 _5793 _5791 _5792) (@lem263799 _5791 _5792 _5793 h1)). Qed.
Lemma lem263802 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) (h1 : term529) : term701 _5793 _5791 _5792 _5794.
Proof. exact (@lem263801 _5793 _5791 _5792 h1 _5794). Qed.
Lemma lem263803 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term701 _5793 _5791 _5792 _5794) = (term689 _5793 _5791 _5792 _5794).
Proof. exact (eq_refl (term701 _5793 _5791 _5792 _5794)). Qed.
Lemma lem263804 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) (h1 : term529) : term689 _5793 _5791 _5792 _5794.
Proof. exact (EQ_MP (@lem263803 _5793 _5791 _5792 _5794) (@lem263802 _5793 _5791 _5792 _5794 h1)). Qed.
Lemma lem263823 (_5801 : nat) (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term501 n _5801.
Proof. exact (@lem263759 q r m n P h1 _5801). Qed.
Lemma lem263824 (_5801 : nat) (n : nat) : (term501 n _5801) = (_5801 = (term502 _5801 n)).
Proof. exact (eq_refl (term501 n _5801)). Qed.
Lemma lem263826 (_5802 : nat) (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term505 n _5802.
Proof. exact (@lem263766 q r m n P h1 _5802). Qed.
Lemma lem263827 (_5802 : nat) (n : nat) : (term505 n _5802) = (term506 _5802 n).
Proof. exact (eq_refl (term505 n _5802)). Qed.
Lemma lem263829 (_5803 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term702 m n P _5803.
Proof. exact (@lem263792 m n P h1 _5803). Qed.
Lemma lem263830 (m : nat) (n : nat) (P : type1605) (_5803 : nat) : (term702 m n P _5803) = (term567 m n P _5803).
Proof. exact (eq_refl (term702 m n P _5803)). Qed.
Lemma lem263831 (_5803 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term567 m n P _5803.
Proof. exact (EQ_MP (@lem263830 m n P _5803) (@lem263829 _5803 m n P h1)). Qed.
Lemma lem263832 (_5803 : nat) (_5804 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term703 m n P _5803 _5804.
Proof. exact (@lem263831 _5803 m n P h1 _5804). Qed.
Lemma lem263833 (m : nat) (n : nat) (P : type1605) (_5803 : nat) (_5804 : nat) : (term703 m n P _5803 _5804) = (term558 m n P _5803 _5804).
Proof. exact (eq_refl (term703 m n P _5803 _5804)). Qed.
Lemma lem263834 (_5803 : nat) (_5804 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term558 m n P _5803 _5804.
Proof. exact (EQ_MP (@lem263833 m n P _5803 _5804) (@lem263832 _5803 _5804 m n P h1)). Qed.
Lemma lem263835 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) (h1 : term529) : term704 _5793 _5791 _5792 _5794.
Proof. exact (proj2 (@lem263804 _5793 _5791 _5792 _5794 h1)). Qed.
Lemma lem263836 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) (h1 : term529) : term705 _5794 _5791 _5792 _5793.
Proof. exact (proj1 (@lem263804 _5793 _5791 _5792 _5794 h1)). Qed.
Lemma lem263844 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term25 P m n.
Proof. exact (proj1 (@lem263637 m n P q r h1)). Qed.
Lemma lem263848 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : m = (term39 q n r).
Proof. exact (proj1 (@lem263642 m n P q r h1)). Qed.
Lemma lem263861 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) : (term705 _5794 _5791 _5792 _5793) = (term706 _5794 _5791 _5792 _5793).
Proof. exact (@lem257927 (term707 _5791 _5793 _5792 _5794) (term708 _5794 _5792) ((Nat.div _5791 _5792) = _5793)). Qed.
Lemma lem263873 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term704 _5793 _5791 _5792 _5794) = (term709 _5793 _5791 _5792 _5794).
Proof. exact (@lem257927 (term707 _5791 _5793 _5792 _5794) (term708 _5794 _5792) ((Nat.modulo _5791 _5792) = _5794)). Qed.
Lemma lem263880 (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term710 P m n.
Proof. exact (proj1 (@lem263638 m n P h1)). Qed.
Lemma lem263891 (m : nat) (n : nat) (P : type1605) (_5803 : nat) (_5804 : nat) : (term558 m n P _5803 _5804) = (term711 m n P _5803 _5804).
Proof. exact (@lem257927 (term707 m _5803 n _5804) (term708 _5804 n) (P _5803 _5804)). Qed.
Lemma lem263892 (_5803 : nat) (_5804 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term711 m n P _5803 _5804.
Proof. exact (EQ_MP (@lem263891 m n P _5803 _5804) (@lem263834 _5803 _5804 m n P h1)). Qed.
Lemma lem263959 (P : type1605) (n : nat) : (term712 P n) = (term712 P n).
Proof. exact (eq_refl (term712 P n)). Qed.
Lemma lem263960 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : (term713 P n m) = (term714 P q n r).
Proof. exact (MK_COMB (@lem263959 P n) (@lem263848 m n P q r h1)). Qed.
Lemma lem263961 (P : type1605) (q : nat) (r : nat) (n : nat) : (term714 P q n r) = (term715 P q r n).
Proof. exact (eq_refl (term714 P q n r)). Qed.
Lemma lem263962 (P : type1605) (n : nat) (m : nat) : (term716 P n m) = (term716 P n m).
Proof. exact (eq_refl (term716 P n m)). Qed.
Lemma lem263963 (m : nat) (P : type1605) (q : nat) (r : nat) (n : nat) : ((term713 P n m) = (term714 P q n r)) = ((term713 P n m) = (term715 P q r n)).
Proof. exact (MK_COMB (@lem263962 P n m) (@lem263961 P q r n)). Qed.
Lemma lem263964 (P : type1605) (m : nat) (n : nat) : (term713 P n m) = (term25 P m n).
Proof. exact (eq_refl (term713 P n m)). Qed.
Lemma lem263965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem263966 (P : type1605) (m : nat) (n : nat) : (term716 P n m) = (term27 P m n).
Proof. exact (MK_COMB (@lem263965) (@lem263964 P m n)). Qed.
Lemma lem263967 (P : type1605) (q : nat) (r : nat) (n : nat) : (term715 P q r n) = (term715 P q r n).
Proof. exact (eq_refl (term715 P q r n)). Qed.
Lemma lem263968 (m : nat) (P : type1605) (q : nat) (r : nat) (n : nat) : ((term713 P n m) = (term715 P q r n)) = ((term25 P m n) = (term715 P q r n)).
Proof. exact (MK_COMB (@lem263966 P m n) (@lem263967 P q r n)). Qed.
Lemma lem263969 (m : nat) (P : type1605) (q : nat) (r : nat) (n : nat) : ((term713 P n m) = (term714 P q n r)) = ((term25 P m n) = (term715 P q r n)).
Proof. exact (TRANS (@lem263963 m P q r n) (@lem263968 m P q r n)). Qed.
Lemma lem263970 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : (term25 P m n) = (term715 P q r n).
Proof. exact (EQ_MP (@lem263969 m P q r n) (@lem263960 m n P q r h1)). Qed.
Lemma lem263985 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term382 P q r.
Proof. exact (proj2 (@lem263639 m n P q r h1)). Qed.
Lemma lem264013 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) (h1 : term529) : term706 _5794 _5791 _5792 _5793.
Proof. exact (EQ_MP (@lem263861 _5794 _5791 _5792 _5793) (@lem263836 _5794 _5791 _5792 _5793 h1)). Qed.
Lemma lem264027 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) (h1 : term529) : term709 _5793 _5791 _5792 _5794.
Proof. exact (EQ_MP (@lem263873 _5793 _5791 _5792 _5794) (@lem263835 _5793 _5791 _5792 _5794 h1)). Qed.
Lemma lem264028 (P : type1605) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem264029 (_5821 : nat) (_5823 : nat) (h1 : _5821 = _5823) : _5821 = _5823.
Proof. exact (h1). Qed.
Lemma lem264030 (_5822 : nat) (_5824 : nat) (h1 : _5822 = _5824) : _5822 = _5824.
Proof. exact (h1). Qed.
Lemma lem264031 (P : type1605) (_5821 : nat) (_5823 : nat) (h1 : _5821 = _5823) : (P _5821) = (P _5823).
Proof. exact (MK_COMB (@lem264028 P) (@lem264029 _5821 _5823 h1)). Qed.
Lemma lem264032 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) (h1 : _5821 = _5823) (h2 : _5822 = _5824) : (P _5821 _5822) = (P _5823 _5824).
Proof. exact (MK_COMB (@lem264031 P _5821 _5823 h1) (@lem264030 _5822 _5824 h2)). Qed.
Lemma lem264034 (b : Prop) (a : Prop) : term397 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem264035 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : term398 _5823 _5824 P _5821 _5822.
Proof. exact (@lem264034 (P _5823 _5824) (P _5821 _5822)). Qed.
Lemma lem264036 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) (h1 : _5821 = _5823) (h2 : _5822 = _5824) : term399 _5823 _5824 P _5821 _5822.
Proof. exact (@lem264035 _5823 _5824 P _5821 _5822 (@lem264032 P _5821 _5823 _5822 _5824 h1 h2)). Qed.
Lemma lem264037 (_5824 : nat) (P : type1605) (_5822 : nat) (_5821 : nat) (_5823 : nat) (h1 : _5821 = _5823) : term400 _5823 _5824 P _5821 _5822.
Proof. exact (fun h0 : _5822 = _5824 => @lem264036 P _5821 _5823 _5822 _5824 h1 h0). Qed.
Lemma lem264039 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem264040 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term400 _5823 _5824 P _5821 _5822) = (term402 _5823 _5824 P _5821 _5822).
Proof. exact (@lem264039 (_5822 = _5824) (term399 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264041 (_5824 : nat) (P : type1605) (_5822 : nat) (_5821 : nat) (_5823 : nat) (h1 : _5821 = _5823) : term402 _5823 _5824 P _5821 _5822.
Proof. exact (EQ_MP (@lem264040 _5823 _5824 P _5821 _5822) (@lem264037 _5824 P _5822 _5821 _5823 h1)). Qed.
Lemma lem264042 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : term403 _5823 _5824 P _5821 _5822.
Proof. exact (fun h0 : _5821 = _5823 => @lem264041 _5824 P _5822 _5821 _5823 h0). Qed.
Lemma lem264044 (a : Prop) (b : Prop) : (a -> b) = (term401 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem264045 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term403 _5823 _5824 P _5821 _5822) = (term404 _5823 _5824 P _5821 _5822).
Proof. exact (@lem264044 (_5821 = _5823) (term402 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264046 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : term404 _5823 _5824 P _5821 _5822.
Proof. exact (EQ_MP (@lem264045 _5823 _5824 P _5821 _5822) (@lem264042 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264129 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem264130 (q : nat) (n : nat) (r : nat) : (term39 q n r) = (term39 q n r).
Proof. exact (@lem264129 (term39 q n r)). Qed.
Lemma lem264131 (q : nat) (n : nat) (r : nat) : term717 q n r.
Proof. exact (fun h0 : term718 q n r => @lem264130 q n r). Qed.
Lemma lem264133 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264134 (q : nat) (n : nat) (r : nat) : (term717 q n r) = ((term39 q n r) = (term39 q n r)).
Proof. exact (@lem264133 ((term39 q n r) = (term39 q n r))). Qed.
Lemma lem264135 (q : nat) (n : nat) (r : nat) : (term39 q n r) = (term39 q n r).
Proof. exact (EQ_MP (@lem264134 q n r) (@lem264131 q n r)). Qed.
Lemma lem264137 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : Peano.lt r n.
Proof. exact (proj2 (@lem263642 m n P q r h1)). Qed.
Lemma lem264138 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term719 r n.
Proof. exact (fun h0 : term708 r n => @lem264137 m n P q r h1). Qed.
Lemma lem264140 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264141 (r : nat) (n : nat) : (term719 r n) = (Peano.lt r n).
Proof. exact (@lem264140 (Peano.lt r n)). Qed.
Lemma lem264142 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : Peano.lt r n.
Proof. exact (EQ_MP (@lem264141 r n) (@lem264138 m n P q r h1)). Qed.
Lemma lem264148 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264149 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) : (term706 _5794 _5791 _5792 _5793) = (term720 _5794 _5791 _5792 _5793).
Proof. exact (@lem264148 (term708 _5794 _5792) (term707 _5791 _5793 _5792 _5794) ((Nat.div _5791 _5792) = _5793)). Qed.
Lemma lem264163 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264164 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term721 _5794 _5791 _5792 _5793) = (term722 _5791 _5793 _5792 _5794).
Proof. exact (@lem264163 ((Nat.div _5791 _5792) = _5793) (term707 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264174 (_5794 : nat) (_5792 : nat) : (term723 _5794 _5792) = (term723 _5794 _5792).
Proof. exact (eq_refl (term723 _5794 _5792)). Qed.
Lemma lem264175 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term720 _5794 _5791 _5792 _5793) = (term724 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264174 _5794 _5792) (@lem264164 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264179 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264180 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term724 _5791 _5793 _5792 _5794) = (term725 _5791 _5793 _5792 _5794).
Proof. exact (@lem264179 ((Nat.div _5791 _5792) = _5793) (term708 _5794 _5792) (term707 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264200 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term720 _5794 _5791 _5792 _5793) = (term725 _5791 _5793 _5792 _5794).
Proof. exact (TRANS (@lem264175 _5791 _5793 _5792 _5794) (@lem264180 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264201 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term706 _5794 _5791 _5792 _5793) = (term725 _5791 _5793 _5792 _5794).
Proof. exact (TRANS (@lem264149 _5794 _5791 _5792 _5793) (@lem264200 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem264203 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term726 _5794 _5791 _5792 _5793) = (term727 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264202) (@lem264201 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264219 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264220 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term552 _5791 _5793 _5794 _5792) = (term728 _5791 _5793 _5792 _5794).
Proof. exact (@lem264219 (term708 _5794 _5792) (term707 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264228 (_5791 : nat) (_5792 : nat) (_5793 : nat) : (term729 _5791 _5792 _5793) = (term729 _5791 _5792 _5793).
Proof. exact (eq_refl (term729 _5791 _5792 _5793)). Qed.
Lemma lem264229 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term730 _5791 _5793 _5794 _5792) = (term725 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264228 _5791 _5792 _5793) (@lem264220 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264240 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : ((term706 _5794 _5791 _5792 _5793) = (term730 _5791 _5793 _5794 _5792)) = ((term725 _5791 _5793 _5792 _5794) = (term725 _5791 _5793 _5792 _5794)).
Proof. exact (MK_COMB (@lem264203 _5791 _5793 _5792 _5794) (@lem264229 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264242 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem264243 (x : Prop) : (x = x) = True.
Proof. exact (@lem264242 Prop x). Qed.
Lemma lem264244 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : ((term725 _5791 _5793 _5792 _5794) = (term725 _5791 _5793 _5792 _5794)) = True.
Proof. exact (@lem264243 (term725 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264245 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : ((term706 _5794 _5791 _5792 _5793) = (term730 _5791 _5793 _5794 _5792)) = True.
Proof. exact (TRANS (@lem264240 _5791 _5793 _5792 _5794) (@lem264244 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264246 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : True = ((term706 _5794 _5791 _5792 _5793) = (term730 _5791 _5793 _5794 _5792)).
Proof. exact (SYM (@lem264245 _5791 _5793 _5794 _5792)). Qed.
Lemma lem264247 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term706 _5794 _5791 _5792 _5793) = (term730 _5791 _5793 _5794 _5792).
Proof. exact (EQ_MP (@lem264246 _5791 _5793 _5794 _5792) (@lem0)). Qed.
Lemma lem264248 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) (h1 : term529) : term730 _5791 _5793 _5794 _5792.
Proof. exact (EQ_MP (@lem264247 _5791 _5793 _5794 _5792) (@lem264013 _5794 _5791 _5792 _5793 h1)). Qed.
Lemma lem264250 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem264251 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) : (term730 _5791 _5793 _5794 _5792) = (term731 _5794 _5791 _5792 _5793).
Proof. exact (@lem264250 (term552 _5791 _5793 _5794 _5792) ((Nat.div _5791 _5792) = _5793)). Qed.
Lemma lem264253 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem264254 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term732 _5791 _5793 _5794 _5792) = (term733 _5791 _5793 _5794 _5792).
Proof. exact (@lem264253 (term707 _5791 _5793 _5792 _5794) (term708 _5794 _5792)). Qed.
Lemma lem264256 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264257 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term734 _5791 _5793 _5792 _5794) = (_5791 = (term39 _5793 _5792 _5794)).
Proof. exact (@lem264256 (_5791 = (term39 _5793 _5792 _5794))). Qed.
Lemma lem264258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem264259 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term735 _5791 _5793 _5792 _5794) = (term41 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264258) (@lem264257 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264261 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264262 (_5794 : nat) (_5792 : nat) : (term736 _5794 _5792) = (Peano.lt _5794 _5792).
Proof. exact (@lem264261 (Peano.lt _5794 _5792)). Qed.
Lemma lem264263 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term733 _5791 _5793 _5794 _5792) = (term44 _5791 _5793 _5794 _5792).
Proof. exact (MK_COMB (@lem264259 _5791 _5793 _5792 _5794) (@lem264262 _5794 _5792)). Qed.
Lemma lem264264 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term732 _5791 _5793 _5794 _5792) = (term44 _5791 _5793 _5794 _5792).
Proof. exact (TRANS (@lem264254 _5791 _5793 _5794 _5792) (@lem264263 _5791 _5793 _5794 _5792)). Qed.
Lemma lem264265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem264266 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term737 _5791 _5793 _5794 _5792) = (term63 _5791 _5793 _5794 _5792).
Proof. exact (MK_COMB (@lem264265) (@lem264264 _5791 _5793 _5794 _5792)). Qed.
Lemma lem264267 (_5791 : nat) (_5792 : nat) (_5793 : nat) : ((Nat.div _5791 _5792) = _5793) = ((Nat.div _5791 _5792) = _5793).
Proof. exact (eq_refl ((Nat.div _5791 _5792) = _5793)). Qed.
Lemma lem264268 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) : (term731 _5794 _5791 _5792 _5793) = (term738 _5794 _5791 _5792 _5793).
Proof. exact (MK_COMB (@lem264266 _5791 _5793 _5794 _5792) (@lem264267 _5791 _5792 _5793)). Qed.
Lemma lem264269 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) : (term730 _5791 _5793 _5794 _5792) = (term738 _5794 _5791 _5792 _5793).
Proof. exact (TRANS (@lem264251 _5794 _5791 _5792 _5793) (@lem264268 _5794 _5791 _5792 _5793)). Qed.
Lemma lem264271 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term739 q r n.
Proof. exact (conj (@lem264135 q n r) (@lem264142 m n P q r h1)). Qed.
Lemma lem264273 (_5794 : nat) (_5791 : nat) (_5792 : nat) (_5793 : nat) (h1 : term529) : term738 _5794 _5791 _5792 _5793.
Proof. exact (EQ_MP (@lem264269 _5794 _5791 _5792 _5793) (@lem264248 _5791 _5793 _5794 _5792 h1)). Qed.
Lemma lem264274 (r : nat) (n : nat) (q : nat) (h1 : term529) : term740 r n q.
Proof. exact (@lem264273 r (term39 q n r) n q h1). Qed.
Lemma lem264277 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : (term741 q r n) = q.
Proof. exact (@lem264274 r n q h1 (@lem264271 m n P q r h2)). Qed.
Lemma lem264278 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : term742 r n q.
Proof. exact (fun h0 : term743 r n q => @lem264277 m n P q r h1 h2). Qed.
Lemma lem264280 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264281 (r : nat) (n : nat) (q : nat) : (term742 r n q) = ((term741 q r n) = q).
Proof. exact (@lem264280 ((term741 q r n) = q)). Qed.
Lemma lem264282 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : (term741 q r n) = q.
Proof. exact (EQ_MP (@lem264281 r n q) (@lem264278 m n P q r h1 h2)). Qed.
Lemma lem264284 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem264285 (q : nat) (n : nat) (r : nat) : (term39 q n r) = (term39 q n r).
Proof. exact (@lem264284 (term39 q n r)). Qed.
Lemma lem264286 (q : nat) (n : nat) (r : nat) : term717 q n r.
Proof. exact (fun h0 : term718 q n r => @lem264285 q n r). Qed.
Lemma lem264288 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264289 (q : nat) (n : nat) (r : nat) : (term717 q n r) = ((term39 q n r) = (term39 q n r)).
Proof. exact (@lem264288 ((term39 q n r) = (term39 q n r))). Qed.
Lemma lem264290 (q : nat) (n : nat) (r : nat) : (term39 q n r) = (term39 q n r).
Proof. exact (EQ_MP (@lem264289 q n r) (@lem264286 q n r)). Qed.
Lemma lem264292 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : Peano.lt r n.
Proof. exact (proj2 (@lem263642 m n P q r h1)). Qed.
Lemma lem264293 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term719 r n.
Proof. exact (fun h0 : term708 r n => @lem264292 m n P q r h1). Qed.
Lemma lem264295 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264296 (r : nat) (n : nat) : (term719 r n) = (Peano.lt r n).
Proof. exact (@lem264295 (Peano.lt r n)). Qed.
Lemma lem264297 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : Peano.lt r n.
Proof. exact (EQ_MP (@lem264296 r n) (@lem264293 m n P q r h1)). Qed.
Lemma lem264303 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264304 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term709 _5793 _5791 _5792 _5794) = (term744 _5793 _5791 _5792 _5794).
Proof. exact (@lem264303 (term708 _5794 _5792) (term707 _5791 _5793 _5792 _5794) ((Nat.modulo _5791 _5792) = _5794)). Qed.
Lemma lem264318 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264319 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term745 _5793 _5791 _5792 _5794) = (term746 _5791 _5793 _5792 _5794).
Proof. exact (@lem264318 ((Nat.modulo _5791 _5792) = _5794) (term707 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264329 (_5794 : nat) (_5792 : nat) : (term723 _5794 _5792) = (term723 _5794 _5792).
Proof. exact (eq_refl (term723 _5794 _5792)). Qed.
Lemma lem264330 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term744 _5793 _5791 _5792 _5794) = (term747 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264329 _5794 _5792) (@lem264319 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264334 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264335 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term747 _5791 _5793 _5792 _5794) = (term748 _5791 _5793 _5792 _5794).
Proof. exact (@lem264334 ((Nat.modulo _5791 _5792) = _5794) (term708 _5794 _5792) (term707 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264355 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term744 _5793 _5791 _5792 _5794) = (term748 _5791 _5793 _5792 _5794).
Proof. exact (TRANS (@lem264330 _5791 _5793 _5792 _5794) (@lem264335 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264356 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term709 _5793 _5791 _5792 _5794) = (term748 _5791 _5793 _5792 _5794).
Proof. exact (TRANS (@lem264304 _5793 _5791 _5792 _5794) (@lem264355 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem264358 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term749 _5793 _5791 _5792 _5794) = (term750 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264357) (@lem264356 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264374 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264375 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term552 _5791 _5793 _5794 _5792) = (term728 _5791 _5793 _5792 _5794).
Proof. exact (@lem264374 (term708 _5794 _5792) (term707 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264383 (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term751 _5791 _5792 _5794) = (term751 _5791 _5792 _5794).
Proof. exact (eq_refl (term751 _5791 _5792 _5794)). Qed.
Lemma lem264384 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term752 _5791 _5793 _5794 _5792) = (term748 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264383 _5791 _5792 _5794) (@lem264375 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264395 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : ((term709 _5793 _5791 _5792 _5794) = (term752 _5791 _5793 _5794 _5792)) = ((term748 _5791 _5793 _5792 _5794) = (term748 _5791 _5793 _5792 _5794)).
Proof. exact (MK_COMB (@lem264358 _5791 _5793 _5792 _5794) (@lem264384 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264397 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem264398 (x : Prop) : (x = x) = True.
Proof. exact (@lem264397 Prop x). Qed.
Lemma lem264399 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : ((term748 _5791 _5793 _5792 _5794) = (term748 _5791 _5793 _5792 _5794)) = True.
Proof. exact (@lem264398 (term748 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264400 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : ((term709 _5793 _5791 _5792 _5794) = (term752 _5791 _5793 _5794 _5792)) = True.
Proof. exact (TRANS (@lem264395 _5791 _5793 _5792 _5794) (@lem264399 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264401 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : True = ((term709 _5793 _5791 _5792 _5794) = (term752 _5791 _5793 _5794 _5792)).
Proof. exact (SYM (@lem264400 _5791 _5793 _5794 _5792)). Qed.
Lemma lem264402 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term709 _5793 _5791 _5792 _5794) = (term752 _5791 _5793 _5794 _5792).
Proof. exact (EQ_MP (@lem264401 _5791 _5793 _5794 _5792) (@lem0)). Qed.
Lemma lem264403 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) (h1 : term529) : term752 _5791 _5793 _5794 _5792.
Proof. exact (EQ_MP (@lem264402 _5791 _5793 _5794 _5792) (@lem264027 _5793 _5791 _5792 _5794 h1)). Qed.
Lemma lem264405 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem264406 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term752 _5791 _5793 _5794 _5792) = (term753 _5793 _5791 _5792 _5794).
Proof. exact (@lem264405 (term552 _5791 _5793 _5794 _5792) ((Nat.modulo _5791 _5792) = _5794)). Qed.
Lemma lem264408 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem264409 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term732 _5791 _5793 _5794 _5792) = (term733 _5791 _5793 _5794 _5792).
Proof. exact (@lem264408 (term707 _5791 _5793 _5792 _5794) (term708 _5794 _5792)). Qed.
Lemma lem264411 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264412 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term734 _5791 _5793 _5792 _5794) = (_5791 = (term39 _5793 _5792 _5794)).
Proof. exact (@lem264411 (_5791 = (term39 _5793 _5792 _5794))). Qed.
Lemma lem264413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem264414 (_5791 : nat) (_5793 : nat) (_5792 : nat) (_5794 : nat) : (term735 _5791 _5793 _5792 _5794) = (term41 _5791 _5793 _5792 _5794).
Proof. exact (MK_COMB (@lem264413) (@lem264412 _5791 _5793 _5792 _5794)). Qed.
Lemma lem264416 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264417 (_5794 : nat) (_5792 : nat) : (term736 _5794 _5792) = (Peano.lt _5794 _5792).
Proof. exact (@lem264416 (Peano.lt _5794 _5792)). Qed.
Lemma lem264418 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term733 _5791 _5793 _5794 _5792) = (term44 _5791 _5793 _5794 _5792).
Proof. exact (MK_COMB (@lem264414 _5791 _5793 _5792 _5794) (@lem264417 _5794 _5792)). Qed.
Lemma lem264419 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term732 _5791 _5793 _5794 _5792) = (term44 _5791 _5793 _5794 _5792).
Proof. exact (TRANS (@lem264409 _5791 _5793 _5794 _5792) (@lem264418 _5791 _5793 _5794 _5792)). Qed.
Lemma lem264420 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem264421 (_5791 : nat) (_5793 : nat) (_5794 : nat) (_5792 : nat) : (term737 _5791 _5793 _5794 _5792) = (term63 _5791 _5793 _5794 _5792).
Proof. exact (MK_COMB (@lem264420) (@lem264419 _5791 _5793 _5794 _5792)). Qed.
Lemma lem264422 (_5791 : nat) (_5792 : nat) (_5794 : nat) : ((Nat.modulo _5791 _5792) = _5794) = ((Nat.modulo _5791 _5792) = _5794).
Proof. exact (eq_refl ((Nat.modulo _5791 _5792) = _5794)). Qed.
Lemma lem264423 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term753 _5793 _5791 _5792 _5794) = (term754 _5793 _5791 _5792 _5794).
Proof. exact (MK_COMB (@lem264421 _5791 _5793 _5794 _5792) (@lem264422 _5791 _5792 _5794)). Qed.
Lemma lem264424 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) : (term752 _5791 _5793 _5794 _5792) = (term754 _5793 _5791 _5792 _5794).
Proof. exact (TRANS (@lem264406 _5793 _5791 _5792 _5794) (@lem264423 _5793 _5791 _5792 _5794)). Qed.
Lemma lem264426 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term739 q r n.
Proof. exact (conj (@lem264290 q n r) (@lem264297 m n P q r h1)). Qed.
Lemma lem264428 (_5793 : nat) (_5791 : nat) (_5792 : nat) (_5794 : nat) (h1 : term529) : term754 _5793 _5791 _5792 _5794.
Proof. exact (EQ_MP (@lem264424 _5793 _5791 _5792 _5794) (@lem264403 _5791 _5793 _5794 _5792 h1)). Qed.
Lemma lem264429 (q : nat) (n : nat) (r : nat) (h1 : term529) : term755 q n r.
Proof. exact (@lem264428 q (term39 q n r) n r h1). Qed.
Lemma lem264432 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : (term756 q r n) = r.
Proof. exact (@lem264429 q n r h1 (@lem264426 m n P q r h2)). Qed.
Lemma lem264433 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : term757 q n r.
Proof. exact (fun h0 : term758 q n r => @lem264432 m n P q r h1 h2). Qed.
Lemma lem264435 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264436 (q : nat) (n : nat) (r : nat) : (term757 q n r) = ((term756 q r n) = r).
Proof. exact (@lem264435 ((term756 q r n) = r)). Qed.
Lemma lem264437 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : (term756 q r n) = r.
Proof. exact (EQ_MP (@lem264436 q n r) (@lem264433 m n P q r h1 h2)). Qed.
Lemma lem264439 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term715 P q r n.
Proof. exact (EQ_MP (@lem263970 m n P q r h1) (@lem263844 m n P q r h1)). Qed.
Lemma lem264440 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term759 P q r n.
Proof. exact (fun h0 : term760 P q r n => @lem264439 m n P q r h1). Qed.
Lemma lem264442 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264443 (P : type1605) (q : nat) (r : nat) (n : nat) : (term759 P q r n) = (term715 P q r n).
Proof. exact (@lem264442 (term715 P q r n)). Qed.
Lemma lem264444 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term715 P q r n.
Proof. exact (EQ_MP (@lem264443 P q r n) (@lem264440 m n P q r h1)). Qed.
Lemma lem264462 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264463 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term402 _5823 _5824 P _5821 _5822) = (term429 _5823 _5824 P _5821 _5822).
Proof. exact (@lem264462 (P _5823 _5824) (term384 _5822 _5824) (term382 P _5821 _5822)). Qed.
Lemma lem264477 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264478 (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term430 _5824 P _5821 _5822) = (term431 P _5821 _5822 _5824).
Proof. exact (@lem264477 (term382 P _5821 _5822) (term384 _5822 _5824)). Qed.
Lemma lem264486 (P : type1605) (_5823 : nat) (_5824 : nat) : (term432 P _5823 _5824) = (term432 P _5823 _5824).
Proof. exact (eq_refl (term432 P _5823 _5824)). Qed.
Lemma lem264487 (_5823 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term429 _5823 _5824 P _5821 _5822) = (term433 _5823 P _5821 _5822 _5824).
Proof. exact (MK_COMB (@lem264486 P _5823 _5824) (@lem264478 P _5821 _5822 _5824)). Qed.
Lemma lem264498 (_5823 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term402 _5823 _5824 P _5821 _5822) = (term433 _5823 P _5821 _5822 _5824).
Proof. exact (TRANS (@lem264463 _5823 _5824 P _5821 _5822) (@lem264487 _5823 P _5821 _5822 _5824)). Qed.
Lemma lem264499 (_5821 : nat) (_5823 : nat) : (term434 _5821 _5823) = (term434 _5821 _5823).
Proof. exact (eq_refl (term434 _5821 _5823)). Qed.
Lemma lem264500 (_5823 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term404 _5823 _5824 P _5821 _5822) = (term435 _5823 P _5821 _5822 _5824).
Proof. exact (MK_COMB (@lem264499 _5821 _5823) (@lem264498 _5823 P _5821 _5822 _5824)). Qed.
Lemma lem264504 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264505 (_5823 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term435 _5823 P _5821 _5822 _5824) = (term436 _5823 P _5821 _5822 _5824).
Proof. exact (@lem264504 (P _5823 _5824) (term384 _5821 _5823) (term431 P _5821 _5822 _5824)). Qed.
Lemma lem264519 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264520 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term437 _5823 P _5821 _5822 _5824) = (term438 P _5821 _5823 _5822 _5824).
Proof. exact (@lem264519 (term382 P _5821 _5822) (term384 _5821 _5823) (term384 _5822 _5824)). Qed.
Lemma lem264540 (P : type1605) (_5823 : nat) (_5824 : nat) : (term432 P _5823 _5824) = (term432 P _5823 _5824).
Proof. exact (eq_refl (term432 P _5823 _5824)). Qed.
Lemma lem264541 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term436 _5823 P _5821 _5822 _5824) = (term439 P _5821 _5823 _5822 _5824).
Proof. exact (MK_COMB (@lem264540 P _5823 _5824) (@lem264520 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264552 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term435 _5823 P _5821 _5822 _5824) = (term439 P _5821 _5823 _5822 _5824).
Proof. exact (TRANS (@lem264505 _5823 P _5821 _5822 _5824) (@lem264541 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264553 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term404 _5823 _5824 P _5821 _5822) = (term439 P _5821 _5823 _5822 _5824).
Proof. exact (TRANS (@lem264500 _5823 P _5821 _5822 _5824) (@lem264552 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem264555 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term440 _5823 _5824 P _5821 _5822) = (term441 P _5821 _5823 _5822 _5824).
Proof. exact (MK_COMB (@lem264554) (@lem264553 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264581 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264582 (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term430 _5824 P _5821 _5822) = (term431 P _5821 _5822 _5824).
Proof. exact (@lem264581 (term382 P _5821 _5822) (term384 _5822 _5824)). Qed.
Lemma lem264590 (_5821 : nat) (_5823 : nat) : (term434 _5821 _5823) = (term434 _5821 _5823).
Proof. exact (eq_refl (term434 _5821 _5823)). Qed.
Lemma lem264591 (_5823 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) (_5824 : nat) : (term442 _5823 _5824 P _5821 _5822) = (term437 _5823 P _5821 _5822 _5824).
Proof. exact (MK_COMB (@lem264590 _5821 _5823) (@lem264582 P _5821 _5822 _5824)). Qed.
Lemma lem264595 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264596 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term437 _5823 P _5821 _5822 _5824) = (term438 P _5821 _5823 _5822 _5824).
Proof. exact (@lem264595 (term382 P _5821 _5822) (term384 _5821 _5823) (term384 _5822 _5824)). Qed.
Lemma lem264616 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term442 _5823 _5824 P _5821 _5822) = (term438 P _5821 _5823 _5822 _5824).
Proof. exact (TRANS (@lem264591 _5823 P _5821 _5822 _5824) (@lem264596 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264617 (P : type1605) (_5823 : nat) (_5824 : nat) : (term432 P _5823 _5824) = (term432 P _5823 _5824).
Proof. exact (eq_refl (term432 P _5823 _5824)). Qed.
Lemma lem264618 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : (term443 _5823 _5824 P _5821 _5822) = (term439 P _5821 _5823 _5822 _5824).
Proof. exact (MK_COMB (@lem264617 P _5823 _5824) (@lem264616 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264629 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : ((term404 _5823 _5824 P _5821 _5822) = (term443 _5823 _5824 P _5821 _5822)) = ((term439 P _5821 _5823 _5822 _5824) = (term439 P _5821 _5823 _5822 _5824)).
Proof. exact (MK_COMB (@lem264555 P _5821 _5823 _5822 _5824) (@lem264618 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264631 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem264632 (x : Prop) : (x = x) = True.
Proof. exact (@lem264631 Prop x). Qed.
Lemma lem264633 (P : type1605) (_5821 : nat) (_5823 : nat) (_5822 : nat) (_5824 : nat) : ((term439 P _5821 _5823 _5822 _5824) = (term439 P _5821 _5823 _5822 _5824)) = True.
Proof. exact (@lem264632 (term439 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264634 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : ((term404 _5823 _5824 P _5821 _5822) = (term443 _5823 _5824 P _5821 _5822)) = True.
Proof. exact (TRANS (@lem264629 P _5821 _5823 _5822 _5824) (@lem264633 P _5821 _5823 _5822 _5824)). Qed.
Lemma lem264635 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : True = ((term404 _5823 _5824 P _5821 _5822) = (term443 _5823 _5824 P _5821 _5822)).
Proof. exact (SYM (@lem264634 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264636 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term404 _5823 _5824 P _5821 _5822) = (term443 _5823 _5824 P _5821 _5822).
Proof. exact (EQ_MP (@lem264635 _5823 _5824 P _5821 _5822) (@lem0)). Qed.
Lemma lem264637 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : term443 _5823 _5824 P _5821 _5822.
Proof. exact (EQ_MP (@lem264636 _5823 _5824 P _5821 _5822) (@lem264046 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264639 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem264640 (_5821 : nat) (_5822 : nat) (P : type1605) (_5823 : nat) (_5824 : nat) : (term443 _5823 _5824 P _5821 _5822) = (term444 _5821 _5822 P _5823 _5824).
Proof. exact (@lem264639 (term442 _5823 _5824 P _5821 _5822) (P _5823 _5824)). Qed.
Lemma lem264642 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem264643 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term447 _5823 _5824 P _5821 _5822) = (term448 _5823 _5824 P _5821 _5822).
Proof. exact (@lem264642 (term384 _5821 _5823) (term430 _5824 P _5821 _5822)). Qed.
Lemma lem264645 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264646 (_5821 : nat) (_5823 : nat) : (term449 _5821 _5823) = (_5821 = _5823).
Proof. exact (@lem264645 (_5821 = _5823)). Qed.
Lemma lem264647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem264648 (_5821 : nat) (_5823 : nat) : (term450 _5821 _5823) = (term451 _5821 _5823).
Proof. exact (MK_COMB (@lem264647) (@lem264646 _5821 _5823)). Qed.
Lemma lem264650 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem264651 (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term452 _5824 P _5821 _5822) = (term453 _5824 P _5821 _5822).
Proof. exact (@lem264650 (term384 _5822 _5824) (term382 P _5821 _5822)). Qed.
Lemma lem264653 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264654 (_5822 : nat) (_5824 : nat) : (term449 _5822 _5824) = (_5822 = _5824).
Proof. exact (@lem264653 (_5822 = _5824)). Qed.
Lemma lem264655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem264656 (_5822 : nat) (_5824 : nat) : (term450 _5822 _5824) = (term451 _5822 _5824).
Proof. exact (MK_COMB (@lem264655) (@lem264654 _5822 _5824)). Qed.
Lemma lem264658 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264659 (P : type1605) (_5821 : nat) (_5822 : nat) : (term454 P _5821 _5822) = (P _5821 _5822).
Proof. exact (@lem264658 (P _5821 _5822)). Qed.
Lemma lem264660 (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term453 _5824 P _5821 _5822) = (term455 _5824 P _5821 _5822).
Proof. exact (MK_COMB (@lem264656 _5822 _5824) (@lem264659 P _5821 _5822)). Qed.
Lemma lem264661 (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term452 _5824 P _5821 _5822) = (term455 _5824 P _5821 _5822).
Proof. exact (TRANS (@lem264651 _5824 P _5821 _5822) (@lem264660 _5824 P _5821 _5822)). Qed.
Lemma lem264662 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term448 _5823 _5824 P _5821 _5822) = (term456 _5823 _5824 P _5821 _5822).
Proof. exact (MK_COMB (@lem264648 _5821 _5823) (@lem264661 _5824 P _5821 _5822)). Qed.
Lemma lem264663 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term447 _5823 _5824 P _5821 _5822) = (term456 _5823 _5824 P _5821 _5822).
Proof. exact (TRANS (@lem264643 _5823 _5824 P _5821 _5822) (@lem264662 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem264665 (_5823 : nat) (_5824 : nat) (P : type1605) (_5821 : nat) (_5822 : nat) : (term457 _5823 _5824 P _5821 _5822) = (term458 _5823 _5824 P _5821 _5822).
Proof. exact (MK_COMB (@lem264664) (@lem264663 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264666 (P : type1605) (_5823 : nat) (_5824 : nat) : (P _5823 _5824) = (P _5823 _5824).
Proof. exact (eq_refl (P _5823 _5824)). Qed.
Lemma lem264667 (_5821 : nat) (_5822 : nat) (P : type1605) (_5823 : nat) (_5824 : nat) : (term444 _5821 _5822 P _5823 _5824) = (term459 _5821 _5822 P _5823 _5824).
Proof. exact (MK_COMB (@lem264665 _5823 _5824 P _5821 _5822) (@lem264666 P _5823 _5824)). Qed.
Lemma lem264668 (_5821 : nat) (_5822 : nat) (P : type1605) (_5823 : nat) (_5824 : nat) : (term443 _5823 _5824 P _5821 _5822) = (term459 _5821 _5822 P _5823 _5824).
Proof. exact (TRANS (@lem264640 _5821 _5822 P _5823 _5824) (@lem264667 _5821 _5822 P _5823 _5824)). Qed.
Lemma lem264670 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : term761 P q r n.
Proof. exact (conj (@lem264437 m n P q r h1 h2) (@lem264444 m n P q r h2)). Qed.
Lemma lem264671 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : term762 P q r n.
Proof. exact (conj (@lem264282 m n P q r h1 h2) (@lem264670 m n P q r h1 h2)). Qed.
Lemma lem264673 (_5821 : nat) (_5822 : nat) (P : type1605) (_5823 : nat) (_5824 : nat) : term459 _5821 _5822 P _5823 _5824.
Proof. exact (EQ_MP (@lem264668 _5821 _5822 P _5823 _5824) (@lem264637 _5823 _5824 P _5821 _5822)). Qed.
Lemma lem264674 (n : nat) (P : type1605) (q : nat) (r : nat) : term763 n P q r.
Proof. exact (@lem264673 (term741 q r n) (term756 q r n) P q r). Qed.
Lemma lem264677 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : P q r.
Proof. exact (@lem264674 n P q r (@lem264671 m n P q r h1 h2)). Qed.
Lemma lem264678 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : term764 P q r.
Proof. exact (fun h0 : term382 P q r => @lem264677 m n P q r h1 h2). Qed.
Lemma lem264680 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264681 (P : type1605) (q : nat) (r : nat) : (term764 P q r) = (P q r).
Proof. exact (@lem264680 (P q r)). Qed.
Lemma lem264682 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : P q r.
Proof. exact (EQ_MP (@lem264681 P q r) (@lem264678 m n P q r h1 h2)). Qed.
Lemma lem264685 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem264687 (P : type1605) (q : nat) (r : nat) : (term382 P q r) = (term765 P q r).
Proof. exact (@lem264685 (P q r)). Qed.
Lemma lem264690 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term611 m n P q r) : term765 P q r.
Proof. exact (EQ_MP (@lem264687 P q r) (@lem263985 m n P q r h1)). Qed.
Lemma lem264693 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : False.
Proof. exact (@lem264690 m n P q r h2 (@lem264682 m n P q r h1 h2)). Qed.
Lemma lem264694 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : term466.
Proof. exact (fun h0 : ~ False => @lem264693 m n P q r h1 h2). Qed.
Lemma lem264696 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264697 : term466 = False.
Proof. exact (@lem264696 False). Qed.
Lemma lem264800 (_5801 : nat) (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : _5801 = (term502 _5801 n).
Proof. exact (EQ_MP (@lem263824 _5801 n) (@lem263823 _5801 q r m n P h1)). Qed.
Lemma lem264801 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : m = (term502 m n).
Proof. exact (@lem264800 m q r m n P h1). Qed.
Lemma lem264802 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term766 m n.
Proof. exact (fun h0 : term767 m n => @lem264801 q r m n P h1). Qed.
Lemma lem264804 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264805 (m : nat) (n : nat) : (term766 m n) = (m = (term502 m n)).
Proof. exact (@lem264804 (m = (term502 m n))). Qed.
Lemma lem264806 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : m = (term502 m n).
Proof. exact (EQ_MP (@lem264805 m n) (@lem264802 q r m n P h1)). Qed.
Lemma lem264808 (_5802 : nat) (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term506 _5802 n.
Proof. exact (EQ_MP (@lem263827 _5802 n) (@lem263826 _5802 q r m n P h1)). Qed.
Lemma lem264809 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term506 m n.
Proof. exact (@lem264808 m q r m n P h1). Qed.
Lemma lem264810 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term768 m n.
Proof. exact (fun h0 : term769 m n => @lem264809 q r m n P h1). Qed.
Lemma lem264812 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264813 (m : nat) (n : nat) : (term768 m n) = (term506 m n).
Proof. exact (@lem264812 (term506 m n)). Qed.
Lemma lem264814 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term506 m n.
Proof. exact (EQ_MP (@lem264813 m n) (@lem264810 q r m n P h1)). Qed.
Lemma lem264820 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264821 (m : nat) (n : nat) (P : type1605) (_5803 : nat) (_5804 : nat) : (term711 m n P _5803 _5804) = (term770 m n P _5803 _5804).
Proof. exact (@lem264820 (term708 _5804 n) (term707 m _5803 n _5804) (P _5803 _5804)). Qed.
Lemma lem264835 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264836 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term771 m n P _5803 _5804) = (term772 P m _5803 n _5804).
Proof. exact (@lem264835 (P _5803 _5804) (term707 m _5803 n _5804)). Qed.
Lemma lem264844 (_5804 : nat) (n : nat) : (term723 _5804 n) = (term723 _5804 n).
Proof. exact (eq_refl (term723 _5804 n)). Qed.
Lemma lem264845 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term770 m n P _5803 _5804) = (term773 P m _5803 n _5804).
Proof. exact (MK_COMB (@lem264844 _5804 n) (@lem264836 P m _5803 n _5804)). Qed.
Lemma lem264849 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem264850 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term773 P m _5803 n _5804) = (term774 P m _5803 n _5804).
Proof. exact (@lem264849 (P _5803 _5804) (term708 _5804 n) (term707 m _5803 n _5804)). Qed.
Lemma lem264868 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term770 m n P _5803 _5804) = (term774 P m _5803 n _5804).
Proof. exact (TRANS (@lem264845 P m _5803 n _5804) (@lem264850 P m _5803 n _5804)). Qed.
Lemma lem264869 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term711 m n P _5803 _5804) = (term774 P m _5803 n _5804).
Proof. exact (TRANS (@lem264821 m n P _5803 _5804) (@lem264868 P m _5803 n _5804)). Qed.
Lemma lem264870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem264871 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term775 m n P _5803 _5804) = (term776 P m _5803 n _5804).
Proof. exact (MK_COMB (@lem264870) (@lem264869 P m _5803 n _5804)). Qed.
Lemma lem264885 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem264886 (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term552 m _5803 _5804 n) = (term728 m _5803 n _5804).
Proof. exact (@lem264885 (term708 _5804 n) (term707 m _5803 n _5804)). Qed.
Lemma lem264894 (P : type1605) (_5803 : nat) (_5804 : nat) : (term432 P _5803 _5804) = (term432 P _5803 _5804).
Proof. exact (eq_refl (term432 P _5803 _5804)). Qed.
Lemma lem264895 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term777 P m _5803 _5804 n) = (term774 P m _5803 n _5804).
Proof. exact (MK_COMB (@lem264894 P _5803 _5804) (@lem264886 m _5803 n _5804)). Qed.
Lemma lem264906 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : ((term711 m n P _5803 _5804) = (term777 P m _5803 _5804 n)) = ((term774 P m _5803 n _5804) = (term774 P m _5803 n _5804)).
Proof. exact (MK_COMB (@lem264871 P m _5803 n _5804) (@lem264895 P m _5803 n _5804)). Qed.
Lemma lem264908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem264909 (x : Prop) : (x = x) = True.
Proof. exact (@lem264908 Prop x). Qed.
Lemma lem264910 (P : type1605) (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : ((term774 P m _5803 n _5804) = (term774 P m _5803 n _5804)) = True.
Proof. exact (@lem264909 (term774 P m _5803 n _5804)). Qed.
Lemma lem264911 (P : type1605) (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : ((term711 m n P _5803 _5804) = (term777 P m _5803 _5804 n)) = True.
Proof. exact (TRANS (@lem264906 P m _5803 n _5804) (@lem264910 P m _5803 n _5804)). Qed.
Lemma lem264912 (P : type1605) (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : True = ((term711 m n P _5803 _5804) = (term777 P m _5803 _5804 n)).
Proof. exact (SYM (@lem264911 P m _5803 _5804 n)). Qed.
Lemma lem264913 (P : type1605) (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : (term711 m n P _5803 _5804) = (term777 P m _5803 _5804 n).
Proof. exact (EQ_MP (@lem264912 P m _5803 _5804 n) (@lem0)). Qed.
Lemma lem264914 (_5803 : nat) (_5804 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term777 P m _5803 _5804 n.
Proof. exact (EQ_MP (@lem264913 P m _5803 _5804 n) (@lem263892 _5803 _5804 m n P h1)). Qed.
Lemma lem264916 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem264917 (m : nat) (n : nat) (P : type1605) (_5803 : nat) (_5804 : nat) : (term777 P m _5803 _5804 n) = (term778 m n P _5803 _5804).
Proof. exact (@lem264916 (term552 m _5803 _5804 n) (P _5803 _5804)). Qed.
Lemma lem264919 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem264920 (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : (term732 m _5803 _5804 n) = (term733 m _5803 _5804 n).
Proof. exact (@lem264919 (term707 m _5803 n _5804) (term708 _5804 n)). Qed.
Lemma lem264922 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264923 (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term734 m _5803 n _5804) = (m = (term39 _5803 n _5804)).
Proof. exact (@lem264922 (m = (term39 _5803 n _5804))). Qed.
Lemma lem264924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem264925 (m : nat) (_5803 : nat) (n : nat) (_5804 : nat) : (term735 m _5803 n _5804) = (term41 m _5803 n _5804).
Proof. exact (MK_COMB (@lem264924) (@lem264923 m _5803 n _5804)). Qed.
Lemma lem264927 (a : Prop) : (term413 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem264928 (_5804 : nat) (n : nat) : (term736 _5804 n) = (Peano.lt _5804 n).
Proof. exact (@lem264927 (Peano.lt _5804 n)). Qed.
Lemma lem264929 (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : (term733 m _5803 _5804 n) = (term44 m _5803 _5804 n).
Proof. exact (MK_COMB (@lem264925 m _5803 n _5804) (@lem264928 _5804 n)). Qed.
Lemma lem264930 (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : (term732 m _5803 _5804 n) = (term44 m _5803 _5804 n).
Proof. exact (TRANS (@lem264920 m _5803 _5804 n) (@lem264929 m _5803 _5804 n)). Qed.
Lemma lem264931 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem264932 (m : nat) (_5803 : nat) (_5804 : nat) (n : nat) : (term737 m _5803 _5804 n) = (term63 m _5803 _5804 n).
Proof. exact (MK_COMB (@lem264931) (@lem264930 m _5803 _5804 n)). Qed.
Lemma lem264933 (P : type1605) (_5803 : nat) (_5804 : nat) : (P _5803 _5804) = (P _5803 _5804).
Proof. exact (eq_refl (P _5803 _5804)). Qed.
Lemma lem264934 (m : nat) (n : nat) (P : type1605) (_5803 : nat) (_5804 : nat) : (term778 m n P _5803 _5804) = (term64 m n P _5803 _5804).
Proof. exact (MK_COMB (@lem264932 m _5803 _5804 n) (@lem264933 P _5803 _5804)). Qed.
Lemma lem264935 (m : nat) (n : nat) (P : type1605) (_5803 : nat) (_5804 : nat) : (term777 P m _5803 _5804 n) = (term64 m n P _5803 _5804).
Proof. exact (TRANS (@lem264917 m n P _5803 _5804) (@lem264934 m n P _5803 _5804)). Qed.
Lemma lem264937 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term672 q r m n P) : term13 m n.
Proof. exact (conj (@lem264806 q r m n P h1) (@lem264814 q r m n P h1)). Qed.
Lemma lem264939 (_5803 : nat) (_5804 : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term64 m n P _5803 _5804.
Proof. exact (EQ_MP (@lem264935 m n P _5803 _5804) (@lem264914 _5803 _5804 m n P h1)). Qed.
Lemma lem264940 (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term779 P m n.
Proof. exact (@lem264939 (Nat.div m n) (Nat.modulo m n) m n P h1). Qed.
Lemma lem264943 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) (h2 : term672 q r m n P) : term25 P m n.
Proof. exact (@lem264940 m n P h1 (@lem264937 q r m n P h2)). Qed.
Lemma lem264944 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) (h2 : term672 q r m n P) : term780 P m n.
Proof. exact (fun h0 : term710 P m n => @lem264943 q r m n P h1 h2). Qed.
Lemma lem264946 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264947 (P : type1605) (m : nat) (n : nat) : (term780 P m n) = (term25 P m n).
Proof. exact (@lem264946 (term25 P m n)). Qed.
Lemma lem264948 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) (h2 : term672 q r m n P) : term25 P m n.
Proof. exact (EQ_MP (@lem264947 P m n) (@lem264944 q r m n P h1 h2)). Qed.
Lemma lem264951 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem264953 (P : type1605) (m : nat) (n : nat) : (term710 P m n) = (term781 P m n).
Proof. exact (@lem264951 (term25 P m n)). Qed.
Lemma lem264956 (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) : term781 P m n.
Proof. exact (EQ_MP (@lem264953 P m n) (@lem263880 m n P h1)). Qed.
Lemma lem264959 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) (h2 : term672 q r m n P) : False.
Proof. exact (@lem264956 m n P h1 (@lem264948 q r m n P h1 h2)). Qed.
Lemma lem264960 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) (h2 : term672 q r m n P) : term466.
Proof. exact (fun h0 : ~ False => @lem264959 q r m n P h1 h2). Qed.
Lemma lem264962 (p : Prop) : (term407 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem264963 : term466 = False.
Proof. exact (@lem264962 False). Qed.
Lemma lem264964 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term579 m n P) (h2 : term672 q r m n P) : False.
Proof. exact (EQ_MP (@lem264963) (@lem264960 q r m n P h1 h2)). Qed.
Lemma lem264965 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) (h1 : term529) (h2 : term611 m n P q r) : False.
Proof. exact (EQ_MP (@lem264697) (@lem264694 m n P q r h1 h2)). Qed.
Lemma lem264966 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term529) (h2 : term672 q r m n P) : False.
Proof. exact (or_elim (@lem263633 q r m n P h2) (fun h0 : term611 m n P q r => @lem264965 m n P q r h1 h0) (fun h0 : term579 m n P => @lem264964 q r m n P h0 h2)). Qed.
Lemma lem264967 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term529) (h2 : term672 q r m n P) : (term672 q r m n P) = False.
Proof. exact (prop_ext (fun h3 : term672 q r m n P => @lem264966 q r m n P h1 h2) (fun h3 : False => @lem263632 q r m n P h2)). Qed.
Lemma lem264968 (q : nat) (r : nat) (m : nat) (n : nat) (P : type1605) (h1 : term529) (h2 : term672 q r m n P) : False.
Proof. exact (EQ_MP (@lem264967 q r m n P h1 h2) (@lem263632 q r m n P h2)). Qed.
Lemma lem264969 (q : nat) (m : nat) (n : nat) (P : type1605) (h1 : term529) (h2 : term675 q m n P) : False.
Proof. exact (ex_elim (@lem263419 q m n P h2) (fun r : nat => fun h0 : term674 q m n P r => @lem264968 q r m n P h1 h0)). Qed.
Lemma lem264970 (m : nat) (n : nat) (P : type1605) (h1 : term529) (h2 : term524 m n P) : False.
Proof. exact (ex_elim (@lem263324 m n P h2) (fun q : nat => fun h0 : term676 m n P q => @lem264969 q m n P h1 h0)). Qed.
Lemma lem264971 (m : nat) (n : nat) (P : type1605) (h1 : term524 m n P) : term527.
Proof. exact (fun h0 : term529 => @lem264970 m n P h0 h1). Qed.
Lemma lem264972 : term527 = term528.
Proof. exact (@lem69 term529). Qed.
Lemma lem264973 (m : nat) (n : nat) (P : type1605) (h1 : term524 m n P) : term528.
Proof. exact (EQ_MP (@lem264972) (@lem264971 m n P h1)). Qed.
Lemma lem264974 (m : nat) (n : nat) (P : type1605) : term530 m n P.
Proof. exact (fun h0 : term524 m n P => @lem264973 m n P h0). Qed.
Lemma lem264979 (n : nat) (P : type1605) : term534 n P.
Proof. exact (fun m : nat => @lem264974 m n P). Qed.
Lemma lem264984 (P : type1605) : term538 P.
Proof. exact (fun n : nat => @lem264979 n P). Qed.
Lemma lem264989 : term542.
Proof. exact (fun P : type1605 => @lem264984 P). Qed.
Lemma lem264990 : term541.
Proof. exact (EQ_MP (@lem262979) (@lem264989)). Qed.
Lemma lem264991 (P : type1605) : term782 P.
Proof. exact (@lem264990 P). Qed.
Lemma lem264992 (P : type1605) : (term782 P) = (term537 P).
Proof. exact (eq_refl (term782 P)). Qed.
Lemma lem264993 (P : type1605) : term537 P.
Proof. exact (EQ_MP (@lem264992 P) (@lem264991 P)). Qed.
Lemma lem264994 (P : type1605) (n : nat) : term783 P n.
Proof. exact (@lem264993 P n). Qed.
Lemma lem264995 (n : nat) (P : type1605) : (term783 P n) = (term533 n P).
Proof. exact (eq_refl (term783 P n)). Qed.
Lemma lem264996 (n : nat) (P : type1605) : term533 n P.
Proof. exact (EQ_MP (@lem264995 n P) (@lem264994 P n)). Qed.
Lemma lem264997 (n : nat) (P : type1605) (m : nat) : term784 n P m.
Proof. exact (@lem264996 n P m). Qed.
Lemma lem264998 (m : nat) (n : nat) (P : type1605) : (term784 n P m) = (term493 m n P).
Proof. exact (eq_refl (term784 n P m)). Qed.
Lemma lem264999 (m : nat) (n : nat) (P : type1605) : term493 m n P.
Proof. exact (EQ_MP (@lem264998 m n P) (@lem264997 n P m)). Qed.
Lemma lem265001 (m : nat) (n : nat) (P : type1605) : term493 m n P.
Proof. exact (@lem262691 m n P (@lem264999 m n P)). Qed.
Lemma lem265002 (m : nat) (n : nat) (P : type1605) (h1 : term492 m n P) : term527.
Proof. exact (@lem265001 m n P (@lem262676 m n P h1)). Qed.
Lemma lem265003 (m : nat) (n : nat) (P : type1605) (h1 : term492 m n P) : False.
Proof. exact (@lem265002 m n P h1 (@lem169651)). Qed.
Lemma lem265004 (m : nat) (n : nat) (P : type1605) (h1 : term492 m n P) : (term492 m n P) = False.
Proof. exact (prop_ext (fun h2 : term492 m n P => @lem265003 m n P h1) (fun h2 : False => @lem262676 m n P h1)). Qed.
Lemma lem265005 (m : nat) (n : nat) (P : type1605) (h1 : term492 m n P) : False.
Proof. exact (EQ_MP (@lem265004 m n P h1) (@lem262676 m n P h1)). Qed.
Lemma lem265006 (m : nat) (n : nat) (P : type1605) : term491 m n P.
Proof. exact (fun h0 : term492 m n P => @lem265005 m n P h0). Qed.
Lemma lem265007 (m : nat) (n : nat) (P : type1605) : term490 m n P.
Proof. exact (EQ_MP (@lem262675 m n P) (@lem265006 m n P)). Qed.
Lemma lem265008 (m : nat) (P : type1605) (n : nat) (h1 : term12 n) : (term25 P m n) = (term68 m n P).
Proof. exact (@lem265007 m n P (@lem262671 n h1)). Qed.
Lemma lem265009 (m : nat) (P : type1605) (n : nat) (h1 : term12 n) : (term25 P m n) = (term58 m n P).
Proof. exact (EQ_MP (@lem258161 m P n h1) (@lem265008 m P n h1)). Qed.
Lemma lem265010 (m : nat) (P : type1605) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 P m n) = (term58 m n P).
Proof. exact (EQ_MP (@lem258075 m P n h1) (@lem262668 m P n h1)). Qed.
Lemma lem265011 (m : nat) (n : nat) (P : type1605) : (term25 P m n) = (term58 m n P).
Proof. exact (or_elim (@lem257957 n) (fun h0 : n = (NUMERAL 0) => @lem265010 m P n h0) (fun h0 : term12 n => @lem265009 m P n h0)). Qed.
