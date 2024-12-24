Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1012671_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import DE_MORGAN_THM_spec.
Require Import DISJ_ACI_spec.
Require Import LE_ANTISYM_spec.
Require Import LT_EXISTS_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1012003 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1012004 : term1.
Proof. exact (proj2 (@lem1012003)). Qed.
Lemma lem1012005 : term2.
Proof. exact (proj2 (@lem1012004)). Qed.
Lemma lem1012006 (m : nat) : term3 m.
Proof. exact (@lem1012005 m). Qed.
Lemma lem1012007 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1012008 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1012007 m) (@lem1012006 m)). Qed.
Lemma lem1012009 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1012008 m n). Qed.
Lemma lem1012010 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1012012 : term8.
Proof. exact (proj1 (@lem1012004)). Qed.
Lemma lem1012013 (m : nat) : term9 m.
Proof. exact (@lem1012012 m). Qed.
Lemma lem1012014 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1012015 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1012014 m) (@lem1012013 m)). Qed.
Lemma lem1012016 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1012015 m n). Qed.
Lemma lem1012017 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (term7 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1012027 (m : nat) : term13 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem1012028 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1012029 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1012028 m) (@lem1012027 m)). Qed.
Lemma lem1012030 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1012029 m n). Qed.
Lemma lem1012031 (n : nat) (m : nat) : (term15 m n) = ((Peano.lt m n) = (term16 n m)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1012033 (m : nat) : term17 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1012034 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1012035 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1012034 m) (@lem1012033 m)). Qed.
Lemma lem1012036 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1012035 m n). Qed.
Lemma lem1012037 (n : nat) (m : nat) : (term19 m n) = ((term20 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1012041 (m : nat) (n : nat) (h1 : (term21 n m) = (m = n)) : (term21 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem1012042 (m : nat) (n : nat) (h1 : (term21 n m) = (m = n)) : (m = n) = (term21 n m).
Proof. exact (SYM (@lem1012041 m n h1)). Qed.
Lemma lem1012043 (n : nat) (m : nat) (h1 : (m = n) = (term21 n m)) : (m = n) = (term21 n m).
Proof. exact (h1). Qed.
Lemma lem1012044 (n : nat) (m : nat) (h1 : (m = n) = (term21 n m)) : (term21 n m) = (m = n).
Proof. exact (SYM (@lem1012043 n m h1)). Qed.
Lemma lem1012045 (n : nat) (m : nat) : ((term21 n m) = (m = n)) = ((m = n) = (term21 n m)).
Proof. exact (prop_ext (fun h1 : (term21 n m) = (m = n) => @lem1012042 m n h1) (fun h1 : (m = n) = (term21 n m) => @lem1012044 n m h1)). Qed.
Lemma lem1012046 (m : nat) : (term22 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem1012045 n m)). Qed.
Lemma lem1012047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012048 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem1012047) (@lem1012046 m)). Qed.
Lemma lem1012049 : term26 = term27.
Proof. exact (fun_ext (fun m : nat => @lem1012048 m)). Qed.
Lemma lem1012050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012051 : term28 = term29.
Proof. exact (MK_COMB (@lem1012050) (@lem1012049)). Qed.
Lemma lem1012052 : term29.
Proof. exact (EQ_MP (@lem1012051) (@lem92426)). Qed.
Lemma lem1012053 (t1 : Prop) : term30 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem1012054 (t1 : Prop) : (term30 t1) = (term31 t1).
Proof. exact (eq_refl (term30 t1)). Qed.
Lemma lem1012055 (t1 : Prop) : term31 t1.
Proof. exact (EQ_MP (@lem1012054 t1) (@lem1012053 t1)). Qed.
Lemma lem1012056 (t1 : Prop) (t2 : Prop) : term32 t1 t2.
Proof. exact (@lem1012055 t1 t2). Qed.
Lemma lem1012057 (t1 : Prop) (t2 : Prop) : (term32 t1 t2) = (term33 t1 t2).
Proof. exact (eq_refl (term32 t1 t2)). Qed.
Lemma lem1012058 (t1 : Prop) (t2 : Prop) : term33 t1 t2.
Proof. exact (EQ_MP (@lem1012057 t1 t2) (@lem1012056 t1 t2)). Qed.
Lemma lem1012061 (m : nat) : term34 m.
Proof. exact (@lem1012052 m). Qed.
Lemma lem1012062 (m : nat) : (term34 m) = (term25 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1012063 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1012062 m) (@lem1012061 m)). Qed.
Lemma lem1012064 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1012063 m n). Qed.
Lemma lem1012065 (n : nat) (m : nat) : (term35 m n) = ((m = n) = (term21 n m)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1012067 (n : nat) : term36 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1012068 (n : nat) : (term36 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem1012070 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (term7 m n) = p.
Proof. exact (h1). Qed.
Lemma lem1012071 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : p = (term7 m n).
Proof. exact (SYM (@lem1012070 m n p h1)). Qed.
Lemma lem1012072 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem1012073 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (term38 n p) = (term39 m n).
Proof. exact (MK_COMB (@lem1012072 n) (@lem1012071 m n p h1)). Qed.
Lemma lem1012074 (m : nat) (n : nat) : (term39 m n) = (((NUMERAL n) = (term40 m n)) = False).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1012075 (n : nat) (p : nat) : (term41 n p) = (term41 n p).
Proof. exact (eq_refl (term41 n p)). Qed.
Lemma lem1012076 (p : nat) (m : nat) (n : nat) : ((term38 n p) = (term39 m n)) = ((term38 n p) = (((NUMERAL n) = (term40 m n)) = False)).
Proof. exact (MK_COMB (@lem1012075 n p) (@lem1012074 m n)). Qed.
Lemma lem1012077 (n : nat) (p : nat) : (term38 n p) = (((NUMERAL n) = (NUMERAL p)) = False).
Proof. exact (eq_refl (term38 n p)). Qed.
Lemma lem1012078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1012079 (n : nat) (p : nat) : (term41 n p) = (term42 n p).
Proof. exact (MK_COMB (@lem1012078) (@lem1012077 n p)). Qed.
Lemma lem1012080 (m : nat) (n : nat) : (((NUMERAL n) = (term40 m n)) = False) = (((NUMERAL n) = (term40 m n)) = False).
Proof. exact (eq_refl (((NUMERAL n) = (term40 m n)) = False)). Qed.
Lemma lem1012081 (p : nat) (m : nat) (n : nat) : ((term38 n p) = (((NUMERAL n) = (term40 m n)) = False)) = ((((NUMERAL n) = (NUMERAL p)) = False) = (((NUMERAL n) = (term40 m n)) = False)).
Proof. exact (MK_COMB (@lem1012079 n p) (@lem1012080 m n)). Qed.
Lemma lem1012082 (p : nat) (m : nat) (n : nat) : ((term38 n p) = (term39 m n)) = ((((NUMERAL n) = (NUMERAL p)) = False) = (((NUMERAL n) = (term40 m n)) = False)).
Proof. exact (TRANS (@lem1012076 p m n) (@lem1012081 p m n)). Qed.
Lemma lem1012083 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (((NUMERAL n) = (NUMERAL p)) = False) = (((NUMERAL n) = (term40 m n)) = False).
Proof. exact (EQ_MP (@lem1012082 p m n) (@lem1012073 m n p h1)). Qed.
Lemma lem1012084 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (((NUMERAL n) = (term40 m n)) = False) = (((NUMERAL n) = (NUMERAL p)) = False).
Proof. exact (SYM (@lem1012083 m n p h1)). Qed.
Lemma lem1012086 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1012087 (m : nat) (n : nat) : (((NUMERAL n) = (term40 m n)) = False) = (term43 m n).
Proof. exact (@lem1012086 ((NUMERAL n) = (term40 m n))). Qed.
Lemma lem1012091 (n : nat) (m : nat) : (m = n) = (term21 n m).
Proof. exact (EQ_MP (@lem1012065 n m) (@lem1012064 m n)). Qed.
Lemma lem1012092 (m : nat) (n : nat) : ((NUMERAL n) = (term40 m n)) = (term44 m n).
Proof. exact (@lem1012091 (term40 m n) (NUMERAL n)). Qed.
Lemma lem1012096 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012068 n) (@lem1012067 n)). Qed.
Lemma lem1012097 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1012098 (n : nat) : (term45 n) = (Peano.le n).
Proof. exact (MK_COMB (@lem1012097) (@lem1012096 n)). Qed.
Lemma lem1012100 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012068 n) (@lem1012067 n)). Qed.
Lemma lem1012101 (m : nat) (n : nat) : (term40 m n) = (term7 m n).
Proof. exact (@lem1012100 (term7 m n)). Qed.
Lemma lem1012102 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem1012098 n) (@lem1012101 m n)). Qed.
Lemma lem1012103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1012104 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem1012103) (@lem1012102 m n)). Qed.
Lemma lem1012106 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012068 n) (@lem1012067 n)). Qed.
Lemma lem1012107 (m : nat) (n : nat) : (term40 m n) = (term7 m n).
Proof. exact (@lem1012106 (term7 m n)). Qed.
Lemma lem1012108 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1012109 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem1012108) (@lem1012107 m n)). Qed.
Lemma lem1012111 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012068 n) (@lem1012067 n)). Qed.
Lemma lem1012112 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem1012109 m n) (@lem1012111 n)). Qed.
Lemma lem1012113 (m : nat) (n : nat) : (term44 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem1012104 m n) (@lem1012112 m n)). Qed.
Lemma lem1012116 (m : nat) (n : nat) : ((NUMERAL n) = (term40 m n)) = (term54 m n).
Proof. exact (TRANS (@lem1012092 m n) (@lem1012113 m n)). Qed.
Lemma lem1012117 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012118 (m : nat) (n : nat) : (term43 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem1012117) (@lem1012116 m n)). Qed.
Lemma lem1012120 (t1 : Prop) (t2 : Prop) : (term56 t1 t2) = (term57 t1 t2).
Proof. exact (proj1 (@lem1012058 t1 t2)). Qed.
Lemma lem1012121 (m : nat) (n : nat) : (term55 m n) = (term58 m n).
Proof. exact (@lem1012120 (term47 m n) (term53 m n)). Qed.
Lemma lem1012124 (m : nat) (n : nat) : (term43 m n) = (term58 m n).
Proof. exact (TRANS (@lem1012118 m n) (@lem1012121 m n)). Qed.
Lemma lem1012125 (m : nat) (n : nat) : (((NUMERAL n) = (term40 m n)) = False) = (term58 m n).
Proof. exact (TRANS (@lem1012087 m n) (@lem1012124 m n)). Qed.
Lemma lem1012126 (m : nat) (n : nat) : (term58 m n) = (((NUMERAL n) = (term40 m n)) = False).
Proof. exact (SYM (@lem1012125 m n)). Qed.
Lemma lem1012130 (n : nat) (m : nat) : (term20 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1012037 n m) (@lem1012036 m n)). Qed.
Lemma lem1012131 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (@lem1012130 (term7 m n) n). Qed.
Lemma lem1012133 (n : nat) (m : nat) : (Peano.lt m n) = (term16 n m).
Proof. exact (EQ_MP (@lem1012031 n m) (@lem1012030 m n)). Qed.
Lemma lem1012134 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (@lem1012133 n (term7 m n)). Qed.
Lemma lem1012139 (m : nat) (n : nat) : (term59 m n) = (term61 m n).
Proof. exact (TRANS (@lem1012131 m n) (@lem1012134 m n)). Qed.
Lemma lem1012143 (m : nat) (n : nat) : (term12 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1012017 m n) (@lem1012016 m n)). Qed.
Lemma lem1012144 (m : nat) (n : nat) (d : nat) : (term62 m n d) = (term63 m n d).
Proof. exact (@lem1012143 (Nat.add m n) (S d)). Qed.
Lemma lem1012146 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1012010 m n) (@lem1012009 m n)). Qed.
Lemma lem1012147 (m : nat) (n : nat) (d : nat) : (term64 m n d) = (term65 m n d).
Proof. exact (@lem1012146 (Nat.add m n) d). Qed.
Lemma lem1012148 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1012149 (m : nat) (n : nat) (d : nat) : (term63 m n d) = (term66 m n d).
Proof. exact (MK_COMB (@lem1012148) (@lem1012147 m n d)). Qed.
Lemma lem1012150 (m : nat) (n : nat) (d : nat) : (term62 m n d) = (term66 m n d).
Proof. exact (TRANS (@lem1012144 m n d) (@lem1012149 m n d)). Qed.
Lemma lem1012151 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem1012152 (m : nat) (n : nat) (d : nat) : (n = (term62 m n d)) = (n = (term66 m n d)).
Proof. exact (MK_COMB (@lem1012151 n) (@lem1012150 m n d)). Qed.
Lemma lem1012155 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012152 m n d)). Qed.
Lemma lem1012156 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012157 (m : nat) (n : nat) : (term61 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem1012156) (@lem1012155 m n)). Qed.
Lemma lem1012162 (m : nat) (n : nat) : (term59 m n) = (term69 m n).
Proof. exact (TRANS (@lem1012139 m n) (@lem1012157 m n)). Qed.
Lemma lem1012163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1012164 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem1012163) (@lem1012162 m n)). Qed.
Lemma lem1012166 (n : nat) (m : nat) : (term20 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1012037 n m) (@lem1012036 m n)). Qed.
Lemma lem1012167 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (@lem1012166 n (term7 m n)). Qed.
Lemma lem1012169 (n : nat) (m : nat) : (Peano.lt m n) = (term16 n m).
Proof. exact (EQ_MP (@lem1012031 n m) (@lem1012030 m n)). Qed.
Lemma lem1012170 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (@lem1012169 (term7 m n) n). Qed.
Lemma lem1012175 (m : nat) (n : nat) : (term72 m n) = (term74 m n).
Proof. exact (TRANS (@lem1012167 m n) (@lem1012170 m n)). Qed.
Lemma lem1012179 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1012010 m n) (@lem1012009 m n)). Qed.
Lemma lem1012180 (n : nat) (d : nat) : (term6 n d) = (term7 n d).
Proof. exact (@lem1012179 n d). Qed.
Lemma lem1012181 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem1012182 (m : nat) (n : nat) (d : nat) : ((term7 m n) = (term6 n d)) = ((term7 m n) = (term7 n d)).
Proof. exact (MK_COMB (@lem1012181 m n) (@lem1012180 n d)). Qed.
Lemma lem1012185 (m : nat) (n : nat) : (term76 m n) = (term77 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012182 m n d)). Qed.
Lemma lem1012186 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012187 (m : nat) (n : nat) : (term74 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem1012186) (@lem1012185 m n)). Qed.
Lemma lem1012192 (m : nat) (n : nat) : (term72 m n) = (term78 m n).
Proof. exact (TRANS (@lem1012175 m n) (@lem1012187 m n)). Qed.
Lemma lem1012193 (m : nat) (n : nat) : (term58 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem1012164 m n) (@lem1012192 m n)). Qed.
Lemma lem1012196 (m : nat) (n : nat) : (term79 m n) = (term58 m n).
Proof. exact (SYM (@lem1012193 m n)). Qed.
Lemma lem1012198 (p : Prop) : p = (term80 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1012199 (m : nat) (n : nat) : (term79 m n) = (term81 m n).
Proof. exact (@lem1012198 (term79 m n)). Qed.
Lemma lem1012200 (m : nat) (n : nat) : (term81 m n) = (term79 m n).
Proof. exact (SYM (@lem1012199 m n)). Qed.
Lemma lem1012201 (m : nat) (n : nat) (h1 : term82 m n) : term82 m n.
Proof. exact (h1). Qed.
Lemma lem1012204 (m : nat) (n : nat) (h1 : term83 m n) : term83 m n.
Proof. exact (h1). Qed.
Lemma lem1012205 (m : nat) (n : nat) : term84 m n.
Proof. exact (fun h0 : term83 m n => @lem1012204 m n h0). Qed.
Lemma lem1012206 (m : nat) (n : nat) (h1 : term84 m n) : term84 m n.
Proof. exact (h1). Qed.
Lemma lem1012207 (m : nat) (n : nat) (h1 : term83 m n) : term83 m n.
Proof. exact (h1). Qed.
Lemma lem1012208 (m : nat) (n : nat) (h1 : term83 m n) (h2 : term84 m n) : term83 m n.
Proof. exact (@lem1012206 m n h2 (@lem1012207 m n h1)). Qed.
Lemma lem1012209 (m : nat) (n : nat) (h1 : term83 m n) : term85 m n.
Proof. exact (fun h0 : term84 m n => @lem1012208 m n h1 h0). Qed.
Lemma lem1012210 (m : nat) (n : nat) (h1 : term84 m n) : term84 m n.
Proof. exact (h1). Qed.
Lemma lem1012211 (m : nat) (n : nat) (h1 : term83 m n) (h2 : term84 m n) : term83 m n.
Proof. exact (@lem1012209 m n h1 (@lem1012210 m n h2)). Qed.
Lemma lem1012212 (m : nat) (n : nat) (h1 : term84 m n) : term84 m n.
Proof. exact (fun h0 : term83 m n => @lem1012211 m n h0 h1). Qed.
Lemma lem1012213 (m : nat) (n : nat) : term86 m n.
Proof. exact (fun h0 : term84 m n => @lem1012212 m n h0). Qed.
Lemma lem1012216 (m : nat) (n : nat) : term84 m n.
Proof. exact (@lem1012213 m n (@lem1012205 m n)). Qed.
Lemma lem1012238 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1012239 : term87 = term88.
Proof. exact (@lem1012238 term89). Qed.
Lemma lem1012248 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1012249 (m : nat) (n : nat) : (term83 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem1012248 m n) (@lem1012239)). Qed.
Lemma lem1012252 (n : nat) : (term92 n) = (term93 n).
Proof. exact (fun_ext (fun m : nat => @lem1012249 m n)). Qed.
Lemma lem1012253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012254 (n : nat) : (term94 n) = (term95 n).
Proof. exact (MK_COMB (@lem1012253) (@lem1012252 n)). Qed.
Lemma lem1012259 : term96 = term97.
Proof. exact (fun_ext (fun n : nat => @lem1012254 n)). Qed.
Lemma lem1012260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012269 : term98 = term99.
Proof. exact (MK_COMB (@lem1012260) (@lem1012259)). Qed.
Lemma lem1012270 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1012271 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1012270 n m)). Qed.
Lemma lem1012272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012273 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1012272) (@lem1012271 m)). Qed.
Lemma lem1012274 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1012273 m)). Qed.
Lemma lem1012275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012276 : term89 = term89.
Proof. exact (MK_COMB (@lem1012275) (@lem1012274)). Qed.
Lemma lem1012277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012278 : term88 = term88.
Proof. exact (MK_COMB (@lem1012277) (@lem1012276)). Qed.
Lemma lem1012279 (m : nat) (n : nat) (d : nat) : ((term7 m n) = (term7 n d)) = ((term7 m n) = (term7 n d)).
Proof. exact (eq_refl ((term7 m n) = (term7 n d))). Qed.
Lemma lem1012280 (m : nat) (n : nat) : (term77 m n) = (term77 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012279 m n d)). Qed.
Lemma lem1012281 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012282 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem1012281) (@lem1012280 m n)). Qed.
Lemma lem1012283 (m : nat) (n : nat) (d : nat) : (n = (term66 m n d)) = (n = (term66 m n d)).
Proof. exact (eq_refl (n = (term66 m n d))). Qed.
Lemma lem1012284 (m : nat) (n : nat) : (term68 m n) = (term68 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012283 m n d)). Qed.
Lemma lem1012285 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012286 (m : nat) (n : nat) : (term69 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem1012285) (@lem1012284 m n)). Qed.
Lemma lem1012287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1012288 (m : nat) (n : nat) : (term71 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem1012287) (@lem1012286 m n)). Qed.
Lemma lem1012289 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem1012288 m n) (@lem1012282 m n)). Qed.
Lemma lem1012290 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012291 (m : nat) (n : nat) : (term82 m n) = (term82 m n).
Proof. exact (MK_COMB (@lem1012290) (@lem1012289 m n)). Qed.
Lemma lem1012292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1012293 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem1012292) (@lem1012291 m n)). Qed.
Lemma lem1012294 (m : nat) (n : nat) : (term91 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem1012293 m n) (@lem1012278)). Qed.
Lemma lem1012295 (n : nat) : (term93 n) = (term93 n).
Proof. exact (fun_ext (fun m : nat => @lem1012294 m n)). Qed.
Lemma lem1012296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012297 (n : nat) : (term95 n) = (term95 n).
Proof. exact (MK_COMB (@lem1012296) (@lem1012295 n)). Qed.
Lemma lem1012298 : term97 = term97.
Proof. exact (fun_ext (fun n : nat => @lem1012297 n)). Qed.
Lemma lem1012299 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012300 : term99 = term99.
Proof. exact (MK_COMB (@lem1012299) (@lem1012298)). Qed.
Lemma lem1012343 : term98 = term99.
Proof. exact (TRANS (@lem1012269) (@lem1012300)). Qed.
Lemma lem1012344 : term99 = term98.
Proof. exact (SYM (@lem1012343)). Qed.
Lemma lem1012345 (m : nat) (n : nat) (h1 : term82 m n) : term82 m n.
Proof. exact (h1). Qed.
Lemma lem1012346 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1012348 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1012349 (m : nat) (n : nat) : (term105 m n) = (term106 m n).
Proof. exact (@lem1012348 (term68 m n)). Qed.
Lemma lem1012350 (m : nat) (n : nat) (d : nat) : (term107 m n d) = (n = (term66 m n d)).
Proof. exact (eq_refl (term107 m n d)). Qed.
Lemma lem1012351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012353 (m : nat) (n : nat) (d : nat) : (term108 m n d) = (term109 m n d).
Proof. exact (MK_COMB (@lem1012351) (@lem1012350 m n d)). Qed.
Lemma lem1012354 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012353 m n d)). Qed.
Lemma lem1012355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012356 (m : nat) (n : nat) : (term106 m n) = (term112 m n).
Proof. exact (MK_COMB (@lem1012355) (@lem1012354 m n)). Qed.
Lemma lem1012357 (m : nat) (n : nat) : (term105 m n) = (term112 m n).
Proof. exact (TRANS (@lem1012349 m n) (@lem1012356 m n)). Qed.
Lemma lem1012359 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1012360 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (@lem1012359 (term77 m n)). Qed.
Lemma lem1012361 (m : nat) (n : nat) (d : nat) : (term115 m n d) = ((term7 m n) = (term7 n d)).
Proof. exact (eq_refl (term115 m n d)). Qed.
Lemma lem1012362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012364 (m : nat) (n : nat) (d : nat) : (term116 m n d) = (term117 m n d).
Proof. exact (MK_COMB (@lem1012362) (@lem1012361 m n d)). Qed.
Lemma lem1012365 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012364 m n d)). Qed.
Lemma lem1012366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012367 (m : nat) (n : nat) : (term114 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem1012366) (@lem1012365 m n)). Qed.
Lemma lem1012368 (m : nat) (n : nat) : (term113 m n) = (term120 m n).
Proof. exact (TRANS (@lem1012360 m n) (@lem1012367 m n)). Qed.
Lemma lem1012369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1012370 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem1012369) (@lem1012357 m n)). Qed.
Lemma lem1012371 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (MK_COMB (@lem1012370 m n) (@lem1012368 m n)). Qed.
Lemma lem1012372 (m : nat) (n : nat) : (term82 m n) = (term123 m n).
Proof. exact (@lem17160 (term69 m n) (term78 m n)). Qed.
Lemma lem1012385 (m : nat) (n : nat) : (term82 m n) = (term124 m n).
Proof. exact (TRANS (@lem1012372 m n) (@lem1012371 m n)). Qed.
Lemma lem1012386 (m : nat) (n : nat) (h1 : term82 m n) : term124 m n.
Proof. exact (EQ_MP (@lem1012385 m n) (@lem1012345 m n h1)). Qed.
Lemma lem1012387 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1012388 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1012387 n m)). Qed.
Lemma lem1012389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012390 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1012389) (@lem1012388 m)). Qed.
Lemma lem1012391 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1012390 m)). Qed.
Lemma lem1012392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012405 : term89 = term89.
Proof. exact (MK_COMB (@lem1012392) (@lem1012391)). Qed.
Lemma lem1012406 (h1 : term89) : term89.
Proof. exact (EQ_MP (@lem1012405) (@lem1012346 h1)). Qed.
Lemma lem1012425 (m : nat) (n : nat) (d : nat) : (term117 m n d) = (term117 m n d).
Proof. exact (eq_refl (term117 m n d)). Qed.
Lemma lem1012426 (m : nat) (n : nat) : (term119 m n) = (term119 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012425 m n d)). Qed.
Lemma lem1012427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012428 (m : nat) (n : nat) : (term120 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem1012427) (@lem1012426 m n)). Qed.
Lemma lem1012447 (m : nat) (n : nat) (d : nat) : (term109 m n d) = (term109 m n d).
Proof. exact (eq_refl (term109 m n d)). Qed.
Lemma lem1012448 (m : nat) (n : nat) : (term111 m n) = (term111 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012447 m n d)). Qed.
Lemma lem1012449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012450 (m : nat) (n : nat) : (term112 m n) = (term112 m n).
Proof. exact (MK_COMB (@lem1012449) (@lem1012448 m n)). Qed.
Lemma lem1012451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1012452 (m : nat) (n : nat) : (term122 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem1012451) (@lem1012450 m n)). Qed.
Lemma lem1012453 (m : nat) (n : nat) : (term124 m n) = (term124 m n).
Proof. exact (MK_COMB (@lem1012452 m n) (@lem1012428 m n)). Qed.
Lemma lem1012454 (m : nat) (n : nat) (h1 : term82 m n) : term124 m n.
Proof. exact (EQ_MP (@lem1012453 m n) (@lem1012386 m n h1)). Qed.
Lemma lem1012467 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1012468 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1012467 n m)). Qed.
Lemma lem1012469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012470 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1012469) (@lem1012468 m)). Qed.
Lemma lem1012471 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1012470 m)). Qed.
Lemma lem1012472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012473 : term89 = term89.
Proof. exact (MK_COMB (@lem1012472) (@lem1012471)). Qed.
Lemma lem1012474 (h1 : term89) : term89.
Proof. exact (EQ_MP (@lem1012473) (@lem1012406 h1)). Qed.
Lemma lem1012475 (m : nat) (n : nat) (h1 : term82 m n) : term120 m n.
Proof. exact (proj2 (@lem1012454 m n h1)). Qed.
Lemma lem1012478 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1012479 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1012478 n m)). Qed.
Lemma lem1012480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012481 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1012480) (@lem1012479 m)). Qed.
Lemma lem1012482 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1012481 m)). Qed.
Lemma lem1012483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012485 : term89 = term89.
Proof. exact (MK_COMB (@lem1012483) (@lem1012482)). Qed.
Lemma lem1012486 (h1 : term89) : term89.
Proof. exact (EQ_MP (@lem1012485) (@lem1012474 h1)). Qed.
Lemma lem1012495 (m : nat) (n : nat) (d : nat) : (term117 m n d) = (term117 m n d).
Proof. exact (eq_refl (term117 m n d)). Qed.
Lemma lem1012496 (m : nat) (n : nat) : (term119 m n) = (term119 m n).
Proof. exact (fun_ext (fun d : nat => @lem1012495 m n d)). Qed.
Lemma lem1012497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012499 (m : nat) (n : nat) : (term120 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem1012497) (@lem1012496 m n)). Qed.
Lemma lem1012500 (m : nat) (n : nat) (h1 : term82 m n) : term120 m n.
Proof. exact (EQ_MP (@lem1012499 m n) (@lem1012475 m n h1)). Qed.
Lemma lem1012501 (_16449 : nat) (h1 : term89) : term125 _16449.
Proof. exact (@lem1012486 h1 _16449). Qed.
Lemma lem1012502 (_16449 : nat) : (term125 _16449) = (term101 _16449).
Proof. exact (eq_refl (term125 _16449)). Qed.
Lemma lem1012503 (_16449 : nat) (h1 : term89) : term101 _16449.
Proof. exact (EQ_MP (@lem1012502 _16449) (@lem1012501 _16449 h1)). Qed.
Lemma lem1012504 (_16449 : nat) (_16450 : nat) (h1 : term89) : term126 _16449 _16450.
Proof. exact (@lem1012503 _16449 h1 _16450). Qed.
Lemma lem1012505 (_16450 : nat) (_16449 : nat) : (term126 _16449 _16450) = ((Nat.add _16449 _16450) = (Nat.add _16450 _16449)).
Proof. exact (eq_refl (term126 _16449 _16450)). Qed.
Lemma lem1012510 (_16452 : nat) (m : nat) (n : nat) (h1 : term82 m n) : term127 m n _16452.
Proof. exact (@lem1012500 m n h1 _16452). Qed.
Lemma lem1012511 (m : nat) (n : nat) (_16452 : nat) : (term127 m n _16452) = (term117 m n _16452).
Proof. exact (eq_refl (term127 m n _16452)). Qed.
Lemma lem1012518 (_16452 : nat) (m : nat) (n : nat) (h1 : term82 m n) : term117 m n _16452.
Proof. exact (EQ_MP (@lem1012511 m n _16452) (@lem1012510 _16452 m n h1)). Qed.
Lemma lem1012519 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1012520 (_16453 : nat) (_16454 : nat) (h1 : _16453 = _16454) : _16453 = _16454.
Proof. exact (h1). Qed.
Lemma lem1012521 (_16453 : nat) (_16454 : nat) (h1 : _16453 = _16454) : (S _16453) = (S _16454).
Proof. exact (MK_COMB (@lem1012519) (@lem1012520 _16453 _16454 h1)). Qed.
Lemma lem1012522 (_16453 : nat) (_16454 : nat) : term128 _16453 _16454.
Proof. exact (fun h0 : _16453 = _16454 => @lem1012521 _16453 _16454 h0). Qed.
Lemma lem1012524 (a : Prop) (b : Prop) : (a -> b) = (term129 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1012525 (_16453 : nat) (_16454 : nat) : (term128 _16453 _16454) = (term130 _16453 _16454).
Proof. exact (@lem1012524 (_16453 = _16454) ((S _16453) = (S _16454))). Qed.
Lemma lem1012526 (_16453 : nat) (_16454 : nat) : term130 _16453 _16454.
Proof. exact (EQ_MP (@lem1012525 _16453 _16454) (@lem1012522 _16453 _16454)). Qed.
Lemma lem1012545 (_16450 : nat) (_16449 : nat) (h1 : term89) : (Nat.add _16449 _16450) = (Nat.add _16450 _16449).
Proof. exact (EQ_MP (@lem1012505 _16450 _16449) (@lem1012504 _16449 _16450 h1)). Qed.
Lemma lem1012546 (n : nat) (m : nat) (h1 : term89) : (Nat.add m n) = (Nat.add n m).
Proof. exact (@lem1012545 n m h1). Qed.
Lemma lem1012547 (n : nat) (m : nat) (h1 : term89) : term131 n m.
Proof. exact (fun h0 : term132 n m => @lem1012546 n m h1). Qed.
Lemma lem1012549 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1012550 (n : nat) (m : nat) : (term131 n m) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (@lem1012549 ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1012551 (n : nat) (m : nat) (h1 : term89) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1012550 n m) (@lem1012547 n m h1)). Qed.
Lemma lem1012557 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1012558 (_16453 : nat) (_16454 : nat) : (term130 _16453 _16454) = (term134 _16453 _16454).
Proof. exact (@lem1012557 ((S _16453) = (S _16454)) (term135 _16453 _16454)). Qed.
Lemma lem1012568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1012569 (_16453 : nat) (_16454 : nat) : (term136 _16453 _16454) = (term137 _16453 _16454).
Proof. exact (MK_COMB (@lem1012568) (@lem1012558 _16453 _16454)). Qed.
Lemma lem1012579 (_16453 : nat) (_16454 : nat) : (term134 _16453 _16454) = (term134 _16453 _16454).
Proof. exact (eq_refl (term134 _16453 _16454)). Qed.
Lemma lem1012580 (_16453 : nat) (_16454 : nat) : ((term130 _16453 _16454) = (term134 _16453 _16454)) = ((term134 _16453 _16454) = (term134 _16453 _16454)).
Proof. exact (MK_COMB (@lem1012569 _16453 _16454) (@lem1012579 _16453 _16454)). Qed.
Lemma lem1012582 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1012583 (x : Prop) : (x = x) = True.
Proof. exact (@lem1012582 Prop x). Qed.
Lemma lem1012584 (_16453 : nat) (_16454 : nat) : ((term134 _16453 _16454) = (term134 _16453 _16454)) = True.
Proof. exact (@lem1012583 (term134 _16453 _16454)). Qed.
Lemma lem1012585 (_16453 : nat) (_16454 : nat) : ((term130 _16453 _16454) = (term134 _16453 _16454)) = True.
Proof. exact (TRANS (@lem1012580 _16453 _16454) (@lem1012584 _16453 _16454)). Qed.
Lemma lem1012586 (_16453 : nat) (_16454 : nat) : True = ((term130 _16453 _16454) = (term134 _16453 _16454)).
Proof. exact (SYM (@lem1012585 _16453 _16454)). Qed.
Lemma lem1012587 (_16453 : nat) (_16454 : nat) : (term130 _16453 _16454) = (term134 _16453 _16454).
Proof. exact (EQ_MP (@lem1012586 _16453 _16454) (@lem0)). Qed.
Lemma lem1012588 (_16453 : nat) (_16454 : nat) : term134 _16453 _16454.
Proof. exact (EQ_MP (@lem1012587 _16453 _16454) (@lem1012526 _16453 _16454)). Qed.
Lemma lem1012590 (b : Prop) (a : Prop) : (a \/ b) = (term138 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1012591 (_16453 : nat) (_16454 : nat) : (term134 _16453 _16454) = (term139 _16453 _16454).
Proof. exact (@lem1012590 (term135 _16453 _16454) ((S _16453) = (S _16454))). Qed.
Lemma lem1012593 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1012594 (_16453 : nat) (_16454 : nat) : (term141 _16453 _16454) = (_16453 = _16454).
Proof. exact (@lem1012593 (_16453 = _16454)). Qed.
Lemma lem1012595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1012596 (_16453 : nat) (_16454 : nat) : (term142 _16453 _16454) = (term143 _16453 _16454).
Proof. exact (MK_COMB (@lem1012595) (@lem1012594 _16453 _16454)). Qed.
Lemma lem1012597 (_16453 : nat) (_16454 : nat) : ((S _16453) = (S _16454)) = ((S _16453) = (S _16454)).
Proof. exact (eq_refl ((S _16453) = (S _16454))). Qed.
Lemma lem1012598 (_16453 : nat) (_16454 : nat) : (term139 _16453 _16454) = (term128 _16453 _16454).
Proof. exact (MK_COMB (@lem1012596 _16453 _16454) (@lem1012597 _16453 _16454)). Qed.
Lemma lem1012599 (_16453 : nat) (_16454 : nat) : (term134 _16453 _16454) = (term128 _16453 _16454).
Proof. exact (TRANS (@lem1012591 _16453 _16454) (@lem1012598 _16453 _16454)). Qed.
Lemma lem1012602 (_16453 : nat) (_16454 : nat) : term128 _16453 _16454.
Proof. exact (EQ_MP (@lem1012599 _16453 _16454) (@lem1012588 _16453 _16454)). Qed.
Lemma lem1012603 (n : nat) (m : nat) : term144 n m.
Proof. exact (@lem1012602 (Nat.add m n) (Nat.add n m)). Qed.
Lemma lem1012606 (n : nat) (m : nat) (h1 : term89) : (term7 m n) = (term7 n m).
Proof. exact (@lem1012603 n m (@lem1012551 n m h1)). Qed.
Lemma lem1012607 (n : nat) (m : nat) (h1 : term89) : term145 n m.
Proof. exact (fun h0 : term146 n m => @lem1012606 n m h1). Qed.
Lemma lem1012609 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1012610 (n : nat) (m : nat) : (term145 n m) = ((term7 m n) = (term7 n m)).
Proof. exact (@lem1012609 ((term7 m n) = (term7 n m))). Qed.
Lemma lem1012611 (n : nat) (m : nat) (h1 : term89) : (term7 m n) = (term7 n m).
Proof. exact (EQ_MP (@lem1012610 n m) (@lem1012607 n m h1)). Qed.
Lemma lem1012614 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1012616 (m : nat) (n : nat) (_16452 : nat) : (term117 m n _16452) = (term147 m n _16452).
Proof. exact (@lem1012614 ((term7 m n) = (term7 n _16452))). Qed.
Lemma lem1012619 (_16452 : nat) (m : nat) (n : nat) (h1 : term82 m n) : term147 m n _16452.
Proof. exact (EQ_MP (@lem1012616 m n _16452) (@lem1012518 _16452 m n h1)). Qed.
Lemma lem1012620 (m : nat) (n : nat) (h1 : term82 m n) : term148 n m.
Proof. exact (@lem1012619 m m n h1). Qed.
Lemma lem1012623 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : False.
Proof. exact (@lem1012620 m n h2 (@lem1012611 n m h1)). Qed.
Lemma lem1012624 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : term149.
Proof. exact (fun h0 : ~ False => @lem1012623 m n h1 h2). Qed.
Lemma lem1012626 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1012627 : term149 = False.
Proof. exact (@lem1012626 False). Qed.
Lemma lem1012628 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : False.
Proof. exact (EQ_MP (@lem1012627) (@lem1012624 m n h1 h2)). Qed.
Lemma lem1012629 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : term89 = False.
Proof. exact (prop_ext (fun h3 : term89 => @lem1012628 m n h1 h2) (fun h3 : False => @lem1012486 h1)). Qed.
Lemma lem1012630 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : False.
Proof. exact (EQ_MP (@lem1012629 m n h1 h2) (@lem1012486 h1)). Qed.
Lemma lem1012631 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : term89 = False.
Proof. exact (prop_ext (fun h3 : term89 => @lem1012630 m n h1 h2) (fun h3 : False => @lem1012474 h1)). Qed.
Lemma lem1012632 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : False.
Proof. exact (EQ_MP (@lem1012631 m n h1 h2) (@lem1012474 h1)). Qed.
Lemma lem1012633 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : term89 = False.
Proof. exact (prop_ext (fun h3 : term89 => @lem1012632 m n h1 h2) (fun h3 : False => @lem1012406 h1)). Qed.
Lemma lem1012634 (m : nat) (n : nat) (h1 : term89) (h2 : term82 m n) : False.
Proof. exact (EQ_MP (@lem1012633 m n h1 h2) (@lem1012406 h1)). Qed.
Lemma lem1012635 (m : nat) (n : nat) (h1 : term82 m n) : term87.
Proof. exact (fun h0 : term89 => @lem1012634 m n h0 h1). Qed.
Lemma lem1012636 : term87 = term88.
Proof. exact (@lem69 term89). Qed.
Lemma lem1012637 (m : nat) (n : nat) (h1 : term82 m n) : term88.
Proof. exact (EQ_MP (@lem1012636) (@lem1012635 m n h1)). Qed.
Lemma lem1012638 (m : nat) (n : nat) : term91 m n.
Proof. exact (fun h0 : term82 m n => @lem1012637 m n h0). Qed.
Lemma lem1012643 (n : nat) : term95 n.
Proof. exact (fun m : nat => @lem1012638 m n). Qed.
Lemma lem1012648 : term99.
Proof. exact (fun n : nat => @lem1012643 n). Qed.
Lemma lem1012649 : term98.
Proof. exact (EQ_MP (@lem1012344) (@lem1012648)). Qed.
Lemma lem1012650 (n : nat) : term150 n.
Proof. exact (@lem1012649 n). Qed.
Lemma lem1012651 (n : nat) : (term150 n) = (term94 n).
Proof. exact (eq_refl (term150 n)). Qed.
Lemma lem1012652 (n : nat) : term94 n.
Proof. exact (EQ_MP (@lem1012651 n) (@lem1012650 n)). Qed.
Lemma lem1012653 (n : nat) (m : nat) : term151 n m.
Proof. exact (@lem1012652 n m). Qed.
Lemma lem1012654 (m : nat) (n : nat) : (term151 n m) = (term83 m n).
Proof. exact (eq_refl (term151 n m)). Qed.
Lemma lem1012655 (m : nat) (n : nat) : term83 m n.
Proof. exact (EQ_MP (@lem1012654 m n) (@lem1012653 n m)). Qed.
Lemma lem1012657 (m : nat) (n : nat) : term83 m n.
Proof. exact (@lem1012216 m n (@lem1012655 m n)). Qed.
Lemma lem1012658 (m : nat) (n : nat) (h1 : term82 m n) : term87.
Proof. exact (@lem1012657 m n (@lem1012201 m n h1)). Qed.
Lemma lem1012659 (m : nat) (n : nat) (h1 : term82 m n) : False.
Proof. exact (@lem1012658 m n h1 (@lem77775)). Qed.
Lemma lem1012660 (m : nat) (n : nat) (h1 : term82 m n) : (term82 m n) = False.
Proof. exact (prop_ext (fun h2 : term82 m n => @lem1012659 m n h1) (fun h2 : False => @lem1012201 m n h1)). Qed.
Lemma lem1012661 (m : nat) (n : nat) (h1 : term82 m n) : False.
Proof. exact (EQ_MP (@lem1012660 m n h1) (@lem1012201 m n h1)). Qed.
Lemma lem1012662 (m : nat) (n : nat) : term81 m n.
Proof. exact (fun h0 : term82 m n => @lem1012661 m n h0). Qed.
Lemma lem1012663 (m : nat) (n : nat) : term79 m n.
Proof. exact (EQ_MP (@lem1012200 m n) (@lem1012662 m n)). Qed.
Lemma lem1012664 (m : nat) (n : nat) : term58 m n.
Proof. exact (EQ_MP (@lem1012196 m n) (@lem1012663 m n)). Qed.
Lemma lem1012665 (m : nat) (n : nat) : ((NUMERAL n) = (term40 m n)) = False.
Proof. exact (EQ_MP (@lem1012126 m n) (@lem1012664 m n)). Qed.
Lemma lem1012666 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : ((NUMERAL n) = (NUMERAL p)) = False.
Proof. exact (EQ_MP (@lem1012084 m n p h1) (@lem1012665 m n)). Qed.
Lemma lem1012669 (m : nat) (n : nat) (p : nat) : term152 m n p.
Proof. exact (fun h0 : (term7 m n) = p => @lem1012666 m n p h0). Qed.
Lemma lem1012670 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (term7 m n) = p.
Proof. exact (h1). Qed.
Lemma lem1012671 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : ((NUMERAL n) = (NUMERAL p)) = False.
Proof. exact (@lem1012669 m n p (@lem1012670 m n p h1)). Qed.
