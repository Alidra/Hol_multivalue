Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_EXISTS_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import MOD_MULT_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem185848 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term0 _476 _475 _474 _477) = (term1 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem185849 (_474 : Prop) (_475 : Prop) (m : nat) (n : nat) (_477 : Prop) : (term2 m n _475 _474 _477) = (term3 _474 _475 m n _477).
Proof. exact (@lem185848 _474 _475 (term4 m n) _477). Qed.
Lemma lem185850 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (@lem185849 (m = (NUMERAL 0)) (n = (NUMERAL 0)) m n ((Nat.modulo m n) = (NUMERAL 0))). Qed.
Lemma lem185851 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = ((Nat.modulo m n) = (NUMERAL 0))).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem185852 (n : nat) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem185853 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem185852 n) (@lem185851 m n)). Qed.
Lemma lem185854 (n : nat) (m : nat) : (term12 n m) = ((term8 m n) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term12 n m)). Qed.
Lemma lem185855 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem185856 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem185855 n) (@lem185854 n m)). Qed.
Lemma lem185857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem185858 (n : nat) (m : nat) : (term16 n m) = (term17 n m).
Proof. exact (MK_COMB (@lem185857) (@lem185856 n m)). Qed.
Lemma lem185859 (m : nat) (n : nat) : (term6 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem185858 n m) (@lem185853 m n)). Qed.
Lemma lem185860 (m : nat) (n : nat) : (term5 m n) = ((term8 m n) = (term19 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem185861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem185862 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem185861) (@lem185860 m n)). Qed.
Lemma lem185863 (m : nat) (n : nat) : ((term5 m n) = (term6 m n)) = (((term8 m n) = (term19 m n)) = (term18 m n)).
Proof. exact (MK_COMB (@lem185862 m n) (@lem185859 m n)). Qed.
Lemma lem185864 (m : nat) (n : nat) : ((term8 m n) = (term19 m n)) = (term18 m n).
Proof. exact (EQ_MP (@lem185863 m n) (@lem185850 m n)). Qed.
Lemma lem185865 (m : nat) (n : nat) : (term18 m n) = ((term8 m n) = (term19 m n)).
Proof. exact (SYM (@lem185864 m n)). Qed.
Lemma lem185866 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185883 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem185930 : term23.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem185931 (n : nat) : term24 n.
Proof. exact (@lem185930 n). Qed.
Lemma lem185932 (n : nat) : (term24 n) = ((term25 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem185943 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185944 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem185945 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term26.
Proof. exact (MK_COMB (@lem185944) (@lem185943 n h1)). Qed.
Lemma lem185946 (q : nat) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem185947 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n q) = (term25 q).
Proof. exact (MK_COMB (@lem185945 n h1) (@lem185946 q)). Qed.
Lemma lem185949 (n : nat) : (term25 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem185932 n) (@lem185931 n)). Qed.
Lemma lem185950 (q : nat) : (term25 q) = (NUMERAL 0).
Proof. exact (@lem185949 q). Qed.
Lemma lem185951 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n q) = (NUMERAL 0).
Proof. exact (TRANS (@lem185947 q n h1) (@lem185950 q)). Qed.
Lemma lem185952 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem185953 (q : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (m = (Nat.mul n q)) = (m = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem185952 m) (@lem185951 q n h1)). Qed.
Lemma lem185956 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term27 m n) = (term28 m).
Proof. exact (fun_ext (fun q : nat => @lem185953 q m n h1)). Qed.
Lemma lem185957 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem185958 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term8 m n) = (term29 m).
Proof. exact (MK_COMB (@lem185957) (@lem185956 m n h1)). Qed.
Lemma lem185960 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem185961 (t : Prop) : (term31 t) = t.
Proof. exact (@lem185960 nat t). Qed.
Lemma lem185962 (m : nat) : (term29 m) = (m = (NUMERAL 0)).
Proof. exact (@lem185961 (m = (NUMERAL 0))). Qed.
Lemma lem185965 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term8 m n) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem185958 m n h1) (@lem185962 m)). Qed.
Lemma lem185966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem185967 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term32 m n) = (term33 m).
Proof. exact (MK_COMB (@lem185966) (@lem185965 m n h1)). Qed.
Lemma lem185970 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem185971 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term8 m n) = (m = (NUMERAL 0))) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem185967 m n h1) (@lem185970 m)). Qed.
Lemma lem185973 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem185974 (x : Prop) : (x = x) = True.
Proof. exact (@lem185973 Prop x). Qed.
Lemma lem185975 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem185974 (m = (NUMERAL 0))). Qed.
Lemma lem185976 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term8 m n) = (m = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem185971 m n h1) (@lem185975 m)). Qed.
Lemma lem185977 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term8 m n) = (m = (NUMERAL 0))).
Proof. exact (SYM (@lem185976 m n h1)). Qed.
Lemma lem186038 (m : nat) (n : nat) (h1 : term8 m n) : term8 m n.
Proof. exact (h1). Qed.
Lemma lem186039 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : m = (Nat.mul n q).
Proof. exact (h1). Qed.
Lemma lem186040 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem186041 (m : nat) : term34 m.
Proof. exact (@lem170526 m). Qed.
Lemma lem186042 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem186043 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem186042 m) (@lem186041 m)). Qed.
Lemma lem186044 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem186043 m n). Qed.
Lemma lem186045 (n : nat) (m : nat) : (term36 m n) = ((term37 n m) = (NUMERAL 0)).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem186063 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : m = (Nat.mul n q).
Proof. exact (h1). Qed.
Lemma lem186064 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem186065 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (Nat.modulo m) = (term38 n q).
Proof. exact (MK_COMB (@lem186064) (@lem186063 m n q h1)). Qed.
Lemma lem186066 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem186067 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (Nat.modulo m n) = (term37 q n).
Proof. exact (MK_COMB (@lem186065 m n q h1) (@lem186066 n)). Qed.
Lemma lem186069 (n : nat) (m : nat) : (term37 n m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem186045 n m) (@lem186044 m n)). Qed.
Lemma lem186070 (q : nat) (n : nat) : (term37 q n) = (NUMERAL 0).
Proof. exact (@lem186069 q n). Qed.
Lemma lem186071 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem186067 m n q h1) (@lem186070 q n)). Qed.
Lemma lem186072 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem186073 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (term39 m n) = term40.
Proof. exact (MK_COMB (@lem186072) (@lem186071 m n q h1)). Qed.
Lemma lem186074 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem186075 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : ((Nat.modulo m n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem186073 m n q h1) (@lem186074)). Qed.
Lemma lem186077 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem186078 (x : nat) : (x = x) = True.
Proof. exact (@lem186077 nat x). Qed.
Lemma lem186079 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem186078 (NUMERAL 0)). Qed.
Lemma lem186080 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : ((Nat.modulo m n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem186075 m n q h1) (@lem186079)). Qed.
Lemma lem186081 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : True = ((Nat.modulo m n) = (NUMERAL 0)).
Proof. exact (SYM (@lem186080 m n q h1)). Qed.
Lemma lem186082 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem186081 m n q h1) (@lem0)). Qed.
Lemma lem186112 (m : nat) (n : nat) (h1 : m = (term41 m n)) : m = (term41 m n).
Proof. exact (h1). Qed.
Lemma lem186113 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem186114 (m : nat) (n : nat) (h1 : m = (term41 m n)) : (@eq nat m) = (term42 m n).
Proof. exact (MK_COMB (@lem186113) (@lem186112 m n h1)). Qed.
Lemma lem186115 (m : nat) (n : nat) : (term43 m n) = (term43 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem186116 (m : nat) (n : nat) (h1 : m = (term41 m n)) : (m = (term43 m n)) = ((term41 m n) = (term43 m n)).
Proof. exact (MK_COMB (@lem186114 m n h1) (@lem186115 m n)). Qed.
Lemma lem186117 (m : nat) (n : nat) (h1 : m = (term41 m n)) : ((term41 m n) = (term43 m n)) = (m = (term43 m n)).
Proof. exact (SYM (@lem186116 m n h1)). Qed.
Lemma lem186119 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem186120 (m : nat) (n : nat) : (m = (term41 m n)) = (term45 m n).
Proof. exact (@lem186119 (m = (term41 m n))). Qed.
Lemma lem186121 (m : nat) (n : nat) : (term45 m n) = (m = (term41 m n)).
Proof. exact (SYM (@lem186120 m n)). Qed.
Lemma lem186122 (m : nat) (n : nat) (h1 : term46 m n) : term46 m n.
Proof. exact (h1). Qed.
Lemma lem186125 (m : nat) (n : nat) (h1 : term47 m n) : term47 m n.
Proof. exact (h1). Qed.
Lemma lem186126 (m : nat) (n : nat) : term48 m n.
Proof. exact (fun h0 : term47 m n => @lem186125 m n h0). Qed.
Lemma lem186127 (m : nat) (n : nat) (h1 : term48 m n) : term48 m n.
Proof. exact (h1). Qed.
Lemma lem186128 (m : nat) (n : nat) (h1 : term47 m n) : term47 m n.
Proof. exact (h1). Qed.
Lemma lem186129 (m : nat) (n : nat) (h1 : term47 m n) (h2 : term48 m n) : term47 m n.
Proof. exact (@lem186127 m n h2 (@lem186128 m n h1)). Qed.
Lemma lem186130 (m : nat) (n : nat) (h1 : term47 m n) : term49 m n.
Proof. exact (fun h0 : term48 m n => @lem186129 m n h1 h0). Qed.
Lemma lem186131 (m : nat) (n : nat) (h1 : term48 m n) : term48 m n.
Proof. exact (h1). Qed.
Lemma lem186132 (m : nat) (n : nat) (h1 : term47 m n) (h2 : term48 m n) : term47 m n.
Proof. exact (@lem186130 m n h1 (@lem186131 m n h2)). Qed.
Lemma lem186133 (m : nat) (n : nat) (h1 : term48 m n) : term48 m n.
Proof. exact (fun h0 : term47 m n => @lem186132 m n h0 h1). Qed.
Lemma lem186134 (m : nat) (n : nat) : term50 m n.
Proof. exact (fun h0 : term48 m n => @lem186133 m n h0). Qed.
Lemma lem186137 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem186134 m n (@lem186126 m n)). Qed.
Lemma lem186153 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem186154 : term51 = term52.
Proof. exact (@lem186153 term53). Qed.
Lemma lem186167 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem186168 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem186167 m n) (@lem186154)). Qed.
Lemma lem186171 (m : nat) (n : nat) : (term57 m n) = (term57 m n).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem186172 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem186171 m n) (@lem186168 m n)). Qed.
Lemma lem186175 (n : nat) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem186176 (m : nat) (n : nat) : (term47 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem186175 n) (@lem186172 m n)). Qed.
Lemma lem186179 (n : nat) : (term61 n) = (term62 n).
Proof. exact (fun_ext (fun m : nat => @lem186176 m n)). Qed.
Lemma lem186180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186181 (n : nat) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem186180) (@lem186179 n)). Qed.
Lemma lem186186 : term65 = term66.
Proof. exact (fun_ext (fun n : nat => @lem186181 n)). Qed.
Lemma lem186187 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186196 : term67 = term68.
Proof. exact (MK_COMB (@lem186187) (@lem186186)). Qed.
Lemma lem186207 (m : nat) (n : nat) : (term69 m n) = (term69 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem186208 (m : nat) : (term70 m) = (term70 m).
Proof. exact (fun_ext (fun n : nat => @lem186207 m n)). Qed.
Lemma lem186209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186210 (m : nat) : (term71 m) = (term71 m).
Proof. exact (MK_COMB (@lem186209) (@lem186208 m)). Qed.
Lemma lem186211 : term72 = term72.
Proof. exact (fun_ext (fun m : nat => @lem186210 m)). Qed.
Lemma lem186212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186213 : term53 = term53.
Proof. exact (MK_COMB (@lem186212) (@lem186211)). Qed.
Lemma lem186214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem186215 : term52 = term52.
Proof. exact (MK_COMB (@lem186214) (@lem186213)). Qed.
Lemma lem186220 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem186221 (m : nat) (n : nat) : (term56 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem186220 m n) (@lem186215)). Qed.
Lemma lem186224 (m : nat) (n : nat) : (term57 m n) = (term57 m n).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem186225 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem186224 m n) (@lem186221 m n)). Qed.
Lemma lem186230 (n : nat) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem186231 (m : nat) (n : nat) : (term60 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem186230 n) (@lem186225 m n)). Qed.
Lemma lem186232 (n : nat) : (term62 n) = (term62 n).
Proof. exact (fun_ext (fun m : nat => @lem186231 m n)). Qed.
Lemma lem186233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186234 (n : nat) : (term64 n) = (term64 n).
Proof. exact (MK_COMB (@lem186233) (@lem186232 n)). Qed.
Lemma lem186235 : term66 = term66.
Proof. exact (fun_ext (fun n : nat => @lem186234 n)). Qed.
Lemma lem186236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186237 : term68 = term68.
Proof. exact (MK_COMB (@lem186236) (@lem186235)). Qed.
Lemma lem186274 : term67 = term68.
Proof. exact (TRANS (@lem186196) (@lem186237)). Qed.
Lemma lem186275 : term68 = term67.
Proof. exact (SYM (@lem186274)). Qed.
Lemma lem186279 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem186285 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem186297 (m : nat) (n : nat) (h1 : term46 m n) : term46 m n.
Proof. exact (h1). Qed.
Lemma lem186300 (n : nat) : (term73 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem186305 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem186306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem186307 (n : nat) : (term75 n) = (term76 n).
Proof. exact (MK_COMB (@lem186306) (@lem186300 n)). Qed.
Lemma lem186308 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem186307 n) (@lem186305 m n)). Qed.
Lemma lem186309 (m : nat) (n : nat) : (term69 m n) = (term77 m n).
Proof. exact (@lem17265 (term22 n) (term74 m n)). Qed.
Lemma lem186310 (m : nat) (n : nat) : (term69 m n) = (term78 m n).
Proof. exact (TRANS (@lem186309 m n) (@lem186308 m n)). Qed.
Lemma lem186311 (m : nat) : (term70 m) = (term79 m).
Proof. exact (fun_ext (fun n : nat => @lem186310 m n)). Qed.
Lemma lem186312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186313 (m : nat) : (term71 m) = (term80 m).
Proof. exact (MK_COMB (@lem186312) (@lem186311 m)). Qed.
Lemma lem186314 : term72 = term81.
Proof. exact (fun_ext (fun m : nat => @lem186313 m)). Qed.
Lemma lem186315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186372 : term53 = term82.
Proof. exact (MK_COMB (@lem186315) (@lem186314)). Qed.
Lemma lem186373 (h1 : term53) : term82.
Proof. exact (EQ_MP (@lem186372) (@lem186279 h1)). Qed.
Lemma lem186383 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem186419 (m : nat) (n : nat) (h1 : term46 m n) : term46 m n.
Proof. exact (h1). Qed.
Lemma lem186462 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem186463 (m : nat) : (term79 m) = (term79 m).
Proof. exact (fun_ext (fun n : nat => @lem186462 m n)). Qed.
Lemma lem186464 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186465 (m : nat) : (term80 m) = (term80 m).
Proof. exact (MK_COMB (@lem186464) (@lem186463 m)). Qed.
Lemma lem186466 : term81 = term81.
Proof. exact (fun_ext (fun m : nat => @lem186465 m)). Qed.
Lemma lem186467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186468 : term82 = term82.
Proof. exact (MK_COMB (@lem186467) (@lem186466)). Qed.
Lemma lem186469 (h1 : term53) : term82.
Proof. exact (EQ_MP (@lem186468) (@lem186373 h1)). Qed.
Lemma lem186473 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem186481 (m : nat) (n : nat) (h1 : term46 m n) : term46 m n.
Proof. exact (h1). Qed.
Lemma lem186499 (m : nat) (n : nat) : (term78 m n) = (term83 m n).
Proof. exact (@lem19490 (m = (term41 m n)) (n = (NUMERAL 0)) (term84 m n)). Qed.
Lemma lem186500 (m : nat) : (term79 m) = (term85 m).
Proof. exact (fun_ext (fun n : nat => @lem186499 m n)). Qed.
Lemma lem186501 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186502 (m : nat) : (term80 m) = (term86 m).
Proof. exact (MK_COMB (@lem186501) (@lem186500 m)). Qed.
Lemma lem186503 : term81 = term87.
Proof. exact (fun_ext (fun m : nat => @lem186502 m)). Qed.
Lemma lem186504 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem186506 : term82 = term88.
Proof. exact (MK_COMB (@lem186504) (@lem186503)). Qed.
Lemma lem186507 (h1 : term53) : term88.
Proof. exact (EQ_MP (@lem186506) (@lem186469 h1)). Qed.
Lemma lem186508 (_3777 : nat) (h1 : term53) : term89 _3777.
Proof. exact (@lem186507 h1 _3777). Qed.
Lemma lem186509 (_3777 : nat) : (term89 _3777) = (term86 _3777).
Proof. exact (eq_refl (term89 _3777)). Qed.
Lemma lem186510 (_3777 : nat) (h1 : term53) : term86 _3777.
Proof. exact (EQ_MP (@lem186509 _3777) (@lem186508 _3777 h1)). Qed.
Lemma lem186511 (_3777 : nat) (_3778 : nat) (h1 : term53) : term90 _3777 _3778.
Proof. exact (@lem186510 _3777 h1 _3778). Qed.
Lemma lem186512 (_3777 : nat) (_3778 : nat) : (term90 _3777 _3778) = (term83 _3777 _3778).
Proof. exact (eq_refl (term90 _3777 _3778)). Qed.
Lemma lem186513 (_3777 : nat) (_3778 : nat) (h1 : term53) : term83 _3777 _3778.
Proof. exact (EQ_MP (@lem186512 _3777 _3778) (@lem186511 _3777 _3778 h1)). Qed.
Lemma lem186517 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem186521 (m : nat) (n : nat) (h1 : term46 m n) : term46 m n.
Proof. exact (h1). Qed.
Lemma lem186527 (_3777 : nat) (_3778 : nat) (h1 : term53) : term91 _3777 _3778.
Proof. exact (proj1 (@lem186513 _3777 _3778 h1)). Qed.
Lemma lem186624 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem186625 (n : nat) (h1 : term22 n) : term92 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem186624 n h1). Qed.
Lemma lem186627 (p : Prop) : (term93 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem186628 (n : nat) : (term92 n) = (term22 n).
Proof. exact (@lem186627 (n = (NUMERAL 0))). Qed.
Lemma lem186629 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (EQ_MP (@lem186628 n) (@lem186625 n h1)). Qed.
Lemma lem186635 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem186636 (_3777 : nat) (_3778 : nat) : (term91 _3777 _3778) = (term94 _3777 _3778).
Proof. exact (@lem186635 (_3777 = (term41 _3777 _3778)) (_3778 = (NUMERAL 0))). Qed.
Lemma lem186646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem186647 (_3777 : nat) (_3778 : nat) : (term95 _3777 _3778) = (term96 _3777 _3778).
Proof. exact (MK_COMB (@lem186646) (@lem186636 _3777 _3778)). Qed.
Lemma lem186657 (_3777 : nat) (_3778 : nat) : (term94 _3777 _3778) = (term94 _3777 _3778).
Proof. exact (eq_refl (term94 _3777 _3778)). Qed.
Lemma lem186658 (_3777 : nat) (_3778 : nat) : ((term91 _3777 _3778) = (term94 _3777 _3778)) = ((term94 _3777 _3778) = (term94 _3777 _3778)).
Proof. exact (MK_COMB (@lem186647 _3777 _3778) (@lem186657 _3777 _3778)). Qed.
Lemma lem186660 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem186661 (x : Prop) : (x = x) = True.
Proof. exact (@lem186660 Prop x). Qed.
Lemma lem186662 (_3777 : nat) (_3778 : nat) : ((term94 _3777 _3778) = (term94 _3777 _3778)) = True.
Proof. exact (@lem186661 (term94 _3777 _3778)). Qed.
Lemma lem186663 (_3777 : nat) (_3778 : nat) : ((term91 _3777 _3778) = (term94 _3777 _3778)) = True.
Proof. exact (TRANS (@lem186658 _3777 _3778) (@lem186662 _3777 _3778)). Qed.
Lemma lem186664 (_3777 : nat) (_3778 : nat) : True = ((term91 _3777 _3778) = (term94 _3777 _3778)).
Proof. exact (SYM (@lem186663 _3777 _3778)). Qed.
Lemma lem186665 (_3777 : nat) (_3778 : nat) : (term91 _3777 _3778) = (term94 _3777 _3778).
Proof. exact (EQ_MP (@lem186664 _3777 _3778) (@lem0)). Qed.
Lemma lem186666 (_3777 : nat) (_3778 : nat) (h1 : term53) : term94 _3777 _3778.
Proof. exact (EQ_MP (@lem186665 _3777 _3778) (@lem186527 _3777 _3778 h1)). Qed.
Lemma lem186668 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem186671 (_3777 : nat) (_3778 : nat) : (term94 _3777 _3778) = (term98 _3777 _3778).
Proof. exact (@lem186668 (_3778 = (NUMERAL 0)) (_3777 = (term41 _3777 _3778))). Qed.
Lemma lem186674 (_3777 : nat) (_3778 : nat) (h1 : term53) : term98 _3777 _3778.
Proof. exact (EQ_MP (@lem186671 _3777 _3778) (@lem186666 _3777 _3778 h1)). Qed.
Lemma lem186675 (_3777 : nat) (n : nat) (h1 : term53) : term98 _3777 n.
Proof. exact (@lem186674 _3777 n h1). Qed.
Lemma lem186678 (_3777 : nat) (n : nat) (h1 : term53) (h2 : term22 n) : _3777 = (term41 _3777 n).
Proof. exact (@lem186675 _3777 n h1 (@lem186629 n h2)). Qed.
Lemma lem186679 (m : nat) (n : nat) (h1 : term53) (h2 : term22 n) : m = (term41 m n).
Proof. exact (@lem186678 m n h1 h2). Qed.
Lemma lem186680 (m : nat) (n : nat) (h1 : term53) (h2 : term22 n) : term99 m n.
Proof. exact (fun h0 : term46 m n => @lem186679 m n h1 h2). Qed.
Lemma lem186682 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem186683 (m : nat) (n : nat) : (term99 m n) = (m = (term41 m n)).
Proof. exact (@lem186682 (m = (term41 m n))). Qed.
Lemma lem186684 (m : nat) (n : nat) (h1 : term53) (h2 : term22 n) : m = (term41 m n).
Proof. exact (EQ_MP (@lem186683 m n) (@lem186680 m n h1 h2)). Qed.
Lemma lem186687 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem186689 (m : nat) (n : nat) : (term46 m n) = (term101 m n).
Proof. exact (@lem186687 (m = (term41 m n))). Qed.
Lemma lem186692 (m : nat) (n : nat) (h1 : term46 m n) : term101 m n.
Proof. exact (EQ_MP (@lem186689 m n) (@lem186521 m n h1)). Qed.
Lemma lem186695 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (@lem186692 m n h2 (@lem186684 m n h1 h3)). Qed.
Lemma lem186696 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : term102.
Proof. exact (fun h0 : ~ False => @lem186695 m n h1 h2 h3). Qed.
Lemma lem186698 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem186699 : term102 = False.
Proof. exact (@lem186698 False). Qed.
Lemma lem186700 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186699) (@lem186696 m n h1 h2 h3)). Qed.
Lemma lem186701 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term46 m n) = False.
Proof. exact (prop_ext (fun h4 : term46 m n => @lem186700 m n h1 h2 h3) (fun h4 : False => @lem186521 m n h2)). Qed.
Lemma lem186702 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186701 m n h1 h2 h3) (@lem186521 m n h2)). Qed.
Lemma lem186703 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term22 n) = False.
Proof. exact (prop_ext (fun h4 : term22 n => @lem186702 m n h1 h2 h3) (fun h4 : False => @lem186517 n h3)). Qed.
Lemma lem186704 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186703 m n h1 h2 h3) (@lem186517 n h3)). Qed.
Lemma lem186705 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term46 m n) = False.
Proof. exact (prop_ext (fun h4 : term46 m n => @lem186704 m n h1 h2 h3) (fun h4 : False => @lem186481 m n h2)). Qed.
Lemma lem186706 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186705 m n h1 h2 h3) (@lem186481 m n h2)). Qed.
Lemma lem186707 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term22 n) = False.
Proof. exact (prop_ext (fun h4 : term22 n => @lem186706 m n h1 h2 h3) (fun h4 : False => @lem186473 n h3)). Qed.
Lemma lem186708 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186707 m n h1 h2 h3) (@lem186473 n h3)). Qed.
Lemma lem186709 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term46 m n) = False.
Proof. exact (prop_ext (fun h4 : term46 m n => @lem186708 m n h1 h2 h3) (fun h4 : False => @lem186481 m n h2)). Qed.
Lemma lem186710 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186709 m n h1 h2 h3) (@lem186481 m n h2)). Qed.
Lemma lem186711 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term22 n) = False.
Proof. exact (prop_ext (fun h4 : term22 n => @lem186710 m n h1 h2 h3) (fun h4 : False => @lem186473 n h3)). Qed.
Lemma lem186712 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186711 m n h1 h2 h3) (@lem186473 n h3)). Qed.
Lemma lem186713 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term46 m n) = False.
Proof. exact (prop_ext (fun h4 : term46 m n => @lem186712 m n h1 h2 h3) (fun h4 : False => @lem186419 m n h2)). Qed.
Lemma lem186714 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186713 m n h1 h2 h3) (@lem186419 m n h2)). Qed.
Lemma lem186715 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term22 n) = False.
Proof. exact (prop_ext (fun h4 : term22 n => @lem186714 m n h1 h2 h3) (fun h4 : False => @lem186383 n h3)). Qed.
Lemma lem186716 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186715 m n h1 h2 h3) (@lem186383 n h3)). Qed.
Lemma lem186717 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term46 m n) = False.
Proof. exact (prop_ext (fun h4 : term46 m n => @lem186716 m n h1 h2 h3) (fun h4 : False => @lem186297 m n h2)). Qed.
Lemma lem186718 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186717 m n h1 h2 h3) (@lem186297 m n h2)). Qed.
Lemma lem186719 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : (term22 n) = False.
Proof. exact (prop_ext (fun h4 : term22 n => @lem186718 m n h1 h2 h3) (fun h4 : False => @lem186285 n h3)). Qed.
Lemma lem186720 (m : nat) (n : nat) (h1 : term53) (h2 : term46 m n) (h3 : term22 n) : False.
Proof. exact (EQ_MP (@lem186719 m n h1 h2 h3) (@lem186285 n h3)). Qed.
Lemma lem186721 (m : nat) (n : nat) (h1 : term46 m n) (h2 : term22 n) : term51.
Proof. exact (fun h0 : term53 => @lem186720 m n h0 h1 h2). Qed.
Lemma lem186722 : term51 = term52.
Proof. exact (@lem69 term53). Qed.
Lemma lem186723 (m : nat) (n : nat) (h1 : term46 m n) (h2 : term22 n) : term52.
Proof. exact (EQ_MP (@lem186722) (@lem186721 m n h1 h2)). Qed.
Lemma lem186724 (m : nat) (n : nat) (h1 : term22 n) : term56 m n.
Proof. exact (fun h0 : term46 m n => @lem186723 m n h0 h1). Qed.
Lemma lem186725 (m : nat) (n : nat) (h1 : term22 n) : term59 m n.
Proof. exact (fun h0 : (Nat.modulo m n) = (NUMERAL 0) => @lem186724 m n h1). Qed.
Lemma lem186726 (m : nat) (n : nat) : term60 m n.
Proof. exact (fun h0 : term22 n => @lem186725 m n h0). Qed.
Lemma lem186731 (n : nat) : term64 n.
Proof. exact (fun m : nat => @lem186726 m n). Qed.
Lemma lem186736 : term68.
Proof. exact (fun n : nat => @lem186731 n). Qed.
Lemma lem186737 : term67.
Proof. exact (EQ_MP (@lem186275) (@lem186736)). Qed.
Lemma lem186738 (n : nat) : term103 n.
Proof. exact (@lem186737 n). Qed.
Lemma lem186739 (n : nat) : (term103 n) = (term63 n).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem186740 (n : nat) : term63 n.
Proof. exact (EQ_MP (@lem186739 n) (@lem186738 n)). Qed.
Lemma lem186741 (n : nat) (m : nat) : term104 n m.
Proof. exact (@lem186740 n m). Qed.
Lemma lem186742 (m : nat) (n : nat) : (term104 n m) = (term47 m n).
Proof. exact (eq_refl (term104 n m)). Qed.
Lemma lem186743 (m : nat) (n : nat) : term47 m n.
Proof. exact (EQ_MP (@lem186742 m n) (@lem186741 n m)). Qed.
Lemma lem186745 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem186137 m n (@lem186743 m n)). Qed.
Lemma lem186746 (m : nat) (n : nat) (h1 : term22 n) : term58 m n.
Proof. exact (@lem186745 m n (@lem185883 n h1)). Qed.
Lemma lem186747 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : term55 m n.
Proof. exact (@lem186746 m n h1 (@lem186040 m n h2)). Qed.
Lemma lem186748 (m : nat) (n : nat) (h1 : term46 m n) (h2 : term22 n) (h3 : (Nat.modulo m n) = (NUMERAL 0)) : term51.
Proof. exact (@lem186747 m n h2 h3 (@lem186122 m n h1)). Qed.
Lemma lem186749 (m : nat) (n : nat) (h1 : term46 m n) (h2 : term22 n) (h3 : (Nat.modulo m n) = (NUMERAL 0)) : False.
Proof. exact (@lem186748 m n h1 h2 h3 (@lem157261)). Qed.
Lemma lem186750 (m : nat) (n : nat) (h1 : term46 m n) (h2 : term22 n) (h3 : (Nat.modulo m n) = (NUMERAL 0)) : (term46 m n) = False.
Proof. exact (prop_ext (fun h4 : term46 m n => @lem186749 m n h1 h2 h3) (fun h4 : False => @lem186122 m n h1)). Qed.
Lemma lem186751 (m : nat) (n : nat) (h1 : term46 m n) (h2 : term22 n) (h3 : (Nat.modulo m n) = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem186750 m n h1 h2 h3) (@lem186122 m n h1)). Qed.
Lemma lem186752 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : term45 m n.
Proof. exact (fun h0 : term46 m n => @lem186751 m n h0 h1 h2). Qed.
Lemma lem186753 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : m = (term41 m n).
Proof. exact (EQ_MP (@lem186121 m n) (@lem186752 m n h1 h2)). Qed.
Lemma lem186758 : term105.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem186774 : term106.
Proof. exact (proj1 (@lem186758)). Qed.
Lemma lem186775 (m : nat) : term107 m.
Proof. exact (@lem186774 m). Qed.
Lemma lem186776 (m : nat) : (term107 m) = ((term108 m) = m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem186798 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem186799 (m : nat) (n : nat) : (term109 m n) = (term43 m n).
Proof. exact (@lem186798 n (Nat.div m n)). Qed.
Lemma lem186803 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem186804 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem186803) (@lem186799 m n)). Qed.
Lemma lem186806 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem186807 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term41 m n) = (term112 m n).
Proof. exact (MK_COMB (@lem186804 m n) (@lem186806 m n h1)). Qed.
Lemma lem186809 (m : nat) : (term108 m) = m.
Proof. exact (EQ_MP (@lem186776 m) (@lem186775 m)). Qed.
Lemma lem186810 (m : nat) (n : nat) : (term112 m n) = (term43 m n).
Proof. exact (@lem186809 (term43 m n)). Qed.
Lemma lem186814 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term41 m n) = (term43 m n).
Proof. exact (TRANS (@lem186807 m n h1) (@lem186810 m n)). Qed.
Lemma lem186815 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem186816 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term42 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem186815) (@lem186814 m n h1)). Qed.
Lemma lem186820 (m : nat) (n : nat) : (term43 m n) = (term43 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem186821 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : ((term41 m n) = (term43 m n)) = ((term43 m n) = (term43 m n)).
Proof. exact (MK_COMB (@lem186816 m n h1) (@lem186820 m n)). Qed.
Lemma lem186823 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem186824 (x : nat) : (x = x) = True.
Proof. exact (@lem186823 nat x). Qed.
Lemma lem186825 (m : nat) (n : nat) : ((term43 m n) = (term43 m n)) = True.
Proof. exact (@lem186824 (term43 m n)). Qed.
Lemma lem186826 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : ((term41 m n) = (term43 m n)) = True.
Proof. exact (TRANS (@lem186821 m n h1) (@lem186825 m n)). Qed.
Lemma lem186827 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : True = ((term41 m n) = (term43 m n)).
Proof. exact (SYM (@lem186826 m n h1)). Qed.
Lemma lem186828 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term41 m n) = (term43 m n).
Proof. exact (EQ_MP (@lem186827 m n h1) (@lem0)). Qed.
Lemma lem186829 (m : nat) (n : nat) (h1 : m = (term41 m n)) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : m = (term43 m n).
Proof. exact (EQ_MP (@lem186117 m n h1) (@lem186828 m n h2)). Qed.
Lemma lem186830 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : (m = (term41 m n)) = (m = (term43 m n)).
Proof. exact (prop_ext (fun h3 : m = (term41 m n) => @lem186829 m n h3 h2) (fun h3 : m = (term43 m n) => @lem186753 m n h1 h2)). Qed.
Lemma lem186831 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : m = (term43 m n).
Proof. exact (EQ_MP (@lem186830 m n h1 h2) (@lem186753 m n h1 h2)). Qed.
Lemma lem186833 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : term8 m n.
Proof. exact (ex_intro (term27 m n) (Nat.div m n) (@lem186831 m n h1 h2)). Qed.
Lemma lem186834 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : ((Nat.modulo m n) = (NUMERAL 0)) = (term8 m n).
Proof. exact (prop_ext (fun h3 : (Nat.modulo m n) = (NUMERAL 0) => @lem186833 m n h1 h2) (fun h3 : term8 m n => @lem186040 m n h2)). Qed.
Lemma lem186835 (m : nat) (n : nat) (h1 : term22 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : term8 m n.
Proof. exact (EQ_MP (@lem186834 m n h1 h2) (@lem186040 m n h2)). Qed.
Lemma lem186836 (m : nat) (n : nat) (h1 : term22 n) : term114 m n.
Proof. exact (fun h0 : (Nat.modulo m n) = (NUMERAL 0) => @lem186835 m n h1 h0). Qed.
Lemma lem186837 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (m = (Nat.mul n q)) = ((Nat.modulo m n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : m = (Nat.mul n q) => @lem186082 m n q h1) (fun h2 : (Nat.modulo m n) = (NUMERAL 0) => @lem186039 m n q h1)). Qed.
Lemma lem186838 (m : nat) (n : nat) (q : nat) (h1 : m = (Nat.mul n q)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem186837 m n q h1) (@lem186039 m n q h1)). Qed.
Lemma lem186839 (m : nat) (n : nat) (h1 : term8 m n) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (ex_elim (@lem186038 m n h1) (fun q : nat => fun h0 : term27 m n q => @lem186838 m n q h0)). Qed.
Lemma lem186840 (m : nat) (n : nat) : term115 m n.
Proof. exact (fun h0 : term8 m n => @lem186839 m n h0). Qed.
Lemma lem186841 (m : nat) (n : nat) (h1 : term22 n) : term116 m n.
Proof. exact (conj (@lem186840 m n) (@lem186836 m n h1)). Qed.
Lemma lem186842 (m : nat) (n : nat) : (term116 m n) = ((term8 m n) = ((Nat.modulo m n) = (NUMERAL 0))).
Proof. exact (@lem32 (term8 m n) ((Nat.modulo m n) = (NUMERAL 0))). Qed.
Lemma lem186845 (m : nat) (n : nat) (h1 : term22 n) : (term8 m n) = ((Nat.modulo m n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem186842 m n) (@lem186841 m n h1)). Qed.
Lemma lem186846 (m : nat) (n : nat) (h1 : term22 n) : (term22 n) = ((term8 m n) = ((Nat.modulo m n) = (NUMERAL 0))).
Proof. exact (prop_ext (fun h2 : term22 n => @lem186845 m n h1) (fun h2 : (term8 m n) = ((Nat.modulo m n) = (NUMERAL 0)) => @lem185883 n h1)). Qed.
Lemma lem186847 (m : nat) (n : nat) (h1 : term22 n) : (term8 m n) = ((Nat.modulo m n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem186846 m n h1) (@lem185883 n h1)). Qed.
Lemma lem186848 (m : nat) (n : nat) : term11 m n.
Proof. exact (fun h0 : term22 n => @lem186847 m n h0). Qed.
Lemma lem186849 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term8 m n) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem185977 m n h1) (@lem0)). Qed.
Lemma lem186850 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((term8 m n) = (m = (NUMERAL 0))).
Proof. exact (prop_ext (fun h2 : n = (NUMERAL 0) => @lem186849 m n h1) (fun h2 : (term8 m n) = (m = (NUMERAL 0)) => @lem185866 n h1)). Qed.
Lemma lem186851 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term8 m n) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem186850 m n h1) (@lem185866 n h1)). Qed.
Lemma lem186852 (n : nat) (m : nat) : term15 n m.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem186851 m n h0). Qed.
Lemma lem186853 (m : nat) (n : nat) : term18 m n.
Proof. exact (conj (@lem186852 n m) (@lem186848 m n)). Qed.
Lemma lem186854 (m : nat) (n : nat) : (term8 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem185865 m n) (@lem186853 m n)). Qed.
Lemma lem186859 (m : nat) : term117 m.
Proof. exact (fun n : nat => @lem186854 m n). Qed.
Lemma lem186864 : term118.
Proof. exact (fun m : nat => @lem186859 m). Qed.
