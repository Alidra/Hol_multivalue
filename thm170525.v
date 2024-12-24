Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm170525_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import AND_FORALL_THM_spec.
Require Import DIVMOD_UNIQ_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LT_NZ_spec.
Require Import MOD_0_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem170052 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem170053 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem170052 h1 m). Qed.
Lemma lem170054 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem170055 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem170054 m) (@lem170053 m h1)). Qed.
Lemma lem170056 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem170055 m h1 n). Qed.
Lemma lem170057 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem170058 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem170057 m n) (@lem170056 m n h1)). Qed.
Lemma lem170059 (m : nat) (n : nat) (q : nat) (h1 : term0) : term5 m n q.
Proof. exact (@lem170058 m n h1 q). Qed.
Lemma lem170060 (q : nat) (m : nat) (n : nat) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem170061 (q : nat) (m : nat) (n : nat) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem170060 q m n) (@lem170059 m n q h1)). Qed.
Lemma lem170062 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term7 q m n r.
Proof. exact (@lem170061 q m n h1 r). Qed.
Lemma lem170063 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem170064 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem170063 q m n r) (@lem170062 q m n r h1)). Qed.
Lemma lem170065 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem170066 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem170064 q m n r h1 (@lem170065 m q r n h2)). Qed.
Lemma lem170067 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term11 q m n r.
Proof. exact (fun h0 : term0 => @lem170066 m q r n h0 h1). Qed.
Lemma lem170068 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem170069 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem170067 m q r n h2 (@lem170068 h1)). Qed.
Lemma lem170070 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term8 q m n r.
Proof. exact (fun h0 : term9 m q r n => @lem170069 m q r n h1 h0). Qed.
Lemma lem170071 (q : nat) (m : nat) (n : nat) (h1 : term0) : term6 q m n.
Proof. exact (fun r : nat => @lem170070 q m n r h1). Qed.
Lemma lem170072 (q : nat) (m : nat) (h1 : term0) : term12 q m.
Proof. exact (fun n : nat => @lem170071 q m n h1). Qed.
Lemma lem170073 (q : nat) (h1 : term0) : term13 q.
Proof. exact (fun m : nat => @lem170072 q m h1). Qed.
Lemma lem170074 (h1 : term0) : term14.
Proof. exact (fun q : nat => @lem170073 q h1). Qed.
Lemma lem170075 : term15.
Proof. exact (fun h0 : term0 => @lem170074 h0). Qed.
Lemma lem170076 : term14.
Proof. exact (@lem170075 (@lem169651)). Qed.
Lemma lem170077 (q : nat) : term16 q.
Proof. exact (@lem170076 q). Qed.
Lemma lem170078 (q : nat) : (term16 q) = (term13 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem170079 (q : nat) : term13 q.
Proof. exact (EQ_MP (@lem170078 q) (@lem170077 q)). Qed.
Lemma lem170080 (q : nat) (m : nat) : term17 q m.
Proof. exact (@lem170079 q m). Qed.
Lemma lem170081 (q : nat) (m : nat) : (term17 q m) = (term12 q m).
Proof. exact (eq_refl (term17 q m)). Qed.
Lemma lem170082 (q : nat) (m : nat) : term12 q m.
Proof. exact (EQ_MP (@lem170081 q m) (@lem170080 q m)). Qed.
Lemma lem170083 (q : nat) (m : nat) (n : nat) : term18 q m n.
Proof. exact (@lem170082 q m n). Qed.
Lemma lem170084 (q : nat) (m : nat) (n : nat) : (term18 q m n) = (term6 q m n).
Proof. exact (eq_refl (term18 q m n)). Qed.
Lemma lem170085 (q : nat) (m : nat) (n : nat) : term6 q m n.
Proof. exact (EQ_MP (@lem170084 q m n) (@lem170083 q m n)). Qed.
Lemma lem170086 (q : nat) (m : nat) (n : nat) (r : nat) : term7 q m n r.
Proof. exact (@lem170085 q m n r). Qed.
Lemma lem170087 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem170089 (m : nat) : term19 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem170090 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem170091 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem170090 m) (@lem170089 m)). Qed.
Lemma lem170093 (m : nat) (h1 : term21 m) : term21 m.
Proof. exact (h1). Qed.
Lemma lem170094 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem170095 {A : Type'} (P : A -> Prop) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem170096 {A : Type'} (P : A -> Prop) : term23 A P.
Proof. exact (EQ_MP (@lem170095 A P) (@lem170094 A P)). Qed.
Lemma lem170097 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term24 A P Q.
Proof. exact (@lem170096 A P Q). Qed.
Lemma lem170098 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term24 A P Q) = ((term25 A P Q) = (term26 A P Q)).
Proof. exact (eq_refl (term24 A P Q)). Qed.
Lemma lem170101 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term25 A P Q) = (term26 A P Q).
Proof. exact (EQ_MP (@lem170098 A P Q) (@lem170097 A P Q)). Qed.
Lemma lem170102 (P : nat -> Prop) (Q : nat -> Prop) : (term27 P Q) = (term28 P Q).
Proof. exact (@lem170101 nat P Q). Qed.
Lemma lem170103 : term29 = term30.
Proof. exact (@lem170102 term31 term32). Qed.
Lemma lem170104 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem170105 : term35 = term31.
Proof. exact (fun_ext (fun m : nat => @lem170104 m)). Qed.
Lemma lem170106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170107 : term36 = term37.
Proof. exact (MK_COMB (@lem170106) (@lem170105)). Qed.
Lemma lem170108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170109 : term38 = term39.
Proof. exact (MK_COMB (@lem170108) (@lem170107)). Qed.
Lemma lem170110 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem170111 : term42 = term32.
Proof. exact (fun_ext (fun m : nat => @lem170110 m)). Qed.
Lemma lem170112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170113 : term43 = term44.
Proof. exact (MK_COMB (@lem170112) (@lem170111)). Qed.
Lemma lem170114 : term29 = term45.
Proof. exact (MK_COMB (@lem170109) (@lem170113)). Qed.
Lemma lem170115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem170116 : term46 = term47.
Proof. exact (MK_COMB (@lem170115) (@lem170114)). Qed.
Lemma lem170117 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem170118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170119 (m : nat) : (term48 m) = (term49 m).
Proof. exact (MK_COMB (@lem170118) (@lem170117 m)). Qed.
Lemma lem170120 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem170121 (m : nat) : (term50 m) = (term51 m).
Proof. exact (MK_COMB (@lem170119 m) (@lem170120 m)). Qed.
Lemma lem170122 : term52 = term53.
Proof. exact (fun_ext (fun m : nat => @lem170121 m)). Qed.
Lemma lem170123 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170124 : term30 = term54.
Proof. exact (MK_COMB (@lem170123) (@lem170122)). Qed.
Lemma lem170125 : (term29 = term30) = (term45 = term54).
Proof. exact (MK_COMB (@lem170116) (@lem170124)). Qed.
Lemma lem170126 : term45 = term54.
Proof. exact (EQ_MP (@lem170125) (@lem170103)). Qed.
Lemma lem170132 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term25 A P Q) = (term26 A P Q).
Proof. exact (EQ_MP (@lem170098 A P Q) (@lem170097 A P Q)). Qed.
Lemma lem170133 (P : nat -> Prop) (Q : nat -> Prop) : (term27 P Q) = (term28 P Q).
Proof. exact (@lem170132 nat P Q). Qed.
Lemma lem170134 (m : nat) : (term55 m) = (term56 m).
Proof. exact (@lem170133 (term57 m) (term58 m)). Qed.
Lemma lem170135 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem170136 (m : nat) : (term61 m) = (term57 m).
Proof. exact (fun_ext (fun n : nat => @lem170135 m n)). Qed.
Lemma lem170137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170138 (m : nat) : (term62 m) = (term34 m).
Proof. exact (MK_COMB (@lem170137) (@lem170136 m)). Qed.
Lemma lem170139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170140 (m : nat) : (term63 m) = (term49 m).
Proof. exact (MK_COMB (@lem170139) (@lem170138 m)). Qed.
Lemma lem170141 (n : nat) (m : nat) : (term64 m n) = ((term65 n m) = (NUMERAL 0)).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem170142 (m : nat) : (term66 m) = (term58 m).
Proof. exact (fun_ext (fun n : nat => @lem170141 n m)). Qed.
Lemma lem170143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170144 (m : nat) : (term67 m) = (term41 m).
Proof. exact (MK_COMB (@lem170143) (@lem170142 m)). Qed.
Lemma lem170145 (m : nat) : (term55 m) = (term51 m).
Proof. exact (MK_COMB (@lem170140 m) (@lem170144 m)). Qed.
Lemma lem170146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem170147 (m : nat) : (term68 m) = (term69 m).
Proof. exact (MK_COMB (@lem170146) (@lem170145 m)). Qed.
Lemma lem170148 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem170149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170150 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem170149) (@lem170148 m n)). Qed.
Lemma lem170151 (n : nat) (m : nat) : (term64 m n) = ((term65 n m) = (NUMERAL 0)).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem170152 (n : nat) (m : nat) : (term72 m n) = (term73 n m).
Proof. exact (MK_COMB (@lem170150 m n) (@lem170151 n m)). Qed.
Lemma lem170153 (m : nat) : (term74 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem170152 n m)). Qed.
Lemma lem170154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170155 (m : nat) : (term56 m) = (term76 m).
Proof. exact (MK_COMB (@lem170154) (@lem170153 m)). Qed.
Lemma lem170156 (m : nat) : ((term55 m) = (term56 m)) = ((term51 m) = (term76 m)).
Proof. exact (MK_COMB (@lem170147 m) (@lem170155 m)). Qed.
Lemma lem170157 (m : nat) : (term51 m) = (term76 m).
Proof. exact (EQ_MP (@lem170156 m) (@lem170134 m)). Qed.
Lemma lem170172 : term53 = term77.
Proof. exact (fun_ext (fun m : nat => @lem170157 m)). Qed.
Lemma lem170173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170174 : term54 = term78.
Proof. exact (MK_COMB (@lem170173) (@lem170172)). Qed.
Lemma lem170179 : term45 = term78.
Proof. exact (TRANS (@lem170126) (@lem170174)). Qed.
Lemma lem170180 : term78 = term45.
Proof. exact (SYM (@lem170179)). Qed.
Lemma lem170181 (n : nat) : term79 n.
Proof. exact (@lem170050 n). Qed.
Lemma lem170182 (n : nat) : (term79 n) = ((term80 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term79 n)). Qed.
Lemma lem170214 : term81.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem170215 (n : nat) : term82 n.
Proof. exact (@lem170214 n). Qed.
Lemma lem170216 (n : nat) : (term82 n) = ((term83 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem170225 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem170226 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem170227 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term84.
Proof. exact (MK_COMB (@lem170226) (@lem170225 m h1)). Qed.
Lemma lem170228 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem170229 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem170227 m h1) (@lem170228)). Qed.
Lemma lem170231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem170232 (x : nat) : (x = x) = True.
Proof. exact (@lem170231 nat x). Qed.
Lemma lem170233 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem170232 (NUMERAL 0)). Qed.
Lemma lem170234 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem170229 m h1) (@lem170233)). Qed.
Lemma lem170235 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem170236 (m : nat) (h1 : m = (NUMERAL 0)) : (term21 m) = (~ True).
Proof. exact (MK_COMB (@lem170235) (@lem170234 m h1)). Qed.
Lemma lem170238 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem170239 (m : nat) (h1 : m = (NUMERAL 0)) : (term21 m) = False.
Proof. exact (TRANS (@lem170236 m h1) (@lem170238)). Qed.
Lemma lem170240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem170241 (m : nat) (h1 : m = (NUMERAL 0)) : (term85 m) = (imp False).
Proof. exact (MK_COMB (@lem170240) (@lem170239 m h1)). Qed.
Lemma lem170245 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem170246 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem170247 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m) = term86.
Proof. exact (MK_COMB (@lem170246) (@lem170245 m h1)). Qed.
Lemma lem170248 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem170249 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m n) = (term83 n).
Proof. exact (MK_COMB (@lem170247 m h1) (@lem170248 n)). Qed.
Lemma lem170251 (n : nat) : (term83 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem170216 n) (@lem170215 n)). Qed.
Lemma lem170252 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem170249 n m h1) (@lem170251 n)). Qed.
Lemma lem170253 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem170254 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term87 m n) = term88.
Proof. exact (MK_COMB (@lem170253) (@lem170252 n m h1)). Qed.
Lemma lem170256 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem170257 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term89 n m) = term90.
Proof. exact (MK_COMB (@lem170254 n m h1) (@lem170256 m h1)). Qed.
Lemma lem170258 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem170259 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term91 n m) = term92.
Proof. exact (MK_COMB (@lem170258) (@lem170257 n m h1)). Qed.
Lemma lem170260 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem170261 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term89 n m) = n) = (term90 = n).
Proof. exact (MK_COMB (@lem170259 n m h1) (@lem170260 n)). Qed.
Lemma lem170264 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term60 m n) = (term93 n).
Proof. exact (MK_COMB (@lem170241 m h1) (@lem170261 n m h1)). Qed.
Lemma lem170266 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem170267 (n : nat) : (term93 n) = True.
Proof. exact (@lem170266 (term90 = n)). Qed.
Lemma lem170268 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term60 m n) = True.
Proof. exact (TRANS (@lem170264 n m h1) (@lem170267 n)). Qed.
Lemma lem170269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170270 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term71 m n) = (and True).
Proof. exact (MK_COMB (@lem170269) (@lem170268 n m h1)). Qed.
Lemma lem170274 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem170275 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem170276 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m) = term86.
Proof. exact (MK_COMB (@lem170275) (@lem170274 m h1)). Qed.
Lemma lem170277 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem170278 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m n) = (term83 n).
Proof. exact (MK_COMB (@lem170276 m h1) (@lem170277 n)). Qed.
Lemma lem170280 (n : nat) : (term83 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem170216 n) (@lem170215 n)). Qed.
Lemma lem170281 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem170278 n m h1) (@lem170280 n)). Qed.
Lemma lem170282 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem170283 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term94 m n) = term95.
Proof. exact (MK_COMB (@lem170282) (@lem170281 n m h1)). Qed.
Lemma lem170285 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem170286 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term65 n m) = term96.
Proof. exact (MK_COMB (@lem170283 n m h1) (@lem170285 m h1)). Qed.
Lemma lem170288 (n : nat) : (term80 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem170182 n) (@lem170181 n)). Qed.
Lemma lem170289 : term96 = (NUMERAL 0).
Proof. exact (@lem170288 (NUMERAL 0)). Qed.
Lemma lem170290 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term65 n m) = (NUMERAL 0).
Proof. exact (TRANS (@lem170286 n m h1) (@lem170289)). Qed.
Lemma lem170291 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem170292 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term97 n m) = term84.
Proof. exact (MK_COMB (@lem170291) (@lem170290 n m h1)). Qed.
Lemma lem170293 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem170294 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term65 n m) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem170292 n m h1) (@lem170293)). Qed.
Lemma lem170296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem170297 (x : nat) : (x = x) = True.
Proof. exact (@lem170296 nat x). Qed.
Lemma lem170298 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem170297 (NUMERAL 0)). Qed.
Lemma lem170299 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term65 n m) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem170294 n m h1) (@lem170298)). Qed.
Lemma lem170300 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term73 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem170270 n m h1) (@lem170299 n m h1)). Qed.
Lemma lem170302 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem170303 : (True /\ True) = True.
Proof. exact (@lem170302 True). Qed.
Lemma lem170304 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term73 n m) = True.
Proof. exact (TRANS (@lem170300 n m h1) (@lem170303)). Qed.
Lemma lem170305 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : True = (term73 n m).
Proof. exact (SYM (@lem170304 n m h1)). Qed.
Lemma lem170306 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : term73 n m.
Proof. exact (EQ_MP (@lem170305 n m h1) (@lem0)). Qed.
Lemma lem170344 (m : nat) : term98 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem170362 (m : nat) (h1 : term21 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem170344 m (@lem170093 m h1)). Qed.
Lemma lem170363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem170364 (m : nat) (h1 : term21 m) : (term21 m) = (~ False).
Proof. exact (MK_COMB (@lem170363) (@lem170362 m h1)). Qed.
Lemma lem170366 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem170367 (m : nat) (h1 : term21 m) : (term21 m) = True.
Proof. exact (TRANS (@lem170364 m h1) (@lem170366)). Qed.
Lemma lem170368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem170369 (m : nat) (h1 : term21 m) : (term85 m) = (imp True).
Proof. exact (MK_COMB (@lem170368) (@lem170367 m h1)). Qed.
Lemma lem170372 (m : nat) (n : nat) : ((term89 n m) = n) = ((term89 n m) = n).
Proof. exact (eq_refl ((term89 n m) = n)). Qed.
Lemma lem170373 (n : nat) (m : nat) (h1 : term21 m) : (term60 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem170369 m h1) (@lem170372 m n)). Qed.
Lemma lem170375 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem170376 (m : nat) (n : nat) : (term99 m n) = ((term89 n m) = n).
Proof. exact (@lem170375 ((term89 n m) = n)). Qed.
Lemma lem170379 (n : nat) (m : nat) (h1 : term21 m) : (term60 m n) = ((term89 n m) = n).
Proof. exact (TRANS (@lem170373 n m h1) (@lem170376 m n)). Qed.
Lemma lem170380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170381 (n : nat) (m : nat) (h1 : term21 m) : (term71 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem170380) (@lem170379 n m h1)). Qed.
Lemma lem170384 (n : nat) (m : nat) : ((term65 n m) = (NUMERAL 0)) = ((term65 n m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term65 n m) = (NUMERAL 0))). Qed.
Lemma lem170385 (n : nat) (m : nat) (h1 : term21 m) : (term73 n m) = (term101 n m).
Proof. exact (MK_COMB (@lem170381 n m h1) (@lem170384 n m)). Qed.
Lemma lem170388 (n : nat) (m : nat) (h1 : term21 m) : (term101 n m) = (term73 n m).
Proof. exact (SYM (@lem170385 n m h1)). Qed.
Lemma lem170390 (q : nat) (m : nat) (n : nat) (r : nat) : term8 q m n r.
Proof. exact (EQ_MP (@lem170087 q m n r) (@lem170086 q m n r)). Qed.
Lemma lem170391 (n : nat) (m : nat) : term102 n m.
Proof. exact (@lem170390 n (Nat.mul m n) m (NUMERAL 0)). Qed.
Lemma lem170392 (n : nat) : term103 n.
Proof. exact (@lem98731 n). Qed.
Lemma lem170393 (n : nat) : (term103 n) = ((term104 n) = (term21 n)).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem170399 : term105.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem170415 : term106.
Proof. exact (proj1 (@lem170399)). Qed.
Lemma lem170416 (m : nat) : term107 m.
Proof. exact (@lem170415 m). Qed.
Lemma lem170417 (m : nat) : (term107 m) = ((term108 m) = m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem170457 (m : nat) : term98 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem170477 (m : nat) : (term108 m) = m.
Proof. exact (EQ_MP (@lem170417 m) (@lem170416 m)). Qed.
Lemma lem170478 (n : nat) (m : nat) : (term109 n m) = (Nat.mul n m).
Proof. exact (@lem170477 (Nat.mul n m)). Qed.
Lemma lem170480 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem170481 (m : nat) (n : nat) : (Nat.mul n m) = (Nat.mul m n).
Proof. exact (@lem170480 m n). Qed.
Lemma lem170484 (m : nat) (n : nat) : (term109 n m) = (Nat.mul m n).
Proof. exact (TRANS (@lem170478 n m) (@lem170481 m n)). Qed.
Lemma lem170485 (m : nat) (n : nat) : (term110 m n) = (term110 m n).
Proof. exact (eq_refl (term110 m n)). Qed.
Lemma lem170486 (m : nat) (n : nat) : ((Nat.mul m n) = (term109 n m)) = ((Nat.mul m n) = (Nat.mul m n)).
Proof. exact (MK_COMB (@lem170485 m n) (@lem170484 m n)). Qed.
Lemma lem170488 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem170489 (x : nat) : (x = x) = True.
Proof. exact (@lem170488 nat x). Qed.
Lemma lem170490 (m : nat) (n : nat) : ((Nat.mul m n) = (Nat.mul m n)) = True.
Proof. exact (@lem170489 (Nat.mul m n)). Qed.
Lemma lem170491 (n : nat) (m : nat) : ((Nat.mul m n) = (term109 n m)) = True.
Proof. exact (TRANS (@lem170486 m n) (@lem170490 m n)). Qed.
Lemma lem170492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170493 (n : nat) (m : nat) : (term111 n m) = (and True).
Proof. exact (MK_COMB (@lem170492) (@lem170491 n m)). Qed.
Lemma lem170495 (n : nat) : (term104 n) = (term21 n).
Proof. exact (EQ_MP (@lem170393 n) (@lem170392 n)). Qed.
Lemma lem170496 (m : nat) : (term104 m) = (term21 m).
Proof. exact (@lem170495 m). Qed.
Lemma lem170498 (m : nat) (h1 : term21 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem170457 m (@lem170093 m h1)). Qed.
Lemma lem170499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem170500 (m : nat) (h1 : term21 m) : (term21 m) = (~ False).
Proof. exact (MK_COMB (@lem170499) (@lem170498 m h1)). Qed.
Lemma lem170502 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem170503 (m : nat) (h1 : term21 m) : (term21 m) = True.
Proof. exact (TRANS (@lem170500 m h1) (@lem170502)). Qed.
Lemma lem170504 (m : nat) (h1 : term21 m) : (term104 m) = True.
Proof. exact (TRANS (@lem170496 m) (@lem170503 m h1)). Qed.
Lemma lem170505 (n : nat) (m : nat) (h1 : term21 m) : (term112 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem170493 n m) (@lem170504 m h1)). Qed.
Lemma lem170507 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem170508 : (True /\ True) = True.
Proof. exact (@lem170507 True). Qed.
Lemma lem170509 (n : nat) (m : nat) (h1 : term21 m) : (term112 n m) = True.
Proof. exact (TRANS (@lem170505 n m h1) (@lem170508)). Qed.
Lemma lem170510 (n : nat) (m : nat) (h1 : term21 m) : True = (term112 n m).
Proof. exact (SYM (@lem170509 n m h1)). Qed.
Lemma lem170511 (n : nat) (m : nat) (h1 : term21 m) : term112 n m.
Proof. exact (EQ_MP (@lem170510 n m h1) (@lem0)). Qed.
Lemma lem170512 (n : nat) (m : nat) (h1 : term21 m) : term101 n m.
Proof. exact (@lem170391 n m (@lem170511 n m h1)). Qed.
Lemma lem170513 (n : nat) (m : nat) (h1 : term21 m) : term73 n m.
Proof. exact (EQ_MP (@lem170388 n m h1) (@lem170512 n m h1)). Qed.
Lemma lem170514 (n : nat) (m : nat) : term73 n m.
Proof. exact (or_elim (@lem170091 m) (fun h0 : m = (NUMERAL 0) => @lem170306 n m h0) (fun h0 : term21 m => @lem170513 n m h0)). Qed.
Lemma lem170519 (m : nat) : term76 m.
Proof. exact (fun n : nat => @lem170514 n m). Qed.
Lemma lem170524 : term78.
Proof. exact (fun m : nat => @lem170519 m). Qed.
Lemma lem170525 : term45.
Proof. exact (EQ_MP (@lem170180) (@lem170524)). Qed.
