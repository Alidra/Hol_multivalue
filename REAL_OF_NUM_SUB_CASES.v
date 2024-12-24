Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_SUB_CASES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LE_CASES_spec.
Require Import REAL_NEG_SUB_spec.
Require Import REAL_OF_NUM_SUB_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1485056 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1485057 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1485056 h1 m). Qed.
Lemma lem1485058 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1485059 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1485058 m) (@lem1485057 m h1)). Qed.
Lemma lem1485060 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1485059 m h1 n). Qed.
Lemma lem1485061 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1485062 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1485061 n m) (@lem1485060 m n h1)). Qed.
Lemma lem1485063 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1485064 (m : nat) (n : nat) (h1 : term0) (h2 : Peano.le m n) : (term5 n m) = (term6 n m).
Proof. exact (@lem1485062 n m h1 (@lem1485063 m n h2)). Qed.
Lemma lem1485065 (m : nat) (n : nat) (h1 : Peano.le m n) : term7 n m.
Proof. exact (fun h0 : term0 => @lem1485064 m n h0 h1). Qed.
Lemma lem1485066 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1485067 (m : nat) (n : nat) (h1 : term0) (h2 : Peano.le m n) : (term5 n m) = (term6 n m).
Proof. exact (@lem1485065 m n h2 (@lem1485066 h1)). Qed.
Lemma lem1485068 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1485067 m n h1 h0). Qed.
Lemma lem1485069 (n : nat) (h1 : term0) : term8 n.
Proof. exact (fun m : nat => @lem1485068 n m h1). Qed.
Lemma lem1485070 (h1 : term0) : term9.
Proof. exact (fun n : nat => @lem1485069 n h1). Qed.
Lemma lem1485071 : term10.
Proof. exact (fun h0 : term0 => @lem1485070 h0). Qed.
Lemma lem1485072 : term9.
Proof. exact (@lem1485071 (@lem1485045)). Qed.
Lemma lem1485073 (n : nat) : term11 n.
Proof. exact (@lem1485072 n). Qed.
Lemma lem1485074 (n : nat) : (term11 n) = (term8 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem1485075 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem1485074 n) (@lem1485073 n)). Qed.
Lemma lem1485076 (n : nat) (m : nat) : term12 n m.
Proof. exact (@lem1485075 n m). Qed.
Lemma lem1485077 (n : nat) (m : nat) : (term12 n m) = (term4 n m).
Proof. exact (eq_refl (term12 n m)). Qed.
Lemma lem1485081 (y : real) (x : real) (h1 : (term13 x y) = (real_sub y x)) : (term13 x y) = (real_sub y x).
Proof. exact (h1). Qed.
Lemma lem1485082 (y : real) (x : real) (h1 : (term13 x y) = (real_sub y x)) : (real_sub y x) = (term13 x y).
Proof. exact (SYM (@lem1485081 y x h1)). Qed.
Lemma lem1485083 (x : real) (y : real) (h1 : (real_sub y x) = (term13 x y)) : (real_sub y x) = (term13 x y).
Proof. exact (h1). Qed.
Lemma lem1485084 (x : real) (y : real) (h1 : (real_sub y x) = (term13 x y)) : (term13 x y) = (real_sub y x).
Proof. exact (SYM (@lem1485083 x y h1)). Qed.
Lemma lem1485085 (x : real) (y : real) : ((term13 x y) = (real_sub y x)) = ((real_sub y x) = (term13 x y)).
Proof. exact (prop_ext (fun h1 : (term13 x y) = (real_sub y x) => @lem1485082 y x h1) (fun h1 : (real_sub y x) = (term13 x y) => @lem1485084 x y h1)). Qed.
Lemma lem1485086 (x : real) : (term14 x) = (term15 x).
Proof. exact (fun_ext (fun y : real => @lem1485085 x y)). Qed.
Lemma lem1485087 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1485088 (x : real) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1485087) (@lem1485086 x)). Qed.
Lemma lem1485089 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1485088 x)). Qed.
Lemma lem1485090 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1485091 : term20 = term21.
Proof. exact (MK_COMB (@lem1485090) (@lem1485089)). Qed.
Lemma lem1485092 : term21.
Proof. exact (EQ_MP (@lem1485091) (@lem1374337)). Qed.
Lemma lem1485093 (x : real) : term22 x.
Proof. exact (@lem1485092 x). Qed.
Lemma lem1485094 (x : real) : (term22 x) = (term17 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1485095 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1485094 x) (@lem1485093 x)). Qed.
Lemma lem1485096 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1485095 x y). Qed.
Lemma lem1485097 (x : real) (y : real) : (term23 x y) = ((real_sub y x) = (term13 x y)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1485099 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term24 _476 _475 _474 _477) = (term25 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1485100 (_474 : real) (_475 : Prop) (m : nat) (n : nat) (_477 : real) : (term26 m n _475 _474 _477) = (term27 _474 _475 m n _477).
Proof. exact (@lem1485099 _474 _475 (term28 m n) _477). Qed.
Lemma lem1485101 (n : nat) (m : nat) : (term29 n m) = (term30 n m).
Proof. exact (@lem1485100 (term6 m n) (Peano.le n m) m n (term31 n m)). Qed.
Lemma lem1485102 (n : nat) (m : nat) : (term32 n m) = ((term5 m n) = (term31 n m)).
Proof. exact (eq_refl (term32 n m)). Qed.
Lemma lem1485103 (n : nat) (m : nat) : (term33 n m) = (term33 n m).
Proof. exact (eq_refl (term33 n m)). Qed.
Lemma lem1485104 (n : nat) (m : nat) : (term34 n m) = (term35 n m).
Proof. exact (MK_COMB (@lem1485103 n m) (@lem1485102 n m)). Qed.
Lemma lem1485105 (m : nat) (n : nat) : (term36 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1485106 (n : nat) (m : nat) : (term37 n m) = (term37 n m).
Proof. exact (eq_refl (term37 n m)). Qed.
Lemma lem1485107 (m : nat) (n : nat) : (term38 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem1485106 n m) (@lem1485105 m n)). Qed.
Lemma lem1485108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1485109 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1485108) (@lem1485107 m n)). Qed.
Lemma lem1485110 (n : nat) (m : nat) : (term30 n m) = (term41 n m).
Proof. exact (MK_COMB (@lem1485109 m n) (@lem1485104 n m)). Qed.
Lemma lem1485111 (n : nat) (m : nat) : (term29 n m) = ((term5 m n) = (term42 n m)).
Proof. exact (eq_refl (term29 n m)). Qed.
Lemma lem1485112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1485113 (n : nat) (m : nat) : (term43 n m) = (term44 n m).
Proof. exact (MK_COMB (@lem1485112) (@lem1485111 n m)). Qed.
Lemma lem1485114 (n : nat) (m : nat) : ((term29 n m) = (term30 n m)) = (((term5 m n) = (term42 n m)) = (term41 n m)).
Proof. exact (MK_COMB (@lem1485113 n m) (@lem1485110 n m)). Qed.
Lemma lem1485115 (n : nat) (m : nat) : ((term5 m n) = (term42 n m)) = (term41 n m).
Proof. exact (EQ_MP (@lem1485114 n m) (@lem1485101 n m)). Qed.
Lemma lem1485116 (n : nat) (m : nat) : (term41 n m) = ((term5 m n) = (term42 n m)).
Proof. exact (SYM (@lem1485115 n m)). Qed.
Lemma lem1485117 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem1485134 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1485151 (m : nat) : term1 m.
Proof. exact (@lem1485045 m). Qed.
Lemma lem1485152 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1485153 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1485152 m) (@lem1485151 m)). Qed.
Lemma lem1485154 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1485153 m n). Qed.
Lemma lem1485155 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1485156 (n : nat) (m : nat) : term4 n m.
Proof. exact (EQ_MP (@lem1485155 n m) (@lem1485154 m n)). Qed.
Lemma lem1485157 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1485158 (m : nat) (n : nat) (h1 : Peano.le m n) : (term5 n m) = (term6 n m).
Proof. exact (@lem1485156 n m (@lem1485157 m n h1)). Qed.
Lemma lem1485164 (n : nat) (m : nat) : (Peano.le n m) = ((Peano.le n m) = True).
Proof. exact (@lem7 (Peano.le n m)). Qed.
Lemma lem1485169 (n : nat) (m : nat) : term4 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1485158 m n h0). Qed.
Lemma lem1485170 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1485169 m n). Qed.
Lemma lem1485172 (n : nat) (m : nat) (h1 : Peano.le n m) : (Peano.le n m) = True.
Proof. exact (EQ_MP (@lem1485164 n m) (@lem1485117 n m h1)). Qed.
Lemma lem1485173 (n : nat) (m : nat) (h1 : Peano.le n m) : True = (Peano.le n m).
Proof. exact (SYM (@lem1485172 n m h1)). Qed.
Lemma lem1485174 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (EQ_MP (@lem1485173 n m h1) (@lem0)). Qed.
Lemma lem1485175 (n : nat) (m : nat) (h1 : Peano.le n m) : (term5 m n) = (term6 m n).
Proof. exact (@lem1485170 m n (@lem1485174 n m h1)). Qed.
Lemma lem1485176 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1485177 (n : nat) (m : nat) (h1 : Peano.le n m) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem1485176) (@lem1485175 n m h1)). Qed.
Lemma lem1485178 (m : nat) (n : nat) : (term6 m n) = (term6 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1485179 (n : nat) (m : nat) (h1 : Peano.le n m) : ((term5 m n) = (term6 m n)) = ((term6 m n) = (term6 m n)).
Proof. exact (MK_COMB (@lem1485177 n m h1) (@lem1485178 m n)). Qed.
Lemma lem1485181 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1485182 (x : real) : (x = x) = True.
Proof. exact (@lem1485181 real x). Qed.
Lemma lem1485183 (m : nat) (n : nat) : ((term6 m n) = (term6 m n)) = True.
Proof. exact (@lem1485182 (term6 m n)). Qed.
Lemma lem1485184 (n : nat) (m : nat) (h1 : Peano.le n m) : ((term5 m n) = (term6 m n)) = True.
Proof. exact (TRANS (@lem1485179 n m h1) (@lem1485183 m n)). Qed.
Lemma lem1485185 (n : nat) (m : nat) (h1 : Peano.le n m) : True = ((term5 m n) = (term6 m n)).
Proof. exact (SYM (@lem1485184 n m h1)). Qed.
Lemma lem1485213 (x : real) (y : real) : (real_sub y x) = (term13 x y).
Proof. exact (EQ_MP (@lem1485097 x y) (@lem1485096 x y)). Qed.
Lemma lem1485214 (n : nat) (m : nat) : (term5 m n) = (term48 n m).
Proof. exact (@lem1485213 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1485215 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1485216 (n : nat) (m : nat) : (term46 m n) = (term49 n m).
Proof. exact (MK_COMB (@lem1485215) (@lem1485214 n m)). Qed.
Lemma lem1485217 (n : nat) (m : nat) : (term31 n m) = (term31 n m).
Proof. exact (eq_refl (term31 n m)). Qed.
Lemma lem1485218 (n : nat) (m : nat) : ((term5 m n) = (term31 n m)) = ((term48 n m) = (term31 n m)).
Proof. exact (MK_COMB (@lem1485216 n m) (@lem1485217 n m)). Qed.
Lemma lem1485219 (n : nat) (m : nat) : ((term48 n m) = (term31 n m)) = ((term5 m n) = (term31 n m)).
Proof. exact (SYM (@lem1485218 n m)). Qed.
Lemma lem1485220 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1485222 (n : nat) (m : nat) : term4 n m.
Proof. exact (EQ_MP (@lem1485077 n m) (@lem1485076 n m)). Qed.
Lemma lem1485224 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1485225 (m : nat) (n : nat) : (Peano.le m n) = (term51 m n).
Proof. exact (@lem1485224 (Peano.le m n)). Qed.
Lemma lem1485226 (m : nat) (n : nat) : (term51 m n) = (Peano.le m n).
Proof. exact (SYM (@lem1485225 m n)). Qed.
Lemma lem1485227 (m : nat) (n : nat) (h1 : term45 m n) : term45 m n.
Proof. exact (h1). Qed.
Lemma lem1485230 (m : nat) (n : nat) (h1 : term52 m n) : term52 m n.
Proof. exact (h1). Qed.
Lemma lem1485231 (m : nat) (n : nat) : term53 m n.
Proof. exact (fun h0 : term52 m n => @lem1485230 m n h0). Qed.
Lemma lem1485232 (m : nat) (n : nat) (h1 : term53 m n) : term53 m n.
Proof. exact (h1). Qed.
Lemma lem1485233 (m : nat) (n : nat) (h1 : term52 m n) : term52 m n.
Proof. exact (h1). Qed.
Lemma lem1485234 (m : nat) (n : nat) (h1 : term52 m n) (h2 : term53 m n) : term52 m n.
Proof. exact (@lem1485232 m n h2 (@lem1485233 m n h1)). Qed.
Lemma lem1485235 (m : nat) (n : nat) (h1 : term52 m n) : term54 m n.
Proof. exact (fun h0 : term53 m n => @lem1485234 m n h1 h0). Qed.
Lemma lem1485236 (m : nat) (n : nat) (h1 : term53 m n) : term53 m n.
Proof. exact (h1). Qed.
Lemma lem1485237 (m : nat) (n : nat) (h1 : term52 m n) (h2 : term53 m n) : term52 m n.
Proof. exact (@lem1485235 m n h1 (@lem1485236 m n h2)). Qed.
Lemma lem1485238 (m : nat) (n : nat) (h1 : term53 m n) : term53 m n.
Proof. exact (fun h0 : term52 m n => @lem1485237 m n h0 h1). Qed.
Lemma lem1485239 (m : nat) (n : nat) : term55 m n.
Proof. exact (fun h0 : term53 m n => @lem1485238 m n h0). Qed.
Lemma lem1485242 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem1485239 m n (@lem1485231 m n)). Qed.
Lemma lem1485256 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1485257 : term56 = term57.
Proof. exact (@lem1485256 term58). Qed.
Lemma lem1485312 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1485313 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem1485312 m n) (@lem1485257)). Qed.
Lemma lem1485316 (n : nat) (m : nat) : (term33 n m) = (term33 n m).
Proof. exact (eq_refl (term33 n m)). Qed.
Lemma lem1485317 (m : nat) (n : nat) : (term52 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem1485316 n m) (@lem1485313 m n)). Qed.
Lemma lem1485320 (n : nat) : (term62 n) = (term63 n).
Proof. exact (fun_ext (fun m : nat => @lem1485317 m n)). Qed.
Lemma lem1485321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485322 (n : nat) : (term64 n) = (term65 n).
Proof. exact (MK_COMB (@lem1485321) (@lem1485320 n)). Qed.
Lemma lem1485327 : term66 = term67.
Proof. exact (fun_ext (fun n : nat => @lem1485322 n)). Qed.
Lemma lem1485328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485337 : term68 = term69.
Proof. exact (MK_COMB (@lem1485328) (@lem1485327)). Qed.
Lemma lem1485342 (n : nat) (m : nat) : (term70 n m) = (term70 n m).
Proof. exact (eq_refl (term70 n m)). Qed.
Lemma lem1485343 (m : nat) : (term71 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem1485342 n m)). Qed.
Lemma lem1485344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485345 (m : nat) : (term72 m) = (term72 m).
Proof. exact (MK_COMB (@lem1485344) (@lem1485343 m)). Qed.
Lemma lem1485346 : term73 = term73.
Proof. exact (fun_ext (fun m : nat => @lem1485345 m)). Qed.
Lemma lem1485347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485348 : term58 = term58.
Proof. exact (MK_COMB (@lem1485347) (@lem1485346)). Qed.
Lemma lem1485349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1485350 : term57 = term57.
Proof. exact (MK_COMB (@lem1485349) (@lem1485348)). Qed.
Lemma lem1485355 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1485356 (m : nat) (n : nat) : (term60 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem1485355 m n) (@lem1485350)). Qed.
Lemma lem1485361 (n : nat) (m : nat) : (term33 n m) = (term33 n m).
Proof. exact (eq_refl (term33 n m)). Qed.
Lemma lem1485362 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem1485361 n m) (@lem1485356 m n)). Qed.
Lemma lem1485363 (n : nat) : (term63 n) = (term63 n).
Proof. exact (fun_ext (fun m : nat => @lem1485362 m n)). Qed.
Lemma lem1485364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485365 (n : nat) : (term65 n) = (term65 n).
Proof. exact (MK_COMB (@lem1485364) (@lem1485363 n)). Qed.
Lemma lem1485366 : term67 = term67.
Proof. exact (fun_ext (fun n : nat => @lem1485365 n)). Qed.
Lemma lem1485367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485368 : term69 = term69.
Proof. exact (MK_COMB (@lem1485367) (@lem1485366)). Qed.
Lemma lem1485401 : term68 = term69.
Proof. exact (TRANS (@lem1485337) (@lem1485368)). Qed.
Lemma lem1485402 : term69 = term68.
Proof. exact (SYM (@lem1485401)). Qed.
Lemma lem1485405 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem1485411 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1485417 (m : nat) (n : nat) (h1 : term45 m n) : term45 m n.
Proof. exact (h1). Qed.
Lemma lem1485422 (n : nat) (m : nat) : (term70 n m) = (term70 n m).
Proof. exact (eq_refl (term70 n m)). Qed.
Lemma lem1485423 (m : nat) : (term71 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem1485422 n m)). Qed.
Lemma lem1485424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485425 (m : nat) : (term72 m) = (term72 m).
Proof. exact (MK_COMB (@lem1485424) (@lem1485423 m)). Qed.
Lemma lem1485426 : term73 = term73.
Proof. exact (fun_ext (fun m : nat => @lem1485425 m)). Qed.
Lemma lem1485427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485484 : term58 = term58.
Proof. exact (MK_COMB (@lem1485427) (@lem1485426)). Qed.
Lemma lem1485485 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem1485484) (@lem1485405 h1)). Qed.
Lemma lem1485493 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1485501 (m : nat) (n : nat) (h1 : term45 m n) : term45 m n.
Proof. exact (h1). Qed.
Lemma lem1485514 (n : nat) (m : nat) : (term70 n m) = (term70 n m).
Proof. exact (eq_refl (term70 n m)). Qed.
Lemma lem1485515 (m : nat) : (term71 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem1485514 n m)). Qed.
Lemma lem1485516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485517 (m : nat) : (term72 m) = (term72 m).
Proof. exact (MK_COMB (@lem1485516) (@lem1485515 m)). Qed.
Lemma lem1485518 : term73 = term73.
Proof. exact (fun_ext (fun m : nat => @lem1485517 m)). Qed.
Lemma lem1485519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485520 : term58 = term58.
Proof. exact (MK_COMB (@lem1485519) (@lem1485518)). Qed.
Lemma lem1485521 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem1485520) (@lem1485485 h1)). Qed.
Lemma lem1485525 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1485529 (m : nat) (n : nat) (h1 : term45 m n) : term45 m n.
Proof. exact (h1). Qed.
Lemma lem1485537 (n : nat) (m : nat) : (term70 n m) = (term70 n m).
Proof. exact (eq_refl (term70 n m)). Qed.
Lemma lem1485538 (m : nat) : (term71 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem1485537 n m)). Qed.
Lemma lem1485539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485540 (m : nat) : (term72 m) = (term72 m).
Proof. exact (MK_COMB (@lem1485539) (@lem1485538 m)). Qed.
Lemma lem1485541 : term73 = term73.
Proof. exact (fun_ext (fun m : nat => @lem1485540 m)). Qed.
Lemma lem1485542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485544 : term58 = term58.
Proof. exact (MK_COMB (@lem1485542) (@lem1485541)). Qed.
Lemma lem1485545 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem1485544) (@lem1485521 h1)). Qed.
Lemma lem1485546 (_24828 : nat) (h1 : term58) : term74 _24828.
Proof. exact (@lem1485545 h1 _24828). Qed.
Lemma lem1485547 (_24828 : nat) : (term74 _24828) = (term72 _24828).
Proof. exact (eq_refl (term74 _24828)). Qed.
Lemma lem1485548 (_24828 : nat) (h1 : term58) : term72 _24828.
Proof. exact (EQ_MP (@lem1485547 _24828) (@lem1485546 _24828 h1)). Qed.
Lemma lem1485549 (_24828 : nat) (_24829 : nat) (h1 : term58) : term75 _24828 _24829.
Proof. exact (@lem1485548 _24828 h1 _24829). Qed.
Lemma lem1485550 (_24829 : nat) (_24828 : nat) : (term75 _24828 _24829) = (term70 _24829 _24828).
Proof. exact (eq_refl (term75 _24828 _24829)). Qed.
Lemma lem1485553 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1485555 (m : nat) (n : nat) (h1 : term45 m n) : term45 m n.
Proof. exact (h1). Qed.
Lemma lem1485561 (_24829 : nat) (_24828 : nat) (h1 : term58) : term70 _24829 _24828.
Proof. exact (EQ_MP (@lem1485550 _24829 _24828) (@lem1485549 _24828 _24829 h1)). Qed.
Lemma lem1485563 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1485564 (n : nat) (m : nat) (h1 : term45 n m) : term76 n m.
Proof. exact (fun h0 : Peano.le n m => @lem1485563 n m h1). Qed.
Lemma lem1485566 (p : Prop) : (term77 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1485567 (n : nat) (m : nat) : (term76 n m) = (term45 n m).
Proof. exact (@lem1485566 (Peano.le n m)). Qed.
Lemma lem1485568 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (EQ_MP (@lem1485567 n m) (@lem1485564 n m h1)). Qed.
Lemma lem1485579 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1485580 (_24829 : nat) (_24828 : nat) : (term70 _24828 _24829) = (term70 _24829 _24828).
Proof. exact (@lem1485579 (Peano.le _24828 _24829) (Peano.le _24829 _24828)). Qed.
Lemma lem1485586 (_24829 : nat) (_24828 : nat) : (term78 _24829 _24828) = (term78 _24829 _24828).
Proof. exact (eq_refl (term78 _24829 _24828)). Qed.
Lemma lem1485587 (_24829 : nat) (_24828 : nat) : ((term70 _24829 _24828) = (term70 _24828 _24829)) = ((term70 _24829 _24828) = (term70 _24829 _24828)).
Proof. exact (MK_COMB (@lem1485586 _24829 _24828) (@lem1485580 _24829 _24828)). Qed.
Lemma lem1485589 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1485590 (x : Prop) : (x = x) = True.
Proof. exact (@lem1485589 Prop x). Qed.
Lemma lem1485591 (_24829 : nat) (_24828 : nat) : ((term70 _24829 _24828) = (term70 _24829 _24828)) = True.
Proof. exact (@lem1485590 (term70 _24829 _24828)). Qed.
Lemma lem1485592 (_24828 : nat) (_24829 : nat) : ((term70 _24829 _24828) = (term70 _24828 _24829)) = True.
Proof. exact (TRANS (@lem1485587 _24829 _24828) (@lem1485591 _24829 _24828)). Qed.
Lemma lem1485593 (_24828 : nat) (_24829 : nat) : True = ((term70 _24829 _24828) = (term70 _24828 _24829)).
Proof. exact (SYM (@lem1485592 _24828 _24829)). Qed.
Lemma lem1485594 (_24828 : nat) (_24829 : nat) : (term70 _24829 _24828) = (term70 _24828 _24829).
Proof. exact (EQ_MP (@lem1485593 _24828 _24829) (@lem0)). Qed.
Lemma lem1485595 (_24828 : nat) (_24829 : nat) (h1 : term58) : term70 _24828 _24829.
Proof. exact (EQ_MP (@lem1485594 _24828 _24829) (@lem1485561 _24829 _24828 h1)). Qed.
Lemma lem1485597 (b : Prop) (a : Prop) : (a \/ b) = (term79 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1485600 (_24829 : nat) (_24828 : nat) : (term70 _24828 _24829) = (term80 _24829 _24828).
Proof. exact (@lem1485597 (Peano.le _24828 _24829) (Peano.le _24829 _24828)). Qed.
Lemma lem1485603 (_24829 : nat) (_24828 : nat) (h1 : term58) : term80 _24829 _24828.
Proof. exact (EQ_MP (@lem1485600 _24829 _24828) (@lem1485595 _24828 _24829 h1)). Qed.
Lemma lem1485604 (m : nat) (n : nat) (h1 : term58) : term80 m n.
Proof. exact (@lem1485603 m n h1). Qed.
Lemma lem1485607 (n : nat) (m : nat) (h1 : term58) (h2 : term45 n m) : Peano.le m n.
Proof. exact (@lem1485604 m n h1 (@lem1485568 n m h2)). Qed.
Lemma lem1485608 (n : nat) (m : nat) (h1 : term58) (h2 : term45 n m) : term81 m n.
Proof. exact (fun h0 : term45 m n => @lem1485607 n m h1 h2). Qed.
Lemma lem1485610 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1485611 (m : nat) (n : nat) : (term81 m n) = (Peano.le m n).
Proof. exact (@lem1485610 (Peano.le m n)). Qed.
Lemma lem1485612 (n : nat) (m : nat) (h1 : term58) (h2 : term45 n m) : Peano.le m n.
Proof. exact (EQ_MP (@lem1485611 m n) (@lem1485608 n m h1 h2)). Qed.
Lemma lem1485615 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1485617 (m : nat) (n : nat) : (term45 m n) = (term83 m n).
Proof. exact (@lem1485615 (Peano.le m n)). Qed.
Lemma lem1485620 (m : nat) (n : nat) (h1 : term45 m n) : term83 m n.
Proof. exact (EQ_MP (@lem1485617 m n) (@lem1485555 m n h1)). Qed.
Lemma lem1485623 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (@lem1485620 m n h2 (@lem1485612 n m h1 h3)). Qed.
Lemma lem1485624 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : term84.
Proof. exact (fun h0 : ~ False => @lem1485623 n m h1 h2 h3). Qed.
Lemma lem1485626 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1485627 : term84 = False.
Proof. exact (@lem1485626 False). Qed.
Lemma lem1485628 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485627) (@lem1485624 n m h1 h2 h3)). Qed.
Lemma lem1485629 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 m n) = False.
Proof. exact (prop_ext (fun h4 : term45 m n => @lem1485628 n m h1 h2 h3) (fun h4 : False => @lem1485555 m n h2)). Qed.
Lemma lem1485630 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485629 n m h1 h2 h3) (@lem1485555 m n h2)). Qed.
Lemma lem1485631 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h4 : term45 n m => @lem1485630 n m h1 h2 h3) (fun h4 : False => @lem1485553 n m h3)). Qed.
Lemma lem1485632 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485631 n m h1 h2 h3) (@lem1485553 n m h3)). Qed.
Lemma lem1485633 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 m n) = False.
Proof. exact (prop_ext (fun h4 : term45 m n => @lem1485632 n m h1 h2 h3) (fun h4 : False => @lem1485529 m n h2)). Qed.
Lemma lem1485634 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485633 n m h1 h2 h3) (@lem1485529 m n h2)). Qed.
Lemma lem1485635 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h4 : term45 n m => @lem1485634 n m h1 h2 h3) (fun h4 : False => @lem1485525 n m h3)). Qed.
Lemma lem1485636 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485635 n m h1 h2 h3) (@lem1485525 n m h3)). Qed.
Lemma lem1485637 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem1485636 n m h1 h2 h3) (fun h4 : False => @lem1485545 h1)). Qed.
Lemma lem1485638 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485637 n m h1 h2 h3) (@lem1485545 h1)). Qed.
Lemma lem1485639 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 m n) = False.
Proof. exact (prop_ext (fun h4 : term45 m n => @lem1485638 n m h1 h2 h3) (fun h4 : False => @lem1485529 m n h2)). Qed.
Lemma lem1485640 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485639 n m h1 h2 h3) (@lem1485529 m n h2)). Qed.
Lemma lem1485641 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h4 : term45 n m => @lem1485640 n m h1 h2 h3) (fun h4 : False => @lem1485525 n m h3)). Qed.
Lemma lem1485642 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485641 n m h1 h2 h3) (@lem1485525 n m h3)). Qed.
Lemma lem1485643 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem1485642 n m h1 h2 h3) (fun h4 : False => @lem1485521 h1)). Qed.
Lemma lem1485644 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485643 n m h1 h2 h3) (@lem1485521 h1)). Qed.
Lemma lem1485645 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 m n) = False.
Proof. exact (prop_ext (fun h4 : term45 m n => @lem1485644 n m h1 h2 h3) (fun h4 : False => @lem1485501 m n h2)). Qed.
Lemma lem1485646 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485645 n m h1 h2 h3) (@lem1485501 m n h2)). Qed.
Lemma lem1485647 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h4 : term45 n m => @lem1485646 n m h1 h2 h3) (fun h4 : False => @lem1485493 n m h3)). Qed.
Lemma lem1485648 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485647 n m h1 h2 h3) (@lem1485493 n m h3)). Qed.
Lemma lem1485649 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem1485648 n m h1 h2 h3) (fun h4 : False => @lem1485485 h1)). Qed.
Lemma lem1485650 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485649 n m h1 h2 h3) (@lem1485485 h1)). Qed.
Lemma lem1485651 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 m n) = False.
Proof. exact (prop_ext (fun h4 : term45 m n => @lem1485650 n m h1 h2 h3) (fun h4 : False => @lem1485417 m n h2)). Qed.
Lemma lem1485652 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485651 n m h1 h2 h3) (@lem1485417 m n h2)). Qed.
Lemma lem1485653 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h4 : term45 n m => @lem1485652 n m h1 h2 h3) (fun h4 : False => @lem1485411 n m h3)). Qed.
Lemma lem1485654 (n : nat) (m : nat) (h1 : term58) (h2 : term45 m n) (h3 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485653 n m h1 h2 h3) (@lem1485411 n m h3)). Qed.
Lemma lem1485655 (n : nat) (m : nat) (h1 : term45 m n) (h2 : term45 n m) : term56.
Proof. exact (fun h0 : term58 => @lem1485654 n m h0 h1 h2). Qed.
Lemma lem1485656 : term56 = term57.
Proof. exact (@lem69 term58). Qed.
Lemma lem1485657 (n : nat) (m : nat) (h1 : term45 m n) (h2 : term45 n m) : term57.
Proof. exact (EQ_MP (@lem1485656) (@lem1485655 n m h1 h2)). Qed.
Lemma lem1485658 (n : nat) (m : nat) (h1 : term45 n m) : term60 m n.
Proof. exact (fun h0 : term45 m n => @lem1485657 n m h0 h1). Qed.
Lemma lem1485659 (m : nat) (n : nat) : term61 m n.
Proof. exact (fun h0 : term45 n m => @lem1485658 n m h0). Qed.
Lemma lem1485664 (n : nat) : term65 n.
Proof. exact (fun m : nat => @lem1485659 m n). Qed.
Lemma lem1485669 : term69.
Proof. exact (fun n : nat => @lem1485664 n). Qed.
Lemma lem1485670 : term68.
Proof. exact (EQ_MP (@lem1485402) (@lem1485669)). Qed.
Lemma lem1485671 (n : nat) : term85 n.
Proof. exact (@lem1485670 n). Qed.
Lemma lem1485672 (n : nat) : (term85 n) = (term64 n).
Proof. exact (eq_refl (term85 n)). Qed.
Lemma lem1485673 (n : nat) : term64 n.
Proof. exact (EQ_MP (@lem1485672 n) (@lem1485671 n)). Qed.
Lemma lem1485674 (n : nat) (m : nat) : term86 n m.
Proof. exact (@lem1485673 n m). Qed.
Lemma lem1485675 (m : nat) (n : nat) : (term86 n m) = (term52 m n).
Proof. exact (eq_refl (term86 n m)). Qed.
Lemma lem1485676 (m : nat) (n : nat) : term52 m n.
Proof. exact (EQ_MP (@lem1485675 m n) (@lem1485674 n m)). Qed.
Lemma lem1485678 (m : nat) (n : nat) : term52 m n.
Proof. exact (@lem1485242 m n (@lem1485676 m n)). Qed.
Lemma lem1485679 (n : nat) (m : nat) (h1 : term45 n m) : term59 m n.
Proof. exact (@lem1485678 m n (@lem1485134 n m h1)). Qed.
Lemma lem1485680 (n : nat) (m : nat) (h1 : term45 m n) (h2 : term45 n m) : term56.
Proof. exact (@lem1485679 n m h2 (@lem1485227 m n h1)). Qed.
Lemma lem1485681 (n : nat) (m : nat) (h1 : term45 m n) (h2 : term45 n m) : False.
Proof. exact (@lem1485680 n m h1 h2 (@lem96155)). Qed.
Lemma lem1485682 (n : nat) (m : nat) (h1 : term45 m n) (h2 : term45 n m) : (term45 m n) = False.
Proof. exact (prop_ext (fun h3 : term45 m n => @lem1485681 n m h1 h2) (fun h3 : False => @lem1485227 m n h1)). Qed.
Lemma lem1485683 (n : nat) (m : nat) (h1 : term45 m n) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1485682 n m h1 h2) (@lem1485227 m n h1)). Qed.
Lemma lem1485684 (n : nat) (m : nat) (h1 : term45 n m) : term51 m n.
Proof. exact (fun h0 : term45 m n => @lem1485683 n m h0 h1). Qed.
Lemma lem1485685 (n : nat) (m : nat) (h1 : term45 n m) : Peano.le m n.
Proof. exact (EQ_MP (@lem1485226 m n) (@lem1485684 n m h1)). Qed.
Lemma lem1485686 (n : nat) (m : nat) (h1 : term45 n m) : (term5 n m) = (term6 n m).
Proof. exact (@lem1485222 n m (@lem1485685 n m h1)). Qed.
Lemma lem1485687 (n : nat) (m : nat) (h1 : term45 n m) : (term48 n m) = (term31 n m).
Proof. exact (MK_COMB (@lem1485220) (@lem1485686 n m h1)). Qed.
Lemma lem1485690 (n : nat) (m : nat) (h1 : term45 n m) : (term5 m n) = (term31 n m).
Proof. exact (EQ_MP (@lem1485219 n m) (@lem1485687 n m h1)). Qed.
Lemma lem1485691 (n : nat) (m : nat) (h1 : term45 n m) : (term45 n m) = ((term5 m n) = (term31 n m)).
Proof. exact (prop_ext (fun h2 : term45 n m => @lem1485690 n m h1) (fun h2 : (term5 m n) = (term31 n m) => @lem1485134 n m h1)). Qed.
Lemma lem1485692 (n : nat) (m : nat) (h1 : term45 n m) : (term5 m n) = (term31 n m).
Proof. exact (EQ_MP (@lem1485691 n m h1) (@lem1485134 n m h1)). Qed.
Lemma lem1485693 (n : nat) (m : nat) : term35 n m.
Proof. exact (fun h0 : term45 n m => @lem1485692 n m h0). Qed.
Lemma lem1485694 (n : nat) (m : nat) (h1 : Peano.le n m) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem1485185 n m h1) (@lem0)). Qed.
Lemma lem1485695 (n : nat) (m : nat) (h1 : Peano.le n m) : (Peano.le n m) = ((term5 m n) = (term6 m n)).
Proof. exact (prop_ext (fun h2 : Peano.le n m => @lem1485694 n m h1) (fun h2 : (term5 m n) = (term6 m n) => @lem1485117 n m h1)). Qed.
Lemma lem1485696 (n : nat) (m : nat) (h1 : Peano.le n m) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem1485695 n m h1) (@lem1485117 n m h1)). Qed.
Lemma lem1485697 (m : nat) (n : nat) : term4 m n.
Proof. exact (fun h0 : Peano.le n m => @lem1485696 n m h0). Qed.
Lemma lem1485698 (n : nat) (m : nat) : term41 n m.
Proof. exact (conj (@lem1485697 m n) (@lem1485693 n m)). Qed.
Lemma lem1485699 (n : nat) (m : nat) : (term5 m n) = (term42 n m).
Proof. exact (EQ_MP (@lem1485116 n m) (@lem1485698 n m)). Qed.
Lemma lem1485704 (m : nat) : term87 m.
Proof. exact (fun n : nat => @lem1485699 n m). Qed.
Lemma lem1485709 : term88.
Proof. exact (fun m : nat => @lem1485704 m). Qed.
