Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340174_term_abbrevs.
Require Import TREAL_MUL_LINV_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1338076_spec.
Require Import thm1338081_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1340096 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1340097 (x : prod hreal hreal) : (term1 x) = ((term0 x) = term2).
Proof. exact (@lem1340096 x term3). Qed.
Lemma lem1340101 (m : nat) : (term4 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340102 : term2 = term5.
Proof. exact (@lem1340101 (NUMERAL 0)). Qed.
Lemma lem1340103 (x : prod hreal hreal) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1340104 (x : prod hreal hreal) : ((term0 x) = term2) = ((term0 x) = term5).
Proof. exact (MK_COMB (@lem1340103 x) (@lem1340102)). Qed.
Lemma lem1340107 (x : prod hreal hreal) : (term1 x) = ((term0 x) = term5).
Proof. exact (TRANS (@lem1340097 x) (@lem1340104 x)). Qed.
Lemma lem1340108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1340109 (x : prod hreal hreal) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1340108) (@lem1340107 x)). Qed.
Lemma lem1340110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1340111 (x : prod hreal hreal) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1340110) (@lem1340109 x)). Qed.
Lemma lem1340113 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1340114 (x : prod hreal hreal) : (term11 x) = ((term12 x) = term13).
Proof. exact (@lem1340113 (term14 x) term15). Qed.
Lemma lem1340118 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term16 x1 y1) = (term17 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1340119 (x : prod hreal hreal) : (term12 x) = (term18 x).
Proof. exact (@lem1340118 (treal_inv x) x). Qed.
Lemma lem1340121 (x : prod hreal hreal) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1338081 x) (@lem1338076 x)). Qed.
Lemma lem1340122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1340123 (x : prod hreal hreal) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem1340122) (@lem1340121 x)). Qed.
Lemma lem1340124 (x : prod hreal hreal) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1340125 (x : prod hreal hreal) : (term18 x) = (term23 x).
Proof. exact (MK_COMB (@lem1340123 x) (@lem1340124 x)). Qed.
Lemma lem1340126 (x : prod hreal hreal) : (term12 x) = (term23 x).
Proof. exact (TRANS (@lem1340119 x) (@lem1340125 x)). Qed.
Lemma lem1340127 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1340128 (x : prod hreal hreal) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1340127) (@lem1340126 x)). Qed.
Lemma lem1340130 (m : nat) : (term4 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340131 : term13 = term26.
Proof. exact (@lem1340130 term27). Qed.
Lemma lem1340132 (x : prod hreal hreal) : ((term12 x) = term13) = ((term23 x) = term26).
Proof. exact (MK_COMB (@lem1340128 x) (@lem1340131)). Qed.
Lemma lem1340135 (x : prod hreal hreal) : (term11 x) = ((term23 x) = term26).
Proof. exact (TRANS (@lem1340114 x) (@lem1340132 x)). Qed.
Lemma lem1340136 (x : prod hreal hreal) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1340111 x) (@lem1340135 x)). Qed.
Lemma lem1340139 : term30 = term31.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1340136 x)). Qed.
Lemma lem1340140 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1340141 : term32 = term33.
Proof. exact (MK_COMB (@lem1340140) (@lem1340139)). Qed.
Lemma lem1340147 (P : real -> Prop) : (term34 P) = (term35 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1340148 : term36 = term37.
Proof. exact (@lem1340147 term38). Qed.
Lemma lem1340149 (x : prod hreal hreal) : (term39 x) = (term29 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1340150 : term40 = term31.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1340149 x)). Qed.
Lemma lem1340151 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1340152 : term36 = term33.
Proof. exact (MK_COMB (@lem1340151) (@lem1340150)). Qed.
Lemma lem1340153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1340154 : term41 = term42.
Proof. exact (MK_COMB (@lem1340153) (@lem1340152)). Qed.
Lemma lem1340155 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1340156 : term45 = term38.
Proof. exact (fun_ext (fun x : real => @lem1340155 x)). Qed.
Lemma lem1340157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1340158 : term37 = term46.
Proof. exact (MK_COMB (@lem1340157) (@lem1340156)). Qed.
Lemma lem1340159 : (term36 = term37) = (term33 = term46).
Proof. exact (MK_COMB (@lem1340154) (@lem1340158)). Qed.
Lemma lem1340160 : term33 = term46.
Proof. exact (EQ_MP (@lem1340159) (@lem1340148)). Qed.
Lemma lem1340173 : term32 = term46.
Proof. exact (TRANS (@lem1340141) (@lem1340160)). Qed.
Lemma lem1340174 : term46.
Proof. exact (EQ_MP (@lem1340173) (@lem1332639)). Qed.
