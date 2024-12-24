Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_OF_NUM_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1318933_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_add_spec.
Require Import treal_eq_spec.
Require Import treal_of_num_spec.
Lemma lem1327050 : term0.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1327051 (n : nat) : term1 n.
Proof. exact (@lem1327050 n). Qed.
Lemma lem1327052 (n : nat) : (term1 n) = ((term2 n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1327057 (m : nat) : term3 m.
Proof. exact (@lem1318933 m). Qed.
Lemma lem1327058 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1327059 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1327058 m) (@lem1327057 m)). Qed.
Lemma lem1327060 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1327059 m n). Qed.
Lemma lem1327061 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1327063 (x1 : hreal) : term8 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1327064 (x1 : hreal) : (term8 x1) = (term9 x1).
Proof. exact (eq_refl (term8 x1)). Qed.
Lemma lem1327065 (x1 : hreal) : term9 x1.
Proof. exact (EQ_MP (@lem1327064 x1) (@lem1327063 x1)). Qed.
Lemma lem1327066 (x1 : hreal) (x2 : hreal) : term10 x1 x2.
Proof. exact (@lem1327065 x1 x2). Qed.
Lemma lem1327067 (x1 : hreal) (x2 : hreal) : (term10 x1 x2) = (term11 x1 x2).
Proof. exact (eq_refl (term10 x1 x2)). Qed.
Lemma lem1327068 (x1 : hreal) (x2 : hreal) : term11 x1 x2.
Proof. exact (EQ_MP (@lem1327067 x1 x2) (@lem1327066 x1 x2)). Qed.
Lemma lem1327069 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term12 x1 x2 y1.
Proof. exact (@lem1327068 x1 x2 y1). Qed.
Lemma lem1327070 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term12 x1 x2 y1) = (term13 x1 x2 y1).
Proof. exact (eq_refl (term12 x1 x2 y1)). Qed.
Lemma lem1327071 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term13 x1 x2 y1.
Proof. exact (EQ_MP (@lem1327070 x1 x2 y1) (@lem1327069 x1 x2 y1)). Qed.
Lemma lem1327072 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term14 x1 x2 y1 y2.
Proof. exact (@lem1327071 x1 x2 y1 y2). Qed.
Lemma lem1327073 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term14 x1 x2 y1 y2) = ((term15 x1 y1 x2 y2) = (term16 x1 x2 y1 y2)).
Proof. exact (eq_refl (term14 x1 x2 y1 y2)). Qed.
Lemma lem1327075 (x1 : hreal) : term17 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1327076 (x1 : hreal) : (term17 x1) = (term18 x1).
Proof. exact (eq_refl (term17 x1)). Qed.
Lemma lem1327077 (x1 : hreal) : term18 x1.
Proof. exact (EQ_MP (@lem1327076 x1) (@lem1327075 x1)). Qed.
Lemma lem1327078 (x1 : hreal) (y2 : hreal) : term19 x1 y2.
Proof. exact (@lem1327077 x1 y2). Qed.
Lemma lem1327079 (x1 : hreal) (y2 : hreal) : (term19 x1 y2) = (term20 x1 y2).
Proof. exact (eq_refl (term19 x1 y2)). Qed.
Lemma lem1327080 (x1 : hreal) (y2 : hreal) : term20 x1 y2.
Proof. exact (EQ_MP (@lem1327079 x1 y2) (@lem1327078 x1 y2)). Qed.
Lemma lem1327081 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term21 x1 y2 x2.
Proof. exact (@lem1327080 x1 y2 x2). Qed.
Lemma lem1327082 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term21 x1 y2 x2) = (term22 x1 y2 x2).
Proof. exact (eq_refl (term21 x1 y2 x2)). Qed.
Lemma lem1327083 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term22 x1 y2 x2.
Proof. exact (EQ_MP (@lem1327082 x1 y2 x2) (@lem1327081 x1 y2 x2)). Qed.
Lemma lem1327084 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term23 x1 y2 x2 y1.
Proof. exact (@lem1327083 x1 y2 x2 y1). Qed.
Lemma lem1327085 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term23 x1 y2 x2 y1) = ((term24 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term23 x1 y2 x2 y1)). Qed.
Lemma lem1327087 (n : nat) : term25 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1327088 (n : nat) : (term25 n) = ((treal_of_num n) = (term26 n)).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem1327099 (n : nat) : (treal_of_num n) = (term26 n).
Proof. exact (EQ_MP (@lem1327088 n) (@lem1327087 n)). Qed.
Lemma lem1327100 (m : nat) : (treal_of_num m) = (term26 m).
Proof. exact (@lem1327099 m). Qed.
Lemma lem1327101 : treal_add = treal_add.
Proof. exact (eq_refl treal_add). Qed.
Lemma lem1327102 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem1327101) (@lem1327100 m)). Qed.
Lemma lem1327104 (n : nat) : (treal_of_num n) = (term26 n).
Proof. exact (EQ_MP (@lem1327088 n) (@lem1327087 n)). Qed.
Lemma lem1327105 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem1327102 m) (@lem1327104 n)). Qed.
Lemma lem1327107 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term15 x1 y1 x2 y2) = (term16 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327073 x1 x2 y1 y2) (@lem1327072 x1 x2 y1 y2)). Qed.
Lemma lem1327108 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (@lem1327107 (hreal_of_num m) (hreal_of_num n) term32 term32). Qed.
Lemma lem1327110 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1327061 m n) (@lem1327060 m n)). Qed.
Lemma lem1327111 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1327112 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem1327111) (@lem1327110 m n)). Qed.
Lemma lem1327114 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1327061 m n) (@lem1327060 m n)). Qed.
Lemma lem1327115 : term35 = term36.
Proof. exact (@lem1327114 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1327117 (n : nat) : (term2 n) = n.
Proof. exact (EQ_MP (@lem1327052 n) (@lem1327051 n)). Qed.
Lemma lem1327118 : term37 = (NUMERAL 0).
Proof. exact (@lem1327117 (NUMERAL 0)). Qed.
Lemma lem1327119 : hreal_of_num = hreal_of_num.
Proof. exact (eq_refl hreal_of_num). Qed.
Lemma lem1327120 : term36 = term32.
Proof. exact (MK_COMB (@lem1327119) (@lem1327118)). Qed.
Lemma lem1327121 : term35 = term32.
Proof. exact (TRANS (@lem1327115) (@lem1327120)). Qed.
Lemma lem1327122 (m : nat) (n : nat) : (term31 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem1327112 m n) (@lem1327121)). Qed.
Lemma lem1327123 (m : nat) (n : nat) : (term30 m n) = (term38 m n).
Proof. exact (TRANS (@lem1327108 m n) (@lem1327122 m n)). Qed.
Lemma lem1327124 (m : nat) (n : nat) : (term29 m n) = (term38 m n).
Proof. exact (TRANS (@lem1327105 m n) (@lem1327123 m n)). Qed.
Lemma lem1327125 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1327126 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1327125) (@lem1327124 m n)). Qed.
Lemma lem1327128 (n : nat) : (treal_of_num n) = (term26 n).
Proof. exact (EQ_MP (@lem1327088 n) (@lem1327087 n)). Qed.
Lemma lem1327129 (m : nat) (n : nat) : (term41 m n) = (term38 m n).
Proof. exact (@lem1327128 (Nat.add m n)). Qed.
Lemma lem1327130 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem1327126 m n) (@lem1327129 m n)). Qed.
Lemma lem1327132 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term24 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1327085 x1 y2 x2 y1) (@lem1327084 x1 y2 x2 y1)). Qed.
Lemma lem1327133 (m : nat) (n : nat) : (term43 m n) = ((term44 m n) = (term44 m n)).
Proof. exact (@lem1327132 (term7 m n) term32 (term7 m n) term32). Qed.
Lemma lem1327135 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327136 (x : hreal) : (x = x) = True.
Proof. exact (@lem1327135 hreal x). Qed.
Lemma lem1327137 (m : nat) (n : nat) : ((term44 m n) = (term44 m n)) = True.
Proof. exact (@lem1327136 (term44 m n)). Qed.
Lemma lem1327138 (m : nat) (n : nat) : (term43 m n) = True.
Proof. exact (TRANS (@lem1327133 m n) (@lem1327137 m n)). Qed.
Lemma lem1327139 (m : nat) (n : nat) : (term42 m n) = True.
Proof. exact (TRANS (@lem1327130 m n) (@lem1327138 m n)). Qed.
Lemma lem1327140 (m : nat) : (term45 m) = term46.
Proof. exact (fun_ext (fun n : nat => @lem1327139 m n)). Qed.
Lemma lem1327141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1327142 (m : nat) : (term47 m) = term48.
Proof. exact (MK_COMB (@lem1327141) (@lem1327140 m)). Qed.
Lemma lem1327144 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327145 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1327144 nat t). Qed.
Lemma lem1327146 : term48 = True.
Proof. exact (@lem1327145 True). Qed.
Lemma lem1327147 (m : nat) : (term47 m) = True.
Proof. exact (TRANS (@lem1327142 m) (@lem1327146)). Qed.
Lemma lem1327148 : term51 = term46.
Proof. exact (fun_ext (fun m : nat => @lem1327147 m)). Qed.
Lemma lem1327149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1327150 : term52 = term48.
Proof. exact (MK_COMB (@lem1327149) (@lem1327148)). Qed.
Lemma lem1327152 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327153 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1327152 nat t). Qed.
Lemma lem1327154 : term48 = True.
Proof. exact (@lem1327153 True). Qed.
Lemma lem1327155 : term52 = True.
Proof. exact (TRANS (@lem1327150) (@lem1327154)). Qed.
Lemma lem1327156 : True = term52.
Proof. exact (SYM (@lem1327155)). Qed.
Lemma lem1327157 : term52.
Proof. exact (EQ_MP (@lem1327156) (@lem0)). Qed.
