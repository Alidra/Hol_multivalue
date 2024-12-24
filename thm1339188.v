Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1339188_term_abbrevs.
Require Import TREAL_ADD_LDISTRIB_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1339045 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1339046 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term1 y x z) = ((term2 x y z) = (term3 y x z)).
Proof. exact (@lem1339045 (term4 x y z) (term5 y x z)). Qed.
Lemma lem1339050 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1339051 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term2 x y z) = (term8 x y z).
Proof. exact (@lem1339050 x (treal_add y z)). Qed.
Lemma lem1339053 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term9 x1 y1) = (term10 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1339054 (y : prod hreal hreal) (z : prod hreal hreal) : (term9 y z) = (term10 y z).
Proof. exact (@lem1339053 y z). Qed.
Lemma lem1339055 (x : prod hreal hreal) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1339056 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term8 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem1339055 x) (@lem1339054 y z)). Qed.
Lemma lem1339057 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term2 x y z) = (term12 x y z).
Proof. exact (TRANS (@lem1339051 x y z) (@lem1339056 x y z)). Qed.
Lemma lem1339058 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1339059 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem1339058) (@lem1339057 x y z)). Qed.
Lemma lem1339061 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term9 x1 y1) = (term10 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1339062 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term3 y x z) = (term15 y x z).
Proof. exact (@lem1339061 (treal_mul x y) (treal_mul x z)). Qed.
Lemma lem1339064 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1339065 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (@lem1339064 x y). Qed.
Lemma lem1339066 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1339067 (x : prod hreal hreal) (y : prod hreal hreal) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1339066) (@lem1339065 x y)). Qed.
Lemma lem1339069 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1339070 (x : prod hreal hreal) (z : prod hreal hreal) : (term6 x z) = (term7 x z).
Proof. exact (@lem1339069 x z). Qed.
Lemma lem1339071 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term15 y x z) = (term18 y x z).
Proof. exact (MK_COMB (@lem1339067 x y) (@lem1339070 x z)). Qed.
Lemma lem1339072 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term3 y x z) = (term18 y x z).
Proof. exact (TRANS (@lem1339062 y x z) (@lem1339071 y x z)). Qed.
Lemma lem1339073 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : ((term2 x y z) = (term3 y x z)) = ((term12 x y z) = (term18 y x z)).
Proof. exact (MK_COMB (@lem1339059 x y z) (@lem1339072 y x z)). Qed.
Lemma lem1339076 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term1 y x z) = ((term12 x y z) = (term18 y x z)).
Proof. exact (TRANS (@lem1339046 y x z) (@lem1339073 y x z)). Qed.
Lemma lem1339077 (y : prod hreal hreal) (x : prod hreal hreal) : (term19 y x) = (term20 y x).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1339076 y x z)). Qed.
Lemma lem1339078 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339079 (y : prod hreal hreal) (x : prod hreal hreal) : (term21 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1339078) (@lem1339077 y x)). Qed.
Lemma lem1339085 (P : real -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339086 (y : prod hreal hreal) (x : prod hreal hreal) : (term25 y x) = (term26 y x).
Proof. exact (@lem1339085 (term27 y x)). Qed.
Lemma lem1339087 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term28 y x z) = ((term12 x y z) = (term18 y x z)).
Proof. exact (eq_refl (term28 y x z)). Qed.
Lemma lem1339088 (y : prod hreal hreal) (x : prod hreal hreal) : (term29 y x) = (term20 y x).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1339087 y x z)). Qed.
Lemma lem1339089 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339090 (y : prod hreal hreal) (x : prod hreal hreal) : (term25 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1339089) (@lem1339088 y x)). Qed.
Lemma lem1339091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339092 (y : prod hreal hreal) (x : prod hreal hreal) : (term30 y x) = (term31 y x).
Proof. exact (MK_COMB (@lem1339091) (@lem1339090 y x)). Qed.
Lemma lem1339093 (y : prod hreal hreal) (x : prod hreal hreal) (z : real) : (term32 y x z) = ((term33 x y z) = (term34 y x z)).
Proof. exact (eq_refl (term32 y x z)). Qed.
Lemma lem1339094 (y : prod hreal hreal) (x : prod hreal hreal) : (term35 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : real => @lem1339093 y x z)). Qed.
Lemma lem1339095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339096 (y : prod hreal hreal) (x : prod hreal hreal) : (term26 y x) = (term36 y x).
Proof. exact (MK_COMB (@lem1339095) (@lem1339094 y x)). Qed.
Lemma lem1339097 (y : prod hreal hreal) (x : prod hreal hreal) : ((term25 y x) = (term26 y x)) = ((term22 y x) = (term36 y x)).
Proof. exact (MK_COMB (@lem1339092 y x) (@lem1339096 y x)). Qed.
Lemma lem1339098 (y : prod hreal hreal) (x : prod hreal hreal) : (term22 y x) = (term36 y x).
Proof. exact (EQ_MP (@lem1339097 y x) (@lem1339086 y x)). Qed.
Lemma lem1339107 (y : prod hreal hreal) (x : prod hreal hreal) : (term21 y x) = (term36 y x).
Proof. exact (TRANS (@lem1339079 y x) (@lem1339098 y x)). Qed.
Lemma lem1339108 (x : prod hreal hreal) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339107 y x)). Qed.
Lemma lem1339109 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339110 (x : prod hreal hreal) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1339109) (@lem1339108 x)). Qed.
Lemma lem1339116 (P : real -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339117 (x : prod hreal hreal) : (term41 x) = (term42 x).
Proof. exact (@lem1339116 (term43 x)). Qed.
Lemma lem1339118 (y : prod hreal hreal) (x : prod hreal hreal) : (term44 x y) = (term36 y x).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1339119 (x : prod hreal hreal) : (term45 x) = (term38 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339118 y x)). Qed.
Lemma lem1339120 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339121 (x : prod hreal hreal) : (term41 x) = (term40 x).
Proof. exact (MK_COMB (@lem1339120) (@lem1339119 x)). Qed.
Lemma lem1339122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339123 (x : prod hreal hreal) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1339122) (@lem1339121 x)). Qed.
Lemma lem1339124 (y : real) (x : prod hreal hreal) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1339125 (x : prod hreal hreal) : (term50 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1339124 y x)). Qed.
Lemma lem1339126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339127 (x : prod hreal hreal) : (term42 x) = (term51 x).
Proof. exact (MK_COMB (@lem1339126) (@lem1339125 x)). Qed.
Lemma lem1339128 (x : prod hreal hreal) : ((term41 x) = (term42 x)) = ((term40 x) = (term51 x)).
Proof. exact (MK_COMB (@lem1339123 x) (@lem1339127 x)). Qed.
Lemma lem1339129 (x : prod hreal hreal) : (term40 x) = (term51 x).
Proof. exact (EQ_MP (@lem1339128 x) (@lem1339117 x)). Qed.
Lemma lem1339144 (x : prod hreal hreal) : (term39 x) = (term51 x).
Proof. exact (TRANS (@lem1339110 x) (@lem1339129 x)). Qed.
Lemma lem1339145 : term52 = term53.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339144 x)). Qed.
Lemma lem1339146 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339147 : term54 = term55.
Proof. exact (MK_COMB (@lem1339146) (@lem1339145)). Qed.
Lemma lem1339153 (P : real -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339154 : term56 = term57.
Proof. exact (@lem1339153 term58). Qed.
Lemma lem1339155 (x : prod hreal hreal) : (term59 x) = (term51 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1339156 : term60 = term53.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339155 x)). Qed.
Lemma lem1339157 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339158 : term56 = term55.
Proof. exact (MK_COMB (@lem1339157) (@lem1339156)). Qed.
Lemma lem1339159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339160 : term61 = term62.
Proof. exact (MK_COMB (@lem1339159) (@lem1339158)). Qed.
Lemma lem1339161 (x : real) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1339162 : term65 = term58.
Proof. exact (fun_ext (fun x : real => @lem1339161 x)). Qed.
Lemma lem1339163 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339164 : term57 = term66.
Proof. exact (MK_COMB (@lem1339163) (@lem1339162)). Qed.
Lemma lem1339165 : (term56 = term57) = (term55 = term66).
Proof. exact (MK_COMB (@lem1339160) (@lem1339164)). Qed.
Lemma lem1339166 : term55 = term66.
Proof. exact (EQ_MP (@lem1339165) (@lem1339154)). Qed.
Lemma lem1339187 : term54 = term66.
Proof. exact (TRANS (@lem1339147) (@lem1339166)). Qed.
Lemma lem1339188 : term66.
Proof. exact (EQ_MP (@lem1339187) (@lem1329890)). Qed.
