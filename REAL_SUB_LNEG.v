Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_LNEG_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1519013 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519014 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1519013 (term4 x)). Qed.
Lemma lem1519015 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (term7 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1519016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519018 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1519016) (@lem1519015 x y)). Qed.
Lemma lem1519019 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1519018 x y)). Qed.
Lemma lem1519020 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519021 (x : real) : (term3 x) = (term12 x).
Proof. exact (MK_COMB (@lem1519020) (@lem1519019 x)). Qed.
Lemma lem1519022 (x : real) : (term2 x) = (term12 x).
Proof. exact (TRANS (@lem1519014 x) (@lem1519021 x)). Qed.
Lemma lem1519023 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519024 : term13 = term14.
Proof. exact (@lem1519023 term15). Qed.
Lemma lem1519025 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1519026 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519027 (x : real) : (term18 x) = (term2 x).
Proof. exact (MK_COMB (@lem1519026) (@lem1519025 x)). Qed.
Lemma lem1519028 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1519027 x) (@lem1519022 x)). Qed.
Lemma lem1519029 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1519028 x)). Qed.
Lemma lem1519030 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519031 : term14 = term21.
Proof. exact (MK_COMB (@lem1519030) (@lem1519029)). Qed.
Lemma lem1519033 : term13 = term21.
Proof. exact (TRANS (@lem1519024) (@lem1519031)). Qed.
Lemma lem1519036 (x : real) (y : real) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1519037 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1519036 x y)). Qed.
Lemma lem1519038 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519039 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1519038) (@lem1519037 x)). Qed.
Lemma lem1519040 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1519039 x)). Qed.
Lemma lem1519041 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519042 : term21 = term21.
Proof. exact (MK_COMB (@lem1519041) (@lem1519040)). Qed.
Lemma lem1519043 : term13 = term21.
Proof. exact (TRANS (@lem1519033) (@lem1519042)). Qed.
Lemma lem1519044 (x : real) (y : real) : (term9 x y) = (term22 x y).
Proof. exact (@lem1483554 (term6 x y) (term7 x y)). Qed.
Lemma lem1519054 (x : real) (y : real) : (term7 x y) = (term23 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1519061 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (@lem1483508 x term25 y). Qed.
Lemma lem1519063 (x : real) (y : real) : (term7 x y) = (term24 x y).
Proof. exact (TRANS (@lem1519054 x y) (@lem1519061 x y)). Qed.
Lemma lem1519064 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519071 (x : real) : (real_neg x) = (term26 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1519072 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1519073 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1519072) (@lem1519071 x)). Qed.
Lemma lem1519074 (x : real) (y : real) : (term6 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1519073 x) (@lem1519064 y)). Qed.
Lemma lem1519081 (x : real) (y : real) : (term29 x y) = (term24 x y).
Proof. exact (@lem1483519 (term26 x) y). Qed.
Lemma lem1519082 (x : real) (y : real) : (term6 x y) = (term24 x y).
Proof. exact (TRANS (@lem1519074 x y) (@lem1519081 x y)). Qed.
Lemma lem1519083 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1519084 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1519083) (@lem1519082 x y)). Qed.
Lemma lem1519085 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1519084 x y) (@lem1519063 x y)). Qed.
Lemma lem1519086 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (@lem1483519 (term24 x y) (term24 x y)). Qed.
Lemma lem1519087 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem1483508 (term26 x) term25 (term26 y)). Qed.
Lemma lem1519088 (y : real) : (term37 y) = (term38 y).
Proof. exact (@lem1483476 term25 term25 y). Qed.
Lemma lem1519090 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1519091 : term41 = term42.
Proof. exact (@lem1519090 term43 term43). Qed.
Lemma lem1519092 : (term44 = (BIT1 0)) = (term45 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1519093 : term45 = term43.
Proof. exact (EQ_MP (@lem1519092) (@lem940073)). Qed.
Lemma lem1519094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1519095 : term42 = term46.
Proof. exact (MK_COMB (@lem1519094) (@lem1519093)). Qed.
Lemma lem1519096 : term41 = term46.
Proof. exact (TRANS (@lem1519091) (@lem1519095)). Qed.
Lemma lem1519097 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519098 : term47 = term48.
Proof. exact (MK_COMB (@lem1519097) (@lem1519096)). Qed.
Lemma lem1519099 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519100 (y : real) : (term38 y) = (term49 y).
Proof. exact (MK_COMB (@lem1519098) (@lem1519099 y)). Qed.
Lemma lem1519101 (y : real) : (term37 y) = (term49 y).
Proof. exact (TRANS (@lem1519088 y) (@lem1519100 y)). Qed.
Lemma lem1519102 (y : real) : (term49 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1519103 (y : real) : (term37 y) = y.
Proof. exact (TRANS (@lem1519101 y) (@lem1519102 y)). Qed.
Lemma lem1519104 (x : real) : (term37 x) = (term38 x).
Proof. exact (@lem1483476 term25 term25 x). Qed.
Lemma lem1519106 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1519107 : term41 = term42.
Proof. exact (@lem1519106 term43 term43). Qed.
Lemma lem1519108 : (term44 = (BIT1 0)) = (term45 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1519109 : term45 = term43.
Proof. exact (EQ_MP (@lem1519108) (@lem940073)). Qed.
Lemma lem1519110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1519111 : term42 = term46.
Proof. exact (MK_COMB (@lem1519110) (@lem1519109)). Qed.
Lemma lem1519112 : term41 = term46.
Proof. exact (TRANS (@lem1519107) (@lem1519111)). Qed.
Lemma lem1519113 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519114 : term47 = term48.
Proof. exact (MK_COMB (@lem1519113) (@lem1519112)). Qed.
Lemma lem1519115 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1519116 (x : real) : (term38 x) = (term49 x).
Proof. exact (MK_COMB (@lem1519114) (@lem1519115 x)). Qed.
Lemma lem1519117 (x : real) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1519104 x) (@lem1519116 x)). Qed.
Lemma lem1519118 (x : real) : (term49 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1519119 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1519117 x) (@lem1519118 x)). Qed.
Lemma lem1519120 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519121 (x : real) : (term50 x) = (real_add x).
Proof. exact (MK_COMB (@lem1519120) (@lem1519119 x)). Qed.
Lemma lem1519122 (x : real) (y : real) : (term36 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1519121 x) (@lem1519103 y)). Qed.
Lemma lem1519123 (x : real) (y : real) : (term35 x y) = (real_add x y).
Proof. exact (TRANS (@lem1519087 x y) (@lem1519122 x y)). Qed.
Lemma lem1519124 (x : real) (y : real) : (term51 x y) = (term51 x y).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1519125 (x : real) (y : real) : (term34 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1519124 x y) (@lem1519123 x y)). Qed.
Lemma lem1519126 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483480 (term26 x) x (term26 y) y). Qed.
Lemma lem1519127 (x : real) : (term54 x) = (term55 x).
Proof. exact (@lem1483440 term25 x). Qed.
Lemma lem1519129 (m : nat) : (term56 m) = term57.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519130 : term58 = term57.
Proof. exact (@lem1519129 term43). Qed.
Lemma lem1519131 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519132 : term59 = term60.
Proof. exact (MK_COMB (@lem1519131) (@lem1519130)). Qed.
Lemma lem1519133 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1519134 (x : real) : (term55 x) = (term61 x).
Proof. exact (MK_COMB (@lem1519132) (@lem1519133 x)). Qed.
Lemma lem1519135 (x : real) : (term54 x) = (term61 x).
Proof. exact (TRANS (@lem1519127 x) (@lem1519134 x)). Qed.
Lemma lem1519136 (x : real) : (term61 x) = term57.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1519137 (x : real) : (term54 x) = term57.
Proof. exact (TRANS (@lem1519135 x) (@lem1519136 x)). Qed.
Lemma lem1519138 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519139 (x : real) : (term62 x) = term63.
Proof. exact (MK_COMB (@lem1519138) (@lem1519137 x)). Qed.
Lemma lem1519140 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1483440 term25 y). Qed.
Lemma lem1519142 (m : nat) : (term56 m) = term57.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519143 : term58 = term57.
Proof. exact (@lem1519142 term43). Qed.
Lemma lem1519144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519145 : term59 = term60.
Proof. exact (MK_COMB (@lem1519144) (@lem1519143)). Qed.
Lemma lem1519146 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519147 (y : real) : (term55 y) = (term61 y).
Proof. exact (MK_COMB (@lem1519145) (@lem1519146 y)). Qed.
Lemma lem1519148 (y : real) : (term54 y) = (term61 y).
Proof. exact (TRANS (@lem1519140 y) (@lem1519147 y)). Qed.
Lemma lem1519149 (y : real) : (term61 y) = term57.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1519150 (y : real) : (term54 y) = term57.
Proof. exact (TRANS (@lem1519148 y) (@lem1519149 y)). Qed.
Lemma lem1519151 (x : real) (y : real) : (term53 x y) = term64.
Proof. exact (MK_COMB (@lem1519139 x) (@lem1519150 y)). Qed.
Lemma lem1519152 (x : real) (y : real) : (term52 x y) = term64.
Proof. exact (TRANS (@lem1519126 x y) (@lem1519151 x y)). Qed.
Lemma lem1519153 : term64 = term57.
Proof. exact (@lem1483448 term57). Qed.
Lemma lem1519154 (x : real) (y : real) : (term52 x y) = term57.
Proof. exact (TRANS (@lem1519152 x y) (@lem1519153)). Qed.
Lemma lem1519155 (x : real) (y : real) : (term34 x y) = term57.
Proof. exact (TRANS (@lem1519125 x y) (@lem1519154 x y)). Qed.
Lemma lem1519156 (x : real) (y : real) : (term33 x y) = term57.
Proof. exact (TRANS (@lem1519086 x y) (@lem1519155 x y)). Qed.
Lemma lem1519157 (x : real) (y : real) : (term32 x y) = term57.
Proof. exact (TRANS (@lem1519085 x y) (@lem1519156 x y)). Qed.
Lemma lem1519158 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1519159 (x : real) (y : real) : (term65 x y) = term66.
Proof. exact (MK_COMB (@lem1519158) (@lem1519157 x y)). Qed.
Lemma lem1519160 : term66 = term67.
Proof. exact (@lem1483512 term57). Qed.
Lemma lem1519162 (x : nat) : (term68 x) = term57.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1519163 : term67 = term57.
Proof. exact (@lem1519162 term43). Qed.
Lemma lem1519164 : term66 = term57.
Proof. exact (TRANS (@lem1519160) (@lem1519163)). Qed.
Lemma lem1519165 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1519166 (x : real) (y : real) : ((term65 x y) = term66) = ((term65 x y) = term57).
Proof. exact (MK_COMB (@lem1519165 x y) (@lem1519164)). Qed.
Lemma lem1519167 (x : real) (y : real) : (term65 x y) = term57.
Proof. exact (EQ_MP (@lem1519166 x y) (@lem1519159 x y)). Qed.
Lemma lem1519168 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1519169 (x : real) (y : real) : (term70 x y) = term71.
Proof. exact (MK_COMB (@lem1519168) (@lem1519167 x y)). Qed.
Lemma lem1519170 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1519171 (x : real) (y : real) : (term72 x y) = term73.
Proof. exact (MK_COMB (@lem1519169 x y) (@lem1519170)). Qed.
Lemma lem1519172 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1519173 (x : real) (y : real) : (term74 x y) = term71.
Proof. exact (MK_COMB (@lem1519172) (@lem1519157 x y)). Qed.
Lemma lem1519174 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1519175 (x : real) (y : real) : (term75 x y) = term73.
Proof. exact (MK_COMB (@lem1519173 x y) (@lem1519174)). Qed.
Lemma lem1519176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519177 (x : real) (y : real) : (term76 x y) = term77.
Proof. exact (MK_COMB (@lem1519176) (@lem1519175 x y)). Qed.
Lemma lem1519178 (x : real) (y : real) : (term22 x y) = term78.
Proof. exact (MK_COMB (@lem1519177 x y) (@lem1519171 x y)). Qed.
Lemma lem1519179 (x : real) (y : real) : (term9 x y) = term78.
Proof. exact (TRANS (@lem1519044 x y) (@lem1519178 x y)). Qed.
Lemma lem1519180 (x : real) : (term11 x) = term79.
Proof. exact (fun_ext (fun y : real => @lem1519179 x y)). Qed.
Lemma lem1519181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519182 (x : real) : (term12 x) = term80.
Proof. exact (MK_COMB (@lem1519181) (@lem1519180 x)). Qed.
Lemma lem1519183 : term20 = term81.
Proof. exact (fun_ext (fun x : real => @lem1519182 x)). Qed.
Lemma lem1519184 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519185 : term21 = term82.
Proof. exact (MK_COMB (@lem1519184) (@lem1519183)). Qed.
Lemma lem1519186 : term13 = term82.
Proof. exact (TRANS (@lem1519043) (@lem1519185)). Qed.
Lemma lem1519188 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519189 (t : Prop) : (term84 t) = t.
Proof. exact (@lem1519188 real t). Qed.
Lemma lem1519190 : term82 = term80.
Proof. exact (@lem1519189 term80). Qed.
Lemma lem1519192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1519193 (P : real -> Prop) (Q : real -> Prop) : (term87 P Q) = (term88 P Q).
Proof. exact (@lem1519192 real P Q). Qed.
Lemma lem1519194 : term89 = term90.
Proof. exact (@lem1519193 term91 term91). Qed.
Lemma lem1519195 (y : real) : (term92 y) = term73.
Proof. exact (eq_refl (term92 y)). Qed.
Lemma lem1519196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519197 (y : real) : (term93 y) = term77.
Proof. exact (MK_COMB (@lem1519196) (@lem1519195 y)). Qed.
Lemma lem1519198 (y : real) : (term92 y) = term73.
Proof. exact (eq_refl (term92 y)). Qed.
Lemma lem1519199 (y : real) : (term94 y) = term78.
Proof. exact (MK_COMB (@lem1519197 y) (@lem1519198 y)). Qed.
Lemma lem1519200 : term95 = term79.
Proof. exact (fun_ext (fun y : real => @lem1519199 y)). Qed.
Lemma lem1519201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519202 : term89 = term80.
Proof. exact (MK_COMB (@lem1519201) (@lem1519200)). Qed.
Lemma lem1519203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1519204 : term96 = term97.
Proof. exact (MK_COMB (@lem1519203) (@lem1519202)). Qed.
Lemma lem1519205 (y : real) : (term92 y) = term73.
Proof. exact (eq_refl (term92 y)). Qed.
Lemma lem1519206 : term98 = term91.
Proof. exact (fun_ext (fun y : real => @lem1519205 y)). Qed.
Lemma lem1519207 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519208 : term99 = term100.
Proof. exact (MK_COMB (@lem1519207) (@lem1519206)). Qed.
Lemma lem1519209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519210 : term101 = term102.
Proof. exact (MK_COMB (@lem1519209) (@lem1519208)). Qed.
Lemma lem1519211 (y : real) : (term92 y) = term73.
Proof. exact (eq_refl (term92 y)). Qed.
Lemma lem1519212 : term98 = term91.
Proof. exact (fun_ext (fun y : real => @lem1519211 y)). Qed.
Lemma lem1519213 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519214 : term99 = term100.
Proof. exact (MK_COMB (@lem1519213) (@lem1519212)). Qed.
Lemma lem1519215 : term90 = term103.
Proof. exact (MK_COMB (@lem1519210) (@lem1519214)). Qed.
Lemma lem1519216 : (term89 = term90) = (term80 = term103).
Proof. exact (MK_COMB (@lem1519204) (@lem1519215)). Qed.
Lemma lem1519217 : term80 = term103.
Proof. exact (EQ_MP (@lem1519216) (@lem1519194)). Qed.
Lemma lem1519218 : term82 = term103.
Proof. exact (TRANS (@lem1519190) (@lem1519217)). Qed.
Lemma lem1519220 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519221 (t : Prop) : (term84 t) = t.
Proof. exact (@lem1519220 real t). Qed.
Lemma lem1519222 : term100 = term73.
Proof. exact (@lem1519221 term73). Qed.
Lemma lem1519223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519224 : term102 = term77.
Proof. exact (MK_COMB (@lem1519223) (@lem1519222)). Qed.
Lemma lem1519226 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519227 (t : Prop) : (term84 t) = t.
Proof. exact (@lem1519226 real t). Qed.
Lemma lem1519228 : term100 = term73.
Proof. exact (@lem1519227 term73). Qed.
Lemma lem1519229 : term103 = term78.
Proof. exact (MK_COMB (@lem1519224) (@lem1519228)). Qed.
Lemma lem1519232 : term82 = term78.
Proof. exact (TRANS (@lem1519218) (@lem1519229)). Qed.
Lemma lem1519241 : term13 = term78.
Proof. exact (TRANS (@lem1519186) (@lem1519232)). Qed.
Lemma lem1519251 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem1519252 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1519254 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1519255 : term73 = term105.
Proof. exact (@lem1519254 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1519256 : term105 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1519257 : term73 = False.
Proof. exact (TRANS (@lem1519255) (@lem1519256)). Qed.
Lemma lem1519258 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1519257) (@lem1519252 h1)). Qed.
Lemma lem1519259 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1519261 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1519262 : term73 = term105.
Proof. exact (@lem1519261 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1519263 : term105 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1519264 : term73 = False.
Proof. exact (TRANS (@lem1519262) (@lem1519263)). Qed.
Lemma lem1519265 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1519264) (@lem1519259 h1)). Qed.
Lemma lem1519266 (h1 : term78) : False.
Proof. exact (or_elim (@lem1519251 h1) (fun h0 : term73 => @lem1519258 h0) (fun h0 : term73 => @lem1519265 h0)). Qed.
Lemma lem1519268 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem1519269 (h1 : term78) : term78 = False.
Proof. exact (prop_ext (fun h2 : term78 => @lem1519266 h1) (fun h2 : False => @lem1519268 h1)). Qed.
Lemma lem1519270 (h1 : term78) : False.
Proof. exact (EQ_MP (@lem1519269 h1) (@lem1519268 h1)). Qed.
Lemma lem1519271 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1519272 (h1 : term13) : term78.
Proof. exact (EQ_MP (@lem1519241) (@lem1519271 h1)). Qed.
Lemma lem1519273 (h1 : term13) : term78 = False.
Proof. exact (prop_ext (fun h2 : term78 => @lem1519270 h2) (fun h2 : False => @lem1519272 h1)). Qed.
Lemma lem1519274 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1519273 h1) (@lem1519272 h1)). Qed.
Lemma lem1519275 : term106.
Proof. exact (fun h0 : term13 => @lem1519274 h0). Qed.
Lemma lem1519276 : term107.
Proof. exact (@lem1386578 term108). Qed.
Lemma lem1519277 : term108.
Proof. exact (@lem1519276 (@lem1519275)). Qed.
