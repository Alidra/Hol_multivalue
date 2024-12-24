Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_EXISTS_term_abbrevs.
Require Import INT_IMAGE_spec.
Require Import INT_POS_spec.
Require Import MONO_EXISTS_spec.
Require Import OR_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1396812_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982717_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318541_spec.
Require Import thm2318542_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2327115 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem2327116 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem2327117 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem2327115 A P Q h2 (@lem2327116 A P Q h1)). Qed.
Lemma lem2327118 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem2327117 A P Q h1 h0). Qed.
Lemma lem2327119 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem2327120 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem2327118 A P Q h1 (@lem2327119 A P Q h2)). Qed.
Lemma lem2327121 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem2327120 A P Q h0 h1). Qed.
Lemma lem2327122 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem2327121 A P Q h0). Qed.
Lemma lem2327124 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (@lem5488 A P). Qed.
Lemma lem2327125 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (eq_refl (term5 A P)). Qed.
Lemma lem2327126 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (EQ_MP (@lem2327125 A P) (@lem2327124 A P)). Qed.
Lemma lem2327127 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem2327126 A P Q). Qed.
Lemma lem2327128 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term7 A P Q) = ((term8 A P Q) = (term9 A P Q)).
Proof. exact (eq_refl (term7 A P Q)). Qed.
Lemma lem2327130 (x : int) : term10 x.
Proof. exact (@lem2295400 x). Qed.
Lemma lem2327131 (x : int) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem2327132 (x : int) : term11 x.
Proof. exact (EQ_MP (@lem2327131 x) (@lem2327130 x)). Qed.
Lemma lem2327133 (x : int) (h1 : term12 x) : term12 x.
Proof. exact (h1). Qed.
Lemma lem2327134 (x : int) (n : nat) (h1 : x = (int_of_num n)) : x = (int_of_num n).
Proof. exact (h1). Qed.
Lemma lem2327135 (x : int) (h1 : term13 x) : term13 x.
Proof. exact (h1). Qed.
Lemma lem2327136 (n : nat) : term14 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem2327137 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem2327138 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem2327137 n) (@lem2327136 n)). Qed.
Lemma lem2327139 (n : nat) : (term15 n) = ((term15 n) = True).
Proof. exact (@lem7 (term15 n)). Qed.
Lemma lem2327142 (x : int) (n : nat) (h1 : x = (int_of_num n)) : x = (int_of_num n).
Proof. exact (h1). Qed.
Lemma lem2327143 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem2327144 (x : int) (n : nat) (h1 : x = (int_of_num n)) : (term13 x) = (term15 n).
Proof. exact (MK_COMB (@lem2327143) (@lem2327142 x n h1)). Qed.
Lemma lem2327146 (n : nat) : (term15 n) = True.
Proof. exact (EQ_MP (@lem2327139 n) (@lem2327138 n)). Qed.
Lemma lem2327147 (x : int) (n : nat) (h1 : x = (int_of_num n)) : (term13 x) = True.
Proof. exact (TRANS (@lem2327144 x n h1) (@lem2327146 n)). Qed.
Lemma lem2327148 (x : int) (n : nat) (h1 : x = (int_of_num n)) : True = (term13 x).
Proof. exact (SYM (@lem2327147 x n h1)). Qed.
Lemma lem2327149 (x : int) (n : nat) (h1 : x = (int_of_num n)) : term13 x.
Proof. exact (EQ_MP (@lem2327148 x n h1) (@lem0)). Qed.
Lemma lem2327168 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem2327128 A P Q) (@lem2327127 A P Q)). Qed.
Lemma lem2327169 (P : nat -> Prop) (Q : nat -> Prop) : (term17 P Q) = (term18 P Q).
Proof. exact (@lem2327168 nat P Q). Qed.
Lemma lem2327170 (x : int) : (term19 x) = (term20 x).
Proof. exact (@lem2327169 (term21 x) (term22 x)). Qed.
Lemma lem2327171 (x : int) (n : nat) : (term23 x n) = (x = (int_of_num n)).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem2327172 (x : int) : (term24 x) = (term21 x).
Proof. exact (fun_ext (fun n : nat => @lem2327171 x n)). Qed.
Lemma lem2327173 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327174 (x : int) : (term25 x) = (term12 x).
Proof. exact (MK_COMB (@lem2327173) (@lem2327172 x)). Qed.
Lemma lem2327175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327176 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2327175) (@lem2327174 x)). Qed.
Lemma lem2327177 (x : int) (n : nat) : (term28 x n) = (x = (term29 n)).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem2327178 (x : int) : (term30 x) = (term22 x).
Proof. exact (fun_ext (fun n : nat => @lem2327177 x n)). Qed.
Lemma lem2327179 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327180 (x : int) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem2327179) (@lem2327178 x)). Qed.
Lemma lem2327181 (x : int) : (term19 x) = (term11 x).
Proof. exact (MK_COMB (@lem2327176 x) (@lem2327180 x)). Qed.
Lemma lem2327182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2327183 (x : int) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem2327182) (@lem2327181 x)). Qed.
Lemma lem2327184 (x : int) (n : nat) : (term23 x n) = (x = (int_of_num n)).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem2327185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327186 (x : int) (n : nat) : (term35 x n) = (term36 x n).
Proof. exact (MK_COMB (@lem2327185) (@lem2327184 x n)). Qed.
Lemma lem2327187 (x : int) (n : nat) : (term28 x n) = (x = (term29 n)).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem2327188 (x : int) (n : nat) : (term37 x n) = (term38 x n).
Proof. exact (MK_COMB (@lem2327186 x n) (@lem2327187 x n)). Qed.
Lemma lem2327189 (x : int) : (term39 x) = (term40 x).
Proof. exact (fun_ext (fun n : nat => @lem2327188 x n)). Qed.
Lemma lem2327190 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327191 (x : int) : (term20 x) = (term41 x).
Proof. exact (MK_COMB (@lem2327190) (@lem2327189 x)). Qed.
Lemma lem2327192 (x : int) : ((term19 x) = (term20 x)) = ((term11 x) = (term41 x)).
Proof. exact (MK_COMB (@lem2327183 x) (@lem2327191 x)). Qed.
Lemma lem2327193 (x : int) : (term11 x) = (term41 x).
Proof. exact (EQ_MP (@lem2327192 x) (@lem2327170 x)). Qed.
Lemma lem2327204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2327205 (x : int) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem2327204) (@lem2327193 x)). Qed.
Lemma lem2327212 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2327213 (x : int) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem2327205 x) (@lem2327212 x)). Qed.
Lemma lem2327216 (x : int) : (term45 x) = (term44 x).
Proof. exact (SYM (@lem2327213 x)). Qed.
Lemma lem2327218 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem2327122 A P Q (@lem7401 A P Q)). Qed.
Lemma lem2327219 (P : nat -> Prop) (Q : nat -> Prop) : term46 P Q.
Proof. exact (@lem2327218 nat P Q). Qed.
Lemma lem2327220 (x : int) : term47 x.
Proof. exact (@lem2327219 (term40 x) (term21 x)). Qed.
Lemma lem2327221 (x : int) (n : nat) : (term48 x n) = (term38 x n).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem2327222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2327223 (x : int) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem2327222) (@lem2327221 x n)). Qed.
Lemma lem2327224 (x : int) (n : nat) : (term23 x n) = (x = (int_of_num n)).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem2327225 (x : int) (n : nat) : (term51 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem2327223 x n) (@lem2327224 x n)). Qed.
Lemma lem2327226 (x : int) : (term53 x) = (term54 x).
Proof. exact (fun_ext (fun n : nat => @lem2327225 x n)). Qed.
Lemma lem2327227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2327228 (x : int) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem2327227) (@lem2327226 x)). Qed.
Lemma lem2327229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2327230 (x : int) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem2327229) (@lem2327228 x)). Qed.
Lemma lem2327231 (x : int) (n : nat) : (term48 x n) = (term38 x n).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem2327232 (x : int) : (term59 x) = (term40 x).
Proof. exact (fun_ext (fun n : nat => @lem2327231 x n)). Qed.
Lemma lem2327233 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327234 (x : int) : (term60 x) = (term41 x).
Proof. exact (MK_COMB (@lem2327233) (@lem2327232 x)). Qed.
Lemma lem2327235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2327236 (x : int) : (term61 x) = (term43 x).
Proof. exact (MK_COMB (@lem2327235) (@lem2327234 x)). Qed.
Lemma lem2327237 (x : int) (n : nat) : (term23 x n) = (x = (int_of_num n)).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem2327238 (x : int) : (term24 x) = (term21 x).
Proof. exact (fun_ext (fun n : nat => @lem2327237 x n)). Qed.
Lemma lem2327239 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327240 (x : int) : (term25 x) = (term12 x).
Proof. exact (MK_COMB (@lem2327239) (@lem2327238 x)). Qed.
Lemma lem2327241 (x : int) : (term62 x) = (term45 x).
Proof. exact (MK_COMB (@lem2327236 x) (@lem2327240 x)). Qed.
Lemma lem2327242 (x : int) : (term47 x) = (term63 x).
Proof. exact (MK_COMB (@lem2327230 x) (@lem2327241 x)). Qed.
Lemma lem2327243 (x : int) : term63 x.
Proof. exact (EQ_MP (@lem2327242 x) (@lem2327220 x)). Qed.
Lemma lem2327244 (x : int) : (term64 x) = (term65 x).
Proof. exact (@lem2318604 (term65 x)). Qed.
Lemma lem2327271 (x : int) (n : nat) : (term66 x n) = (term67 x n).
Proof. exact (@lem17362 (term38 x n) (x = (int_of_num n))). Qed.
Lemma lem2327272 (P : nat -> Prop) : (term68 P) = (term69 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem2327273 (x : int) : (term70 x) = (term71 x).
Proof. exact (@lem2327272 (term54 x)). Qed.
Lemma lem2327274 (x : int) (n : nat) : (term72 x n) = (term52 x n).
Proof. exact (eq_refl (term72 x n)). Qed.
Lemma lem2327275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2327276 (x : int) (n : nat) : (term73 x n) = (term66 x n).
Proof. exact (MK_COMB (@lem2327275) (@lem2327274 x n)). Qed.
Lemma lem2327277 (x : int) (n : nat) : (term73 x n) = (term67 x n).
Proof. exact (TRANS (@lem2327276 x n) (@lem2327271 x n)). Qed.
Lemma lem2327278 (x : int) : (term74 x) = (term75 x).
Proof. exact (fun_ext (fun n : nat => @lem2327277 x n)). Qed.
Lemma lem2327279 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327280 (x : int) : (term71 x) = (term76 x).
Proof. exact (MK_COMB (@lem2327279) (@lem2327278 x)). Qed.
Lemma lem2327281 (x : int) : (term70 x) = (term76 x).
Proof. exact (TRANS (@lem2327273 x) (@lem2327280 x)). Qed.
Lemma lem2327283 (x : int) : (term77 x) = (term77 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2327284 (x : int) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem2327283 x) (@lem2327281 x)). Qed.
Lemma lem2327285 (x : int) : (term80 x) = (term78 x).
Proof. exact (@lem17362 (term13 x) (term56 x)). Qed.
Lemma lem2327287 (x : int) : (term80 x) = (term79 x).
Proof. exact (TRANS (@lem2327285 x) (@lem2327284 x)). Qed.
Lemma lem2327298 (x : int) (n : nat) : (term67 x n) = (term67 x n).
Proof. exact (eq_refl (term67 x n)). Qed.
Lemma lem2327299 (x : int) : (term75 x) = (term75 x).
Proof. exact (fun_ext (fun n : nat => @lem2327298 x n)). Qed.
Lemma lem2327300 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327301 (x : int) : (term76 x) = (term76 x).
Proof. exact (MK_COMB (@lem2327300) (@lem2327299 x)). Qed.
Lemma lem2327304 (x : int) : (term77 x) = (term77 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2327305 (x : int) : (term79 x) = (term79 x).
Proof. exact (MK_COMB (@lem2327304 x) (@lem2327301 x)). Qed.
Lemma lem2327306 (x : int) : (term80 x) = (term79 x).
Proof. exact (TRANS (@lem2327287 x) (@lem2327305 x)). Qed.
Lemma lem2327309 (x : int) (y : int) : (int_le x y) = (term81 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2327310 (x : int) : (term13 x) = (term82 x).
Proof. exact (@lem2327309 term83 x). Qed.
Lemma lem2327312 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327313 : term85 = term86.
Proof. exact (@lem2327312 (NUMERAL 0)). Qed.
Lemma lem2327314 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2327315 : term87 = term88.
Proof. exact (MK_COMB (@lem2327314) (@lem2327313)). Qed.
Lemma lem2327316 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2327317 (x : int) : (term82 x) = (term89 x).
Proof. exact (MK_COMB (@lem2327315) (@lem2327316 x)). Qed.
Lemma lem2327319 (x : int) : (term13 x) = (term89 x).
Proof. exact (TRANS (@lem2327310 x) (@lem2327317 x)). Qed.
Lemma lem2327322 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2327323 (x : int) (n : nat) : (x = (int_of_num n)) = ((real_of_int x) = (term84 n)).
Proof. exact (@lem2327322 x (int_of_num n)). Qed.
Lemma lem2327327 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327328 (x : int) : (term90 x) = (term90 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem2327329 (x : int) (n : nat) : ((real_of_int x) = (term84 n)) = ((real_of_int x) = (real_of_num n)).
Proof. exact (MK_COMB (@lem2327328 x) (@lem2327327 n)). Qed.
Lemma lem2327331 (x : int) (n : nat) : (x = (int_of_num n)) = ((real_of_int x) = (real_of_num n)).
Proof. exact (TRANS (@lem2327323 x n) (@lem2327329 x n)). Qed.
Lemma lem2327334 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2327335 (x : int) (n : nat) : (x = (term29 n)) = ((real_of_int x) = (term91 n)).
Proof. exact (@lem2327334 x (term29 n)). Qed.
Lemma lem2327339 (x : int) : (term92 x) = (term93 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2327340 (n : nat) : (term91 n) = (term94 n).
Proof. exact (@lem2327339 (int_of_num n)). Qed.
Lemma lem2327342 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327343 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2327344 (n : nat) : (term94 n) = (term95 n).
Proof. exact (MK_COMB (@lem2327343) (@lem2327342 n)). Qed.
Lemma lem2327345 (n : nat) : (term91 n) = (term95 n).
Proof. exact (TRANS (@lem2327340 n) (@lem2327344 n)). Qed.
Lemma lem2327346 (x : int) : (term90 x) = (term90 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem2327347 (x : int) (n : nat) : ((real_of_int x) = (term91 n)) = ((real_of_int x) = (term95 n)).
Proof. exact (MK_COMB (@lem2327346 x) (@lem2327345 n)). Qed.
Lemma lem2327349 (x : int) (n : nat) : (x = (term29 n)) = ((real_of_int x) = (term95 n)).
Proof. exact (TRANS (@lem2327335 x n) (@lem2327347 x n)). Qed.
Lemma lem2327350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327351 (x : int) (n : nat) : (term36 x n) = (term96 x n).
Proof. exact (MK_COMB (@lem2327350) (@lem2327331 x n)). Qed.
Lemma lem2327352 (x : int) (n : nat) : (term38 x n) = (term97 x n).
Proof. exact (MK_COMB (@lem2327351 x n) (@lem2327349 x n)). Qed.
Lemma lem2327354 (y : int) (x : int) : (term98 x y) = (term99 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2327355 (n : nat) (x : int) : (term100 x n) = (term101 n x).
Proof. exact (@lem2327354 (int_of_num n) x). Qed.
Lemma lem2327357 (x : int) (y : int) : (int_le x y) = (term81 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2327358 (x : int) (n : nat) : (term102 x n) = (term103 x n).
Proof. exact (@lem2327357 (term104 x) (int_of_num n)). Qed.
Lemma lem2327360 (x : int) (y : int) : (term105 x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2327361 (x : int) : (term107 x) = (term108 x).
Proof. exact (@lem2327360 x term109). Qed.
Lemma lem2327363 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327364 : term110 = term111.
Proof. exact (@lem2327363 term112). Qed.
Lemma lem2327365 (x : int) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2327366 (x : int) : (term108 x) = (term114 x).
Proof. exact (MK_COMB (@lem2327365 x) (@lem2327364)). Qed.
Lemma lem2327367 (x : int) : (term107 x) = (term114 x).
Proof. exact (TRANS (@lem2327361 x) (@lem2327366 x)). Qed.
Lemma lem2327368 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2327369 (x : int) : (term115 x) = (term116 x).
Proof. exact (MK_COMB (@lem2327368) (@lem2327367 x)). Qed.
Lemma lem2327371 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327372 (x : int) (n : nat) : (term103 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2327369 x) (@lem2327371 n)). Qed.
Lemma lem2327373 (x : int) (n : nat) : (term102 x n) = (term117 x n).
Proof. exact (TRANS (@lem2327358 x n) (@lem2327372 x n)). Qed.
Lemma lem2327374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327375 (x : int) (n : nat) : (term118 x n) = (term119 x n).
Proof. exact (MK_COMB (@lem2327374) (@lem2327373 x n)). Qed.
Lemma lem2327377 (x : int) (y : int) : (int_le x y) = (term81 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2327378 (n : nat) (x : int) : (term120 n x) = (term121 n x).
Proof. exact (@lem2327377 (term122 n) x). Qed.
Lemma lem2327380 (x : int) (y : int) : (term105 x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2327381 (n : nat) : (term123 n) = (term124 n).
Proof. exact (@lem2327380 (int_of_num n) term109). Qed.
Lemma lem2327383 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327384 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2327385 (n : nat) : (term125 n) = (term126 n).
Proof. exact (MK_COMB (@lem2327384) (@lem2327383 n)). Qed.
Lemma lem2327387 (n : nat) : (term84 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2327388 : term110 = term111.
Proof. exact (@lem2327387 term112). Qed.
Lemma lem2327389 (n : nat) : (term124 n) = (term127 n).
Proof. exact (MK_COMB (@lem2327385 n) (@lem2327388)). Qed.
Lemma lem2327390 (n : nat) : (term123 n) = (term127 n).
Proof. exact (TRANS (@lem2327381 n) (@lem2327389 n)). Qed.
Lemma lem2327391 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2327392 (n : nat) : (term128 n) = (term129 n).
Proof. exact (MK_COMB (@lem2327391) (@lem2327390 n)). Qed.
Lemma lem2327393 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2327394 (n : nat) (x : int) : (term121 n x) = (term130 n x).
Proof. exact (MK_COMB (@lem2327392 n) (@lem2327393 x)). Qed.
Lemma lem2327395 (n : nat) (x : int) : (term120 n x) = (term130 n x).
Proof. exact (TRANS (@lem2327378 n x) (@lem2327394 n x)). Qed.
Lemma lem2327396 (n : nat) (x : int) : (term101 n x) = (term131 n x).
Proof. exact (MK_COMB (@lem2327375 x n) (@lem2327395 n x)). Qed.
Lemma lem2327397 (n : nat) (x : int) : (term100 x n) = (term131 n x).
Proof. exact (TRANS (@lem2327355 n x) (@lem2327396 n x)). Qed.
Lemma lem2327398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2327399 (x : int) (n : nat) : (term132 x n) = (term133 x n).
Proof. exact (MK_COMB (@lem2327398) (@lem2327352 x n)). Qed.
Lemma lem2327400 (n : nat) (x : int) : (term67 x n) = (term134 n x).
Proof. exact (MK_COMB (@lem2327399 x n) (@lem2327397 n x)). Qed.
Lemma lem2327401 (x : int) : (term75 x) = (term135 x).
Proof. exact (fun_ext (fun n : nat => @lem2327400 n x)). Qed.
Lemma lem2327402 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327403 (x : int) : (term76 x) = (term136 x).
Proof. exact (MK_COMB (@lem2327402) (@lem2327401 x)). Qed.
Lemma lem2327404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2327405 (x : int) : (term77 x) = (term137 x).
Proof. exact (MK_COMB (@lem2327404) (@lem2327319 x)). Qed.
Lemma lem2327406 (x : int) : (term79 x) = (term138 x).
Proof. exact (MK_COMB (@lem2327405 x) (@lem2327403 x)). Qed.
Lemma lem2327407 (x : int) : (term80 x) = (term138 x).
Proof. exact (TRANS (@lem2327306 x) (@lem2327406 x)). Qed.
Lemma lem2327411 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2327469 (x : int) : (term140 x) = (term138 x).
Proof. exact (@lem2327411 (term138 x)). Qed.
Lemma lem2327483 (n : nat) (x : int) : (term134 n x) = (term134 n x).
Proof. exact (eq_refl (term134 n x)). Qed.
Lemma lem2327484 (x : int) : (term135 x) = (term135 x).
Proof. exact (fun_ext (fun n : nat => @lem2327483 n x)). Qed.
Lemma lem2327485 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327486 (x : int) : (term136 x) = (term136 x).
Proof. exact (MK_COMB (@lem2327485) (@lem2327484 x)). Qed.
Lemma lem2327488 (x : int) : (term137 x) = (term137 x).
Proof. exact (eq_refl (term137 x)). Qed.
Lemma lem2327489 (x : int) : (term138 x) = (term138 x).
Proof. exact (MK_COMB (@lem2327488 x) (@lem2327486 x)). Qed.
Lemma lem2327490 (x : int) : (term140 x) = (term138 x).
Proof. exact (TRANS (@lem2327469 x) (@lem2327489 x)). Qed.
Lemma lem2327503 (n : nat) (x : int) : (term134 n x) = (term134 n x).
Proof. exact (eq_refl (term134 n x)). Qed.
Lemma lem2327504 (x : int) : (term135 x) = (term135 x).
Proof. exact (fun_ext (fun n : nat => @lem2327503 n x)). Qed.
Lemma lem2327505 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327506 (x : int) : (term136 x) = (term136 x).
Proof. exact (MK_COMB (@lem2327505) (@lem2327504 x)). Qed.
Lemma lem2327509 (x : int) : (term137 x) = (term137 x).
Proof. exact (eq_refl (term137 x)). Qed.
Lemma lem2327510 (x : int) : (term138 x) = (term138 x).
Proof. exact (MK_COMB (@lem2327509 x) (@lem2327506 x)). Qed.
Lemma lem2327511 (x : int) : (term140 x) = (term138 x).
Proof. exact (TRANS (@lem2327490 x) (@lem2327510 x)). Qed.
Lemma lem2327512 (x : int) : (term89 x) = (term141 x).
Proof. exact (@lem1988287 (real_of_int x) term86). Qed.
Lemma lem2327518 (x : int) : (term142 x) = (term143 x).
Proof. exact (@lem1982792 (real_of_int x) term86). Qed.
Lemma lem2327520 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2327521 : term86 = term145.
Proof. exact (@lem2327520 (NUMERAL 0)). Qed.
Lemma lem2327523 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2327524 : term147 = term148.
Proof. exact (@lem2327523 term112). Qed.
Lemma lem2327525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2327526 : term149 = term150.
Proof. exact (MK_COMB (@lem2327525) (@lem2327524)). Qed.
Lemma lem2327527 : term151 = term152.
Proof. exact (MK_COMB (@lem2327526) (@lem2327521)). Qed.
Lemma lem2327528 : term152 = term153.
Proof. exact (@lem1981613 term147 term86 term111 term111). Qed.
Lemma lem2327530 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2327531 : term156 = term157.
Proof. exact (@lem2327530 term112 term112). Qed.
Lemma lem2327532 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327533 : term159 = term112.
Proof. exact (EQ_MP (@lem2327532) (@lem940073)). Qed.
Lemma lem2327534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327535 : term157 = term111.
Proof. exact (MK_COMB (@lem2327534) (@lem2327533)). Qed.
Lemma lem2327536 : term156 = term111.
Proof. exact (TRANS (@lem2327531) (@lem2327535)). Qed.
Lemma lem2327538 (x : nat) : (term160 x) = term86.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2327539 : term151 = term86.
Proof. exact (@lem2327538 term112). Qed.
Lemma lem2327540 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2327541 : term161 = term162.
Proof. exact (MK_COMB (@lem2327540) (@lem2327539)). Qed.
Lemma lem2327542 : term153 = term145.
Proof. exact (MK_COMB (@lem2327541) (@lem2327536)). Qed.
Lemma lem2327543 : term152 = term145.
Proof. exact (TRANS (@lem2327528) (@lem2327542)). Qed.
Lemma lem2327544 : term151 = term145.
Proof. exact (TRANS (@lem2327527) (@lem2327543)). Qed.
Lemma lem2327546 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2327547 : term145 = term86.
Proof. exact (@lem2327546 term86). Qed.
Lemma lem2327548 : term151 = term86.
Proof. exact (TRANS (@lem2327544) (@lem2327547)). Qed.
Lemma lem2327549 (x : int) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2327550 (x : int) : (term143 x) = (term164 x).
Proof. exact (MK_COMB (@lem2327549 x) (@lem2327548)). Qed.
Lemma lem2327551 (x : int) : (term164 x) = (real_of_int x).
Proof. exact (@lem1982723 (real_of_int x)). Qed.
Lemma lem2327552 (x : int) : (term143 x) = (real_of_int x).
Proof. exact (TRANS (@lem2327550 x) (@lem2327551 x)). Qed.
Lemma lem2327554 (x : int) : (term142 x) = (real_of_int x).
Proof. exact (TRANS (@lem2327518 x) (@lem2327552 x)). Qed.
Lemma lem2327555 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2327556 (x : int) : (term165 x) = (term166 x).
Proof. exact (MK_COMB (@lem2327555) (@lem2327554 x)). Qed.
Lemma lem2327557 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2327558 (x : int) : (term141 x) = (term167 x).
Proof. exact (MK_COMB (@lem2327556 x) (@lem2327557)). Qed.
Lemma lem2327559 (x : int) : (term89 x) = (term167 x).
Proof. exact (TRANS (@lem2327512 x) (@lem2327558 x)). Qed.
Lemma lem2327560 (x : int) (n : nat) : ((real_of_int x) = (real_of_num n)) = ((term168 x n) = term86).
Proof. exact (@lem1988293 (real_of_int x) (real_of_num n)). Qed.
Lemma lem2327573 (x : int) (n : nat) : (term168 x n) = (term169 x n).
Proof. exact (@lem1982792 (real_of_int x) (real_of_num n)). Qed.
Lemma lem2327574 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2327575 (x : int) (n : nat) : (term170 x n) = (term171 x n).
Proof. exact (MK_COMB (@lem2327574) (@lem2327573 x n)). Qed.
Lemma lem2327576 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2327577 (x : int) (n : nat) : ((term168 x n) = term86) = ((term169 x n) = term86).
Proof. exact (MK_COMB (@lem2327575 x n) (@lem2327576)). Qed.
Lemma lem2327578 (x : int) (n : nat) : ((real_of_int x) = (real_of_num n)) = ((term169 x n) = term86).
Proof. exact (TRANS (@lem2327560 x n) (@lem2327577 x n)). Qed.
Lemma lem2327579 (x : int) (n : nat) : ((real_of_int x) = (term95 n)) = ((term172 x n) = term86).
Proof. exact (@lem1988293 (real_of_int x) (term95 n)). Qed.
Lemma lem2327586 (n : nat) : (term95 n) = (term173 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2327589 (x : int) : (term174 x) = (term174 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem2327590 (x : int) (n : nat) : (term172 x n) = (term175 x n).
Proof. exact (MK_COMB (@lem2327589 x) (@lem2327586 n)). Qed.
Lemma lem2327591 (x : int) (n : nat) : (term175 x n) = (term176 x n).
Proof. exact (@lem1982792 (real_of_int x) (term173 n)). Qed.
Lemma lem2327592 (n : nat) : (term177 n) = (term178 n).
Proof. exact (@lem1982749 term147 term147 (real_of_num n)). Qed.
Lemma lem2327594 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2327595 : term147 = term148.
Proof. exact (@lem2327594 term112). Qed.
Lemma lem2327597 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2327598 : term147 = term148.
Proof. exact (@lem2327597 term112). Qed.
Lemma lem2327599 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2327600 : term149 = term150.
Proof. exact (MK_COMB (@lem2327599) (@lem2327598)). Qed.
Lemma lem2327601 : term179 = term180.
Proof. exact (MK_COMB (@lem2327600) (@lem2327595)). Qed.
Lemma lem2327602 : term180 = term181.
Proof. exact (@lem1981613 term147 term147 term111 term111). Qed.
Lemma lem2327604 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2327605 : term156 = term157.
Proof. exact (@lem2327604 term112 term112). Qed.
Lemma lem2327606 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327607 : term159 = term112.
Proof. exact (EQ_MP (@lem2327606) (@lem940073)). Qed.
Lemma lem2327608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327609 : term157 = term111.
Proof. exact (MK_COMB (@lem2327608) (@lem2327607)). Qed.
Lemma lem2327610 : term156 = term111.
Proof. exact (TRANS (@lem2327605) (@lem2327609)). Qed.
Lemma lem2327612 (m : nat) (n : nat) : (term182 m n) = (term155 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2327613 : term179 = term157.
Proof. exact (@lem2327612 term112 term112). Qed.
Lemma lem2327614 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327615 : term159 = term112.
Proof. exact (EQ_MP (@lem2327614) (@lem940073)). Qed.
Lemma lem2327616 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327617 : term157 = term111.
Proof. exact (MK_COMB (@lem2327616) (@lem2327615)). Qed.
Lemma lem2327618 : term179 = term111.
Proof. exact (TRANS (@lem2327613) (@lem2327617)). Qed.
Lemma lem2327619 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2327620 : term183 = term184.
Proof. exact (MK_COMB (@lem2327619) (@lem2327618)). Qed.
Lemma lem2327621 : term181 = term185.
Proof. exact (MK_COMB (@lem2327620) (@lem2327610)). Qed.
Lemma lem2327622 : term180 = term185.
Proof. exact (TRANS (@lem2327602) (@lem2327621)). Qed.
Lemma lem2327623 : term179 = term185.
Proof. exact (TRANS (@lem2327601) (@lem2327622)). Qed.
Lemma lem2327625 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2327626 : term185 = term111.
Proof. exact (@lem2327625 term111). Qed.
Lemma lem2327627 : term179 = term111.
Proof. exact (TRANS (@lem2327623) (@lem2327626)). Qed.
Lemma lem2327628 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2327629 : term186 = term187.
Proof. exact (MK_COMB (@lem2327628) (@lem2327627)). Qed.
Lemma lem2327630 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2327631 (n : nat) : (term178 n) = (term188 n).
Proof. exact (MK_COMB (@lem2327629) (@lem2327630 n)). Qed.
Lemma lem2327632 (n : nat) : (term177 n) = (term188 n).
Proof. exact (TRANS (@lem2327592 n) (@lem2327631 n)). Qed.
Lemma lem2327633 (n : nat) : (term188 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2327634 (n : nat) : (term177 n) = (real_of_num n).
Proof. exact (TRANS (@lem2327632 n) (@lem2327633 n)). Qed.
Lemma lem2327635 (x : int) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2327638 (x : int) (n : nat) : (term176 x n) = (term189 x n).
Proof. exact (MK_COMB (@lem2327635 x) (@lem2327634 n)). Qed.
Lemma lem2327639 (x : int) (n : nat) : (term175 x n) = (term189 x n).
Proof. exact (TRANS (@lem2327591 x n) (@lem2327638 x n)). Qed.
Lemma lem2327640 (x : int) (n : nat) : (term172 x n) = (term189 x n).
Proof. exact (TRANS (@lem2327590 x n) (@lem2327639 x n)). Qed.
Lemma lem2327641 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2327642 (x : int) (n : nat) : (term190 x n) = (term191 x n).
Proof. exact (MK_COMB (@lem2327641) (@lem2327640 x n)). Qed.
Lemma lem2327643 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2327644 (x : int) (n : nat) : ((term172 x n) = term86) = ((term189 x n) = term86).
Proof. exact (MK_COMB (@lem2327642 x n) (@lem2327643)). Qed.
Lemma lem2327645 (x : int) (n : nat) : ((real_of_int x) = (term95 n)) = ((term189 x n) = term86).
Proof. exact (TRANS (@lem2327579 x n) (@lem2327644 x n)). Qed.
Lemma lem2327646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327647 (x : int) (n : nat) : (term96 x n) = (term192 x n).
Proof. exact (MK_COMB (@lem2327646) (@lem2327578 x n)). Qed.
Lemma lem2327648 (x : int) (n : nat) : (term97 x n) = (term193 x n).
Proof. exact (MK_COMB (@lem2327647 x n) (@lem2327645 x n)). Qed.
Lemma lem2327649 (n : nat) (x : int) : (term117 x n) = (term194 n x).
Proof. exact (@lem1988287 (real_of_num n) (term114 x)). Qed.
Lemma lem2327661 (n : nat) (x : int) : (term195 n x) = (term196 n x).
Proof. exact (@lem1982792 (real_of_num n) (term114 x)). Qed.
Lemma lem2327662 (x : int) : (term197 x) = (term198 x).
Proof. exact (@lem1982781 (real_of_int x) term147 term111). Qed.
Lemma lem2327664 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2327665 : term111 = term185.
Proof. exact (@lem2327664 term112). Qed.
Lemma lem2327667 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2327668 : term147 = term148.
Proof. exact (@lem2327667 term112). Qed.
Lemma lem2327669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2327670 : term149 = term150.
Proof. exact (MK_COMB (@lem2327669) (@lem2327668)). Qed.
Lemma lem2327671 : term199 = term200.
Proof. exact (MK_COMB (@lem2327670) (@lem2327665)). Qed.
Lemma lem2327672 : term200 = term201.
Proof. exact (@lem1981613 term147 term111 term111 term111). Qed.
Lemma lem2327674 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2327675 : term156 = term157.
Proof. exact (@lem2327674 term112 term112). Qed.
Lemma lem2327676 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327677 : term159 = term112.
Proof. exact (EQ_MP (@lem2327676) (@lem940073)). Qed.
Lemma lem2327678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327679 : term157 = term111.
Proof. exact (MK_COMB (@lem2327678) (@lem2327677)). Qed.
Lemma lem2327680 : term156 = term111.
Proof. exact (TRANS (@lem2327675) (@lem2327679)). Qed.
Lemma lem2327682 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2327683 : term199 = term204.
Proof. exact (@lem2327682 term112 term112). Qed.
Lemma lem2327684 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327685 : term159 = term112.
Proof. exact (EQ_MP (@lem2327684) (@lem940073)). Qed.
Lemma lem2327686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327687 : term157 = term111.
Proof. exact (MK_COMB (@lem2327686) (@lem2327685)). Qed.
Lemma lem2327688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2327689 : term204 = term147.
Proof. exact (MK_COMB (@lem2327688) (@lem2327687)). Qed.
Lemma lem2327690 : term199 = term147.
Proof. exact (TRANS (@lem2327683) (@lem2327689)). Qed.
Lemma lem2327691 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2327692 : term205 = term206.
Proof. exact (MK_COMB (@lem2327691) (@lem2327690)). Qed.
Lemma lem2327693 : term201 = term148.
Proof. exact (MK_COMB (@lem2327692) (@lem2327680)). Qed.
Lemma lem2327694 : term200 = term148.
Proof. exact (TRANS (@lem2327672) (@lem2327693)). Qed.
Lemma lem2327695 : term199 = term148.
Proof. exact (TRANS (@lem2327671) (@lem2327694)). Qed.
Lemma lem2327697 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2327698 : term148 = term147.
Proof. exact (@lem2327697 term147). Qed.
Lemma lem2327699 : term199 = term147.
Proof. exact (TRANS (@lem2327695) (@lem2327698)). Qed.
Lemma lem2327702 (x : int) : (term207 x) = (term207 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem2327703 (x : int) : (term198 x) = (term208 x).
Proof. exact (MK_COMB (@lem2327702 x) (@lem2327699)). Qed.
Lemma lem2327704 (x : int) : (term197 x) = (term208 x).
Proof. exact (TRANS (@lem2327662 x) (@lem2327703 x)). Qed.
Lemma lem2327705 (n : nat) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2327706 (n : nat) (x : int) : (term196 n x) = (term209 n x).
Proof. exact (MK_COMB (@lem2327705 n) (@lem2327704 x)). Qed.
Lemma lem2327711 (x : int) (n : nat) : (term209 n x) = (term210 x n).
Proof. exact (@lem1982757 (term211 x) (real_of_num n) term147). Qed.
Lemma lem2327712 (x : int) (n : nat) : (term196 n x) = (term210 x n).
Proof. exact (TRANS (@lem2327706 n x) (@lem2327711 x n)). Qed.
Lemma lem2327714 (x : int) (n : nat) : (term195 n x) = (term210 x n).
Proof. exact (TRANS (@lem2327661 n x) (@lem2327712 x n)). Qed.
Lemma lem2327715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2327716 (x : int) (n : nat) : (term212 n x) = (term213 x n).
Proof. exact (MK_COMB (@lem2327715) (@lem2327714 x n)). Qed.
Lemma lem2327717 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2327718 (x : int) (n : nat) : (term194 n x) = (term214 x n).
Proof. exact (MK_COMB (@lem2327716 x n) (@lem2327717)). Qed.
Lemma lem2327719 (x : int) (n : nat) : (term117 x n) = (term214 x n).
Proof. exact (TRANS (@lem2327649 n x) (@lem2327718 x n)). Qed.
Lemma lem2327720 (x : int) (n : nat) : (term130 n x) = (term215 x n).
Proof. exact (@lem1988287 (real_of_int x) (term127 n)). Qed.
Lemma lem2327732 (x : int) (n : nat) : (term216 x n) = (term217 x n).
Proof. exact (@lem1982792 (real_of_int x) (term127 n)). Qed.
Lemma lem2327733 (n : nat) : (term218 n) = (term219 n).
Proof. exact (@lem1982781 (real_of_num n) term147 term111). Qed.
Lemma lem2327735 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2327736 : term111 = term185.
Proof. exact (@lem2327735 term112). Qed.
Lemma lem2327738 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2327739 : term147 = term148.
Proof. exact (@lem2327738 term112). Qed.
Lemma lem2327740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2327741 : term149 = term150.
Proof. exact (MK_COMB (@lem2327740) (@lem2327739)). Qed.
Lemma lem2327742 : term199 = term200.
Proof. exact (MK_COMB (@lem2327741) (@lem2327736)). Qed.
Lemma lem2327743 : term200 = term201.
Proof. exact (@lem1981613 term147 term111 term111 term111). Qed.
Lemma lem2327745 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2327746 : term156 = term157.
Proof. exact (@lem2327745 term112 term112). Qed.
Lemma lem2327747 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327748 : term159 = term112.
Proof. exact (EQ_MP (@lem2327747) (@lem940073)). Qed.
Lemma lem2327749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327750 : term157 = term111.
Proof. exact (MK_COMB (@lem2327749) (@lem2327748)). Qed.
Lemma lem2327751 : term156 = term111.
Proof. exact (TRANS (@lem2327746) (@lem2327750)). Qed.
Lemma lem2327753 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2327754 : term199 = term204.
Proof. exact (@lem2327753 term112 term112). Qed.
Lemma lem2327755 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327756 : term159 = term112.
Proof. exact (EQ_MP (@lem2327755) (@lem940073)). Qed.
Lemma lem2327757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327758 : term157 = term111.
Proof. exact (MK_COMB (@lem2327757) (@lem2327756)). Qed.
Lemma lem2327759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2327760 : term204 = term147.
Proof. exact (MK_COMB (@lem2327759) (@lem2327758)). Qed.
Lemma lem2327761 : term199 = term147.
Proof. exact (TRANS (@lem2327754) (@lem2327760)). Qed.
Lemma lem2327762 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2327763 : term205 = term206.
Proof. exact (MK_COMB (@lem2327762) (@lem2327761)). Qed.
Lemma lem2327764 : term201 = term148.
Proof. exact (MK_COMB (@lem2327763) (@lem2327751)). Qed.
Lemma lem2327765 : term200 = term148.
Proof. exact (TRANS (@lem2327743) (@lem2327764)). Qed.
Lemma lem2327766 : term199 = term148.
Proof. exact (TRANS (@lem2327742) (@lem2327765)). Qed.
Lemma lem2327768 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2327769 : term148 = term147.
Proof. exact (@lem2327768 term147). Qed.
Lemma lem2327770 : term199 = term147.
Proof. exact (TRANS (@lem2327766) (@lem2327769)). Qed.
Lemma lem2327773 (n : nat) : (term220 n) = (term220 n).
Proof. exact (eq_refl (term220 n)). Qed.
Lemma lem2327774 (n : nat) : (term219 n) = (term221 n).
Proof. exact (MK_COMB (@lem2327773 n) (@lem2327770)). Qed.
Lemma lem2327775 (n : nat) : (term218 n) = (term221 n).
Proof. exact (TRANS (@lem2327733 n) (@lem2327774 n)). Qed.
Lemma lem2327776 (x : int) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2327779 (x : int) (n : nat) : (term217 x n) = (term222 x n).
Proof. exact (MK_COMB (@lem2327776 x) (@lem2327775 n)). Qed.
Lemma lem2327781 (x : int) (n : nat) : (term216 x n) = (term222 x n).
Proof. exact (TRANS (@lem2327732 x n) (@lem2327779 x n)). Qed.
Lemma lem2327782 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2327783 (x : int) (n : nat) : (term223 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2327782) (@lem2327781 x n)). Qed.
Lemma lem2327784 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2327785 (x : int) (n : nat) : (term215 x n) = (term225 x n).
Proof. exact (MK_COMB (@lem2327783 x n) (@lem2327784)). Qed.
Lemma lem2327786 (x : int) (n : nat) : (term130 n x) = (term225 x n).
Proof. exact (TRANS (@lem2327720 x n) (@lem2327785 x n)). Qed.
Lemma lem2327787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327788 (x : int) (n : nat) : (term119 x n) = (term226 x n).
Proof. exact (MK_COMB (@lem2327787) (@lem2327719 x n)). Qed.
Lemma lem2327789 (x : int) (n : nat) : (term131 n x) = (term227 x n).
Proof. exact (MK_COMB (@lem2327788 x n) (@lem2327786 x n)). Qed.
Lemma lem2327790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2327791 (x : int) (n : nat) : (term133 x n) = (term228 x n).
Proof. exact (MK_COMB (@lem2327790) (@lem2327648 x n)). Qed.
Lemma lem2327792 (x : int) (n : nat) : (term134 n x) = (term229 x n).
Proof. exact (MK_COMB (@lem2327791 x n) (@lem2327789 x n)). Qed.
Lemma lem2327793 (x : int) : (term135 x) = (term230 x).
Proof. exact (fun_ext (fun n : nat => @lem2327792 x n)). Qed.
Lemma lem2327794 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327795 (x : int) : (term136 x) = (term231 x).
Proof. exact (MK_COMB (@lem2327794) (@lem2327793 x)). Qed.
Lemma lem2327796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2327797 (x : int) : (term137 x) = (term232 x).
Proof. exact (MK_COMB (@lem2327796) (@lem2327559 x)). Qed.
Lemma lem2327798 (x : int) : (term138 x) = (term233 x).
Proof. exact (MK_COMB (@lem2327797 x) (@lem2327795 x)). Qed.
Lemma lem2327799 (x : int) : (term140 x) = (term233 x).
Proof. exact (TRANS (@lem2327511 x) (@lem2327798 x)). Qed.
Lemma lem2327850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2327851 (P : Prop) (Q : nat -> Prop) : (term236 P Q) = (term237 P Q).
Proof. exact (@lem2327850 nat P Q). Qed.
Lemma lem2327852 (x : int) : (term238 x) = (term239 x).
Proof. exact (@lem2327851 (term167 x) (term230 x)). Qed.
Lemma lem2327853 (x : int) (n : nat) : (term240 x n) = (term229 x n).
Proof. exact (eq_refl (term240 x n)). Qed.
Lemma lem2327854 (x : int) : (term241 x) = (term230 x).
Proof. exact (fun_ext (fun n : nat => @lem2327853 x n)). Qed.
Lemma lem2327855 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327856 (x : int) : (term242 x) = (term231 x).
Proof. exact (MK_COMB (@lem2327855) (@lem2327854 x)). Qed.
Lemma lem2327857 (x : int) : (term232 x) = (term232 x).
Proof. exact (eq_refl (term232 x)). Qed.
Lemma lem2327858 (x : int) : (term238 x) = (term233 x).
Proof. exact (MK_COMB (@lem2327857 x) (@lem2327856 x)). Qed.
Lemma lem2327859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2327860 (x : int) : (term243 x) = (term244 x).
Proof. exact (MK_COMB (@lem2327859) (@lem2327858 x)). Qed.
Lemma lem2327861 (x : int) (n : nat) : (term240 x n) = (term229 x n).
Proof. exact (eq_refl (term240 x n)). Qed.
Lemma lem2327862 (x : int) : (term232 x) = (term232 x).
Proof. exact (eq_refl (term232 x)). Qed.
Lemma lem2327863 (x : int) (n : nat) : (term245 x n) = (term246 x n).
Proof. exact (MK_COMB (@lem2327862 x) (@lem2327861 x n)). Qed.
Lemma lem2327864 (x : int) : (term247 x) = (term248 x).
Proof. exact (fun_ext (fun n : nat => @lem2327863 x n)). Qed.
Lemma lem2327865 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327866 (x : int) : (term239 x) = (term249 x).
Proof. exact (MK_COMB (@lem2327865) (@lem2327864 x)). Qed.
Lemma lem2327867 (x : int) : ((term238 x) = (term239 x)) = ((term233 x) = (term249 x)).
Proof. exact (MK_COMB (@lem2327860 x) (@lem2327866 x)). Qed.
Lemma lem2327869 (x : int) : (term233 x) = (term249 x).
Proof. exact (EQ_MP (@lem2327867 x) (@lem2327852 x)). Qed.
Lemma lem2327872 (x : int) : (term140 x) = (term249 x).
Proof. exact (TRANS (@lem2327799 x) (@lem2327869 x)). Qed.
Lemma lem2327886 (x : int) (n : nat) : (term229 x n) = (term250 x n).
Proof. exact (@lem19158 (term214 x n) (term193 x n) (term225 x n)). Qed.
Lemma lem2327893 (x : int) (n : nat) : (term251 x n) = (term252 x n).
Proof. exact (@lem19367 ((term169 x n) = term86) ((term189 x n) = term86) (term225 x n)). Qed.
Lemma lem2327900 (x : int) (n : nat) : (term253 x n) = (term254 x n).
Proof. exact (@lem19367 ((term169 x n) = term86) ((term189 x n) = term86) (term214 x n)). Qed.
Lemma lem2327901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327902 (x : int) (n : nat) : (term255 x n) = (term256 x n).
Proof. exact (MK_COMB (@lem2327901) (@lem2327900 x n)). Qed.
Lemma lem2327903 (x : int) (n : nat) : (term250 x n) = (term257 x n).
Proof. exact (MK_COMB (@lem2327902 x n) (@lem2327893 x n)). Qed.
Lemma lem2327905 (x : int) (n : nat) : (term229 x n) = (term257 x n).
Proof. exact (TRANS (@lem2327886 x n) (@lem2327903 x n)). Qed.
Lemma lem2327908 (x : int) : (term232 x) = (term232 x).
Proof. exact (eq_refl (term232 x)). Qed.
Lemma lem2327909 (x : int) (n : nat) : (term246 x n) = (term258 x n).
Proof. exact (MK_COMB (@lem2327908 x) (@lem2327905 x n)). Qed.
Lemma lem2327910 (x : int) (n : nat) : (term258 x n) = (term259 x n).
Proof. exact (@lem19158 (term254 x n) (term167 x) (term252 x n)). Qed.
Lemma lem2327917 (x : int) (n : nat) : (term260 x n) = (term261 x n).
Proof. exact (@lem19158 (term262 x n) (term167 x) (term263 x n)). Qed.
Lemma lem2327924 (x : int) (n : nat) : (term264 x n) = (term265 x n).
Proof. exact (@lem19158 (term266 x n) (term167 x) (term267 x n)). Qed.
Lemma lem2327925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2327926 (x : int) (n : nat) : (term268 x n) = (term269 x n).
Proof. exact (MK_COMB (@lem2327925) (@lem2327924 x n)). Qed.
Lemma lem2327927 (x : int) (n : nat) : (term259 x n) = (term270 x n).
Proof. exact (MK_COMB (@lem2327926 x n) (@lem2327917 x n)). Qed.
Lemma lem2327928 (x : int) (n : nat) : (term258 x n) = (term270 x n).
Proof. exact (TRANS (@lem2327910 x n) (@lem2327927 x n)). Qed.
Lemma lem2327929 (x : int) (n : nat) : (term246 x n) = (term270 x n).
Proof. exact (TRANS (@lem2327909 x n) (@lem2327928 x n)). Qed.
Lemma lem2327930 (x : int) : (term248 x) = (term271 x).
Proof. exact (fun_ext (fun n : nat => @lem2327929 x n)). Qed.
Lemma lem2327931 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2327932 (x : int) : (term249 x) = (term272 x).
Proof. exact (MK_COMB (@lem2327931) (@lem2327930 x)). Qed.
Lemma lem2327933 (x : int) : (term140 x) = (term272 x).
Proof. exact (TRANS (@lem2327872 x) (@lem2327932 x)). Qed.
Lemma lem2327955 (x : int) (n : nat) (h1 : term270 x n) : term270 x n.
Proof. exact (h1). Qed.
Lemma lem2327956 (x : int) (n : nat) (h1 : term265 x n) : term265 x n.
Proof. exact (h1). Qed.
Lemma lem2327957 (x : int) (n : nat) (h1 : term273 x n) : term273 x n.
Proof. exact (h1). Qed.
Lemma lem2327958 (x : int) (n : nat) (h1 : term273 x n) : term266 x n.
Proof. exact (proj2 (@lem2327957 x n h1)). Qed.
Lemma lem2327960 (x : int) (n : nat) (h1 : term273 x n) : term214 x n.
Proof. exact (proj2 (@lem2327958 x n h1)). Qed.
Lemma lem2327961 (x : int) (n : nat) (h1 : term273 x n) : (term169 x n) = term86.
Proof. exact (proj1 (@lem2327958 x n h1)). Qed.
Lemma lem2327964 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2327965 : term274 = term275.
Proof. exact (@lem2327964 term86 term111). Qed.
Lemma lem2327967 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2327968 : term111 = term185.
Proof. exact (@lem2327967 term112). Qed.
Lemma lem2327970 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2327971 : term86 = term145.
Proof. exact (@lem2327970 (NUMERAL 0)). Qed.
Lemma lem2327972 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2327973 : term276 = term277.
Proof. exact (MK_COMB (@lem2327972) (@lem2327971)). Qed.
Lemma lem2327974 : term275 = term278.
Proof. exact (MK_COMB (@lem2327973) (@lem2327968)). Qed.
Lemma lem2327975 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2327977 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2327978 : term275 = term281.
Proof. exact (@lem2327977 (NUMERAL 0) term112). Qed.
Lemma lem2327979 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2327980 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2327981 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2327980 h1) (fun h1 : term281 = True => @lem2327979)). Qed.
Lemma lem2327982 : term281 = True.
Proof. exact (EQ_MP (@lem2327981) (@lem2327979)). Qed.
Lemma lem2327983 : term275 = True.
Proof. exact (TRANS (@lem2327978) (@lem2327982)). Qed.
Lemma lem2327984 : True = term275.
Proof. exact (SYM (@lem2327983)). Qed.
Lemma lem2327985 : term275.
Proof. exact (EQ_MP (@lem2327984) (@lem0)). Qed.
Lemma lem2327986 : term283.
Proof. exact (@lem2327975 (@lem2327985)). Qed.
Lemma lem2327988 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2327989 : term275 = term281.
Proof. exact (@lem2327988 (NUMERAL 0) term112). Qed.
Lemma lem2327990 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2327991 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2327992 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2327991 h1) (fun h1 : term281 = True => @lem2327990)). Qed.
Lemma lem2327993 : term281 = True.
Proof. exact (EQ_MP (@lem2327992) (@lem2327990)). Qed.
Lemma lem2327994 : term275 = True.
Proof. exact (TRANS (@lem2327989) (@lem2327993)). Qed.
Lemma lem2327995 : True = term275.
Proof. exact (SYM (@lem2327994)). Qed.
Lemma lem2327996 : term275.
Proof. exact (EQ_MP (@lem2327995) (@lem0)). Qed.
Lemma lem2327997 : term278 = term284.
Proof. exact (@lem2327986 (@lem2327996)). Qed.
Lemma lem2327999 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328000 : term156 = term157.
Proof. exact (@lem2327999 term112 term112). Qed.
Lemma lem2328001 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328002 : term159 = term112.
Proof. exact (EQ_MP (@lem2328001) (@lem940073)). Qed.
Lemma lem2328003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328004 : term157 = term111.
Proof. exact (MK_COMB (@lem2328003) (@lem2328002)). Qed.
Lemma lem2328005 : term156 = term111.
Proof. exact (TRANS (@lem2328000) (@lem2328004)). Qed.
Lemma lem2328007 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328008 : term286 = term86.
Proof. exact (@lem2328007 term112). Qed.
Lemma lem2328009 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328010 : term287 = term276.
Proof. exact (MK_COMB (@lem2328009) (@lem2328008)). Qed.
Lemma lem2328011 : term284 = term275.
Proof. exact (MK_COMB (@lem2328010) (@lem2328005)). Qed.
Lemma lem2328013 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328014 : term275 = term281.
Proof. exact (@lem2328013 (NUMERAL 0) term112). Qed.
Lemma lem2328015 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328016 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328017 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328016 h1) (fun h1 : term281 = True => @lem2328015)). Qed.
Lemma lem2328018 : term281 = True.
Proof. exact (EQ_MP (@lem2328017) (@lem2328015)). Qed.
Lemma lem2328019 : term275 = True.
Proof. exact (TRANS (@lem2328014) (@lem2328018)). Qed.
Lemma lem2328020 : term284 = True.
Proof. exact (TRANS (@lem2328011) (@lem2328019)). Qed.
Lemma lem2328021 : term278 = True.
Proof. exact (TRANS (@lem2327997) (@lem2328020)). Qed.
Lemma lem2328022 : term275 = True.
Proof. exact (TRANS (@lem2327974) (@lem2328021)). Qed.
Lemma lem2328023 : term274 = True.
Proof. exact (TRANS (@lem2327965) (@lem2328022)). Qed.
Lemma lem2328024 : True = term274.
Proof. exact (SYM (@lem2328023)). Qed.
Lemma lem2328025 : term274.
Proof. exact (EQ_MP (@lem2328024) (@lem0)). Qed.
Lemma lem2328026 (x : int) (n : nat) (h1 : term273 x n) : term288 x n.
Proof. exact (conj (@lem2328025) (@lem2327960 x n h1)). Qed.
Lemma lem2328028 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2328029 (x : int) (n : nat) : term290 x n.
Proof. exact (@lem2328028 term111 (term210 x n)). Qed.
Lemma lem2328030 (x : int) (n : nat) (h1 : term273 x n) : term291 x n.
Proof. exact (@lem2328029 x n (@lem2328026 x n h1)). Qed.
Lemma lem2328031 (x : int) (n : nat) : (term292 x n) = (term210 x n).
Proof. exact (@lem1982733 (term210 x n)). Qed.
Lemma lem2328032 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2328033 (x : int) (n : nat) : (term293 x n) = (term213 x n).
Proof. exact (MK_COMB (@lem2328032) (@lem2328031 x n)). Qed.
Lemma lem2328034 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328035 (x : int) (n : nat) : (term291 x n) = (term214 x n).
Proof. exact (MK_COMB (@lem2328033 x n) (@lem2328034)). Qed.
Lemma lem2328036 (x : int) (n : nat) (h1 : term273 x n) : term214 x n.
Proof. exact (EQ_MP (@lem2328035 x n) (@lem2328030 x n h1)). Qed.
Lemma lem2328038 (y : real) : term294 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2328039 (x : int) (n : nat) : term295 x n.
Proof. exact (@lem2328038 (term169 x n)). Qed.
Lemma lem2328040 (x : int) (n : nat) (h1 : term273 x n) : term296 x n.
Proof. exact (@lem2328039 x n (@lem2327961 x n h1)). Qed.
Lemma lem2328041 (x : int) (n : nat) (h1 : term273 x n) : term297 x n.
Proof. exact (@lem2328040 x n h1 term111). Qed.
Lemma lem2328042 (x : int) (n : nat) : (term297 x n) = ((term298 x n) = term86).
Proof. exact (eq_refl (term297 x n)). Qed.
Lemma lem2328043 (x : int) (n : nat) (h1 : term273 x n) : (term298 x n) = term86.
Proof. exact (EQ_MP (@lem2328042 x n) (@lem2328041 x n h1)). Qed.
Lemma lem2328044 (x : int) (n : nat) : (term298 x n) = (term169 x n).
Proof. exact (@lem1982733 (term169 x n)). Qed.
Lemma lem2328045 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2328046 (x : int) (n : nat) : (term299 x n) = (term171 x n).
Proof. exact (MK_COMB (@lem2328045) (@lem2328044 x n)). Qed.
Lemma lem2328047 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328048 (x : int) (n : nat) : ((term298 x n) = term86) = ((term169 x n) = term86).
Proof. exact (MK_COMB (@lem2328046 x n) (@lem2328047)). Qed.
Lemma lem2328049 (x : int) (n : nat) (h1 : term273 x n) : (term169 x n) = term86.
Proof. exact (EQ_MP (@lem2328048 x n) (@lem2328043 x n h1)). Qed.
Lemma lem2328050 (x : int) (n : nat) (h1 : term273 x n) : term266 x n.
Proof. exact (conj (@lem2328049 x n h1) (@lem2328036 x n h1)). Qed.
Lemma lem2328052 (x : real) (y : real) : term300 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2328053 (x : int) (n : nat) : term301 x n.
Proof. exact (@lem2328052 (term169 x n) (term210 x n)). Qed.
Lemma lem2328054 (x : int) (n : nat) (h1 : term273 x n) : term302 x n.
Proof. exact (@lem2328053 x n (@lem2328050 x n h1)). Qed.
Lemma lem2328055 (x : int) (n : nat) : (term303 x n) = (term304 x n).
Proof. exact (@lem1982753 (real_of_int x) (term211 x) (term173 n) (term305 n)). Qed.
Lemma lem2328056 (x : int) : (term306 x) = (term307 x).
Proof. exact (@lem1982715 term147 (real_of_int x)). Qed.
Lemma lem2328058 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328059 : term111 = term185.
Proof. exact (@lem2328058 term112). Qed.
Lemma lem2328061 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328062 : term147 = term148.
Proof. exact (@lem2328061 term112). Qed.
Lemma lem2328063 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328064 : term308 = term309.
Proof. exact (MK_COMB (@lem2328063) (@lem2328062)). Qed.
Lemma lem2328065 : term310 = term311.
Proof. exact (MK_COMB (@lem2328064) (@lem2328059)). Qed.
Lemma lem2328066 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2328068 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328069 : term275 = term281.
Proof. exact (@lem2328068 (NUMERAL 0) term112). Qed.
Lemma lem2328070 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328071 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328072 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328071 h1) (fun h1 : term281 = True => @lem2328070)). Qed.
Lemma lem2328073 : term281 = True.
Proof. exact (EQ_MP (@lem2328072) (@lem2328070)). Qed.
Lemma lem2328074 : term275 = True.
Proof. exact (TRANS (@lem2328069) (@lem2328073)). Qed.
Lemma lem2328075 : True = term275.
Proof. exact (SYM (@lem2328074)). Qed.
Lemma lem2328076 : term275.
Proof. exact (EQ_MP (@lem2328075) (@lem0)). Qed.
Lemma lem2328077 : term313.
Proof. exact (@lem2328066 (@lem2328076)). Qed.
Lemma lem2328079 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328080 : term275 = term281.
Proof. exact (@lem2328079 (NUMERAL 0) term112). Qed.
Lemma lem2328081 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328082 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328083 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328082 h1) (fun h1 : term281 = True => @lem2328081)). Qed.
Lemma lem2328084 : term281 = True.
Proof. exact (EQ_MP (@lem2328083) (@lem2328081)). Qed.
Lemma lem2328085 : term275 = True.
Proof. exact (TRANS (@lem2328080) (@lem2328084)). Qed.
Lemma lem2328086 : True = term275.
Proof. exact (SYM (@lem2328085)). Qed.
Lemma lem2328087 : term275.
Proof. exact (EQ_MP (@lem2328086) (@lem0)). Qed.
Lemma lem2328088 : term314.
Proof. exact (@lem2328077 (@lem2328087)). Qed.
Lemma lem2328090 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328091 : term275 = term281.
Proof. exact (@lem2328090 (NUMERAL 0) term112). Qed.
Lemma lem2328092 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328093 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328094 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328093 h1) (fun h1 : term281 = True => @lem2328092)). Qed.
Lemma lem2328095 : term281 = True.
Proof. exact (EQ_MP (@lem2328094) (@lem2328092)). Qed.
Lemma lem2328096 : term275 = True.
Proof. exact (TRANS (@lem2328091) (@lem2328095)). Qed.
Lemma lem2328097 : True = term275.
Proof. exact (SYM (@lem2328096)). Qed.
Lemma lem2328098 : term275.
Proof. exact (EQ_MP (@lem2328097) (@lem0)). Qed.
Lemma lem2328099 : term315.
Proof. exact (@lem2328088 (@lem2328098)). Qed.
Lemma lem2328101 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328102 : term156 = term157.
Proof. exact (@lem2328101 term112 term112). Qed.
Lemma lem2328103 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328104 : term159 = term112.
Proof. exact (EQ_MP (@lem2328103) (@lem940073)). Qed.
Lemma lem2328105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328106 : term157 = term111.
Proof. exact (MK_COMB (@lem2328105) (@lem2328104)). Qed.
Lemma lem2328107 : term156 = term111.
Proof. exact (TRANS (@lem2328102) (@lem2328106)). Qed.
Lemma lem2328109 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328110 : term199 = term204.
Proof. exact (@lem2328109 term112 term112). Qed.
Lemma lem2328111 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328112 : term159 = term112.
Proof. exact (EQ_MP (@lem2328111) (@lem940073)). Qed.
Lemma lem2328113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328114 : term157 = term111.
Proof. exact (MK_COMB (@lem2328113) (@lem2328112)). Qed.
Lemma lem2328115 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328116 : term204 = term147.
Proof. exact (MK_COMB (@lem2328115) (@lem2328114)). Qed.
Lemma lem2328117 : term199 = term147.
Proof. exact (TRANS (@lem2328110) (@lem2328116)). Qed.
Lemma lem2328118 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328119 : term316 = term308.
Proof. exact (MK_COMB (@lem2328118) (@lem2328117)). Qed.
Lemma lem2328120 : term317 = term310.
Proof. exact (MK_COMB (@lem2328119) (@lem2328107)). Qed.
Lemma lem2328122 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2328123 : term310 = term86.
Proof. exact (@lem2328122 term112). Qed.
Lemma lem2328124 : term317 = term86.
Proof. exact (TRANS (@lem2328120) (@lem2328123)). Qed.
Lemma lem2328125 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328126 : term319 = term320.
Proof. exact (MK_COMB (@lem2328125) (@lem2328124)). Qed.
Lemma lem2328127 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2328128 : term321 = term286.
Proof. exact (MK_COMB (@lem2328126) (@lem2328127)). Qed.
Lemma lem2328130 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328131 : term286 = term86.
Proof. exact (@lem2328130 term112). Qed.
Lemma lem2328132 : term321 = term86.
Proof. exact (TRANS (@lem2328128) (@lem2328131)). Qed.
Lemma lem2328134 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328135 : term156 = term157.
Proof. exact (@lem2328134 term112 term112). Qed.
Lemma lem2328136 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328137 : term159 = term112.
Proof. exact (EQ_MP (@lem2328136) (@lem940073)). Qed.
Lemma lem2328138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328139 : term157 = term111.
Proof. exact (MK_COMB (@lem2328138) (@lem2328137)). Qed.
Lemma lem2328140 : term156 = term111.
Proof. exact (TRANS (@lem2328135) (@lem2328139)). Qed.
Lemma lem2328141 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2328142 : term322 = term286.
Proof. exact (MK_COMB (@lem2328141) (@lem2328140)). Qed.
Lemma lem2328144 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328145 : term286 = term86.
Proof. exact (@lem2328144 term112). Qed.
Lemma lem2328146 : term322 = term86.
Proof. exact (TRANS (@lem2328142) (@lem2328145)). Qed.
Lemma lem2328147 : term86 = term322.
Proof. exact (SYM (@lem2328146)). Qed.
Lemma lem2328148 : term321 = term322.
Proof. exact (TRANS (@lem2328132) (@lem2328147)). Qed.
Lemma lem2328149 : term311 = term145.
Proof. exact (@lem2328099 (@lem2328148)). Qed.
Lemma lem2328150 : term310 = term145.
Proof. exact (TRANS (@lem2328065) (@lem2328149)). Qed.
Lemma lem2328152 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2328153 : term145 = term86.
Proof. exact (@lem2328152 term86). Qed.
Lemma lem2328154 : term310 = term86.
Proof. exact (TRANS (@lem2328150) (@lem2328153)). Qed.
Lemma lem2328155 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328156 : term323 = term320.
Proof. exact (MK_COMB (@lem2328155) (@lem2328154)). Qed.
Lemma lem2328157 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2328158 (x : int) : (term307 x) = (term324 x).
Proof. exact (MK_COMB (@lem2328156) (@lem2328157 x)). Qed.
Lemma lem2328159 (x : int) : (term306 x) = (term324 x).
Proof. exact (TRANS (@lem2328056 x) (@lem2328158 x)). Qed.
Lemma lem2328160 (x : int) : (term324 x) = term86.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2328161 (x : int) : (term306 x) = term86.
Proof. exact (TRANS (@lem2328159 x) (@lem2328160 x)). Qed.
Lemma lem2328162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328163 (x : int) : (term325 x) = term326.
Proof. exact (MK_COMB (@lem2328162) (@lem2328161 x)). Qed.
Lemma lem2328164 (n : nat) : (term327 n) = (term328 n).
Proof. exact (@lem1982763 (term173 n) (real_of_num n) term147). Qed.
Lemma lem2328165 (n : nat) : (term329 n) = (term330 n).
Proof. exact (@lem1982713 term147 (real_of_num n)). Qed.
Lemma lem2328167 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328168 : term111 = term185.
Proof. exact (@lem2328167 term112). Qed.
Lemma lem2328170 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328171 : term147 = term148.
Proof. exact (@lem2328170 term112). Qed.
Lemma lem2328172 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328173 : term308 = term309.
Proof. exact (MK_COMB (@lem2328172) (@lem2328171)). Qed.
Lemma lem2328174 : term310 = term311.
Proof. exact (MK_COMB (@lem2328173) (@lem2328168)). Qed.
Lemma lem2328175 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2328177 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328178 : term275 = term281.
Proof. exact (@lem2328177 (NUMERAL 0) term112). Qed.
Lemma lem2328179 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328180 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328181 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328180 h1) (fun h1 : term281 = True => @lem2328179)). Qed.
Lemma lem2328182 : term281 = True.
Proof. exact (EQ_MP (@lem2328181) (@lem2328179)). Qed.
Lemma lem2328183 : term275 = True.
Proof. exact (TRANS (@lem2328178) (@lem2328182)). Qed.
Lemma lem2328184 : True = term275.
Proof. exact (SYM (@lem2328183)). Qed.
Lemma lem2328185 : term275.
Proof. exact (EQ_MP (@lem2328184) (@lem0)). Qed.
Lemma lem2328186 : term313.
Proof. exact (@lem2328175 (@lem2328185)). Qed.
Lemma lem2328188 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328189 : term275 = term281.
Proof. exact (@lem2328188 (NUMERAL 0) term112). Qed.
Lemma lem2328190 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328191 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328192 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328191 h1) (fun h1 : term281 = True => @lem2328190)). Qed.
Lemma lem2328193 : term281 = True.
Proof. exact (EQ_MP (@lem2328192) (@lem2328190)). Qed.
Lemma lem2328194 : term275 = True.
Proof. exact (TRANS (@lem2328189) (@lem2328193)). Qed.
Lemma lem2328195 : True = term275.
Proof. exact (SYM (@lem2328194)). Qed.
Lemma lem2328196 : term275.
Proof. exact (EQ_MP (@lem2328195) (@lem0)). Qed.
Lemma lem2328197 : term314.
Proof. exact (@lem2328186 (@lem2328196)). Qed.
Lemma lem2328199 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328200 : term275 = term281.
Proof. exact (@lem2328199 (NUMERAL 0) term112). Qed.
Lemma lem2328201 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328202 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328203 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328202 h1) (fun h1 : term281 = True => @lem2328201)). Qed.
Lemma lem2328204 : term281 = True.
Proof. exact (EQ_MP (@lem2328203) (@lem2328201)). Qed.
Lemma lem2328205 : term275 = True.
Proof. exact (TRANS (@lem2328200) (@lem2328204)). Qed.
Lemma lem2328206 : True = term275.
Proof. exact (SYM (@lem2328205)). Qed.
Lemma lem2328207 : term275.
Proof. exact (EQ_MP (@lem2328206) (@lem0)). Qed.
Lemma lem2328208 : term315.
Proof. exact (@lem2328197 (@lem2328207)). Qed.
Lemma lem2328210 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328211 : term156 = term157.
Proof. exact (@lem2328210 term112 term112). Qed.
Lemma lem2328212 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328213 : term159 = term112.
Proof. exact (EQ_MP (@lem2328212) (@lem940073)). Qed.
Lemma lem2328214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328215 : term157 = term111.
Proof. exact (MK_COMB (@lem2328214) (@lem2328213)). Qed.
Lemma lem2328216 : term156 = term111.
Proof. exact (TRANS (@lem2328211) (@lem2328215)). Qed.
Lemma lem2328218 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328219 : term199 = term204.
Proof. exact (@lem2328218 term112 term112). Qed.
Lemma lem2328220 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328221 : term159 = term112.
Proof. exact (EQ_MP (@lem2328220) (@lem940073)). Qed.
Lemma lem2328222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328223 : term157 = term111.
Proof. exact (MK_COMB (@lem2328222) (@lem2328221)). Qed.
Lemma lem2328224 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328225 : term204 = term147.
Proof. exact (MK_COMB (@lem2328224) (@lem2328223)). Qed.
Lemma lem2328226 : term199 = term147.
Proof. exact (TRANS (@lem2328219) (@lem2328225)). Qed.
Lemma lem2328227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328228 : term316 = term308.
Proof. exact (MK_COMB (@lem2328227) (@lem2328226)). Qed.
Lemma lem2328229 : term317 = term310.
Proof. exact (MK_COMB (@lem2328228) (@lem2328216)). Qed.
Lemma lem2328231 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2328232 : term310 = term86.
Proof. exact (@lem2328231 term112). Qed.
Lemma lem2328233 : term317 = term86.
Proof. exact (TRANS (@lem2328229) (@lem2328232)). Qed.
Lemma lem2328234 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328235 : term319 = term320.
Proof. exact (MK_COMB (@lem2328234) (@lem2328233)). Qed.
Lemma lem2328236 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2328237 : term321 = term286.
Proof. exact (MK_COMB (@lem2328235) (@lem2328236)). Qed.
Lemma lem2328239 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328240 : term286 = term86.
Proof. exact (@lem2328239 term112). Qed.
Lemma lem2328241 : term321 = term86.
Proof. exact (TRANS (@lem2328237) (@lem2328240)). Qed.
Lemma lem2328243 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328244 : term156 = term157.
Proof. exact (@lem2328243 term112 term112). Qed.
Lemma lem2328245 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328246 : term159 = term112.
Proof. exact (EQ_MP (@lem2328245) (@lem940073)). Qed.
Lemma lem2328247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328248 : term157 = term111.
Proof. exact (MK_COMB (@lem2328247) (@lem2328246)). Qed.
Lemma lem2328249 : term156 = term111.
Proof. exact (TRANS (@lem2328244) (@lem2328248)). Qed.
Lemma lem2328250 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2328251 : term322 = term286.
Proof. exact (MK_COMB (@lem2328250) (@lem2328249)). Qed.
Lemma lem2328253 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328254 : term286 = term86.
Proof. exact (@lem2328253 term112). Qed.
Lemma lem2328255 : term322 = term86.
Proof. exact (TRANS (@lem2328251) (@lem2328254)). Qed.
Lemma lem2328256 : term86 = term322.
Proof. exact (SYM (@lem2328255)). Qed.
Lemma lem2328257 : term321 = term322.
Proof. exact (TRANS (@lem2328241) (@lem2328256)). Qed.
Lemma lem2328258 : term311 = term145.
Proof. exact (@lem2328208 (@lem2328257)). Qed.
Lemma lem2328259 : term310 = term145.
Proof. exact (TRANS (@lem2328174) (@lem2328258)). Qed.
Lemma lem2328261 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2328262 : term145 = term86.
Proof. exact (@lem2328261 term86). Qed.
Lemma lem2328263 : term310 = term86.
Proof. exact (TRANS (@lem2328259) (@lem2328262)). Qed.
Lemma lem2328264 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328265 : term323 = term320.
Proof. exact (MK_COMB (@lem2328264) (@lem2328263)). Qed.
Lemma lem2328266 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2328267 (n : nat) : (term330 n) = (term285 n).
Proof. exact (MK_COMB (@lem2328265) (@lem2328266 n)). Qed.
Lemma lem2328268 (n : nat) : (term329 n) = (term285 n).
Proof. exact (TRANS (@lem2328165 n) (@lem2328267 n)). Qed.
Lemma lem2328269 (n : nat) : (term285 n) = term86.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2328270 (n : nat) : (term329 n) = term86.
Proof. exact (TRANS (@lem2328268 n) (@lem2328269 n)). Qed.
Lemma lem2328271 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328272 (n : nat) : (term331 n) = term326.
Proof. exact (MK_COMB (@lem2328271) (@lem2328270 n)). Qed.
Lemma lem2328273 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem2328274 (n : nat) : (term328 n) = term332.
Proof. exact (MK_COMB (@lem2328272 n) (@lem2328273)). Qed.
Lemma lem2328275 (n : nat) : (term327 n) = term332.
Proof. exact (TRANS (@lem2328164 n) (@lem2328274 n)). Qed.
Lemma lem2328276 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2328277 (n : nat) : (term327 n) = term147.
Proof. exact (TRANS (@lem2328275 n) (@lem2328276)). Qed.
Lemma lem2328278 (x : int) (n : nat) : (term304 x n) = term332.
Proof. exact (MK_COMB (@lem2328163 x) (@lem2328277 n)). Qed.
Lemma lem2328279 (x : int) (n : nat) : (term303 x n) = term332.
Proof. exact (TRANS (@lem2328055 x n) (@lem2328278 x n)). Qed.
Lemma lem2328280 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2328281 (x : int) (n : nat) : (term303 x n) = term147.
Proof. exact (TRANS (@lem2328279 x n) (@lem2328280)). Qed.
Lemma lem2328282 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2328283 (x : int) (n : nat) : (term333 x n) = term334.
Proof. exact (MK_COMB (@lem2328282) (@lem2328281 x n)). Qed.
Lemma lem2328284 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328285 (x : int) (n : nat) : (term302 x n) = term335.
Proof. exact (MK_COMB (@lem2328283 x n) (@lem2328284)). Qed.
Lemma lem2328286 (x : int) (n : nat) (h1 : term273 x n) : term335.
Proof. exact (EQ_MP (@lem2328285 x n) (@lem2328054 x n h1)). Qed.
Lemma lem2328288 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2328289 : term335 = term336.
Proof. exact (@lem2328288 term86 term147). Qed.
Lemma lem2328291 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328292 : term147 = term148.
Proof. exact (@lem2328291 term112). Qed.
Lemma lem2328294 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328295 : term86 = term145.
Proof. exact (@lem2328294 (NUMERAL 0)). Qed.
Lemma lem2328296 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2328297 : term88 = term337.
Proof. exact (MK_COMB (@lem2328296) (@lem2328295)). Qed.
Lemma lem2328298 : term336 = term338.
Proof. exact (MK_COMB (@lem2328297) (@lem2328292)). Qed.
Lemma lem2328299 : term339.
Proof. exact (@lem1980026 term86 term111 term147 term111). Qed.
Lemma lem2328301 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328302 : term275 = term281.
Proof. exact (@lem2328301 (NUMERAL 0) term112). Qed.
Lemma lem2328303 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328304 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328305 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328304 h1) (fun h1 : term281 = True => @lem2328303)). Qed.
Lemma lem2328306 : term281 = True.
Proof. exact (EQ_MP (@lem2328305) (@lem2328303)). Qed.
Lemma lem2328307 : term275 = True.
Proof. exact (TRANS (@lem2328302) (@lem2328306)). Qed.
Lemma lem2328308 : True = term275.
Proof. exact (SYM (@lem2328307)). Qed.
Lemma lem2328309 : term275.
Proof. exact (EQ_MP (@lem2328308) (@lem0)). Qed.
Lemma lem2328310 : term340.
Proof. exact (@lem2328299 (@lem2328309)). Qed.
Lemma lem2328312 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328313 : term275 = term281.
Proof. exact (@lem2328312 (NUMERAL 0) term112). Qed.
Lemma lem2328314 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328315 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328316 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328315 h1) (fun h1 : term281 = True => @lem2328314)). Qed.
Lemma lem2328317 : term281 = True.
Proof. exact (EQ_MP (@lem2328316) (@lem2328314)). Qed.
Lemma lem2328318 : term275 = True.
Proof. exact (TRANS (@lem2328313) (@lem2328317)). Qed.
Lemma lem2328319 : True = term275.
Proof. exact (SYM (@lem2328318)). Qed.
Lemma lem2328320 : term275.
Proof. exact (EQ_MP (@lem2328319) (@lem0)). Qed.
Lemma lem2328321 : term338 = term341.
Proof. exact (@lem2328310 (@lem2328320)). Qed.
Lemma lem2328323 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328324 : term199 = term204.
Proof. exact (@lem2328323 term112 term112). Qed.
Lemma lem2328325 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328326 : term159 = term112.
Proof. exact (EQ_MP (@lem2328325) (@lem940073)). Qed.
Lemma lem2328327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328328 : term157 = term111.
Proof. exact (MK_COMB (@lem2328327) (@lem2328326)). Qed.
Lemma lem2328329 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328330 : term204 = term147.
Proof. exact (MK_COMB (@lem2328329) (@lem2328328)). Qed.
Lemma lem2328331 : term199 = term147.
Proof. exact (TRANS (@lem2328324) (@lem2328330)). Qed.
Lemma lem2328333 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328334 : term286 = term86.
Proof. exact (@lem2328333 term112). Qed.
Lemma lem2328335 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2328336 : term342 = term88.
Proof. exact (MK_COMB (@lem2328335) (@lem2328334)). Qed.
Lemma lem2328337 : term341 = term336.
Proof. exact (MK_COMB (@lem2328336) (@lem2328331)). Qed.
Lemma lem2328339 (m : nat) (n : nat) : (term343 m n) = (term344 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2328340 : term336 = term345.
Proof. exact (@lem2328339 (NUMERAL 0) term112). Qed.
Lemma lem2328341 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328342 (h1 : term282 = (BIT1 0)) : (term112 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2328343 : (term282 = (BIT1 0)) = ((term112 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328342 h1) (fun h1 : (term112 = (NUMERAL 0)) = False => @lem2328341)). Qed.
Lemma lem2328344 : (term112 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2328343) (@lem2328341)). Qed.
Lemma lem2328345 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2328346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2328347 : term346 = (and True).
Proof. exact (MK_COMB (@lem2328346) (@lem2328345)). Qed.
Lemma lem2328348 : term345 = (True /\ False).
Proof. exact (MK_COMB (@lem2328347) (@lem2328344)). Qed.
Lemma lem2328350 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2328351 : term345 = False.
Proof. exact (TRANS (@lem2328348) (@lem2328350)). Qed.
Lemma lem2328352 : term336 = False.
Proof. exact (TRANS (@lem2328340) (@lem2328351)). Qed.
Lemma lem2328353 : term341 = False.
Proof. exact (TRANS (@lem2328337) (@lem2328352)). Qed.
Lemma lem2328354 : term338 = False.
Proof. exact (TRANS (@lem2328321) (@lem2328353)). Qed.
Lemma lem2328355 : term336 = False.
Proof. exact (TRANS (@lem2328298) (@lem2328354)). Qed.
Lemma lem2328356 : term335 = False.
Proof. exact (TRANS (@lem2328289) (@lem2328355)). Qed.
Lemma lem2328357 (x : int) (n : nat) (h1 : term273 x n) : False.
Proof. exact (EQ_MP (@lem2328356) (@lem2328286 x n h1)). Qed.
Lemma lem2328358 (x : int) (n : nat) (h1 : term347 x n) : term347 x n.
Proof. exact (h1). Qed.
Lemma lem2328359 (x : int) (n : nat) (h1 : term347 x n) : term267 x n.
Proof. exact (proj2 (@lem2328358 x n h1)). Qed.
Lemma lem2328360 (x : int) (n : nat) (h1 : term347 x n) : term167 x.
Proof. exact (proj1 (@lem2328358 x n h1)). Qed.
Lemma lem2328361 (x : int) (n : nat) (h1 : term347 x n) : term214 x n.
Proof. exact (proj2 (@lem2328359 x n h1)). Qed.
Lemma lem2328362 (x : int) (n : nat) (h1 : term347 x n) : (term189 x n) = term86.
Proof. exact (proj1 (@lem2328359 x n h1)). Qed.
Lemma lem2328365 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2328366 : term348 = term349.
Proof. exact (@lem2328365 term86 term350). Qed.
Lemma lem2328368 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328369 : term350 = term351.
Proof. exact (@lem2328368 term352). Qed.
Lemma lem2328371 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328372 : term86 = term145.
Proof. exact (@lem2328371 (NUMERAL 0)). Qed.
Lemma lem2328373 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328374 : term276 = term277.
Proof. exact (MK_COMB (@lem2328373) (@lem2328372)). Qed.
Lemma lem2328375 : term349 = term353.
Proof. exact (MK_COMB (@lem2328374) (@lem2328369)). Qed.
Lemma lem2328376 : term354.
Proof. exact (@lem1980255 term86 term111 term350 term111). Qed.
Lemma lem2328378 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328379 : term275 = term281.
Proof. exact (@lem2328378 (NUMERAL 0) term112). Qed.
Lemma lem2328380 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328381 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328382 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328381 h1) (fun h1 : term281 = True => @lem2328380)). Qed.
Lemma lem2328383 : term281 = True.
Proof. exact (EQ_MP (@lem2328382) (@lem2328380)). Qed.
Lemma lem2328384 : term275 = True.
Proof. exact (TRANS (@lem2328379) (@lem2328383)). Qed.
Lemma lem2328385 : True = term275.
Proof. exact (SYM (@lem2328384)). Qed.
Lemma lem2328386 : term275.
Proof. exact (EQ_MP (@lem2328385) (@lem0)). Qed.
Lemma lem2328387 : term355.
Proof. exact (@lem2328376 (@lem2328386)). Qed.
Lemma lem2328389 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328390 : term275 = term281.
Proof. exact (@lem2328389 (NUMERAL 0) term112). Qed.
Lemma lem2328391 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328392 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328393 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328392 h1) (fun h1 : term281 = True => @lem2328391)). Qed.
Lemma lem2328394 : term281 = True.
Proof. exact (EQ_MP (@lem2328393) (@lem2328391)). Qed.
Lemma lem2328395 : term275 = True.
Proof. exact (TRANS (@lem2328390) (@lem2328394)). Qed.
Lemma lem2328396 : True = term275.
Proof. exact (SYM (@lem2328395)). Qed.
Lemma lem2328397 : term275.
Proof. exact (EQ_MP (@lem2328396) (@lem0)). Qed.
Lemma lem2328398 : term353 = term356.
Proof. exact (@lem2328387 (@lem2328397)). Qed.
Lemma lem2328400 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328401 : term357 = term358.
Proof. exact (@lem2328400 term352 term112). Qed.
Lemma lem2328402 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2328403 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2328404 : term361 = term352.
Proof. exact (EQ_MP (@lem2328403) (@lem2328402)). Qed.
Lemma lem2328405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328406 : term358 = term350.
Proof. exact (MK_COMB (@lem2328405) (@lem2328404)). Qed.
Lemma lem2328407 : term357 = term350.
Proof. exact (TRANS (@lem2328401) (@lem2328406)). Qed.
Lemma lem2328409 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328410 : term286 = term86.
Proof. exact (@lem2328409 term112). Qed.
Lemma lem2328411 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328412 : term287 = term276.
Proof. exact (MK_COMB (@lem2328411) (@lem2328410)). Qed.
Lemma lem2328413 : term356 = term349.
Proof. exact (MK_COMB (@lem2328412) (@lem2328407)). Qed.
Lemma lem2328415 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328416 : term349 = term362.
Proof. exact (@lem2328415 (NUMERAL 0) term352). Qed.
Lemma lem2328417 : term363 = term360.
Proof. exact (@lem912803). Qed.
Lemma lem2328418 (h1 : term363 = term360) : term362 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term360 h1). Qed.
Lemma lem2328419 : (term363 = term360) = (term362 = True).
Proof. exact (prop_ext (fun h1 : term363 = term360 => @lem2328418 h1) (fun h1 : term362 = True => @lem2328417)). Qed.
Lemma lem2328420 : term362 = True.
Proof. exact (EQ_MP (@lem2328419) (@lem2328417)). Qed.
Lemma lem2328421 : term349 = True.
Proof. exact (TRANS (@lem2328416) (@lem2328420)). Qed.
Lemma lem2328422 : term356 = True.
Proof. exact (TRANS (@lem2328413) (@lem2328421)). Qed.
Lemma lem2328423 : term353 = True.
Proof. exact (TRANS (@lem2328398) (@lem2328422)). Qed.
Lemma lem2328424 : term349 = True.
Proof. exact (TRANS (@lem2328375) (@lem2328423)). Qed.
Lemma lem2328425 : term348 = True.
Proof. exact (TRANS (@lem2328366) (@lem2328424)). Qed.
Lemma lem2328426 : True = term348.
Proof. exact (SYM (@lem2328425)). Qed.
Lemma lem2328427 : term348.
Proof. exact (EQ_MP (@lem2328426) (@lem0)). Qed.
Lemma lem2328428 (x : int) (n : nat) (h1 : term347 x n) : term364 x.
Proof. exact (conj (@lem2328427) (@lem2328360 x n h1)). Qed.
Lemma lem2328430 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2328431 (x : int) : term365 x.
Proof. exact (@lem2328430 term350 (real_of_int x)). Qed.
Lemma lem2328438 (x : int) (n : nat) (h1 : term347 x n) : term366 x.
Proof. exact (@lem2328431 x (@lem2328428 x n h1)). Qed.
Lemma lem2328440 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2328441 : term274 = term275.
Proof. exact (@lem2328440 term86 term111). Qed.
Lemma lem2328443 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328444 : term111 = term185.
Proof. exact (@lem2328443 term112). Qed.
Lemma lem2328446 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328447 : term86 = term145.
Proof. exact (@lem2328446 (NUMERAL 0)). Qed.
Lemma lem2328448 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328449 : term276 = term277.
Proof. exact (MK_COMB (@lem2328448) (@lem2328447)). Qed.
Lemma lem2328450 : term275 = term278.
Proof. exact (MK_COMB (@lem2328449) (@lem2328444)). Qed.
Lemma lem2328451 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2328453 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328454 : term275 = term281.
Proof. exact (@lem2328453 (NUMERAL 0) term112). Qed.
Lemma lem2328455 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328456 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328457 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328456 h1) (fun h1 : term281 = True => @lem2328455)). Qed.
Lemma lem2328458 : term281 = True.
Proof. exact (EQ_MP (@lem2328457) (@lem2328455)). Qed.
Lemma lem2328459 : term275 = True.
Proof. exact (TRANS (@lem2328454) (@lem2328458)). Qed.
Lemma lem2328460 : True = term275.
Proof. exact (SYM (@lem2328459)). Qed.
Lemma lem2328461 : term275.
Proof. exact (EQ_MP (@lem2328460) (@lem0)). Qed.
Lemma lem2328462 : term283.
Proof. exact (@lem2328451 (@lem2328461)). Qed.
Lemma lem2328464 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328465 : term275 = term281.
Proof. exact (@lem2328464 (NUMERAL 0) term112). Qed.
Lemma lem2328466 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328467 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328468 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328467 h1) (fun h1 : term281 = True => @lem2328466)). Qed.
Lemma lem2328469 : term281 = True.
Proof. exact (EQ_MP (@lem2328468) (@lem2328466)). Qed.
Lemma lem2328470 : term275 = True.
Proof. exact (TRANS (@lem2328465) (@lem2328469)). Qed.
Lemma lem2328471 : True = term275.
Proof. exact (SYM (@lem2328470)). Qed.
Lemma lem2328472 : term275.
Proof. exact (EQ_MP (@lem2328471) (@lem0)). Qed.
Lemma lem2328473 : term278 = term284.
Proof. exact (@lem2328462 (@lem2328472)). Qed.
Lemma lem2328475 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328476 : term156 = term157.
Proof. exact (@lem2328475 term112 term112). Qed.
Lemma lem2328477 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328478 : term159 = term112.
Proof. exact (EQ_MP (@lem2328477) (@lem940073)). Qed.
Lemma lem2328479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328480 : term157 = term111.
Proof. exact (MK_COMB (@lem2328479) (@lem2328478)). Qed.
Lemma lem2328481 : term156 = term111.
Proof. exact (TRANS (@lem2328476) (@lem2328480)). Qed.
Lemma lem2328483 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328484 : term286 = term86.
Proof. exact (@lem2328483 term112). Qed.
Lemma lem2328485 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328486 : term287 = term276.
Proof. exact (MK_COMB (@lem2328485) (@lem2328484)). Qed.
Lemma lem2328487 : term284 = term275.
Proof. exact (MK_COMB (@lem2328486) (@lem2328481)). Qed.
Lemma lem2328489 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328490 : term275 = term281.
Proof. exact (@lem2328489 (NUMERAL 0) term112). Qed.
Lemma lem2328491 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328492 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328493 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328492 h1) (fun h1 : term281 = True => @lem2328491)). Qed.
Lemma lem2328494 : term281 = True.
Proof. exact (EQ_MP (@lem2328493) (@lem2328491)). Qed.
Lemma lem2328495 : term275 = True.
Proof. exact (TRANS (@lem2328490) (@lem2328494)). Qed.
Lemma lem2328496 : term284 = True.
Proof. exact (TRANS (@lem2328487) (@lem2328495)). Qed.
Lemma lem2328497 : term278 = True.
Proof. exact (TRANS (@lem2328473) (@lem2328496)). Qed.
Lemma lem2328498 : term275 = True.
Proof. exact (TRANS (@lem2328450) (@lem2328497)). Qed.
Lemma lem2328499 : term274 = True.
Proof. exact (TRANS (@lem2328441) (@lem2328498)). Qed.
Lemma lem2328500 : True = term274.
Proof. exact (SYM (@lem2328499)). Qed.
Lemma lem2328501 : term274.
Proof. exact (EQ_MP (@lem2328500) (@lem0)). Qed.
Lemma lem2328502 (x : int) (n : nat) (h1 : term347 x n) : term288 x n.
Proof. exact (conj (@lem2328501) (@lem2328361 x n h1)). Qed.
Lemma lem2328504 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2328505 (x : int) (n : nat) : term290 x n.
Proof. exact (@lem2328504 term111 (term210 x n)). Qed.
Lemma lem2328506 (x : int) (n : nat) (h1 : term347 x n) : term291 x n.
Proof. exact (@lem2328505 x n (@lem2328502 x n h1)). Qed.
Lemma lem2328507 (x : int) (n : nat) : (term292 x n) = (term210 x n).
Proof. exact (@lem1982733 (term210 x n)). Qed.
Lemma lem2328508 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2328509 (x : int) (n : nat) : (term293 x n) = (term213 x n).
Proof. exact (MK_COMB (@lem2328508) (@lem2328507 x n)). Qed.
Lemma lem2328510 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328511 (x : int) (n : nat) : (term291 x n) = (term214 x n).
Proof. exact (MK_COMB (@lem2328509 x n) (@lem2328510)). Qed.
Lemma lem2328512 (x : int) (n : nat) (h1 : term347 x n) : term214 x n.
Proof. exact (EQ_MP (@lem2328511 x n) (@lem2328506 x n h1)). Qed.
Lemma lem2328514 (y : real) : term294 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2328515 (x : int) (n : nat) : term367 x n.
Proof. exact (@lem2328514 (term189 x n)). Qed.
Lemma lem2328516 (x : int) (n : nat) (h1 : term347 x n) : term368 x n.
Proof. exact (@lem2328515 x n (@lem2328362 x n h1)). Qed.
Lemma lem2328517 (x : int) (n : nat) (h1 : term347 x n) : term369 x n.
Proof. exact (@lem2328516 x n h1 term147). Qed.
Lemma lem2328518 (x : int) (n : nat) : (term369 x n) = ((term370 x n) = term86).
Proof. exact (eq_refl (term369 x n)). Qed.
Lemma lem2328519 (x : int) (n : nat) (h1 : term347 x n) : (term370 x n) = term86.
Proof. exact (EQ_MP (@lem2328518 x n) (@lem2328517 x n h1)). Qed.
Lemma lem2328526 (x : int) (n : nat) : (term370 x n) = (term371 x n).
Proof. exact (@lem1982781 (real_of_int x) term147 (real_of_num n)). Qed.
Lemma lem2328527 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2328528 (x : int) (n : nat) : (term372 x n) = (term373 x n).
Proof. exact (MK_COMB (@lem2328527) (@lem2328526 x n)). Qed.
Lemma lem2328529 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328530 (x : int) (n : nat) : ((term370 x n) = term86) = ((term371 x n) = term86).
Proof. exact (MK_COMB (@lem2328528 x n) (@lem2328529)). Qed.
Lemma lem2328531 (x : int) (n : nat) (h1 : term347 x n) : (term371 x n) = term86.
Proof. exact (EQ_MP (@lem2328530 x n) (@lem2328519 x n h1)). Qed.
Lemma lem2328532 (x : int) (n : nat) (h1 : term347 x n) : term374 x n.
Proof. exact (conj (@lem2328531 x n h1) (@lem2328512 x n h1)). Qed.
Lemma lem2328534 (x : real) (y : real) : term300 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2328535 (x : int) (n : nat) : term375 x n.
Proof. exact (@lem2328534 (term371 x n) (term210 x n)). Qed.
Lemma lem2328536 (x : int) (n : nat) (h1 : term347 x n) : term376 x n.
Proof. exact (@lem2328535 x n (@lem2328532 x n h1)). Qed.
Lemma lem2328537 (x : int) (n : nat) : (term377 x n) = (term378 x n).
Proof. exact (@lem1982753 (term211 x) (term211 x) (term173 n) (term305 n)). Qed.
Lemma lem2328538 (x : int) : (term379 x) = (term380 x).
Proof. exact (@lem1982711 term147 term147 (real_of_int x)). Qed.
Lemma lem2328540 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328541 : term147 = term148.
Proof. exact (@lem2328540 term112). Qed.
Lemma lem2328543 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328544 : term147 = term148.
Proof. exact (@lem2328543 term112). Qed.
Lemma lem2328545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328546 : term308 = term309.
Proof. exact (MK_COMB (@lem2328545) (@lem2328544)). Qed.
Lemma lem2328547 : term381 = term382.
Proof. exact (MK_COMB (@lem2328546) (@lem2328541)). Qed.
Lemma lem2328548 : term383.
Proof. exact (@lem1981473 term147 term111 term147 term111 term384 term111). Qed.
Lemma lem2328550 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328551 : term275 = term281.
Proof. exact (@lem2328550 (NUMERAL 0) term112). Qed.
Lemma lem2328552 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328553 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328554 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328553 h1) (fun h1 : term281 = True => @lem2328552)). Qed.
Lemma lem2328555 : term281 = True.
Proof. exact (EQ_MP (@lem2328554) (@lem2328552)). Qed.
Lemma lem2328556 : term275 = True.
Proof. exact (TRANS (@lem2328551) (@lem2328555)). Qed.
Lemma lem2328557 : True = term275.
Proof. exact (SYM (@lem2328556)). Qed.
Lemma lem2328558 : term275.
Proof. exact (EQ_MP (@lem2328557) (@lem0)). Qed.
Lemma lem2328559 : term385.
Proof. exact (@lem2328548 (@lem2328558)). Qed.
Lemma lem2328561 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328562 : term275 = term281.
Proof. exact (@lem2328561 (NUMERAL 0) term112). Qed.
Lemma lem2328563 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328564 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328565 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328564 h1) (fun h1 : term281 = True => @lem2328563)). Qed.
Lemma lem2328566 : term281 = True.
Proof. exact (EQ_MP (@lem2328565) (@lem2328563)). Qed.
Lemma lem2328567 : term275 = True.
Proof. exact (TRANS (@lem2328562) (@lem2328566)). Qed.
Lemma lem2328568 : True = term275.
Proof. exact (SYM (@lem2328567)). Qed.
Lemma lem2328569 : term275.
Proof. exact (EQ_MP (@lem2328568) (@lem0)). Qed.
Lemma lem2328570 : term386.
Proof. exact (@lem2328559 (@lem2328569)). Qed.
Lemma lem2328572 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328573 : term275 = term281.
Proof. exact (@lem2328572 (NUMERAL 0) term112). Qed.
Lemma lem2328574 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328575 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328576 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328575 h1) (fun h1 : term281 = True => @lem2328574)). Qed.
Lemma lem2328577 : term281 = True.
Proof. exact (EQ_MP (@lem2328576) (@lem2328574)). Qed.
Lemma lem2328578 : term275 = True.
Proof. exact (TRANS (@lem2328573) (@lem2328577)). Qed.
Lemma lem2328579 : True = term275.
Proof. exact (SYM (@lem2328578)). Qed.
Lemma lem2328580 : term275.
Proof. exact (EQ_MP (@lem2328579) (@lem0)). Qed.
Lemma lem2328581 : term387.
Proof. exact (@lem2328570 (@lem2328580)). Qed.
Lemma lem2328583 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328584 : term199 = term204.
Proof. exact (@lem2328583 term112 term112). Qed.
Lemma lem2328585 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328586 : term159 = term112.
Proof. exact (EQ_MP (@lem2328585) (@lem940073)). Qed.
Lemma lem2328587 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328588 : term157 = term111.
Proof. exact (MK_COMB (@lem2328587) (@lem2328586)). Qed.
Lemma lem2328589 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328590 : term204 = term147.
Proof. exact (MK_COMB (@lem2328589) (@lem2328588)). Qed.
Lemma lem2328591 : term199 = term147.
Proof. exact (TRANS (@lem2328584) (@lem2328590)). Qed.
Lemma lem2328593 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328594 : term199 = term204.
Proof. exact (@lem2328593 term112 term112). Qed.
Lemma lem2328595 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328596 : term159 = term112.
Proof. exact (EQ_MP (@lem2328595) (@lem940073)). Qed.
Lemma lem2328597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328598 : term157 = term111.
Proof. exact (MK_COMB (@lem2328597) (@lem2328596)). Qed.
Lemma lem2328599 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328600 : term204 = term147.
Proof. exact (MK_COMB (@lem2328599) (@lem2328598)). Qed.
Lemma lem2328601 : term199 = term147.
Proof. exact (TRANS (@lem2328594) (@lem2328600)). Qed.
Lemma lem2328602 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328603 : term316 = term308.
Proof. exact (MK_COMB (@lem2328602) (@lem2328601)). Qed.
Lemma lem2328604 : term388 = term381.
Proof. exact (MK_COMB (@lem2328603) (@lem2328591)). Qed.
Lemma lem2328605 : term381 = term389.
Proof. exact (@lem1367763 term112 term112). Qed.
Lemma lem2328606 : term390 = term360.
Proof. exact (@lem706885). Qed.
Lemma lem2328607 : (term390 = term360) = (term391 = term352).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term360). Qed.
Lemma lem2328608 : term391 = term352.
Proof. exact (EQ_MP (@lem2328607) (@lem2328606)). Qed.
Lemma lem2328609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328610 : term392 = term350.
Proof. exact (MK_COMB (@lem2328609) (@lem2328608)). Qed.
Lemma lem2328611 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328612 : term389 = term384.
Proof. exact (MK_COMB (@lem2328611) (@lem2328610)). Qed.
Lemma lem2328613 : term381 = term384.
Proof. exact (TRANS (@lem2328605) (@lem2328612)). Qed.
Lemma lem2328614 : term388 = term384.
Proof. exact (TRANS (@lem2328604) (@lem2328613)). Qed.
Lemma lem2328615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328616 : term393 = term394.
Proof. exact (MK_COMB (@lem2328615) (@lem2328614)). Qed.
Lemma lem2328617 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2328618 : term395 = term396.
Proof. exact (MK_COMB (@lem2328616) (@lem2328617)). Qed.
Lemma lem2328620 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328621 : term396 = term397.
Proof. exact (@lem2328620 term352 term112). Qed.
Lemma lem2328622 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2328623 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2328624 : term361 = term352.
Proof. exact (EQ_MP (@lem2328623) (@lem2328622)). Qed.
Lemma lem2328625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328626 : term358 = term350.
Proof. exact (MK_COMB (@lem2328625) (@lem2328624)). Qed.
Lemma lem2328627 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328628 : term397 = term384.
Proof. exact (MK_COMB (@lem2328627) (@lem2328626)). Qed.
Lemma lem2328629 : term396 = term384.
Proof. exact (TRANS (@lem2328621) (@lem2328628)). Qed.
Lemma lem2328630 : term395 = term384.
Proof. exact (TRANS (@lem2328618) (@lem2328629)). Qed.
Lemma lem2328632 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328633 : term156 = term157.
Proof. exact (@lem2328632 term112 term112). Qed.
Lemma lem2328634 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328635 : term159 = term112.
Proof. exact (EQ_MP (@lem2328634) (@lem940073)). Qed.
Lemma lem2328636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328637 : term157 = term111.
Proof. exact (MK_COMB (@lem2328636) (@lem2328635)). Qed.
Lemma lem2328638 : term156 = term111.
Proof. exact (TRANS (@lem2328633) (@lem2328637)). Qed.
Lemma lem2328639 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem2328640 : term398 = term396.
Proof. exact (MK_COMB (@lem2328639) (@lem2328638)). Qed.
Lemma lem2328642 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328643 : term396 = term397.
Proof. exact (@lem2328642 term352 term112). Qed.
Lemma lem2328644 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2328645 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2328646 : term361 = term352.
Proof. exact (EQ_MP (@lem2328645) (@lem2328644)). Qed.
Lemma lem2328647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328648 : term358 = term350.
Proof. exact (MK_COMB (@lem2328647) (@lem2328646)). Qed.
Lemma lem2328649 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328650 : term397 = term384.
Proof. exact (MK_COMB (@lem2328649) (@lem2328648)). Qed.
Lemma lem2328651 : term396 = term384.
Proof. exact (TRANS (@lem2328643) (@lem2328650)). Qed.
Lemma lem2328652 : term398 = term384.
Proof. exact (TRANS (@lem2328640) (@lem2328651)). Qed.
Lemma lem2328653 : term384 = term398.
Proof. exact (SYM (@lem2328652)). Qed.
Lemma lem2328654 : term395 = term398.
Proof. exact (TRANS (@lem2328630) (@lem2328653)). Qed.
Lemma lem2328655 : term382 = term399.
Proof. exact (@lem2328581 (@lem2328654)). Qed.
Lemma lem2328656 : term381 = term399.
Proof. exact (TRANS (@lem2328547) (@lem2328655)). Qed.
Lemma lem2328658 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2328659 : term399 = term384.
Proof. exact (@lem2328658 term384). Qed.
Lemma lem2328660 : term381 = term384.
Proof. exact (TRANS (@lem2328656) (@lem2328659)). Qed.
Lemma lem2328661 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328662 : term400 = term394.
Proof. exact (MK_COMB (@lem2328661) (@lem2328660)). Qed.
Lemma lem2328663 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2328664 (x : int) : (term380 x) = (term401 x).
Proof. exact (MK_COMB (@lem2328662) (@lem2328663 x)). Qed.
Lemma lem2328665 (x : int) : (term379 x) = (term401 x).
Proof. exact (TRANS (@lem2328538 x) (@lem2328664 x)). Qed.
Lemma lem2328666 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328667 (x : int) : (term402 x) = (term403 x).
Proof. exact (MK_COMB (@lem2328666) (@lem2328665 x)). Qed.
Lemma lem2328668 (n : nat) : (term327 n) = (term328 n).
Proof. exact (@lem1982763 (term173 n) (real_of_num n) term147). Qed.
Lemma lem2328669 (n : nat) : (term329 n) = (term330 n).
Proof. exact (@lem1982713 term147 (real_of_num n)). Qed.
Lemma lem2328671 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328672 : term111 = term185.
Proof. exact (@lem2328671 term112). Qed.
Lemma lem2328674 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328675 : term147 = term148.
Proof. exact (@lem2328674 term112). Qed.
Lemma lem2328676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328677 : term308 = term309.
Proof. exact (MK_COMB (@lem2328676) (@lem2328675)). Qed.
Lemma lem2328678 : term310 = term311.
Proof. exact (MK_COMB (@lem2328677) (@lem2328672)). Qed.
Lemma lem2328679 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2328681 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328682 : term275 = term281.
Proof. exact (@lem2328681 (NUMERAL 0) term112). Qed.
Lemma lem2328683 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328684 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328685 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328684 h1) (fun h1 : term281 = True => @lem2328683)). Qed.
Lemma lem2328686 : term281 = True.
Proof. exact (EQ_MP (@lem2328685) (@lem2328683)). Qed.
Lemma lem2328687 : term275 = True.
Proof. exact (TRANS (@lem2328682) (@lem2328686)). Qed.
Lemma lem2328688 : True = term275.
Proof. exact (SYM (@lem2328687)). Qed.
Lemma lem2328689 : term275.
Proof. exact (EQ_MP (@lem2328688) (@lem0)). Qed.
Lemma lem2328690 : term313.
Proof. exact (@lem2328679 (@lem2328689)). Qed.
Lemma lem2328692 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328693 : term275 = term281.
Proof. exact (@lem2328692 (NUMERAL 0) term112). Qed.
Lemma lem2328694 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328695 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328696 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328695 h1) (fun h1 : term281 = True => @lem2328694)). Qed.
Lemma lem2328697 : term281 = True.
Proof. exact (EQ_MP (@lem2328696) (@lem2328694)). Qed.
Lemma lem2328698 : term275 = True.
Proof. exact (TRANS (@lem2328693) (@lem2328697)). Qed.
Lemma lem2328699 : True = term275.
Proof. exact (SYM (@lem2328698)). Qed.
Lemma lem2328700 : term275.
Proof. exact (EQ_MP (@lem2328699) (@lem0)). Qed.
Lemma lem2328701 : term314.
Proof. exact (@lem2328690 (@lem2328700)). Qed.
Lemma lem2328703 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328704 : term275 = term281.
Proof. exact (@lem2328703 (NUMERAL 0) term112). Qed.
Lemma lem2328705 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328706 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328707 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328706 h1) (fun h1 : term281 = True => @lem2328705)). Qed.
Lemma lem2328708 : term281 = True.
Proof. exact (EQ_MP (@lem2328707) (@lem2328705)). Qed.
Lemma lem2328709 : term275 = True.
Proof. exact (TRANS (@lem2328704) (@lem2328708)). Qed.
Lemma lem2328710 : True = term275.
Proof. exact (SYM (@lem2328709)). Qed.
Lemma lem2328711 : term275.
Proof. exact (EQ_MP (@lem2328710) (@lem0)). Qed.
Lemma lem2328712 : term315.
Proof. exact (@lem2328701 (@lem2328711)). Qed.
Lemma lem2328714 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328715 : term156 = term157.
Proof. exact (@lem2328714 term112 term112). Qed.
Lemma lem2328716 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328717 : term159 = term112.
Proof. exact (EQ_MP (@lem2328716) (@lem940073)). Qed.
Lemma lem2328718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328719 : term157 = term111.
Proof. exact (MK_COMB (@lem2328718) (@lem2328717)). Qed.
Lemma lem2328720 : term156 = term111.
Proof. exact (TRANS (@lem2328715) (@lem2328719)). Qed.
Lemma lem2328722 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328723 : term199 = term204.
Proof. exact (@lem2328722 term112 term112). Qed.
Lemma lem2328724 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328725 : term159 = term112.
Proof. exact (EQ_MP (@lem2328724) (@lem940073)). Qed.
Lemma lem2328726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328727 : term157 = term111.
Proof. exact (MK_COMB (@lem2328726) (@lem2328725)). Qed.
Lemma lem2328728 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328729 : term204 = term147.
Proof. exact (MK_COMB (@lem2328728) (@lem2328727)). Qed.
Lemma lem2328730 : term199 = term147.
Proof. exact (TRANS (@lem2328723) (@lem2328729)). Qed.
Lemma lem2328731 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328732 : term316 = term308.
Proof. exact (MK_COMB (@lem2328731) (@lem2328730)). Qed.
Lemma lem2328733 : term317 = term310.
Proof. exact (MK_COMB (@lem2328732) (@lem2328720)). Qed.
Lemma lem2328735 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2328736 : term310 = term86.
Proof. exact (@lem2328735 term112). Qed.
Lemma lem2328737 : term317 = term86.
Proof. exact (TRANS (@lem2328733) (@lem2328736)). Qed.
Lemma lem2328738 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328739 : term319 = term320.
Proof. exact (MK_COMB (@lem2328738) (@lem2328737)). Qed.
Lemma lem2328740 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2328741 : term321 = term286.
Proof. exact (MK_COMB (@lem2328739) (@lem2328740)). Qed.
Lemma lem2328743 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328744 : term286 = term86.
Proof. exact (@lem2328743 term112). Qed.
Lemma lem2328745 : term321 = term86.
Proof. exact (TRANS (@lem2328741) (@lem2328744)). Qed.
Lemma lem2328747 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328748 : term156 = term157.
Proof. exact (@lem2328747 term112 term112). Qed.
Lemma lem2328749 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328750 : term159 = term112.
Proof. exact (EQ_MP (@lem2328749) (@lem940073)). Qed.
Lemma lem2328751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328752 : term157 = term111.
Proof. exact (MK_COMB (@lem2328751) (@lem2328750)). Qed.
Lemma lem2328753 : term156 = term111.
Proof. exact (TRANS (@lem2328748) (@lem2328752)). Qed.
Lemma lem2328754 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2328755 : term322 = term286.
Proof. exact (MK_COMB (@lem2328754) (@lem2328753)). Qed.
Lemma lem2328757 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328758 : term286 = term86.
Proof. exact (@lem2328757 term112). Qed.
Lemma lem2328759 : term322 = term86.
Proof. exact (TRANS (@lem2328755) (@lem2328758)). Qed.
Lemma lem2328760 : term86 = term322.
Proof. exact (SYM (@lem2328759)). Qed.
Lemma lem2328761 : term321 = term322.
Proof. exact (TRANS (@lem2328745) (@lem2328760)). Qed.
Lemma lem2328762 : term311 = term145.
Proof. exact (@lem2328712 (@lem2328761)). Qed.
Lemma lem2328763 : term310 = term145.
Proof. exact (TRANS (@lem2328678) (@lem2328762)). Qed.
Lemma lem2328765 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2328766 : term145 = term86.
Proof. exact (@lem2328765 term86). Qed.
Lemma lem2328767 : term310 = term86.
Proof. exact (TRANS (@lem2328763) (@lem2328766)). Qed.
Lemma lem2328768 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328769 : term323 = term320.
Proof. exact (MK_COMB (@lem2328768) (@lem2328767)). Qed.
Lemma lem2328770 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2328771 (n : nat) : (term330 n) = (term285 n).
Proof. exact (MK_COMB (@lem2328769) (@lem2328770 n)). Qed.
Lemma lem2328772 (n : nat) : (term329 n) = (term285 n).
Proof. exact (TRANS (@lem2328669 n) (@lem2328771 n)). Qed.
Lemma lem2328773 (n : nat) : (term285 n) = term86.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2328774 (n : nat) : (term329 n) = term86.
Proof. exact (TRANS (@lem2328772 n) (@lem2328773 n)). Qed.
Lemma lem2328775 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328776 (n : nat) : (term331 n) = term326.
Proof. exact (MK_COMB (@lem2328775) (@lem2328774 n)). Qed.
Lemma lem2328777 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem2328778 (n : nat) : (term328 n) = term332.
Proof. exact (MK_COMB (@lem2328776 n) (@lem2328777)). Qed.
Lemma lem2328779 (n : nat) : (term327 n) = term332.
Proof. exact (TRANS (@lem2328668 n) (@lem2328778 n)). Qed.
Lemma lem2328780 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2328781 (n : nat) : (term327 n) = term147.
Proof. exact (TRANS (@lem2328779 n) (@lem2328780)). Qed.
Lemma lem2328782 (n : nat) (x : int) : (term378 x n) = (term404 x).
Proof. exact (MK_COMB (@lem2328667 x) (@lem2328781 n)). Qed.
Lemma lem2328783 (n : nat) (x : int) : (term377 x n) = (term404 x).
Proof. exact (TRANS (@lem2328537 x n) (@lem2328782 n x)). Qed.
Lemma lem2328784 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2328785 (n : nat) (x : int) : (term405 x n) = (term406 x).
Proof. exact (MK_COMB (@lem2328784) (@lem2328783 n x)). Qed.
Lemma lem2328786 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328787 (n : nat) (x : int) : (term376 x n) = (term407 x).
Proof. exact (MK_COMB (@lem2328785 n x) (@lem2328786)). Qed.
Lemma lem2328788 (x : int) (n : nat) (h1 : term347 x n) : term407 x.
Proof. exact (EQ_MP (@lem2328787 n x) (@lem2328536 x n h1)). Qed.
Lemma lem2328790 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2328791 : term274 = term275.
Proof. exact (@lem2328790 term86 term111). Qed.
Lemma lem2328793 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328794 : term111 = term185.
Proof. exact (@lem2328793 term112). Qed.
Lemma lem2328796 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328797 : term86 = term145.
Proof. exact (@lem2328796 (NUMERAL 0)). Qed.
Lemma lem2328798 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328799 : term276 = term277.
Proof. exact (MK_COMB (@lem2328798) (@lem2328797)). Qed.
Lemma lem2328800 : term275 = term278.
Proof. exact (MK_COMB (@lem2328799) (@lem2328794)). Qed.
Lemma lem2328801 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2328803 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328804 : term275 = term281.
Proof. exact (@lem2328803 (NUMERAL 0) term112). Qed.
Lemma lem2328805 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328806 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328807 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328806 h1) (fun h1 : term281 = True => @lem2328805)). Qed.
Lemma lem2328808 : term281 = True.
Proof. exact (EQ_MP (@lem2328807) (@lem2328805)). Qed.
Lemma lem2328809 : term275 = True.
Proof. exact (TRANS (@lem2328804) (@lem2328808)). Qed.
Lemma lem2328810 : True = term275.
Proof. exact (SYM (@lem2328809)). Qed.
Lemma lem2328811 : term275.
Proof. exact (EQ_MP (@lem2328810) (@lem0)). Qed.
Lemma lem2328812 : term283.
Proof. exact (@lem2328801 (@lem2328811)). Qed.
Lemma lem2328814 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328815 : term275 = term281.
Proof. exact (@lem2328814 (NUMERAL 0) term112). Qed.
Lemma lem2328816 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328817 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328818 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328817 h1) (fun h1 : term281 = True => @lem2328816)). Qed.
Lemma lem2328819 : term281 = True.
Proof. exact (EQ_MP (@lem2328818) (@lem2328816)). Qed.
Lemma lem2328820 : term275 = True.
Proof. exact (TRANS (@lem2328815) (@lem2328819)). Qed.
Lemma lem2328821 : True = term275.
Proof. exact (SYM (@lem2328820)). Qed.
Lemma lem2328822 : term275.
Proof. exact (EQ_MP (@lem2328821) (@lem0)). Qed.
Lemma lem2328823 : term278 = term284.
Proof. exact (@lem2328812 (@lem2328822)). Qed.
Lemma lem2328825 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328826 : term156 = term157.
Proof. exact (@lem2328825 term112 term112). Qed.
Lemma lem2328827 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328828 : term159 = term112.
Proof. exact (EQ_MP (@lem2328827) (@lem940073)). Qed.
Lemma lem2328829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328830 : term157 = term111.
Proof. exact (MK_COMB (@lem2328829) (@lem2328828)). Qed.
Lemma lem2328831 : term156 = term111.
Proof. exact (TRANS (@lem2328826) (@lem2328830)). Qed.
Lemma lem2328833 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328834 : term286 = term86.
Proof. exact (@lem2328833 term112). Qed.
Lemma lem2328835 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2328836 : term287 = term276.
Proof. exact (MK_COMB (@lem2328835) (@lem2328834)). Qed.
Lemma lem2328837 : term284 = term275.
Proof. exact (MK_COMB (@lem2328836) (@lem2328831)). Qed.
Lemma lem2328839 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328840 : term275 = term281.
Proof. exact (@lem2328839 (NUMERAL 0) term112). Qed.
Lemma lem2328841 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328842 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328843 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328842 h1) (fun h1 : term281 = True => @lem2328841)). Qed.
Lemma lem2328844 : term281 = True.
Proof. exact (EQ_MP (@lem2328843) (@lem2328841)). Qed.
Lemma lem2328845 : term275 = True.
Proof. exact (TRANS (@lem2328840) (@lem2328844)). Qed.
Lemma lem2328846 : term284 = True.
Proof. exact (TRANS (@lem2328837) (@lem2328845)). Qed.
Lemma lem2328847 : term278 = True.
Proof. exact (TRANS (@lem2328823) (@lem2328846)). Qed.
Lemma lem2328848 : term275 = True.
Proof. exact (TRANS (@lem2328800) (@lem2328847)). Qed.
Lemma lem2328849 : term274 = True.
Proof. exact (TRANS (@lem2328791) (@lem2328848)). Qed.
Lemma lem2328850 : True = term274.
Proof. exact (SYM (@lem2328849)). Qed.
Lemma lem2328851 : term274.
Proof. exact (EQ_MP (@lem2328850) (@lem0)). Qed.
Lemma lem2328852 (x : int) (n : nat) (h1 : term347 x n) : term408 x.
Proof. exact (conj (@lem2328851) (@lem2328788 x n h1)). Qed.
Lemma lem2328854 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2328855 (x : int) : term409 x.
Proof. exact (@lem2328854 term111 (term404 x)). Qed.
Lemma lem2328856 (x : int) (n : nat) (h1 : term347 x n) : term410 x.
Proof. exact (@lem2328855 x (@lem2328852 x n h1)). Qed.
Lemma lem2328857 (x : int) : (term411 x) = (term404 x).
Proof. exact (@lem1982733 (term404 x)). Qed.
Lemma lem2328858 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2328859 (x : int) : (term412 x) = (term406 x).
Proof. exact (MK_COMB (@lem2328858) (@lem2328857 x)). Qed.
Lemma lem2328860 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328861 (x : int) : (term410 x) = (term407 x).
Proof. exact (MK_COMB (@lem2328859 x) (@lem2328860)). Qed.
Lemma lem2328862 (x : int) (n : nat) (h1 : term347 x n) : term407 x.
Proof. exact (EQ_MP (@lem2328861 x) (@lem2328856 x n h1)). Qed.
Lemma lem2328863 (x : int) (n : nat) (h1 : term347 x n) : term413 x.
Proof. exact (conj (@lem2328862 x n h1) (@lem2328438 x n h1)). Qed.
Lemma lem2328865 (x : real) (y : real) : term414 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2328866 (x : int) : term415 x.
Proof. exact (@lem2328865 (term404 x) (term416 x)). Qed.
Lemma lem2328867 (x : int) (n : nat) (h1 : term347 x n) : term417 x.
Proof. exact (@lem2328866 x (@lem2328863 x n h1)). Qed.
Lemma lem2328868 (x : int) : (term418 x) = (term419 x).
Proof. exact (@lem1982759 (term401 x) (term416 x) term147). Qed.
Lemma lem2328869 (x : int) : (term420 x) = (term421 x).
Proof. exact (@lem1982711 term384 term350 (real_of_int x)). Qed.
Lemma lem2328871 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328872 : term350 = term351.
Proof. exact (@lem2328871 term352). Qed.
Lemma lem2328874 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328875 : term384 = term399.
Proof. exact (@lem2328874 term352). Qed.
Lemma lem2328876 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328877 : term422 = term423.
Proof. exact (MK_COMB (@lem2328876) (@lem2328875)). Qed.
Lemma lem2328878 : term424 = term425.
Proof. exact (MK_COMB (@lem2328877) (@lem2328872)). Qed.
Lemma lem2328879 : term426.
Proof. exact (@lem1981473 term384 term111 term350 term111 term86 term111). Qed.
Lemma lem2328881 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328882 : term275 = term281.
Proof. exact (@lem2328881 (NUMERAL 0) term112). Qed.
Lemma lem2328883 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328884 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328885 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328884 h1) (fun h1 : term281 = True => @lem2328883)). Qed.
Lemma lem2328886 : term281 = True.
Proof. exact (EQ_MP (@lem2328885) (@lem2328883)). Qed.
Lemma lem2328887 : term275 = True.
Proof. exact (TRANS (@lem2328882) (@lem2328886)). Qed.
Lemma lem2328888 : True = term275.
Proof. exact (SYM (@lem2328887)). Qed.
Lemma lem2328889 : term275.
Proof. exact (EQ_MP (@lem2328888) (@lem0)). Qed.
Lemma lem2328890 : term427.
Proof. exact (@lem2328879 (@lem2328889)). Qed.
Lemma lem2328892 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328893 : term275 = term281.
Proof. exact (@lem2328892 (NUMERAL 0) term112). Qed.
Lemma lem2328894 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328895 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328896 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328895 h1) (fun h1 : term281 = True => @lem2328894)). Qed.
Lemma lem2328897 : term281 = True.
Proof. exact (EQ_MP (@lem2328896) (@lem2328894)). Qed.
Lemma lem2328898 : term275 = True.
Proof. exact (TRANS (@lem2328893) (@lem2328897)). Qed.
Lemma lem2328899 : True = term275.
Proof. exact (SYM (@lem2328898)). Qed.
Lemma lem2328900 : term275.
Proof. exact (EQ_MP (@lem2328899) (@lem0)). Qed.
Lemma lem2328901 : term428.
Proof. exact (@lem2328890 (@lem2328900)). Qed.
Lemma lem2328903 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2328904 : term275 = term281.
Proof. exact (@lem2328903 (NUMERAL 0) term112). Qed.
Lemma lem2328905 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2328906 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2328907 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2328906 h1) (fun h1 : term281 = True => @lem2328905)). Qed.
Lemma lem2328908 : term281 = True.
Proof. exact (EQ_MP (@lem2328907) (@lem2328905)). Qed.
Lemma lem2328909 : term275 = True.
Proof. exact (TRANS (@lem2328904) (@lem2328908)). Qed.
Lemma lem2328910 : True = term275.
Proof. exact (SYM (@lem2328909)). Qed.
Lemma lem2328911 : term275.
Proof. exact (EQ_MP (@lem2328910) (@lem0)). Qed.
Lemma lem2328912 : term429.
Proof. exact (@lem2328901 (@lem2328911)). Qed.
Lemma lem2328914 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328915 : term357 = term358.
Proof. exact (@lem2328914 term352 term112). Qed.
Lemma lem2328916 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2328917 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2328918 : term361 = term352.
Proof. exact (EQ_MP (@lem2328917) (@lem2328916)). Qed.
Lemma lem2328919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328920 : term358 = term350.
Proof. exact (MK_COMB (@lem2328919) (@lem2328918)). Qed.
Lemma lem2328921 : term357 = term350.
Proof. exact (TRANS (@lem2328915) (@lem2328920)). Qed.
Lemma lem2328923 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2328924 : term396 = term397.
Proof. exact (@lem2328923 term352 term112). Qed.
Lemma lem2328925 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2328926 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2328927 : term361 = term352.
Proof. exact (EQ_MP (@lem2328926) (@lem2328925)). Qed.
Lemma lem2328928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328929 : term358 = term350.
Proof. exact (MK_COMB (@lem2328928) (@lem2328927)). Qed.
Lemma lem2328930 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2328931 : term397 = term384.
Proof. exact (MK_COMB (@lem2328930) (@lem2328929)). Qed.
Lemma lem2328932 : term396 = term384.
Proof. exact (TRANS (@lem2328924) (@lem2328931)). Qed.
Lemma lem2328933 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328934 : term430 = term422.
Proof. exact (MK_COMB (@lem2328933) (@lem2328932)). Qed.
Lemma lem2328935 : term431 = term424.
Proof. exact (MK_COMB (@lem2328934) (@lem2328921)). Qed.
Lemma lem2328937 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2328938 : term424 = term86.
Proof. exact (@lem2328937 term352). Qed.
Lemma lem2328939 : term431 = term86.
Proof. exact (TRANS (@lem2328935) (@lem2328938)). Qed.
Lemma lem2328940 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328941 : term432 = term320.
Proof. exact (MK_COMB (@lem2328940) (@lem2328939)). Qed.
Lemma lem2328942 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2328943 : term433 = term286.
Proof. exact (MK_COMB (@lem2328941) (@lem2328942)). Qed.
Lemma lem2328945 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328946 : term286 = term86.
Proof. exact (@lem2328945 term112). Qed.
Lemma lem2328947 : term433 = term86.
Proof. exact (TRANS (@lem2328943) (@lem2328946)). Qed.
Lemma lem2328949 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2328950 : term156 = term157.
Proof. exact (@lem2328949 term112 term112). Qed.
Lemma lem2328951 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2328952 : term159 = term112.
Proof. exact (EQ_MP (@lem2328951) (@lem940073)). Qed.
Lemma lem2328953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2328954 : term157 = term111.
Proof. exact (MK_COMB (@lem2328953) (@lem2328952)). Qed.
Lemma lem2328955 : term156 = term111.
Proof. exact (TRANS (@lem2328950) (@lem2328954)). Qed.
Lemma lem2328956 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2328957 : term322 = term286.
Proof. exact (MK_COMB (@lem2328956) (@lem2328955)). Qed.
Lemma lem2328959 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2328960 : term286 = term86.
Proof. exact (@lem2328959 term112). Qed.
Lemma lem2328961 : term322 = term86.
Proof. exact (TRANS (@lem2328957) (@lem2328960)). Qed.
Lemma lem2328962 : term86 = term322.
Proof. exact (SYM (@lem2328961)). Qed.
Lemma lem2328963 : term433 = term322.
Proof. exact (TRANS (@lem2328947) (@lem2328962)). Qed.
Lemma lem2328964 : term425 = term145.
Proof. exact (@lem2328912 (@lem2328963)). Qed.
Lemma lem2328965 : term424 = term145.
Proof. exact (TRANS (@lem2328878) (@lem2328964)). Qed.
Lemma lem2328967 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2328968 : term145 = term86.
Proof. exact (@lem2328967 term86). Qed.
Lemma lem2328969 : term424 = term86.
Proof. exact (TRANS (@lem2328965) (@lem2328968)). Qed.
Lemma lem2328970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2328971 : term434 = term320.
Proof. exact (MK_COMB (@lem2328970) (@lem2328969)). Qed.
Lemma lem2328972 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2328973 (x : int) : (term421 x) = (term324 x).
Proof. exact (MK_COMB (@lem2328971) (@lem2328972 x)). Qed.
Lemma lem2328974 (x : int) : (term420 x) = (term324 x).
Proof. exact (TRANS (@lem2328869 x) (@lem2328973 x)). Qed.
Lemma lem2328975 (x : int) : (term324 x) = term86.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2328976 (x : int) : (term420 x) = term86.
Proof. exact (TRANS (@lem2328974 x) (@lem2328975 x)). Qed.
Lemma lem2328977 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2328978 (x : int) : (term435 x) = term326.
Proof. exact (MK_COMB (@lem2328977) (@lem2328976 x)). Qed.
Lemma lem2328979 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem2328980 (x : int) : (term419 x) = term332.
Proof. exact (MK_COMB (@lem2328978 x) (@lem2328979)). Qed.
Lemma lem2328981 (x : int) : (term418 x) = term332.
Proof. exact (TRANS (@lem2328868 x) (@lem2328980 x)). Qed.
Lemma lem2328982 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2328983 (x : int) : (term418 x) = term147.
Proof. exact (TRANS (@lem2328981 x) (@lem2328982)). Qed.
Lemma lem2328984 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2328985 (x : int) : (term436 x) = term334.
Proof. exact (MK_COMB (@lem2328984) (@lem2328983 x)). Qed.
Lemma lem2328986 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2328987 (x : int) : (term417 x) = term335.
Proof. exact (MK_COMB (@lem2328985 x) (@lem2328986)). Qed.
Lemma lem2328988 (x : int) (n : nat) (h1 : term347 x n) : term335.
Proof. exact (EQ_MP (@lem2328987 x) (@lem2328867 x n h1)). Qed.
Lemma lem2328990 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2328991 : term335 = term336.
Proof. exact (@lem2328990 term86 term147). Qed.
Lemma lem2328993 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2328994 : term147 = term148.
Proof. exact (@lem2328993 term112). Qed.
Lemma lem2328996 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2328997 : term86 = term145.
Proof. exact (@lem2328996 (NUMERAL 0)). Qed.
Lemma lem2328998 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2328999 : term88 = term337.
Proof. exact (MK_COMB (@lem2328998) (@lem2328997)). Qed.
Lemma lem2329000 : term336 = term338.
Proof. exact (MK_COMB (@lem2328999) (@lem2328994)). Qed.
Lemma lem2329001 : term339.
Proof. exact (@lem1980026 term86 term111 term147 term111). Qed.
Lemma lem2329003 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329004 : term275 = term281.
Proof. exact (@lem2329003 (NUMERAL 0) term112). Qed.
Lemma lem2329005 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329006 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329007 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329006 h1) (fun h1 : term281 = True => @lem2329005)). Qed.
Lemma lem2329008 : term281 = True.
Proof. exact (EQ_MP (@lem2329007) (@lem2329005)). Qed.
Lemma lem2329009 : term275 = True.
Proof. exact (TRANS (@lem2329004) (@lem2329008)). Qed.
Lemma lem2329010 : True = term275.
Proof. exact (SYM (@lem2329009)). Qed.
Lemma lem2329011 : term275.
Proof. exact (EQ_MP (@lem2329010) (@lem0)). Qed.
Lemma lem2329012 : term340.
Proof. exact (@lem2329001 (@lem2329011)). Qed.
Lemma lem2329014 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329015 : term275 = term281.
Proof. exact (@lem2329014 (NUMERAL 0) term112). Qed.
Lemma lem2329016 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329017 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329018 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329017 h1) (fun h1 : term281 = True => @lem2329016)). Qed.
Lemma lem2329019 : term281 = True.
Proof. exact (EQ_MP (@lem2329018) (@lem2329016)). Qed.
Lemma lem2329020 : term275 = True.
Proof. exact (TRANS (@lem2329015) (@lem2329019)). Qed.
Lemma lem2329021 : True = term275.
Proof. exact (SYM (@lem2329020)). Qed.
Lemma lem2329022 : term275.
Proof. exact (EQ_MP (@lem2329021) (@lem0)). Qed.
Lemma lem2329023 : term338 = term341.
Proof. exact (@lem2329012 (@lem2329022)). Qed.
Lemma lem2329025 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2329026 : term199 = term204.
Proof. exact (@lem2329025 term112 term112). Qed.
Lemma lem2329027 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329028 : term159 = term112.
Proof. exact (EQ_MP (@lem2329027) (@lem940073)). Qed.
Lemma lem2329029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329030 : term157 = term111.
Proof. exact (MK_COMB (@lem2329029) (@lem2329028)). Qed.
Lemma lem2329031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2329032 : term204 = term147.
Proof. exact (MK_COMB (@lem2329031) (@lem2329030)). Qed.
Lemma lem2329033 : term199 = term147.
Proof. exact (TRANS (@lem2329026) (@lem2329032)). Qed.
Lemma lem2329035 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329036 : term286 = term86.
Proof. exact (@lem2329035 term112). Qed.
Lemma lem2329037 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2329038 : term342 = term88.
Proof. exact (MK_COMB (@lem2329037) (@lem2329036)). Qed.
Lemma lem2329039 : term341 = term336.
Proof. exact (MK_COMB (@lem2329038) (@lem2329033)). Qed.
Lemma lem2329041 (m : nat) (n : nat) : (term343 m n) = (term344 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2329042 : term336 = term345.
Proof. exact (@lem2329041 (NUMERAL 0) term112). Qed.
Lemma lem2329043 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329044 (h1 : term282 = (BIT1 0)) : (term112 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2329045 : (term282 = (BIT1 0)) = ((term112 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329044 h1) (fun h1 : (term112 = (NUMERAL 0)) = False => @lem2329043)). Qed.
Lemma lem2329046 : (term112 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2329045) (@lem2329043)). Qed.
Lemma lem2329047 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2329048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2329049 : term346 = (and True).
Proof. exact (MK_COMB (@lem2329048) (@lem2329047)). Qed.
Lemma lem2329050 : term345 = (True /\ False).
Proof. exact (MK_COMB (@lem2329049) (@lem2329046)). Qed.
Lemma lem2329052 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2329053 : term345 = False.
Proof. exact (TRANS (@lem2329050) (@lem2329052)). Qed.
Lemma lem2329054 : term336 = False.
Proof. exact (TRANS (@lem2329042) (@lem2329053)). Qed.
Lemma lem2329055 : term341 = False.
Proof. exact (TRANS (@lem2329039) (@lem2329054)). Qed.
Lemma lem2329056 : term338 = False.
Proof. exact (TRANS (@lem2329023) (@lem2329055)). Qed.
Lemma lem2329057 : term336 = False.
Proof. exact (TRANS (@lem2329000) (@lem2329056)). Qed.
Lemma lem2329058 : term335 = False.
Proof. exact (TRANS (@lem2328991) (@lem2329057)). Qed.
Lemma lem2329059 (x : int) (n : nat) (h1 : term347 x n) : False.
Proof. exact (EQ_MP (@lem2329058) (@lem2328988 x n h1)). Qed.
Lemma lem2329060 (x : int) (n : nat) (h1 : term265 x n) : False.
Proof. exact (or_elim (@lem2327956 x n h1) (fun h0 : term273 x n => @lem2328357 x n h0) (fun h0 : term347 x n => @lem2329059 x n h0)). Qed.
Lemma lem2329061 (x : int) (n : nat) (h1 : term261 x n) : term261 x n.
Proof. exact (h1). Qed.
Lemma lem2329062 (x : int) (n : nat) (h1 : term437 x n) : term437 x n.
Proof. exact (h1). Qed.
Lemma lem2329063 (x : int) (n : nat) (h1 : term437 x n) : term262 x n.
Proof. exact (proj2 (@lem2329062 x n h1)). Qed.
Lemma lem2329065 (x : int) (n : nat) (h1 : term437 x n) : term225 x n.
Proof. exact (proj2 (@lem2329063 x n h1)). Qed.
Lemma lem2329066 (x : int) (n : nat) (h1 : term437 x n) : (term169 x n) = term86.
Proof. exact (proj1 (@lem2329063 x n h1)). Qed.
Lemma lem2329069 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2329070 : term274 = term275.
Proof. exact (@lem2329069 term86 term111). Qed.
Lemma lem2329072 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329073 : term111 = term185.
Proof. exact (@lem2329072 term112). Qed.
Lemma lem2329075 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329076 : term86 = term145.
Proof. exact (@lem2329075 (NUMERAL 0)). Qed.
Lemma lem2329077 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329078 : term276 = term277.
Proof. exact (MK_COMB (@lem2329077) (@lem2329076)). Qed.
Lemma lem2329079 : term275 = term278.
Proof. exact (MK_COMB (@lem2329078) (@lem2329073)). Qed.
Lemma lem2329080 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2329082 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329083 : term275 = term281.
Proof. exact (@lem2329082 (NUMERAL 0) term112). Qed.
Lemma lem2329084 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329085 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329086 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329085 h1) (fun h1 : term281 = True => @lem2329084)). Qed.
Lemma lem2329087 : term281 = True.
Proof. exact (EQ_MP (@lem2329086) (@lem2329084)). Qed.
Lemma lem2329088 : term275 = True.
Proof. exact (TRANS (@lem2329083) (@lem2329087)). Qed.
Lemma lem2329089 : True = term275.
Proof. exact (SYM (@lem2329088)). Qed.
Lemma lem2329090 : term275.
Proof. exact (EQ_MP (@lem2329089) (@lem0)). Qed.
Lemma lem2329091 : term283.
Proof. exact (@lem2329080 (@lem2329090)). Qed.
Lemma lem2329093 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329094 : term275 = term281.
Proof. exact (@lem2329093 (NUMERAL 0) term112). Qed.
Lemma lem2329095 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329096 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329097 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329096 h1) (fun h1 : term281 = True => @lem2329095)). Qed.
Lemma lem2329098 : term281 = True.
Proof. exact (EQ_MP (@lem2329097) (@lem2329095)). Qed.
Lemma lem2329099 : term275 = True.
Proof. exact (TRANS (@lem2329094) (@lem2329098)). Qed.
Lemma lem2329100 : True = term275.
Proof. exact (SYM (@lem2329099)). Qed.
Lemma lem2329101 : term275.
Proof. exact (EQ_MP (@lem2329100) (@lem0)). Qed.
Lemma lem2329102 : term278 = term284.
Proof. exact (@lem2329091 (@lem2329101)). Qed.
Lemma lem2329104 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329105 : term156 = term157.
Proof. exact (@lem2329104 term112 term112). Qed.
Lemma lem2329106 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329107 : term159 = term112.
Proof. exact (EQ_MP (@lem2329106) (@lem940073)). Qed.
Lemma lem2329108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329109 : term157 = term111.
Proof. exact (MK_COMB (@lem2329108) (@lem2329107)). Qed.
Lemma lem2329110 : term156 = term111.
Proof. exact (TRANS (@lem2329105) (@lem2329109)). Qed.
Lemma lem2329112 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329113 : term286 = term86.
Proof. exact (@lem2329112 term112). Qed.
Lemma lem2329114 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329115 : term287 = term276.
Proof. exact (MK_COMB (@lem2329114) (@lem2329113)). Qed.
Lemma lem2329116 : term284 = term275.
Proof. exact (MK_COMB (@lem2329115) (@lem2329110)). Qed.
Lemma lem2329118 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329119 : term275 = term281.
Proof. exact (@lem2329118 (NUMERAL 0) term112). Qed.
Lemma lem2329120 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329121 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329122 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329121 h1) (fun h1 : term281 = True => @lem2329120)). Qed.
Lemma lem2329123 : term281 = True.
Proof. exact (EQ_MP (@lem2329122) (@lem2329120)). Qed.
Lemma lem2329124 : term275 = True.
Proof. exact (TRANS (@lem2329119) (@lem2329123)). Qed.
Lemma lem2329125 : term284 = True.
Proof. exact (TRANS (@lem2329116) (@lem2329124)). Qed.
Lemma lem2329126 : term278 = True.
Proof. exact (TRANS (@lem2329102) (@lem2329125)). Qed.
Lemma lem2329127 : term275 = True.
Proof. exact (TRANS (@lem2329079) (@lem2329126)). Qed.
Lemma lem2329128 : term274 = True.
Proof. exact (TRANS (@lem2329070) (@lem2329127)). Qed.
Lemma lem2329129 : True = term274.
Proof. exact (SYM (@lem2329128)). Qed.
Lemma lem2329130 : term274.
Proof. exact (EQ_MP (@lem2329129) (@lem0)). Qed.
Lemma lem2329131 (x : int) (n : nat) (h1 : term437 x n) : term438 x n.
Proof. exact (conj (@lem2329130) (@lem2329065 x n h1)). Qed.
Lemma lem2329133 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2329134 (x : int) (n : nat) : term439 x n.
Proof. exact (@lem2329133 term111 (term222 x n)). Qed.
Lemma lem2329135 (x : int) (n : nat) (h1 : term437 x n) : term440 x n.
Proof. exact (@lem2329134 x n (@lem2329131 x n h1)). Qed.
Lemma lem2329136 (x : int) (n : nat) : (term441 x n) = (term222 x n).
Proof. exact (@lem1982733 (term222 x n)). Qed.
Lemma lem2329137 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2329138 (x : int) (n : nat) : (term442 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2329137) (@lem2329136 x n)). Qed.
Lemma lem2329139 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329140 (x : int) (n : nat) : (term440 x n) = (term225 x n).
Proof. exact (MK_COMB (@lem2329138 x n) (@lem2329139)). Qed.
Lemma lem2329141 (x : int) (n : nat) (h1 : term437 x n) : term225 x n.
Proof. exact (EQ_MP (@lem2329140 x n) (@lem2329135 x n h1)). Qed.
Lemma lem2329143 (y : real) : term294 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2329144 (x : int) (n : nat) : term295 x n.
Proof. exact (@lem2329143 (term169 x n)). Qed.
Lemma lem2329145 (x : int) (n : nat) (h1 : term437 x n) : term296 x n.
Proof. exact (@lem2329144 x n (@lem2329066 x n h1)). Qed.
Lemma lem2329146 (x : int) (n : nat) (h1 : term437 x n) : term443 x n.
Proof. exact (@lem2329145 x n h1 term147). Qed.
Lemma lem2329147 (x : int) (n : nat) : (term443 x n) = ((term444 x n) = term86).
Proof. exact (eq_refl (term443 x n)). Qed.
Lemma lem2329148 (x : int) (n : nat) (h1 : term437 x n) : (term444 x n) = term86.
Proof. exact (EQ_MP (@lem2329147 x n) (@lem2329146 x n h1)). Qed.
Lemma lem2329149 (x : int) (n : nat) : (term444 x n) = (term445 x n).
Proof. exact (@lem1982781 (real_of_int x) term147 (term173 n)). Qed.
Lemma lem2329150 (n : nat) : (term177 n) = (term178 n).
Proof. exact (@lem1982749 term147 term147 (real_of_num n)). Qed.
Lemma lem2329152 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2329153 : term147 = term148.
Proof. exact (@lem2329152 term112). Qed.
Lemma lem2329155 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2329156 : term147 = term148.
Proof. exact (@lem2329155 term112). Qed.
Lemma lem2329157 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329158 : term149 = term150.
Proof. exact (MK_COMB (@lem2329157) (@lem2329156)). Qed.
Lemma lem2329159 : term179 = term180.
Proof. exact (MK_COMB (@lem2329158) (@lem2329153)). Qed.
Lemma lem2329160 : term180 = term181.
Proof. exact (@lem1981613 term147 term147 term111 term111). Qed.
Lemma lem2329162 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329163 : term156 = term157.
Proof. exact (@lem2329162 term112 term112). Qed.
Lemma lem2329164 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329165 : term159 = term112.
Proof. exact (EQ_MP (@lem2329164) (@lem940073)). Qed.
Lemma lem2329166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329167 : term157 = term111.
Proof. exact (MK_COMB (@lem2329166) (@lem2329165)). Qed.
Lemma lem2329168 : term156 = term111.
Proof. exact (TRANS (@lem2329163) (@lem2329167)). Qed.
Lemma lem2329170 (m : nat) (n : nat) : (term182 m n) = (term155 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2329171 : term179 = term157.
Proof. exact (@lem2329170 term112 term112). Qed.
Lemma lem2329172 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329173 : term159 = term112.
Proof. exact (EQ_MP (@lem2329172) (@lem940073)). Qed.
Lemma lem2329174 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329175 : term157 = term111.
Proof. exact (MK_COMB (@lem2329174) (@lem2329173)). Qed.
Lemma lem2329176 : term179 = term111.
Proof. exact (TRANS (@lem2329171) (@lem2329175)). Qed.
Lemma lem2329177 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2329178 : term183 = term184.
Proof. exact (MK_COMB (@lem2329177) (@lem2329176)). Qed.
Lemma lem2329179 : term181 = term185.
Proof. exact (MK_COMB (@lem2329178) (@lem2329168)). Qed.
Lemma lem2329180 : term180 = term185.
Proof. exact (TRANS (@lem2329160) (@lem2329179)). Qed.
Lemma lem2329181 : term179 = term185.
Proof. exact (TRANS (@lem2329159) (@lem2329180)). Qed.
Lemma lem2329183 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2329184 : term185 = term111.
Proof. exact (@lem2329183 term111). Qed.
Lemma lem2329185 : term179 = term111.
Proof. exact (TRANS (@lem2329181) (@lem2329184)). Qed.
Lemma lem2329186 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329187 : term186 = term187.
Proof. exact (MK_COMB (@lem2329186) (@lem2329185)). Qed.
Lemma lem2329188 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2329189 (n : nat) : (term178 n) = (term188 n).
Proof. exact (MK_COMB (@lem2329187) (@lem2329188 n)). Qed.
Lemma lem2329190 (n : nat) : (term177 n) = (term188 n).
Proof. exact (TRANS (@lem2329150 n) (@lem2329189 n)). Qed.
Lemma lem2329191 (n : nat) : (term188 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2329192 (n : nat) : (term177 n) = (real_of_num n).
Proof. exact (TRANS (@lem2329190 n) (@lem2329191 n)). Qed.
Lemma lem2329195 (x : int) : (term207 x) = (term207 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem2329196 (x : int) (n : nat) : (term445 x n) = (term446 x n).
Proof. exact (MK_COMB (@lem2329195 x) (@lem2329192 n)). Qed.
Lemma lem2329197 (x : int) (n : nat) : (term444 x n) = (term446 x n).
Proof. exact (TRANS (@lem2329149 x n) (@lem2329196 x n)). Qed.
Lemma lem2329198 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2329199 (x : int) (n : nat) : (term447 x n) = (term448 x n).
Proof. exact (MK_COMB (@lem2329198) (@lem2329197 x n)). Qed.
Lemma lem2329200 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329201 (x : int) (n : nat) : ((term444 x n) = term86) = ((term446 x n) = term86).
Proof. exact (MK_COMB (@lem2329199 x n) (@lem2329200)). Qed.
Lemma lem2329202 (x : int) (n : nat) (h1 : term437 x n) : (term446 x n) = term86.
Proof. exact (EQ_MP (@lem2329201 x n) (@lem2329148 x n h1)). Qed.
Lemma lem2329203 (x : int) (n : nat) (h1 : term437 x n) : term449 x n.
Proof. exact (conj (@lem2329202 x n h1) (@lem2329141 x n h1)). Qed.
Lemma lem2329205 (x : real) (y : real) : term300 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2329206 (x : int) (n : nat) : term450 x n.
Proof. exact (@lem2329205 (term446 x n) (term222 x n)). Qed.
Lemma lem2329207 (x : int) (n : nat) (h1 : term437 x n) : term451 x n.
Proof. exact (@lem2329206 x n (@lem2329203 x n h1)). Qed.
Lemma lem2329208 (x : int) (n : nat) : (term452 x n) = (term453 x n).
Proof. exact (@lem1982753 (term211 x) (real_of_int x) (real_of_num n) (term221 n)). Qed.
Lemma lem2329209 (x : int) : (term454 x) = (term307 x).
Proof. exact (@lem1982713 term147 (real_of_int x)). Qed.
Lemma lem2329211 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329212 : term111 = term185.
Proof. exact (@lem2329211 term112). Qed.
Lemma lem2329214 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2329215 : term147 = term148.
Proof. exact (@lem2329214 term112). Qed.
Lemma lem2329216 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329217 : term308 = term309.
Proof. exact (MK_COMB (@lem2329216) (@lem2329215)). Qed.
Lemma lem2329218 : term310 = term311.
Proof. exact (MK_COMB (@lem2329217) (@lem2329212)). Qed.
Lemma lem2329219 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2329221 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329222 : term275 = term281.
Proof. exact (@lem2329221 (NUMERAL 0) term112). Qed.
Lemma lem2329223 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329224 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329225 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329224 h1) (fun h1 : term281 = True => @lem2329223)). Qed.
Lemma lem2329226 : term281 = True.
Proof. exact (EQ_MP (@lem2329225) (@lem2329223)). Qed.
Lemma lem2329227 : term275 = True.
Proof. exact (TRANS (@lem2329222) (@lem2329226)). Qed.
Lemma lem2329228 : True = term275.
Proof. exact (SYM (@lem2329227)). Qed.
Lemma lem2329229 : term275.
Proof. exact (EQ_MP (@lem2329228) (@lem0)). Qed.
Lemma lem2329230 : term313.
Proof. exact (@lem2329219 (@lem2329229)). Qed.
Lemma lem2329232 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329233 : term275 = term281.
Proof. exact (@lem2329232 (NUMERAL 0) term112). Qed.
Lemma lem2329234 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329235 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329236 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329235 h1) (fun h1 : term281 = True => @lem2329234)). Qed.
Lemma lem2329237 : term281 = True.
Proof. exact (EQ_MP (@lem2329236) (@lem2329234)). Qed.
Lemma lem2329238 : term275 = True.
Proof. exact (TRANS (@lem2329233) (@lem2329237)). Qed.
Lemma lem2329239 : True = term275.
Proof. exact (SYM (@lem2329238)). Qed.
Lemma lem2329240 : term275.
Proof. exact (EQ_MP (@lem2329239) (@lem0)). Qed.
Lemma lem2329241 : term314.
Proof. exact (@lem2329230 (@lem2329240)). Qed.
Lemma lem2329243 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329244 : term275 = term281.
Proof. exact (@lem2329243 (NUMERAL 0) term112). Qed.
Lemma lem2329245 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329246 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329247 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329246 h1) (fun h1 : term281 = True => @lem2329245)). Qed.
Lemma lem2329248 : term281 = True.
Proof. exact (EQ_MP (@lem2329247) (@lem2329245)). Qed.
Lemma lem2329249 : term275 = True.
Proof. exact (TRANS (@lem2329244) (@lem2329248)). Qed.
Lemma lem2329250 : True = term275.
Proof. exact (SYM (@lem2329249)). Qed.
Lemma lem2329251 : term275.
Proof. exact (EQ_MP (@lem2329250) (@lem0)). Qed.
Lemma lem2329252 : term315.
Proof. exact (@lem2329241 (@lem2329251)). Qed.
Lemma lem2329254 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329255 : term156 = term157.
Proof. exact (@lem2329254 term112 term112). Qed.
Lemma lem2329256 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329257 : term159 = term112.
Proof. exact (EQ_MP (@lem2329256) (@lem940073)). Qed.
Lemma lem2329258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329259 : term157 = term111.
Proof. exact (MK_COMB (@lem2329258) (@lem2329257)). Qed.
Lemma lem2329260 : term156 = term111.
Proof. exact (TRANS (@lem2329255) (@lem2329259)). Qed.
Lemma lem2329262 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2329263 : term199 = term204.
Proof. exact (@lem2329262 term112 term112). Qed.
Lemma lem2329264 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329265 : term159 = term112.
Proof. exact (EQ_MP (@lem2329264) (@lem940073)). Qed.
Lemma lem2329266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329267 : term157 = term111.
Proof. exact (MK_COMB (@lem2329266) (@lem2329265)). Qed.
Lemma lem2329268 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2329269 : term204 = term147.
Proof. exact (MK_COMB (@lem2329268) (@lem2329267)). Qed.
Lemma lem2329270 : term199 = term147.
Proof. exact (TRANS (@lem2329263) (@lem2329269)). Qed.
Lemma lem2329271 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329272 : term316 = term308.
Proof. exact (MK_COMB (@lem2329271) (@lem2329270)). Qed.
Lemma lem2329273 : term317 = term310.
Proof. exact (MK_COMB (@lem2329272) (@lem2329260)). Qed.
Lemma lem2329275 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2329276 : term310 = term86.
Proof. exact (@lem2329275 term112). Qed.
Lemma lem2329277 : term317 = term86.
Proof. exact (TRANS (@lem2329273) (@lem2329276)). Qed.
Lemma lem2329278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329279 : term319 = term320.
Proof. exact (MK_COMB (@lem2329278) (@lem2329277)). Qed.
Lemma lem2329280 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2329281 : term321 = term286.
Proof. exact (MK_COMB (@lem2329279) (@lem2329280)). Qed.
Lemma lem2329283 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329284 : term286 = term86.
Proof. exact (@lem2329283 term112). Qed.
Lemma lem2329285 : term321 = term86.
Proof. exact (TRANS (@lem2329281) (@lem2329284)). Qed.
Lemma lem2329287 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329288 : term156 = term157.
Proof. exact (@lem2329287 term112 term112). Qed.
Lemma lem2329289 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329290 : term159 = term112.
Proof. exact (EQ_MP (@lem2329289) (@lem940073)). Qed.
Lemma lem2329291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329292 : term157 = term111.
Proof. exact (MK_COMB (@lem2329291) (@lem2329290)). Qed.
Lemma lem2329293 : term156 = term111.
Proof. exact (TRANS (@lem2329288) (@lem2329292)). Qed.
Lemma lem2329294 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2329295 : term322 = term286.
Proof. exact (MK_COMB (@lem2329294) (@lem2329293)). Qed.
Lemma lem2329297 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329298 : term286 = term86.
Proof. exact (@lem2329297 term112). Qed.
Lemma lem2329299 : term322 = term86.
Proof. exact (TRANS (@lem2329295) (@lem2329298)). Qed.
Lemma lem2329300 : term86 = term322.
Proof. exact (SYM (@lem2329299)). Qed.
Lemma lem2329301 : term321 = term322.
Proof. exact (TRANS (@lem2329285) (@lem2329300)). Qed.
Lemma lem2329302 : term311 = term145.
Proof. exact (@lem2329252 (@lem2329301)). Qed.
Lemma lem2329303 : term310 = term145.
Proof. exact (TRANS (@lem2329218) (@lem2329302)). Qed.
Lemma lem2329305 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2329306 : term145 = term86.
Proof. exact (@lem2329305 term86). Qed.
Lemma lem2329307 : term310 = term86.
Proof. exact (TRANS (@lem2329303) (@lem2329306)). Qed.
Lemma lem2329308 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329309 : term323 = term320.
Proof. exact (MK_COMB (@lem2329308) (@lem2329307)). Qed.
Lemma lem2329310 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2329311 (x : int) : (term307 x) = (term324 x).
Proof. exact (MK_COMB (@lem2329309) (@lem2329310 x)). Qed.
Lemma lem2329312 (x : int) : (term454 x) = (term324 x).
Proof. exact (TRANS (@lem2329209 x) (@lem2329311 x)). Qed.
Lemma lem2329313 (x : int) : (term324 x) = term86.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2329314 (x : int) : (term454 x) = term86.
Proof. exact (TRANS (@lem2329312 x) (@lem2329313 x)). Qed.
Lemma lem2329315 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329316 (x : int) : (term455 x) = term326.
Proof. exact (MK_COMB (@lem2329315) (@lem2329314 x)). Qed.
Lemma lem2329317 (n : nat) : (term456 n) = (term457 n).
Proof. exact (@lem1982763 (real_of_num n) (term173 n) term147). Qed.
Lemma lem2329318 (n : nat) : (term458 n) = (term330 n).
Proof. exact (@lem1982715 term147 (real_of_num n)). Qed.
Lemma lem2329320 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329321 : term111 = term185.
Proof. exact (@lem2329320 term112). Qed.
Lemma lem2329323 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2329324 : term147 = term148.
Proof. exact (@lem2329323 term112). Qed.
Lemma lem2329325 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329326 : term308 = term309.
Proof. exact (MK_COMB (@lem2329325) (@lem2329324)). Qed.
Lemma lem2329327 : term310 = term311.
Proof. exact (MK_COMB (@lem2329326) (@lem2329321)). Qed.
Lemma lem2329328 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2329330 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329331 : term275 = term281.
Proof. exact (@lem2329330 (NUMERAL 0) term112). Qed.
Lemma lem2329332 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329333 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329334 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329333 h1) (fun h1 : term281 = True => @lem2329332)). Qed.
Lemma lem2329335 : term281 = True.
Proof. exact (EQ_MP (@lem2329334) (@lem2329332)). Qed.
Lemma lem2329336 : term275 = True.
Proof. exact (TRANS (@lem2329331) (@lem2329335)). Qed.
Lemma lem2329337 : True = term275.
Proof. exact (SYM (@lem2329336)). Qed.
Lemma lem2329338 : term275.
Proof. exact (EQ_MP (@lem2329337) (@lem0)). Qed.
Lemma lem2329339 : term313.
Proof. exact (@lem2329328 (@lem2329338)). Qed.
Lemma lem2329341 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329342 : term275 = term281.
Proof. exact (@lem2329341 (NUMERAL 0) term112). Qed.
Lemma lem2329343 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329344 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329345 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329344 h1) (fun h1 : term281 = True => @lem2329343)). Qed.
Lemma lem2329346 : term281 = True.
Proof. exact (EQ_MP (@lem2329345) (@lem2329343)). Qed.
Lemma lem2329347 : term275 = True.
Proof. exact (TRANS (@lem2329342) (@lem2329346)). Qed.
Lemma lem2329348 : True = term275.
Proof. exact (SYM (@lem2329347)). Qed.
Lemma lem2329349 : term275.
Proof. exact (EQ_MP (@lem2329348) (@lem0)). Qed.
Lemma lem2329350 : term314.
Proof. exact (@lem2329339 (@lem2329349)). Qed.
Lemma lem2329352 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329353 : term275 = term281.
Proof. exact (@lem2329352 (NUMERAL 0) term112). Qed.
Lemma lem2329354 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329355 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329356 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329355 h1) (fun h1 : term281 = True => @lem2329354)). Qed.
Lemma lem2329357 : term281 = True.
Proof. exact (EQ_MP (@lem2329356) (@lem2329354)). Qed.
Lemma lem2329358 : term275 = True.
Proof. exact (TRANS (@lem2329353) (@lem2329357)). Qed.
Lemma lem2329359 : True = term275.
Proof. exact (SYM (@lem2329358)). Qed.
Lemma lem2329360 : term275.
Proof. exact (EQ_MP (@lem2329359) (@lem0)). Qed.
Lemma lem2329361 : term315.
Proof. exact (@lem2329350 (@lem2329360)). Qed.
Lemma lem2329363 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329364 : term156 = term157.
Proof. exact (@lem2329363 term112 term112). Qed.
Lemma lem2329365 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329366 : term159 = term112.
Proof. exact (EQ_MP (@lem2329365) (@lem940073)). Qed.
Lemma lem2329367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329368 : term157 = term111.
Proof. exact (MK_COMB (@lem2329367) (@lem2329366)). Qed.
Lemma lem2329369 : term156 = term111.
Proof. exact (TRANS (@lem2329364) (@lem2329368)). Qed.
Lemma lem2329371 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2329372 : term199 = term204.
Proof. exact (@lem2329371 term112 term112). Qed.
Lemma lem2329373 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329374 : term159 = term112.
Proof. exact (EQ_MP (@lem2329373) (@lem940073)). Qed.
Lemma lem2329375 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329376 : term157 = term111.
Proof. exact (MK_COMB (@lem2329375) (@lem2329374)). Qed.
Lemma lem2329377 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2329378 : term204 = term147.
Proof. exact (MK_COMB (@lem2329377) (@lem2329376)). Qed.
Lemma lem2329379 : term199 = term147.
Proof. exact (TRANS (@lem2329372) (@lem2329378)). Qed.
Lemma lem2329380 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329381 : term316 = term308.
Proof. exact (MK_COMB (@lem2329380) (@lem2329379)). Qed.
Lemma lem2329382 : term317 = term310.
Proof. exact (MK_COMB (@lem2329381) (@lem2329369)). Qed.
Lemma lem2329384 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2329385 : term310 = term86.
Proof. exact (@lem2329384 term112). Qed.
Lemma lem2329386 : term317 = term86.
Proof. exact (TRANS (@lem2329382) (@lem2329385)). Qed.
Lemma lem2329387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329388 : term319 = term320.
Proof. exact (MK_COMB (@lem2329387) (@lem2329386)). Qed.
Lemma lem2329389 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2329390 : term321 = term286.
Proof. exact (MK_COMB (@lem2329388) (@lem2329389)). Qed.
Lemma lem2329392 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329393 : term286 = term86.
Proof. exact (@lem2329392 term112). Qed.
Lemma lem2329394 : term321 = term86.
Proof. exact (TRANS (@lem2329390) (@lem2329393)). Qed.
Lemma lem2329396 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329397 : term156 = term157.
Proof. exact (@lem2329396 term112 term112). Qed.
Lemma lem2329398 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329399 : term159 = term112.
Proof. exact (EQ_MP (@lem2329398) (@lem940073)). Qed.
Lemma lem2329400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329401 : term157 = term111.
Proof. exact (MK_COMB (@lem2329400) (@lem2329399)). Qed.
Lemma lem2329402 : term156 = term111.
Proof. exact (TRANS (@lem2329397) (@lem2329401)). Qed.
Lemma lem2329403 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2329404 : term322 = term286.
Proof. exact (MK_COMB (@lem2329403) (@lem2329402)). Qed.
Lemma lem2329406 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329407 : term286 = term86.
Proof. exact (@lem2329406 term112). Qed.
Lemma lem2329408 : term322 = term86.
Proof. exact (TRANS (@lem2329404) (@lem2329407)). Qed.
Lemma lem2329409 : term86 = term322.
Proof. exact (SYM (@lem2329408)). Qed.
Lemma lem2329410 : term321 = term322.
Proof. exact (TRANS (@lem2329394) (@lem2329409)). Qed.
Lemma lem2329411 : term311 = term145.
Proof. exact (@lem2329361 (@lem2329410)). Qed.
Lemma lem2329412 : term310 = term145.
Proof. exact (TRANS (@lem2329327) (@lem2329411)). Qed.
Lemma lem2329414 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2329415 : term145 = term86.
Proof. exact (@lem2329414 term86). Qed.
Lemma lem2329416 : term310 = term86.
Proof. exact (TRANS (@lem2329412) (@lem2329415)). Qed.
Lemma lem2329417 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329418 : term323 = term320.
Proof. exact (MK_COMB (@lem2329417) (@lem2329416)). Qed.
Lemma lem2329419 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2329420 (n : nat) : (term330 n) = (term285 n).
Proof. exact (MK_COMB (@lem2329418) (@lem2329419 n)). Qed.
Lemma lem2329421 (n : nat) : (term458 n) = (term285 n).
Proof. exact (TRANS (@lem2329318 n) (@lem2329420 n)). Qed.
Lemma lem2329422 (n : nat) : (term285 n) = term86.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2329423 (n : nat) : (term458 n) = term86.
Proof. exact (TRANS (@lem2329421 n) (@lem2329422 n)). Qed.
Lemma lem2329424 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329425 (n : nat) : (term459 n) = term326.
Proof. exact (MK_COMB (@lem2329424) (@lem2329423 n)). Qed.
Lemma lem2329426 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem2329427 (n : nat) : (term457 n) = term332.
Proof. exact (MK_COMB (@lem2329425 n) (@lem2329426)). Qed.
Lemma lem2329428 (n : nat) : (term456 n) = term332.
Proof. exact (TRANS (@lem2329317 n) (@lem2329427 n)). Qed.
Lemma lem2329429 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2329430 (n : nat) : (term456 n) = term147.
Proof. exact (TRANS (@lem2329428 n) (@lem2329429)). Qed.
Lemma lem2329431 (x : int) (n : nat) : (term453 x n) = term332.
Proof. exact (MK_COMB (@lem2329316 x) (@lem2329430 n)). Qed.
Lemma lem2329432 (x : int) (n : nat) : (term452 x n) = term332.
Proof. exact (TRANS (@lem2329208 x n) (@lem2329431 x n)). Qed.
Lemma lem2329433 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2329434 (x : int) (n : nat) : (term452 x n) = term147.
Proof. exact (TRANS (@lem2329432 x n) (@lem2329433)). Qed.
Lemma lem2329435 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2329436 (x : int) (n : nat) : (term460 x n) = term334.
Proof. exact (MK_COMB (@lem2329435) (@lem2329434 x n)). Qed.
Lemma lem2329437 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329438 (x : int) (n : nat) : (term451 x n) = term335.
Proof. exact (MK_COMB (@lem2329436 x n) (@lem2329437)). Qed.
Lemma lem2329439 (x : int) (n : nat) (h1 : term437 x n) : term335.
Proof. exact (EQ_MP (@lem2329438 x n) (@lem2329207 x n h1)). Qed.
Lemma lem2329441 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2329442 : term335 = term336.
Proof. exact (@lem2329441 term86 term147). Qed.
Lemma lem2329444 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2329445 : term147 = term148.
Proof. exact (@lem2329444 term112). Qed.
Lemma lem2329447 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329448 : term86 = term145.
Proof. exact (@lem2329447 (NUMERAL 0)). Qed.
Lemma lem2329449 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2329450 : term88 = term337.
Proof. exact (MK_COMB (@lem2329449) (@lem2329448)). Qed.
Lemma lem2329451 : term336 = term338.
Proof. exact (MK_COMB (@lem2329450) (@lem2329445)). Qed.
Lemma lem2329452 : term339.
Proof. exact (@lem1980026 term86 term111 term147 term111). Qed.
Lemma lem2329454 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329455 : term275 = term281.
Proof. exact (@lem2329454 (NUMERAL 0) term112). Qed.
Lemma lem2329456 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329457 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329458 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329457 h1) (fun h1 : term281 = True => @lem2329456)). Qed.
Lemma lem2329459 : term281 = True.
Proof. exact (EQ_MP (@lem2329458) (@lem2329456)). Qed.
Lemma lem2329460 : term275 = True.
Proof. exact (TRANS (@lem2329455) (@lem2329459)). Qed.
Lemma lem2329461 : True = term275.
Proof. exact (SYM (@lem2329460)). Qed.
Lemma lem2329462 : term275.
Proof. exact (EQ_MP (@lem2329461) (@lem0)). Qed.
Lemma lem2329463 : term340.
Proof. exact (@lem2329452 (@lem2329462)). Qed.
Lemma lem2329465 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329466 : term275 = term281.
Proof. exact (@lem2329465 (NUMERAL 0) term112). Qed.
Lemma lem2329467 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329468 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329469 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329468 h1) (fun h1 : term281 = True => @lem2329467)). Qed.
Lemma lem2329470 : term281 = True.
Proof. exact (EQ_MP (@lem2329469) (@lem2329467)). Qed.
Lemma lem2329471 : term275 = True.
Proof. exact (TRANS (@lem2329466) (@lem2329470)). Qed.
Lemma lem2329472 : True = term275.
Proof. exact (SYM (@lem2329471)). Qed.
Lemma lem2329473 : term275.
Proof. exact (EQ_MP (@lem2329472) (@lem0)). Qed.
Lemma lem2329474 : term338 = term341.
Proof. exact (@lem2329463 (@lem2329473)). Qed.
Lemma lem2329476 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2329477 : term199 = term204.
Proof. exact (@lem2329476 term112 term112). Qed.
Lemma lem2329478 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329479 : term159 = term112.
Proof. exact (EQ_MP (@lem2329478) (@lem940073)). Qed.
Lemma lem2329480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329481 : term157 = term111.
Proof. exact (MK_COMB (@lem2329480) (@lem2329479)). Qed.
Lemma lem2329482 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2329483 : term204 = term147.
Proof. exact (MK_COMB (@lem2329482) (@lem2329481)). Qed.
Lemma lem2329484 : term199 = term147.
Proof. exact (TRANS (@lem2329477) (@lem2329483)). Qed.
Lemma lem2329486 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329487 : term286 = term86.
Proof. exact (@lem2329486 term112). Qed.
Lemma lem2329488 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2329489 : term342 = term88.
Proof. exact (MK_COMB (@lem2329488) (@lem2329487)). Qed.
Lemma lem2329490 : term341 = term336.
Proof. exact (MK_COMB (@lem2329489) (@lem2329484)). Qed.
Lemma lem2329492 (m : nat) (n : nat) : (term343 m n) = (term344 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2329493 : term336 = term345.
Proof. exact (@lem2329492 (NUMERAL 0) term112). Qed.
Lemma lem2329494 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329495 (h1 : term282 = (BIT1 0)) : (term112 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2329496 : (term282 = (BIT1 0)) = ((term112 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329495 h1) (fun h1 : (term112 = (NUMERAL 0)) = False => @lem2329494)). Qed.
Lemma lem2329497 : (term112 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2329496) (@lem2329494)). Qed.
Lemma lem2329498 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2329499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2329500 : term346 = (and True).
Proof. exact (MK_COMB (@lem2329499) (@lem2329498)). Qed.
Lemma lem2329501 : term345 = (True /\ False).
Proof. exact (MK_COMB (@lem2329500) (@lem2329497)). Qed.
Lemma lem2329503 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2329504 : term345 = False.
Proof. exact (TRANS (@lem2329501) (@lem2329503)). Qed.
Lemma lem2329505 : term336 = False.
Proof. exact (TRANS (@lem2329493) (@lem2329504)). Qed.
Lemma lem2329506 : term341 = False.
Proof. exact (TRANS (@lem2329490) (@lem2329505)). Qed.
Lemma lem2329507 : term338 = False.
Proof. exact (TRANS (@lem2329474) (@lem2329506)). Qed.
Lemma lem2329508 : term336 = False.
Proof. exact (TRANS (@lem2329451) (@lem2329507)). Qed.
Lemma lem2329509 : term335 = False.
Proof. exact (TRANS (@lem2329442) (@lem2329508)). Qed.
Lemma lem2329510 (x : int) (n : nat) (h1 : term437 x n) : False.
Proof. exact (EQ_MP (@lem2329509) (@lem2329439 x n h1)). Qed.
Lemma lem2329511 (x : int) (n : nat) (h1 : term461 x n) : term461 x n.
Proof. exact (h1). Qed.
Lemma lem2329512 (x : int) (n : nat) (h1 : term461 x n) : term263 x n.
Proof. exact (proj2 (@lem2329511 x n h1)). Qed.
Lemma lem2329514 (x : int) (n : nat) (h1 : term461 x n) : term225 x n.
Proof. exact (proj2 (@lem2329512 x n h1)). Qed.
Lemma lem2329515 (x : int) (n : nat) (h1 : term461 x n) : (term189 x n) = term86.
Proof. exact (proj1 (@lem2329512 x n h1)). Qed.
Lemma lem2329516 (n : nat) : term462 n.
Proof. exact (@lem1396812 n). Qed.
Lemma lem2329518 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2329519 : term274 = term275.
Proof. exact (@lem2329518 term86 term111). Qed.
Lemma lem2329521 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329522 : term111 = term185.
Proof. exact (@lem2329521 term112). Qed.
Lemma lem2329524 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329525 : term86 = term145.
Proof. exact (@lem2329524 (NUMERAL 0)). Qed.
Lemma lem2329526 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329527 : term276 = term277.
Proof. exact (MK_COMB (@lem2329526) (@lem2329525)). Qed.
Lemma lem2329528 : term275 = term278.
Proof. exact (MK_COMB (@lem2329527) (@lem2329522)). Qed.
Lemma lem2329529 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2329531 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329532 : term275 = term281.
Proof. exact (@lem2329531 (NUMERAL 0) term112). Qed.
Lemma lem2329533 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329534 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329535 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329534 h1) (fun h1 : term281 = True => @lem2329533)). Qed.
Lemma lem2329536 : term281 = True.
Proof. exact (EQ_MP (@lem2329535) (@lem2329533)). Qed.
Lemma lem2329537 : term275 = True.
Proof. exact (TRANS (@lem2329532) (@lem2329536)). Qed.
Lemma lem2329538 : True = term275.
Proof. exact (SYM (@lem2329537)). Qed.
Lemma lem2329539 : term275.
Proof. exact (EQ_MP (@lem2329538) (@lem0)). Qed.
Lemma lem2329540 : term283.
Proof. exact (@lem2329529 (@lem2329539)). Qed.
Lemma lem2329542 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329543 : term275 = term281.
Proof. exact (@lem2329542 (NUMERAL 0) term112). Qed.
Lemma lem2329544 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329545 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329546 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329545 h1) (fun h1 : term281 = True => @lem2329544)). Qed.
Lemma lem2329547 : term281 = True.
Proof. exact (EQ_MP (@lem2329546) (@lem2329544)). Qed.
Lemma lem2329548 : term275 = True.
Proof. exact (TRANS (@lem2329543) (@lem2329547)). Qed.
Lemma lem2329549 : True = term275.
Proof. exact (SYM (@lem2329548)). Qed.
Lemma lem2329550 : term275.
Proof. exact (EQ_MP (@lem2329549) (@lem0)). Qed.
Lemma lem2329551 : term278 = term284.
Proof. exact (@lem2329540 (@lem2329550)). Qed.
Lemma lem2329553 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329554 : term156 = term157.
Proof. exact (@lem2329553 term112 term112). Qed.
Lemma lem2329555 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329556 : term159 = term112.
Proof. exact (EQ_MP (@lem2329555) (@lem940073)). Qed.
Lemma lem2329557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329558 : term157 = term111.
Proof. exact (MK_COMB (@lem2329557) (@lem2329556)). Qed.
Lemma lem2329559 : term156 = term111.
Proof. exact (TRANS (@lem2329554) (@lem2329558)). Qed.
Lemma lem2329561 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329562 : term286 = term86.
Proof. exact (@lem2329561 term112). Qed.
Lemma lem2329563 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329564 : term287 = term276.
Proof. exact (MK_COMB (@lem2329563) (@lem2329562)). Qed.
Lemma lem2329565 : term284 = term275.
Proof. exact (MK_COMB (@lem2329564) (@lem2329559)). Qed.
Lemma lem2329567 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329568 : term275 = term281.
Proof. exact (@lem2329567 (NUMERAL 0) term112). Qed.
Lemma lem2329569 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329570 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329571 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329570 h1) (fun h1 : term281 = True => @lem2329569)). Qed.
Lemma lem2329572 : term281 = True.
Proof. exact (EQ_MP (@lem2329571) (@lem2329569)). Qed.
Lemma lem2329573 : term275 = True.
Proof. exact (TRANS (@lem2329568) (@lem2329572)). Qed.
Lemma lem2329574 : term284 = True.
Proof. exact (TRANS (@lem2329565) (@lem2329573)). Qed.
Lemma lem2329575 : term278 = True.
Proof. exact (TRANS (@lem2329551) (@lem2329574)). Qed.
Lemma lem2329576 : term275 = True.
Proof. exact (TRANS (@lem2329528) (@lem2329575)). Qed.
Lemma lem2329577 : term274 = True.
Proof. exact (TRANS (@lem2329519) (@lem2329576)). Qed.
Lemma lem2329578 : True = term274.
Proof. exact (SYM (@lem2329577)). Qed.
Lemma lem2329579 : term274.
Proof. exact (EQ_MP (@lem2329578) (@lem0)). Qed.
Lemma lem2329580 (x : int) (n : nat) (h1 : term461 x n) : term438 x n.
Proof. exact (conj (@lem2329579) (@lem2329514 x n h1)). Qed.
Lemma lem2329582 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2329583 (x : int) (n : nat) : term439 x n.
Proof. exact (@lem2329582 term111 (term222 x n)). Qed.
Lemma lem2329584 (x : int) (n : nat) (h1 : term461 x n) : term440 x n.
Proof. exact (@lem2329583 x n (@lem2329580 x n h1)). Qed.
Lemma lem2329585 (x : int) (n : nat) : (term441 x n) = (term222 x n).
Proof. exact (@lem1982733 (term222 x n)). Qed.
Lemma lem2329586 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2329587 (x : int) (n : nat) : (term442 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2329586) (@lem2329585 x n)). Qed.
Lemma lem2329588 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329589 (x : int) (n : nat) : (term440 x n) = (term225 x n).
Proof. exact (MK_COMB (@lem2329587 x n) (@lem2329588)). Qed.
Lemma lem2329590 (x : int) (n : nat) (h1 : term461 x n) : term225 x n.
Proof. exact (EQ_MP (@lem2329589 x n) (@lem2329584 x n h1)). Qed.
Lemma lem2329592 (y : real) : term294 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2329593 (x : int) (n : nat) : term367 x n.
Proof. exact (@lem2329592 (term189 x n)). Qed.
Lemma lem2329594 (x : int) (n : nat) (h1 : term461 x n) : term368 x n.
Proof. exact (@lem2329593 x n (@lem2329515 x n h1)). Qed.
Lemma lem2329595 (x : int) (n : nat) (h1 : term461 x n) : term463 x n.
Proof. exact (@lem2329594 x n h1 term111). Qed.
Lemma lem2329596 (x : int) (n : nat) : (term463 x n) = ((term464 x n) = term86).
Proof. exact (eq_refl (term463 x n)). Qed.
Lemma lem2329597 (x : int) (n : nat) (h1 : term461 x n) : (term464 x n) = term86.
Proof. exact (EQ_MP (@lem2329596 x n) (@lem2329595 x n h1)). Qed.
Lemma lem2329598 (x : int) (n : nat) : (term464 x n) = (term189 x n).
Proof. exact (@lem1982733 (term189 x n)). Qed.
Lemma lem2329599 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2329600 (x : int) (n : nat) : (term465 x n) = (term191 x n).
Proof. exact (MK_COMB (@lem2329599) (@lem2329598 x n)). Qed.
Lemma lem2329601 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329602 (x : int) (n : nat) : ((term464 x n) = term86) = ((term189 x n) = term86).
Proof. exact (MK_COMB (@lem2329600 x n) (@lem2329601)). Qed.
Lemma lem2329603 (x : int) (n : nat) (h1 : term461 x n) : (term189 x n) = term86.
Proof. exact (EQ_MP (@lem2329602 x n) (@lem2329597 x n h1)). Qed.
Lemma lem2329604 (x : int) (n : nat) (h1 : term461 x n) : term263 x n.
Proof. exact (conj (@lem2329603 x n h1) (@lem2329590 x n h1)). Qed.
Lemma lem2329606 (x : real) (y : real) : term300 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2329607 (x : int) (n : nat) : term466 x n.
Proof. exact (@lem2329606 (term189 x n) (term222 x n)). Qed.
Lemma lem2329608 (x : int) (n : nat) (h1 : term461 x n) : term467 x n.
Proof. exact (@lem2329607 x n (@lem2329604 x n h1)). Qed.
Lemma lem2329609 (x : int) (n : nat) : (term468 x n) = (term469 x n).
Proof. exact (@lem1982753 (real_of_int x) (real_of_int x) (real_of_num n) (term221 n)). Qed.
Lemma lem2329610 (x : int) : (term470 x) = (term471 x).
Proof. exact (@lem1982717 (real_of_int x)). Qed.
Lemma lem2329612 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329613 : term111 = term185.
Proof. exact (@lem2329612 term112). Qed.
Lemma lem2329615 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329616 : term111 = term185.
Proof. exact (@lem2329615 term112). Qed.
Lemma lem2329617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329618 : term472 = term473.
Proof. exact (MK_COMB (@lem2329617) (@lem2329616)). Qed.
Lemma lem2329619 : term474 = term475.
Proof. exact (MK_COMB (@lem2329618) (@lem2329613)). Qed.
Lemma lem2329620 : term476.
Proof. exact (@lem1981473 term111 term111 term111 term111 term350 term111). Qed.
Lemma lem2329622 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329623 : term275 = term281.
Proof. exact (@lem2329622 (NUMERAL 0) term112). Qed.
Lemma lem2329624 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329625 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329626 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329625 h1) (fun h1 : term281 = True => @lem2329624)). Qed.
Lemma lem2329627 : term281 = True.
Proof. exact (EQ_MP (@lem2329626) (@lem2329624)). Qed.
Lemma lem2329628 : term275 = True.
Proof. exact (TRANS (@lem2329623) (@lem2329627)). Qed.
Lemma lem2329629 : True = term275.
Proof. exact (SYM (@lem2329628)). Qed.
Lemma lem2329630 : term275.
Proof. exact (EQ_MP (@lem2329629) (@lem0)). Qed.
Lemma lem2329631 : term477.
Proof. exact (@lem2329620 (@lem2329630)). Qed.
Lemma lem2329633 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329634 : term275 = term281.
Proof. exact (@lem2329633 (NUMERAL 0) term112). Qed.
Lemma lem2329635 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329636 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329637 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329636 h1) (fun h1 : term281 = True => @lem2329635)). Qed.
Lemma lem2329638 : term281 = True.
Proof. exact (EQ_MP (@lem2329637) (@lem2329635)). Qed.
Lemma lem2329639 : term275 = True.
Proof. exact (TRANS (@lem2329634) (@lem2329638)). Qed.
Lemma lem2329640 : True = term275.
Proof. exact (SYM (@lem2329639)). Qed.
Lemma lem2329641 : term275.
Proof. exact (EQ_MP (@lem2329640) (@lem0)). Qed.
Lemma lem2329642 : term478.
Proof. exact (@lem2329631 (@lem2329641)). Qed.
Lemma lem2329644 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329645 : term275 = term281.
Proof. exact (@lem2329644 (NUMERAL 0) term112). Qed.
Lemma lem2329646 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329647 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329648 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329647 h1) (fun h1 : term281 = True => @lem2329646)). Qed.
Lemma lem2329649 : term281 = True.
Proof. exact (EQ_MP (@lem2329648) (@lem2329646)). Qed.
Lemma lem2329650 : term275 = True.
Proof. exact (TRANS (@lem2329645) (@lem2329649)). Qed.
Lemma lem2329651 : True = term275.
Proof. exact (SYM (@lem2329650)). Qed.
Lemma lem2329652 : term275.
Proof. exact (EQ_MP (@lem2329651) (@lem0)). Qed.
Lemma lem2329653 : term479.
Proof. exact (@lem2329642 (@lem2329652)). Qed.
Lemma lem2329655 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329656 : term156 = term157.
Proof. exact (@lem2329655 term112 term112). Qed.
Lemma lem2329657 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329658 : term159 = term112.
Proof. exact (EQ_MP (@lem2329657) (@lem940073)). Qed.
Lemma lem2329659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329660 : term157 = term111.
Proof. exact (MK_COMB (@lem2329659) (@lem2329658)). Qed.
Lemma lem2329661 : term156 = term111.
Proof. exact (TRANS (@lem2329656) (@lem2329660)). Qed.
Lemma lem2329663 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329664 : term156 = term157.
Proof. exact (@lem2329663 term112 term112). Qed.
Lemma lem2329665 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329666 : term159 = term112.
Proof. exact (EQ_MP (@lem2329665) (@lem940073)). Qed.
Lemma lem2329667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329668 : term157 = term111.
Proof. exact (MK_COMB (@lem2329667) (@lem2329666)). Qed.
Lemma lem2329669 : term156 = term111.
Proof. exact (TRANS (@lem2329664) (@lem2329668)). Qed.
Lemma lem2329670 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329671 : term480 = term472.
Proof. exact (MK_COMB (@lem2329670) (@lem2329669)). Qed.
Lemma lem2329672 : term481 = term474.
Proof. exact (MK_COMB (@lem2329671) (@lem2329661)). Qed.
Lemma lem2329673 : term474 = term392.
Proof. exact (@lem1367770 term112 term112). Qed.
Lemma lem2329674 : term390 = term360.
Proof. exact (@lem706885). Qed.
Lemma lem2329675 : (term390 = term360) = (term391 = term352).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term360). Qed.
Lemma lem2329676 : term391 = term352.
Proof. exact (EQ_MP (@lem2329675) (@lem2329674)). Qed.
Lemma lem2329677 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329678 : term392 = term350.
Proof. exact (MK_COMB (@lem2329677) (@lem2329676)). Qed.
Lemma lem2329679 : term474 = term350.
Proof. exact (TRANS (@lem2329673) (@lem2329678)). Qed.
Lemma lem2329680 : term481 = term350.
Proof. exact (TRANS (@lem2329672) (@lem2329679)). Qed.
Lemma lem2329681 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329682 : term482 = term483.
Proof. exact (MK_COMB (@lem2329681) (@lem2329680)). Qed.
Lemma lem2329683 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2329684 : term484 = term357.
Proof. exact (MK_COMB (@lem2329682) (@lem2329683)). Qed.
Lemma lem2329686 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329687 : term357 = term358.
Proof. exact (@lem2329686 term352 term112). Qed.
Lemma lem2329688 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2329689 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2329690 : term361 = term352.
Proof. exact (EQ_MP (@lem2329689) (@lem2329688)). Qed.
Lemma lem2329691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329692 : term358 = term350.
Proof. exact (MK_COMB (@lem2329691) (@lem2329690)). Qed.
Lemma lem2329693 : term357 = term350.
Proof. exact (TRANS (@lem2329687) (@lem2329692)). Qed.
Lemma lem2329694 : term484 = term350.
Proof. exact (TRANS (@lem2329684) (@lem2329693)). Qed.
Lemma lem2329696 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329697 : term156 = term157.
Proof. exact (@lem2329696 term112 term112). Qed.
Lemma lem2329698 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329699 : term159 = term112.
Proof. exact (EQ_MP (@lem2329698) (@lem940073)). Qed.
Lemma lem2329700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329701 : term157 = term111.
Proof. exact (MK_COMB (@lem2329700) (@lem2329699)). Qed.
Lemma lem2329702 : term156 = term111.
Proof. exact (TRANS (@lem2329697) (@lem2329701)). Qed.
Lemma lem2329703 : term483 = term483.
Proof. exact (eq_refl term483). Qed.
Lemma lem2329704 : term485 = term357.
Proof. exact (MK_COMB (@lem2329703) (@lem2329702)). Qed.
Lemma lem2329706 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329707 : term357 = term358.
Proof. exact (@lem2329706 term352 term112). Qed.
Lemma lem2329708 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2329709 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2329710 : term361 = term352.
Proof. exact (EQ_MP (@lem2329709) (@lem2329708)). Qed.
Lemma lem2329711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329712 : term358 = term350.
Proof. exact (MK_COMB (@lem2329711) (@lem2329710)). Qed.
Lemma lem2329713 : term357 = term350.
Proof. exact (TRANS (@lem2329707) (@lem2329712)). Qed.
Lemma lem2329714 : term485 = term350.
Proof. exact (TRANS (@lem2329704) (@lem2329713)). Qed.
Lemma lem2329715 : term350 = term485.
Proof. exact (SYM (@lem2329714)). Qed.
Lemma lem2329716 : term484 = term485.
Proof. exact (TRANS (@lem2329694) (@lem2329715)). Qed.
Lemma lem2329717 : term475 = term351.
Proof. exact (@lem2329653 (@lem2329716)). Qed.
Lemma lem2329718 : term474 = term351.
Proof. exact (TRANS (@lem2329619) (@lem2329717)). Qed.
Lemma lem2329720 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2329721 : term351 = term350.
Proof. exact (@lem2329720 term350). Qed.
Lemma lem2329722 : term474 = term350.
Proof. exact (TRANS (@lem2329718) (@lem2329721)). Qed.
Lemma lem2329723 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329724 : term486 = term483.
Proof. exact (MK_COMB (@lem2329723) (@lem2329722)). Qed.
Lemma lem2329725 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2329726 (x : int) : (term471 x) = (term416 x).
Proof. exact (MK_COMB (@lem2329724) (@lem2329725 x)). Qed.
Lemma lem2329727 (x : int) : (term470 x) = (term416 x).
Proof. exact (TRANS (@lem2329610 x) (@lem2329726 x)). Qed.
Lemma lem2329728 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329729 (x : int) : (term487 x) = (term488 x).
Proof. exact (MK_COMB (@lem2329728) (@lem2329727 x)). Qed.
Lemma lem2329730 (n : nat) : (term456 n) = (term457 n).
Proof. exact (@lem1982763 (real_of_num n) (term173 n) term147). Qed.
Lemma lem2329731 (n : nat) : (term458 n) = (term330 n).
Proof. exact (@lem1982715 term147 (real_of_num n)). Qed.
Lemma lem2329733 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329734 : term111 = term185.
Proof. exact (@lem2329733 term112). Qed.
Lemma lem2329736 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2329737 : term147 = term148.
Proof. exact (@lem2329736 term112). Qed.
Lemma lem2329738 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329739 : term308 = term309.
Proof. exact (MK_COMB (@lem2329738) (@lem2329737)). Qed.
Lemma lem2329740 : term310 = term311.
Proof. exact (MK_COMB (@lem2329739) (@lem2329734)). Qed.
Lemma lem2329741 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2329743 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329744 : term275 = term281.
Proof. exact (@lem2329743 (NUMERAL 0) term112). Qed.
Lemma lem2329745 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329746 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329747 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329746 h1) (fun h1 : term281 = True => @lem2329745)). Qed.
Lemma lem2329748 : term281 = True.
Proof. exact (EQ_MP (@lem2329747) (@lem2329745)). Qed.
Lemma lem2329749 : term275 = True.
Proof. exact (TRANS (@lem2329744) (@lem2329748)). Qed.
Lemma lem2329750 : True = term275.
Proof. exact (SYM (@lem2329749)). Qed.
Lemma lem2329751 : term275.
Proof. exact (EQ_MP (@lem2329750) (@lem0)). Qed.
Lemma lem2329752 : term313.
Proof. exact (@lem2329741 (@lem2329751)). Qed.
Lemma lem2329754 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329755 : term275 = term281.
Proof. exact (@lem2329754 (NUMERAL 0) term112). Qed.
Lemma lem2329756 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329757 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329758 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329757 h1) (fun h1 : term281 = True => @lem2329756)). Qed.
Lemma lem2329759 : term281 = True.
Proof. exact (EQ_MP (@lem2329758) (@lem2329756)). Qed.
Lemma lem2329760 : term275 = True.
Proof. exact (TRANS (@lem2329755) (@lem2329759)). Qed.
Lemma lem2329761 : True = term275.
Proof. exact (SYM (@lem2329760)). Qed.
Lemma lem2329762 : term275.
Proof. exact (EQ_MP (@lem2329761) (@lem0)). Qed.
Lemma lem2329763 : term314.
Proof. exact (@lem2329752 (@lem2329762)). Qed.
Lemma lem2329765 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329766 : term275 = term281.
Proof. exact (@lem2329765 (NUMERAL 0) term112). Qed.
Lemma lem2329767 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329768 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329769 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329768 h1) (fun h1 : term281 = True => @lem2329767)). Qed.
Lemma lem2329770 : term281 = True.
Proof. exact (EQ_MP (@lem2329769) (@lem2329767)). Qed.
Lemma lem2329771 : term275 = True.
Proof. exact (TRANS (@lem2329766) (@lem2329770)). Qed.
Lemma lem2329772 : True = term275.
Proof. exact (SYM (@lem2329771)). Qed.
Lemma lem2329773 : term275.
Proof. exact (EQ_MP (@lem2329772) (@lem0)). Qed.
Lemma lem2329774 : term315.
Proof. exact (@lem2329763 (@lem2329773)). Qed.
Lemma lem2329776 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329777 : term156 = term157.
Proof. exact (@lem2329776 term112 term112). Qed.
Lemma lem2329778 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329779 : term159 = term112.
Proof. exact (EQ_MP (@lem2329778) (@lem940073)). Qed.
Lemma lem2329780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329781 : term157 = term111.
Proof. exact (MK_COMB (@lem2329780) (@lem2329779)). Qed.
Lemma lem2329782 : term156 = term111.
Proof. exact (TRANS (@lem2329777) (@lem2329781)). Qed.
Lemma lem2329784 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2329785 : term199 = term204.
Proof. exact (@lem2329784 term112 term112). Qed.
Lemma lem2329786 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329787 : term159 = term112.
Proof. exact (EQ_MP (@lem2329786) (@lem940073)). Qed.
Lemma lem2329788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329789 : term157 = term111.
Proof. exact (MK_COMB (@lem2329788) (@lem2329787)). Qed.
Lemma lem2329790 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2329791 : term204 = term147.
Proof. exact (MK_COMB (@lem2329790) (@lem2329789)). Qed.
Lemma lem2329792 : term199 = term147.
Proof. exact (TRANS (@lem2329785) (@lem2329791)). Qed.
Lemma lem2329793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329794 : term316 = term308.
Proof. exact (MK_COMB (@lem2329793) (@lem2329792)). Qed.
Lemma lem2329795 : term317 = term310.
Proof. exact (MK_COMB (@lem2329794) (@lem2329782)). Qed.
Lemma lem2329797 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2329798 : term310 = term86.
Proof. exact (@lem2329797 term112). Qed.
Lemma lem2329799 : term317 = term86.
Proof. exact (TRANS (@lem2329795) (@lem2329798)). Qed.
Lemma lem2329800 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329801 : term319 = term320.
Proof. exact (MK_COMB (@lem2329800) (@lem2329799)). Qed.
Lemma lem2329802 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2329803 : term321 = term286.
Proof. exact (MK_COMB (@lem2329801) (@lem2329802)). Qed.
Lemma lem2329805 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329806 : term286 = term86.
Proof. exact (@lem2329805 term112). Qed.
Lemma lem2329807 : term321 = term86.
Proof. exact (TRANS (@lem2329803) (@lem2329806)). Qed.
Lemma lem2329809 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329810 : term156 = term157.
Proof. exact (@lem2329809 term112 term112). Qed.
Lemma lem2329811 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329812 : term159 = term112.
Proof. exact (EQ_MP (@lem2329811) (@lem940073)). Qed.
Lemma lem2329813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329814 : term157 = term111.
Proof. exact (MK_COMB (@lem2329813) (@lem2329812)). Qed.
Lemma lem2329815 : term156 = term111.
Proof. exact (TRANS (@lem2329810) (@lem2329814)). Qed.
Lemma lem2329816 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2329817 : term322 = term286.
Proof. exact (MK_COMB (@lem2329816) (@lem2329815)). Qed.
Lemma lem2329819 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329820 : term286 = term86.
Proof. exact (@lem2329819 term112). Qed.
Lemma lem2329821 : term322 = term86.
Proof. exact (TRANS (@lem2329817) (@lem2329820)). Qed.
Lemma lem2329822 : term86 = term322.
Proof. exact (SYM (@lem2329821)). Qed.
Lemma lem2329823 : term321 = term322.
Proof. exact (TRANS (@lem2329807) (@lem2329822)). Qed.
Lemma lem2329824 : term311 = term145.
Proof. exact (@lem2329774 (@lem2329823)). Qed.
Lemma lem2329825 : term310 = term145.
Proof. exact (TRANS (@lem2329740) (@lem2329824)). Qed.
Lemma lem2329827 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2329828 : term145 = term86.
Proof. exact (@lem2329827 term86). Qed.
Lemma lem2329829 : term310 = term86.
Proof. exact (TRANS (@lem2329825) (@lem2329828)). Qed.
Lemma lem2329830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2329831 : term323 = term320.
Proof. exact (MK_COMB (@lem2329830) (@lem2329829)). Qed.
Lemma lem2329832 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2329833 (n : nat) : (term330 n) = (term285 n).
Proof. exact (MK_COMB (@lem2329831) (@lem2329832 n)). Qed.
Lemma lem2329834 (n : nat) : (term458 n) = (term285 n).
Proof. exact (TRANS (@lem2329731 n) (@lem2329833 n)). Qed.
Lemma lem2329835 (n : nat) : (term285 n) = term86.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2329836 (n : nat) : (term458 n) = term86.
Proof. exact (TRANS (@lem2329834 n) (@lem2329835 n)). Qed.
Lemma lem2329837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2329838 (n : nat) : (term459 n) = term326.
Proof. exact (MK_COMB (@lem2329837) (@lem2329836 n)). Qed.
Lemma lem2329839 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem2329840 (n : nat) : (term457 n) = term332.
Proof. exact (MK_COMB (@lem2329838 n) (@lem2329839)). Qed.
Lemma lem2329841 (n : nat) : (term456 n) = term332.
Proof. exact (TRANS (@lem2329730 n) (@lem2329840 n)). Qed.
Lemma lem2329842 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2329843 (n : nat) : (term456 n) = term147.
Proof. exact (TRANS (@lem2329841 n) (@lem2329842)). Qed.
Lemma lem2329844 (n : nat) (x : int) : (term469 x n) = (term489 x).
Proof. exact (MK_COMB (@lem2329729 x) (@lem2329843 n)). Qed.
Lemma lem2329845 (n : nat) (x : int) : (term468 x n) = (term489 x).
Proof. exact (TRANS (@lem2329609 x n) (@lem2329844 n x)). Qed.
Lemma lem2329846 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2329847 (n : nat) (x : int) : (term490 x n) = (term491 x).
Proof. exact (MK_COMB (@lem2329846) (@lem2329845 n x)). Qed.
Lemma lem2329848 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329849 (n : nat) (x : int) : (term467 x n) = (term492 x).
Proof. exact (MK_COMB (@lem2329847 n x) (@lem2329848)). Qed.
Lemma lem2329850 (x : int) (n : nat) (h1 : term461 x n) : term492 x.
Proof. exact (EQ_MP (@lem2329849 n x) (@lem2329608 x n h1)). Qed.
Lemma lem2329852 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2329853 : term274 = term275.
Proof. exact (@lem2329852 term86 term111). Qed.
Lemma lem2329855 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329856 : term111 = term185.
Proof. exact (@lem2329855 term112). Qed.
Lemma lem2329858 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329859 : term86 = term145.
Proof. exact (@lem2329858 (NUMERAL 0)). Qed.
Lemma lem2329860 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329861 : term276 = term277.
Proof. exact (MK_COMB (@lem2329860) (@lem2329859)). Qed.
Lemma lem2329862 : term275 = term278.
Proof. exact (MK_COMB (@lem2329861) (@lem2329856)). Qed.
Lemma lem2329863 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2329865 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329866 : term275 = term281.
Proof. exact (@lem2329865 (NUMERAL 0) term112). Qed.
Lemma lem2329867 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329868 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329869 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329868 h1) (fun h1 : term281 = True => @lem2329867)). Qed.
Lemma lem2329870 : term281 = True.
Proof. exact (EQ_MP (@lem2329869) (@lem2329867)). Qed.
Lemma lem2329871 : term275 = True.
Proof. exact (TRANS (@lem2329866) (@lem2329870)). Qed.
Lemma lem2329872 : True = term275.
Proof. exact (SYM (@lem2329871)). Qed.
Lemma lem2329873 : term275.
Proof. exact (EQ_MP (@lem2329872) (@lem0)). Qed.
Lemma lem2329874 : term283.
Proof. exact (@lem2329863 (@lem2329873)). Qed.
Lemma lem2329876 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329877 : term275 = term281.
Proof. exact (@lem2329876 (NUMERAL 0) term112). Qed.
Lemma lem2329878 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329879 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329880 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329879 h1) (fun h1 : term281 = True => @lem2329878)). Qed.
Lemma lem2329881 : term281 = True.
Proof. exact (EQ_MP (@lem2329880) (@lem2329878)). Qed.
Lemma lem2329882 : term275 = True.
Proof. exact (TRANS (@lem2329877) (@lem2329881)). Qed.
Lemma lem2329883 : True = term275.
Proof. exact (SYM (@lem2329882)). Qed.
Lemma lem2329884 : term275.
Proof. exact (EQ_MP (@lem2329883) (@lem0)). Qed.
Lemma lem2329885 : term278 = term284.
Proof. exact (@lem2329874 (@lem2329884)). Qed.
Lemma lem2329887 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329888 : term156 = term157.
Proof. exact (@lem2329887 term112 term112). Qed.
Lemma lem2329889 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329890 : term159 = term112.
Proof. exact (EQ_MP (@lem2329889) (@lem940073)). Qed.
Lemma lem2329891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329892 : term157 = term111.
Proof. exact (MK_COMB (@lem2329891) (@lem2329890)). Qed.
Lemma lem2329893 : term156 = term111.
Proof. exact (TRANS (@lem2329888) (@lem2329892)). Qed.
Lemma lem2329895 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329896 : term286 = term86.
Proof. exact (@lem2329895 term112). Qed.
Lemma lem2329897 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329898 : term287 = term276.
Proof. exact (MK_COMB (@lem2329897) (@lem2329896)). Qed.
Lemma lem2329899 : term284 = term275.
Proof. exact (MK_COMB (@lem2329898) (@lem2329893)). Qed.
Lemma lem2329901 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329902 : term275 = term281.
Proof. exact (@lem2329901 (NUMERAL 0) term112). Qed.
Lemma lem2329903 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329904 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329905 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329904 h1) (fun h1 : term281 = True => @lem2329903)). Qed.
Lemma lem2329906 : term281 = True.
Proof. exact (EQ_MP (@lem2329905) (@lem2329903)). Qed.
Lemma lem2329907 : term275 = True.
Proof. exact (TRANS (@lem2329902) (@lem2329906)). Qed.
Lemma lem2329908 : term284 = True.
Proof. exact (TRANS (@lem2329899) (@lem2329907)). Qed.
Lemma lem2329909 : term278 = True.
Proof. exact (TRANS (@lem2329885) (@lem2329908)). Qed.
Lemma lem2329910 : term275 = True.
Proof. exact (TRANS (@lem2329862) (@lem2329909)). Qed.
Lemma lem2329911 : term274 = True.
Proof. exact (TRANS (@lem2329853) (@lem2329910)). Qed.
Lemma lem2329912 : True = term274.
Proof. exact (SYM (@lem2329911)). Qed.
Lemma lem2329913 : term274.
Proof. exact (EQ_MP (@lem2329912) (@lem0)). Qed.
Lemma lem2329914 (x : int) (n : nat) (h1 : term461 x n) : term493 x.
Proof. exact (conj (@lem2329913) (@lem2329850 x n h1)). Qed.
Lemma lem2329916 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2329917 (x : int) : term494 x.
Proof. exact (@lem2329916 term111 (term489 x)). Qed.
Lemma lem2329918 (x : int) (n : nat) (h1 : term461 x n) : term495 x.
Proof. exact (@lem2329917 x (@lem2329914 x n h1)). Qed.
Lemma lem2329919 (x : int) : (term496 x) = (term489 x).
Proof. exact (@lem1982733 (term489 x)). Qed.
Lemma lem2329920 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2329921 (x : int) : (term497 x) = (term491 x).
Proof. exact (MK_COMB (@lem2329920) (@lem2329919 x)). Qed.
Lemma lem2329922 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329923 (x : int) : (term495 x) = (term492 x).
Proof. exact (MK_COMB (@lem2329921 x) (@lem2329922)). Qed.
Lemma lem2329924 (x : int) (n : nat) (h1 : term461 x n) : term492 x.
Proof. exact (EQ_MP (@lem2329923 x) (@lem2329918 x n h1)). Qed.
Lemma lem2329926 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2329927 : term274 = term275.
Proof. exact (@lem2329926 term86 term111). Qed.
Lemma lem2329929 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329930 : term111 = term185.
Proof. exact (@lem2329929 term112). Qed.
Lemma lem2329932 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2329933 : term86 = term145.
Proof. exact (@lem2329932 (NUMERAL 0)). Qed.
Lemma lem2329934 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329935 : term276 = term277.
Proof. exact (MK_COMB (@lem2329934) (@lem2329933)). Qed.
Lemma lem2329936 : term275 = term278.
Proof. exact (MK_COMB (@lem2329935) (@lem2329930)). Qed.
Lemma lem2329937 : term279.
Proof. exact (@lem1980255 term86 term111 term111 term111). Qed.
Lemma lem2329939 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329940 : term275 = term281.
Proof. exact (@lem2329939 (NUMERAL 0) term112). Qed.
Lemma lem2329941 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329942 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329943 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329942 h1) (fun h1 : term281 = True => @lem2329941)). Qed.
Lemma lem2329944 : term281 = True.
Proof. exact (EQ_MP (@lem2329943) (@lem2329941)). Qed.
Lemma lem2329945 : term275 = True.
Proof. exact (TRANS (@lem2329940) (@lem2329944)). Qed.
Lemma lem2329946 : True = term275.
Proof. exact (SYM (@lem2329945)). Qed.
Lemma lem2329947 : term275.
Proof. exact (EQ_MP (@lem2329946) (@lem0)). Qed.
Lemma lem2329948 : term283.
Proof. exact (@lem2329937 (@lem2329947)). Qed.
Lemma lem2329950 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329951 : term275 = term281.
Proof. exact (@lem2329950 (NUMERAL 0) term112). Qed.
Lemma lem2329952 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329953 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329954 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329953 h1) (fun h1 : term281 = True => @lem2329952)). Qed.
Lemma lem2329955 : term281 = True.
Proof. exact (EQ_MP (@lem2329954) (@lem2329952)). Qed.
Lemma lem2329956 : term275 = True.
Proof. exact (TRANS (@lem2329951) (@lem2329955)). Qed.
Lemma lem2329957 : True = term275.
Proof. exact (SYM (@lem2329956)). Qed.
Lemma lem2329958 : term275.
Proof. exact (EQ_MP (@lem2329957) (@lem0)). Qed.
Lemma lem2329959 : term278 = term284.
Proof. exact (@lem2329948 (@lem2329958)). Qed.
Lemma lem2329961 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2329962 : term156 = term157.
Proof. exact (@lem2329961 term112 term112). Qed.
Lemma lem2329963 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2329964 : term159 = term112.
Proof. exact (EQ_MP (@lem2329963) (@lem940073)). Qed.
Lemma lem2329965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2329966 : term157 = term111.
Proof. exact (MK_COMB (@lem2329965) (@lem2329964)). Qed.
Lemma lem2329967 : term156 = term111.
Proof. exact (TRANS (@lem2329962) (@lem2329966)). Qed.
Lemma lem2329969 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2329970 : term286 = term86.
Proof. exact (@lem2329969 term112). Qed.
Lemma lem2329971 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2329972 : term287 = term276.
Proof. exact (MK_COMB (@lem2329971) (@lem2329970)). Qed.
Lemma lem2329973 : term284 = term275.
Proof. exact (MK_COMB (@lem2329972) (@lem2329967)). Qed.
Lemma lem2329975 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2329976 : term275 = term281.
Proof. exact (@lem2329975 (NUMERAL 0) term112). Qed.
Lemma lem2329977 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2329978 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2329979 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2329978 h1) (fun h1 : term281 = True => @lem2329977)). Qed.
Lemma lem2329980 : term281 = True.
Proof. exact (EQ_MP (@lem2329979) (@lem2329977)). Qed.
Lemma lem2329981 : term275 = True.
Proof. exact (TRANS (@lem2329976) (@lem2329980)). Qed.
Lemma lem2329982 : term284 = True.
Proof. exact (TRANS (@lem2329973) (@lem2329981)). Qed.
Lemma lem2329983 : term278 = True.
Proof. exact (TRANS (@lem2329959) (@lem2329982)). Qed.
Lemma lem2329984 : term275 = True.
Proof. exact (TRANS (@lem2329936) (@lem2329983)). Qed.
Lemma lem2329985 : term274 = True.
Proof. exact (TRANS (@lem2329927) (@lem2329984)). Qed.
Lemma lem2329986 : True = term274.
Proof. exact (SYM (@lem2329985)). Qed.
Lemma lem2329987 : term274.
Proof. exact (EQ_MP (@lem2329986) (@lem0)). Qed.
Lemma lem2329988 (n : nat) : term498 n.
Proof. exact (conj (@lem2329987) (@lem2329516 n)). Qed.
Lemma lem2329990 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2329991 (n : nat) : term499 n.
Proof. exact (@lem2329990 term111 (real_of_num n)). Qed.
Lemma lem2329992 (n : nat) : term500 n.
Proof. exact (@lem2329991 n (@lem2329988 n)). Qed.
Lemma lem2329993 (n : nat) : (term188 n) = (real_of_num n).
Proof. exact (@lem1982733 (real_of_num n)). Qed.
Lemma lem2329994 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2329995 (n : nat) : (term501 n) = (term502 n).
Proof. exact (MK_COMB (@lem2329994) (@lem2329993 n)). Qed.
Lemma lem2329996 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2329997 (n : nat) : (term500 n) = (term462 n).
Proof. exact (MK_COMB (@lem2329995 n) (@lem2329996)). Qed.
Lemma lem2329998 (n : nat) : term462 n.
Proof. exact (EQ_MP (@lem2329997 n) (@lem2329992 n)). Qed.
Lemma lem2330000 (y : real) : term294 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2330001 (x : int) (n : nat) : term367 x n.
Proof. exact (@lem2330000 (term189 x n)). Qed.
Lemma lem2330002 (x : int) (n : nat) (h1 : term461 x n) : term368 x n.
Proof. exact (@lem2330001 x n (@lem2329515 x n h1)). Qed.
Lemma lem2330003 (x : int) (n : nat) (h1 : term461 x n) : term369 x n.
Proof. exact (@lem2330002 x n h1 term147). Qed.
Lemma lem2330004 (x : int) (n : nat) : (term369 x n) = ((term370 x n) = term86).
Proof. exact (eq_refl (term369 x n)). Qed.
Lemma lem2330005 (x : int) (n : nat) (h1 : term461 x n) : (term370 x n) = term86.
Proof. exact (EQ_MP (@lem2330004 x n) (@lem2330003 x n h1)). Qed.
Lemma lem2330012 (x : int) (n : nat) : (term370 x n) = (term371 x n).
Proof. exact (@lem1982781 (real_of_int x) term147 (real_of_num n)). Qed.
Lemma lem2330013 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2330014 (x : int) (n : nat) : (term372 x n) = (term373 x n).
Proof. exact (MK_COMB (@lem2330013) (@lem2330012 x n)). Qed.
Lemma lem2330015 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2330016 (x : int) (n : nat) : ((term370 x n) = term86) = ((term371 x n) = term86).
Proof. exact (MK_COMB (@lem2330014 x n) (@lem2330015)). Qed.
Lemma lem2330017 (x : int) (n : nat) (h1 : term461 x n) : (term371 x n) = term86.
Proof. exact (EQ_MP (@lem2330016 x n) (@lem2330005 x n h1)). Qed.
Lemma lem2330018 (x : int) (n : nat) (h1 : term461 x n) : term503 x n.
Proof. exact (conj (@lem2330017 x n h1) (@lem2329998 n)). Qed.
Lemma lem2330020 (x : real) (y : real) : term300 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2330021 (x : int) (n : nat) : term504 x n.
Proof. exact (@lem2330020 (term371 x n) (real_of_num n)). Qed.
Lemma lem2330022 (x : int) (n : nat) (h1 : term461 x n) : term505 x n.
Proof. exact (@lem2330021 x n (@lem2330018 x n h1)). Qed.
Lemma lem2330023 (x : int) (n : nat) : (term506 x n) = (term507 x n).
Proof. exact (@lem1982755 (term211 x) (term173 n) (real_of_num n)). Qed.
Lemma lem2330024 (n : nat) : (term329 n) = (term330 n).
Proof. exact (@lem1982713 term147 (real_of_num n)). Qed.
Lemma lem2330026 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2330027 : term111 = term185.
Proof. exact (@lem2330026 term112). Qed.
Lemma lem2330029 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2330030 : term147 = term148.
Proof. exact (@lem2330029 term112). Qed.
Lemma lem2330031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2330032 : term308 = term309.
Proof. exact (MK_COMB (@lem2330031) (@lem2330030)). Qed.
Lemma lem2330033 : term310 = term311.
Proof. exact (MK_COMB (@lem2330032) (@lem2330027)). Qed.
Lemma lem2330034 : term312.
Proof. exact (@lem1981473 term147 term111 term111 term111 term86 term111). Qed.
Lemma lem2330036 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330037 : term275 = term281.
Proof. exact (@lem2330036 (NUMERAL 0) term112). Qed.
Lemma lem2330038 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330039 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330040 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330039 h1) (fun h1 : term281 = True => @lem2330038)). Qed.
Lemma lem2330041 : term281 = True.
Proof. exact (EQ_MP (@lem2330040) (@lem2330038)). Qed.
Lemma lem2330042 : term275 = True.
Proof. exact (TRANS (@lem2330037) (@lem2330041)). Qed.
Lemma lem2330043 : True = term275.
Proof. exact (SYM (@lem2330042)). Qed.
Lemma lem2330044 : term275.
Proof. exact (EQ_MP (@lem2330043) (@lem0)). Qed.
Lemma lem2330045 : term313.
Proof. exact (@lem2330034 (@lem2330044)). Qed.
Lemma lem2330047 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330048 : term275 = term281.
Proof. exact (@lem2330047 (NUMERAL 0) term112). Qed.
Lemma lem2330049 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330050 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330051 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330050 h1) (fun h1 : term281 = True => @lem2330049)). Qed.
Lemma lem2330052 : term281 = True.
Proof. exact (EQ_MP (@lem2330051) (@lem2330049)). Qed.
Lemma lem2330053 : term275 = True.
Proof. exact (TRANS (@lem2330048) (@lem2330052)). Qed.
Lemma lem2330054 : True = term275.
Proof. exact (SYM (@lem2330053)). Qed.
Lemma lem2330055 : term275.
Proof. exact (EQ_MP (@lem2330054) (@lem0)). Qed.
Lemma lem2330056 : term314.
Proof. exact (@lem2330045 (@lem2330055)). Qed.
Lemma lem2330058 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330059 : term275 = term281.
Proof. exact (@lem2330058 (NUMERAL 0) term112). Qed.
Lemma lem2330060 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330061 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330062 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330061 h1) (fun h1 : term281 = True => @lem2330060)). Qed.
Lemma lem2330063 : term281 = True.
Proof. exact (EQ_MP (@lem2330062) (@lem2330060)). Qed.
Lemma lem2330064 : term275 = True.
Proof. exact (TRANS (@lem2330059) (@lem2330063)). Qed.
Lemma lem2330065 : True = term275.
Proof. exact (SYM (@lem2330064)). Qed.
Lemma lem2330066 : term275.
Proof. exact (EQ_MP (@lem2330065) (@lem0)). Qed.
Lemma lem2330067 : term315.
Proof. exact (@lem2330056 (@lem2330066)). Qed.
Lemma lem2330069 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2330070 : term156 = term157.
Proof. exact (@lem2330069 term112 term112). Qed.
Lemma lem2330071 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2330072 : term159 = term112.
Proof. exact (EQ_MP (@lem2330071) (@lem940073)). Qed.
Lemma lem2330073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330074 : term157 = term111.
Proof. exact (MK_COMB (@lem2330073) (@lem2330072)). Qed.
Lemma lem2330075 : term156 = term111.
Proof. exact (TRANS (@lem2330070) (@lem2330074)). Qed.
Lemma lem2330077 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2330078 : term199 = term204.
Proof. exact (@lem2330077 term112 term112). Qed.
Lemma lem2330079 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2330080 : term159 = term112.
Proof. exact (EQ_MP (@lem2330079) (@lem940073)). Qed.
Lemma lem2330081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330082 : term157 = term111.
Proof. exact (MK_COMB (@lem2330081) (@lem2330080)). Qed.
Lemma lem2330083 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2330084 : term204 = term147.
Proof. exact (MK_COMB (@lem2330083) (@lem2330082)). Qed.
Lemma lem2330085 : term199 = term147.
Proof. exact (TRANS (@lem2330078) (@lem2330084)). Qed.
Lemma lem2330086 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2330087 : term316 = term308.
Proof. exact (MK_COMB (@lem2330086) (@lem2330085)). Qed.
Lemma lem2330088 : term317 = term310.
Proof. exact (MK_COMB (@lem2330087) (@lem2330075)). Qed.
Lemma lem2330090 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2330091 : term310 = term86.
Proof. exact (@lem2330090 term112). Qed.
Lemma lem2330092 : term317 = term86.
Proof. exact (TRANS (@lem2330088) (@lem2330091)). Qed.
Lemma lem2330093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2330094 : term319 = term320.
Proof. exact (MK_COMB (@lem2330093) (@lem2330092)). Qed.
Lemma lem2330095 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2330096 : term321 = term286.
Proof. exact (MK_COMB (@lem2330094) (@lem2330095)). Qed.
Lemma lem2330098 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2330099 : term286 = term86.
Proof. exact (@lem2330098 term112). Qed.
Lemma lem2330100 : term321 = term86.
Proof. exact (TRANS (@lem2330096) (@lem2330099)). Qed.
Lemma lem2330102 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2330103 : term156 = term157.
Proof. exact (@lem2330102 term112 term112). Qed.
Lemma lem2330104 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2330105 : term159 = term112.
Proof. exact (EQ_MP (@lem2330104) (@lem940073)). Qed.
Lemma lem2330106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330107 : term157 = term111.
Proof. exact (MK_COMB (@lem2330106) (@lem2330105)). Qed.
Lemma lem2330108 : term156 = term111.
Proof. exact (TRANS (@lem2330103) (@lem2330107)). Qed.
Lemma lem2330109 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2330110 : term322 = term286.
Proof. exact (MK_COMB (@lem2330109) (@lem2330108)). Qed.
Lemma lem2330112 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2330113 : term286 = term86.
Proof. exact (@lem2330112 term112). Qed.
Lemma lem2330114 : term322 = term86.
Proof. exact (TRANS (@lem2330110) (@lem2330113)). Qed.
Lemma lem2330115 : term86 = term322.
Proof. exact (SYM (@lem2330114)). Qed.
Lemma lem2330116 : term321 = term322.
Proof. exact (TRANS (@lem2330100) (@lem2330115)). Qed.
Lemma lem2330117 : term311 = term145.
Proof. exact (@lem2330067 (@lem2330116)). Qed.
Lemma lem2330118 : term310 = term145.
Proof. exact (TRANS (@lem2330033) (@lem2330117)). Qed.
Lemma lem2330120 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2330121 : term145 = term86.
Proof. exact (@lem2330120 term86). Qed.
Lemma lem2330122 : term310 = term86.
Proof. exact (TRANS (@lem2330118) (@lem2330121)). Qed.
Lemma lem2330123 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2330124 : term323 = term320.
Proof. exact (MK_COMB (@lem2330123) (@lem2330122)). Qed.
Lemma lem2330125 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2330126 (n : nat) : (term330 n) = (term285 n).
Proof. exact (MK_COMB (@lem2330124) (@lem2330125 n)). Qed.
Lemma lem2330127 (n : nat) : (term329 n) = (term285 n).
Proof. exact (TRANS (@lem2330024 n) (@lem2330126 n)). Qed.
Lemma lem2330128 (n : nat) : (term285 n) = term86.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2330129 (n : nat) : (term329 n) = term86.
Proof. exact (TRANS (@lem2330127 n) (@lem2330128 n)). Qed.
Lemma lem2330130 (x : int) : (term207 x) = (term207 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem2330131 (n : nat) (x : int) : (term507 x n) = (term508 x).
Proof. exact (MK_COMB (@lem2330130 x) (@lem2330129 n)). Qed.
Lemma lem2330132 (n : nat) (x : int) : (term506 x n) = (term508 x).
Proof. exact (TRANS (@lem2330023 x n) (@lem2330131 n x)). Qed.
Lemma lem2330133 (x : int) : (term508 x) = (term211 x).
Proof. exact (@lem1982723 (term211 x)). Qed.
Lemma lem2330134 (n : nat) (x : int) : (term506 x n) = (term211 x).
Proof. exact (TRANS (@lem2330132 n x) (@lem2330133 x)). Qed.
Lemma lem2330135 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2330136 (n : nat) (x : int) : (term509 x n) = (term510 x).
Proof. exact (MK_COMB (@lem2330135) (@lem2330134 n x)). Qed.
Lemma lem2330137 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2330138 (n : nat) (x : int) : (term505 x n) = (term511 x).
Proof. exact (MK_COMB (@lem2330136 n x) (@lem2330137)). Qed.
Lemma lem2330139 (x : int) (n : nat) (h1 : term461 x n) : term511 x.
Proof. exact (EQ_MP (@lem2330138 n x) (@lem2330022 x n h1)). Qed.
Lemma lem2330141 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2330142 : term348 = term349.
Proof. exact (@lem2330141 term86 term350). Qed.
Lemma lem2330144 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2330145 : term350 = term351.
Proof. exact (@lem2330144 term352). Qed.
Lemma lem2330147 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2330148 : term86 = term145.
Proof. exact (@lem2330147 (NUMERAL 0)). Qed.
Lemma lem2330149 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2330150 : term276 = term277.
Proof. exact (MK_COMB (@lem2330149) (@lem2330148)). Qed.
Lemma lem2330151 : term349 = term353.
Proof. exact (MK_COMB (@lem2330150) (@lem2330145)). Qed.
Lemma lem2330152 : term354.
Proof. exact (@lem1980255 term86 term111 term350 term111). Qed.
Lemma lem2330154 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330155 : term275 = term281.
Proof. exact (@lem2330154 (NUMERAL 0) term112). Qed.
Lemma lem2330156 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330157 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330158 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330157 h1) (fun h1 : term281 = True => @lem2330156)). Qed.
Lemma lem2330159 : term281 = True.
Proof. exact (EQ_MP (@lem2330158) (@lem2330156)). Qed.
Lemma lem2330160 : term275 = True.
Proof. exact (TRANS (@lem2330155) (@lem2330159)). Qed.
Lemma lem2330161 : True = term275.
Proof. exact (SYM (@lem2330160)). Qed.
Lemma lem2330162 : term275.
Proof. exact (EQ_MP (@lem2330161) (@lem0)). Qed.
Lemma lem2330163 : term355.
Proof. exact (@lem2330152 (@lem2330162)). Qed.
Lemma lem2330165 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330166 : term275 = term281.
Proof. exact (@lem2330165 (NUMERAL 0) term112). Qed.
Lemma lem2330167 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330168 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330169 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330168 h1) (fun h1 : term281 = True => @lem2330167)). Qed.
Lemma lem2330170 : term281 = True.
Proof. exact (EQ_MP (@lem2330169) (@lem2330167)). Qed.
Lemma lem2330171 : term275 = True.
Proof. exact (TRANS (@lem2330166) (@lem2330170)). Qed.
Lemma lem2330172 : True = term275.
Proof. exact (SYM (@lem2330171)). Qed.
Lemma lem2330173 : term275.
Proof. exact (EQ_MP (@lem2330172) (@lem0)). Qed.
Lemma lem2330174 : term353 = term356.
Proof. exact (@lem2330163 (@lem2330173)). Qed.
Lemma lem2330176 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2330177 : term357 = term358.
Proof. exact (@lem2330176 term352 term112). Qed.
Lemma lem2330178 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2330179 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2330180 : term361 = term352.
Proof. exact (EQ_MP (@lem2330179) (@lem2330178)). Qed.
Lemma lem2330181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330182 : term358 = term350.
Proof. exact (MK_COMB (@lem2330181) (@lem2330180)). Qed.
Lemma lem2330183 : term357 = term350.
Proof. exact (TRANS (@lem2330177) (@lem2330182)). Qed.
Lemma lem2330185 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2330186 : term286 = term86.
Proof. exact (@lem2330185 term112). Qed.
Lemma lem2330187 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2330188 : term287 = term276.
Proof. exact (MK_COMB (@lem2330187) (@lem2330186)). Qed.
Lemma lem2330189 : term356 = term349.
Proof. exact (MK_COMB (@lem2330188) (@lem2330183)). Qed.
Lemma lem2330191 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330192 : term349 = term362.
Proof. exact (@lem2330191 (NUMERAL 0) term352). Qed.
Lemma lem2330193 : term363 = term360.
Proof. exact (@lem912803). Qed.
Lemma lem2330194 (h1 : term363 = term360) : term362 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term360 h1). Qed.
Lemma lem2330195 : (term363 = term360) = (term362 = True).
Proof. exact (prop_ext (fun h1 : term363 = term360 => @lem2330194 h1) (fun h1 : term362 = True => @lem2330193)). Qed.
Lemma lem2330196 : term362 = True.
Proof. exact (EQ_MP (@lem2330195) (@lem2330193)). Qed.
Lemma lem2330197 : term349 = True.
Proof. exact (TRANS (@lem2330192) (@lem2330196)). Qed.
Lemma lem2330198 : term356 = True.
Proof. exact (TRANS (@lem2330189) (@lem2330197)). Qed.
Lemma lem2330199 : term353 = True.
Proof. exact (TRANS (@lem2330174) (@lem2330198)). Qed.
Lemma lem2330200 : term349 = True.
Proof. exact (TRANS (@lem2330151) (@lem2330199)). Qed.
Lemma lem2330201 : term348 = True.
Proof. exact (TRANS (@lem2330142) (@lem2330200)). Qed.
Lemma lem2330202 : True = term348.
Proof. exact (SYM (@lem2330201)). Qed.
Lemma lem2330203 : term348.
Proof. exact (EQ_MP (@lem2330202) (@lem0)). Qed.
Lemma lem2330204 (x : int) (n : nat) (h1 : term461 x n) : term512 x.
Proof. exact (conj (@lem2330203) (@lem2330139 x n h1)). Qed.
Lemma lem2330206 (x : real) (y : real) : term289 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2330207 (x : int) : term513 x.
Proof. exact (@lem2330206 term350 (term211 x)). Qed.
Lemma lem2330208 (x : int) (n : nat) (h1 : term461 x n) : term514 x.
Proof. exact (@lem2330207 x (@lem2330204 x n h1)). Qed.
Lemma lem2330209 (x : int) : (term515 x) = (term516 x).
Proof. exact (@lem1982749 term350 term147 (real_of_int x)). Qed.
Lemma lem2330211 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2330212 : term147 = term148.
Proof. exact (@lem2330211 term112). Qed.
Lemma lem2330214 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2330215 : term350 = term351.
Proof. exact (@lem2330214 term352). Qed.
Lemma lem2330216 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2330217 : term483 = term517.
Proof. exact (MK_COMB (@lem2330216) (@lem2330215)). Qed.
Lemma lem2330218 : term518 = term519.
Proof. exact (MK_COMB (@lem2330217) (@lem2330212)). Qed.
Lemma lem2330219 : term519 = term520.
Proof. exact (@lem1981613 term350 term147 term111 term111). Qed.
Lemma lem2330221 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2330222 : term156 = term157.
Proof. exact (@lem2330221 term112 term112). Qed.
Lemma lem2330223 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2330224 : term159 = term112.
Proof. exact (EQ_MP (@lem2330223) (@lem940073)). Qed.
Lemma lem2330225 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330226 : term157 = term111.
Proof. exact (MK_COMB (@lem2330225) (@lem2330224)). Qed.
Lemma lem2330227 : term156 = term111.
Proof. exact (TRANS (@lem2330222) (@lem2330226)). Qed.
Lemma lem2330229 (m : nat) (n : nat) : (term521 m n) = (term203 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2330230 : term518 = term397.
Proof. exact (@lem2330229 term352 term112). Qed.
Lemma lem2330231 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2330232 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2330233 : term361 = term352.
Proof. exact (EQ_MP (@lem2330232) (@lem2330231)). Qed.
Lemma lem2330234 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330235 : term358 = term350.
Proof. exact (MK_COMB (@lem2330234) (@lem2330233)). Qed.
Lemma lem2330236 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2330237 : term397 = term384.
Proof. exact (MK_COMB (@lem2330236) (@lem2330235)). Qed.
Lemma lem2330238 : term518 = term384.
Proof. exact (TRANS (@lem2330230) (@lem2330237)). Qed.
Lemma lem2330239 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2330240 : term522 = term523.
Proof. exact (MK_COMB (@lem2330239) (@lem2330238)). Qed.
Lemma lem2330241 : term520 = term399.
Proof. exact (MK_COMB (@lem2330240) (@lem2330227)). Qed.
Lemma lem2330242 : term519 = term399.
Proof. exact (TRANS (@lem2330219) (@lem2330241)). Qed.
Lemma lem2330243 : term518 = term399.
Proof. exact (TRANS (@lem2330218) (@lem2330242)). Qed.
Lemma lem2330245 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2330246 : term399 = term384.
Proof. exact (@lem2330245 term384). Qed.
Lemma lem2330247 : term518 = term384.
Proof. exact (TRANS (@lem2330243) (@lem2330246)). Qed.
Lemma lem2330248 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2330249 : term524 = term394.
Proof. exact (MK_COMB (@lem2330248) (@lem2330247)). Qed.
Lemma lem2330250 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2330251 (x : int) : (term516 x) = (term401 x).
Proof. exact (MK_COMB (@lem2330249) (@lem2330250 x)). Qed.
Lemma lem2330252 (x : int) : (term515 x) = (term401 x).
Proof. exact (TRANS (@lem2330209 x) (@lem2330251 x)). Qed.
Lemma lem2330253 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2330254 (x : int) : (term525 x) = (term526 x).
Proof. exact (MK_COMB (@lem2330253) (@lem2330252 x)). Qed.
Lemma lem2330255 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2330256 (x : int) : (term514 x) = (term527 x).
Proof. exact (MK_COMB (@lem2330254 x) (@lem2330255)). Qed.
Lemma lem2330257 (x : int) (n : nat) (h1 : term461 x n) : term527 x.
Proof. exact (EQ_MP (@lem2330256 x) (@lem2330208 x n h1)). Qed.
Lemma lem2330258 (x : int) (n : nat) (h1 : term461 x n) : term528 x.
Proof. exact (conj (@lem2330257 x n h1) (@lem2329924 x n h1)). Qed.
Lemma lem2330260 (x : real) (y : real) : term414 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2330261 (x : int) : term529 x.
Proof. exact (@lem2330260 (term401 x) (term489 x)). Qed.
Lemma lem2330262 (x : int) (n : nat) (h1 : term461 x n) : term530 x.
Proof. exact (@lem2330261 x (@lem2330258 x n h1)). Qed.
Lemma lem2330263 (x : int) : (term531 x) = (term419 x).
Proof. exact (@lem1982763 (term401 x) (term416 x) term147). Qed.
Lemma lem2330264 (x : int) : (term420 x) = (term421 x).
Proof. exact (@lem1982711 term384 term350 (real_of_int x)). Qed.
Lemma lem2330266 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2330267 : term350 = term351.
Proof. exact (@lem2330266 term352). Qed.
Lemma lem2330269 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2330270 : term384 = term399.
Proof. exact (@lem2330269 term352). Qed.
Lemma lem2330271 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2330272 : term422 = term423.
Proof. exact (MK_COMB (@lem2330271) (@lem2330270)). Qed.
Lemma lem2330273 : term424 = term425.
Proof. exact (MK_COMB (@lem2330272) (@lem2330267)). Qed.
Lemma lem2330274 : term426.
Proof. exact (@lem1981473 term384 term111 term350 term111 term86 term111). Qed.
Lemma lem2330276 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330277 : term275 = term281.
Proof. exact (@lem2330276 (NUMERAL 0) term112). Qed.
Lemma lem2330278 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330279 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330280 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330279 h1) (fun h1 : term281 = True => @lem2330278)). Qed.
Lemma lem2330281 : term281 = True.
Proof. exact (EQ_MP (@lem2330280) (@lem2330278)). Qed.
Lemma lem2330282 : term275 = True.
Proof. exact (TRANS (@lem2330277) (@lem2330281)). Qed.
Lemma lem2330283 : True = term275.
Proof. exact (SYM (@lem2330282)). Qed.
Lemma lem2330284 : term275.
Proof. exact (EQ_MP (@lem2330283) (@lem0)). Qed.
Lemma lem2330285 : term427.
Proof. exact (@lem2330274 (@lem2330284)). Qed.
Lemma lem2330287 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330288 : term275 = term281.
Proof. exact (@lem2330287 (NUMERAL 0) term112). Qed.
Lemma lem2330289 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330290 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330291 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330290 h1) (fun h1 : term281 = True => @lem2330289)). Qed.
Lemma lem2330292 : term281 = True.
Proof. exact (EQ_MP (@lem2330291) (@lem2330289)). Qed.
Lemma lem2330293 : term275 = True.
Proof. exact (TRANS (@lem2330288) (@lem2330292)). Qed.
Lemma lem2330294 : True = term275.
Proof. exact (SYM (@lem2330293)). Qed.
Lemma lem2330295 : term275.
Proof. exact (EQ_MP (@lem2330294) (@lem0)). Qed.
Lemma lem2330296 : term428.
Proof. exact (@lem2330285 (@lem2330295)). Qed.
Lemma lem2330298 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330299 : term275 = term281.
Proof. exact (@lem2330298 (NUMERAL 0) term112). Qed.
Lemma lem2330300 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330301 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330302 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330301 h1) (fun h1 : term281 = True => @lem2330300)). Qed.
Lemma lem2330303 : term281 = True.
Proof. exact (EQ_MP (@lem2330302) (@lem2330300)). Qed.
Lemma lem2330304 : term275 = True.
Proof. exact (TRANS (@lem2330299) (@lem2330303)). Qed.
Lemma lem2330305 : True = term275.
Proof. exact (SYM (@lem2330304)). Qed.
Lemma lem2330306 : term275.
Proof. exact (EQ_MP (@lem2330305) (@lem0)). Qed.
Lemma lem2330307 : term429.
Proof. exact (@lem2330296 (@lem2330306)). Qed.
Lemma lem2330309 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2330310 : term357 = term358.
Proof. exact (@lem2330309 term352 term112). Qed.
Lemma lem2330311 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2330312 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2330313 : term361 = term352.
Proof. exact (EQ_MP (@lem2330312) (@lem2330311)). Qed.
Lemma lem2330314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330315 : term358 = term350.
Proof. exact (MK_COMB (@lem2330314) (@lem2330313)). Qed.
Lemma lem2330316 : term357 = term350.
Proof. exact (TRANS (@lem2330310) (@lem2330315)). Qed.
Lemma lem2330318 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2330319 : term396 = term397.
Proof. exact (@lem2330318 term352 term112). Qed.
Lemma lem2330320 : term359 = term360.
Proof. exact (@lem996237 term360). Qed.
Lemma lem2330321 : (term359 = term360) = (term361 = term352).
Proof. exact (@lem1007663 term360 (BIT1 0) term360). Qed.
Lemma lem2330322 : term361 = term352.
Proof. exact (EQ_MP (@lem2330321) (@lem2330320)). Qed.
Lemma lem2330323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330324 : term358 = term350.
Proof. exact (MK_COMB (@lem2330323) (@lem2330322)). Qed.
Lemma lem2330325 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2330326 : term397 = term384.
Proof. exact (MK_COMB (@lem2330325) (@lem2330324)). Qed.
Lemma lem2330327 : term396 = term384.
Proof. exact (TRANS (@lem2330319) (@lem2330326)). Qed.
Lemma lem2330328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2330329 : term430 = term422.
Proof. exact (MK_COMB (@lem2330328) (@lem2330327)). Qed.
Lemma lem2330330 : term431 = term424.
Proof. exact (MK_COMB (@lem2330329) (@lem2330316)). Qed.
Lemma lem2330332 (m : nat) : (term318 m) = term86.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2330333 : term424 = term86.
Proof. exact (@lem2330332 term352). Qed.
Lemma lem2330334 : term431 = term86.
Proof. exact (TRANS (@lem2330330) (@lem2330333)). Qed.
Lemma lem2330335 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2330336 : term432 = term320.
Proof. exact (MK_COMB (@lem2330335) (@lem2330334)). Qed.
Lemma lem2330337 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem2330338 : term433 = term286.
Proof. exact (MK_COMB (@lem2330336) (@lem2330337)). Qed.
Lemma lem2330340 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2330341 : term286 = term86.
Proof. exact (@lem2330340 term112). Qed.
Lemma lem2330342 : term433 = term86.
Proof. exact (TRANS (@lem2330338) (@lem2330341)). Qed.
Lemma lem2330344 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2330345 : term156 = term157.
Proof. exact (@lem2330344 term112 term112). Qed.
Lemma lem2330346 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2330347 : term159 = term112.
Proof. exact (EQ_MP (@lem2330346) (@lem940073)). Qed.
Lemma lem2330348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330349 : term157 = term111.
Proof. exact (MK_COMB (@lem2330348) (@lem2330347)). Qed.
Lemma lem2330350 : term156 = term111.
Proof. exact (TRANS (@lem2330345) (@lem2330349)). Qed.
Lemma lem2330351 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem2330352 : term322 = term286.
Proof. exact (MK_COMB (@lem2330351) (@lem2330350)). Qed.
Lemma lem2330354 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2330355 : term286 = term86.
Proof. exact (@lem2330354 term112). Qed.
Lemma lem2330356 : term322 = term86.
Proof. exact (TRANS (@lem2330352) (@lem2330355)). Qed.
Lemma lem2330357 : term86 = term322.
Proof. exact (SYM (@lem2330356)). Qed.
Lemma lem2330358 : term433 = term322.
Proof. exact (TRANS (@lem2330342) (@lem2330357)). Qed.
Lemma lem2330359 : term425 = term145.
Proof. exact (@lem2330307 (@lem2330358)). Qed.
Lemma lem2330360 : term424 = term145.
Proof. exact (TRANS (@lem2330273) (@lem2330359)). Qed.
Lemma lem2330362 (x : real) : (term163 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2330363 : term145 = term86.
Proof. exact (@lem2330362 term86). Qed.
Lemma lem2330364 : term424 = term86.
Proof. exact (TRANS (@lem2330360) (@lem2330363)). Qed.
Lemma lem2330365 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2330366 : term434 = term320.
Proof. exact (MK_COMB (@lem2330365) (@lem2330364)). Qed.
Lemma lem2330367 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2330368 (x : int) : (term421 x) = (term324 x).
Proof. exact (MK_COMB (@lem2330366) (@lem2330367 x)). Qed.
Lemma lem2330369 (x : int) : (term420 x) = (term324 x).
Proof. exact (TRANS (@lem2330264 x) (@lem2330368 x)). Qed.
Lemma lem2330370 (x : int) : (term324 x) = term86.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2330371 (x : int) : (term420 x) = term86.
Proof. exact (TRANS (@lem2330369 x) (@lem2330370 x)). Qed.
Lemma lem2330372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2330373 (x : int) : (term435 x) = term326.
Proof. exact (MK_COMB (@lem2330372) (@lem2330371 x)). Qed.
Lemma lem2330374 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem2330375 (x : int) : (term419 x) = term332.
Proof. exact (MK_COMB (@lem2330373 x) (@lem2330374)). Qed.
Lemma lem2330376 (x : int) : (term531 x) = term332.
Proof. exact (TRANS (@lem2330263 x) (@lem2330375 x)). Qed.
Lemma lem2330377 : term332 = term147.
Proof. exact (@lem1982721 term147). Qed.
Lemma lem2330378 (x : int) : (term531 x) = term147.
Proof. exact (TRANS (@lem2330376 x) (@lem2330377)). Qed.
Lemma lem2330379 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2330380 (x : int) : (term532 x) = term334.
Proof. exact (MK_COMB (@lem2330379) (@lem2330378 x)). Qed.
Lemma lem2330381 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2330382 (x : int) : (term530 x) = term335.
Proof. exact (MK_COMB (@lem2330380 x) (@lem2330381)). Qed.
Lemma lem2330383 (x : int) (n : nat) (h1 : term461 x n) : term335.
Proof. exact (EQ_MP (@lem2330382 x) (@lem2330262 x n h1)). Qed.
Lemma lem2330385 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2330386 : term335 = term336.
Proof. exact (@lem2330385 term86 term147). Qed.
Lemma lem2330388 (x : nat) : (term95 x) = (term146 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2330389 : term147 = term148.
Proof. exact (@lem2330388 term112). Qed.
Lemma lem2330391 (x : nat) : (real_of_num x) = (term144 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2330392 : term86 = term145.
Proof. exact (@lem2330391 (NUMERAL 0)). Qed.
Lemma lem2330393 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2330394 : term88 = term337.
Proof. exact (MK_COMB (@lem2330393) (@lem2330392)). Qed.
Lemma lem2330395 : term336 = term338.
Proof. exact (MK_COMB (@lem2330394) (@lem2330389)). Qed.
Lemma lem2330396 : term339.
Proof. exact (@lem1980026 term86 term111 term147 term111). Qed.
Lemma lem2330398 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330399 : term275 = term281.
Proof. exact (@lem2330398 (NUMERAL 0) term112). Qed.
Lemma lem2330400 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330401 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330402 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330401 h1) (fun h1 : term281 = True => @lem2330400)). Qed.
Lemma lem2330403 : term281 = True.
Proof. exact (EQ_MP (@lem2330402) (@lem2330400)). Qed.
Lemma lem2330404 : term275 = True.
Proof. exact (TRANS (@lem2330399) (@lem2330403)). Qed.
Lemma lem2330405 : True = term275.
Proof. exact (SYM (@lem2330404)). Qed.
Lemma lem2330406 : term275.
Proof. exact (EQ_MP (@lem2330405) (@lem0)). Qed.
Lemma lem2330407 : term340.
Proof. exact (@lem2330396 (@lem2330406)). Qed.
Lemma lem2330409 (m : nat) (n : nat) : (term280 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2330410 : term275 = term281.
Proof. exact (@lem2330409 (NUMERAL 0) term112). Qed.
Lemma lem2330411 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330412 (h1 : term282 = (BIT1 0)) : term281 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2330413 : (term282 = (BIT1 0)) = (term281 = True).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330412 h1) (fun h1 : term281 = True => @lem2330411)). Qed.
Lemma lem2330414 : term281 = True.
Proof. exact (EQ_MP (@lem2330413) (@lem2330411)). Qed.
Lemma lem2330415 : term275 = True.
Proof. exact (TRANS (@lem2330410) (@lem2330414)). Qed.
Lemma lem2330416 : True = term275.
Proof. exact (SYM (@lem2330415)). Qed.
Lemma lem2330417 : term275.
Proof. exact (EQ_MP (@lem2330416) (@lem0)). Qed.
Lemma lem2330418 : term338 = term341.
Proof. exact (@lem2330407 (@lem2330417)). Qed.
Lemma lem2330420 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2330421 : term199 = term204.
Proof. exact (@lem2330420 term112 term112). Qed.
Lemma lem2330422 : (term158 = (BIT1 0)) = (term159 = term112).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2330423 : term159 = term112.
Proof. exact (EQ_MP (@lem2330422) (@lem940073)). Qed.
Lemma lem2330424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2330425 : term157 = term111.
Proof. exact (MK_COMB (@lem2330424) (@lem2330423)). Qed.
Lemma lem2330426 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2330427 : term204 = term147.
Proof. exact (MK_COMB (@lem2330426) (@lem2330425)). Qed.
Lemma lem2330428 : term199 = term147.
Proof. exact (TRANS (@lem2330421) (@lem2330427)). Qed.
Lemma lem2330430 (x : nat) : (term285 x) = term86.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2330431 : term286 = term86.
Proof. exact (@lem2330430 term112). Qed.
Lemma lem2330432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2330433 : term342 = term88.
Proof. exact (MK_COMB (@lem2330432) (@lem2330431)). Qed.
Lemma lem2330434 : term341 = term336.
Proof. exact (MK_COMB (@lem2330433) (@lem2330428)). Qed.
Lemma lem2330436 (m : nat) (n : nat) : (term343 m n) = (term344 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2330437 : term336 = term345.
Proof. exact (@lem2330436 (NUMERAL 0) term112). Qed.
Lemma lem2330438 : term282 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2330439 (h1 : term282 = (BIT1 0)) : (term112 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2330440 : (term282 = (BIT1 0)) = ((term112 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term282 = (BIT1 0) => @lem2330439 h1) (fun h1 : (term112 = (NUMERAL 0)) = False => @lem2330438)). Qed.
Lemma lem2330441 : (term112 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2330440) (@lem2330438)). Qed.
Lemma lem2330442 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2330443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2330444 : term346 = (and True).
Proof. exact (MK_COMB (@lem2330443) (@lem2330442)). Qed.
Lemma lem2330445 : term345 = (True /\ False).
Proof. exact (MK_COMB (@lem2330444) (@lem2330441)). Qed.
Lemma lem2330447 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2330448 : term345 = False.
Proof. exact (TRANS (@lem2330445) (@lem2330447)). Qed.
Lemma lem2330449 : term336 = False.
Proof. exact (TRANS (@lem2330437) (@lem2330448)). Qed.
Lemma lem2330450 : term341 = False.
Proof. exact (TRANS (@lem2330434) (@lem2330449)). Qed.
Lemma lem2330451 : term338 = False.
Proof. exact (TRANS (@lem2330418) (@lem2330450)). Qed.
Lemma lem2330452 : term336 = False.
Proof. exact (TRANS (@lem2330395) (@lem2330451)). Qed.
Lemma lem2330453 : term335 = False.
Proof. exact (TRANS (@lem2330386) (@lem2330452)). Qed.
Lemma lem2330454 (x : int) (n : nat) (h1 : term461 x n) : False.
Proof. exact (EQ_MP (@lem2330453) (@lem2330383 x n h1)). Qed.
Lemma lem2330455 (x : int) (n : nat) (h1 : term261 x n) : False.
Proof. exact (or_elim (@lem2329061 x n h1) (fun h0 : term437 x n => @lem2329510 x n h0) (fun h0 : term461 x n => @lem2330454 x n h0)). Qed.
Lemma lem2330456 (x : int) (n : nat) (h1 : term270 x n) : False.
Proof. exact (or_elim (@lem2327955 x n h1) (fun h0 : term265 x n => @lem2329060 x n h0) (fun h0 : term261 x n => @lem2330455 x n h0)). Qed.
Lemma lem2330458 (x : int) (n : nat) (h1 : term270 x n) : term270 x n.
Proof. exact (h1). Qed.
Lemma lem2330459 (x : int) (n : nat) (h1 : term270 x n) : (term270 x n) = False.
Proof. exact (prop_ext (fun h2 : term270 x n => @lem2330456 x n h1) (fun h2 : False => @lem2330458 x n h1)). Qed.
Lemma lem2330460 (x : int) (n : nat) (h1 : term270 x n) : False.
Proof. exact (EQ_MP (@lem2330459 x n h1) (@lem2330458 x n h1)). Qed.
Lemma lem2330461 (x : int) (h1 : term272 x) : term272 x.
Proof. exact (h1). Qed.
Lemma lem2330462 (x : int) (h1 : term272 x) : False.
Proof. exact (ex_elim (@lem2330461 x h1) (fun n : nat => fun h0 : term271 x n => @lem2330460 x n h0)). Qed.
Lemma lem2330463 (x : int) (h1 : term140 x) : term140 x.
Proof. exact (h1). Qed.
Lemma lem2330464 (x : int) (h1 : term140 x) : term272 x.
Proof. exact (EQ_MP (@lem2327933 x) (@lem2330463 x h1)). Qed.
Lemma lem2330465 (x : int) (h1 : term140 x) : (term272 x) = False.
Proof. exact (prop_ext (fun h2 : term272 x => @lem2330462 x h2) (fun h2 : False => @lem2330464 x h1)). Qed.
Lemma lem2330466 (x : int) (h1 : term140 x) : False.
Proof. exact (EQ_MP (@lem2330465 x h1) (@lem2330464 x h1)). Qed.
Lemma lem2330467 (x : int) : term533 x.
Proof. exact (fun h0 : term140 x => @lem2330466 x h0). Qed.
Lemma lem2330468 (x : int) : term534 x.
Proof. exact (@lem1386578 (term535 x)). Qed.
Lemma lem2330471 (x : int) : term535 x.
Proof. exact (@lem2330468 x (@lem2330467 x)). Qed.
Lemma lem2330472 (x : int) : (term138 x) = (term80 x).
Proof. exact (SYM (@lem2327407 x)). Qed.
Lemma lem2330473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2330474 (x : int) : (term535 x) = (term64 x).
Proof. exact (MK_COMB (@lem2330473) (@lem2330472 x)). Qed.
Lemma lem2330475 (x : int) : term64 x.
Proof. exact (EQ_MP (@lem2330474 x) (@lem2330471 x)). Qed.
Lemma lem2330476 (x : int) : term65 x.
Proof. exact (EQ_MP (@lem2327244 x) (@lem2330475 x)). Qed.
Lemma lem2330477 (x : int) : (term65 x) = ((term65 x) = True).
Proof. exact (@lem7 (term65 x)). Qed.
Lemma lem2330478 (x : int) : (term65 x) = True.
Proof. exact (EQ_MP (@lem2330477 x) (@lem2330476 x)). Qed.
Lemma lem2330479 (x : int) : True = (term65 x).
Proof. exact (SYM (@lem2330478 x)). Qed.
Lemma lem2330480 (x : int) : term65 x.
Proof. exact (EQ_MP (@lem2330479 x) (@lem0)). Qed.
Lemma lem2330481 (x : int) (h1 : term13 x) : term56 x.
Proof. exact (@lem2330480 x (@lem2327135 x h1)). Qed.
Lemma lem2330482 (x : int) (h1 : term13 x) : term45 x.
Proof. exact (@lem2327243 x (@lem2330481 x h1)). Qed.
Lemma lem2330483 (x : int) (h1 : term13 x) : term44 x.
Proof. exact (EQ_MP (@lem2327216 x) (@lem2330482 x h1)). Qed.
Lemma lem2330485 (x : int) (h1 : term13 x) : term12 x.
Proof. exact (@lem2330483 x h1 (@lem2327132 x)). Qed.
Lemma lem2330486 (x : int) (h1 : term13 x) : (term13 x) = (term12 x).
Proof. exact (prop_ext (fun h2 : term13 x => @lem2330485 x h1) (fun h2 : term12 x => @lem2327135 x h1)). Qed.
Lemma lem2330487 (x : int) (h1 : term13 x) : term12 x.
Proof. exact (EQ_MP (@lem2330486 x h1) (@lem2327135 x h1)). Qed.
Lemma lem2330488 (x : int) : term536 x.
Proof. exact (fun h0 : term13 x => @lem2330487 x h0). Qed.
Lemma lem2330489 (x : int) (n : nat) (h1 : x = (int_of_num n)) : (x = (int_of_num n)) = (term13 x).
Proof. exact (prop_ext (fun h2 : x = (int_of_num n) => @lem2327149 x n h1) (fun h2 : term13 x => @lem2327134 x n h1)). Qed.
Lemma lem2330490 (x : int) (n : nat) (h1 : x = (int_of_num n)) : term13 x.
Proof. exact (EQ_MP (@lem2330489 x n h1) (@lem2327134 x n h1)). Qed.
Lemma lem2330491 (x : int) (h1 : term12 x) : term13 x.
Proof. exact (ex_elim (@lem2327133 x h1) (fun n : nat => fun h0 : term21 x n => @lem2330490 x n h0)). Qed.
Lemma lem2330492 (x : int) : term537 x.
Proof. exact (fun h0 : term12 x => @lem2330491 x h0). Qed.
Lemma lem2330493 (x : int) : term538 x.
Proof. exact (conj (@lem2330492 x) (@lem2330488 x)). Qed.
Lemma lem2330494 (x : int) : (term538 x) = ((term12 x) = (term13 x)).
Proof. exact (@lem32 (term12 x) (term13 x)). Qed.
Lemma lem2330495 (x : int) : (term12 x) = (term13 x).
Proof. exact (EQ_MP (@lem2330494 x) (@lem2330493 x)). Qed.
Lemma lem2330500 : term539.
Proof. exact (fun x : int => @lem2330495 x). Qed.
