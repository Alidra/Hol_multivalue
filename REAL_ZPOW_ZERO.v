Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_ZERO_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import INT_NEG_EQ_0_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import REAL_INV_1_spec.
Require Import REAL_POW_ZERO_spec.
Require Import REAL_ZPOW_NEG_spec.
Require Import REAL_ZPOW_NUM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1340073_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3173105 (m : nat) : term0 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem3173106 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3173107 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3173106 m) (@lem3173105 m)). Qed.
Lemma lem3173108 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3173107 m n). Qed.
Lemma lem3173109 (m : nat) (n : nat) : (term2 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem3173111 (x : int) : term3 x.
Proof. exact (@lem2306427 x). Qed.
Lemma lem3173112 (x : int) : (term3 x) = (((int_neg x) = term4) = (x = term4)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem3173114 (n : nat) : term5 n.
Proof. exact (@lem1648695 n). Qed.
Lemma lem3173115 (n : nat) : (term5 n) = ((term6 n) = (term7 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem3173117 (x : real) : term8 x.
Proof. exact (@lem3169304 x). Qed.
Lemma lem3173118 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem3173119 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem3173118 x) (@lem3173117 x)). Qed.
Lemma lem3173120 (x : real) (n : nat) : term10 x n.
Proof. exact (@lem3173119 x n). Qed.
Lemma lem3173121 (x : real) (n : nat) : (term10 x n) = ((term11 x n) = (real_pow x n)).
Proof. exact (eq_refl (term10 x n)). Qed.
Lemma lem3173123 (x : real) : term12 x.
Proof. exact (@lem3173052 x). Qed.
Lemma lem3173124 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem3173125 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem3173124 x) (@lem3173123 x)). Qed.
Lemma lem3173126 (x : real) (n : int) : term14 x n.
Proof. exact (@lem3173125 x n). Qed.
Lemma lem3173127 (x : real) (n : int) : (term14 x n) = ((term15 x n) = (term16 x n)).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem3173129 (P : int -> Prop) : term17 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3173130 (P : int -> Prop) : (term17 P) = ((term18 P) = (term19 P)).
Proof. exact (eq_refl (term17 P)). Qed.
Lemma lem3173137 (P : int -> Prop) : (term18 P) = (term19 P).
Proof. exact (EQ_MP (@lem3173130 P) (@lem3173129 P)). Qed.
Lemma lem3173138 : term20 = term21.
Proof. exact (@lem3173137 term22). Qed.
Lemma lem3173139 (n : int) : (term23 n) = ((term24 n) = (term25 n)).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem3173140 : term26 = term22.
Proof. exact (fun_ext (fun n : int => @lem3173139 n)). Qed.
Lemma lem3173141 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3173142 : term20 = term27.
Proof. exact (MK_COMB (@lem3173141) (@lem3173140)). Qed.
Lemma lem3173143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173144 : term28 = term29.
Proof. exact (MK_COMB (@lem3173143) (@lem3173142)). Qed.
Lemma lem3173145 (n : nat) : (term30 n) = ((term31 n) = (term32 n)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem3173146 : term33 = term34.
Proof. exact (fun_ext (fun n : nat => @lem3173145 n)). Qed.
Lemma lem3173147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173148 : term35 = term36.
Proof. exact (MK_COMB (@lem3173147) (@lem3173146)). Qed.
Lemma lem3173149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173150 : term37 = term38.
Proof. exact (MK_COMB (@lem3173149) (@lem3173148)). Qed.
Lemma lem3173151 (n : nat) : (term39 n) = ((term40 n) = (term41 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem3173152 : term42 = term43.
Proof. exact (fun_ext (fun n : nat => @lem3173151 n)). Qed.
Lemma lem3173153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173154 : term44 = term45.
Proof. exact (MK_COMB (@lem3173153) (@lem3173152)). Qed.
Lemma lem3173155 : term21 = term46.
Proof. exact (MK_COMB (@lem3173150) (@lem3173154)). Qed.
Lemma lem3173156 : (term20 = term21) = (term27 = term46).
Proof. exact (MK_COMB (@lem3173144) (@lem3173155)). Qed.
Lemma lem3173157 : term27 = term46.
Proof. exact (EQ_MP (@lem3173156) (@lem3173138)). Qed.
Lemma lem3173169 (x : real) (n : nat) : (term11 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3173121 x n) (@lem3173120 x n)). Qed.
Lemma lem3173170 (n : nat) : (term31 n) = (term6 n).
Proof. exact (@lem3173169 term47 n). Qed.
Lemma lem3173171 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173172 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem3173171) (@lem3173170 n)). Qed.
Lemma lem3173177 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem3173178 (n : nat) : ((term31 n) = (term32 n)) = ((term6 n) = (term32 n)).
Proof. exact (MK_COMB (@lem3173172 n) (@lem3173177 n)). Qed.
Lemma lem3173181 : term34 = term50.
Proof. exact (fun_ext (fun n : nat => @lem3173178 n)). Qed.
Lemma lem3173182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173183 : term36 = term51.
Proof. exact (MK_COMB (@lem3173182) (@lem3173181)). Qed.
Lemma lem3173190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173191 : term38 = term52.
Proof. exact (MK_COMB (@lem3173190) (@lem3173183)). Qed.
Lemma lem3173201 (x : real) (n : int) : (term15 x n) = (term16 x n).
Proof. exact (EQ_MP (@lem3173127 x n) (@lem3173126 x n)). Qed.
Lemma lem3173202 (n : nat) : (term40 n) = (term53 n).
Proof. exact (@lem3173201 term47 (int_of_num n)). Qed.
Lemma lem3173204 (x : real) (n : nat) : (term11 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3173121 x n) (@lem3173120 x n)). Qed.
Lemma lem3173205 (n : nat) : (term31 n) = (term6 n).
Proof. exact (@lem3173204 term47 n). Qed.
Lemma lem3173206 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3173207 (n : nat) : (term53 n) = (term54 n).
Proof. exact (MK_COMB (@lem3173206) (@lem3173205 n)). Qed.
Lemma lem3173208 (n : nat) : (term40 n) = (term54 n).
Proof. exact (TRANS (@lem3173202 n) (@lem3173207 n)). Qed.
Lemma lem3173209 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173210 (n : nat) : (term55 n) = (term56 n).
Proof. exact (MK_COMB (@lem3173209) (@lem3173208 n)). Qed.
Lemma lem3173215 (n : nat) : (term41 n) = (term41 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem3173216 (n : nat) : ((term40 n) = (term41 n)) = ((term54 n) = (term41 n)).
Proof. exact (MK_COMB (@lem3173210 n) (@lem3173215 n)). Qed.
Lemma lem3173219 : term43 = term57.
Proof. exact (fun_ext (fun n : nat => @lem3173216 n)). Qed.
Lemma lem3173220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173221 : term45 = term58.
Proof. exact (MK_COMB (@lem3173220) (@lem3173219)). Qed.
Lemma lem3173228 : term46 = term59.
Proof. exact (MK_COMB (@lem3173191) (@lem3173221)). Qed.
Lemma lem3173231 : term27 = term59.
Proof. exact (TRANS (@lem3173157) (@lem3173228)). Qed.
Lemma lem3173232 : term59 = term27.
Proof. exact (SYM (@lem3173231)). Qed.
Lemma lem3173242 (n : nat) : (term6 n) = (term7 n).
Proof. exact (EQ_MP (@lem3173115 n) (@lem3173114 n)). Qed.
Lemma lem3173247 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173248 (n : nat) : (term49 n) = (term60 n).
Proof. exact (MK_COMB (@lem3173247) (@lem3173242 n)). Qed.
Lemma lem3173252 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem3173109 m n) (@lem3173108 m n)). Qed.
Lemma lem3173253 (n : nat) : ((int_of_num n) = term4) = (n = (NUMERAL 0)).
Proof. exact (@lem3173252 n (NUMERAL 0)). Qed.
Lemma lem3173256 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3173257 (n : nat) : (term61 n) = (term62 n).
Proof. exact (MK_COMB (@lem3173256) (@lem3173253 n)). Qed.
Lemma lem3173258 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem3173259 (n : nat) : (term64 n) = (term65 n).
Proof. exact (MK_COMB (@lem3173257 n) (@lem3173258)). Qed.
Lemma lem3173260 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem3173261 (n : nat) : (term32 n) = (term7 n).
Proof. exact (MK_COMB (@lem3173259 n) (@lem3173260)). Qed.
Lemma lem3173264 (n : nat) : ((term6 n) = (term32 n)) = ((term7 n) = (term7 n)).
Proof. exact (MK_COMB (@lem3173248 n) (@lem3173261 n)). Qed.
Lemma lem3173266 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3173267 (x : real) : (x = x) = True.
Proof. exact (@lem3173266 real x). Qed.
Lemma lem3173268 (n : nat) : ((term7 n) = (term7 n)) = True.
Proof. exact (@lem3173267 (term7 n)). Qed.
Lemma lem3173269 (n : nat) : ((term6 n) = (term32 n)) = True.
Proof. exact (TRANS (@lem3173264 n) (@lem3173268 n)). Qed.
Lemma lem3173270 : term50 = term66.
Proof. exact (fun_ext (fun n : nat => @lem3173269 n)). Qed.
Lemma lem3173271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173272 : term51 = term67.
Proof. exact (MK_COMB (@lem3173271) (@lem3173270)). Qed.
Lemma lem3173274 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3173275 (t : Prop) : (term69 t) = t.
Proof. exact (@lem3173274 nat t). Qed.
Lemma lem3173276 : term67 = True.
Proof. exact (@lem3173275 True). Qed.
Lemma lem3173277 : term51 = True.
Proof. exact (TRANS (@lem3173272) (@lem3173276)). Qed.
Lemma lem3173278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173279 : term52 = (and True).
Proof. exact (MK_COMB (@lem3173278) (@lem3173277)). Qed.
Lemma lem3173287 (n : nat) : (term6 n) = (term7 n).
Proof. exact (EQ_MP (@lem3173115 n) (@lem3173114 n)). Qed.
Lemma lem3173292 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3173293 (n : nat) : (term54 n) = (term70 n).
Proof. exact (MK_COMB (@lem3173292) (@lem3173287 n)). Qed.
Lemma lem3173294 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173295 (n : nat) : (term56 n) = (term71 n).
Proof. exact (MK_COMB (@lem3173294) (@lem3173293 n)). Qed.
Lemma lem3173299 (x : int) : ((int_neg x) = term4) = (x = term4).
Proof. exact (EQ_MP (@lem3173112 x) (@lem3173111 x)). Qed.
Lemma lem3173300 (n : nat) : ((term72 n) = term4) = ((int_of_num n) = term4).
Proof. exact (@lem3173299 (int_of_num n)). Qed.
Lemma lem3173302 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem3173109 m n) (@lem3173108 m n)). Qed.
Lemma lem3173303 (n : nat) : ((int_of_num n) = term4) = (n = (NUMERAL 0)).
Proof. exact (@lem3173302 n (NUMERAL 0)). Qed.
Lemma lem3173306 (n : nat) : ((term72 n) = term4) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem3173300 n) (@lem3173303 n)). Qed.
Lemma lem3173307 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3173308 (n : nat) : (term73 n) = (term62 n).
Proof. exact (MK_COMB (@lem3173307) (@lem3173306 n)). Qed.
Lemma lem3173309 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem3173310 (n : nat) : (term74 n) = (term65 n).
Proof. exact (MK_COMB (@lem3173308 n) (@lem3173309)). Qed.
Lemma lem3173311 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem3173312 (n : nat) : (term41 n) = (term7 n).
Proof. exact (MK_COMB (@lem3173310 n) (@lem3173311)). Qed.
Lemma lem3173315 (n : nat) : ((term54 n) = (term41 n)) = ((term70 n) = (term7 n)).
Proof. exact (MK_COMB (@lem3173295 n) (@lem3173312 n)). Qed.
Lemma lem3173318 : term57 = term75.
Proof. exact (fun_ext (fun n : nat => @lem3173315 n)). Qed.
Lemma lem3173319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173320 : term58 = term76.
Proof. exact (MK_COMB (@lem3173319) (@lem3173318)). Qed.
Lemma lem3173325 : term59 = term77.
Proof. exact (MK_COMB (@lem3173279) (@lem3173320)). Qed.
Lemma lem3173327 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3173328 : term77 = term76.
Proof. exact (@lem3173327 term76). Qed.
Lemma lem3173343 : term59 = term76.
Proof. exact (TRANS (@lem3173325) (@lem3173328)). Qed.
Lemma lem3173344 : term76 = term59.
Proof. exact (SYM (@lem3173343)). Qed.
Lemma lem3173346 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3173347 : term76 = term79.
Proof. exact (@lem3173346 term76). Qed.
Lemma lem3173348 : term79 = term76.
Proof. exact (SYM (@lem3173347)). Qed.
Lemma lem3173349 (h1 : term80) : term80.
Proof. exact (h1). Qed.
Lemma lem3173352 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem3173353 : term82.
Proof. exact (fun h0 : term81 => @lem3173352 h0). Qed.
Lemma lem3173354 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem3173355 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem3173356 (h1 : term81) (h2 : term82) : term81.
Proof. exact (@lem3173354 h2 (@lem3173355 h1)). Qed.
Lemma lem3173357 (h1 : term81) : term83.
Proof. exact (fun h0 : term82 => @lem3173356 h1 h0). Qed.
Lemma lem3173358 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem3173359 (h1 : term81) (h2 : term82) : term81.
Proof. exact (@lem3173357 h1 (@lem3173358 h2)). Qed.
Lemma lem3173360 (h1 : term82) : term82.
Proof. exact (fun h0 : term81 => @lem3173359 h0 h1). Qed.
Lemma lem3173361 : term84.
Proof. exact (fun h0 : term82 => @lem3173360 h0). Qed.
Lemma lem3173364 : term82.
Proof. exact (@lem3173361 (@lem3173353)). Qed.
Lemma lem3173374 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3173375 : term85 = term86.
Proof. exact (@lem3173374 (term87 = term47)). Qed.
Lemma lem3173376 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem3173377 : term89 = term90.
Proof. exact (MK_COMB (@lem3173376) (@lem3173375)). Qed.
Lemma lem3173380 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem3173387 : term81 = term92.
Proof. exact (MK_COMB (@lem3173380) (@lem3173377)). Qed.
Lemma lem3173394 : term90 = term90.
Proof. exact (eq_refl term90). Qed.
Lemma lem3173398 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem3173399 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3173400 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term62 n) = (@COND real False).
Proof. exact (MK_COMB (@lem3173399) (@lem3173398 n h1)). Qed.
Lemma lem3173401 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem3173402 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term65 n) = term93.
Proof. exact (MK_COMB (@lem3173400 n h1) (@lem3173401)). Qed.
Lemma lem3173403 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem3173404 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term7 n) = term94.
Proof. exact (MK_COMB (@lem3173402 n h1) (@lem3173403)). Qed.
Lemma lem3173406 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3173407 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem3173406 real t1 t2). Qed.
Lemma lem3173408 : term94 = term47.
Proof. exact (@lem3173407 term63 term47). Qed.
Lemma lem3173409 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term7 n) = term47.
Proof. exact (TRANS (@lem3173404 n h1) (@lem3173408)). Qed.
Lemma lem3173410 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3173411 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term70 n) = term87.
Proof. exact (MK_COMB (@lem3173410) (@lem3173409 n h1)). Qed.
Lemma lem3173412 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173413 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term71 n) = term95.
Proof. exact (MK_COMB (@lem3173412) (@lem3173411 n h1)). Qed.
Lemma lem3173415 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem3173416 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3173417 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term62 n) = (@COND real False).
Proof. exact (MK_COMB (@lem3173416) (@lem3173415 n h1)). Qed.
Lemma lem3173418 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem3173419 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term65 n) = term93.
Proof. exact (MK_COMB (@lem3173417 n h1) (@lem3173418)). Qed.
Lemma lem3173420 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem3173421 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term7 n) = term94.
Proof. exact (MK_COMB (@lem3173419 n h1) (@lem3173420)). Qed.
Lemma lem3173423 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3173424 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem3173423 real t1 t2). Qed.
Lemma lem3173425 : term94 = term47.
Proof. exact (@lem3173424 term63 term47). Qed.
Lemma lem3173426 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term7 n) = term47.
Proof. exact (TRANS (@lem3173421 n h1) (@lem3173425)). Qed.
Lemma lem3173427 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term70 n) = (term7 n)) = (term87 = term47).
Proof. exact (MK_COMB (@lem3173413 n h1) (@lem3173426 n h1)). Qed.
Lemma lem3173430 (n : nat) : term96 n.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = False => @lem3173427 n h0). Qed.
Lemma lem3173432 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem3173433 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3173434 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term62 n) = (@COND real True).
Proof. exact (MK_COMB (@lem3173433) (@lem3173432 n h1)). Qed.
Lemma lem3173435 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem3173436 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term65 n) = term97.
Proof. exact (MK_COMB (@lem3173434 n h1) (@lem3173435)). Qed.
Lemma lem3173437 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem3173438 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term7 n) = term98.
Proof. exact (MK_COMB (@lem3173436 n h1) (@lem3173437)). Qed.
Lemma lem3173440 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3173441 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem3173440 real t2 t1). Qed.
Lemma lem3173442 : term98 = term63.
Proof. exact (@lem3173441 term47 term63). Qed.
Lemma lem3173443 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term7 n) = term63.
Proof. exact (TRANS (@lem3173438 n h1) (@lem3173442)). Qed.
Lemma lem3173444 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3173445 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term70 n) = term99.
Proof. exact (MK_COMB (@lem3173444) (@lem3173443 n h1)). Qed.
Lemma lem3173446 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173447 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term71 n) = term100.
Proof. exact (MK_COMB (@lem3173446) (@lem3173445 n h1)). Qed.
Lemma lem3173449 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem3173450 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3173451 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term62 n) = (@COND real True).
Proof. exact (MK_COMB (@lem3173450) (@lem3173449 n h1)). Qed.
Lemma lem3173452 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem3173453 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term65 n) = term97.
Proof. exact (MK_COMB (@lem3173451 n h1) (@lem3173452)). Qed.
Lemma lem3173454 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem3173455 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term7 n) = term98.
Proof. exact (MK_COMB (@lem3173453 n h1) (@lem3173454)). Qed.
Lemma lem3173457 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3173458 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem3173457 real t2 t1). Qed.
Lemma lem3173459 : term98 = term63.
Proof. exact (@lem3173458 term47 term63). Qed.
Lemma lem3173460 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term7 n) = term63.
Proof. exact (TRANS (@lem3173455 n h1) (@lem3173459)). Qed.
Lemma lem3173461 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term70 n) = (term7 n)) = (term99 = term63).
Proof. exact (MK_COMB (@lem3173447 n h1) (@lem3173460 n h1)). Qed.
Lemma lem3173464 (n : nat) : term101 n.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = True => @lem3173461 n h0). Qed.
Lemma lem3173465 (n : nat) : term102 n.
Proof. exact (conj (@lem3173430 n) (@lem3173464 n)). Qed.
Lemma lem3173467 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term103 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem3173468 (n : nat) : term104 n.
Proof. exact (@lem3173467 ((term70 n) = (term7 n)) (term99 = term63) (n = (NUMERAL 0)) (term87 = term47)). Qed.
Lemma lem3173501 (n : nat) : ((term70 n) = (term7 n)) = (term105 n).
Proof. exact (@lem3173468 n (@lem3173465 n)). Qed.
Lemma lem3173502 : term75 = term106.
Proof. exact (fun_ext (fun n : nat => @lem3173501 n)). Qed.
Lemma lem3173503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3173504 : term76 = term107.
Proof. exact (MK_COMB (@lem3173503) (@lem3173502)). Qed.
Lemma lem3173505 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3173506 : term80 = term108.
Proof. exact (MK_COMB (@lem3173505) (@lem3173504)). Qed.
Lemma lem3173507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3173508 : term91 = term109.
Proof. exact (MK_COMB (@lem3173507) (@lem3173506)). Qed.
Lemma lem3173509 : term92 = term110.
Proof. exact (MK_COMB (@lem3173508) (@lem3173394)). Qed.
Lemma lem3173528 : term81 = term110.
Proof. exact (TRANS (@lem3173387) (@lem3173509)). Qed.
Lemma lem3173529 : term110 = term81.
Proof. exact (SYM (@lem3173528)). Qed.
Lemma lem3173530 (h1 : term108) : term108.
Proof. exact (h1). Qed.
Lemma lem3173535 (n : nat) : (term111 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem3173536 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem3173537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173538 (n : nat) : (term113 n) = (term114 n).
Proof. exact (MK_COMB (@lem3173537) (@lem3173535 n)). Qed.
Lemma lem3173539 (n : nat) : (term115 n) = (term116 n).
Proof. exact (MK_COMB (@lem3173538 n) (@lem3173536)). Qed.
Lemma lem3173540 (n : nat) : (term117 n) = (term115 n).
Proof. exact (@lem17160 (term118 n) (term99 = term63)). Qed.
Lemma lem3173541 (n : nat) : (term117 n) = (term116 n).
Proof. exact (TRANS (@lem3173540 n) (@lem3173539 n)). Qed.
Lemma lem3173548 (n : nat) : (term119 n) = (term120 n).
Proof. exact (@lem17160 (n = (NUMERAL 0)) (term87 = term47)). Qed.
Lemma lem3173549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173550 (n : nat) : (term121 n) = (term122 n).
Proof. exact (MK_COMB (@lem3173549) (@lem3173541 n)). Qed.
Lemma lem3173551 (n : nat) : (term123 n) = (term124 n).
Proof. exact (MK_COMB (@lem3173550 n) (@lem3173548 n)). Qed.
Lemma lem3173552 (n : nat) : (term125 n) = (term123 n).
Proof. exact (@lem17045 (term126 n) (term127 n)). Qed.
Lemma lem3173553 (n : nat) : (term125 n) = (term124 n).
Proof. exact (TRANS (@lem3173552 n) (@lem3173551 n)). Qed.
Lemma lem3173554 (P : nat -> Prop) : (term128 P) = (term129 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3173555 : term108 = term130.
Proof. exact (@lem3173554 term106). Qed.
Lemma lem3173556 (n : nat) : (term131 n) = (term105 n).
Proof. exact (eq_refl (term131 n)). Qed.
Lemma lem3173557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3173558 (n : nat) : (term132 n) = (term125 n).
Proof. exact (MK_COMB (@lem3173557) (@lem3173556 n)). Qed.
Lemma lem3173559 (n : nat) : (term132 n) = (term124 n).
Proof. exact (TRANS (@lem3173558 n) (@lem3173553 n)). Qed.
Lemma lem3173560 : term133 = term134.
Proof. exact (fun_ext (fun n : nat => @lem3173559 n)). Qed.
Lemma lem3173561 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173562 : term130 = term135.
Proof. exact (MK_COMB (@lem3173561) (@lem3173560)). Qed.
Lemma lem3173563 : term108 = term135.
Proof. exact (TRANS (@lem3173555) (@lem3173562)). Qed.
Lemma lem3173565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3173566 (P : nat -> Prop) (Q : nat -> Prop) : (term138 P Q) = (term139 P Q).
Proof. exact (@lem3173565 nat P Q). Qed.
Lemma lem3173567 : term140 = term141.
Proof. exact (@lem3173566 term142 term143). Qed.
Lemma lem3173568 (n : nat) : (term144 n) = (term116 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem3173569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173570 (n : nat) : (term145 n) = (term122 n).
Proof. exact (MK_COMB (@lem3173569) (@lem3173568 n)). Qed.
Lemma lem3173571 (n : nat) : (term146 n) = (term120 n).
Proof. exact (eq_refl (term146 n)). Qed.
Lemma lem3173572 (n : nat) : (term147 n) = (term124 n).
Proof. exact (MK_COMB (@lem3173570 n) (@lem3173571 n)). Qed.
Lemma lem3173573 : term148 = term134.
Proof. exact (fun_ext (fun n : nat => @lem3173572 n)). Qed.
Lemma lem3173574 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173575 : term140 = term135.
Proof. exact (MK_COMB (@lem3173574) (@lem3173573)). Qed.
Lemma lem3173576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173577 : term149 = term150.
Proof. exact (MK_COMB (@lem3173576) (@lem3173575)). Qed.
Lemma lem3173578 (n : nat) : (term144 n) = (term116 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem3173579 : term151 = term142.
Proof. exact (fun_ext (fun n : nat => @lem3173578 n)). Qed.
Lemma lem3173580 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173581 : term152 = term153.
Proof. exact (MK_COMB (@lem3173580) (@lem3173579)). Qed.
Lemma lem3173582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173583 : term154 = term155.
Proof. exact (MK_COMB (@lem3173582) (@lem3173581)). Qed.
Lemma lem3173584 (n : nat) : (term146 n) = (term120 n).
Proof. exact (eq_refl (term146 n)). Qed.
Lemma lem3173585 : term156 = term143.
Proof. exact (fun_ext (fun n : nat => @lem3173584 n)). Qed.
Lemma lem3173586 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173587 : term157 = term158.
Proof. exact (MK_COMB (@lem3173586) (@lem3173585)). Qed.
Lemma lem3173588 : term141 = term159.
Proof. exact (MK_COMB (@lem3173583) (@lem3173587)). Qed.
Lemma lem3173589 : (term140 = term141) = (term135 = term159).
Proof. exact (MK_COMB (@lem3173577) (@lem3173588)). Qed.
Lemma lem3173590 : term135 = term159.
Proof. exact (EQ_MP (@lem3173589) (@lem3173567)). Qed.
Lemma lem3173612 {A : Type'} (P : A -> Prop) (Q : Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem3173613 (P : nat -> Prop) (Q : Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem3173612 nat P Q). Qed.
Lemma lem3173614 : term164 = term165.
Proof. exact (@lem3173613 term166 term112). Qed.
Lemma lem3173615 (n : nat) : (term167 n) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem3173616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173617 (n : nat) : (term168 n) = (term114 n).
Proof. exact (MK_COMB (@lem3173616) (@lem3173615 n)). Qed.
Lemma lem3173618 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem3173619 (n : nat) : (term169 n) = (term116 n).
Proof. exact (MK_COMB (@lem3173617 n) (@lem3173618)). Qed.
Lemma lem3173620 : term170 = term142.
Proof. exact (fun_ext (fun n : nat => @lem3173619 n)). Qed.
Lemma lem3173621 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173622 : term164 = term153.
Proof. exact (MK_COMB (@lem3173621) (@lem3173620)). Qed.
Lemma lem3173623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173624 : term171 = term172.
Proof. exact (MK_COMB (@lem3173623) (@lem3173622)). Qed.
Lemma lem3173625 (n : nat) : (term167 n) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem3173626 : term173 = term166.
Proof. exact (fun_ext (fun n : nat => @lem3173625 n)). Qed.
Lemma lem3173627 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173628 : term174 = term175.
Proof. exact (MK_COMB (@lem3173627) (@lem3173626)). Qed.
Lemma lem3173629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173630 : term176 = term177.
Proof. exact (MK_COMB (@lem3173629) (@lem3173628)). Qed.
Lemma lem3173631 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem3173632 : term165 = term178.
Proof. exact (MK_COMB (@lem3173630) (@lem3173631)). Qed.
Lemma lem3173633 : (term164 = term165) = (term153 = term178).
Proof. exact (MK_COMB (@lem3173624) (@lem3173632)). Qed.
Lemma lem3173634 : term153 = term178.
Proof. exact (EQ_MP (@lem3173633) (@lem3173614)). Qed.
Lemma lem3173639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173640 : term155 = term179.
Proof. exact (MK_COMB (@lem3173639) (@lem3173634)). Qed.
Lemma lem3173662 {A : Type'} (P : A -> Prop) (Q : Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem3173663 (P : nat -> Prop) (Q : Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem3173662 nat P Q). Qed.
Lemma lem3173664 : term180 = term181.
Proof. exact (@lem3173663 term182 term86). Qed.
Lemma lem3173665 (n : nat) : (term183 n) = (term118 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem3173666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173667 (n : nat) : (term184 n) = (term185 n).
Proof. exact (MK_COMB (@lem3173666) (@lem3173665 n)). Qed.
Lemma lem3173668 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem3173669 (n : nat) : (term186 n) = (term120 n).
Proof. exact (MK_COMB (@lem3173667 n) (@lem3173668)). Qed.
Lemma lem3173670 : term187 = term143.
Proof. exact (fun_ext (fun n : nat => @lem3173669 n)). Qed.
Lemma lem3173671 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173672 : term180 = term158.
Proof. exact (MK_COMB (@lem3173671) (@lem3173670)). Qed.
Lemma lem3173673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173674 : term188 = term189.
Proof. exact (MK_COMB (@lem3173673) (@lem3173672)). Qed.
Lemma lem3173675 (n : nat) : (term183 n) = (term118 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem3173676 : term190 = term182.
Proof. exact (fun_ext (fun n : nat => @lem3173675 n)). Qed.
Lemma lem3173677 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173678 : term191 = term192.
Proof. exact (MK_COMB (@lem3173677) (@lem3173676)). Qed.
Lemma lem3173679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173680 : term193 = term194.
Proof. exact (MK_COMB (@lem3173679) (@lem3173678)). Qed.
Lemma lem3173681 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem3173682 : term181 = term195.
Proof. exact (MK_COMB (@lem3173680) (@lem3173681)). Qed.
Lemma lem3173683 : (term180 = term181) = (term158 = term195).
Proof. exact (MK_COMB (@lem3173674) (@lem3173682)). Qed.
Lemma lem3173684 : term158 = term195.
Proof. exact (EQ_MP (@lem3173683) (@lem3173664)). Qed.
Lemma lem3173689 : term159 = term196.
Proof. exact (MK_COMB (@lem3173640) (@lem3173684)). Qed.
Lemma lem3173690 : term135 = term196.
Proof. exact (TRANS (@lem3173590) (@lem3173689)). Qed.
Lemma lem3173692 {A : Type'} (P : A -> Prop) (Q : Prop) : (term161 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3173693 (P : nat -> Prop) (Q : Prop) : (term163 P Q) = (term162 P Q).
Proof. exact (@lem3173692 nat P Q). Qed.
Lemma lem3173694 : term165 = term164.
Proof. exact (@lem3173693 term166 term112). Qed.
Lemma lem3173695 (n : nat) : (term167 n) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem3173696 : term173 = term166.
Proof. exact (fun_ext (fun n : nat => @lem3173695 n)). Qed.
Lemma lem3173697 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173698 : term174 = term175.
Proof. exact (MK_COMB (@lem3173697) (@lem3173696)). Qed.
Lemma lem3173699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173700 : term176 = term177.
Proof. exact (MK_COMB (@lem3173699) (@lem3173698)). Qed.
Lemma lem3173701 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem3173702 : term165 = term178.
Proof. exact (MK_COMB (@lem3173700) (@lem3173701)). Qed.
Lemma lem3173703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173704 : term197 = term198.
Proof. exact (MK_COMB (@lem3173703) (@lem3173702)). Qed.
Lemma lem3173705 (n : nat) : (term167 n) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem3173706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173707 (n : nat) : (term168 n) = (term114 n).
Proof. exact (MK_COMB (@lem3173706) (@lem3173705 n)). Qed.
Lemma lem3173708 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem3173709 (n : nat) : (term169 n) = (term116 n).
Proof. exact (MK_COMB (@lem3173707 n) (@lem3173708)). Qed.
Lemma lem3173710 : term170 = term142.
Proof. exact (fun_ext (fun n : nat => @lem3173709 n)). Qed.
Lemma lem3173711 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173712 : term164 = term153.
Proof. exact (MK_COMB (@lem3173711) (@lem3173710)). Qed.
Lemma lem3173713 : (term165 = term164) = (term178 = term153).
Proof. exact (MK_COMB (@lem3173704) (@lem3173712)). Qed.
Lemma lem3173714 : term178 = term153.
Proof. exact (EQ_MP (@lem3173713) (@lem3173694)). Qed.
Lemma lem3173715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173716 : term179 = term155.
Proof. exact (MK_COMB (@lem3173715) (@lem3173714)). Qed.
Lemma lem3173718 {A : Type'} (P : A -> Prop) (Q : Prop) : (term161 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3173719 (P : nat -> Prop) (Q : Prop) : (term163 P Q) = (term162 P Q).
Proof. exact (@lem3173718 nat P Q). Qed.
Lemma lem3173720 : term181 = term180.
Proof. exact (@lem3173719 term182 term86). Qed.
Lemma lem3173721 (n : nat) : (term183 n) = (term118 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem3173722 : term190 = term182.
Proof. exact (fun_ext (fun n : nat => @lem3173721 n)). Qed.
Lemma lem3173723 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173724 : term191 = term192.
Proof. exact (MK_COMB (@lem3173723) (@lem3173722)). Qed.
Lemma lem3173725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173726 : term193 = term194.
Proof. exact (MK_COMB (@lem3173725) (@lem3173724)). Qed.
Lemma lem3173727 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem3173728 : term181 = term195.
Proof. exact (MK_COMB (@lem3173726) (@lem3173727)). Qed.
Lemma lem3173729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173730 : term199 = term200.
Proof. exact (MK_COMB (@lem3173729) (@lem3173728)). Qed.
Lemma lem3173731 (n : nat) : (term183 n) = (term118 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem3173732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3173733 (n : nat) : (term184 n) = (term185 n).
Proof. exact (MK_COMB (@lem3173732) (@lem3173731 n)). Qed.
Lemma lem3173734 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem3173735 (n : nat) : (term186 n) = (term120 n).
Proof. exact (MK_COMB (@lem3173733 n) (@lem3173734)). Qed.
Lemma lem3173736 : term187 = term143.
Proof. exact (fun_ext (fun n : nat => @lem3173735 n)). Qed.
Lemma lem3173737 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173738 : term180 = term158.
Proof. exact (MK_COMB (@lem3173737) (@lem3173736)). Qed.
Lemma lem3173739 : (term181 = term180) = (term195 = term158).
Proof. exact (MK_COMB (@lem3173730) (@lem3173738)). Qed.
Lemma lem3173740 : term195 = term158.
Proof. exact (EQ_MP (@lem3173739) (@lem3173720)). Qed.
Lemma lem3173741 : term196 = term159.
Proof. exact (MK_COMB (@lem3173716) (@lem3173740)). Qed.
Lemma lem3173743 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3173744 (P : nat -> Prop) (Q : nat -> Prop) : (term139 P Q) = (term138 P Q).
Proof. exact (@lem3173743 nat P Q). Qed.
Lemma lem3173745 : term141 = term140.
Proof. exact (@lem3173744 term142 term143). Qed.
Lemma lem3173746 (n : nat) : (term144 n) = (term116 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem3173747 : term151 = term142.
Proof. exact (fun_ext (fun n : nat => @lem3173746 n)). Qed.
Lemma lem3173748 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173749 : term152 = term153.
Proof. exact (MK_COMB (@lem3173748) (@lem3173747)). Qed.
Lemma lem3173750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173751 : term154 = term155.
Proof. exact (MK_COMB (@lem3173750) (@lem3173749)). Qed.
Lemma lem3173752 (n : nat) : (term146 n) = (term120 n).
Proof. exact (eq_refl (term146 n)). Qed.
Lemma lem3173753 : term156 = term143.
Proof. exact (fun_ext (fun n : nat => @lem3173752 n)). Qed.
Lemma lem3173754 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173755 : term157 = term158.
Proof. exact (MK_COMB (@lem3173754) (@lem3173753)). Qed.
Lemma lem3173756 : term141 = term159.
Proof. exact (MK_COMB (@lem3173751) (@lem3173755)). Qed.
Lemma lem3173757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3173758 : term201 = term202.
Proof. exact (MK_COMB (@lem3173757) (@lem3173756)). Qed.
Lemma lem3173759 (n : nat) : (term144 n) = (term116 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem3173760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3173761 (n : nat) : (term145 n) = (term122 n).
Proof. exact (MK_COMB (@lem3173760) (@lem3173759 n)). Qed.
Lemma lem3173762 (n : nat) : (term146 n) = (term120 n).
Proof. exact (eq_refl (term146 n)). Qed.
Lemma lem3173763 (n : nat) : (term147 n) = (term124 n).
Proof. exact (MK_COMB (@lem3173761 n) (@lem3173762 n)). Qed.
Lemma lem3173764 : term148 = term134.
Proof. exact (fun_ext (fun n : nat => @lem3173763 n)). Qed.
Lemma lem3173765 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3173766 : term140 = term135.
Proof. exact (MK_COMB (@lem3173765) (@lem3173764)). Qed.
Lemma lem3173767 : (term141 = term140) = (term159 = term135).
Proof. exact (MK_COMB (@lem3173758) (@lem3173766)). Qed.
Lemma lem3173768 : term159 = term135.
Proof. exact (EQ_MP (@lem3173767) (@lem3173745)). Qed.
Lemma lem3173769 : term196 = term135.
Proof. exact (TRANS (@lem3173741) (@lem3173768)). Qed.
Lemma lem3173770 : term135 = term135.
Proof. exact (TRANS (@lem3173690) (@lem3173769)). Qed.
Lemma lem3173771 : term108 = term135.
Proof. exact (TRANS (@lem3173563) (@lem3173770)). Qed.
Lemma lem3173772 (h1 : term108) : term135.
Proof. exact (EQ_MP (@lem3173771) (@lem3173530 h1)). Qed.
Lemma lem3173778 (h1 : term99 = term63) : term99 = term63.
Proof. exact (h1). Qed.
Lemma lem3173784 (h1 : term87 = term47) : term87 = term47.
Proof. exact (h1). Qed.
Lemma lem3173805 (h1 : term99 = term63) : term99 = term63.
Proof. exact (h1). Qed.
Lemma lem3173821 (h1 : term87 = term47) : term87 = term47.
Proof. exact (h1). Qed.
Lemma lem3173885 (n : nat) (h1 : term124 n) : term124 n.
Proof. exact (h1). Qed.
Lemma lem3173886 (n : nat) (h1 : term116 n) : term116 n.
Proof. exact (h1). Qed.
Lemma lem3173887 (n : nat) (h1 : term120 n) : term120 n.
Proof. exact (h1). Qed.
Lemma lem3173895 (h1 : term99 = term63) : term99 = term63.
Proof. exact (h1). Qed.
Lemma lem3173915 (h1 : term87 = term47) : term87 = term47.
Proof. exact (h1). Qed.
Lemma lem3173925 (h1 : term99 = term63) : term99 = term63.
Proof. exact (h1). Qed.
Lemma lem3173935 (h1 : term87 = term47) : term87 = term47.
Proof. exact (h1). Qed.
Lemma lem3173939 (n : nat) (h1 : term120 n) : term86.
Proof. exact (proj2 (@lem3173887 n h1)). Qed.
Lemma lem3173967 (h1 : term99 = term63) : term99 = term63.
Proof. exact (h1). Qed.
Lemma lem3173995 (n : nat) (h1 : term116 n) : term112.
Proof. exact (proj2 (@lem3173886 n h1)). Qed.
Lemma lem3174033 (h1 : term99 = term63) : term99 = term63.
Proof. exact (h1). Qed.
Lemma lem3174034 (h1 : term99 = term63) : term203.
Proof. exact (fun h0 : term112 => @lem3174033 h1). Qed.
Lemma lem3174036 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3174037 : term203 = (term99 = term63).
Proof. exact (@lem3174036 (term99 = term63)). Qed.
Lemma lem3174038 (h1 : term99 = term63) : term99 = term63.
Proof. exact (EQ_MP (@lem3174037) (@lem3174034 h1)). Qed.
Lemma lem3174041 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3174043 : term112 = term205.
Proof. exact (@lem3174041 (term99 = term63)). Qed.
Lemma lem3174046 (n : nat) (h1 : term116 n) : term205.
Proof. exact (EQ_MP (@lem3174043) (@lem3173995 n h1)). Qed.
Lemma lem3174049 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : False.
Proof. exact (@lem3174046 n h1 (@lem3174038 h2)). Qed.
Lemma lem3174050 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : term206.
Proof. exact (fun h0 : ~ False => @lem3174049 n h1 h2). Qed.
Lemma lem3174052 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3174053 : term206 = False.
Proof. exact (@lem3174052 False). Qed.
Lemma lem3174054 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174053) (@lem3174050 n h1 h2)). Qed.
Lemma lem3174092 (h1 : term87 = term47) : term87 = term47.
Proof. exact (h1). Qed.
Lemma lem3174093 (h1 : term87 = term47) : term207.
Proof. exact (fun h0 : term86 => @lem3174092 h1). Qed.
Lemma lem3174095 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3174096 : term207 = (term87 = term47).
Proof. exact (@lem3174095 (term87 = term47)). Qed.
Lemma lem3174097 (h1 : term87 = term47) : term87 = term47.
Proof. exact (EQ_MP (@lem3174096) (@lem3174093 h1)). Qed.
Lemma lem3174100 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3174102 : term86 = term85.
Proof. exact (@lem3174100 (term87 = term47)). Qed.
Lemma lem3174105 (n : nat) (h1 : term120 n) : term85.
Proof. exact (EQ_MP (@lem3174102) (@lem3173939 n h1)). Qed.
Lemma lem3174108 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : False.
Proof. exact (@lem3174105 n h1 (@lem3174097 h2)). Qed.
Lemma lem3174109 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : term206.
Proof. exact (fun h0 : ~ False => @lem3174108 n h1 h2). Qed.
Lemma lem3174111 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3174112 : term206 = False.
Proof. exact (@lem3174111 False). Qed.
Lemma lem3174113 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : False.
Proof. exact (EQ_MP (@lem3174112) (@lem3174109 n h1 h2)). Qed.
Lemma lem3174114 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : (term99 = term63) = False.
Proof. exact (prop_ext (fun h3 : term99 = term63 => @lem3174054 n h1 h2) (fun h3 : False => @lem3173967 h2)). Qed.
Lemma lem3174116 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174114 n h1 h2) (@lem3173967 h2)). Qed.
Lemma lem3174117 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : (term87 = term47) = False.
Proof. exact (prop_ext (fun h3 : term87 = term47 => @lem3174113 n h1 h2) (fun h3 : False => @lem3173935 h2)). Qed.
Lemma lem3174118 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : False.
Proof. exact (EQ_MP (@lem3174117 n h1 h2) (@lem3173935 h2)). Qed.
Lemma lem3174119 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : (term99 = term63) = False.
Proof. exact (prop_ext (fun h3 : term99 = term63 => @lem3174116 n h1 h2) (fun h3 : False => @lem3173925 h2)). Qed.
Lemma lem3174120 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174119 n h1 h2) (@lem3173925 h2)). Qed.
Lemma lem3174121 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : (term87 = term47) = False.
Proof. exact (prop_ext (fun h3 : term87 = term47 => @lem3174118 n h1 h2) (fun h3 : False => @lem3173915 h2)). Qed.
Lemma lem3174122 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : False.
Proof. exact (EQ_MP (@lem3174121 n h1 h2) (@lem3173915 h2)). Qed.
Lemma lem3174123 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : (term99 = term63) = False.
Proof. exact (prop_ext (fun h3 : term99 = term63 => @lem3174120 n h1 h2) (fun h3 : False => @lem3173895 h2)). Qed.
Lemma lem3174124 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174123 n h1 h2) (@lem3173895 h2)). Qed.
Lemma lem3174125 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : (term87 = term47) = False.
Proof. exact (prop_ext (fun h3 : term87 = term47 => @lem3174122 n h1 h2) (fun h3 : False => @lem3173915 h2)). Qed.
Lemma lem3174126 (n : nat) (h1 : term120 n) (h2 : term87 = term47) : False.
Proof. exact (EQ_MP (@lem3174125 n h1 h2) (@lem3173915 h2)). Qed.
Lemma lem3174127 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : (term99 = term63) = False.
Proof. exact (prop_ext (fun h3 : term99 = term63 => @lem3174124 n h1 h2) (fun h3 : False => @lem3173895 h2)). Qed.
Lemma lem3174128 (n : nat) (h1 : term116 n) (h2 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174127 n h1 h2) (@lem3173895 h2)). Qed.
Lemma lem3174129 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : False.
Proof. exact (or_elim (@lem3173885 n h3) (fun h0 : term116 n => @lem3174128 n h0 h2) (fun h0 : term120 n => @lem3174126 n h0 h1)). Qed.
Lemma lem3174130 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : (term124 n) = False.
Proof. exact (prop_ext (fun h4 : term124 n => @lem3174129 n h1 h2 h3) (fun h4 : False => @lem3173885 n h3)). Qed.
Lemma lem3174131 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : False.
Proof. exact (EQ_MP (@lem3174130 n h1 h2 h3) (@lem3173885 n h3)). Qed.
Lemma lem3174132 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : (term87 = term47) = False.
Proof. exact (prop_ext (fun h4 : term87 = term47 => @lem3174131 n h1 h2 h3) (fun h4 : False => @lem3173821 h1)). Qed.
Lemma lem3174133 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : False.
Proof. exact (EQ_MP (@lem3174132 n h1 h2 h3) (@lem3173821 h1)). Qed.
Lemma lem3174134 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : (term99 = term63) = False.
Proof. exact (prop_ext (fun h4 : term99 = term63 => @lem3174133 n h1 h2 h3) (fun h4 : False => @lem3173805 h2)). Qed.
Lemma lem3174135 (n : nat) (h1 : term87 = term47) (h2 : term99 = term63) (h3 : term124 n) : False.
Proof. exact (EQ_MP (@lem3174134 n h1 h2 h3) (@lem3173805 h2)). Qed.
Lemma lem3174136 (h1 : term108) (h2 : term87 = term47) (h3 : term99 = term63) : False.
Proof. exact (ex_elim (@lem3173772 h1) (fun n : nat => fun h0 : term134 n => @lem3174135 n h2 h3 h0)). Qed.
Lemma lem3174137 (h1 : term108) (h2 : term87 = term47) (h3 : term99 = term63) : (term87 = term47) = False.
Proof. exact (prop_ext (fun h4 : term87 = term47 => @lem3174136 h1 h2 h3) (fun h4 : False => @lem3173784 h2)). Qed.
Lemma lem3174138 (h1 : term108) (h2 : term87 = term47) (h3 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174137 h1 h2 h3) (@lem3173784 h2)). Qed.
Lemma lem3174139 (h1 : term108) (h2 : term87 = term47) (h3 : term99 = term63) : (term99 = term63) = False.
Proof. exact (prop_ext (fun h4 : term99 = term63 => @lem3174138 h1 h2 h3) (fun h4 : False => @lem3173778 h3)). Qed.
Lemma lem3174140 (h1 : term108) (h2 : term87 = term47) (h3 : term99 = term63) : False.
Proof. exact (EQ_MP (@lem3174139 h1 h2 h3) (@lem3173778 h3)). Qed.
Lemma lem3174141 (h1 : term108) (h2 : term99 = term63) : term85.
Proof. exact (fun h0 : term87 = term47 => @lem3174140 h1 h0 h2). Qed.
Lemma lem3174142 : term85 = term86.
Proof. exact (@lem69 (term87 = term47)). Qed.
Lemma lem3174143 (h1 : term108) (h2 : term99 = term63) : term86.
Proof. exact (EQ_MP (@lem3174142) (@lem3174141 h1 h2)). Qed.
Lemma lem3174144 (h1 : term108) : term90.
Proof. exact (fun h0 : term99 = term63 => @lem3174143 h1 h0). Qed.
Lemma lem3174145 : term110.
Proof. exact (fun h0 : term108 => @lem3174144 h0). Qed.
Lemma lem3174146 : term81.
Proof. exact (EQ_MP (@lem3173529) (@lem3174145)). Qed.
Lemma lem3174148 : term81.
Proof. exact (@lem3173364 (@lem3174146)). Qed.
Lemma lem3174149 (h1 : term80) : term89.
Proof. exact (@lem3174148 (@lem3173349 h1)). Qed.
Lemma lem3174150 (h1 : term80) : term85.
Proof. exact (@lem3174149 h1 (@lem1592031)). Qed.
Lemma lem3174151 (h1 : term80) : False.
Proof. exact (@lem3174150 h1 (@lem1340073)). Qed.
Lemma lem3174152 (h1 : term80) : term80 = False.
Proof. exact (prop_ext (fun h2 : term80 => @lem3174151 h1) (fun h2 : False => @lem3173349 h1)). Qed.
Lemma lem3174153 (h1 : term80) : False.
Proof. exact (EQ_MP (@lem3174152 h1) (@lem3173349 h1)). Qed.
Lemma lem3174154 : term79.
Proof. exact (fun h0 : term80 => @lem3174153 h0). Qed.
Lemma lem3174155 : term76.
Proof. exact (EQ_MP (@lem3173348) (@lem3174154)). Qed.
Lemma lem3174156 : term59.
Proof. exact (EQ_MP (@lem3173344) (@lem3174155)). Qed.
Lemma lem3174157 : term27.
Proof. exact (EQ_MP (@lem3173232) (@lem3174156)). Qed.
