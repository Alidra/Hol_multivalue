Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_CASES_term_abbrevs.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem96156 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem96157 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem96158 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem96157 n) (@lem96156 n)). Qed.
Lemma lem96159 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem96163 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem96164 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem96163 n h1)). Qed.
Lemma lem96165 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem96166 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem96165 n h1)). Qed.
Lemma lem96167 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem96164 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem96166 n h1)). Qed.
Lemma lem96168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem96169 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem96168) (@lem96167 n)). Qed.
Lemma lem96170 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem96169 n)). Qed.
Lemma lem96171 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96172 : term6 = term7.
Proof. exact (MK_COMB (@lem96171) (@lem96170)). Qed.
Lemma lem96173 : term7.
Proof. exact (EQ_MP (@lem96172) (@lem75570)). Qed.
Lemma lem96174 (n : nat) : term8 n.
Proof. exact (@lem96173 n). Qed.
Lemma lem96175 (n : nat) : (term8 n) = (term3 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem96176 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem96175 n) (@lem96174 n)). Qed.
Lemma lem96177 (n : nat) : term9 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem96180 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem96181 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem96180 n h1)). Qed.
Lemma lem96182 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem96183 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem96182 n h1)). Qed.
Lemma lem96184 (n : nat) : ((NUMERAL 0) = (S n)) = ((S n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = (S n) => @lem96181 n h1) (fun h1 : (S n) = (NUMERAL 0) => @lem96183 n h1)). Qed.
Lemma lem96185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem96186 (n : nat) : (term3 n) = (term2 n).
Proof. exact (MK_COMB (@lem96185) (@lem96184 n)). Qed.
Lemma lem96187 (n : nat) : term2 n.
Proof. exact (EQ_MP (@lem96186 n) (@lem96176 n)). Qed.
Lemma lem96188 (n : nat) : term10 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem96206 : term11.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem96207 (m : nat) : term12 m.
Proof. exact (@lem96206 m). Qed.
Lemma lem96208 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem96209 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem96208 m) (@lem96207 m)). Qed.
Lemma lem96210 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem96209 m n). Qed.
Lemma lem96211 (m : nat) (n : nat) : (term14 m n) = ((term15 m n) = (term16 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem96213 : term17.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem96214 (m : nat) : term18 m.
Proof. exact (@lem96213 m). Qed.
Lemma lem96215 (m : nat) : (term18 m) = ((term19 m) = False).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem96218 (P : nat -> Prop) : term20 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96219 : term21.
Proof. exact (@lem96218 term22). Qed.
Lemma lem96220 : term23 = term24.
Proof. exact (eq_refl term23). Qed.
Lemma lem96221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96222 : term25 = term26.
Proof. exact (MK_COMB (@lem96221) (@lem96220)). Qed.
Lemma lem96223 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem96224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96225 (m : nat) : (term29 m) = (term30 m).
Proof. exact (MK_COMB (@lem96224) (@lem96223 m)). Qed.
Lemma lem96226 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem96227 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem96225 m) (@lem96226 m)). Qed.
Lemma lem96228 : term35 = term36.
Proof. exact (fun_ext (fun m : nat => @lem96227 m)). Qed.
Lemma lem96229 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96230 : term37 = term38.
Proof. exact (MK_COMB (@lem96229) (@lem96228)). Qed.
Lemma lem96231 : term39 = term40.
Proof. exact (MK_COMB (@lem96222) (@lem96230)). Qed.
Lemma lem96232 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96233 : term41 = term42.
Proof. exact (MK_COMB (@lem96232) (@lem96231)). Qed.
Lemma lem96234 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem96235 : term43 = term22.
Proof. exact (fun_ext (fun m : nat => @lem96234 m)). Qed.
Lemma lem96236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96237 : term44 = term45.
Proof. exact (MK_COMB (@lem96236) (@lem96235)). Qed.
Lemma lem96238 : term21 = term46.
Proof. exact (MK_COMB (@lem96233) (@lem96237)). Qed.
Lemma lem96239 : term46.
Proof. exact (EQ_MP (@lem96238) (@lem96219)). Qed.
Lemma lem96240 (m : nat) (h1 : term28 m) : term28 m.
Proof. exact (h1). Qed.
Lemma lem96242 (P : nat -> Prop) : term20 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96243 : term47.
Proof. exact (@lem96242 term48). Qed.
Lemma lem96244 : term49 = term50.
Proof. exact (eq_refl term49). Qed.
Lemma lem96245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96246 : term51 = term52.
Proof. exact (MK_COMB (@lem96245) (@lem96244)). Qed.
Lemma lem96247 (n : nat) : (term53 n) = (term54 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem96248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96249 (n : nat) : (term55 n) = (term56 n).
Proof. exact (MK_COMB (@lem96248) (@lem96247 n)). Qed.
Lemma lem96250 (n : nat) : (term57 n) = (term58 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem96251 (n : nat) : (term59 n) = (term60 n).
Proof. exact (MK_COMB (@lem96249 n) (@lem96250 n)). Qed.
Lemma lem96252 : term61 = term62.
Proof. exact (fun_ext (fun n : nat => @lem96251 n)). Qed.
Lemma lem96253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96254 : term63 = term64.
Proof. exact (MK_COMB (@lem96253) (@lem96252)). Qed.
Lemma lem96255 : term65 = term66.
Proof. exact (MK_COMB (@lem96246) (@lem96254)). Qed.
Lemma lem96256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96257 : term67 = term68.
Proof. exact (MK_COMB (@lem96256) (@lem96255)). Qed.
Lemma lem96258 (n : nat) : (term53 n) = (term54 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem96259 : term69 = term48.
Proof. exact (fun_ext (fun n : nat => @lem96258 n)). Qed.
Lemma lem96260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96261 : term70 = term24.
Proof. exact (MK_COMB (@lem96260) (@lem96259)). Qed.
Lemma lem96262 : term47 = term71.
Proof. exact (MK_COMB (@lem96257) (@lem96261)). Qed.
Lemma lem96263 : term71.
Proof. exact (EQ_MP (@lem96262) (@lem96243)). Qed.
Lemma lem96270 (P : nat -> Prop) : term20 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96271 (m : nat) : term72 m.
Proof. exact (@lem96270 (term73 m)). Qed.
Lemma lem96272 (m : nat) : (term74 m) = (term75 m).
Proof. exact (eq_refl (term74 m)). Qed.
Lemma lem96273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96274 (m : nat) : (term76 m) = (term77 m).
Proof. exact (MK_COMB (@lem96273) (@lem96272 m)). Qed.
Lemma lem96275 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem96276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96277 (m : nat) (n : nat) : (term80 m n) = (term81 m n).
Proof. exact (MK_COMB (@lem96276) (@lem96275 m n)). Qed.
Lemma lem96278 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem96279 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem96277 m n) (@lem96278 m n)). Qed.
Lemma lem96280 (m : nat) : (term86 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem96279 m n)). Qed.
Lemma lem96281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96282 (m : nat) : (term88 m) = (term89 m).
Proof. exact (MK_COMB (@lem96281) (@lem96280 m)). Qed.
Lemma lem96283 (m : nat) : (term90 m) = (term91 m).
Proof. exact (MK_COMB (@lem96274 m) (@lem96282 m)). Qed.
Lemma lem96284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96285 (m : nat) : (term92 m) = (term93 m).
Proof. exact (MK_COMB (@lem96284) (@lem96283 m)). Qed.
Lemma lem96286 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem96287 (m : nat) : (term94 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem96286 m n)). Qed.
Lemma lem96288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96289 (m : nat) : (term95 m) = (term32 m).
Proof. exact (MK_COMB (@lem96288) (@lem96287 m)). Qed.
Lemma lem96290 (m : nat) : (term72 m) = (term96 m).
Proof. exact (MK_COMB (@lem96285 m) (@lem96289 m)). Qed.
Lemma lem96291 (m : nat) : term96 m.
Proof. exact (EQ_MP (@lem96290 m) (@lem96271 m)). Qed.
Lemma lem96314 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem96315 (x : nat) : (x = x) = True.
Proof. exact (@lem96314 nat x). Qed.
Lemma lem96316 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem96315 (NUMERAL 0)). Qed.
Lemma lem96317 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem96318 : term98 = term99.
Proof. exact (MK_COMB (@lem96317) (@lem96316)). Qed.
Lemma lem96320 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem96321 : term99 = True.
Proof. exact (@lem96320 term100). Qed.
Lemma lem96322 : term98 = True.
Proof. exact (TRANS (@lem96318) (@lem96321)). Qed.
Lemma lem96323 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem96324 : term50 = term99.
Proof. exact (MK_COMB (@lem96323) (@lem96322)). Qed.
Lemma lem96326 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem96327 : term99 = True.
Proof. exact (@lem96326 term100). Qed.
Lemma lem96328 : term50 = True.
Proof. exact (TRANS (@lem96324) (@lem96327)). Qed.
Lemma lem96329 : True = term50.
Proof. exact (SYM (@lem96328)). Qed.
Lemma lem96330 : term50.
Proof. exact (EQ_MP (@lem96329) (@lem0)). Qed.
Lemma lem96378 (m : nat) : term101 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem96379 (m : nat) : (term101 m) = (term102 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem96380 (m : nat) : term102 m.
Proof. exact (EQ_MP (@lem96379 m) (@lem96378 m)). Qed.
Lemma lem96381 (m : nat) (n : nat) : term103 m n.
Proof. exact (@lem96380 m n). Qed.
Lemma lem96382 (m : nat) (n : nat) : (term103 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term103 m n)). Qed.
Lemma lem96384 (m : nat) : term104 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem96385 (m : nat) : (term104 m) = (term105 m).
Proof. exact (eq_refl (term104 m)). Qed.
Lemma lem96386 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem96385 m) (@lem96384 m)). Qed.
Lemma lem96387 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem96386 m n). Qed.
Lemma lem96388 (m : nat) (n : nat) : (term106 m n) = ((term107 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem96390 (n : nat) (m : nat) (h1 : term28 m) : term108 m n.
Proof. exact (@lem96240 m h1 n). Qed.
Lemma lem96391 (m : nat) (n : nat) : (term108 m n) = (term109 m n).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem96392 (n : nat) (m : nat) (h1 : term28 m) : term109 m n.
Proof. exact (EQ_MP (@lem96391 m n) (@lem96390 n m h1)). Qed.
Lemma lem96393 (m : nat) (n : nat) : (term109 m n) = ((term109 m n) = True).
Proof. exact (@lem7 (term109 m n)). Qed.
Lemma lem96400 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem96388 m n) (@lem96387 m n)). Qed.
Lemma lem96401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96402 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem96401) (@lem96400 m n)). Qed.
Lemma lem96406 (m : nat) (n : nat) : (term107 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem96388 m n) (@lem96387 m n)). Qed.
Lemma lem96407 (n : nat) (m : nat) : (term107 n m) = (Peano.lt n m).
Proof. exact (@lem96406 n m). Qed.
Lemma lem96408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96409 (n : nat) (m : nat) : (term110 n m) = (term111 n m).
Proof. exact (MK_COMB (@lem96408) (@lem96407 n m)). Qed.
Lemma lem96411 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem96382 m n) (@lem96381 m n)). Qed.
Lemma lem96414 (m : nat) (n : nat) : (term112 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem96409 n m) (@lem96411 m n)). Qed.
Lemma lem96417 (m : nat) (n : nat) : (term83 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem96402 m n) (@lem96414 m n)). Qed.
Lemma lem96419 (n : nat) (m : nat) (h1 : term28 m) : (term109 m n) = True.
Proof. exact (EQ_MP (@lem96393 m n) (@lem96392 n m h1)). Qed.
Lemma lem96420 (n : nat) (m : nat) (h1 : term28 m) : (term83 m n) = True.
Proof. exact (TRANS (@lem96417 m n) (@lem96419 n m h1)). Qed.
Lemma lem96421 (n : nat) (m : nat) (h1 : term28 m) : True = (term83 m n).
Proof. exact (SYM (@lem96420 n m h1)). Qed.
Lemma lem96422 (n : nat) (m : nat) (h1 : term28 m) : term83 m n.
Proof. exact (EQ_MP (@lem96421 n m h1) (@lem0)). Qed.
Lemma lem96426 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem96211 m n) (@lem96210 m n)). Qed.
Lemma lem96427 (n : nat) : (term1 n) = (term114 n).
Proof. exact (@lem96426 (NUMERAL 0) n). Qed.
Lemma lem96432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96433 (n : nat) : (term115 n) = (term116 n).
Proof. exact (MK_COMB (@lem96432) (@lem96427 n)). Qed.
Lemma lem96437 (m : nat) : (term19 m) = False.
Proof. exact (EQ_MP (@lem96215 m) (@lem96214 m)). Qed.
Lemma lem96438 (n : nat) : (term117 n) = False.
Proof. exact (@lem96437 (S n)). Qed.
Lemma lem96439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96440 (n : nat) : (term118 n) = (or False).
Proof. exact (MK_COMB (@lem96439) (@lem96438 n)). Qed.
Lemma lem96442 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem96177 n (@lem96176 n)). Qed.
Lemma lem96443 (n : nat) : (term119 n) = (False \/ False).
Proof. exact (MK_COMB (@lem96440 n) (@lem96442 n)). Qed.
Lemma lem96445 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem96446 : (False \/ False) = False.
Proof. exact (@lem96445 False). Qed.
Lemma lem96447 (n : nat) : (term119 n) = False.
Proof. exact (TRANS (@lem96443 n) (@lem96446)). Qed.
Lemma lem96448 (n : nat) : (term58 n) = (term120 n).
Proof. exact (MK_COMB (@lem96433 n) (@lem96447 n)). Qed.
Lemma lem96450 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem96451 (n : nat) : (term120 n) = (term114 n).
Proof. exact (@lem96450 (term114 n)). Qed.
Lemma lem96456 (n : nat) : (term58 n) = (term114 n).
Proof. exact (TRANS (@lem96448 n) (@lem96451 n)). Qed.
Lemma lem96457 (n : nat) : (term114 n) = (term58 n).
Proof. exact (SYM (@lem96456 n)). Qed.
Lemma lem96461 (m : nat) : (term19 m) = False.
Proof. exact (EQ_MP (@lem96215 m) (@lem96214 m)). Qed.
Lemma lem96462 (m : nat) : (term117 m) = False.
Proof. exact (@lem96461 (S m)). Qed.
Lemma lem96463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96464 (m : nat) : (term118 m) = (or False).
Proof. exact (MK_COMB (@lem96463) (@lem96462 m)). Qed.
Lemma lem96468 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem96211 m n) (@lem96210 m n)). Qed.
Lemma lem96469 (m : nat) : (term1 m) = (term114 m).
Proof. exact (@lem96468 (NUMERAL 0) m). Qed.
Lemma lem96474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96475 (m : nat) : (term115 m) = (term116 m).
Proof. exact (MK_COMB (@lem96474) (@lem96469 m)). Qed.
Lemma lem96477 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem96188 n (@lem96187 n)). Qed.
Lemma lem96478 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem96477 m). Qed.
Lemma lem96479 (m : nat) : (term121 m) = (term120 m).
Proof. exact (MK_COMB (@lem96475 m) (@lem96478 m)). Qed.
Lemma lem96481 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem96482 (m : nat) : (term120 m) = (term114 m).
Proof. exact (@lem96481 (term114 m)). Qed.
Lemma lem96487 (m : nat) : (term121 m) = (term114 m).
Proof. exact (TRANS (@lem96479 m) (@lem96482 m)). Qed.
Lemma lem96488 (m : nat) : (term75 m) = (term122 m).
Proof. exact (MK_COMB (@lem96464 m) (@lem96487 m)). Qed.
Lemma lem96490 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem96491 (m : nat) : (term122 m) = (term114 m).
Proof. exact (@lem96490 (term114 m)). Qed.
Lemma lem96496 (m : nat) : (term75 m) = (term114 m).
Proof. exact (TRANS (@lem96488 m) (@lem96491 m)). Qed.
Lemma lem96497 (m : nat) : (term114 m) = (term75 m).
Proof. exact (SYM (@lem96496 m)). Qed.
Lemma lem96499 (P : nat -> Prop) : term20 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96500 : term123.
Proof. exact (@lem96499 term124). Qed.
Lemma lem96501 : term125 = term126.
Proof. exact (eq_refl term125). Qed.
Lemma lem96502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96503 : term127 = term128.
Proof. exact (MK_COMB (@lem96502) (@lem96501)). Qed.
Lemma lem96504 (n : nat) : (term129 n) = (term114 n).
Proof. exact (eq_refl (term129 n)). Qed.
Lemma lem96505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96506 (n : nat) : (term130 n) = (term131 n).
Proof. exact (MK_COMB (@lem96505) (@lem96504 n)). Qed.
Lemma lem96507 (n : nat) : (term132 n) = (term133 n).
Proof. exact (eq_refl (term132 n)). Qed.
Lemma lem96508 (n : nat) : (term134 n) = (term135 n).
Proof. exact (MK_COMB (@lem96506 n) (@lem96507 n)). Qed.
Lemma lem96509 : term136 = term137.
Proof. exact (fun_ext (fun n : nat => @lem96508 n)). Qed.
Lemma lem96510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96511 : term138 = term139.
Proof. exact (MK_COMB (@lem96510) (@lem96509)). Qed.
Lemma lem96512 : term140 = term141.
Proof. exact (MK_COMB (@lem96503) (@lem96511)). Qed.
Lemma lem96513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96514 : term142 = term143.
Proof. exact (MK_COMB (@lem96513) (@lem96512)). Qed.
Lemma lem96515 (n : nat) : (term129 n) = (term114 n).
Proof. exact (eq_refl (term129 n)). Qed.
Lemma lem96516 : term144 = term124.
Proof. exact (fun_ext (fun n : nat => @lem96515 n)). Qed.
Lemma lem96517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96518 : term145 = term146.
Proof. exact (MK_COMB (@lem96517) (@lem96516)). Qed.
Lemma lem96519 : term123 = term147.
Proof. exact (MK_COMB (@lem96514) (@lem96518)). Qed.
Lemma lem96520 : term147.
Proof. exact (EQ_MP (@lem96519) (@lem96500)). Qed.
Lemma lem96523 (P : nat -> Prop) : term20 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96524 : term123.
Proof. exact (@lem96523 term124). Qed.
Lemma lem96525 : term125 = term126.
Proof. exact (eq_refl term125). Qed.
Lemma lem96526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96527 : term127 = term128.
Proof. exact (MK_COMB (@lem96526) (@lem96525)). Qed.
Lemma lem96528 (m : nat) : (term129 m) = (term114 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem96529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96530 (m : nat) : (term130 m) = (term131 m).
Proof. exact (MK_COMB (@lem96529) (@lem96528 m)). Qed.
Lemma lem96531 (m : nat) : (term132 m) = (term133 m).
Proof. exact (eq_refl (term132 m)). Qed.
Lemma lem96532 (m : nat) : (term134 m) = (term135 m).
Proof. exact (MK_COMB (@lem96530 m) (@lem96531 m)). Qed.
Lemma lem96533 : term136 = term137.
Proof. exact (fun_ext (fun m : nat => @lem96532 m)). Qed.
Lemma lem96534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96535 : term138 = term139.
Proof. exact (MK_COMB (@lem96534) (@lem96533)). Qed.
Lemma lem96536 : term140 = term141.
Proof. exact (MK_COMB (@lem96527) (@lem96535)). Qed.
Lemma lem96537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96538 : term142 = term143.
Proof. exact (MK_COMB (@lem96537) (@lem96536)). Qed.
Lemma lem96539 (m : nat) : (term129 m) = (term114 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem96540 : term144 = term124.
Proof. exact (fun_ext (fun m : nat => @lem96539 m)). Qed.
Lemma lem96541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96542 : term145 = term146.
Proof. exact (MK_COMB (@lem96541) (@lem96540)). Qed.
Lemma lem96543 : term123 = term147.
Proof. exact (MK_COMB (@lem96538) (@lem96542)). Qed.
Lemma lem96544 : term147.
Proof. exact (EQ_MP (@lem96543) (@lem96524)). Qed.
Lemma lem96549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem96550 (x : nat) : (x = x) = True.
Proof. exact (@lem96549 nat x). Qed.
Lemma lem96551 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem96550 (NUMERAL 0)). Qed.
Lemma lem96552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96553 : term148 = (or True).
Proof. exact (MK_COMB (@lem96552) (@lem96551)). Qed.
Lemma lem96554 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem96555 : term126 = term149.
Proof. exact (MK_COMB (@lem96553) (@lem96554)). Qed.
Lemma lem96557 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem96558 : term149 = True.
Proof. exact (@lem96557 term100). Qed.
Lemma lem96559 : term126 = True.
Proof. exact (TRANS (@lem96555) (@lem96558)). Qed.
Lemma lem96560 : True = term126.
Proof. exact (SYM (@lem96559)). Qed.
Lemma lem96561 : term126.
Proof. exact (EQ_MP (@lem96560) (@lem0)). Qed.
Lemma lem96567 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem96159 n) (@lem96158 n)). Qed.
Lemma lem96568 (n' : nat) : (term1 n') = True.
Proof. exact (@lem96567 n'). Qed.
Lemma lem96569 (n' : nat) : (term150 n') = (term150 n').
Proof. exact (eq_refl (term150 n')). Qed.
Lemma lem96570 (n' : nat) : (term133 n') = (term151 n').
Proof. exact (MK_COMB (@lem96569 n') (@lem96568 n')). Qed.
Lemma lem96572 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem96573 (n' : nat) : (term151 n') = True.
Proof. exact (@lem96572 ((NUMERAL 0) = (S n'))). Qed.
Lemma lem96574 (n' : nat) : (term133 n') = True.
Proof. exact (TRANS (@lem96570 n') (@lem96573 n')). Qed.
Lemma lem96575 (n' : nat) : True = (term133 n').
Proof. exact (SYM (@lem96574 n')). Qed.
Lemma lem96576 (n' : nat) : term133 n'.
Proof. exact (EQ_MP (@lem96575 n') (@lem0)). Qed.
Lemma lem96580 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem96581 (x : nat) : (x = x) = True.
Proof. exact (@lem96580 nat x). Qed.
Lemma lem96582 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem96581 (NUMERAL 0)). Qed.
Lemma lem96583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96584 : term148 = (or True).
Proof. exact (MK_COMB (@lem96583) (@lem96582)). Qed.
Lemma lem96585 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem96586 : term126 = term149.
Proof. exact (MK_COMB (@lem96584) (@lem96585)). Qed.
Lemma lem96588 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem96589 : term149 = True.
Proof. exact (@lem96588 term100). Qed.
Lemma lem96590 : term126 = True.
Proof. exact (TRANS (@lem96586) (@lem96589)). Qed.
Lemma lem96591 : True = term126.
Proof. exact (SYM (@lem96590)). Qed.
Lemma lem96592 : term126.
Proof. exact (EQ_MP (@lem96591) (@lem0)). Qed.
Lemma lem96598 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem96159 n) (@lem96158 n)). Qed.
Lemma lem96599 (m' : nat) : (term1 m') = True.
Proof. exact (@lem96598 m'). Qed.
Lemma lem96600 (m' : nat) : (term150 m') = (term150 m').
Proof. exact (eq_refl (term150 m')). Qed.
Lemma lem96601 (m' : nat) : (term133 m') = (term151 m').
Proof. exact (MK_COMB (@lem96600 m') (@lem96599 m')). Qed.
Lemma lem96603 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem96604 (m' : nat) : (term151 m') = True.
Proof. exact (@lem96603 ((NUMERAL 0) = (S m'))). Qed.
Lemma lem96605 (m' : nat) : (term133 m') = True.
Proof. exact (TRANS (@lem96601 m') (@lem96604 m')). Qed.
Lemma lem96606 (m' : nat) : True = (term133 m').
Proof. exact (SYM (@lem96605 m')). Qed.
Lemma lem96607 (m' : nat) : term133 m'.
Proof. exact (EQ_MP (@lem96606 m') (@lem0)). Qed.
Lemma lem96608 (m' : nat) : term135 m'.
Proof. exact (fun h0 : term114 m' => @lem96607 m'). Qed.
Lemma lem96613 : term139.
Proof. exact (fun m' : nat => @lem96608 m'). Qed.
Lemma lem96614 : term141.
Proof. exact (conj (@lem96592) (@lem96613)). Qed.
Lemma lem96615 : term146.
Proof. exact (@lem96544 (@lem96614)). Qed.
Lemma lem96616 (n' : nat) : term135 n'.
Proof. exact (fun h0 : term114 n' => @lem96576 n'). Qed.
Lemma lem96621 : term139.
Proof. exact (fun n' : nat => @lem96616 n'). Qed.
Lemma lem96622 : term141.
Proof. exact (conj (@lem96561) (@lem96621)). Qed.
Lemma lem96623 : term146.
Proof. exact (@lem96520 (@lem96622)). Qed.
Lemma lem96624 (m : nat) : term129 m.
Proof. exact (@lem96615 m). Qed.
Lemma lem96625 (m : nat) : (term129 m) = (term114 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem96626 (m : nat) : term114 m.
Proof. exact (EQ_MP (@lem96625 m) (@lem96624 m)). Qed.
Lemma lem96627 (n : nat) : term129 n.
Proof. exact (@lem96623 n). Qed.
Lemma lem96628 (n : nat) : (term129 n) = (term114 n).
Proof. exact (eq_refl (term129 n)). Qed.
Lemma lem96629 (n : nat) : term114 n.
Proof. exact (EQ_MP (@lem96628 n) (@lem96627 n)). Qed.
Lemma lem96632 (m : nat) : term75 m.
Proof. exact (EQ_MP (@lem96497 m) (@lem96626 m)). Qed.
Lemma lem96633 (n : nat) : term58 n.
Proof. exact (EQ_MP (@lem96457 n) (@lem96629 n)). Qed.
Lemma lem96634 (n : nat) (m : nat) (h1 : term28 m) : term85 m n.
Proof. exact (fun h0 : term79 m n => @lem96422 n m h1). Qed.
Lemma lem96639 (m : nat) (h1 : term28 m) : term89 m.
Proof. exact (fun n : nat => @lem96634 n m h1). Qed.
Lemma lem96640 (m : nat) (h1 : term28 m) : term91 m.
Proof. exact (conj (@lem96632 m) (@lem96639 m h1)). Qed.
Lemma lem96641 (m : nat) (h1 : term28 m) : term32 m.
Proof. exact (@lem96291 m (@lem96640 m h1)). Qed.
Lemma lem96642 (n : nat) : term60 n.
Proof. exact (fun h0 : term54 n => @lem96633 n). Qed.
Lemma lem96647 : term64.
Proof. exact (fun n : nat => @lem96642 n). Qed.
Lemma lem96648 : term66.
Proof. exact (conj (@lem96330) (@lem96647)). Qed.
Lemma lem96649 : term24.
Proof. exact (@lem96263 (@lem96648)). Qed.
Lemma lem96650 (m : nat) : term34 m.
Proof. exact (fun h0 : term28 m => @lem96641 m h0). Qed.
Lemma lem96655 : term38.
Proof. exact (fun m : nat => @lem96650 m). Qed.
Lemma lem96656 : term40.
Proof. exact (conj (@lem96649) (@lem96655)). Qed.
Lemma lem96657 : term45.
Proof. exact (@lem96239 (@lem96656)). Qed.
