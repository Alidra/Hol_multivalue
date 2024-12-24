Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm940073_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm512818_spec.
Require Import thm513870_spec.
Require Import thm514290_spec.
Require Import thm514761_spec.
Require Import thm515543_spec.
Require Import thm515916_spec.
Require Import thm516204_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem939075 : term0.
Proof. exact (EQ_MP (@lem515916) (@lem516204)). Qed.
Lemma lem939076 : term1.
Proof. exact (proj2 (@lem939075)). Qed.
Lemma lem939077 : term2.
Proof. exact (proj2 (@lem939076)). Qed.
Lemma lem939078 : term3.
Proof. exact (proj2 (@lem939077)). Qed.
Lemma lem939079 : term4.
Proof. exact (proj2 (@lem939078)). Qed.
Lemma lem939080 : term5.
Proof. exact (proj2 (@lem939079)). Qed.
Lemma lem939081 : term6.
Proof. exact (proj2 (@lem939080)). Qed.
Lemma lem939082 : term7.
Proof. exact (proj2 (@lem939081)). Qed.
Lemma lem939083 : term8.
Proof. exact (proj2 (@lem939082)). Qed.
Lemma lem939084 : term9.
Proof. exact (proj2 (@lem939083)). Qed.
Lemma lem939085 (m : nat) : term10 m.
Proof. exact (@lem939084 m). Qed.
Lemma lem939086 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem939087 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem939086 m) (@lem939085 m)). Qed.
Lemma lem939088 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem939087 m n). Qed.
Lemma lem939089 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem939102 : term15.
Proof. exact (proj1 (@lem939081)). Qed.
Lemma lem939103 (m : nat) : term16 m.
Proof. exact (@lem939102 m). Qed.
Lemma lem939104 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem939105 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem939104 m) (@lem939103 m)). Qed.
Lemma lem939106 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem939105 m n). Qed.
Lemma lem939107 (m : nat) (n : nat) : (term18 m n) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem939120 : term21.
Proof. exact (proj1 (@lem939078)). Qed.
Lemma lem939121 (m : nat) : term22 m.
Proof. exact (@lem939120 m). Qed.
Lemma lem939122 (m : nat) : (term22 m) = ((term23 m) = (BIT1 0)).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem939129 : term24.
Proof. exact (proj1 (@lem939075)). Qed.
Lemma lem939130 (m : nat) : term25 m.
Proof. exact (@lem939129 m). Qed.
Lemma lem939131 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem939132 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem939131 m) (@lem939130 m)). Qed.
Lemma lem939133 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem939132 m n). Qed.
Lemma lem939134 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (term29 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem939136 : term30.
Proof. exact (EQ_MP (@lem514761) (@lem515543)). Qed.
Lemma lem939137 : term31.
Proof. exact (proj2 (@lem939136)). Qed.
Lemma lem939138 : term32.
Proof. exact (proj2 (@lem939137)). Qed.
Lemma lem939139 : term33.
Proof. exact (proj2 (@lem939138)). Qed.
Lemma lem939140 : term34.
Proof. exact (proj2 (@lem939139)). Qed.
Lemma lem939141 : term35.
Proof. exact (proj2 (@lem939140)). Qed.
Lemma lem939142 : term36.
Proof. exact (proj2 (@lem939141)). Qed.
Lemma lem939143 : term37.
Proof. exact (proj2 (@lem939142)). Qed.
Lemma lem939144 : term38.
Proof. exact (proj2 (@lem939143)). Qed.
Lemma lem939145 : term39.
Proof. exact (proj2 (@lem939144)). Qed.
Lemma lem939146 (m : nat) : term40 m.
Proof. exact (@lem939145 m). Qed.
Lemma lem939147 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem939148 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem939147 m) (@lem939146 m)). Qed.
Lemma lem939149 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem939148 m n). Qed.
Lemma lem939150 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (term44 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem939197 : term45.
Proof. exact (EQ_MP (@lem513870) (@lem514290)). Qed.
Lemma lem939198 : term46.
Proof. exact (proj2 (@lem939197)). Qed.
Lemma lem939199 : term47.
Proof. exact (proj2 (@lem939198)). Qed.
Lemma lem939200 : term48.
Proof. exact (proj2 (@lem939199)). Qed.
Lemma lem939201 : term49.
Proof. exact (proj2 (@lem939200)). Qed.
Lemma lem939202 : term50.
Proof. exact (proj2 (@lem939201)). Qed.
Lemma lem939203 : term51.
Proof. exact (proj2 (@lem939202)). Qed.
Lemma lem939227 : term52.
Proof. exact (proj1 (@lem939203)). Qed.
Lemma lem939228 (m : nat) : term53 m.
Proof. exact (@lem939227 m). Qed.
Lemma lem939229 (m : nat) : (term53 m) = (term54 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem939230 (m : nat) : term54 m.
Proof. exact (EQ_MP (@lem939229 m) (@lem939228 m)). Qed.
Lemma lem939231 (m : nat) (n : nat) : term55 m n.
Proof. exact (@lem939230 m n). Qed.
Lemma lem939232 (m : nat) (n : nat) : (term55 m n) = ((term56 m n) = (term57 m n)).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem939234 : term58.
Proof. exact (proj1 (@lem939202)). Qed.
Lemma lem939235 (n : nat) : term59 n.
Proof. exact (@lem939234 n). Qed.
Lemma lem939236 (n : nat) : (term59 n) = ((term60 n) = (BIT1 n)).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem939246 : term61.
Proof. exact (proj1 (@lem939199)). Qed.
Lemma lem939247 (n : nat) : term62 n.
Proof. exact (@lem939246 n). Qed.
Lemma lem939248 (n : nat) : (term62 n) = ((term63 n) = (BIT0 n)).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem939290 : term64.
Proof. exact (EQ_MP (@lem512818) (@lem0)). Qed.
Lemma lem939294 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem939134 m n) (@lem939133 m n)). Qed.
Lemma lem939295 : term65 = term66.
Proof. exact (@lem939294 (BIT1 0) term67). Qed.
Lemma lem939297 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem939107 m n) (@lem939106 m n)). Qed.
Lemma lem939298 : term68 = term69.
Proof. exact (@lem939297 0 (BIT1 0)). Qed.
Lemma lem939300 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem939089 m n) (@lem939088 m n)). Qed.
Lemma lem939301 : term70 = term71.
Proof. exact (@lem939300 0 0). Qed.
Lemma lem939303 (m : nat) : (term23 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem939122 m) (@lem939121 m)). Qed.
Lemma lem939304 : term72 = (BIT1 0).
Proof. exact (@lem939303 0). Qed.
Lemma lem939305 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem939306 : term73 = term74.
Proof. exact (MK_COMB (@lem939305) (@lem939304)). Qed.
Lemma lem939308 (m : nat) : (term23 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem939122 m) (@lem939121 m)). Qed.
Lemma lem939309 : term72 = (BIT1 0).
Proof. exact (@lem939308 0). Qed.
Lemma lem939310 : term75 = term76.
Proof. exact (MK_COMB (@lem939306) (@lem939309)). Qed.
Lemma lem939312 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem939150 m n) (@lem939149 m n)). Qed.
Lemma lem939313 : term76 = term77.
Proof. exact (@lem939312 0 0). Qed.
Lemma lem939315 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (EQ_MP (@lem939232 m n) (@lem939231 m n)). Qed.
Lemma lem939316 : term78 = term79.
Proof. exact (@lem939315 0 term80). Qed.
Lemma lem939318 (n : nat) : (term63 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem939248 n) (@lem939247 n)). Qed.
Lemma lem939319 : term81 = term80.
Proof. exact (@lem939318 (Nat.mul 0 0)). Qed.
Lemma lem939321 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem939137)). Qed.
Lemma lem939322 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939323 : term80 = (BIT0 0).
Proof. exact (MK_COMB (@lem939322) (@lem939321)). Qed.
Lemma lem939325 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939326 : term80 = 0.
Proof. exact (TRANS (@lem939323) (@lem939325)). Qed.
Lemma lem939327 : term81 = 0.
Proof. exact (TRANS (@lem939319) (@lem939326)). Qed.
Lemma lem939328 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939329 : term79 = (BIT0 0).
Proof. exact (MK_COMB (@lem939328) (@lem939327)). Qed.
Lemma lem939331 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939332 : term79 = 0.
Proof. exact (TRANS (@lem939329) (@lem939331)). Qed.
Lemma lem939333 : term78 = 0.
Proof. exact (TRANS (@lem939316) (@lem939332)). Qed.
Lemma lem939334 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem939335 : term77 = term83.
Proof. exact (MK_COMB (@lem939334) (@lem939333)). Qed.
Lemma lem939337 (n : nat) : (term60 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem939236 n) (@lem939235 n)). Qed.
Lemma lem939338 : term83 = (BIT1 0).
Proof. exact (@lem939337 0). Qed.
Lemma lem939339 : term77 = (BIT1 0).
Proof. exact (TRANS (@lem939335) (@lem939338)). Qed.
Lemma lem939340 : term76 = (BIT1 0).
Proof. exact (TRANS (@lem939313) (@lem939339)). Qed.
Lemma lem939341 : term75 = (BIT1 0).
Proof. exact (TRANS (@lem939310) (@lem939340)). Qed.
Lemma lem939342 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem939343 : term71 = term76.
Proof. exact (MK_COMB (@lem939342) (@lem939341)). Qed.
Lemma lem939345 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem939150 m n) (@lem939149 m n)). Qed.
Lemma lem939346 : term76 = term77.
Proof. exact (@lem939345 0 0). Qed.
Lemma lem939348 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (EQ_MP (@lem939232 m n) (@lem939231 m n)). Qed.
Lemma lem939349 : term78 = term79.
Proof. exact (@lem939348 0 term80). Qed.
Lemma lem939351 (n : nat) : (term63 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem939248 n) (@lem939247 n)). Qed.
Lemma lem939352 : term81 = term80.
Proof. exact (@lem939351 (Nat.mul 0 0)). Qed.
Lemma lem939354 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem939137)). Qed.
Lemma lem939355 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939356 : term80 = (BIT0 0).
Proof. exact (MK_COMB (@lem939355) (@lem939354)). Qed.
Lemma lem939358 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939359 : term80 = 0.
Proof. exact (TRANS (@lem939356) (@lem939358)). Qed.
Lemma lem939360 : term81 = 0.
Proof. exact (TRANS (@lem939352) (@lem939359)). Qed.
Lemma lem939361 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939362 : term79 = (BIT0 0).
Proof. exact (MK_COMB (@lem939361) (@lem939360)). Qed.
Lemma lem939364 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939365 : term79 = 0.
Proof. exact (TRANS (@lem939362) (@lem939364)). Qed.
Lemma lem939366 : term78 = 0.
Proof. exact (TRANS (@lem939349) (@lem939365)). Qed.
Lemma lem939367 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem939368 : term77 = term83.
Proof. exact (MK_COMB (@lem939367) (@lem939366)). Qed.
Lemma lem939370 (n : nat) : (term60 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem939236 n) (@lem939235 n)). Qed.
Lemma lem939371 : term83 = (BIT1 0).
Proof. exact (@lem939370 0). Qed.
Lemma lem939372 : term77 = (BIT1 0).
Proof. exact (TRANS (@lem939368) (@lem939371)). Qed.
Lemma lem939373 : term76 = (BIT1 0).
Proof. exact (TRANS (@lem939346) (@lem939372)). Qed.
Lemma lem939374 : term71 = (BIT1 0).
Proof. exact (TRANS (@lem939343) (@lem939373)). Qed.
Lemma lem939375 : term70 = (BIT1 0).
Proof. exact (TRANS (@lem939301) (@lem939374)). Qed.
Lemma lem939376 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem939377 : term84 = term74.
Proof. exact (MK_COMB (@lem939376) (@lem939375)). Qed.
Lemma lem939379 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem939089 m n) (@lem939088 m n)). Qed.
Lemma lem939380 : term70 = term71.
Proof. exact (@lem939379 0 0). Qed.
Lemma lem939382 (m : nat) : (term23 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem939122 m) (@lem939121 m)). Qed.
Lemma lem939383 : term72 = (BIT1 0).
Proof. exact (@lem939382 0). Qed.
Lemma lem939384 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem939385 : term73 = term74.
Proof. exact (MK_COMB (@lem939384) (@lem939383)). Qed.
Lemma lem939387 (m : nat) : (term23 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem939122 m) (@lem939121 m)). Qed.
Lemma lem939388 : term72 = (BIT1 0).
Proof. exact (@lem939387 0). Qed.
Lemma lem939389 : term75 = term76.
Proof. exact (MK_COMB (@lem939385) (@lem939388)). Qed.
Lemma lem939391 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem939150 m n) (@lem939149 m n)). Qed.
Lemma lem939392 : term76 = term77.
Proof. exact (@lem939391 0 0). Qed.
Lemma lem939394 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (EQ_MP (@lem939232 m n) (@lem939231 m n)). Qed.
Lemma lem939395 : term78 = term79.
Proof. exact (@lem939394 0 term80). Qed.
Lemma lem939397 (n : nat) : (term63 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem939248 n) (@lem939247 n)). Qed.
Lemma lem939398 : term81 = term80.
Proof. exact (@lem939397 (Nat.mul 0 0)). Qed.
Lemma lem939400 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem939137)). Qed.
Lemma lem939401 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939402 : term80 = (BIT0 0).
Proof. exact (MK_COMB (@lem939401) (@lem939400)). Qed.
Lemma lem939404 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939405 : term80 = 0.
Proof. exact (TRANS (@lem939402) (@lem939404)). Qed.
Lemma lem939406 : term81 = 0.
Proof. exact (TRANS (@lem939398) (@lem939405)). Qed.
Lemma lem939407 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939408 : term79 = (BIT0 0).
Proof. exact (MK_COMB (@lem939407) (@lem939406)). Qed.
Lemma lem939410 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939411 : term79 = 0.
Proof. exact (TRANS (@lem939408) (@lem939410)). Qed.
Lemma lem939412 : term78 = 0.
Proof. exact (TRANS (@lem939395) (@lem939411)). Qed.
Lemma lem939413 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem939414 : term77 = term83.
Proof. exact (MK_COMB (@lem939413) (@lem939412)). Qed.
Lemma lem939416 (n : nat) : (term60 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem939236 n) (@lem939235 n)). Qed.
Lemma lem939417 : term83 = (BIT1 0).
Proof. exact (@lem939416 0). Qed.
Lemma lem939418 : term77 = (BIT1 0).
Proof. exact (TRANS (@lem939414) (@lem939417)). Qed.
Lemma lem939419 : term76 = (BIT1 0).
Proof. exact (TRANS (@lem939392) (@lem939418)). Qed.
Lemma lem939420 : term75 = (BIT1 0).
Proof. exact (TRANS (@lem939389) (@lem939419)). Qed.
Lemma lem939421 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem939422 : term71 = term76.
Proof. exact (MK_COMB (@lem939421) (@lem939420)). Qed.
Lemma lem939424 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem939150 m n) (@lem939149 m n)). Qed.
Lemma lem939425 : term76 = term77.
Proof. exact (@lem939424 0 0). Qed.
Lemma lem939427 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (EQ_MP (@lem939232 m n) (@lem939231 m n)). Qed.
Lemma lem939428 : term78 = term79.
Proof. exact (@lem939427 0 term80). Qed.
Lemma lem939430 (n : nat) : (term63 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem939248 n) (@lem939247 n)). Qed.
Lemma lem939431 : term81 = term80.
Proof. exact (@lem939430 (Nat.mul 0 0)). Qed.
Lemma lem939433 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem939137)). Qed.
Lemma lem939434 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939435 : term80 = (BIT0 0).
Proof. exact (MK_COMB (@lem939434) (@lem939433)). Qed.
Lemma lem939437 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939438 : term80 = 0.
Proof. exact (TRANS (@lem939435) (@lem939437)). Qed.
Lemma lem939439 : term81 = 0.
Proof. exact (TRANS (@lem939431) (@lem939438)). Qed.
Lemma lem939440 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939441 : term79 = (BIT0 0).
Proof. exact (MK_COMB (@lem939440) (@lem939439)). Qed.
Lemma lem939443 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939444 : term79 = 0.
Proof. exact (TRANS (@lem939441) (@lem939443)). Qed.
Lemma lem939445 : term78 = 0.
Proof. exact (TRANS (@lem939428) (@lem939444)). Qed.
Lemma lem939446 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem939447 : term77 = term83.
Proof. exact (MK_COMB (@lem939446) (@lem939445)). Qed.
Lemma lem939449 (n : nat) : (term60 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem939236 n) (@lem939235 n)). Qed.
Lemma lem939450 : term83 = (BIT1 0).
Proof. exact (@lem939449 0). Qed.
Lemma lem939451 : term77 = (BIT1 0).
Proof. exact (TRANS (@lem939447) (@lem939450)). Qed.
Lemma lem939452 : term76 = (BIT1 0).
Proof. exact (TRANS (@lem939425) (@lem939451)). Qed.
Lemma lem939453 : term71 = (BIT1 0).
Proof. exact (TRANS (@lem939422) (@lem939452)). Qed.
Lemma lem939454 : term70 = (BIT1 0).
Proof. exact (TRANS (@lem939380) (@lem939453)). Qed.
Lemma lem939455 : term69 = term76.
Proof. exact (MK_COMB (@lem939377) (@lem939454)). Qed.
Lemma lem939457 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem939150 m n) (@lem939149 m n)). Qed.
Lemma lem939458 : term76 = term77.
Proof. exact (@lem939457 0 0). Qed.
Lemma lem939460 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (EQ_MP (@lem939232 m n) (@lem939231 m n)). Qed.
Lemma lem939461 : term78 = term79.
Proof. exact (@lem939460 0 term80). Qed.
Lemma lem939463 (n : nat) : (term63 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem939248 n) (@lem939247 n)). Qed.
Lemma lem939464 : term81 = term80.
Proof. exact (@lem939463 (Nat.mul 0 0)). Qed.
Lemma lem939466 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem939137)). Qed.
Lemma lem939467 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939468 : term80 = (BIT0 0).
Proof. exact (MK_COMB (@lem939467) (@lem939466)). Qed.
Lemma lem939470 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939471 : term80 = 0.
Proof. exact (TRANS (@lem939468) (@lem939470)). Qed.
Lemma lem939472 : term81 = 0.
Proof. exact (TRANS (@lem939464) (@lem939471)). Qed.
Lemma lem939473 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem939474 : term79 = (BIT0 0).
Proof. exact (MK_COMB (@lem939473) (@lem939472)). Qed.
Lemma lem939476 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem939290)). Qed.
Lemma lem939477 : term79 = 0.
Proof. exact (TRANS (@lem939474) (@lem939476)). Qed.
Lemma lem939478 : term78 = 0.
Proof. exact (TRANS (@lem939461) (@lem939477)). Qed.
Lemma lem939479 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem939480 : term77 = term83.
Proof. exact (MK_COMB (@lem939479) (@lem939478)). Qed.
Lemma lem939482 (n : nat) : (term60 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem939236 n) (@lem939235 n)). Qed.
Lemma lem939483 : term83 = (BIT1 0).
Proof. exact (@lem939482 0). Qed.
Lemma lem939484 : term77 = (BIT1 0).
Proof. exact (TRANS (@lem939480) (@lem939483)). Qed.
Lemma lem939485 : term76 = (BIT1 0).
Proof. exact (TRANS (@lem939458) (@lem939484)). Qed.
Lemma lem939486 : term69 = (BIT1 0).
Proof. exact (TRANS (@lem939455) (@lem939485)). Qed.
Lemma lem939487 : term68 = (BIT1 0).
Proof. exact (TRANS (@lem939298) (@lem939486)). Qed.
Lemma lem939488 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem939489 : term66 = term85.
Proof. exact (MK_COMB (@lem939488) (@lem939487)). Qed.
Lemma lem939490 : term65 = term85.
Proof. exact (TRANS (@lem939295) (@lem939489)). Qed.
Lemma lem939502 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem939503 : (term87 = (BIT1 0)) = term88.
Proof. exact (@lem939502 (term87 = (BIT1 0))). Qed.
Lemma lem939504 : term88 = (term87 = (BIT1 0)).
Proof. exact (SYM (@lem939503)). Qed.
Lemma lem939505 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem939508 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem939509 : term91.
Proof. exact (fun h0 : term90 => @lem939508 h0). Qed.
Lemma lem939510 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem939511 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem939512 (h1 : term90) (h2 : term91) : term90.
Proof. exact (@lem939510 h2 (@lem939511 h1)). Qed.
Lemma lem939513 (h1 : term90) : term92.
Proof. exact (fun h0 : term91 => @lem939512 h1 h0). Qed.
Lemma lem939514 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem939515 (h1 : term90) (h2 : term91) : term90.
Proof. exact (@lem939513 h1 (@lem939514 h2)). Qed.
Lemma lem939516 (h1 : term91) : term91.
Proof. exact (fun h0 : term90 => @lem939515 h0 h1). Qed.
Lemma lem939517 : term93.
Proof. exact (fun h0 : term91 => @lem939516 h0). Qed.
Lemma lem939520 : term91.
Proof. exact (@lem939517 (@lem939509)). Qed.
Lemma lem939526 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem939527 : term94 = term95.
Proof. exact (@lem939526 term96). Qed.
Lemma lem939532 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem939533 : term98 = term99.
Proof. exact (MK_COMB (@lem939532) (@lem939527)). Qed.
Lemma lem939536 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem939543 : term90 = term101.
Proof. exact (MK_COMB (@lem939536) (@lem939533)). Qed.
Lemma lem939544 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem939545 : term102 = term102.
Proof. exact (fun_ext (fun n : nat => @lem939544 n)). Qed.
Lemma lem939546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem939547 : term96 = term96.
Proof. exact (MK_COMB (@lem939546) (@lem939545)). Qed.
Lemma lem939548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem939549 : term95 = term95.
Proof. exact (MK_COMB (@lem939548) (@lem939547)). Qed.
Lemma lem939552 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem939553 : term99 = term99.
Proof. exact (MK_COMB (@lem939552) (@lem939549)). Qed.
Lemma lem939558 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem939559 : term101 = term101.
Proof. exact (MK_COMB (@lem939558) (@lem939553)). Qed.
Lemma lem939572 : term90 = term101.
Proof. exact (TRANS (@lem939543) (@lem939559)). Qed.
Lemma lem939573 : term101 = term90.
Proof. exact (SYM (@lem939572)). Qed.
Lemma lem939576 (h1 : term96) : term96.
Proof. exact (h1). Qed.
Lemma lem939582 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem939588 (h1 : term65 = term85) : term65 = term85.
Proof. exact (h1). Qed.
Lemma lem939589 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem939590 : term102 = term102.
Proof. exact (fun_ext (fun n : nat => @lem939589 n)). Qed.
Lemma lem939591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem939600 : term96 = term96.
Proof. exact (MK_COMB (@lem939591) (@lem939590)). Qed.
Lemma lem939601 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem939600) (@lem939576 h1)). Qed.
Lemma lem939623 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem939647 (h1 : term65 = term85) : term65 = term85.
Proof. exact (h1). Qed.
Lemma lem939654 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem939655 : term102 = term102.
Proof. exact (fun_ext (fun n : nat => @lem939654 n)). Qed.
Lemma lem939656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem939657 : term96 = term96.
Proof. exact (MK_COMB (@lem939656) (@lem939655)). Qed.
Lemma lem939658 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem939657) (@lem939601 h1)). Qed.
Lemma lem939662 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem939666 (h1 : term65 = term85) : term65 = term85.
Proof. exact (h1). Qed.
Lemma lem939668 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem939669 : term102 = term102.
Proof. exact (fun_ext (fun n : nat => @lem939668 n)). Qed.
Lemma lem939670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem939672 : term96 = term96.
Proof. exact (MK_COMB (@lem939670) (@lem939669)). Qed.
Lemma lem939673 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem939672) (@lem939658 h1)). Qed.
Lemma lem939674 (_15929 : nat) (h1 : term96) : term103 _15929.
Proof. exact (@lem939673 h1 _15929). Qed.
Lemma lem939675 (_15929 : nat) : (term103 _15929) = ((NUMERAL _15929) = _15929).
Proof. exact (eq_refl (term103 _15929)). Qed.
Lemma lem939678 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem939680 (h1 : term65 = term85) : term65 = term85.
Proof. exact (h1). Qed.
Lemma lem939699 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem939700 (_15934 : nat) (_15936 : nat) (h1 : _15934 = _15936) : _15934 = _15936.
Proof. exact (h1). Qed.
Lemma lem939701 (_15935 : nat) (_15937 : nat) (h1 : _15935 = _15937) : _15935 = _15937.
Proof. exact (h1). Qed.
Lemma lem939702 (_15934 : nat) (_15936 : nat) (h1 : _15934 = _15936) : (Nat.pow _15934) = (Nat.pow _15936).
Proof. exact (MK_COMB (@lem939699) (@lem939700 _15934 _15936 h1)). Qed.
Lemma lem939703 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) (h1 : _15934 = _15936) (h2 : _15935 = _15937) : (Nat.pow _15934 _15935) = (Nat.pow _15936 _15937).
Proof. exact (MK_COMB (@lem939702 _15934 _15936 h1) (@lem939701 _15935 _15937 h2)). Qed.
Lemma lem939704 (_15935 : nat) (_15937 : nat) (_15934 : nat) (_15936 : nat) (h1 : _15934 = _15936) : term104 _15934 _15935 _15936 _15937.
Proof. exact (fun h0 : _15935 = _15937 => @lem939703 _15934 _15936 _15935 _15937 h1 h0). Qed.
Lemma lem939706 (a : Prop) (b : Prop) : (a -> b) = (term105 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem939707 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : (term104 _15934 _15935 _15936 _15937) = (term106 _15934 _15935 _15936 _15937).
Proof. exact (@lem939706 (_15935 = _15937) ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937))). Qed.
Lemma lem939708 (_15935 : nat) (_15937 : nat) (_15934 : nat) (_15936 : nat) (h1 : _15934 = _15936) : term106 _15934 _15935 _15936 _15937.
Proof. exact (EQ_MP (@lem939707 _15934 _15935 _15936 _15937) (@lem939704 _15935 _15937 _15934 _15936 h1)). Qed.
Lemma lem939709 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : term107 _15934 _15935 _15936 _15937.
Proof. exact (fun h0 : _15934 = _15936 => @lem939708 _15935 _15937 _15934 _15936 h0). Qed.
Lemma lem939711 (a : Prop) (b : Prop) : (a -> b) = (term105 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem939712 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : (term107 _15934 _15935 _15936 _15937) = (term108 _15934 _15935 _15936 _15937).
Proof. exact (@lem939711 (_15934 = _15936) (term106 _15934 _15935 _15936 _15937)). Qed.
Lemma lem939713 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : term108 _15934 _15935 _15936 _15937.
Proof. exact (EQ_MP (@lem939712 _15934 _15935 _15936 _15937) (@lem939709 _15934 _15935 _15936 _15937)). Qed.
Lemma lem939723 (x : nat) (y : nat) (z : nat) : term109 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem939725 (h1 : term65 = term85) : term65 = term85.
Proof. exact (h1). Qed.
Lemma lem939726 (h1 : term65 = term85) : term110.
Proof. exact (fun h0 : term111 => @lem939725 h1). Qed.
Lemma lem939728 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem939729 : term110 = (term65 = term85).
Proof. exact (@lem939728 (term65 = term85)). Qed.
Lemma lem939730 (h1 : term65 = term85) : term65 = term85.
Proof. exact (EQ_MP (@lem939729) (@lem939726 h1)). Qed.
Lemma lem939732 (_15929 : nat) (h1 : term96) : (NUMERAL _15929) = _15929.
Proof. exact (EQ_MP (@lem939675 _15929) (@lem939674 _15929 h1)). Qed.
Lemma lem939733 (h1 : term96) : term85 = (BIT1 0).
Proof. exact (@lem939732 (BIT1 0) h1). Qed.
Lemma lem939734 (h1 : term96) : term113.
Proof. exact (fun h0 : term114 => @lem939733 h1). Qed.
Lemma lem939736 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem939737 : term113 = (term85 = (BIT1 0)).
Proof. exact (@lem939736 (term85 = (BIT1 0))). Qed.
Lemma lem939738 (h1 : term96) : term85 = (BIT1 0).
Proof. exact (EQ_MP (@lem939737) (@lem939734 h1)). Qed.
Lemma lem939740 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem939741 : term115 = term115.
Proof. exact (@lem939740 term115). Qed.
Lemma lem939742 : term116.
Proof. exact (fun h0 : term117 => @lem939741). Qed.
Lemma lem939744 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem939745 : term116 = (term115 = term115).
Proof. exact (@lem939744 (term115 = term115)). Qed.
Lemma lem939746 : term115 = term115.
Proof. exact (EQ_MP (@lem939745) (@lem939742)). Qed.
Lemma lem939764 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem939765 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term106 _15934 _15935 _15936 _15937) = (term118 _15934 _15936 _15935 _15937).
Proof. exact (@lem939764 ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937)) (term119 _15935 _15937)). Qed.
Lemma lem939775 (_15934 : nat) (_15936 : nat) : (term120 _15934 _15936) = (term120 _15934 _15936).
Proof. exact (eq_refl (term120 _15934 _15936)). Qed.
Lemma lem939776 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term108 _15934 _15935 _15936 _15937) = (term121 _15934 _15936 _15935 _15937).
Proof. exact (MK_COMB (@lem939775 _15934 _15936) (@lem939765 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939780 (q : Prop) (p : Prop) (r : Prop) : (term122 p q r) = (term122 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem939781 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term121 _15934 _15936 _15935 _15937) = (term123 _15934 _15936 _15935 _15937).
Proof. exact (@lem939780 ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937)) (term119 _15934 _15936) (term119 _15935 _15937)). Qed.
Lemma lem939803 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term108 _15934 _15935 _15936 _15937) = (term123 _15934 _15936 _15935 _15937).
Proof. exact (TRANS (@lem939776 _15934 _15936 _15935 _15937) (@lem939781 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem939805 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term124 _15934 _15935 _15936 _15937) = (term125 _15934 _15936 _15935 _15937).
Proof. exact (MK_COMB (@lem939804) (@lem939803 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939827 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term123 _15934 _15936 _15935 _15937) = (term123 _15934 _15936 _15935 _15937).
Proof. exact (eq_refl (term123 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939828 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : ((term108 _15934 _15935 _15936 _15937) = (term123 _15934 _15936 _15935 _15937)) = ((term123 _15934 _15936 _15935 _15937) = (term123 _15934 _15936 _15935 _15937)).
Proof. exact (MK_COMB (@lem939805 _15934 _15936 _15935 _15937) (@lem939827 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939830 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem939831 (x : Prop) : (x = x) = True.
Proof. exact (@lem939830 Prop x). Qed.
Lemma lem939832 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : ((term123 _15934 _15936 _15935 _15937) = (term123 _15934 _15936 _15935 _15937)) = True.
Proof. exact (@lem939831 (term123 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939833 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : ((term108 _15934 _15935 _15936 _15937) = (term123 _15934 _15936 _15935 _15937)) = True.
Proof. exact (TRANS (@lem939828 _15934 _15936 _15935 _15937) (@lem939832 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939834 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : True = ((term108 _15934 _15935 _15936 _15937) = (term123 _15934 _15936 _15935 _15937)).
Proof. exact (SYM (@lem939833 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939835 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term108 _15934 _15935 _15936 _15937) = (term123 _15934 _15936 _15935 _15937).
Proof. exact (EQ_MP (@lem939834 _15934 _15936 _15935 _15937) (@lem0)). Qed.
Lemma lem939836 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : term123 _15934 _15936 _15935 _15937.
Proof. exact (EQ_MP (@lem939835 _15934 _15936 _15935 _15937) (@lem939713 _15934 _15935 _15936 _15937)). Qed.
Lemma lem939838 (b : Prop) (a : Prop) : (a \/ b) = (term126 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem939839 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : (term123 _15934 _15936 _15935 _15937) = (term127 _15934 _15935 _15936 _15937).
Proof. exact (@lem939838 (term128 _15934 _15936 _15935 _15937) ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937))). Qed.
Lemma lem939841 (a : Prop) (b : Prop) : (term129 a b) = (term130 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem939842 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term131 _15934 _15936 _15935 _15937) = (term132 _15934 _15936 _15935 _15937).
Proof. exact (@lem939841 (term119 _15934 _15936) (term119 _15935 _15937)). Qed.
Lemma lem939844 (a : Prop) : (term133 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem939845 (_15934 : nat) (_15936 : nat) : (term134 _15934 _15936) = (_15934 = _15936).
Proof. exact (@lem939844 (_15934 = _15936)). Qed.
Lemma lem939846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem939847 (_15934 : nat) (_15936 : nat) : (term135 _15934 _15936) = (term136 _15934 _15936).
Proof. exact (MK_COMB (@lem939846) (@lem939845 _15934 _15936)). Qed.
Lemma lem939849 (a : Prop) : (term133 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem939850 (_15935 : nat) (_15937 : nat) : (term134 _15935 _15937) = (_15935 = _15937).
Proof. exact (@lem939849 (_15935 = _15937)). Qed.
Lemma lem939851 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term132 _15934 _15936 _15935 _15937) = (term137 _15934 _15936 _15935 _15937).
Proof. exact (MK_COMB (@lem939847 _15934 _15936) (@lem939850 _15935 _15937)). Qed.
Lemma lem939852 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term131 _15934 _15936 _15935 _15937) = (term137 _15934 _15936 _15935 _15937).
Proof. exact (TRANS (@lem939842 _15934 _15936 _15935 _15937) (@lem939851 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem939854 (_15934 : nat) (_15936 : nat) (_15935 : nat) (_15937 : nat) : (term138 _15934 _15936 _15935 _15937) = (term139 _15934 _15936 _15935 _15937).
Proof. exact (MK_COMB (@lem939853) (@lem939852 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939855 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937)) = ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937)).
Proof. exact (eq_refl ((Nat.pow _15934 _15935) = (Nat.pow _15936 _15937))). Qed.
Lemma lem939856 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : (term127 _15934 _15935 _15936 _15937) = (term140 _15934 _15935 _15936 _15937).
Proof. exact (MK_COMB (@lem939854 _15934 _15936 _15935 _15937) (@lem939855 _15934 _15935 _15936 _15937)). Qed.
Lemma lem939857 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : (term123 _15934 _15936 _15935 _15937) = (term140 _15934 _15935 _15936 _15937).
Proof. exact (TRANS (@lem939839 _15934 _15935 _15936 _15937) (@lem939856 _15934 _15935 _15936 _15937)). Qed.
Lemma lem939859 (h1 : term96) : term141.
Proof. exact (conj (@lem939738 h1) (@lem939746)). Qed.
Lemma lem939861 (_15934 : nat) (_15935 : nat) (_15936 : nat) (_15937 : nat) : term140 _15934 _15935 _15936 _15937.
Proof. exact (EQ_MP (@lem939857 _15934 _15935 _15936 _15937) (@lem939836 _15934 _15936 _15935 _15937)). Qed.
Lemma lem939862 : term142.
Proof. exact (@lem939861 term85 term115 (BIT1 0) term115). Qed.
Lemma lem939865 (h1 : term96) : term65 = term87.
Proof. exact (@lem939862 (@lem939859 h1)). Qed.
Lemma lem939866 (h1 : term96) : term143.
Proof. exact (fun h0 : term144 => @lem939865 h1). Qed.
Lemma lem939868 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem939869 : term143 = (term65 = term87).
Proof. exact (@lem939868 (term65 = term87)). Qed.
Lemma lem939870 (h1 : term96) : term65 = term87.
Proof. exact (EQ_MP (@lem939869) (@lem939866 h1)). Qed.
Lemma lem939888 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem939889 (y : nat) (x : nat) (z : nat) : (term145 x y z) = (term146 y x z).
Proof. exact (@lem939888 (y = z) (term119 x z)). Qed.
Lemma lem939899 (x : nat) (y : nat) : (term120 x y) = (term120 x y).
Proof. exact (eq_refl (term120 x y)). Qed.
Lemma lem939900 (y : nat) (x : nat) (z : nat) : (term109 x y z) = (term147 y x z).
Proof. exact (MK_COMB (@lem939899 x y) (@lem939889 y x z)). Qed.
Lemma lem939904 (q : Prop) (p : Prop) (r : Prop) : (term122 p q r) = (term122 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem939905 (y : nat) (x : nat) (z : nat) : (term147 y x z) = (term148 y x z).
Proof. exact (@lem939904 (y = z) (term119 x y) (term119 x z)). Qed.
Lemma lem939927 (y : nat) (x : nat) (z : nat) : (term109 x y z) = (term148 y x z).
Proof. exact (TRANS (@lem939900 y x z) (@lem939905 y x z)). Qed.
Lemma lem939928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem939929 (y : nat) (x : nat) (z : nat) : (term149 x y z) = (term150 y x z).
Proof. exact (MK_COMB (@lem939928) (@lem939927 y x z)). Qed.
Lemma lem939951 (y : nat) (x : nat) (z : nat) : (term148 y x z) = (term148 y x z).
Proof. exact (eq_refl (term148 y x z)). Qed.
Lemma lem939952 (y : nat) (x : nat) (z : nat) : ((term109 x y z) = (term148 y x z)) = ((term148 y x z) = (term148 y x z)).
Proof. exact (MK_COMB (@lem939929 y x z) (@lem939951 y x z)). Qed.
Lemma lem939954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem939955 (x : Prop) : (x = x) = True.
Proof. exact (@lem939954 Prop x). Qed.
Lemma lem939956 (y : nat) (x : nat) (z : nat) : ((term148 y x z) = (term148 y x z)) = True.
Proof. exact (@lem939955 (term148 y x z)). Qed.
Lemma lem939957 (y : nat) (x : nat) (z : nat) : ((term109 x y z) = (term148 y x z)) = True.
Proof. exact (TRANS (@lem939952 y x z) (@lem939956 y x z)). Qed.
Lemma lem939958 (y : nat) (x : nat) (z : nat) : True = ((term109 x y z) = (term148 y x z)).
Proof. exact (SYM (@lem939957 y x z)). Qed.
Lemma lem939959 (y : nat) (x : nat) (z : nat) : (term109 x y z) = (term148 y x z).
Proof. exact (EQ_MP (@lem939958 y x z) (@lem0)). Qed.
Lemma lem939960 (y : nat) (x : nat) (z : nat) : term148 y x z.
Proof. exact (EQ_MP (@lem939959 y x z) (@lem939723 x y z)). Qed.
Lemma lem939962 (b : Prop) (a : Prop) : (a \/ b) = (term126 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem939963 (x : nat) (y : nat) (z : nat) : (term148 y x z) = (term151 x y z).
Proof. exact (@lem939962 (term152 y x z) (y = z)). Qed.
Lemma lem939965 (a : Prop) (b : Prop) : (term129 a b) = (term130 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem939966 (y : nat) (x : nat) (z : nat) : (term153 y x z) = (term154 y x z).
Proof. exact (@lem939965 (term119 x y) (term119 x z)). Qed.
Lemma lem939968 (a : Prop) : (term133 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem939969 (x : nat) (y : nat) : (term134 x y) = (x = y).
Proof. exact (@lem939968 (x = y)). Qed.
Lemma lem939970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem939971 (x : nat) (y : nat) : (term135 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem939970) (@lem939969 x y)). Qed.
Lemma lem939973 (a : Prop) : (term133 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem939974 (x : nat) (z : nat) : (term134 x z) = (x = z).
Proof. exact (@lem939973 (x = z)). Qed.
Lemma lem939975 (y : nat) (x : nat) (z : nat) : (term154 y x z) = (term155 y x z).
Proof. exact (MK_COMB (@lem939971 x y) (@lem939974 x z)). Qed.
Lemma lem939976 (y : nat) (x : nat) (z : nat) : (term153 y x z) = (term155 y x z).
Proof. exact (TRANS (@lem939966 y x z) (@lem939975 y x z)). Qed.
Lemma lem939977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem939978 (y : nat) (x : nat) (z : nat) : (term156 y x z) = (term157 y x z).
Proof. exact (MK_COMB (@lem939977) (@lem939976 y x z)). Qed.
Lemma lem939979 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem939980 (x : nat) (y : nat) (z : nat) : (term151 x y z) = (term158 x y z).
Proof. exact (MK_COMB (@lem939978 y x z) (@lem939979 y z)). Qed.
Lemma lem939981 (x : nat) (y : nat) (z : nat) : (term148 y x z) = (term158 x y z).
Proof. exact (TRANS (@lem939963 x y z) (@lem939980 x y z)). Qed.
Lemma lem939983 (h1 : term96) (h2 : term65 = term85) : term159.
Proof. exact (conj (@lem939730 h2) (@lem939870 h1)). Qed.
Lemma lem939985 (x : nat) (y : nat) (z : nat) : term158 x y z.
Proof. exact (EQ_MP (@lem939981 x y z) (@lem939960 y x z)). Qed.
Lemma lem939986 : term160.
Proof. exact (@lem939985 term65 term85 term87). Qed.
Lemma lem939989 (h1 : term96) (h2 : term65 = term85) : term85 = term87.
Proof. exact (@lem939986 (@lem939983 h1 h2)). Qed.
Lemma lem939990 (h1 : term96) (h2 : term65 = term85) : term161.
Proof. exact (fun h0 : term162 => @lem939989 h1 h2). Qed.
Lemma lem939992 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem939993 : term161 = (term85 = term87).
Proof. exact (@lem939992 (term85 = term87)). Qed.
Lemma lem939994 (h1 : term96) (h2 : term65 = term85) : term85 = term87.
Proof. exact (EQ_MP (@lem939993) (@lem939990 h1 h2)). Qed.
Lemma lem939996 (_15929 : nat) (h1 : term96) : (NUMERAL _15929) = _15929.
Proof. exact (EQ_MP (@lem939675 _15929) (@lem939674 _15929 h1)). Qed.
Lemma lem939997 (h1 : term96) : term85 = (BIT1 0).
Proof. exact (@lem939996 (BIT1 0) h1). Qed.
Lemma lem939998 (h1 : term96) : term113.
Proof. exact (fun h0 : term114 => @lem939997 h1). Qed.
Lemma lem940000 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem940001 : term113 = (term85 = (BIT1 0)).
Proof. exact (@lem940000 (term85 = (BIT1 0))). Qed.
Lemma lem940002 (h1 : term96) : term85 = (BIT1 0).
Proof. exact (EQ_MP (@lem940001) (@lem939998 h1)). Qed.
Lemma lem940003 (h1 : term96) (h2 : term65 = term85) : term163.
Proof. exact (conj (@lem939994 h1 h2) (@lem940002 h1)). Qed.
Lemma lem940005 (x : nat) (y : nat) (z : nat) : term158 x y z.
Proof. exact (EQ_MP (@lem939981 x y z) (@lem939960 y x z)). Qed.
Lemma lem940006 : term164.
Proof. exact (@lem940005 term85 term87 (BIT1 0)). Qed.
Lemma lem940009 (h1 : term96) (h2 : term65 = term85) : term87 = (BIT1 0).
Proof. exact (@lem940006 (@lem940003 h1 h2)). Qed.
Lemma lem940010 (h1 : term96) (h2 : term65 = term85) : term165.
Proof. exact (fun h0 : term89 => @lem940009 h1 h2). Qed.
Lemma lem940012 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem940013 : term165 = (term87 = (BIT1 0)).
Proof. exact (@lem940012 (term87 = (BIT1 0))). Qed.
Lemma lem940014 (h1 : term96) (h2 : term65 = term85) : term87 = (BIT1 0).
Proof. exact (EQ_MP (@lem940013) (@lem940010 h1 h2)). Qed.
Lemma lem940017 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem940019 : term89 = term166.
Proof. exact (@lem940017 (term87 = (BIT1 0))). Qed.
Lemma lem940022 (h1 : term89) : term166.
Proof. exact (EQ_MP (@lem940019) (@lem939678 h1)). Qed.
Lemma lem940025 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (@lem940022 h2 (@lem940014 h1 h3)). Qed.
Lemma lem940026 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term167.
Proof. exact (fun h0 : ~ False => @lem940025 h1 h2 h3). Qed.
Lemma lem940028 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem940029 : term167 = False.
Proof. exact (@lem940028 False). Qed.
Lemma lem940030 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940029) (@lem940026 h1 h2 h3)). Qed.
Lemma lem940031 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : (term65 = term85) = False.
Proof. exact (prop_ext (fun h4 : term65 = term85 => @lem940030 h1 h2 h3) (fun h4 : False => @lem939680 h3)). Qed.
Lemma lem940032 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940031 h1 h2 h3) (@lem939680 h3)). Qed.
Lemma lem940033 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term89 = False.
Proof. exact (prop_ext (fun h4 : term89 => @lem940032 h1 h2 h3) (fun h4 : False => @lem939678 h2)). Qed.
Lemma lem940034 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940033 h1 h2 h3) (@lem939678 h2)). Qed.
Lemma lem940035 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : (term65 = term85) = False.
Proof. exact (prop_ext (fun h4 : term65 = term85 => @lem940034 h1 h2 h3) (fun h4 : False => @lem939666 h3)). Qed.
Lemma lem940036 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940035 h1 h2 h3) (@lem939666 h3)). Qed.
Lemma lem940037 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term89 = False.
Proof. exact (prop_ext (fun h4 : term89 => @lem940036 h1 h2 h3) (fun h4 : False => @lem939662 h2)). Qed.
Lemma lem940038 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940037 h1 h2 h3) (@lem939662 h2)). Qed.
Lemma lem940039 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term96 = False.
Proof. exact (prop_ext (fun h4 : term96 => @lem940038 h1 h2 h3) (fun h4 : False => @lem939673 h1)). Qed.
Lemma lem940040 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940039 h1 h2 h3) (@lem939673 h1)). Qed.
Lemma lem940041 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : (term65 = term85) = False.
Proof. exact (prop_ext (fun h4 : term65 = term85 => @lem940040 h1 h2 h3) (fun h4 : False => @lem939666 h3)). Qed.
Lemma lem940042 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940041 h1 h2 h3) (@lem939666 h3)). Qed.
Lemma lem940043 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term89 = False.
Proof. exact (prop_ext (fun h4 : term89 => @lem940042 h1 h2 h3) (fun h4 : False => @lem939662 h2)). Qed.
Lemma lem940044 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940043 h1 h2 h3) (@lem939662 h2)). Qed.
Lemma lem940045 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term96 = False.
Proof. exact (prop_ext (fun h4 : term96 => @lem940044 h1 h2 h3) (fun h4 : False => @lem939658 h1)). Qed.
Lemma lem940046 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940045 h1 h2 h3) (@lem939658 h1)). Qed.
Lemma lem940047 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : (term65 = term85) = False.
Proof. exact (prop_ext (fun h4 : term65 = term85 => @lem940046 h1 h2 h3) (fun h4 : False => @lem939647 h3)). Qed.
Lemma lem940048 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940047 h1 h2 h3) (@lem939647 h3)). Qed.
Lemma lem940049 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term89 = False.
Proof. exact (prop_ext (fun h4 : term89 => @lem940048 h1 h2 h3) (fun h4 : False => @lem939623 h2)). Qed.
Lemma lem940050 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940049 h1 h2 h3) (@lem939623 h2)). Qed.
Lemma lem940051 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term96 = False.
Proof. exact (prop_ext (fun h4 : term96 => @lem940050 h1 h2 h3) (fun h4 : False => @lem939601 h1)). Qed.
Lemma lem940052 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940051 h1 h2 h3) (@lem939601 h1)). Qed.
Lemma lem940053 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : (term65 = term85) = False.
Proof. exact (prop_ext (fun h4 : term65 = term85 => @lem940052 h1 h2 h3) (fun h4 : False => @lem939588 h3)). Qed.
Lemma lem940054 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940053 h1 h2 h3) (@lem939588 h3)). Qed.
Lemma lem940055 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : term89 = False.
Proof. exact (prop_ext (fun h4 : term89 => @lem940054 h1 h2 h3) (fun h4 : False => @lem939582 h2)). Qed.
Lemma lem940056 (h1 : term96) (h2 : term89) (h3 : term65 = term85) : False.
Proof. exact (EQ_MP (@lem940055 h1 h2 h3) (@lem939582 h2)). Qed.
Lemma lem940057 (h1 : term89) (h2 : term65 = term85) : term94.
Proof. exact (fun h0 : term96 => @lem940056 h0 h1 h2). Qed.
Lemma lem940058 : term94 = term95.
Proof. exact (@lem69 term96). Qed.
Lemma lem940059 (h1 : term89) (h2 : term65 = term85) : term95.
Proof. exact (EQ_MP (@lem940058) (@lem940057 h1 h2)). Qed.
Lemma lem940060 (h1 : term89) : term99.
Proof. exact (fun h0 : term65 = term85 => @lem940059 h1 h0). Qed.
Lemma lem940061 : term101.
Proof. exact (fun h0 : term89 => @lem940060 h0). Qed.
Lemma lem940062 : term90.
Proof. exact (EQ_MP (@lem939573) (@lem940061)). Qed.
Lemma lem940064 : term90.
Proof. exact (@lem939520 (@lem940062)). Qed.
Lemma lem940065 (h1 : term89) : term98.
Proof. exact (@lem940064 (@lem939505 h1)). Qed.
Lemma lem940066 (h1 : term89) : term94.
Proof. exact (@lem940065 h1 (@lem939490)). Qed.
Lemma lem940067 (h1 : term89) : False.
Proof. exact (@lem940066 h1 (@lem75543)). Qed.
Lemma lem940068 (h1 : term89) : term89 = False.
Proof. exact (prop_ext (fun h2 : term89 => @lem940067 h1) (fun h2 : False => @lem939505 h1)). Qed.
Lemma lem940069 (h1 : term89) : False.
Proof. exact (EQ_MP (@lem940068 h1) (@lem939505 h1)). Qed.
Lemma lem940070 : term88.
Proof. exact (fun h0 : term89 => @lem940069 h0). Qed.
Lemma lem940073 : term87 = (BIT1 0).
Proof. exact (EQ_MP (@lem939504) (@lem940070)). Qed.
