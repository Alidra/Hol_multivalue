Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_ZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm155916_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem158204 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem158205 : term1 = term2.
Proof. exact (@lem158204 term1). Qed.
Lemma lem158206 : term2 = term1.
Proof. exact (SYM (@lem158205)). Qed.
Lemma lem158207 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem158210 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem158211 : term5.
Proof. exact (fun h0 : term4 => @lem158210 h0). Qed.
Lemma lem158212 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem158213 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem158214 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem158212 h2 (@lem158213 h1)). Qed.
Lemma lem158215 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem158214 h1 h0). Qed.
Lemma lem158216 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem158217 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem158215 h1 (@lem158216 h2)). Qed.
Lemma lem158218 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem158217 h0 h1). Qed.
Lemma lem158219 : term7.
Proof. exact (fun h0 : term5 => @lem158218 h0). Qed.
Lemma lem158222 : term5.
Proof. exact (@lem158219 (@lem158211)). Qed.
Lemma lem158230 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem158231 : term8 = term9.
Proof. exact (@lem158230 term10). Qed.
Lemma lem158244 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem158251 : term4 = term12.
Proof. exact (MK_COMB (@lem158244) (@lem158231)). Qed.
Lemma lem158255 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem158256 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem158257 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term13 n) = (@COND Prop False).
Proof. exact (MK_COMB (@lem158256) (@lem158255 n h1)). Qed.
Lemma lem158264 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem158265 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term15 n m) = (term16 n m).
Proof. exact (MK_COMB (@lem158257 n h1) (@lem158264 n m)). Qed.
Lemma lem158270 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem158271 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem158265 m n h1) (@lem158270 m n)). Qed.
Lemma lem158273 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem158274 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem158273 Prop t1 t2). Qed.
Lemma lem158275 (m : nat) (n : nat) : (term19 m n) = (term17 m n).
Proof. exact (@lem158274 (term14 n m) (term17 m n)). Qed.
Lemma lem158278 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 m n) = (term17 m n).
Proof. exact (TRANS (@lem158271 m n h1) (@lem158275 m n)). Qed.
Lemma lem158279 (m : nat) (n : nat) : term20 m n.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = False => @lem158278 m n h0). Qed.
Lemma lem158281 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem158282 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem158283 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term13 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem158282) (@lem158281 n h1)). Qed.
Lemma lem158290 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem158291 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term15 n m) = (term21 n m).
Proof. exact (MK_COMB (@lem158283 n h1) (@lem158290 n m)). Qed.
Lemma lem158296 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem158297 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem158291 m n h1) (@lem158296 m n)). Qed.
Lemma lem158299 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem158300 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem158299 Prop t2 t1). Qed.
Lemma lem158301 (n : nat) (m : nat) : (term22 m n) = (term14 n m).
Proof. exact (@lem158300 (term17 m n) (term14 n m)). Qed.
Lemma lem158304 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 m n) = (term14 n m).
Proof. exact (TRANS (@lem158297 m n h1) (@lem158301 n m)). Qed.
Lemma lem158305 (n : nat) (m : nat) : term23 n m.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = True => @lem158304 m n h0). Qed.
Lemma lem158306 (n : nat) (m : nat) : term24 n m.
Proof. exact (conj (@lem158279 m n) (@lem158305 n m)). Qed.
Lemma lem158308 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term25 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem158309 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem158308 (term18 m n) (term14 n m) (n = (NUMERAL 0)) (term17 m n)). Qed.
Lemma lem158350 (m : nat) (n : nat) : (term18 m n) = (term27 m n).
Proof. exact (@lem158309 m n (@lem158306 n m)). Qed.
Lemma lem158351 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem158350 m n)). Qed.
Lemma lem158352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158353 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem158352) (@lem158351 m)). Qed.
Lemma lem158354 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem158353 m)). Qed.
Lemma lem158355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158356 : term10 = term34.
Proof. exact (MK_COMB (@lem158355) (@lem158354)). Qed.
Lemma lem158357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem158358 : term9 = term35.
Proof. exact (MK_COMB (@lem158357) (@lem158356)). Qed.
Lemma lem158359 (n : nat) : ((term36 n) = n) = ((term36 n) = n).
Proof. exact (eq_refl ((term36 n) = n)). Qed.
Lemma lem158360 : term37 = term37.
Proof. exact (fun_ext (fun n : nat => @lem158359 n)). Qed.
Lemma lem158361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158362 : term1 = term1.
Proof. exact (MK_COMB (@lem158361) (@lem158360)). Qed.
Lemma lem158363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem158364 : term3 = term3.
Proof. exact (MK_COMB (@lem158363) (@lem158362)). Qed.
Lemma lem158365 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem158366 : term11 = term11.
Proof. exact (MK_COMB (@lem158365) (@lem158364)). Qed.
Lemma lem158367 : term12 = term38.
Proof. exact (MK_COMB (@lem158366) (@lem158358)). Qed.
Lemma lem158400 : term4 = term38.
Proof. exact (TRANS (@lem158251) (@lem158367)). Qed.
Lemma lem158401 : term38 = term4.
Proof. exact (SYM (@lem158400)). Qed.
Lemma lem158402 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem158403 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem158405 (P : nat -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem158406 : term3 = term41.
Proof. exact (@lem158405 term37). Qed.
Lemma lem158407 (n : nat) : (term42 n) = ((term36 n) = n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem158408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem158410 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem158408) (@lem158407 n)). Qed.
Lemma lem158411 : term45 = term46.
Proof. exact (fun_ext (fun n : nat => @lem158410 n)). Qed.
Lemma lem158412 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem158413 : term41 = term47.
Proof. exact (MK_COMB (@lem158412) (@lem158411)). Qed.
Lemma lem158422 : term3 = term47.
Proof. exact (TRANS (@lem158406) (@lem158413)). Qed.
Lemma lem158423 (h1 : term3) : term47.
Proof. exact (EQ_MP (@lem158422) (@lem158402 h1)). Qed.
Lemma lem158444 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem158445 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem158444 m n)). Qed.
Lemma lem158446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158447 (m : nat) : (term31 m) = (term31 m).
Proof. exact (MK_COMB (@lem158446) (@lem158445 m)). Qed.
Lemma lem158448 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem158447 m)). Qed.
Lemma lem158449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158450 : term34 = term34.
Proof. exact (MK_COMB (@lem158449) (@lem158448)). Qed.
Lemma lem158456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem158457 (P : nat -> Prop) (Q : nat -> Prop) : (term50 P Q) = (term51 P Q).
Proof. exact (@lem158456 nat P Q). Qed.
Lemma lem158458 (m : nat) : (term52 m) = (term53 m).
Proof. exact (@lem158457 (term54 m) (term55 m)). Qed.
Lemma lem158459 (n : nat) (m : nat) : (term56 m n) = (term57 n m).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem158460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem158461 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem158460) (@lem158459 n m)). Qed.
Lemma lem158462 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem158463 (m : nat) (n : nat) : (term62 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem158461 n m) (@lem158462 m n)). Qed.
Lemma lem158464 (m : nat) : (term63 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem158463 m n)). Qed.
Lemma lem158465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158466 (m : nat) : (term52 m) = (term31 m).
Proof. exact (MK_COMB (@lem158465) (@lem158464 m)). Qed.
Lemma lem158467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem158468 (m : nat) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem158467) (@lem158466 m)). Qed.
Lemma lem158469 (n : nat) (m : nat) : (term56 m n) = (term57 n m).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem158470 (m : nat) : (term66 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem158469 n m)). Qed.
Lemma lem158471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158472 (m : nat) : (term67 m) = (term68 m).
Proof. exact (MK_COMB (@lem158471) (@lem158470 m)). Qed.
Lemma lem158473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem158474 (m : nat) : (term69 m) = (term70 m).
Proof. exact (MK_COMB (@lem158473) (@lem158472 m)). Qed.
Lemma lem158475 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem158476 (m : nat) : (term71 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem158475 m n)). Qed.
Lemma lem158477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158478 (m : nat) : (term72 m) = (term73 m).
Proof. exact (MK_COMB (@lem158477) (@lem158476 m)). Qed.
Lemma lem158479 (m : nat) : (term53 m) = (term74 m).
Proof. exact (MK_COMB (@lem158474 m) (@lem158478 m)). Qed.
Lemma lem158480 (m : nat) : ((term52 m) = (term53 m)) = ((term31 m) = (term74 m)).
Proof. exact (MK_COMB (@lem158468 m) (@lem158479 m)). Qed.
Lemma lem158481 (m : nat) : (term31 m) = (term74 m).
Proof. exact (EQ_MP (@lem158480 m) (@lem158458 m)). Qed.
Lemma lem158578 : term33 = term75.
Proof. exact (fun_ext (fun m : nat => @lem158481 m)). Qed.
Lemma lem158579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158580 : term34 = term76.
Proof. exact (MK_COMB (@lem158579) (@lem158578)). Qed.
Lemma lem158582 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem158583 (P : nat -> Prop) (Q : nat -> Prop) : (term50 P Q) = (term51 P Q).
Proof. exact (@lem158582 nat P Q). Qed.
Lemma lem158584 : term77 = term78.
Proof. exact (@lem158583 term79 term80). Qed.
Lemma lem158585 (m : nat) : (term81 m) = (term68 m).
Proof. exact (eq_refl (term81 m)). Qed.
Lemma lem158586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem158587 (m : nat) : (term82 m) = (term70 m).
Proof. exact (MK_COMB (@lem158586) (@lem158585 m)). Qed.
Lemma lem158588 (m : nat) : (term83 m) = (term73 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem158589 (m : nat) : (term84 m) = (term74 m).
Proof. exact (MK_COMB (@lem158587 m) (@lem158588 m)). Qed.
Lemma lem158590 : term85 = term75.
Proof. exact (fun_ext (fun m : nat => @lem158589 m)). Qed.
Lemma lem158591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158592 : term77 = term76.
Proof. exact (MK_COMB (@lem158591) (@lem158590)). Qed.
Lemma lem158593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem158594 : term86 = term87.
Proof. exact (MK_COMB (@lem158593) (@lem158592)). Qed.
Lemma lem158595 (m : nat) : (term81 m) = (term68 m).
Proof. exact (eq_refl (term81 m)). Qed.
Lemma lem158596 : term88 = term79.
Proof. exact (fun_ext (fun m : nat => @lem158595 m)). Qed.
Lemma lem158597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158598 : term89 = term90.
Proof. exact (MK_COMB (@lem158597) (@lem158596)). Qed.
Lemma lem158599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem158600 : term91 = term92.
Proof. exact (MK_COMB (@lem158599) (@lem158598)). Qed.
Lemma lem158601 (m : nat) : (term83 m) = (term73 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem158602 : term93 = term80.
Proof. exact (fun_ext (fun m : nat => @lem158601 m)). Qed.
Lemma lem158603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158604 : term94 = term95.
Proof. exact (MK_COMB (@lem158603) (@lem158602)). Qed.
Lemma lem158605 : term78 = term96.
Proof. exact (MK_COMB (@lem158600) (@lem158604)). Qed.
Lemma lem158606 : (term77 = term78) = (term76 = term96).
Proof. exact (MK_COMB (@lem158594) (@lem158605)). Qed.
Lemma lem158607 : term76 = term96.
Proof. exact (EQ_MP (@lem158606) (@lem158584)). Qed.
Lemma lem158714 : term34 = term96.
Proof. exact (TRANS (@lem158580) (@lem158607)). Qed.
Lemma lem158715 : term34 = term96.
Proof. exact (TRANS (@lem158450) (@lem158714)). Qed.
Lemma lem158716 (h1 : term34) : term96.
Proof. exact (EQ_MP (@lem158715) (@lem158403 h1)). Qed.
Lemma lem158760 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem158761 (m : nat) : (term55 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem158760 m n)). Qed.
Lemma lem158762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158763 (m : nat) : (term73 m) = (term73 m).
Proof. exact (MK_COMB (@lem158762) (@lem158761 m)). Qed.
Lemma lem158764 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem158763 m)). Qed.
Lemma lem158765 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158766 : term95 = term95.
Proof. exact (MK_COMB (@lem158765) (@lem158764)). Qed.
Lemma lem158801 (n : nat) (m : nat) : (term57 n m) = (term57 n m).
Proof. exact (eq_refl (term57 n m)). Qed.
Lemma lem158802 (m : nat) : (term54 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem158801 n m)). Qed.
Lemma lem158803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158804 (m : nat) : (term68 m) = (term68 m).
Proof. exact (MK_COMB (@lem158803) (@lem158802 m)). Qed.
Lemma lem158805 : term79 = term79.
Proof. exact (fun_ext (fun m : nat => @lem158804 m)). Qed.
Lemma lem158806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158807 : term90 = term90.
Proof. exact (MK_COMB (@lem158806) (@lem158805)). Qed.
Lemma lem158808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem158809 : term92 = term92.
Proof. exact (MK_COMB (@lem158808) (@lem158807)). Qed.
Lemma lem158810 : term96 = term96.
Proof. exact (MK_COMB (@lem158809) (@lem158766)). Qed.
Lemma lem158811 (h1 : term34) : term96.
Proof. exact (EQ_MP (@lem158810) (@lem158716 h1)). Qed.
Lemma lem158825 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem158827 (h1 : term34) : term90.
Proof. exact (proj1 (@lem158811 h1)). Qed.
Lemma lem158831 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem158849 (n : nat) (m : nat) : (term57 n m) = (term97 n m).
Proof. exact (@lem19490 ((Nat.div m n) = (NUMERAL 0)) (term98 n) ((Nat.modulo m n) = m)). Qed.
Lemma lem158850 (m : nat) : (term54 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem158849 n m)). Qed.
Lemma lem158851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158852 (m : nat) : (term68 m) = (term100 m).
Proof. exact (MK_COMB (@lem158851) (@lem158850 m)). Qed.
Lemma lem158853 : term79 = term101.
Proof. exact (fun_ext (fun m : nat => @lem158852 m)). Qed.
Lemma lem158854 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem158856 : term90 = term102.
Proof. exact (MK_COMB (@lem158854) (@lem158853)). Qed.
Lemma lem158857 (h1 : term34) : term102.
Proof. exact (EQ_MP (@lem158856) (@lem158827 h1)). Qed.
Lemma lem158884 (_3166 : nat) (h1 : term34) : term103 _3166.
Proof. exact (@lem158857 h1 _3166). Qed.
Lemma lem158885 (_3166 : nat) : (term103 _3166) = (term100 _3166).
Proof. exact (eq_refl (term103 _3166)). Qed.
Lemma lem158886 (_3166 : nat) (h1 : term34) : term100 _3166.
Proof. exact (EQ_MP (@lem158885 _3166) (@lem158884 _3166 h1)). Qed.
Lemma lem158887 (_3166 : nat) (_3167 : nat) (h1 : term34) : term104 _3166 _3167.
Proof. exact (@lem158886 _3166 h1 _3167). Qed.
Lemma lem158888 (_3167 : nat) (_3166 : nat) : (term104 _3166 _3167) = (term97 _3167 _3166).
Proof. exact (eq_refl (term104 _3166 _3167)). Qed.
Lemma lem158889 (_3167 : nat) (_3166 : nat) (h1 : term34) : term97 _3167 _3166.
Proof. exact (EQ_MP (@lem158888 _3167 _3166) (@lem158887 _3166 _3167 h1)). Qed.
Lemma lem158901 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem158925 (_3167 : nat) (_3166 : nat) (h1 : term34) : term105 _3167 _3166.
Proof. exact (proj2 (@lem158889 _3167 _3166 h1)). Qed.
Lemma lem159016 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem159017 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem159016 (NUMERAL 0)). Qed.
Lemma lem159018 : term106.
Proof. exact (fun h0 : term107 => @lem159017). Qed.
Lemma lem159020 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem159021 : term106 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem159020 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem159022 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem159021) (@lem159018)). Qed.
Lemma lem159028 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem159029 (_3166 : nat) (_3167 : nat) : (term105 _3167 _3166) = (term109 _3166 _3167).
Proof. exact (@lem159028 ((Nat.modulo _3166 _3167) = _3166) (term98 _3167)). Qed.
Lemma lem159039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem159040 (_3166 : nat) (_3167 : nat) : (term110 _3167 _3166) = (term111 _3166 _3167).
Proof. exact (MK_COMB (@lem159039) (@lem159029 _3166 _3167)). Qed.
Lemma lem159050 (_3166 : nat) (_3167 : nat) : (term109 _3166 _3167) = (term109 _3166 _3167).
Proof. exact (eq_refl (term109 _3166 _3167)). Qed.
Lemma lem159051 (_3166 : nat) (_3167 : nat) : ((term105 _3167 _3166) = (term109 _3166 _3167)) = ((term109 _3166 _3167) = (term109 _3166 _3167)).
Proof. exact (MK_COMB (@lem159040 _3166 _3167) (@lem159050 _3166 _3167)). Qed.
Lemma lem159053 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem159054 (x : Prop) : (x = x) = True.
Proof. exact (@lem159053 Prop x). Qed.
Lemma lem159055 (_3166 : nat) (_3167 : nat) : ((term109 _3166 _3167) = (term109 _3166 _3167)) = True.
Proof. exact (@lem159054 (term109 _3166 _3167)). Qed.
Lemma lem159056 (_3166 : nat) (_3167 : nat) : ((term105 _3167 _3166) = (term109 _3166 _3167)) = True.
Proof. exact (TRANS (@lem159051 _3166 _3167) (@lem159055 _3166 _3167)). Qed.
Lemma lem159057 (_3166 : nat) (_3167 : nat) : True = ((term105 _3167 _3166) = (term109 _3166 _3167)).
Proof. exact (SYM (@lem159056 _3166 _3167)). Qed.
Lemma lem159058 (_3166 : nat) (_3167 : nat) : (term105 _3167 _3166) = (term109 _3166 _3167).
Proof. exact (EQ_MP (@lem159057 _3166 _3167) (@lem0)). Qed.
Lemma lem159059 (_3166 : nat) (_3167 : nat) (h1 : term34) : term109 _3166 _3167.
Proof. exact (EQ_MP (@lem159058 _3166 _3167) (@lem158925 _3167 _3166 h1)). Qed.
Lemma lem159061 (b : Prop) (a : Prop) : (a \/ b) = (term112 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem159062 (_3167 : nat) (_3166 : nat) : (term109 _3166 _3167) = (term113 _3167 _3166).
Proof. exact (@lem159061 (term98 _3167) ((Nat.modulo _3166 _3167) = _3166)). Qed.
Lemma lem159064 (a : Prop) : (term114 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem159065 (_3167 : nat) : (term115 _3167) = (_3167 = (NUMERAL 0)).
Proof. exact (@lem159064 (_3167 = (NUMERAL 0))). Qed.
Lemma lem159066 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem159067 (_3167 : nat) : (term116 _3167) = (term117 _3167).
Proof. exact (MK_COMB (@lem159066) (@lem159065 _3167)). Qed.
Lemma lem159068 (_3167 : nat) (_3166 : nat) : ((Nat.modulo _3166 _3167) = _3166) = ((Nat.modulo _3166 _3167) = _3166).
Proof. exact (eq_refl ((Nat.modulo _3166 _3167) = _3166)). Qed.
Lemma lem159069 (_3167 : nat) (_3166 : nat) : (term113 _3167 _3166) = (term118 _3167 _3166).
Proof. exact (MK_COMB (@lem159067 _3167) (@lem159068 _3167 _3166)). Qed.
Lemma lem159070 (_3167 : nat) (_3166 : nat) : (term109 _3166 _3167) = (term118 _3167 _3166).
Proof. exact (TRANS (@lem159062 _3167 _3166) (@lem159069 _3167 _3166)). Qed.
Lemma lem159073 (_3167 : nat) (_3166 : nat) (h1 : term34) : term118 _3167 _3166.
Proof. exact (EQ_MP (@lem159070 _3167 _3166) (@lem159059 _3166 _3167 h1)). Qed.
Lemma lem159074 (_3166 : nat) (h1 : term34) : term119 _3166.
Proof. exact (@lem159073 (NUMERAL 0) _3166 h1). Qed.
Lemma lem159077 (_3166 : nat) (h1 : term34) : (term36 _3166) = _3166.
Proof. exact (@lem159074 _3166 h1 (@lem159022)). Qed.
Lemma lem159078 (n : nat) (h1 : term34) : (term36 n) = n.
Proof. exact (@lem159077 n h1). Qed.
Lemma lem159079 (n : nat) (h1 : term34) : term120 n.
Proof. exact (fun h0 : term44 n => @lem159078 n h1). Qed.
Lemma lem159081 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem159082 (n : nat) : (term120 n) = ((term36 n) = n).
Proof. exact (@lem159081 ((term36 n) = n)). Qed.
Lemma lem159083 (n : nat) (h1 : term34) : (term36 n) = n.
Proof. exact (EQ_MP (@lem159082 n) (@lem159079 n h1)). Qed.
Lemma lem159086 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem159088 (n : nat) : (term44 n) = (term121 n).
Proof. exact (@lem159086 ((term36 n) = n)). Qed.
Lemma lem159091 (n : nat) (h1 : term44 n) : term121 n.
Proof. exact (EQ_MP (@lem159088 n) (@lem158901 n h1)). Qed.
Lemma lem159094 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (@lem159091 n h2 (@lem159083 n h1)). Qed.
Lemma lem159095 (n : nat) (h1 : term34) (h2 : term44 n) : term122.
Proof. exact (fun h0 : ~ False => @lem159094 n h1 h2). Qed.
Lemma lem159097 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem159098 : term122 = False.
Proof. exact (@lem159097 False). Qed.
Lemma lem159099 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem159098) (@lem159095 n h1 h2)). Qed.
Lemma lem159100 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem159099 n h1 h2) (fun h3 : False => @lem158901 n h2)). Qed.
Lemma lem159101 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem159100 n h1 h2) (@lem158901 n h2)). Qed.
Lemma lem159102 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem159101 n h1 h2) (fun h3 : False => @lem158831 n h2)). Qed.
Lemma lem159103 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem159102 n h1 h2) (@lem158831 n h2)). Qed.
Lemma lem159104 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem159103 n h1 h2) (fun h3 : False => @lem158831 n h2)). Qed.
Lemma lem159105 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem159104 n h1 h2) (@lem158831 n h2)). Qed.
Lemma lem159106 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem159105 n h1 h2) (fun h3 : False => @lem158825 n h2)). Qed.
Lemma lem159107 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem159106 n h1 h2) (@lem158825 n h2)). Qed.
Lemma lem159108 (h1 : term34) (h2 : term3) : False.
Proof. exact (ex_elim (@lem158423 h2) (fun n : nat => fun h0 : term46 n => @lem159107 n h1 h0)). Qed.
Lemma lem159109 (h1 : term3) : term123.
Proof. exact (fun h0 : term34 => @lem159108 h0 h1). Qed.
Lemma lem159110 : term123 = term35.
Proof. exact (@lem69 term34). Qed.
Lemma lem159111 (h1 : term3) : term35.
Proof. exact (EQ_MP (@lem159110) (@lem159109 h1)). Qed.
Lemma lem159112 : term38.
Proof. exact (fun h0 : term3 => @lem159111 h0). Qed.
Lemma lem159113 : term4.
Proof. exact (EQ_MP (@lem158401) (@lem159112)). Qed.
Lemma lem159115 : term4.
Proof. exact (@lem158222 (@lem159113)). Qed.
Lemma lem159116 (h1 : term3) : term8.
Proof. exact (@lem159115 (@lem158207 h1)). Qed.
Lemma lem159117 (h1 : term3) : False.
Proof. exact (@lem159116 h1 (@lem155916)). Qed.
Lemma lem159118 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem159117 h1) (fun h2 : False => @lem158207 h1)). Qed.
Lemma lem159119 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem159118 h1) (@lem158207 h1)). Qed.
Lemma lem159120 : term2.
Proof. exact (fun h0 : term3 => @lem159119 h0). Qed.
Lemma lem159121 : term1.
Proof. exact (EQ_MP (@lem158206) (@lem159120)). Qed.
