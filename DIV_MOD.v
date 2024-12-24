Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MOD_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIVISION_spec.
Require Import DIV_DIV_spec.
Require Import DIV_ZERO_spec.
Require Import EQ_TRANS_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import LE_ANTISYM_spec.
Require Import LE_RDIV_EQ_spec.
Require Import MOD_0_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1820_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19699_spec.
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
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem220361 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem220365 (m : nat) : term1 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem220366 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem220367 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem220366 m) (@lem220365 m)). Qed.
Lemma lem220368 (m : nat) (n : nat) (p : nat) : term3 m n p.
Proof. exact (@lem220367 m (Nat.mul n p)). Qed.
Lemma lem220369 (m : nat) (n : nat) (p : nat) : (term3 m n p) = (term4 m n p).
Proof. exact (eq_refl (term3 m n p)). Qed.
Lemma lem220370 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (EQ_MP (@lem220369 m n p) (@lem220368 m n p)). Qed.
Lemma lem220371 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem157261 (Nat.div m n)). Qed.
Lemma lem220372 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem220373 (m : nat) (n : nat) : term6 m n.
Proof. exact (EQ_MP (@lem220372 m n) (@lem220371 m n)). Qed.
Lemma lem220374 (m : nat) (n : nat) (p : nat) : term7 m n p.
Proof. exact (@lem220373 m n p). Qed.
Lemma lem220375 (m : nat) (n : nat) (p : nat) : (term7 m n p) = (term8 m n p).
Proof. exact (eq_refl (term7 m n p)). Qed.
Lemma lem220376 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (EQ_MP (@lem220375 m n p) (@lem220374 m n p)). Qed.
Lemma lem220377 {A : Type'} (h1 : term9 A) : term9 A.
Proof. exact (h1). Qed.
Lemma lem220378 {A : Type'} (x : A) (h1 : term9 A) : term10 A x.
Proof. exact (@lem220377 A h1 x). Qed.
Lemma lem220379 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem220380 {A : Type'} (x : A) (h1 : term9 A) : term11 A x.
Proof. exact (EQ_MP (@lem220379 A x) (@lem220378 A x h1)). Qed.
Lemma lem220381 {A : Type'} (x : A) (y : A) (h1 : term9 A) : term12 A x y.
Proof. exact (@lem220380 A x h1 y). Qed.
Lemma lem220382 {A : Type'} (y : A) (x : A) : (term12 A x y) = (term13 A y x).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem220383 {A : Type'} (y : A) (x : A) (h1 : term9 A) : term13 A y x.
Proof. exact (EQ_MP (@lem220382 A y x) (@lem220381 A x y h1)). Qed.
Lemma lem220384 {A : Type'} (y : A) (x : A) (z : A) (h1 : term9 A) : term14 A y x z.
Proof. exact (@lem220383 A y x h1 z). Qed.
Lemma lem220385 {A : Type'} (y : A) (x : A) (z : A) : (term14 A y x z) = (term15 A y x z).
Proof. exact (eq_refl (term14 A y x z)). Qed.
Lemma lem220386 {A : Type'} (y : A) (x : A) (z : A) (h1 : term9 A) : term15 A y x z.
Proof. exact (EQ_MP (@lem220385 A y x z) (@lem220384 A y x z h1)). Qed.
Lemma lem220387 {A : Type'} (x : A) (y : A) (z : A) (h1 : term16 A x y z) : term16 A x y z.
Proof. exact (h1). Qed.
Lemma lem220388 {A : Type'} (x : A) (y : A) (z : A) (h1 : term9 A) (h2 : term16 A x y z) : x = z.
Proof. exact (@lem220386 A y x z h1 (@lem220387 A x y z h2)). Qed.
Lemma lem220389 {A : Type'} (x : A) (y : A) (z : A) (h1 : term16 A x y z) : term17 A x z.
Proof. exact (fun h0 : term9 A => @lem220388 A x y z h0 h1). Qed.
Lemma lem220390 {A : Type'} (x : A) (z : A) (h1 : term18 A x z) : term18 A x z.
Proof. exact (h1). Qed.
Lemma lem220391 {A : Type'} (x : A) (z : A) (h1 : term18 A x z) : term17 A x z.
Proof. exact (ex_elim (@lem220390 A x z h1) (fun y : A => fun h0 : term19 A x z y => @lem220389 A x y z h0)). Qed.
Lemma lem220392 {A : Type'} (h1 : term9 A) : term9 A.
Proof. exact (h1). Qed.
Lemma lem220393 {A : Type'} (x : A) (z : A) (h1 : term9 A) (h2 : term18 A x z) : x = z.
Proof. exact (@lem220391 A x z h2 (@lem220392 A h1)). Qed.
Lemma lem220394 {A : Type'} (x : A) (z : A) (h1 : term9 A) : term20 A x z.
Proof. exact (fun h0 : term18 A x z => @lem220393 A x z h1 h0). Qed.
Lemma lem220395 {A : Type'} (x : A) (h1 : term9 A) : term21 A x.
Proof. exact (fun z : A => @lem220394 A x z h1). Qed.
Lemma lem220396 {A : Type'} (h1 : term9 A) : term22 A.
Proof. exact (fun x : A => @lem220395 A x h1). Qed.
Lemma lem220397 {A : Type'} : term23 A.
Proof. exact (fun h0 : term9 A => @lem220396 A h0). Qed.
Lemma lem220398 {A : Type'} : term22 A.
Proof. exact (@lem220397 A (@lem403 A)). Qed.
Lemma lem220399 {A : Type'} (x : A) : term24 A x.
Proof. exact (@lem220398 A x). Qed.
Lemma lem220400 {A : Type'} (x : A) : (term24 A x) = (term21 A x).
Proof. exact (eq_refl (term24 A x)). Qed.
Lemma lem220401 {A : Type'} (x : A) : term21 A x.
Proof. exact (EQ_MP (@lem220400 A x) (@lem220399 A x)). Qed.
Lemma lem220402 {A : Type'} (x : A) (z : A) : term25 A x z.
Proof. exact (@lem220401 A x z). Qed.
Lemma lem220403 {A : Type'} (x : A) (z : A) : (term25 A x z) = (term20 A x z).
Proof. exact (eq_refl (term25 A x z)). Qed.
Lemma lem220405 (t1 : Prop) : term26 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem220406 (t1 : Prop) : (term26 t1) = (term27 t1).
Proof. exact (eq_refl (term26 t1)). Qed.
Lemma lem220407 (t1 : Prop) : term27 t1.
Proof. exact (EQ_MP (@lem220406 t1) (@lem220405 t1)). Qed.
Lemma lem220408 (t1 : Prop) (t2 : Prop) : term28 t1 t2.
Proof. exact (@lem220407 t1 t2). Qed.
Lemma lem220409 (t1 : Prop) (t2 : Prop) : (term28 t1 t2) = (term29 t1 t2).
Proof. exact (eq_refl (term28 t1 t2)). Qed.
Lemma lem220410 (t1 : Prop) (t2 : Prop) : term29 t1 t2.
Proof. exact (EQ_MP (@lem220409 t1 t2) (@lem220408 t1 t2)). Qed.
Lemma lem220411 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term30 t1 t2 t3.
Proof. exact (@lem220410 t1 t2 t3). Qed.
Lemma lem220412 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term30 t1 t2 t3) = ((term31 t1 t2 t3) = (term32 t1 t2 t3)).
Proof. exact (eq_refl (term30 t1 t2 t3)). Qed.
Lemma lem220413 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term31 t1 t2 t3) = (term32 t1 t2 t3).
Proof. exact (EQ_MP (@lem220412 t1 t2 t3) (@lem220411 t1 t2 t3)). Qed.
Lemma lem220414 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term32 t1 t2 t3) = (term31 t1 t2 t3).
Proof. exact (SYM (@lem220413 t1 t2 t3)). Qed.
Lemma lem220416 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem220417 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (@lem220416 (term34 m n)). Qed.
Lemma lem220418 (m : nat) (n : nat) : (term35 m n) = (term34 m n).
Proof. exact (SYM (@lem220417 m n)). Qed.
Lemma lem220419 (m : nat) (n : nat) (h1 : term36 m n) : term36 m n.
Proof. exact (h1). Qed.
Lemma lem220422 (m : nat) (n : nat) (h1 : term37 m n) : term37 m n.
Proof. exact (h1). Qed.
Lemma lem220423 (m : nat) (n : nat) : term38 m n.
Proof. exact (fun h0 : term37 m n => @lem220422 m n h0). Qed.
Lemma lem220424 (m : nat) (n : nat) (h1 : term38 m n) : term38 m n.
Proof. exact (h1). Qed.
Lemma lem220425 (m : nat) (n : nat) (h1 : term37 m n) : term37 m n.
Proof. exact (h1). Qed.
Lemma lem220426 (m : nat) (n : nat) (h1 : term37 m n) (h2 : term38 m n) : term37 m n.
Proof. exact (@lem220424 m n h2 (@lem220425 m n h1)). Qed.
Lemma lem220427 (m : nat) (n : nat) (h1 : term37 m n) : term39 m n.
Proof. exact (fun h0 : term38 m n => @lem220426 m n h1 h0). Qed.
Lemma lem220428 (m : nat) (n : nat) (h1 : term38 m n) : term38 m n.
Proof. exact (h1). Qed.
Lemma lem220429 (m : nat) (n : nat) (h1 : term37 m n) (h2 : term38 m n) : term37 m n.
Proof. exact (@lem220427 m n h1 (@lem220428 m n h2)). Qed.
Lemma lem220430 (m : nat) (n : nat) (h1 : term38 m n) : term38 m n.
Proof. exact (fun h0 : term37 m n => @lem220429 m n h0 h1). Qed.
Lemma lem220431 (m : nat) (n : nat) : term40 m n.
Proof. exact (fun h0 : term38 m n => @lem220430 m n h0). Qed.
Lemma lem220434 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem220431 m n (@lem220423 m n)). Qed.
Lemma lem220452 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem220453 : term41 = term42.
Proof. exact (@lem220452 term43). Qed.
Lemma lem220464 (m : nat) (n : nat) : (term44 m n) = (term44 m n).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem220465 (m : nat) (n : nat) : (term37 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem220464 m n) (@lem220453)). Qed.
Lemma lem220468 (n : nat) : (term46 n) = (term47 n).
Proof. exact (fun_ext (fun m : nat => @lem220465 m n)). Qed.
Lemma lem220469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220470 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem220469) (@lem220468 n)). Qed.
Lemma lem220475 : term50 = term51.
Proof. exact (fun_ext (fun n : nat => @lem220470 n)). Qed.
Lemma lem220476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220485 : term52 = term53.
Proof. exact (MK_COMB (@lem220476) (@lem220475)). Qed.
Lemma lem220494 (m : nat) (n : nat) : ((term54 n m) = (m = n)) = ((term54 n m) = (m = n)).
Proof. exact (eq_refl ((term54 n m) = (m = n))). Qed.
Lemma lem220495 (m : nat) : (term55 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem220494 m n)). Qed.
Lemma lem220496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220497 (m : nat) : (term56 m) = (term56 m).
Proof. exact (MK_COMB (@lem220496) (@lem220495 m)). Qed.
Lemma lem220498 : term57 = term57.
Proof. exact (fun_ext (fun m : nat => @lem220497 m)). Qed.
Lemma lem220499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220500 : term43 = term43.
Proof. exact (MK_COMB (@lem220499) (@lem220498)). Qed.
Lemma lem220501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem220502 : term42 = term42.
Proof. exact (MK_COMB (@lem220501) (@lem220500)). Qed.
Lemma lem220503 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem220508 (m : nat) (k : nat) (n : nat) : ((Peano.le k m) = (Peano.le k n)) = ((Peano.le k m) = (Peano.le k n)).
Proof. exact (eq_refl ((Peano.le k m) = (Peano.le k n))). Qed.
Lemma lem220509 (m : nat) (n : nat) : (term58 m n) = (term58 m n).
Proof. exact (fun_ext (fun k : nat => @lem220508 m k n)). Qed.
Lemma lem220510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220511 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem220510) (@lem220509 m n)). Qed.
Lemma lem220512 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem220513 (m : nat) (n : nat) : (term60 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem220512) (@lem220511 m n)). Qed.
Lemma lem220514 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem220513 m n) (@lem220503 m n)). Qed.
Lemma lem220515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem220516 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem220515) (@lem220514 m n)). Qed.
Lemma lem220517 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem220518 (m : nat) (n : nat) : (term44 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem220517) (@lem220516 m n)). Qed.
Lemma lem220519 (m : nat) (n : nat) : (term45 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem220518 m n) (@lem220502)). Qed.
Lemma lem220520 (n : nat) : (term47 n) = (term47 n).
Proof. exact (fun_ext (fun m : nat => @lem220519 m n)). Qed.
Lemma lem220521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220522 (n : nat) : (term49 n) = (term49 n).
Proof. exact (MK_COMB (@lem220521) (@lem220520 n)). Qed.
Lemma lem220523 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem220522 n)). Qed.
Lemma lem220524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220525 : term53 = term53.
Proof. exact (MK_COMB (@lem220524) (@lem220523)). Qed.
Lemma lem220564 : term52 = term53.
Proof. exact (TRANS (@lem220485) (@lem220525)). Qed.
Lemma lem220565 : term53 = term52.
Proof. exact (SYM (@lem220564)). Qed.
Lemma lem220566 (m : nat) (n : nat) (h1 : term36 m n) : term36 m n.
Proof. exact (h1). Qed.
Lemma lem220567 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem220582 (m : nat) (k : nat) (n : nat) : ((Peano.le k m) = (Peano.le k n)) = (term61 m k n).
Proof. exact (@lem17784 (Peano.le k m) (Peano.le k n)). Qed.
Lemma lem220583 (m : nat) (n : nat) : (term58 m n) = (term62 m n).
Proof. exact (fun_ext (fun k : nat => @lem220582 m k n)). Qed.
Lemma lem220584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220585 (m : nat) (n : nat) : (term59 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem220584) (@lem220583 m n)). Qed.
Lemma lem220586 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem220587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220588 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem220587) (@lem220585 m n)). Qed.
Lemma lem220589 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem220588 m n) (@lem220586 m n)). Qed.
Lemma lem220590 (m : nat) (n : nat) : (term36 m n) = (term67 m n).
Proof. exact (@lem17362 (term59 m n) (m = n)). Qed.
Lemma lem220591 (m : nat) (n : nat) : (term36 m n) = (term68 m n).
Proof. exact (TRANS (@lem220590 m n) (@lem220589 m n)). Qed.
Lemma lem220593 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem220594 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem220593 nat P Q). Qed.
Lemma lem220595 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (@lem220594 (term75 m n) (term76 m n)). Qed.
Lemma lem220596 (m : nat) (k : nat) (n : nat) : (term77 m n k) = (term78 m k n).
Proof. exact (eq_refl (term77 m n k)). Qed.
Lemma lem220597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220598 (m : nat) (k : nat) (n : nat) : (term79 m n k) = (term80 m k n).
Proof. exact (MK_COMB (@lem220597) (@lem220596 m k n)). Qed.
Lemma lem220599 (m : nat) (k : nat) (n : nat) : (term81 m n k) = (term82 m k n).
Proof. exact (eq_refl (term81 m n k)). Qed.
Lemma lem220600 (m : nat) (k : nat) (n : nat) : (term83 m n k) = (term61 m k n).
Proof. exact (MK_COMB (@lem220598 m k n) (@lem220599 m k n)). Qed.
Lemma lem220601 (m : nat) (n : nat) : (term84 m n) = (term62 m n).
Proof. exact (fun_ext (fun k : nat => @lem220600 m k n)). Qed.
Lemma lem220602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220603 (m : nat) (n : nat) : (term73 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem220602) (@lem220601 m n)). Qed.
Lemma lem220604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem220605 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem220604) (@lem220603 m n)). Qed.
Lemma lem220606 (m : nat) (k : nat) (n : nat) : (term77 m n k) = (term78 m k n).
Proof. exact (eq_refl (term77 m n k)). Qed.
Lemma lem220607 (m : nat) (n : nat) : (term87 m n) = (term75 m n).
Proof. exact (fun_ext (fun k : nat => @lem220606 m k n)). Qed.
Lemma lem220608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220609 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem220608) (@lem220607 m n)). Qed.
Lemma lem220610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220611 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem220610) (@lem220609 m n)). Qed.
Lemma lem220612 (m : nat) (k : nat) (n : nat) : (term81 m n k) = (term82 m k n).
Proof. exact (eq_refl (term81 m n k)). Qed.
Lemma lem220613 (m : nat) (n : nat) : (term92 m n) = (term76 m n).
Proof. exact (fun_ext (fun k : nat => @lem220612 m k n)). Qed.
Lemma lem220614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220615 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (MK_COMB (@lem220614) (@lem220613 m n)). Qed.
Lemma lem220616 (m : nat) (n : nat) : (term74 m n) = (term95 m n).
Proof. exact (MK_COMB (@lem220611 m n) (@lem220615 m n)). Qed.
Lemma lem220617 (m : nat) (n : nat) : ((term73 m n) = (term74 m n)) = ((term63 m n) = (term95 m n)).
Proof. exact (MK_COMB (@lem220605 m n) (@lem220616 m n)). Qed.
Lemma lem220618 (m : nat) (n : nat) : (term63 m n) = (term95 m n).
Proof. exact (EQ_MP (@lem220617 m n) (@lem220595 m n)). Qed.
Lemma lem220715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220716 (m : nat) (n : nat) : (term66 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem220715) (@lem220618 m n)). Qed.
Lemma lem220717 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem220720 (m : nat) (n : nat) : (term68 m n) = (term97 m n).
Proof. exact (MK_COMB (@lem220716 m n) (@lem220717 m n)). Qed.
Lemma lem220721 (m : nat) (n : nat) : (term36 m n) = (term97 m n).
Proof. exact (TRANS (@lem220591 m n) (@lem220720 m n)). Qed.
Lemma lem220722 (m : nat) (n : nat) (h1 : term36 m n) : term97 m n.
Proof. exact (EQ_MP (@lem220721 m n) (@lem220566 m n h1)). Qed.
Lemma lem220731 (n : nat) (m : nat) : (term98 n m) = (term99 n m).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n m)). Qed.
Lemma lem220736 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem220737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem220738 (n : nat) (m : nat) : (term100 n m) = (term101 n m).
Proof. exact (MK_COMB (@lem220737) (@lem220731 n m)). Qed.
Lemma lem220739 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (MK_COMB (@lem220738 n m) (@lem220736 m n)). Qed.
Lemma lem220744 (m : nat) (n : nat) : (term104 m n) = (term104 m n).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem220745 (m : nat) (n : nat) : (term105 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem220744 m n) (@lem220739 m n)). Qed.
Lemma lem220746 (m : nat) (n : nat) : ((term54 n m) = (m = n)) = (term105 m n).
Proof. exact (@lem17784 (term54 n m) (m = n)). Qed.
Lemma lem220747 (m : nat) (n : nat) : ((term54 n m) = (m = n)) = (term106 m n).
Proof. exact (TRANS (@lem220746 m n) (@lem220745 m n)). Qed.
Lemma lem220748 (m : nat) : (term55 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem220747 m n)). Qed.
Lemma lem220749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220750 (m : nat) : (term56 m) = (term108 m).
Proof. exact (MK_COMB (@lem220749) (@lem220748 m)). Qed.
Lemma lem220751 : term57 = term109.
Proof. exact (fun_ext (fun m : nat => @lem220750 m)). Qed.
Lemma lem220752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220753 : term43 = term110.
Proof. exact (MK_COMB (@lem220752) (@lem220751)). Qed.
Lemma lem220759 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem220760 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem220759 nat P Q). Qed.
Lemma lem220761 (m : nat) : (term111 m) = (term112 m).
Proof. exact (@lem220760 (term113 m) (term114 m)). Qed.
Lemma lem220762 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem220763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220764 (m : nat) (n : nat) : (term117 m n) = (term104 m n).
Proof. exact (MK_COMB (@lem220763) (@lem220762 m n)). Qed.
Lemma lem220765 (m : nat) (n : nat) : (term118 m n) = (term103 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem220766 (m : nat) (n : nat) : (term119 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem220764 m n) (@lem220765 m n)). Qed.
Lemma lem220767 (m : nat) : (term120 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem220766 m n)). Qed.
Lemma lem220768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220769 (m : nat) : (term111 m) = (term108 m).
Proof. exact (MK_COMB (@lem220768) (@lem220767 m)). Qed.
Lemma lem220770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem220771 (m : nat) : (term121 m) = (term122 m).
Proof. exact (MK_COMB (@lem220770) (@lem220769 m)). Qed.
Lemma lem220772 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem220773 (m : nat) : (term123 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem220772 m n)). Qed.
Lemma lem220774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220775 (m : nat) : (term124 m) = (term125 m).
Proof. exact (MK_COMB (@lem220774) (@lem220773 m)). Qed.
Lemma lem220776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220777 (m : nat) : (term126 m) = (term127 m).
Proof. exact (MK_COMB (@lem220776) (@lem220775 m)). Qed.
Lemma lem220778 (m : nat) (n : nat) : (term118 m n) = (term103 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem220779 (m : nat) : (term128 m) = (term114 m).
Proof. exact (fun_ext (fun n : nat => @lem220778 m n)). Qed.
Lemma lem220780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220781 (m : nat) : (term129 m) = (term130 m).
Proof. exact (MK_COMB (@lem220780) (@lem220779 m)). Qed.
Lemma lem220782 (m : nat) : (term112 m) = (term131 m).
Proof. exact (MK_COMB (@lem220777 m) (@lem220781 m)). Qed.
Lemma lem220783 (m : nat) : ((term111 m) = (term112 m)) = ((term108 m) = (term131 m)).
Proof. exact (MK_COMB (@lem220771 m) (@lem220782 m)). Qed.
Lemma lem220784 (m : nat) : (term108 m) = (term131 m).
Proof. exact (EQ_MP (@lem220783 m) (@lem220761 m)). Qed.
Lemma lem220881 : term109 = term132.
Proof. exact (fun_ext (fun m : nat => @lem220784 m)). Qed.
Lemma lem220882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220883 : term110 = term133.
Proof. exact (MK_COMB (@lem220882) (@lem220881)). Qed.
Lemma lem220885 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem220886 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem220885 nat P Q). Qed.
Lemma lem220887 : term134 = term135.
Proof. exact (@lem220886 term136 term137). Qed.
Lemma lem220888 (m : nat) : (term138 m) = (term125 m).
Proof. exact (eq_refl (term138 m)). Qed.
Lemma lem220889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220890 (m : nat) : (term139 m) = (term127 m).
Proof. exact (MK_COMB (@lem220889) (@lem220888 m)). Qed.
Lemma lem220891 (m : nat) : (term140 m) = (term130 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem220892 (m : nat) : (term141 m) = (term131 m).
Proof. exact (MK_COMB (@lem220890 m) (@lem220891 m)). Qed.
Lemma lem220893 : term142 = term132.
Proof. exact (fun_ext (fun m : nat => @lem220892 m)). Qed.
Lemma lem220894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220895 : term134 = term133.
Proof. exact (MK_COMB (@lem220894) (@lem220893)). Qed.
Lemma lem220896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem220897 : term143 = term144.
Proof. exact (MK_COMB (@lem220896) (@lem220895)). Qed.
Lemma lem220898 (m : nat) : (term138 m) = (term125 m).
Proof. exact (eq_refl (term138 m)). Qed.
Lemma lem220899 : term145 = term136.
Proof. exact (fun_ext (fun m : nat => @lem220898 m)). Qed.
Lemma lem220900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220901 : term146 = term147.
Proof. exact (MK_COMB (@lem220900) (@lem220899)). Qed.
Lemma lem220902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem220903 : term148 = term149.
Proof. exact (MK_COMB (@lem220902) (@lem220901)). Qed.
Lemma lem220904 (m : nat) : (term140 m) = (term130 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem220905 : term150 = term137.
Proof. exact (fun_ext (fun m : nat => @lem220904 m)). Qed.
Lemma lem220906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220907 : term151 = term152.
Proof. exact (MK_COMB (@lem220906) (@lem220905)). Qed.
Lemma lem220908 : term135 = term153.
Proof. exact (MK_COMB (@lem220903) (@lem220907)). Qed.
Lemma lem220909 : (term134 = term135) = (term133 = term153).
Proof. exact (MK_COMB (@lem220897) (@lem220908)). Qed.
Lemma lem220910 : term133 = term153.
Proof. exact (EQ_MP (@lem220909) (@lem220887)). Qed.
Lemma lem221017 : term110 = term153.
Proof. exact (TRANS (@lem220883) (@lem220910)). Qed.
Lemma lem221018 : term43 = term153.
Proof. exact (TRANS (@lem220753) (@lem221017)). Qed.
Lemma lem221019 (h1 : term43) : term153.
Proof. exact (EQ_MP (@lem221018) (@lem220567 h1)). Qed.
Lemma lem221026 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem221041 (m : nat) (k : nat) (n : nat) : (term82 m k n) = (term82 m k n).
Proof. exact (eq_refl (term82 m k n)). Qed.
Lemma lem221042 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (fun_ext (fun k : nat => @lem221041 m k n)). Qed.
Lemma lem221043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221044 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (MK_COMB (@lem221043) (@lem221042 m n)). Qed.
Lemma lem221059 (m : nat) (k : nat) (n : nat) : (term78 m k n) = (term78 m k n).
Proof. exact (eq_refl (term78 m k n)). Qed.
Lemma lem221060 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (fun_ext (fun k : nat => @lem221059 m k n)). Qed.
Lemma lem221061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221062 (m : nat) (n : nat) : (term89 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem221061) (@lem221060 m n)). Qed.
Lemma lem221063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem221064 (m : nat) (n : nat) : (term91 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem221063) (@lem221062 m n)). Qed.
Lemma lem221065 (m : nat) (n : nat) : (term95 m n) = (term95 m n).
Proof. exact (MK_COMB (@lem221064 m n) (@lem221044 m n)). Qed.
Lemma lem221066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem221067 (m : nat) (n : nat) : (term96 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem221066) (@lem221065 m n)). Qed.
Lemma lem221068 (m : nat) (n : nat) : (term97 m n) = (term97 m n).
Proof. exact (MK_COMB (@lem221067 m n) (@lem221026 m n)). Qed.
Lemma lem221069 (m : nat) (n : nat) (h1 : term36 m n) : term97 m n.
Proof. exact (EQ_MP (@lem221068 m n) (@lem220722 m n h1)). Qed.
Lemma lem221094 (m : nat) (n : nat) : (term103 m n) = (term103 m n).
Proof. exact (eq_refl (term103 m n)). Qed.
Lemma lem221095 (m : nat) : (term114 m) = (term114 m).
Proof. exact (fun_ext (fun n : nat => @lem221094 m n)). Qed.
Lemma lem221096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221097 (m : nat) : (term130 m) = (term130 m).
Proof. exact (MK_COMB (@lem221096) (@lem221095 m)). Qed.
Lemma lem221098 : term137 = term137.
Proof. exact (fun_ext (fun m : nat => @lem221097 m)). Qed.
Lemma lem221099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221100 : term152 = term152.
Proof. exact (MK_COMB (@lem221099) (@lem221098)). Qed.
Lemma lem221123 (m : nat) (n : nat) : (term116 m n) = (term116 m n).
Proof. exact (eq_refl (term116 m n)). Qed.
Lemma lem221124 (m : nat) : (term113 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem221123 m n)). Qed.
Lemma lem221125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221126 (m : nat) : (term125 m) = (term125 m).
Proof. exact (MK_COMB (@lem221125) (@lem221124 m)). Qed.
Lemma lem221127 : term136 = term136.
Proof. exact (fun_ext (fun m : nat => @lem221126 m)). Qed.
Lemma lem221128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221129 : term147 = term147.
Proof. exact (MK_COMB (@lem221128) (@lem221127)). Qed.
Lemma lem221130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem221131 : term149 = term149.
Proof. exact (MK_COMB (@lem221130) (@lem221129)). Qed.
Lemma lem221132 : term153 = term153.
Proof. exact (MK_COMB (@lem221131) (@lem221100)). Qed.
Lemma lem221133 (h1 : term43) : term153.
Proof. exact (EQ_MP (@lem221132) (@lem221019 h1)). Qed.
Lemma lem221134 (h1 : term43) : term152.
Proof. exact (proj2 (@lem221133 h1)). Qed.
Lemma lem221135 (h1 : term43) : term147.
Proof. exact (proj1 (@lem221133 h1)). Qed.
Lemma lem221137 (m : nat) (n : nat) (h1 : term36 m n) : term95 m n.
Proof. exact (proj1 (@lem221069 m n h1)). Qed.
Lemma lem221138 (m : nat) (n : nat) (h1 : term36 m n) : term94 m n.
Proof. exact (proj2 (@lem221137 m n h1)). Qed.
Lemma lem221139 (m : nat) (n : nat) (h1 : term36 m n) : term89 m n.
Proof. exact (proj1 (@lem221137 m n h1)). Qed.
Lemma lem221157 (m : nat) (n : nat) : (term116 m n) = (term154 m n).
Proof. exact (@lem19699 (Peano.le m n) (Peano.le n m) (term64 m n)). Qed.
Lemma lem221158 (m : nat) : (term113 m) = (term155 m).
Proof. exact (fun_ext (fun n : nat => @lem221157 m n)). Qed.
Lemma lem221159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221160 (m : nat) : (term125 m) = (term156 m).
Proof. exact (MK_COMB (@lem221159) (@lem221158 m)). Qed.
Lemma lem221161 : term136 = term157.
Proof. exact (fun_ext (fun m : nat => @lem221160 m)). Qed.
Lemma lem221162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221164 : term147 = term158.
Proof. exact (MK_COMB (@lem221162) (@lem221161)). Qed.
Lemma lem221165 (h1 : term43) : term158.
Proof. exact (EQ_MP (@lem221164) (@lem221135 h1)). Qed.
Lemma lem221179 (m : nat) (n : nat) : (term103 m n) = (term103 m n).
Proof. exact (eq_refl (term103 m n)). Qed.
Lemma lem221180 (m : nat) : (term114 m) = (term114 m).
Proof. exact (fun_ext (fun n : nat => @lem221179 m n)). Qed.
Lemma lem221181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221182 (m : nat) : (term130 m) = (term130 m).
Proof. exact (MK_COMB (@lem221181) (@lem221180 m)). Qed.
Lemma lem221183 : term137 = term137.
Proof. exact (fun_ext (fun m : nat => @lem221182 m)). Qed.
Lemma lem221184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221186 : term152 = term152.
Proof. exact (MK_COMB (@lem221184) (@lem221183)). Qed.
Lemma lem221187 (h1 : term43) : term152.
Proof. exact (EQ_MP (@lem221186) (@lem221134 h1)). Qed.
Lemma lem221199 (m : nat) (k : nat) (n : nat) : (term78 m k n) = (term78 m k n).
Proof. exact (eq_refl (term78 m k n)). Qed.
Lemma lem221200 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (fun_ext (fun k : nat => @lem221199 m k n)). Qed.
Lemma lem221201 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221203 (m : nat) (n : nat) : (term89 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem221201) (@lem221200 m n)). Qed.
Lemma lem221204 (m : nat) (n : nat) (h1 : term36 m n) : term89 m n.
Proof. exact (EQ_MP (@lem221203 m n) (@lem221139 m n h1)). Qed.
Lemma lem221212 (m : nat) (k : nat) (n : nat) : (term82 m k n) = (term82 m k n).
Proof. exact (eq_refl (term82 m k n)). Qed.
Lemma lem221213 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (fun_ext (fun k : nat => @lem221212 m k n)). Qed.
Lemma lem221214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem221216 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (MK_COMB (@lem221214) (@lem221213 m n)). Qed.
Lemma lem221217 (m : nat) (n : nat) (h1 : term36 m n) : term94 m n.
Proof. exact (EQ_MP (@lem221216 m n) (@lem221138 m n h1)). Qed.
Lemma lem221218 (_4400 : nat) (h1 : term43) : term159 _4400.
Proof. exact (@lem221165 h1 _4400). Qed.
Lemma lem221219 (_4400 : nat) : (term159 _4400) = (term156 _4400).
Proof. exact (eq_refl (term159 _4400)). Qed.
Lemma lem221220 (_4400 : nat) (h1 : term43) : term156 _4400.
Proof. exact (EQ_MP (@lem221219 _4400) (@lem221218 _4400 h1)). Qed.
Lemma lem221221 (_4400 : nat) (_4401 : nat) (h1 : term43) : term160 _4400 _4401.
Proof. exact (@lem221220 _4400 h1 _4401). Qed.
Lemma lem221222 (_4400 : nat) (_4401 : nat) : (term160 _4400 _4401) = (term154 _4400 _4401).
Proof. exact (eq_refl (term160 _4400 _4401)). Qed.
Lemma lem221223 (_4400 : nat) (_4401 : nat) (h1 : term43) : term154 _4400 _4401.
Proof. exact (EQ_MP (@lem221222 _4400 _4401) (@lem221221 _4400 _4401 h1)). Qed.
Lemma lem221224 (_4402 : nat) (h1 : term43) : term140 _4402.
Proof. exact (@lem221187 h1 _4402). Qed.
Lemma lem221225 (_4402 : nat) : (term140 _4402) = (term130 _4402).
Proof. exact (eq_refl (term140 _4402)). Qed.
Lemma lem221226 (_4402 : nat) (h1 : term43) : term130 _4402.
Proof. exact (EQ_MP (@lem221225 _4402) (@lem221224 _4402 h1)). Qed.
Lemma lem221227 (_4402 : nat) (_4403 : nat) (h1 : term43) : term118 _4402 _4403.
Proof. exact (@lem221226 _4402 h1 _4403). Qed.
Lemma lem221228 (_4402 : nat) (_4403 : nat) : (term118 _4402 _4403) = (term103 _4402 _4403).
Proof. exact (eq_refl (term118 _4402 _4403)). Qed.
Lemma lem221229 (_4402 : nat) (_4403 : nat) (h1 : term43) : term103 _4402 _4403.
Proof. exact (EQ_MP (@lem221228 _4402 _4403) (@lem221227 _4402 _4403 h1)). Qed.
Lemma lem221230 (_4404 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term77 m n _4404.
Proof. exact (@lem221204 m n h1 _4404). Qed.
Lemma lem221231 (m : nat) (_4404 : nat) (n : nat) : (term77 m n _4404) = (term78 m _4404 n).
Proof. exact (eq_refl (term77 m n _4404)). Qed.
Lemma lem221233 (_4405 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term81 m n _4405.
Proof. exact (@lem221217 m n h1 _4405). Qed.
Lemma lem221234 (m : nat) (_4405 : nat) (n : nat) : (term81 m n _4405) = (term82 m _4405 n).
Proof. exact (eq_refl (term81 m n _4405)). Qed.
Lemma lem221248 (_4402 : nat) (_4403 : nat) : (term103 _4402 _4403) = (term161 _4402 _4403).
Proof. exact (@lem220414 (term162 _4402 _4403) (term162 _4403 _4402) (_4402 = _4403)). Qed.
Lemma lem221249 (_4402 : nat) (_4403 : nat) (h1 : term43) : term161 _4402 _4403.
Proof. exact (EQ_MP (@lem221248 _4402 _4403) (@lem221229 _4402 _4403 h1)). Qed.
Lemma lem221251 (m : nat) (n : nat) (h1 : term36 m n) : term64 m n.
Proof. exact (proj2 (@lem221069 m n h1)). Qed.
Lemma lem221257 (_4404 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term78 m _4404 n.
Proof. exact (EQ_MP (@lem221231 m _4404 n) (@lem221230 _4404 m n h1)). Qed.
Lemma lem221263 (_4405 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term82 m _4405 n.
Proof. exact (EQ_MP (@lem221234 m _4405 n) (@lem221233 _4405 m n h1)). Qed.
Lemma lem221275 (_4400 : nat) (_4401 : nat) (h1 : term43) : term163 _4400 _4401.
Proof. exact (proj2 (@lem221223 _4400 _4401 h1)). Qed.
Lemma lem221298 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem221299 (m : nat) : m = m.
Proof. exact (@lem221298 m). Qed.
Lemma lem221300 (m : nat) : term164 m.
Proof. exact (fun h0 : term165 m => @lem221299 m). Qed.
Lemma lem221302 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221303 (m : nat) : (term164 m) = (m = m).
Proof. exact (@lem221302 (m = m)). Qed.
Lemma lem221304 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem221303 m) (@lem221300 m)). Qed.
Lemma lem221306 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem221307 (_4401 : nat) (_4400 : nat) : (term163 _4400 _4401) = (term168 _4401 _4400).
Proof. exact (@lem221306 (term64 _4400 _4401) (Peano.le _4401 _4400)). Qed.
Lemma lem221309 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem221310 (_4400 : nat) (_4401 : nat) : (term170 _4400 _4401) = (_4400 = _4401).
Proof. exact (@lem221309 (_4400 = _4401)). Qed.
Lemma lem221311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem221312 (_4400 : nat) (_4401 : nat) : (term171 _4400 _4401) = (term172 _4400 _4401).
Proof. exact (MK_COMB (@lem221311) (@lem221310 _4400 _4401)). Qed.
Lemma lem221313 (_4401 : nat) (_4400 : nat) : (Peano.le _4401 _4400) = (Peano.le _4401 _4400).
Proof. exact (eq_refl (Peano.le _4401 _4400)). Qed.
Lemma lem221314 (_4401 : nat) (_4400 : nat) : (term168 _4401 _4400) = (term173 _4401 _4400).
Proof. exact (MK_COMB (@lem221312 _4400 _4401) (@lem221313 _4401 _4400)). Qed.
Lemma lem221315 (_4401 : nat) (_4400 : nat) : (term163 _4400 _4401) = (term173 _4401 _4400).
Proof. exact (TRANS (@lem221307 _4401 _4400) (@lem221314 _4401 _4400)). Qed.
Lemma lem221318 (_4401 : nat) (_4400 : nat) (h1 : term43) : term173 _4401 _4400.
Proof. exact (EQ_MP (@lem221315 _4401 _4400) (@lem221275 _4400 _4401 h1)). Qed.
Lemma lem221319 (m : nat) (h1 : term43) : term174 m.
Proof. exact (@lem221318 m m h1). Qed.
Lemma lem221322 (m : nat) (h1 : term43) : Peano.le m m.
Proof. exact (@lem221319 m h1 (@lem221304 m)). Qed.
Lemma lem221323 (m : nat) (h1 : term43) : term175 m.
Proof. exact (fun h0 : term176 m => @lem221322 m h1). Qed.
Lemma lem221325 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221326 (m : nat) : (term175 m) = (Peano.le m m).
Proof. exact (@lem221325 (Peano.le m m)). Qed.
Lemma lem221327 (m : nat) (h1 : term43) : Peano.le m m.
Proof. exact (EQ_MP (@lem221326 m) (@lem221323 m h1)). Qed.
Lemma lem221333 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem221334 (n : nat) (_4405 : nat) (m : nat) : (term82 m _4405 n) = (term78 n _4405 m).
Proof. exact (@lem221333 (Peano.le _4405 n) (term162 _4405 m)). Qed.
Lemma lem221340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem221341 (n : nat) (_4405 : nat) (m : nat) : (term177 m _4405 n) = (term178 n _4405 m).
Proof. exact (MK_COMB (@lem221340) (@lem221334 n _4405 m)). Qed.
Lemma lem221347 (n : nat) (_4405 : nat) (m : nat) : (term78 n _4405 m) = (term78 n _4405 m).
Proof. exact (eq_refl (term78 n _4405 m)). Qed.
Lemma lem221348 (n : nat) (_4405 : nat) (m : nat) : ((term82 m _4405 n) = (term78 n _4405 m)) = ((term78 n _4405 m) = (term78 n _4405 m)).
Proof. exact (MK_COMB (@lem221341 n _4405 m) (@lem221347 n _4405 m)). Qed.
Lemma lem221350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem221351 (x : Prop) : (x = x) = True.
Proof. exact (@lem221350 Prop x). Qed.
Lemma lem221352 (n : nat) (_4405 : nat) (m : nat) : ((term78 n _4405 m) = (term78 n _4405 m)) = True.
Proof. exact (@lem221351 (term78 n _4405 m)). Qed.
Lemma lem221353 (n : nat) (_4405 : nat) (m : nat) : ((term82 m _4405 n) = (term78 n _4405 m)) = True.
Proof. exact (TRANS (@lem221348 n _4405 m) (@lem221352 n _4405 m)). Qed.
Lemma lem221354 (n : nat) (_4405 : nat) (m : nat) : True = ((term82 m _4405 n) = (term78 n _4405 m)).
Proof. exact (SYM (@lem221353 n _4405 m)). Qed.
Lemma lem221355 (n : nat) (_4405 : nat) (m : nat) : (term82 m _4405 n) = (term78 n _4405 m).
Proof. exact (EQ_MP (@lem221354 n _4405 m) (@lem0)). Qed.
Lemma lem221356 (_4405 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term78 n _4405 m.
Proof. exact (EQ_MP (@lem221355 n _4405 m) (@lem221263 _4405 m n h1)). Qed.
Lemma lem221358 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem221359 (m : nat) (_4405 : nat) (n : nat) : (term78 n _4405 m) = (term179 m _4405 n).
Proof. exact (@lem221358 (term162 _4405 m) (Peano.le _4405 n)). Qed.
Lemma lem221361 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem221362 (_4405 : nat) (m : nat) : (term180 _4405 m) = (Peano.le _4405 m).
Proof. exact (@lem221361 (Peano.le _4405 m)). Qed.
Lemma lem221363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem221364 (_4405 : nat) (m : nat) : (term181 _4405 m) = (term182 _4405 m).
Proof. exact (MK_COMB (@lem221363) (@lem221362 _4405 m)). Qed.
Lemma lem221365 (_4405 : nat) (n : nat) : (Peano.le _4405 n) = (Peano.le _4405 n).
Proof. exact (eq_refl (Peano.le _4405 n)). Qed.
Lemma lem221366 (m : nat) (_4405 : nat) (n : nat) : (term179 m _4405 n) = (term183 m _4405 n).
Proof. exact (MK_COMB (@lem221364 _4405 m) (@lem221365 _4405 n)). Qed.
Lemma lem221367 (m : nat) (_4405 : nat) (n : nat) : (term78 n _4405 m) = (term183 m _4405 n).
Proof. exact (TRANS (@lem221359 m _4405 n) (@lem221366 m _4405 n)). Qed.
Lemma lem221370 (_4405 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term183 m _4405 n.
Proof. exact (EQ_MP (@lem221367 m _4405 n) (@lem221356 _4405 m n h1)). Qed.
Lemma lem221371 (m : nat) (n : nat) (h1 : term36 m n) : term184 m n.
Proof. exact (@lem221370 m m n h1). Qed.
Lemma lem221374 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : Peano.le m n.
Proof. exact (@lem221371 m n h2 (@lem221327 m h1)). Qed.
Lemma lem221375 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : term185 m n.
Proof. exact (fun h0 : term162 m n => @lem221374 m n h1 h2). Qed.
Lemma lem221377 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221378 (m : nat) (n : nat) : (term185 m n) = (Peano.le m n).
Proof. exact (@lem221377 (Peano.le m n)). Qed.
Lemma lem221379 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem221378 m n) (@lem221375 m n h1 h2)). Qed.
Lemma lem221381 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem221382 (n : nat) : n = n.
Proof. exact (@lem221381 n). Qed.
Lemma lem221383 (n : nat) : term164 n.
Proof. exact (fun h0 : term165 n => @lem221382 n). Qed.
Lemma lem221385 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221386 (n : nat) : (term164 n) = (n = n).
Proof. exact (@lem221385 (n = n)). Qed.
Lemma lem221387 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem221386 n) (@lem221383 n)). Qed.
Lemma lem221389 (_4401 : nat) (_4400 : nat) (h1 : term43) : term173 _4401 _4400.
Proof. exact (EQ_MP (@lem221315 _4401 _4400) (@lem221275 _4400 _4401 h1)). Qed.
Lemma lem221390 (n : nat) (h1 : term43) : term174 n.
Proof. exact (@lem221389 n n h1). Qed.
Lemma lem221393 (n : nat) (h1 : term43) : Peano.le n n.
Proof. exact (@lem221390 n h1 (@lem221387 n)). Qed.
Lemma lem221394 (n : nat) (h1 : term43) : term175 n.
Proof. exact (fun h0 : term176 n => @lem221393 n h1). Qed.
Lemma lem221396 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221397 (n : nat) : (term175 n) = (Peano.le n n).
Proof. exact (@lem221396 (Peano.le n n)). Qed.
Lemma lem221398 (n : nat) (h1 : term43) : Peano.le n n.
Proof. exact (EQ_MP (@lem221397 n) (@lem221394 n h1)). Qed.
Lemma lem221400 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem221401 (n : nat) (_4404 : nat) (m : nat) : (term78 m _4404 n) = (term179 n _4404 m).
Proof. exact (@lem221400 (term162 _4404 n) (Peano.le _4404 m)). Qed.
Lemma lem221403 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem221404 (_4404 : nat) (n : nat) : (term180 _4404 n) = (Peano.le _4404 n).
Proof. exact (@lem221403 (Peano.le _4404 n)). Qed.
Lemma lem221405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem221406 (_4404 : nat) (n : nat) : (term181 _4404 n) = (term182 _4404 n).
Proof. exact (MK_COMB (@lem221405) (@lem221404 _4404 n)). Qed.
Lemma lem221407 (_4404 : nat) (m : nat) : (Peano.le _4404 m) = (Peano.le _4404 m).
Proof. exact (eq_refl (Peano.le _4404 m)). Qed.
Lemma lem221408 (n : nat) (_4404 : nat) (m : nat) : (term179 n _4404 m) = (term183 n _4404 m).
Proof. exact (MK_COMB (@lem221406 _4404 n) (@lem221407 _4404 m)). Qed.
Lemma lem221409 (n : nat) (_4404 : nat) (m : nat) : (term78 m _4404 n) = (term183 n _4404 m).
Proof. exact (TRANS (@lem221401 n _4404 m) (@lem221408 n _4404 m)). Qed.
Lemma lem221412 (_4404 : nat) (m : nat) (n : nat) (h1 : term36 m n) : term183 n _4404 m.
Proof. exact (EQ_MP (@lem221409 n _4404 m) (@lem221257 _4404 m n h1)). Qed.
Lemma lem221413 (m : nat) (n : nat) (h1 : term36 m n) : term184 n m.
Proof. exact (@lem221412 n m n h1). Qed.
Lemma lem221416 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : Peano.le n m.
Proof. exact (@lem221413 m n h2 (@lem221398 n h1)). Qed.
Lemma lem221417 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : term185 n m.
Proof. exact (fun h0 : term162 n m => @lem221416 m n h1 h2). Qed.
Lemma lem221419 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221420 (n : nat) (m : nat) : (term185 n m) = (Peano.le n m).
Proof. exact (@lem221419 (Peano.le n m)). Qed.
Lemma lem221421 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : Peano.le n m.
Proof. exact (EQ_MP (@lem221420 n m) (@lem221417 m n h1 h2)). Qed.
Lemma lem221437 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem221438 (_4403 : nat) (_4402 : nat) : (term186 _4402 _4403) = (term187 _4403 _4402).
Proof. exact (@lem221437 (_4402 = _4403) (term162 _4403 _4402)). Qed.
Lemma lem221446 (_4402 : nat) (_4403 : nat) : (term188 _4402 _4403) = (term188 _4402 _4403).
Proof. exact (eq_refl (term188 _4402 _4403)). Qed.
Lemma lem221447 (_4403 : nat) (_4402 : nat) : (term161 _4402 _4403) = (term189 _4403 _4402).
Proof. exact (MK_COMB (@lem221446 _4402 _4403) (@lem221438 _4403 _4402)). Qed.
Lemma lem221451 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem221452 (_4403 : nat) (_4402 : nat) : (term189 _4403 _4402) = (term190 _4403 _4402).
Proof. exact (@lem221451 (_4402 = _4403) (term162 _4402 _4403) (term162 _4403 _4402)). Qed.
Lemma lem221470 (_4403 : nat) (_4402 : nat) : (term161 _4402 _4403) = (term190 _4403 _4402).
Proof. exact (TRANS (@lem221447 _4403 _4402) (@lem221452 _4403 _4402)). Qed.
Lemma lem221471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem221472 (_4403 : nat) (_4402 : nat) : (term191 _4402 _4403) = (term192 _4403 _4402).
Proof. exact (MK_COMB (@lem221471) (@lem221470 _4403 _4402)). Qed.
Lemma lem221490 (_4403 : nat) (_4402 : nat) : (term190 _4403 _4402) = (term190 _4403 _4402).
Proof. exact (eq_refl (term190 _4403 _4402)). Qed.
Lemma lem221491 (_4403 : nat) (_4402 : nat) : ((term161 _4402 _4403) = (term190 _4403 _4402)) = ((term190 _4403 _4402) = (term190 _4403 _4402)).
Proof. exact (MK_COMB (@lem221472 _4403 _4402) (@lem221490 _4403 _4402)). Qed.
Lemma lem221493 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem221494 (x : Prop) : (x = x) = True.
Proof. exact (@lem221493 Prop x). Qed.
Lemma lem221495 (_4403 : nat) (_4402 : nat) : ((term190 _4403 _4402) = (term190 _4403 _4402)) = True.
Proof. exact (@lem221494 (term190 _4403 _4402)). Qed.
Lemma lem221496 (_4403 : nat) (_4402 : nat) : ((term161 _4402 _4403) = (term190 _4403 _4402)) = True.
Proof. exact (TRANS (@lem221491 _4403 _4402) (@lem221495 _4403 _4402)). Qed.
Lemma lem221497 (_4403 : nat) (_4402 : nat) : True = ((term161 _4402 _4403) = (term190 _4403 _4402)).
Proof. exact (SYM (@lem221496 _4403 _4402)). Qed.
Lemma lem221498 (_4403 : nat) (_4402 : nat) : (term161 _4402 _4403) = (term190 _4403 _4402).
Proof. exact (EQ_MP (@lem221497 _4403 _4402) (@lem0)). Qed.
Lemma lem221499 (_4403 : nat) (_4402 : nat) (h1 : term43) : term190 _4403 _4402.
Proof. exact (EQ_MP (@lem221498 _4403 _4402) (@lem221249 _4402 _4403 h1)). Qed.
Lemma lem221501 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem221502 (_4402 : nat) (_4403 : nat) : (term190 _4403 _4402) = (term193 _4402 _4403).
Proof. exact (@lem221501 (term99 _4403 _4402) (_4402 = _4403)). Qed.
Lemma lem221504 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem221505 (_4403 : nat) (_4402 : nat) : (term196 _4403 _4402) = (term197 _4403 _4402).
Proof. exact (@lem221504 (term162 _4402 _4403) (term162 _4403 _4402)). Qed.
Lemma lem221507 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem221508 (_4402 : nat) (_4403 : nat) : (term180 _4402 _4403) = (Peano.le _4402 _4403).
Proof. exact (@lem221507 (Peano.le _4402 _4403)). Qed.
Lemma lem221509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem221510 (_4402 : nat) (_4403 : nat) : (term198 _4402 _4403) = (term199 _4402 _4403).
Proof. exact (MK_COMB (@lem221509) (@lem221508 _4402 _4403)). Qed.
Lemma lem221512 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem221513 (_4403 : nat) (_4402 : nat) : (term180 _4403 _4402) = (Peano.le _4403 _4402).
Proof. exact (@lem221512 (Peano.le _4403 _4402)). Qed.
Lemma lem221514 (_4403 : nat) (_4402 : nat) : (term197 _4403 _4402) = (term54 _4403 _4402).
Proof. exact (MK_COMB (@lem221510 _4402 _4403) (@lem221513 _4403 _4402)). Qed.
Lemma lem221515 (_4403 : nat) (_4402 : nat) : (term196 _4403 _4402) = (term54 _4403 _4402).
Proof. exact (TRANS (@lem221505 _4403 _4402) (@lem221514 _4403 _4402)). Qed.
Lemma lem221516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem221517 (_4403 : nat) (_4402 : nat) : (term200 _4403 _4402) = (term201 _4403 _4402).
Proof. exact (MK_COMB (@lem221516) (@lem221515 _4403 _4402)). Qed.
Lemma lem221518 (_4402 : nat) (_4403 : nat) : (_4402 = _4403) = (_4402 = _4403).
Proof. exact (eq_refl (_4402 = _4403)). Qed.
Lemma lem221519 (_4402 : nat) (_4403 : nat) : (term193 _4402 _4403) = (term202 _4402 _4403).
Proof. exact (MK_COMB (@lem221517 _4403 _4402) (@lem221518 _4402 _4403)). Qed.
Lemma lem221520 (_4402 : nat) (_4403 : nat) : (term190 _4403 _4402) = (term202 _4402 _4403).
Proof. exact (TRANS (@lem221502 _4402 _4403) (@lem221519 _4402 _4403)). Qed.
Lemma lem221522 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : term54 n m.
Proof. exact (conj (@lem221379 m n h1 h2) (@lem221421 m n h1 h2)). Qed.
Lemma lem221524 (_4402 : nat) (_4403 : nat) (h1 : term43) : term202 _4402 _4403.
Proof. exact (EQ_MP (@lem221520 _4402 _4403) (@lem221499 _4403 _4402 h1)). Qed.
Lemma lem221525 (m : nat) (n : nat) (h1 : term43) : term202 m n.
Proof. exact (@lem221524 m n h1). Qed.
Lemma lem221528 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : m = n.
Proof. exact (@lem221525 m n h1 (@lem221522 m n h1 h2)). Qed.
Lemma lem221529 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : term203 m n.
Proof. exact (fun h0 : term64 m n => @lem221528 m n h1 h2). Qed.
Lemma lem221531 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221532 (m : nat) (n : nat) : (term203 m n) = (m = n).
Proof. exact (@lem221531 (m = n)). Qed.
Lemma lem221533 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : m = n.
Proof. exact (EQ_MP (@lem221532 m n) (@lem221529 m n h1 h2)). Qed.
Lemma lem221536 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem221538 (m : nat) (n : nat) : (term64 m n) = (term204 m n).
Proof. exact (@lem221536 (m = n)). Qed.
Lemma lem221541 (m : nat) (n : nat) (h1 : term36 m n) : term204 m n.
Proof. exact (EQ_MP (@lem221538 m n) (@lem221251 m n h1)). Qed.
Lemma lem221544 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : False.
Proof. exact (@lem221541 m n h2 (@lem221533 m n h1 h2)). Qed.
Lemma lem221545 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : term205.
Proof. exact (fun h0 : ~ False => @lem221544 m n h1 h2). Qed.
Lemma lem221547 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem221548 : term205 = False.
Proof. exact (@lem221547 False). Qed.
Lemma lem221549 (m : nat) (n : nat) (h1 : term43) (h2 : term36 m n) : False.
Proof. exact (EQ_MP (@lem221548) (@lem221545 m n h1 h2)). Qed.
Lemma lem221550 (m : nat) (n : nat) (h1 : term36 m n) : term41.
Proof. exact (fun h0 : term43 => @lem221549 m n h0 h1). Qed.
Lemma lem221551 : term41 = term42.
Proof. exact (@lem69 term43). Qed.
Lemma lem221552 (m : nat) (n : nat) (h1 : term36 m n) : term42.
Proof. exact (EQ_MP (@lem221551) (@lem221550 m n h1)). Qed.
Lemma lem221553 (m : nat) (n : nat) : term45 m n.
Proof. exact (fun h0 : term36 m n => @lem221552 m n h0). Qed.
Lemma lem221558 (n : nat) : term49 n.
Proof. exact (fun m : nat => @lem221553 m n). Qed.
Lemma lem221563 : term53.
Proof. exact (fun n : nat => @lem221558 n). Qed.
Lemma lem221564 : term52.
Proof. exact (EQ_MP (@lem220565) (@lem221563)). Qed.
Lemma lem221565 (n : nat) : term206 n.
Proof. exact (@lem221564 n). Qed.
Lemma lem221566 (n : nat) : (term206 n) = (term48 n).
Proof. exact (eq_refl (term206 n)). Qed.
Lemma lem221567 (n : nat) : term48 n.
Proof. exact (EQ_MP (@lem221566 n) (@lem221565 n)). Qed.
Lemma lem221568 (n : nat) (m : nat) : term207 n m.
Proof. exact (@lem221567 n m). Qed.
Lemma lem221569 (m : nat) (n : nat) : (term207 n m) = (term37 m n).
Proof. exact (eq_refl (term207 n m)). Qed.
Lemma lem221570 (m : nat) (n : nat) : term37 m n.
Proof. exact (EQ_MP (@lem221569 m n) (@lem221568 n m)). Qed.
Lemma lem221572 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem220434 m n (@lem221570 m n)). Qed.
Lemma lem221573 (m : nat) (n : nat) (h1 : term36 m n) : term41.
Proof. exact (@lem221572 m n (@lem220419 m n h1)). Qed.
Lemma lem221574 (m : nat) (n : nat) (h1 : term36 m n) : False.
Proof. exact (@lem221573 m n h1 (@lem92426)). Qed.
Lemma lem221575 (m : nat) (n : nat) (h1 : term36 m n) : (term36 m n) = False.
Proof. exact (prop_ext (fun h2 : term36 m n => @lem221574 m n h1) (fun h2 : False => @lem220419 m n h1)). Qed.
Lemma lem221576 (m : nat) (n : nat) (h1 : term36 m n) : False.
Proof. exact (EQ_MP (@lem221575 m n h1) (@lem220419 m n h1)). Qed.
Lemma lem221577 (m : nat) (n : nat) : term35 m n.
Proof. exact (fun h0 : term36 m n => @lem221576 m n h0). Qed.
Lemma lem221578 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem220418 m n) (@lem221577 m n)). Qed.
Lemma lem221579 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem221580 (m : nat) (n : nat) (h1 : term59 m n) : term59 m n.
Proof. exact (h1). Qed.
Lemma lem221581 (m : nat) (n : nat) (h1 : term59 m n) (h2 : term34 m n) : m = n.
Proof. exact (@lem221579 m n h2 (@lem221580 m n h1)). Qed.
Lemma lem221582 (m : nat) (n : nat) (h1 : term59 m n) : term208 m n.
Proof. exact (fun h0 : term34 m n => @lem221581 m n h1 h0). Qed.
Lemma lem221583 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem221584 (m : nat) (n : nat) (h1 : term59 m n) (h2 : term34 m n) : m = n.
Proof. exact (@lem221582 m n h1 (@lem221583 m n h2)). Qed.
Lemma lem221585 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (fun h0 : term59 m n => @lem221584 m n h0 h1). Qed.
Lemma lem221586 (m : nat) (n : nat) : term209 m n.
Proof. exact (fun h0 : term34 m n => @lem221585 m n h0). Qed.
Lemma lem221588 (n : nat) : term210 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem221589 (n : nat) : (term210 n) = (term211 n).
Proof. exact (eq_refl (term210 n)). Qed.
Lemma lem221590 (n : nat) : term211 n.
Proof. exact (EQ_MP (@lem221589 n) (@lem221588 n)). Qed.
Lemma lem221592 (n : nat) (h1 : term212 n) : term212 n.
Proof. exact (h1). Qed.
Lemma lem221593 (p : nat) : term210 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem221594 (p : nat) : (term210 p) = (term211 p).
Proof. exact (eq_refl (term210 p)). Qed.
Lemma lem221595 (p : nat) : term211 p.
Proof. exact (EQ_MP (@lem221594 p) (@lem221593 p)). Qed.
Lemma lem221597 (p : nat) (h1 : term212 p) : term212 p.
Proof. exact (h1). Qed.
Lemma lem221598 : term213.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem221624 : term214.
Proof. exact (proj1 (@lem221598)). Qed.
Lemma lem221625 (m : nat) : term215 m.
Proof. exact (@lem221624 m). Qed.
Lemma lem221626 (m : nat) : (term215 m) = ((term216 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term215 m)). Qed.
Lemma lem221632 (n : nat) : term217 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem221633 (n : nat) : (term217 n) = ((term218 n) = n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem221638 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem221639 (m : nat) (n : nat) : (term219 m n) = (term219 m n).
Proof. exact (eq_refl (term219 m n)). Qed.
Lemma lem221640 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term220 m n p) = (term221 m n).
Proof. exact (MK_COMB (@lem221639 m n) (@lem221638 p h1)). Qed.
Lemma lem221642 (n : nat) : (term218 n) = n.
Proof. exact (EQ_MP (@lem221633 n) (@lem221632 n)). Qed.
Lemma lem221643 (m : nat) (n : nat) : (term221 m n) = (Nat.div m n).
Proof. exact (@lem221642 (Nat.div m n)). Qed.
Lemma lem221644 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term220 m n p) = (Nat.div m n).
Proof. exact (TRANS (@lem221640 m n p h1) (@lem221643 m n)). Qed.
Lemma lem221645 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem221646 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term222 m n p) = (term223 m n).
Proof. exact (MK_COMB (@lem221645) (@lem221644 m n p h1)). Qed.
Lemma lem221648 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem221649 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem221650 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (term216 n).
Proof. exact (MK_COMB (@lem221649 n) (@lem221648 p h1)). Qed.
Lemma lem221652 (m : nat) : (term216 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem221626 m) (@lem221625 m)). Qed.
Lemma lem221653 (n : nat) : (term216 n) = (NUMERAL 0).
Proof. exact (@lem221652 n). Qed.
Lemma lem221654 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem221650 n p h1) (@lem221653 n)). Qed.
Lemma lem221655 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem221656 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term224 m n p) = (term218 m).
Proof. exact (MK_COMB (@lem221655 m) (@lem221654 n p h1)). Qed.
Lemma lem221658 (n : nat) : (term218 n) = n.
Proof. exact (EQ_MP (@lem221633 n) (@lem221632 n)). Qed.
Lemma lem221659 (m : nat) : (term218 m) = m.
Proof. exact (@lem221658 m). Qed.
Lemma lem221660 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term224 m n p) = m.
Proof. exact (TRANS (@lem221656 n m p h1) (@lem221659 m)). Qed.
Lemma lem221661 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem221662 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term225 m n p) = (Nat.div m).
Proof. exact (MK_COMB (@lem221661) (@lem221660 n m p h1)). Qed.
Lemma lem221663 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem221664 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term226 m p n) = (Nat.div m n).
Proof. exact (MK_COMB (@lem221662 n m p h1) (@lem221663 n)). Qed.
Lemma lem221665 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term220 m n p) = (term226 m p n)) = ((Nat.div m n) = (Nat.div m n)).
Proof. exact (MK_COMB (@lem221646 m n p h1) (@lem221664 m n p h1)). Qed.
Lemma lem221667 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem221668 (x : nat) : (x = x) = True.
Proof. exact (@lem221667 nat x). Qed.
Lemma lem221669 (m : nat) (n : nat) : ((Nat.div m n) = (Nat.div m n)) = True.
Proof. exact (@lem221668 (Nat.div m n)). Qed.
Lemma lem221670 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term220 m n p) = (term226 m p n)) = True.
Proof. exact (TRANS (@lem221665 m n p h1) (@lem221669 m n)). Qed.
Lemma lem221671 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = ((term220 m n p) = (term226 m p n)).
Proof. exact (SYM (@lem221670 m n p h1)). Qed.
Lemma lem221672 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term220 m n p) = (term226 m p n).
Proof. exact (EQ_MP (@lem221671 m n p h1) (@lem0)). Qed.
Lemma lem221727 (n : nat) : term227 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem221728 (n : nat) : (term227 n) = ((term228 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term227 n)). Qed.
Lemma lem221760 : term229.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem221761 (n : nat) : term230 n.
Proof. exact (@lem221760 n). Qed.
Lemma lem221762 (n : nat) : (term230 n) = ((term231 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term230 n)). Qed.
Lemma lem221764 (n : nat) : term232 n.
Proof. exact (@lem170050 n). Qed.
Lemma lem221765 (n : nat) : (term232 n) = ((term233 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem221783 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem221784 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem221785 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term228 m).
Proof. exact (MK_COMB (@lem221784 m) (@lem221783 n h1)). Qed.
Lemma lem221787 (n : nat) : (term228 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem221728 n) (@lem221727 n)). Qed.
Lemma lem221788 (m : nat) : (term228 m) = (NUMERAL 0).
Proof. exact (@lem221787 m). Qed.
Lemma lem221789 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem221785 m n h1) (@lem221788 m)). Qed.
Lemma lem221790 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem221791 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term219 m n) = term234.
Proof. exact (MK_COMB (@lem221790) (@lem221789 m n h1)). Qed.
Lemma lem221792 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem221793 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term220 m n p) = (term233 p).
Proof. exact (MK_COMB (@lem221791 m n h1) (@lem221792 p)). Qed.
Lemma lem221795 (n : nat) : (term233 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem221765 n) (@lem221764 n)). Qed.
Lemma lem221796 (p : nat) : (term233 p) = (NUMERAL 0).
Proof. exact (@lem221795 p). Qed.
Lemma lem221797 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term220 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem221793 m p n h1) (@lem221796 p)). Qed.
Lemma lem221798 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem221799 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term222 m n p) = term235.
Proof. exact (MK_COMB (@lem221798) (@lem221797 m p n h1)). Qed.
Lemma lem221801 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem221802 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem221803 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term236.
Proof. exact (MK_COMB (@lem221802) (@lem221801 n h1)). Qed.
Lemma lem221804 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem221805 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (term231 p).
Proof. exact (MK_COMB (@lem221803 n h1) (@lem221804 p)). Qed.
Lemma lem221807 (n : nat) : (term231 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem221762 n) (@lem221761 n)). Qed.
Lemma lem221808 (p : nat) : (term231 p) = (NUMERAL 0).
Proof. exact (@lem221807 p). Qed.
Lemma lem221809 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem221805 p n h1) (@lem221808 p)). Qed.
Lemma lem221810 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem221811 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term224 m n p) = (term218 m).
Proof. exact (MK_COMB (@lem221810 m) (@lem221809 p n h1)). Qed.
Lemma lem221812 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem221813 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term225 m n p) = (term237 m).
Proof. exact (MK_COMB (@lem221812) (@lem221811 p m n h1)). Qed.
Lemma lem221815 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem221816 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term226 m p n) = (term238 m).
Proof. exact (MK_COMB (@lem221813 p m n h1) (@lem221815 n h1)). Qed.
Lemma lem221818 (n : nat) : (term228 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem221728 n) (@lem221727 n)). Qed.
Lemma lem221819 (m : nat) : (term238 m) = (NUMERAL 0).
Proof. exact (@lem221818 (term218 m)). Qed.
Lemma lem221820 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term226 m p n) = (NUMERAL 0).
Proof. exact (TRANS (@lem221816 p m n h1) (@lem221819 m)). Qed.
Lemma lem221821 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term220 m n p) = (term226 m p n)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem221799 m p n h1) (@lem221820 m p n h1)). Qed.
Lemma lem221823 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem221824 (x : nat) : (x = x) = True.
Proof. exact (@lem221823 nat x). Qed.
Lemma lem221825 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem221824 (NUMERAL 0)). Qed.
Lemma lem221826 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term220 m n p) = (term226 m p n)) = True.
Proof. exact (TRANS (@lem221821 m p n h1) (@lem221825)). Qed.
Lemma lem221827 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term220 m n p) = (term226 m p n)).
Proof. exact (SYM (@lem221826 m p n h1)). Qed.
Lemma lem221828 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term220 m n p) = (term226 m p n).
Proof. exact (EQ_MP (@lem221827 m p n h1) (@lem0)). Qed.
Lemma lem221900 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem221586 m n (@lem221578 m n)). Qed.
Lemma lem221901 (m : nat) (p : nat) (n : nat) : term239 m p n.
Proof. exact (@lem221900 (term220 m n p) (term226 m p n)). Qed.
Lemma lem221903 {A : Type'} (x : A) (z : A) : term20 A x z.
Proof. exact (EQ_MP (@lem220403 A x z) (@lem220402 A x z)). Qed.
Lemma lem221904 (x : Prop) (z : Prop) : term240 x z.
Proof. exact (@lem221903 Prop x z). Qed.
Lemma lem221905 (k : nat) (m : nat) (p : nat) (n : nat) : term241 k m p n.
Proof. exact (@lem221904 (term242 k m n p) (term243 k m p n)). Qed.
Lemma lem221906 (p : nat) : term244 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem221937 (p : nat) (h1 : term212 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem221906 p (@lem221597 p h1)). Qed.
Lemma lem221938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem221939 (p : nat) (h1 : term212 p) : (term212 p) = (~ False).
Proof. exact (MK_COMB (@lem221938) (@lem221937 p h1)). Qed.
Lemma lem221941 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem221942 (p : nat) (h1 : term212 p) : (term212 p) = True.
Proof. exact (TRANS (@lem221939 p h1) (@lem221941)). Qed.
Lemma lem221943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem221944 (p : nat) (h1 : term212 p) : (term245 p) = (imp True).
Proof. exact (MK_COMB (@lem221943) (@lem221942 p h1)). Qed.
Lemma lem221949 (m : nat) (n : nat) (p : nat) : (term246 m n p) = (term246 m n p).
Proof. exact (eq_refl (term246 m n p)). Qed.
Lemma lem221950 (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term8 m n p) = (term247 m n p).
Proof. exact (MK_COMB (@lem221944 p h1) (@lem221949 m n p)). Qed.
Lemma lem221952 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem221953 (m : nat) (n : nat) (p : nat) : (term247 m n p) = (term246 m n p).
Proof. exact (@lem221952 (term246 m n p)). Qed.
Lemma lem221958 (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term8 m n p) = (term246 m n p).
Proof. exact (TRANS (@lem221950 m n p h1) (@lem221953 m n p)). Qed.
Lemma lem221959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem221960 (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term248 m n p) = (term249 m n p).
Proof. exact (MK_COMB (@lem221959) (@lem221958 m n p h1)). Qed.
Lemma lem221963 (k : nat) (p : nat) (m : nat) (n : nat) : ((term242 k m n p) = (term250 k p m n)) = ((term242 k m n p) = (term250 k p m n)).
Proof. exact (eq_refl ((term242 k m n p) = (term250 k p m n))). Qed.
Lemma lem221964 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term251 k p m n) = (term252 k p m n).
Proof. exact (MK_COMB (@lem221960 m n p h1) (@lem221963 k p m n)). Qed.
Lemma lem221967 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term252 k p m n) = (term251 k p m n).
Proof. exact (SYM (@lem221964 k m n p h1)). Qed.
Lemma lem221968 (m : nat) : term253 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem221969 (m : nat) : (term253 m) = (term254 m).
Proof. exact (eq_refl (term253 m)). Qed.
Lemma lem221970 (m : nat) : term254 m.
Proof. exact (EQ_MP (@lem221969 m) (@lem221968 m)). Qed.
Lemma lem221971 (m : nat) (n : nat) : term255 m n.
Proof. exact (@lem221970 m n). Qed.
Lemma lem221972 (n : nat) (m : nat) : (term255 m n) = (term256 n m).
Proof. exact (eq_refl (term255 m n)). Qed.
Lemma lem221973 (n : nat) (m : nat) : term256 n m.
Proof. exact (EQ_MP (@lem221972 n m) (@lem221971 m n)). Qed.
Lemma lem221974 (n : nat) (m : nat) (p : nat) : term257 n m p.
Proof. exact (@lem221973 n m p). Qed.
Lemma lem221975 (n : nat) (m : nat) (p : nat) : (term257 n m p) = ((term258 m n p) = (term259 n m p)).
Proof. exact (eq_refl (term257 n m p)). Qed.
Lemma lem221977 (m : nat) : term260 m.
Proof. exact (@lem220350 m). Qed.
Lemma lem221978 (m : nat) : (term260 m) = (term261 m).
Proof. exact (eq_refl (term260 m)). Qed.
Lemma lem221979 (m : nat) : term261 m.
Proof. exact (EQ_MP (@lem221978 m) (@lem221977 m)). Qed.
Lemma lem221980 (m : nat) (n : nat) : term262 m n.
Proof. exact (@lem221979 m n). Qed.
Lemma lem221981 (m : nat) (n : nat) : (term262 m n) = (term263 m n).
Proof. exact (eq_refl (term262 m n)). Qed.
Lemma lem221982 (m : nat) (n : nat) : term263 m n.
Proof. exact (EQ_MP (@lem221981 m n) (@lem221980 m n)). Qed.
Lemma lem221983 (m : nat) (n : nat) (p : nat) : term264 m n p.
Proof. exact (@lem221982 m n p). Qed.
Lemma lem221984 (m : nat) (n : nat) (p : nat) : (term264 m n p) = ((term265 m n p) = (term266 m n p)).
Proof. exact (eq_refl (term264 m n p)). Qed.
Lemma lem221986 (m : nat) : term267 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem221987 (m : nat) : (term267 m) = (term268 m).
Proof. exact (eq_refl (term267 m)). Qed.
Lemma lem221988 (m : nat) : term268 m.
Proof. exact (EQ_MP (@lem221987 m) (@lem221986 m)). Qed.
Lemma lem221989 (m : nat) (n : nat) : term269 m n.
Proof. exact (@lem221988 m n). Qed.
Lemma lem221990 (m : nat) (n : nat) : (term269 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term270 m n)).
Proof. exact (eq_refl (term269 m n)). Qed.
Lemma lem221992 (a : nat) : term271 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem221993 (a : nat) : (term271 a) = (term272 a).
Proof. exact (eq_refl (term271 a)). Qed.
Lemma lem221994 (a : nat) : term272 a.
Proof. exact (EQ_MP (@lem221993 a) (@lem221992 a)). Qed.
Lemma lem221995 (a : nat) (b : nat) : term273 a b.
Proof. exact (@lem221994 a b). Qed.
Lemma lem221996 (a : nat) (b : nat) : (term273 a b) = (term274 a b).
Proof. exact (eq_refl (term273 a b)). Qed.
Lemma lem221997 (a : nat) (b : nat) : term274 a b.
Proof. exact (EQ_MP (@lem221996 a b) (@lem221995 a b)). Qed.
Lemma lem221998 (a : nat) (b : nat) (n : nat) : term275 a b n.
Proof. exact (@lem221997 a b n). Qed.
Lemma lem221999 (a : nat) (n : nat) (b : nat) : (term275 a b n) = (term276 a n b).
Proof. exact (eq_refl (term275 a b n)). Qed.
Lemma lem222000 (a : nat) (n : nat) (b : nat) : term276 a n b.
Proof. exact (EQ_MP (@lem221999 a n b) (@lem221998 a b n)). Qed.
Lemma lem222001 (a : nat) (h1 : term212 a) : term212 a.
Proof. exact (h1). Qed.
Lemma lem222002 (n : nat) (b : nat) (a : nat) (h1 : term212 a) : (term277 n b a) = (term278 a n b).
Proof. exact (@lem222000 a n b (@lem222001 a h1)). Qed.
Lemma lem222008 (p : nat) : term244 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem222021 (n : nat) : term244 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem222037 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term279 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem222038 (p : Prop) (q : Prop) (p' : Prop) : term280 p q p'.
Proof. exact (fun q' : Prop => @lem222037 p q p' q'). Qed.
Lemma lem222039 (p : Prop) (q : Prop) : term281 p q.
Proof. exact (fun p' : Prop => @lem222038 p q p'). Qed.
Lemma lem222040 (k : nat) (m : nat) (p : nat) (n : nat) : term282 k m p n.
Proof. exact (@lem222039 (term4 m n p) ((term250 k p m n) = (term243 k m p n))). Qed.
Lemma lem222041 (k : nat) (m : nat) (p : nat) (n : nat) (p' : Prop) : term283 k m p n p'.
Proof. exact (@lem222040 k m p n p'). Qed.
Lemma lem222042 (k : nat) (m : nat) (p : nat) (n : nat) (p' : Prop) : (term283 k m p n p') = (term284 k m p n p').
Proof. exact (eq_refl (term283 k m p n p')). Qed.
Lemma lem222043 (k : nat) (m : nat) (p : nat) (n : nat) (p' : Prop) : term284 k m p n p'.
Proof. exact (EQ_MP (@lem222042 k m p n p') (@lem222041 k m p n p')). Qed.
Lemma lem222044 (k : nat) (m : nat) (p : nat) (n : nat) (p' : Prop) (q' : Prop) : term285 k m p n p' q'.
Proof. exact (@lem222043 k m p n p' q'). Qed.
Lemma lem222045 (k : nat) (m : nat) (p : nat) (n : nat) (p' : Prop) (q' : Prop) : (term285 k m p n p' q') = (term286 k m p n p' q').
Proof. exact (eq_refl (term285 k m p n p' q')). Qed.
Lemma lem222046 (k : nat) (m : nat) (p : nat) (n : nat) (p' : Prop) (q' : Prop) : term286 k m p n p' q'.
Proof. exact (EQ_MP (@lem222045 k m p n p' q') (@lem222044 k m p n p' q')). Qed.
Lemma lem222050 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term279 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem222051 (p : Prop) (q : Prop) (p' : Prop) : term280 p q p'.
Proof. exact (fun q' : Prop => @lem222050 p q p' q'). Qed.
Lemma lem222052 (p : Prop) (q : Prop) : term281 p q.
Proof. exact (fun p' : Prop => @lem222051 p q p'). Qed.
Lemma lem222053 (m : nat) (n : nat) (p : nat) : term287 m n p.
Proof. exact (@lem222052 (term288 n p) (term289 m n p)). Qed.
Lemma lem222054 (m : nat) (n : nat) (p : nat) (p' : Prop) : term290 m n p p'.
Proof. exact (@lem222053 m n p p'). Qed.
Lemma lem222055 (m : nat) (n : nat) (p : nat) (p' : Prop) : (term290 m n p p') = (term291 m n p p').
Proof. exact (eq_refl (term290 m n p p')). Qed.
Lemma lem222056 (m : nat) (n : nat) (p : nat) (p' : Prop) : term291 m n p p'.
Proof. exact (EQ_MP (@lem222055 m n p p') (@lem222054 m n p p')). Qed.
Lemma lem222057 (m : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : term292 m n p p' q'.
Proof. exact (@lem222056 m n p p' q'). Qed.
Lemma lem222058 (m : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : (term292 m n p p' q') = (term293 m n p p' q').
Proof. exact (eq_refl (term292 m n p p' q')). Qed.
Lemma lem222059 (m : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : term293 m n p p' q'.
Proof. exact (EQ_MP (@lem222058 m n p p' q') (@lem222057 m n p p' q')). Qed.
Lemma lem222061 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term270 m n).
Proof. exact (EQ_MP (@lem221990 m n) (@lem221989 m n)). Qed.
Lemma lem222062 (n : nat) (p : nat) : ((Nat.mul n p) = (NUMERAL 0)) = (term270 n p).
Proof. exact (@lem222061 n p). Qed.
Lemma lem222066 (n : nat) (h1 : term212 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem222021 n (@lem221592 n h1)). Qed.
Lemma lem222067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem222068 (n : nat) (h1 : term212 n) : (term294 n) = (or False).
Proof. exact (MK_COMB (@lem222067) (@lem222066 n h1)). Qed.
Lemma lem222070 (p : nat) (h1 : term212 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem222008 p (@lem221597 p h1)). Qed.
Lemma lem222071 (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term270 n p) = (False \/ False).
Proof. exact (MK_COMB (@lem222068 n h1) (@lem222070 p h2)). Qed.
Lemma lem222073 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem222074 : (False \/ False) = False.
Proof. exact (@lem222073 False). Qed.
Lemma lem222075 (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term270 n p) = False.
Proof. exact (TRANS (@lem222071 n p h1 h2) (@lem222074)). Qed.
Lemma lem222076 (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : ((Nat.mul n p) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem222062 n p) (@lem222075 n p h1 h2)). Qed.
Lemma lem222077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem222078 (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term288 n p) = (~ False).
Proof. exact (MK_COMB (@lem222077) (@lem222076 n p h1 h2)). Qed.
Lemma lem222080 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem222081 (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term288 n p) = True.
Proof. exact (TRANS (@lem222078 n p h1 h2) (@lem222080)). Qed.
Lemma lem222082 (m : nat) (n : nat) (p : nat) (q' : Prop) : term295 m n p q'.
Proof. exact (@lem222059 m n p True q'). Qed.
Lemma lem222083 (m : nat) (q' : Prop) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term296 m n p q'.
Proof. exact (@lem222082 m n p q' (@lem222081 n p h1 h2)). Qed.
Lemma lem222093 (m : nat) (n : nat) (p : nat) : (term289 m n p) = (term289 m n p).
Proof. exact (eq_refl (term289 m n p)). Qed.
Lemma lem222094 (m : nat) (n : nat) (p : nat) : term297 m n p.
Proof. exact (fun h0 : True => @lem222093 m n p). Qed.
Lemma lem222095 (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term298 m n p.
Proof. exact (@lem222083 m (term289 m n p) n p h1 h2). Qed.
Lemma lem222096 (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term4 m n p) = (term299 m n p).
Proof. exact (@lem222095 m n p h1 h2 (@lem222094 m n p)). Qed.
Lemma lem222098 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem222099 (m : nat) (n : nat) (p : nat) : (term299 m n p) = (term289 m n p).
Proof. exact (@lem222098 (term289 m n p)). Qed.
Lemma lem222104 (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term4 m n p) = (term289 m n p).
Proof. exact (TRANS (@lem222096 m n p h1 h2) (@lem222099 m n p)). Qed.
Lemma lem222105 (k : nat) (m : nat) (n : nat) (p : nat) (q' : Prop) : term300 k m n p q'.
Proof. exact (@lem222046 k m p n (term289 m n p) q'). Qed.
Lemma lem222106 (k : nat) (m : nat) (q' : Prop) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term301 k m n p q'.
Proof. exact (@lem222105 k m n p q' (@lem222104 m n p h1 h2)). Qed.
Lemma lem222117 (a : nat) (n : nat) (b : nat) : term276 a n b.
Proof. exact (fun h0 : term212 a => @lem222002 n b a h0). Qed.
Lemma lem222118 (k : nat) (n : nat) (p : nat) (m : nat) : term302 k n p m.
Proof. exact (@lem222117 n (term303 k m n p) m). Qed.
Lemma lem222120 (n : nat) (h1 : term212 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem222021 n (@lem221592 n h1)). Qed.
Lemma lem222121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem222122 (n : nat) (h1 : term212 n) : (term212 n) = (~ False).
Proof. exact (MK_COMB (@lem222121) (@lem222120 n h1)). Qed.
Lemma lem222124 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem222125 (n : nat) (h1 : term212 n) : (term212 n) = True.
Proof. exact (TRANS (@lem222122 n h1) (@lem222124)). Qed.
Lemma lem222126 (n : nat) (h1 : term212 n) : True = (term212 n).
Proof. exact (SYM (@lem222125 n h1)). Qed.
Lemma lem222127 (n : nat) (h1 : term212 n) : term212 n.
Proof. exact (EQ_MP (@lem222126 n h1) (@lem0)). Qed.
Lemma lem222128 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term212 n) : (term250 k p m n) = (term304 k n p m).
Proof. exact (@lem222118 k n p m (@lem222127 n h1)). Qed.
Lemma lem222130 (n : nat) (m : nat) (p : nat) : (term258 m n p) = (term259 n m p).
Proof. exact (EQ_MP (@lem221975 n m p) (@lem221974 n m p)). Qed.
Lemma lem222131 (k : nat) (m : nat) (n : nat) (p : nat) : (term305 k m n p) = (term306 k m n p).
Proof. exact (@lem222130 k n (term307 m n p)). Qed.
Lemma lem222133 (m : nat) (n : nat) (p : nat) : (term265 m n p) = (term266 m n p).
Proof. exact (EQ_MP (@lem221984 m n p) (@lem221983 m n p)). Qed.
Lemma lem222136 (p : nat) : (Nat.mul p) = (Nat.mul p).
Proof. exact (eq_refl (Nat.mul p)). Qed.
Lemma lem222137 (m : nat) (n : nat) (p : nat) : (term307 m n p) = (term308 m n p).
Proof. exact (MK_COMB (@lem222136 p) (@lem222133 m n p)). Qed.
Lemma lem222140 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem222141 (m : nat) (n : nat) (p : nat) : (term309 m n p) = (term310 m n p).
Proof. exact (MK_COMB (@lem222140 n) (@lem222137 m n p)). Qed.
Lemma lem222144 (n : nat) (k : nat) : (term311 n k) = (term311 n k).
Proof. exact (eq_refl (term311 n k)). Qed.
Lemma lem222145 (k : nat) (m : nat) (n : nat) (p : nat) : (term306 k m n p) = (term312 k m n p).
Proof. exact (MK_COMB (@lem222144 n k) (@lem222141 m n p)). Qed.
Lemma lem222148 (k : nat) (m : nat) (n : nat) (p : nat) : (term305 k m n p) = (term312 k m n p).
Proof. exact (TRANS (@lem222131 k m n p) (@lem222145 k m n p)). Qed.
Lemma lem222149 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem222150 (k : nat) (m : nat) (n : nat) (p : nat) : (term313 k m n p) = (term314 k m n p).
Proof. exact (MK_COMB (@lem222149) (@lem222148 k m n p)). Qed.
Lemma lem222155 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem222156 (k : nat) (n : nat) (p : nat) (m : nat) : (term304 k n p m) = (term315 k n p m).
Proof. exact (MK_COMB (@lem222150 k m n p) (@lem222155 m)). Qed.
Lemma lem222161 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term212 n) : (term250 k p m n) = (term315 k n p m).
Proof. exact (TRANS (@lem222128 k p m n h1) (@lem222156 k n p m)). Qed.
Lemma lem222162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222163 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term212 n) : (term316 k p m n) = (term317 k n p m).
Proof. exact (MK_COMB (@lem222162) (@lem222161 k p m n h1)). Qed.
Lemma lem222169 (a : nat) (n : nat) (b : nat) : term276 a n b.
Proof. exact (fun h0 : term212 a => @lem222002 n b a h0). Qed.
Lemma lem222170 (k : nat) (m : nat) (n : nat) (p : nat) : term318 k m n p.
Proof. exact (@lem222169 n k (term224 m n p)). Qed.
Lemma lem222172 (n : nat) (h1 : term212 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem222021 n (@lem221592 n h1)). Qed.
Lemma lem222173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem222174 (n : nat) (h1 : term212 n) : (term212 n) = (~ False).
Proof. exact (MK_COMB (@lem222173) (@lem222172 n h1)). Qed.
Lemma lem222176 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem222177 (n : nat) (h1 : term212 n) : (term212 n) = True.
Proof. exact (TRANS (@lem222174 n h1) (@lem222176)). Qed.
Lemma lem222178 (n : nat) (h1 : term212 n) : True = (term212 n).
Proof. exact (SYM (@lem222177 n h1)). Qed.
Lemma lem222179 (n : nat) (h1 : term212 n) : term212 n.
Proof. exact (EQ_MP (@lem222178 n h1) (@lem0)). Qed.
Lemma lem222180 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term212 n) : (term243 k m p n) = (term319 k m n p).
Proof. exact (@lem222170 k m n p (@lem222179 n h1)). Qed.
Lemma lem222183 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term212 n) : ((term250 k p m n) = (term243 k m p n)) = ((term315 k n p m) = (term319 k m n p)).
Proof. exact (MK_COMB (@lem222163 k p m n h1) (@lem222180 k m p n h1)). Qed.
Lemma lem222192 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term212 n) : term320 k m n p.
Proof. exact (fun h0 : term289 m n p => @lem222183 k m p n h1). Qed.
Lemma lem222193 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term321 k m n p.
Proof. exact (@lem222106 k m ((term315 k n p m) = (term319 k m n p)) n p h1 h2). Qed.
Lemma lem222194 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term322 k m p n) = (term323 k m n p).
Proof. exact (@lem222193 k m n p h1 h2 (@lem222192 k m p n h1)). Qed.
Lemma lem222240 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term323 k m n p) = (term322 k m p n).
Proof. exact (SYM (@lem222194 k m n p h1 h2)). Qed.
Lemma lem222248 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem222249 (m : nat) (n : nat) (p : nat) : (term324 m n p) = (term307 m n p).
Proof. exact (@lem222248 p (term265 m n p)). Qed.
Lemma lem222253 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem222254 (m : nat) (n : nat) (p : nat) : (term325 m n p) = (term326 m n p).
Proof. exact (MK_COMB (@lem222253) (@lem222249 m n p)). Qed.
Lemma lem222255 (m : nat) (n : nat) (p : nat) : (term220 m n p) = (term220 m n p).
Proof. exact (eq_refl (term220 m n p)). Qed.
Lemma lem222256 (m : nat) (n : nat) (p : nat) : (term327 m n p) = (term328 m n p).
Proof. exact (MK_COMB (@lem222254 m n p) (@lem222255 m n p)). Qed.
Lemma lem222257 (m : nat) (n : nat) : (term223 m n) = (term223 m n).
Proof. exact (eq_refl (term223 m n)). Qed.
Lemma lem222258 (m : nat) (n : nat) (p : nat) : ((Nat.div m n) = (term327 m n p)) = ((Nat.div m n) = (term328 m n p)).
Proof. exact (MK_COMB (@lem222257 m n) (@lem222256 m n p)). Qed.
Lemma lem222261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222262 (m : nat) (n : nat) (p : nat) : (term329 m n p) = (term330 m n p).
Proof. exact (MK_COMB (@lem222261) (@lem222258 m n p)). Qed.
Lemma lem222263 (m : nat) (n : nat) (p : nat) : (term331 m n p) = (term331 m n p).
Proof. exact (eq_refl (term331 m n p)). Qed.
Lemma lem222264 (m : nat) (n : nat) (p : nat) : (term246 m n p) = (term332 m n p).
Proof. exact (MK_COMB (@lem222262 m n p) (@lem222263 m n p)). Qed.
Lemma lem222267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem222268 (m : nat) (n : nat) (p : nat) : (term249 m n p) = (term333 m n p).
Proof. exact (MK_COMB (@lem222267) (@lem222264 m n p)). Qed.
Lemma lem222274 (k : nat) (p : nat) (m : nat) (n : nat) : ((term242 k m n p) = (term250 k p m n)) = ((term242 k m n p) = (term250 k p m n)).
Proof. exact (eq_refl ((term242 k m n p) = (term250 k p m n))). Qed.
Lemma lem222275 (k : nat) (p : nat) (m : nat) (n : nat) : (term252 k p m n) = (term334 k p m n).
Proof. exact (MK_COMB (@lem222268 m n p) (@lem222274 k p m n)). Qed.
Lemma lem222278 (k : nat) (p : nat) (m : nat) (n : nat) : (term334 k p m n) = (term252 k p m n).
Proof. exact (SYM (@lem222275 k p m n)). Qed.
Lemma lem222286 (n : nat) (m : nat) (p : nat) : (term335 m n p) = (term335 n m p).
Proof. exact (proj2 (@lem220361 n m p)). Qed.
Lemma lem222287 (m : nat) (n : nat) (p : nat) : (term336 m n p) = (term337 m n p).
Proof. exact (@lem222286 n (term266 m n p) p). Qed.
Lemma lem222295 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem222296 (m : nat) (n : nat) (p : nat) : (term338 m n p) = (term308 m n p).
Proof. exact (@lem222295 p (term266 m n p)). Qed.
Lemma lem222303 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem222304 (m : nat) (n : nat) (p : nat) : (term337 m n p) = (term310 m n p).
Proof. exact (MK_COMB (@lem222303 n) (@lem222296 m n p)). Qed.
Lemma lem222311 (m : nat) (n : nat) (p : nat) : (term336 m n p) = (term310 m n p).
Proof. exact (TRANS (@lem222287 m n p) (@lem222304 m n p)). Qed.
Lemma lem222312 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem222313 (m : nat) (n : nat) (p : nat) : (term339 m n p) = (term340 m n p).
Proof. exact (MK_COMB (@lem222312) (@lem222311 m n p)). Qed.
Lemma lem222317 (m : nat) (n : nat) (p : nat) : (term224 m n p) = (term224 m n p).
Proof. exact (eq_refl (term224 m n p)). Qed.
Lemma lem222318 (m : nat) (n : nat) (p : nat) : (term341 m n p) = (term342 m n p).
Proof. exact (MK_COMB (@lem222313 m n p) (@lem222317 m n p)). Qed.
Lemma lem222319 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem222320 (m : nat) (n : nat) (p : nat) : (m = (term341 m n p)) = (m = (term342 m n p)).
Proof. exact (MK_COMB (@lem222319 m) (@lem222318 m n p)). Qed.
Lemma lem222323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222324 (m : nat) (n : nat) (p : nat) : (term343 m n p) = (term344 m n p).
Proof. exact (MK_COMB (@lem222323) (@lem222320 m n p)). Qed.
Lemma lem222331 (m : nat) (n : nat) (p : nat) : (term345 m n p) = (term345 m n p).
Proof. exact (eq_refl (term345 m n p)). Qed.
Lemma lem222332 (m : nat) (n : nat) (p : nat) : (term289 m n p) = (term346 m n p).
Proof. exact (MK_COMB (@lem222324 m n p) (@lem222331 m n p)). Qed.
Lemma lem222335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem222336 (m : nat) (n : nat) (p : nat) : (term347 m n p) = (term348 m n p).
Proof. exact (MK_COMB (@lem222335) (@lem222332 m n p)). Qed.
Lemma lem222340 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem222341 (k : nat) (n : nat) : (Nat.mul n k) = (Nat.mul k n).
Proof. exact (@lem222340 k n). Qed.
Lemma lem222345 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem222346 (k : nat) (n : nat) : (term311 n k) = (term311 k n).
Proof. exact (MK_COMB (@lem222345) (@lem222341 k n)). Qed.
Lemma lem222359 (m : nat) (n : nat) (p : nat) : (term310 m n p) = (term310 m n p).
Proof. exact (eq_refl (term310 m n p)). Qed.
Lemma lem222360 (k : nat) (m : nat) (n : nat) (p : nat) : (term312 k m n p) = (term349 k m n p).
Proof. exact (MK_COMB (@lem222346 k n) (@lem222359 m n p)). Qed.
Lemma lem222361 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem222362 (k : nat) (m : nat) (n : nat) (p : nat) : (term314 k m n p) = (term350 k m n p).
Proof. exact (MK_COMB (@lem222361) (@lem222360 k m n p)). Qed.
Lemma lem222363 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem222364 (k : nat) (n : nat) (p : nat) (m : nat) : (term315 k n p m) = (term351 k n p m).
Proof. exact (MK_COMB (@lem222362 k m n p) (@lem222363 m)). Qed.
Lemma lem222365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222366 (k : nat) (n : nat) (p : nat) (m : nat) : (term317 k n p m) = (term352 k n p m).
Proof. exact (MK_COMB (@lem222365) (@lem222364 k n p m)). Qed.
Lemma lem222368 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem222369 (k : nat) (n : nat) : (Nat.mul n k) = (Nat.mul k n).
Proof. exact (@lem222368 k n). Qed.
Lemma lem222373 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem222374 (k : nat) (n : nat) : (term353 n k) = (term353 k n).
Proof. exact (MK_COMB (@lem222373) (@lem222369 k n)). Qed.
Lemma lem222378 (m : nat) (n : nat) (p : nat) : (term224 m n p) = (term224 m n p).
Proof. exact (eq_refl (term224 m n p)). Qed.
Lemma lem222379 (k : nat) (m : nat) (n : nat) (p : nat) : (term319 k m n p) = (term354 k m n p).
Proof. exact (MK_COMB (@lem222374 k n) (@lem222378 m n p)). Qed.
Lemma lem222380 (k : nat) (m : nat) (n : nat) (p : nat) : ((term315 k n p m) = (term319 k m n p)) = ((term351 k n p m) = (term354 k m n p)).
Proof. exact (MK_COMB (@lem222366 k n p m) (@lem222379 k m n p)). Qed.
Lemma lem222383 (k : nat) (m : nat) (n : nat) (p : nat) : (term323 k m n p) = (term355 k m n p).
Proof. exact (MK_COMB (@lem222336 m n p) (@lem222380 k m n p)). Qed.
Lemma lem222386 (k : nat) (m : nat) (n : nat) (p : nat) : (term355 k m n p) = (term323 k m n p).
Proof. exact (SYM (@lem222383 k m n p)). Qed.
Lemma lem222388 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem222389 (k : nat) (p : nat) (m : nat) (n : nat) : (term334 k p m n) = (term356 k p m n).
Proof. exact (@lem222388 (term334 k p m n)). Qed.
Lemma lem222390 (k : nat) (p : nat) (m : nat) (n : nat) : (term356 k p m n) = (term334 k p m n).
Proof. exact (SYM (@lem222389 k p m n)). Qed.
Lemma lem222391 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term357 k p m n.
Proof. exact (h1). Qed.
Lemma lem222394 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term358 k p m n) : term358 k p m n.
Proof. exact (h1). Qed.
Lemma lem222395 (k : nat) (p : nat) (m : nat) (n : nat) : term359 k p m n.
Proof. exact (fun h0 : term358 k p m n => @lem222394 k p m n h0). Qed.
Lemma lem222396 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term359 k p m n) : term359 k p m n.
Proof. exact (h1). Qed.
Lemma lem222397 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term358 k p m n) : term358 k p m n.
Proof. exact (h1). Qed.
Lemma lem222398 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term358 k p m n) (h2 : term359 k p m n) : term358 k p m n.
Proof. exact (@lem222396 k p m n h2 (@lem222397 k p m n h1)). Qed.
Lemma lem222399 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term358 k p m n) : term360 k p m n.
Proof. exact (fun h0 : term359 k p m n => @lem222398 k p m n h1 h0). Qed.
Lemma lem222400 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term359 k p m n) : term359 k p m n.
Proof. exact (h1). Qed.
Lemma lem222401 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term358 k p m n) (h2 : term359 k p m n) : term358 k p m n.
Proof. exact (@lem222399 k p m n h1 (@lem222400 k p m n h2)). Qed.
Lemma lem222402 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term359 k p m n) : term359 k p m n.
Proof. exact (fun h0 : term358 k p m n => @lem222401 k p m n h0 h1). Qed.
Lemma lem222403 (k : nat) (p : nat) (m : nat) (n : nat) : term361 k p m n.
Proof. exact (fun h0 : term359 k p m n => @lem222402 k p m n h0). Qed.
Lemma lem222406 (k : nat) (p : nat) (m : nat) (n : nat) : term359 k p m n.
Proof. exact (@lem222403 k p m n (@lem222395 k p m n)). Qed.
Lemma lem222454 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem222455 : term362 = term363.
Proof. exact (@lem222454 term364). Qed.
Lemma lem222464 : term365 = term365.
Proof. exact (eq_refl term365). Qed.
Lemma lem222465 : term366 = term367.
Proof. exact (MK_COMB (@lem222464) (@lem222455)). Qed.
Lemma lem222468 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem222469 : term369 = term370.
Proof. exact (MK_COMB (@lem222468) (@lem222465)). Qed.
Lemma lem222472 (k : nat) (p : nat) (m : nat) (n : nat) : (term371 k p m n) = (term371 k p m n).
Proof. exact (eq_refl (term371 k p m n)). Qed.
Lemma lem222473 (k : nat) (p : nat) (m : nat) (n : nat) : (term358 k p m n) = (term372 k p m n).
Proof. exact (MK_COMB (@lem222472 k p m n) (@lem222469)). Qed.
Lemma lem222476 (p : nat) (m : nat) (n : nat) : (term373 p m n) = (term374 p m n).
Proof. exact (fun_ext (fun k : nat => @lem222473 k p m n)). Qed.
Lemma lem222477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222478 (p : nat) (m : nat) (n : nat) : (term375 p m n) = (term376 p m n).
Proof. exact (MK_COMB (@lem222477) (@lem222476 p m n)). Qed.
Lemma lem222483 (m : nat) (n : nat) : (term377 m n) = (term378 m n).
Proof. exact (fun_ext (fun p : nat => @lem222478 p m n)). Qed.
Lemma lem222484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222485 (m : nat) (n : nat) : (term379 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem222484) (@lem222483 m n)). Qed.
Lemma lem222490 (n : nat) : (term381 n) = (term382 n).
Proof. exact (fun_ext (fun m : nat => @lem222485 m n)). Qed.
Lemma lem222491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222492 (n : nat) : (term383 n) = (term384 n).
Proof. exact (MK_COMB (@lem222491) (@lem222490 n)). Qed.
Lemma lem222497 : term385 = term386.
Proof. exact (fun_ext (fun n : nat => @lem222492 n)). Qed.
Lemma lem222498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222507 : term387 = term388.
Proof. exact (MK_COMB (@lem222498) (@lem222497)). Qed.
Lemma lem222508 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem222509 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem222508 n m)). Qed.
Lemma lem222510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222511 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem222510) (@lem222509 m)). Qed.
Lemma lem222512 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem222511 m)). Qed.
Lemma lem222513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222514 : term364 = term364.
Proof. exact (MK_COMB (@lem222513) (@lem222512)). Qed.
Lemma lem222515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem222516 : term363 = term363.
Proof. exact (MK_COMB (@lem222515) (@lem222514)). Qed.
Lemma lem222517 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem222518 (m : nat) : (term392 m) = (term392 m).
Proof. exact (fun_ext (fun n : nat => @lem222517 n m)). Qed.
Lemma lem222519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222520 (m : nat) : (term393 m) = (term393 m).
Proof. exact (MK_COMB (@lem222519) (@lem222518 m)). Qed.
Lemma lem222521 : term394 = term394.
Proof. exact (fun_ext (fun m : nat => @lem222520 m)). Qed.
Lemma lem222522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222523 : term395 = term395.
Proof. exact (MK_COMB (@lem222522) (@lem222521)). Qed.
Lemma lem222524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem222525 : term365 = term365.
Proof. exact (MK_COMB (@lem222524) (@lem222523)). Qed.
Lemma lem222526 : term367 = term367.
Proof. exact (MK_COMB (@lem222525) (@lem222516)). Qed.
Lemma lem222531 (p : nat) (m : nat) (n : nat) : ((term396 m n p) = (Peano.le m n)) = ((term396 m n p) = (Peano.le m n)).
Proof. exact (eq_refl ((term396 m n p) = (Peano.le m n))). Qed.
Lemma lem222532 (m : nat) (n : nat) : (term397 m n) = (term397 m n).
Proof. exact (fun_ext (fun p : nat => @lem222531 p m n)). Qed.
Lemma lem222533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222534 (m : nat) (n : nat) : (term398 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem222533) (@lem222532 m n)). Qed.
Lemma lem222535 (m : nat) : (term399 m) = (term399 m).
Proof. exact (fun_ext (fun n : nat => @lem222534 m n)). Qed.
Lemma lem222536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222537 (m : nat) : (term400 m) = (term400 m).
Proof. exact (MK_COMB (@lem222536) (@lem222535 m)). Qed.
Lemma lem222538 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem222537 m)). Qed.
Lemma lem222539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222540 : term402 = term402.
Proof. exact (MK_COMB (@lem222539) (@lem222538)). Qed.
Lemma lem222541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem222542 : term368 = term368.
Proof. exact (MK_COMB (@lem222541) (@lem222540)). Qed.
Lemma lem222543 : term370 = term370.
Proof. exact (MK_COMB (@lem222542) (@lem222526)). Qed.
Lemma lem222560 (k : nat) (p : nat) (m : nat) (n : nat) : (term371 k p m n) = (term371 k p m n).
Proof. exact (eq_refl (term371 k p m n)). Qed.
Lemma lem222561 (k : nat) (p : nat) (m : nat) (n : nat) : (term372 k p m n) = (term372 k p m n).
Proof. exact (MK_COMB (@lem222560 k p m n) (@lem222543)). Qed.
Lemma lem222562 (p : nat) (m : nat) (n : nat) : (term374 p m n) = (term374 p m n).
Proof. exact (fun_ext (fun k : nat => @lem222561 k p m n)). Qed.
Lemma lem222563 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222564 (p : nat) (m : nat) (n : nat) : (term376 p m n) = (term376 p m n).
Proof. exact (MK_COMB (@lem222563) (@lem222562 p m n)). Qed.
Lemma lem222565 (m : nat) (n : nat) : (term378 m n) = (term378 m n).
Proof. exact (fun_ext (fun p : nat => @lem222564 p m n)). Qed.
Lemma lem222566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222567 (m : nat) (n : nat) : (term380 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem222566) (@lem222565 m n)). Qed.
Lemma lem222568 (n : nat) : (term382 n) = (term382 n).
Proof. exact (fun_ext (fun m : nat => @lem222567 m n)). Qed.
Lemma lem222569 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222570 (n : nat) : (term384 n) = (term384 n).
Proof. exact (MK_COMB (@lem222569) (@lem222568 n)). Qed.
Lemma lem222571 : term386 = term386.
Proof. exact (fun_ext (fun n : nat => @lem222570 n)). Qed.
Lemma lem222572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222573 : term388 = term388.
Proof. exact (MK_COMB (@lem222572) (@lem222571)). Qed.
Lemma lem222652 : term387 = term388.
Proof. exact (TRANS (@lem222507) (@lem222573)). Qed.
Lemma lem222653 : term388 = term387.
Proof. exact (SYM (@lem222652)). Qed.
Lemma lem222654 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term357 k p m n.
Proof. exact (h1). Qed.
Lemma lem222655 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem222657 (h1 : term364) : term364.
Proof. exact (h1). Qed.
Lemma lem222677 (k : nat) (p : nat) (m : nat) (n : nat) : (term403 k p m n) = (term404 k p m n).
Proof. exact (@lem17646 (term242 k m n p) (term250 k p m n)). Qed.
Lemma lem222679 (m : nat) (n : nat) (p : nat) : (term405 m n p) = (term405 m n p).
Proof. exact (eq_refl (term405 m n p)). Qed.
Lemma lem222680 (k : nat) (p : nat) (m : nat) (n : nat) : (term406 k p m n) = (term407 k p m n).
Proof. exact (MK_COMB (@lem222679 m n p) (@lem222677 k p m n)). Qed.
Lemma lem222681 (k : nat) (p : nat) (m : nat) (n : nat) : (term357 k p m n) = (term406 k p m n).
Proof. exact (@lem17362 (term332 m n p) ((term242 k m n p) = (term250 k p m n))). Qed.
Lemma lem222686 (k : nat) (p : nat) (m : nat) (n : nat) : (term357 k p m n) = (term407 k p m n).
Proof. exact (TRANS (@lem222681 k p m n) (@lem222680 k p m n)). Qed.
Lemma lem222702 (p : nat) (m : nat) (n : nat) : ((term396 m n p) = (Peano.le m n)) = (term408 p m n).
Proof. exact (@lem17784 (term396 m n p) (Peano.le m n)). Qed.
Lemma lem222703 (m : nat) (n : nat) : (term397 m n) = (term409 m n).
Proof. exact (fun_ext (fun p : nat => @lem222702 p m n)). Qed.
Lemma lem222704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222705 (m : nat) (n : nat) : (term398 m n) = (term410 m n).
Proof. exact (MK_COMB (@lem222704) (@lem222703 m n)). Qed.
Lemma lem222706 (m : nat) : (term399 m) = (term411 m).
Proof. exact (fun_ext (fun n : nat => @lem222705 m n)). Qed.
Lemma lem222707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222708 (m : nat) : (term400 m) = (term412 m).
Proof. exact (MK_COMB (@lem222707) (@lem222706 m)). Qed.
Lemma lem222709 : term401 = term413.
Proof. exact (fun_ext (fun m : nat => @lem222708 m)). Qed.
Lemma lem222710 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222711 : term402 = term414.
Proof. exact (MK_COMB (@lem222710) (@lem222709)). Qed.
Lemma lem222721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem222722 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem222721 nat P Q). Qed.
Lemma lem222723 (m : nat) (n : nat) : (term415 m n) = (term416 m n).
Proof. exact (@lem222722 (term417 m n) (term418 m n)). Qed.
Lemma lem222724 (p : nat) (m : nat) (n : nat) : (term419 m n p) = (term420 p m n).
Proof. exact (eq_refl (term419 m n p)). Qed.
Lemma lem222725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222726 (p : nat) (m : nat) (n : nat) : (term421 m n p) = (term422 p m n).
Proof. exact (MK_COMB (@lem222725) (@lem222724 p m n)). Qed.
Lemma lem222727 (p : nat) (m : nat) (n : nat) : (term423 m n p) = (term424 p m n).
Proof. exact (eq_refl (term423 m n p)). Qed.
Lemma lem222728 (p : nat) (m : nat) (n : nat) : (term425 m n p) = (term408 p m n).
Proof. exact (MK_COMB (@lem222726 p m n) (@lem222727 p m n)). Qed.
Lemma lem222729 (m : nat) (n : nat) : (term426 m n) = (term409 m n).
Proof. exact (fun_ext (fun p : nat => @lem222728 p m n)). Qed.
Lemma lem222730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222731 (m : nat) (n : nat) : (term415 m n) = (term410 m n).
Proof. exact (MK_COMB (@lem222730) (@lem222729 m n)). Qed.
Lemma lem222732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222733 (m : nat) (n : nat) : (term427 m n) = (term428 m n).
Proof. exact (MK_COMB (@lem222732) (@lem222731 m n)). Qed.
Lemma lem222734 (p : nat) (m : nat) (n : nat) : (term419 m n p) = (term420 p m n).
Proof. exact (eq_refl (term419 m n p)). Qed.
Lemma lem222735 (m : nat) (n : nat) : (term429 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem222734 p m n)). Qed.
Lemma lem222736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222737 (m : nat) (n : nat) : (term430 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem222736) (@lem222735 m n)). Qed.
Lemma lem222738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222739 (m : nat) (n : nat) : (term432 m n) = (term433 m n).
Proof. exact (MK_COMB (@lem222738) (@lem222737 m n)). Qed.
Lemma lem222740 (p : nat) (m : nat) (n : nat) : (term423 m n p) = (term424 p m n).
Proof. exact (eq_refl (term423 m n p)). Qed.
Lemma lem222741 (m : nat) (n : nat) : (term434 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem222740 p m n)). Qed.
Lemma lem222742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222743 (m : nat) (n : nat) : (term435 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem222742) (@lem222741 m n)). Qed.
Lemma lem222744 (m : nat) (n : nat) : (term416 m n) = (term437 m n).
Proof. exact (MK_COMB (@lem222739 m n) (@lem222743 m n)). Qed.
Lemma lem222745 (m : nat) (n : nat) : ((term415 m n) = (term416 m n)) = ((term410 m n) = (term437 m n)).
Proof. exact (MK_COMB (@lem222733 m n) (@lem222744 m n)). Qed.
Lemma lem222746 (m : nat) (n : nat) : (term410 m n) = (term437 m n).
Proof. exact (EQ_MP (@lem222745 m n) (@lem222723 m n)). Qed.
Lemma lem222768 {A : Type'} (P : A -> Prop) (Q : Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem222769 (P : nat -> Prop) (Q : Prop) : (term440 P Q) = (term441 P Q).
Proof. exact (@lem222768 nat P Q). Qed.
Lemma lem222770 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (@lem222769 (term444 m n) (term162 m n)). Qed.
Lemma lem222771 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem222772 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem222773 (m : nat) (n : nat) (p : nat) : (term446 m n p) = (term447 m n p).
Proof. exact (MK_COMB (@lem222772) (@lem222771 m n p)). Qed.
Lemma lem222774 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem222775 (p : nat) (m : nat) (n : nat) : (term448 p m n) = (term420 p m n).
Proof. exact (MK_COMB (@lem222773 m n p) (@lem222774 m n)). Qed.
Lemma lem222776 (m : nat) (n : nat) : (term449 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem222775 p m n)). Qed.
Lemma lem222777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222778 (m : nat) (n : nat) : (term442 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem222777) (@lem222776 m n)). Qed.
Lemma lem222779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222780 (m : nat) (n : nat) : (term450 m n) = (term451 m n).
Proof. exact (MK_COMB (@lem222779) (@lem222778 m n)). Qed.
Lemma lem222781 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem222782 (m : nat) (n : nat) : (term452 m n) = (term444 m n).
Proof. exact (fun_ext (fun p : nat => @lem222781 m n p)). Qed.
Lemma lem222783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222784 (m : nat) (n : nat) : (term453 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem222783) (@lem222782 m n)). Qed.
Lemma lem222785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem222786 (m : nat) (n : nat) : (term455 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem222785) (@lem222784 m n)). Qed.
Lemma lem222787 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem222788 (m : nat) (n : nat) : (term443 m n) = (term457 m n).
Proof. exact (MK_COMB (@lem222786 m n) (@lem222787 m n)). Qed.
Lemma lem222789 (m : nat) (n : nat) : ((term442 m n) = (term443 m n)) = ((term431 m n) = (term457 m n)).
Proof. exact (MK_COMB (@lem222780 m n) (@lem222788 m n)). Qed.
Lemma lem222790 (m : nat) (n : nat) : (term431 m n) = (term457 m n).
Proof. exact (EQ_MP (@lem222789 m n) (@lem222770 m n)). Qed.
Lemma lem222795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222796 (m : nat) (n : nat) : (term433 m n) = (term458 m n).
Proof. exact (MK_COMB (@lem222795) (@lem222790 m n)). Qed.
Lemma lem222818 {A : Type'} (P : A -> Prop) (Q : Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem222819 (P : nat -> Prop) (Q : Prop) : (term440 P Q) = (term441 P Q).
Proof. exact (@lem222818 nat P Q). Qed.
Lemma lem222820 (m : nat) (n : nat) : (term459 m n) = (term460 m n).
Proof. exact (@lem222819 (term461 m n) (Peano.le m n)). Qed.
Lemma lem222821 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem222822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem222823 (m : nat) (n : nat) (p : nat) : (term464 m n p) = (term465 m n p).
Proof. exact (MK_COMB (@lem222822) (@lem222821 m n p)). Qed.
Lemma lem222824 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem222825 (p : nat) (m : nat) (n : nat) : (term466 p m n) = (term424 p m n).
Proof. exact (MK_COMB (@lem222823 m n p) (@lem222824 m n)). Qed.
Lemma lem222826 (m : nat) (n : nat) : (term467 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem222825 p m n)). Qed.
Lemma lem222827 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222828 (m : nat) (n : nat) : (term459 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem222827) (@lem222826 m n)). Qed.
Lemma lem222829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222830 (m : nat) (n : nat) : (term468 m n) = (term469 m n).
Proof. exact (MK_COMB (@lem222829) (@lem222828 m n)). Qed.
Lemma lem222831 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem222832 (m : nat) (n : nat) : (term470 m n) = (term461 m n).
Proof. exact (fun_ext (fun p : nat => @lem222831 m n p)). Qed.
Lemma lem222833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222834 (m : nat) (n : nat) : (term471 m n) = (term472 m n).
Proof. exact (MK_COMB (@lem222833) (@lem222832 m n)). Qed.
Lemma lem222835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem222836 (m : nat) (n : nat) : (term473 m n) = (term474 m n).
Proof. exact (MK_COMB (@lem222835) (@lem222834 m n)). Qed.
Lemma lem222837 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem222838 (m : nat) (n : nat) : (term460 m n) = (term475 m n).
Proof. exact (MK_COMB (@lem222836 m n) (@lem222837 m n)). Qed.
Lemma lem222839 (m : nat) (n : nat) : ((term459 m n) = (term460 m n)) = ((term436 m n) = (term475 m n)).
Proof. exact (MK_COMB (@lem222830 m n) (@lem222838 m n)). Qed.
Lemma lem222840 (m : nat) (n : nat) : (term436 m n) = (term475 m n).
Proof. exact (EQ_MP (@lem222839 m n) (@lem222820 m n)). Qed.
Lemma lem222845 (m : nat) (n : nat) : (term437 m n) = (term476 m n).
Proof. exact (MK_COMB (@lem222796 m n) (@lem222840 m n)). Qed.
Lemma lem222846 (m : nat) (n : nat) : (term410 m n) = (term476 m n).
Proof. exact (TRANS (@lem222746 m n) (@lem222845 m n)). Qed.
Lemma lem222847 (m : nat) : (term411 m) = (term477 m).
Proof. exact (fun_ext (fun n : nat => @lem222846 m n)). Qed.
Lemma lem222848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222849 (m : nat) : (term412 m) = (term478 m).
Proof. exact (MK_COMB (@lem222848) (@lem222847 m)). Qed.
Lemma lem222851 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem222852 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem222851 nat P Q). Qed.
Lemma lem222853 (m : nat) : (term479 m) = (term480 m).
Proof. exact (@lem222852 (term481 m) (term482 m)). Qed.
Lemma lem222854 (m : nat) (n : nat) : (term483 m n) = (term457 m n).
Proof. exact (eq_refl (term483 m n)). Qed.
Lemma lem222855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222856 (m : nat) (n : nat) : (term484 m n) = (term458 m n).
Proof. exact (MK_COMB (@lem222855) (@lem222854 m n)). Qed.
Lemma lem222857 (m : nat) (n : nat) : (term485 m n) = (term475 m n).
Proof. exact (eq_refl (term485 m n)). Qed.
Lemma lem222858 (m : nat) (n : nat) : (term486 m n) = (term476 m n).
Proof. exact (MK_COMB (@lem222856 m n) (@lem222857 m n)). Qed.
Lemma lem222859 (m : nat) : (term487 m) = (term477 m).
Proof. exact (fun_ext (fun n : nat => @lem222858 m n)). Qed.
Lemma lem222860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222861 (m : nat) : (term479 m) = (term478 m).
Proof. exact (MK_COMB (@lem222860) (@lem222859 m)). Qed.
Lemma lem222862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222863 (m : nat) : (term488 m) = (term489 m).
Proof. exact (MK_COMB (@lem222862) (@lem222861 m)). Qed.
Lemma lem222864 (m : nat) (n : nat) : (term483 m n) = (term457 m n).
Proof. exact (eq_refl (term483 m n)). Qed.
Lemma lem222865 (m : nat) : (term490 m) = (term481 m).
Proof. exact (fun_ext (fun n : nat => @lem222864 m n)). Qed.
Lemma lem222866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222867 (m : nat) : (term491 m) = (term492 m).
Proof. exact (MK_COMB (@lem222866) (@lem222865 m)). Qed.
Lemma lem222868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222869 (m : nat) : (term493 m) = (term494 m).
Proof. exact (MK_COMB (@lem222868) (@lem222867 m)). Qed.
Lemma lem222870 (m : nat) (n : nat) : (term485 m n) = (term475 m n).
Proof. exact (eq_refl (term485 m n)). Qed.
Lemma lem222871 (m : nat) : (term495 m) = (term482 m).
Proof. exact (fun_ext (fun n : nat => @lem222870 m n)). Qed.
Lemma lem222872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222873 (m : nat) : (term496 m) = (term497 m).
Proof. exact (MK_COMB (@lem222872) (@lem222871 m)). Qed.
Lemma lem222874 (m : nat) : (term480 m) = (term498 m).
Proof. exact (MK_COMB (@lem222869 m) (@lem222873 m)). Qed.
Lemma lem222875 (m : nat) : ((term479 m) = (term480 m)) = ((term478 m) = (term498 m)).
Proof. exact (MK_COMB (@lem222863 m) (@lem222874 m)). Qed.
Lemma lem222876 (m : nat) : (term478 m) = (term498 m).
Proof. exact (EQ_MP (@lem222875 m) (@lem222853 m)). Qed.
Lemma lem222981 (m : nat) : (term412 m) = (term498 m).
Proof. exact (TRANS (@lem222849 m) (@lem222876 m)). Qed.
Lemma lem222982 : term413 = term499.
Proof. exact (fun_ext (fun m : nat => @lem222981 m)). Qed.
Lemma lem222983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222984 : term414 = term500.
Proof. exact (MK_COMB (@lem222983) (@lem222982)). Qed.
Lemma lem222986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem222987 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem222986 nat P Q). Qed.
Lemma lem222988 : term501 = term502.
Proof. exact (@lem222987 term503 term504). Qed.
Lemma lem222989 (m : nat) : (term505 m) = (term492 m).
Proof. exact (eq_refl (term505 m)). Qed.
Lemma lem222990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem222991 (m : nat) : (term506 m) = (term494 m).
Proof. exact (MK_COMB (@lem222990) (@lem222989 m)). Qed.
Lemma lem222992 (m : nat) : (term507 m) = (term497 m).
Proof. exact (eq_refl (term507 m)). Qed.
Lemma lem222993 (m : nat) : (term508 m) = (term498 m).
Proof. exact (MK_COMB (@lem222991 m) (@lem222992 m)). Qed.
Lemma lem222994 : term509 = term499.
Proof. exact (fun_ext (fun m : nat => @lem222993 m)). Qed.
Lemma lem222995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem222996 : term501 = term500.
Proof. exact (MK_COMB (@lem222995) (@lem222994)). Qed.
Lemma lem222997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem222998 : term510 = term511.
Proof. exact (MK_COMB (@lem222997) (@lem222996)). Qed.
Lemma lem222999 (m : nat) : (term505 m) = (term492 m).
Proof. exact (eq_refl (term505 m)). Qed.
Lemma lem223000 : term512 = term503.
Proof. exact (fun_ext (fun m : nat => @lem222999 m)). Qed.
Lemma lem223001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223002 : term513 = term514.
Proof. exact (MK_COMB (@lem223001) (@lem223000)). Qed.
Lemma lem223003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem223004 : term515 = term516.
Proof. exact (MK_COMB (@lem223003) (@lem223002)). Qed.
Lemma lem223005 (m : nat) : (term507 m) = (term497 m).
Proof. exact (eq_refl (term507 m)). Qed.
Lemma lem223006 : term517 = term504.
Proof. exact (fun_ext (fun m : nat => @lem223005 m)). Qed.
Lemma lem223007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223008 : term518 = term519.
Proof. exact (MK_COMB (@lem223007) (@lem223006)). Qed.
Lemma lem223009 : term502 = term520.
Proof. exact (MK_COMB (@lem223004) (@lem223008)). Qed.
Lemma lem223010 : (term501 = term502) = (term500 = term520).
Proof. exact (MK_COMB (@lem222998) (@lem223009)). Qed.
Lemma lem223011 : term500 = term520.
Proof. exact (EQ_MP (@lem223010) (@lem222988)). Qed.
Lemma lem223126 : term414 = term520.
Proof. exact (TRANS (@lem222984) (@lem223011)). Qed.
Lemma lem223127 : term402 = term520.
Proof. exact (TRANS (@lem222711) (@lem223126)). Qed.
Lemma lem223128 (h1 : term402) : term520.
Proof. exact (EQ_MP (@lem223127) (@lem222655 h1)). Qed.
Lemma lem223149 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem223150 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem223149 n m)). Qed.
Lemma lem223151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223152 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem223151) (@lem223150 m)). Qed.
Lemma lem223153 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem223152 m)). Qed.
Lemma lem223154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223167 : term364 = term364.
Proof. exact (MK_COMB (@lem223154) (@lem223153)). Qed.
Lemma lem223168 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem223167) (@lem222657 h1)). Qed.
Lemma lem223310 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term407 k p m n.
Proof. exact (EQ_MP (@lem222686 k p m n) (@lem222654 k p m n h1)). Qed.
Lemma lem223315 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem223330 (m : nat) (n : nat) (p : nat) : (term463 m n p) = (term463 m n p).
Proof. exact (eq_refl (term463 m n p)). Qed.
Lemma lem223331 (m : nat) (n : nat) : (term461 m n) = (term461 m n).
Proof. exact (fun_ext (fun p : nat => @lem223330 m n p)). Qed.
Lemma lem223332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223333 (m : nat) (n : nat) : (term472 m n) = (term472 m n).
Proof. exact (MK_COMB (@lem223332) (@lem223331 m n)). Qed.
Lemma lem223334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem223335 (m : nat) (n : nat) : (term474 m n) = (term474 m n).
Proof. exact (MK_COMB (@lem223334) (@lem223333 m n)). Qed.
Lemma lem223336 (m : nat) (n : nat) : (term475 m n) = (term475 m n).
Proof. exact (MK_COMB (@lem223335 m n) (@lem223315 m n)). Qed.
Lemma lem223337 (m : nat) : (term482 m) = (term482 m).
Proof. exact (fun_ext (fun n : nat => @lem223336 m n)). Qed.
Lemma lem223338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223339 (m : nat) : (term497 m) = (term497 m).
Proof. exact (MK_COMB (@lem223338) (@lem223337 m)). Qed.
Lemma lem223340 : term504 = term504.
Proof. exact (fun_ext (fun m : nat => @lem223339 m)). Qed.
Lemma lem223341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223342 : term519 = term519.
Proof. exact (MK_COMB (@lem223341) (@lem223340)). Qed.
Lemma lem223349 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem223362 (m : nat) (n : nat) (p : nat) : (term396 m n p) = (term396 m n p).
Proof. exact (eq_refl (term396 m n p)). Qed.
Lemma lem223363 (m : nat) (n : nat) : (term444 m n) = (term444 m n).
Proof. exact (fun_ext (fun p : nat => @lem223362 m n p)). Qed.
Lemma lem223364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223365 (m : nat) (n : nat) : (term454 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem223364) (@lem223363 m n)). Qed.
Lemma lem223366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem223367 (m : nat) (n : nat) : (term456 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem223366) (@lem223365 m n)). Qed.
Lemma lem223368 (m : nat) (n : nat) : (term457 m n) = (term457 m n).
Proof. exact (MK_COMB (@lem223367 m n) (@lem223349 m n)). Qed.
Lemma lem223369 (m : nat) : (term481 m) = (term481 m).
Proof. exact (fun_ext (fun n : nat => @lem223368 m n)). Qed.
Lemma lem223370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223371 (m : nat) : (term492 m) = (term492 m).
Proof. exact (MK_COMB (@lem223370) (@lem223369 m)). Qed.
Lemma lem223372 : term503 = term503.
Proof. exact (fun_ext (fun m : nat => @lem223371 m)). Qed.
Lemma lem223373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223374 : term514 = term514.
Proof. exact (MK_COMB (@lem223373) (@lem223372)). Qed.
Lemma lem223375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem223376 : term516 = term516.
Proof. exact (MK_COMB (@lem223375) (@lem223374)). Qed.
Lemma lem223377 : term520 = term520.
Proof. exact (MK_COMB (@lem223376) (@lem223342)). Qed.
Lemma lem223378 (h1 : term402) : term520.
Proof. exact (EQ_MP (@lem223377) (@lem223128 h1)). Qed.
Lemma lem223411 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem223412 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem223411 n m)). Qed.
Lemma lem223413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223414 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem223413) (@lem223412 m)). Qed.
Lemma lem223415 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem223414 m)). Qed.
Lemma lem223416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223417 : term364 = term364.
Proof. exact (MK_COMB (@lem223416) (@lem223415)). Qed.
Lemma lem223418 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem223417) (@lem223168 h1)). Qed.
Lemma lem223419 (h1 : term402) : term519.
Proof. exact (proj2 (@lem223378 h1)). Qed.
Lemma lem223420 (h1 : term402) : term514.
Proof. exact (proj1 (@lem223378 h1)). Qed.
Lemma lem223421 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term404 k p m n.
Proof. exact (proj2 (@lem223310 k p m n h1)). Qed.
Lemma lem223422 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term332 m n p.
Proof. exact (proj1 (@lem223310 k p m n h1)). Qed.
Lemma lem223425 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term521 k p m n) : term521 k p m n.
Proof. exact (h1). Qed.
Lemma lem223426 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term522 k p m n) : term522 k p m n.
Proof. exact (h1). Qed.
Lemma lem223442 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem223443 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem223442 n m)). Qed.
Lemma lem223444 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223445 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem223444) (@lem223443 m)). Qed.
Lemma lem223446 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem223445 m)). Qed.
Lemma lem223447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223449 : term364 = term364.
Proof. exact (MK_COMB (@lem223447) (@lem223446)). Qed.
Lemma lem223450 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem223449) (@lem223418 h1)). Qed.
Lemma lem223452 {A : Type'} (P : A -> Prop) (Q : Prop) : (term439 A P Q) = (term438 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem223453 (P : nat -> Prop) (Q : Prop) : (term441 P Q) = (term440 P Q).
Proof. exact (@lem223452 nat P Q). Qed.
Lemma lem223454 (m : nat) (n : nat) : (term443 m n) = (term442 m n).
Proof. exact (@lem223453 (term444 m n) (term162 m n)). Qed.
Lemma lem223455 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem223456 (m : nat) (n : nat) : (term452 m n) = (term444 m n).
Proof. exact (fun_ext (fun p : nat => @lem223455 m n p)). Qed.
Lemma lem223457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223458 (m : nat) (n : nat) : (term453 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem223457) (@lem223456 m n)). Qed.
Lemma lem223459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem223460 (m : nat) (n : nat) : (term455 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem223459) (@lem223458 m n)). Qed.
Lemma lem223461 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem223462 (m : nat) (n : nat) : (term443 m n) = (term457 m n).
Proof. exact (MK_COMB (@lem223460 m n) (@lem223461 m n)). Qed.
Lemma lem223463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem223464 (m : nat) (n : nat) : (term523 m n) = (term524 m n).
Proof. exact (MK_COMB (@lem223463) (@lem223462 m n)). Qed.
Lemma lem223465 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem223466 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem223467 (m : nat) (n : nat) (p : nat) : (term446 m n p) = (term447 m n p).
Proof. exact (MK_COMB (@lem223466) (@lem223465 m n p)). Qed.
Lemma lem223468 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem223469 (p : nat) (m : nat) (n : nat) : (term448 p m n) = (term420 p m n).
Proof. exact (MK_COMB (@lem223467 m n p) (@lem223468 m n)). Qed.
Lemma lem223470 (m : nat) (n : nat) : (term449 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem223469 p m n)). Qed.
Lemma lem223471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223472 (m : nat) (n : nat) : (term442 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem223471) (@lem223470 m n)). Qed.
Lemma lem223473 (m : nat) (n : nat) : ((term443 m n) = (term442 m n)) = ((term457 m n) = (term431 m n)).
Proof. exact (MK_COMB (@lem223464 m n) (@lem223472 m n)). Qed.
Lemma lem223474 (m : nat) (n : nat) : (term457 m n) = (term431 m n).
Proof. exact (EQ_MP (@lem223473 m n) (@lem223454 m n)). Qed.
Lemma lem223475 (m : nat) : (term481 m) = (term525 m).
Proof. exact (fun_ext (fun n : nat => @lem223474 m n)). Qed.
Lemma lem223476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223477 (m : nat) : (term492 m) = (term526 m).
Proof. exact (MK_COMB (@lem223476) (@lem223475 m)). Qed.
Lemma lem223478 : term503 = term527.
Proof. exact (fun_ext (fun m : nat => @lem223477 m)). Qed.
Lemma lem223479 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223480 : term514 = term528.
Proof. exact (MK_COMB (@lem223479) (@lem223478)). Qed.
Lemma lem223487 (p : nat) (m : nat) (n : nat) : (term420 p m n) = (term420 p m n).
Proof. exact (eq_refl (term420 p m n)). Qed.
Lemma lem223488 (m : nat) (n : nat) : (term417 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem223487 p m n)). Qed.
Lemma lem223489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223490 (m : nat) (n : nat) : (term431 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem223489) (@lem223488 m n)). Qed.
Lemma lem223491 (m : nat) : (term525 m) = (term525 m).
Proof. exact (fun_ext (fun n : nat => @lem223490 m n)). Qed.
Lemma lem223492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223493 (m : nat) : (term526 m) = (term526 m).
Proof. exact (MK_COMB (@lem223492) (@lem223491 m)). Qed.
Lemma lem223494 : term527 = term527.
Proof. exact (fun_ext (fun m : nat => @lem223493 m)). Qed.
Lemma lem223495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223496 : term528 = term528.
Proof. exact (MK_COMB (@lem223495) (@lem223494)). Qed.
Lemma lem223497 : term514 = term528.
Proof. exact (TRANS (@lem223480) (@lem223496)). Qed.
Lemma lem223498 (h1 : term402) : term528.
Proof. exact (EQ_MP (@lem223497) (@lem223420 h1)). Qed.
Lemma lem223574 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem223575 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem223574 n m)). Qed.
Lemma lem223576 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223577 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem223576) (@lem223575 m)). Qed.
Lemma lem223578 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem223577 m)). Qed.
Lemma lem223579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223581 : term364 = term364.
Proof. exact (MK_COMB (@lem223579) (@lem223578)). Qed.
Lemma lem223582 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem223581) (@lem223418 h1)). Qed.
Lemma lem223632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term439 A P Q) = (term438 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem223633 (P : nat -> Prop) (Q : Prop) : (term441 P Q) = (term440 P Q).
Proof. exact (@lem223632 nat P Q). Qed.
Lemma lem223634 (m : nat) (n : nat) : (term460 m n) = (term459 m n).
Proof. exact (@lem223633 (term461 m n) (Peano.le m n)). Qed.
Lemma lem223635 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem223636 (m : nat) (n : nat) : (term470 m n) = (term461 m n).
Proof. exact (fun_ext (fun p : nat => @lem223635 m n p)). Qed.
Lemma lem223637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223638 (m : nat) (n : nat) : (term471 m n) = (term472 m n).
Proof. exact (MK_COMB (@lem223637) (@lem223636 m n)). Qed.
Lemma lem223639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem223640 (m : nat) (n : nat) : (term473 m n) = (term474 m n).
Proof. exact (MK_COMB (@lem223639) (@lem223638 m n)). Qed.
Lemma lem223641 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem223642 (m : nat) (n : nat) : (term460 m n) = (term475 m n).
Proof. exact (MK_COMB (@lem223640 m n) (@lem223641 m n)). Qed.
Lemma lem223643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem223644 (m : nat) (n : nat) : (term529 m n) = (term530 m n).
Proof. exact (MK_COMB (@lem223643) (@lem223642 m n)). Qed.
Lemma lem223645 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem223646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem223647 (m : nat) (n : nat) (p : nat) : (term464 m n p) = (term465 m n p).
Proof. exact (MK_COMB (@lem223646) (@lem223645 m n p)). Qed.
Lemma lem223648 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem223649 (p : nat) (m : nat) (n : nat) : (term466 p m n) = (term424 p m n).
Proof. exact (MK_COMB (@lem223647 m n p) (@lem223648 m n)). Qed.
Lemma lem223650 (m : nat) (n : nat) : (term467 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem223649 p m n)). Qed.
Lemma lem223651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223652 (m : nat) (n : nat) : (term459 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem223651) (@lem223650 m n)). Qed.
Lemma lem223653 (m : nat) (n : nat) : ((term460 m n) = (term459 m n)) = ((term475 m n) = (term436 m n)).
Proof. exact (MK_COMB (@lem223644 m n) (@lem223652 m n)). Qed.
Lemma lem223654 (m : nat) (n : nat) : (term475 m n) = (term436 m n).
Proof. exact (EQ_MP (@lem223653 m n) (@lem223634 m n)). Qed.
Lemma lem223655 (m : nat) : (term482 m) = (term531 m).
Proof. exact (fun_ext (fun n : nat => @lem223654 m n)). Qed.
Lemma lem223656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223657 (m : nat) : (term497 m) = (term532 m).
Proof. exact (MK_COMB (@lem223656) (@lem223655 m)). Qed.
Lemma lem223658 : term504 = term533.
Proof. exact (fun_ext (fun m : nat => @lem223657 m)). Qed.
Lemma lem223659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223660 : term519 = term534.
Proof. exact (MK_COMB (@lem223659) (@lem223658)). Qed.
Lemma lem223667 (p : nat) (m : nat) (n : nat) : (term424 p m n) = (term424 p m n).
Proof. exact (eq_refl (term424 p m n)). Qed.
Lemma lem223668 (m : nat) (n : nat) : (term418 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem223667 p m n)). Qed.
Lemma lem223669 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223670 (m : nat) (n : nat) : (term436 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem223669) (@lem223668 m n)). Qed.
Lemma lem223671 (m : nat) : (term531 m) = (term531 m).
Proof. exact (fun_ext (fun n : nat => @lem223670 m n)). Qed.
Lemma lem223672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223673 (m : nat) : (term532 m) = (term532 m).
Proof. exact (MK_COMB (@lem223672) (@lem223671 m)). Qed.
Lemma lem223674 : term533 = term533.
Proof. exact (fun_ext (fun m : nat => @lem223673 m)). Qed.
Lemma lem223675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem223676 : term534 = term534.
Proof. exact (MK_COMB (@lem223675) (@lem223674)). Qed.
Lemma lem223677 : term519 = term534.
Proof. exact (TRANS (@lem223660) (@lem223676)). Qed.
Lemma lem223678 (h1 : term402) : term534.
Proof. exact (EQ_MP (@lem223677) (@lem223419 h1)). Qed.
Lemma lem223701 (_4412 : nat) (h1 : term364) : term535 _4412.
Proof. exact (@lem223450 h1 _4412). Qed.
Lemma lem223702 (_4412 : nat) : (term535 _4412) = (term390 _4412).
Proof. exact (eq_refl (term535 _4412)). Qed.
Lemma lem223703 (_4412 : nat) (h1 : term364) : term390 _4412.
Proof. exact (EQ_MP (@lem223702 _4412) (@lem223701 _4412 h1)). Qed.
Lemma lem223704 (_4412 : nat) (_4413 : nat) (h1 : term364) : term536 _4412 _4413.
Proof. exact (@lem223703 _4412 h1 _4413). Qed.
Lemma lem223705 (_4413 : nat) (_4412 : nat) : (term536 _4412 _4413) = ((Nat.add _4412 _4413) = (Nat.add _4413 _4412)).
Proof. exact (eq_refl (term536 _4412 _4413)). Qed.
Lemma lem223707 (_4414 : nat) (h1 : term402) : term537 _4414.
Proof. exact (@lem223498 h1 _4414). Qed.
Lemma lem223708 (_4414 : nat) : (term537 _4414) = (term526 _4414).
Proof. exact (eq_refl (term537 _4414)). Qed.
Lemma lem223709 (_4414 : nat) (h1 : term402) : term526 _4414.
Proof. exact (EQ_MP (@lem223708 _4414) (@lem223707 _4414 h1)). Qed.
Lemma lem223710 (_4414 : nat) (_4415 : nat) (h1 : term402) : term538 _4414 _4415.
Proof. exact (@lem223709 _4414 h1 _4415). Qed.
Lemma lem223711 (_4414 : nat) (_4415 : nat) : (term538 _4414 _4415) = (term431 _4414 _4415).
Proof. exact (eq_refl (term538 _4414 _4415)). Qed.
Lemma lem223712 (_4414 : nat) (_4415 : nat) (h1 : term402) : term431 _4414 _4415.
Proof. exact (EQ_MP (@lem223711 _4414 _4415) (@lem223710 _4414 _4415 h1)). Qed.
Lemma lem223713 (_4414 : nat) (_4415 : nat) (_4416 : nat) (h1 : term402) : term419 _4414 _4415 _4416.
Proof. exact (@lem223712 _4414 _4415 h1 _4416). Qed.
Lemma lem223714 (_4416 : nat) (_4414 : nat) (_4415 : nat) : (term419 _4414 _4415 _4416) = (term420 _4416 _4414 _4415).
Proof. exact (eq_refl (term419 _4414 _4415 _4416)). Qed.
Lemma lem223731 (_4422 : nat) (h1 : term364) : term535 _4422.
Proof. exact (@lem223582 h1 _4422). Qed.
Lemma lem223732 (_4422 : nat) : (term535 _4422) = (term390 _4422).
Proof. exact (eq_refl (term535 _4422)). Qed.
Lemma lem223733 (_4422 : nat) (h1 : term364) : term390 _4422.
Proof. exact (EQ_MP (@lem223732 _4422) (@lem223731 _4422 h1)). Qed.
Lemma lem223734 (_4422 : nat) (_4423 : nat) (h1 : term364) : term536 _4422 _4423.
Proof. exact (@lem223733 _4422 h1 _4423). Qed.
Lemma lem223735 (_4423 : nat) (_4422 : nat) : (term536 _4422 _4423) = ((Nat.add _4422 _4423) = (Nat.add _4423 _4422)).
Proof. exact (eq_refl (term536 _4422 _4423)). Qed.
Lemma lem223746 (_4427 : nat) (h1 : term402) : term539 _4427.
Proof. exact (@lem223678 h1 _4427). Qed.
Lemma lem223747 (_4427 : nat) : (term539 _4427) = (term532 _4427).
Proof. exact (eq_refl (term539 _4427)). Qed.
Lemma lem223748 (_4427 : nat) (h1 : term402) : term532 _4427.
Proof. exact (EQ_MP (@lem223747 _4427) (@lem223746 _4427 h1)). Qed.
Lemma lem223749 (_4427 : nat) (_4428 : nat) (h1 : term402) : term540 _4427 _4428.
Proof. exact (@lem223748 _4427 h1 _4428). Qed.
Lemma lem223750 (_4427 : nat) (_4428 : nat) : (term540 _4427 _4428) = (term436 _4427 _4428).
Proof. exact (eq_refl (term540 _4427 _4428)). Qed.
Lemma lem223751 (_4427 : nat) (_4428 : nat) (h1 : term402) : term436 _4427 _4428.
Proof. exact (EQ_MP (@lem223750 _4427 _4428) (@lem223749 _4427 _4428 h1)). Qed.
Lemma lem223752 (_4427 : nat) (_4428 : nat) (_4429 : nat) (h1 : term402) : term423 _4427 _4428 _4429.
Proof. exact (@lem223751 _4427 _4428 h1 _4429). Qed.
Lemma lem223753 (_4429 : nat) (_4427 : nat) (_4428 : nat) : (term423 _4427 _4428 _4429) = (term424 _4429 _4427 _4428).
Proof. exact (eq_refl (term423 _4427 _4428 _4429)). Qed.
Lemma lem223764 (_4416 : nat) (_4414 : nat) (_4415 : nat) (h1 : term402) : term420 _4416 _4414 _4415.
Proof. exact (EQ_MP (@lem223714 _4416 _4414 _4415) (@lem223713 _4414 _4415 _4416 h1)). Qed.
Lemma lem223778 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term521 k p m n) : term541 k p m n.
Proof. exact (proj2 (@lem223425 k p m n h1)). Qed.
Lemma lem223794 (_4429 : nat) (_4427 : nat) (_4428 : nat) (h1 : term402) : term424 _4429 _4427 _4428.
Proof. exact (EQ_MP (@lem223753 _4429 _4427 _4428) (@lem223752 _4427 _4428 _4429 h1)). Qed.
Lemma lem223800 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term522 k p m n) : term542 k m n p.
Proof. exact (proj1 (@lem223426 k p m n h1)). Qed.
Lemma lem223822 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem223823 (_4434 : nat) (_4436 : nat) (h1 : _4434 = _4436) : _4434 = _4436.
Proof. exact (h1). Qed.
Lemma lem223824 (_4435 : nat) (_4437 : nat) (h1 : _4435 = _4437) : _4435 = _4437.
Proof. exact (h1). Qed.
Lemma lem223825 (_4434 : nat) (_4436 : nat) (h1 : _4434 = _4436) : (Peano.le _4434) = (Peano.le _4436).
Proof. exact (MK_COMB (@lem223822) (@lem223823 _4434 _4436 h1)). Qed.
Lemma lem223826 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) (h1 : _4434 = _4436) (h2 : _4435 = _4437) : (Peano.le _4434 _4435) = (Peano.le _4436 _4437).
Proof. exact (MK_COMB (@lem223825 _4434 _4436 h1) (@lem223824 _4435 _4437 h2)). Qed.
Lemma lem223828 (b : Prop) (a : Prop) : term543 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem223829 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : term544 _4436 _4437 _4434 _4435.
Proof. exact (@lem223828 (Peano.le _4436 _4437) (Peano.le _4434 _4435)). Qed.
Lemma lem223830 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) (h1 : _4434 = _4436) (h2 : _4435 = _4437) : term545 _4436 _4437 _4434 _4435.
Proof. exact (@lem223829 _4436 _4437 _4434 _4435 (@lem223826 _4434 _4436 _4435 _4437 h1 h2)). Qed.
Lemma lem223831 (_4437 : nat) (_4435 : nat) (_4434 : nat) (_4436 : nat) (h1 : _4434 = _4436) : term546 _4436 _4437 _4434 _4435.
Proof. exact (fun h0 : _4435 = _4437 => @lem223830 _4434 _4436 _4435 _4437 h1 h0). Qed.
Lemma lem223833 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem223834 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term546 _4436 _4437 _4434 _4435) = (term548 _4436 _4437 _4434 _4435).
Proof. exact (@lem223833 (_4435 = _4437) (term545 _4436 _4437 _4434 _4435)). Qed.
Lemma lem223835 (_4437 : nat) (_4435 : nat) (_4434 : nat) (_4436 : nat) (h1 : _4434 = _4436) : term548 _4436 _4437 _4434 _4435.
Proof. exact (EQ_MP (@lem223834 _4436 _4437 _4434 _4435) (@lem223831 _4437 _4435 _4434 _4436 h1)). Qed.
Lemma lem223836 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : term549 _4436 _4437 _4434 _4435.
Proof. exact (fun h0 : _4434 = _4436 => @lem223835 _4437 _4435 _4434 _4436 h0). Qed.
Lemma lem223838 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem223839 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term549 _4436 _4437 _4434 _4435) = (term550 _4436 _4437 _4434 _4435).
Proof. exact (@lem223838 (_4434 = _4436) (term548 _4436 _4437 _4434 _4435)). Qed.
Lemma lem223840 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : term550 _4436 _4437 _4434 _4435.
Proof. exact (EQ_MP (@lem223839 _4436 _4437 _4434 _4435) (@lem223836 _4436 _4437 _4434 _4435)). Qed.
Lemma lem223902 (x : nat) (y : nat) (z : nat) : term551 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem223904 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem223905 (k : nat) (m : nat) (n : nat) (p : nat) : (term303 k m n p) = (term303 k m n p).
Proof. exact (@lem223904 (term303 k m n p)). Qed.
Lemma lem223906 (k : nat) (m : nat) (n : nat) (p : nat) : term552 k m n p.
Proof. exact (fun h0 : term553 k m n p => @lem223905 k m n p). Qed.
Lemma lem223908 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem223909 (k : nat) (m : nat) (n : nat) (p : nat) : (term552 k m n p) = ((term303 k m n p) = (term303 k m n p)).
Proof. exact (@lem223908 ((term303 k m n p) = (term303 k m n p))). Qed.
Lemma lem223910 (k : nat) (m : nat) (n : nat) (p : nat) : (term303 k m n p) = (term303 k m n p).
Proof. exact (EQ_MP (@lem223909 k m n p) (@lem223906 k m n p)). Qed.
Lemma lem223912 (_4413 : nat) (_4412 : nat) (h1 : term364) : (Nat.add _4412 _4413) = (Nat.add _4413 _4412).
Proof. exact (EQ_MP (@lem223705 _4413 _4412) (@lem223704 _4412 _4413 h1)). Qed.
Lemma lem223913 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term328 m n p) = (term554 m n p).
Proof. exact (@lem223912 (term220 m n p) (term307 m n p) h1). Qed.
Lemma lem223914 (m : nat) (n : nat) (p : nat) (h1 : term364) : term555 m n p.
Proof. exact (fun h0 : term556 m n p => @lem223913 m n p h1). Qed.
Lemma lem223916 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem223917 (m : nat) (n : nat) (p : nat) : (term555 m n p) = ((term328 m n p) = (term554 m n p)).
Proof. exact (@lem223916 ((term328 m n p) = (term554 m n p))). Qed.
Lemma lem223918 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term328 m n p) = (term554 m n p).
Proof. exact (EQ_MP (@lem223917 m n p) (@lem223914 m n p h1)). Qed.
Lemma lem223920 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (Nat.div m n) = (term328 m n p).
Proof. exact (proj1 (@lem223422 k p m n h1)). Qed.
Lemma lem223921 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term557 m n p.
Proof. exact (fun h0 : term558 m n p => @lem223920 k p m n h1). Qed.
Lemma lem223923 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem223924 (m : nat) (n : nat) (p : nat) : (term557 m n p) = ((Nat.div m n) = (term328 m n p)).
Proof. exact (@lem223923 ((Nat.div m n) = (term328 m n p))). Qed.
Lemma lem223925 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (Nat.div m n) = (term328 m n p).
Proof. exact (EQ_MP (@lem223924 m n p) (@lem223921 k p m n h1)). Qed.
Lemma lem223927 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem223928 (m : nat) (n : nat) : (Nat.div m n) = (Nat.div m n).
Proof. exact (@lem223927 (Nat.div m n)). Qed.
Lemma lem223929 (m : nat) (n : nat) : term559 m n.
Proof. exact (fun h0 : term560 m n => @lem223928 m n). Qed.
Lemma lem223931 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem223932 (m : nat) (n : nat) : (term559 m n) = ((Nat.div m n) = (Nat.div m n)).
Proof. exact (@lem223931 ((Nat.div m n) = (Nat.div m n))). Qed.
Lemma lem223933 (m : nat) (n : nat) : (Nat.div m n) = (Nat.div m n).
Proof. exact (EQ_MP (@lem223932 m n) (@lem223929 m n)). Qed.
Lemma lem223951 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem223952 (y : nat) (x : nat) (z : nat) : (term561 x y z) = (term562 y x z).
Proof. exact (@lem223951 (y = z) (term64 x z)). Qed.
Lemma lem223962 (x : nat) (y : nat) : (term563 x y) = (term563 x y).
Proof. exact (eq_refl (term563 x y)). Qed.
Lemma lem223963 (y : nat) (x : nat) (z : nat) : (term551 x y z) = (term564 y x z).
Proof. exact (MK_COMB (@lem223962 x y) (@lem223952 y x z)). Qed.
Lemma lem223967 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem223968 (y : nat) (x : nat) (z : nat) : (term564 y x z) = (term565 y x z).
Proof. exact (@lem223967 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem223990 (y : nat) (x : nat) (z : nat) : (term551 x y z) = (term565 y x z).
Proof. exact (TRANS (@lem223963 y x z) (@lem223968 y x z)). Qed.
Lemma lem223991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem223992 (y : nat) (x : nat) (z : nat) : (term566 x y z) = (term567 y x z).
Proof. exact (MK_COMB (@lem223991) (@lem223990 y x z)). Qed.
Lemma lem224014 (y : nat) (x : nat) (z : nat) : (term565 y x z) = (term565 y x z).
Proof. exact (eq_refl (term565 y x z)). Qed.
Lemma lem224015 (y : nat) (x : nat) (z : nat) : ((term551 x y z) = (term565 y x z)) = ((term565 y x z) = (term565 y x z)).
Proof. exact (MK_COMB (@lem223992 y x z) (@lem224014 y x z)). Qed.
Lemma lem224017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem224018 (x : Prop) : (x = x) = True.
Proof. exact (@lem224017 Prop x). Qed.
Lemma lem224019 (y : nat) (x : nat) (z : nat) : ((term565 y x z) = (term565 y x z)) = True.
Proof. exact (@lem224018 (term565 y x z)). Qed.
Lemma lem224020 (y : nat) (x : nat) (z : nat) : ((term551 x y z) = (term565 y x z)) = True.
Proof. exact (TRANS (@lem224015 y x z) (@lem224019 y x z)). Qed.
Lemma lem224021 (y : nat) (x : nat) (z : nat) : True = ((term551 x y z) = (term565 y x z)).
Proof. exact (SYM (@lem224020 y x z)). Qed.
Lemma lem224022 (y : nat) (x : nat) (z : nat) : (term551 x y z) = (term565 y x z).
Proof. exact (EQ_MP (@lem224021 y x z) (@lem0)). Qed.
Lemma lem224023 (y : nat) (x : nat) (z : nat) : term565 y x z.
Proof. exact (EQ_MP (@lem224022 y x z) (@lem223902 x y z)). Qed.
Lemma lem224025 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem224026 (x : nat) (y : nat) (z : nat) : (term565 y x z) = (term568 x y z).
Proof. exact (@lem224025 (term569 y x z) (y = z)). Qed.
Lemma lem224028 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem224029 (y : nat) (x : nat) (z : nat) : (term570 y x z) = (term571 y x z).
Proof. exact (@lem224028 (term64 x y) (term64 x z)). Qed.
Lemma lem224031 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224032 (x : nat) (y : nat) : (term170 x y) = (x = y).
Proof. exact (@lem224031 (x = y)). Qed.
Lemma lem224033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem224034 (x : nat) (y : nat) : (term572 x y) = (term573 x y).
Proof. exact (MK_COMB (@lem224033) (@lem224032 x y)). Qed.
Lemma lem224036 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224037 (x : nat) (z : nat) : (term170 x z) = (x = z).
Proof. exact (@lem224036 (x = z)). Qed.
Lemma lem224038 (y : nat) (x : nat) (z : nat) : (term571 y x z) = (term574 y x z).
Proof. exact (MK_COMB (@lem224034 x y) (@lem224037 x z)). Qed.
Lemma lem224039 (y : nat) (x : nat) (z : nat) : (term570 y x z) = (term574 y x z).
Proof. exact (TRANS (@lem224029 y x z) (@lem224038 y x z)). Qed.
Lemma lem224040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem224041 (y : nat) (x : nat) (z : nat) : (term575 y x z) = (term576 y x z).
Proof. exact (MK_COMB (@lem224040) (@lem224039 y x z)). Qed.
Lemma lem224042 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem224043 (x : nat) (y : nat) (z : nat) : (term568 x y z) = (term577 x y z).
Proof. exact (MK_COMB (@lem224041 y x z) (@lem224042 y z)). Qed.
Lemma lem224044 (x : nat) (y : nat) (z : nat) : (term565 y x z) = (term577 x y z).
Proof. exact (TRANS (@lem224026 x y z) (@lem224043 x y z)). Qed.
Lemma lem224046 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term578 p m n.
Proof. exact (conj (@lem223925 k p m n h1) (@lem223933 m n)). Qed.
Lemma lem224048 (x : nat) (y : nat) (z : nat) : term577 x y z.
Proof. exact (EQ_MP (@lem224044 x y z) (@lem224023 y x z)). Qed.
Lemma lem224049 (p : nat) (m : nat) (n : nat) : term579 p m n.
Proof. exact (@lem224048 (Nat.div m n) (term328 m n p) (Nat.div m n)). Qed.
Lemma lem224052 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (term328 m n p) = (Nat.div m n).
Proof. exact (@lem224049 p m n (@lem224046 k p m n h1)). Qed.
Lemma lem224053 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term580 p m n.
Proof. exact (fun h0 : term581 p m n => @lem224052 k p m n h1). Qed.
Lemma lem224055 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224056 (p : nat) (m : nat) (n : nat) : (term580 p m n) = ((term328 m n p) = (Nat.div m n)).
Proof. exact (@lem224055 ((term328 m n p) = (Nat.div m n))). Qed.
Lemma lem224057 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (term328 m n p) = (Nat.div m n).
Proof. exact (EQ_MP (@lem224056 p m n) (@lem224053 k p m n h1)). Qed.
Lemma lem224058 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) : term582 p m n.
Proof. exact (conj (@lem223918 m n p h1) (@lem224057 k p m n h2)). Qed.
Lemma lem224060 (x : nat) (y : nat) (z : nat) : term577 x y z.
Proof. exact (EQ_MP (@lem224044 x y z) (@lem224023 y x z)). Qed.
Lemma lem224061 (p : nat) (m : nat) (n : nat) : term583 p m n.
Proof. exact (@lem224060 (term328 m n p) (term554 m n p) (Nat.div m n)). Qed.
Lemma lem224064 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) : (term554 m n p) = (Nat.div m n).
Proof. exact (@lem224061 p m n (@lem224058 k p m n h1 h2)). Qed.
Lemma lem224065 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) : term584 p m n.
Proof. exact (fun h0 : term585 p m n => @lem224064 k p m n h1 h2). Qed.
Lemma lem224067 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224068 (p : nat) (m : nat) (n : nat) : (term584 p m n) = ((term554 m n p) = (Nat.div m n)).
Proof. exact (@lem224067 ((term554 m n p) = (Nat.div m n))). Qed.
Lemma lem224069 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) : (term554 m n p) = (Nat.div m n).
Proof. exact (EQ_MP (@lem224068 p m n) (@lem224065 k p m n h1 h2)). Qed.
Lemma lem224071 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term521 k p m n) : term242 k m n p.
Proof. exact (proj1 (@lem223425 k p m n h1)). Qed.
Lemma lem224072 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term521 k p m n) : term586 k m n p.
Proof. exact (fun h0 : term542 k m n p => @lem224071 k p m n h1). Qed.
Lemma lem224074 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224075 (k : nat) (m : nat) (n : nat) (p : nat) : (term586 k m n p) = (term242 k m n p).
Proof. exact (@lem224074 (term242 k m n p)). Qed.
Lemma lem224076 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term521 k p m n) : term242 k m n p.
Proof. exact (EQ_MP (@lem224075 k m n p) (@lem224072 k p m n h1)). Qed.
Lemma lem224078 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem224079 (_4414 : nat) (_4415 : nat) (_4416 : nat) : (term420 _4416 _4414 _4415) = (term587 _4414 _4415 _4416).
Proof. exact (@lem224078 (term162 _4414 _4415) (term396 _4414 _4415 _4416)). Qed.
Lemma lem224081 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224082 (_4414 : nat) (_4415 : nat) : (term180 _4414 _4415) = (Peano.le _4414 _4415).
Proof. exact (@lem224081 (Peano.le _4414 _4415)). Qed.
Lemma lem224083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem224084 (_4414 : nat) (_4415 : nat) : (term181 _4414 _4415) = (term182 _4414 _4415).
Proof. exact (MK_COMB (@lem224083) (@lem224082 _4414 _4415)). Qed.
Lemma lem224085 (_4414 : nat) (_4415 : nat) (_4416 : nat) : (term396 _4414 _4415 _4416) = (term396 _4414 _4415 _4416).
Proof. exact (eq_refl (term396 _4414 _4415 _4416)). Qed.
Lemma lem224086 (_4414 : nat) (_4415 : nat) (_4416 : nat) : (term587 _4414 _4415 _4416) = (term588 _4414 _4415 _4416).
Proof. exact (MK_COMB (@lem224084 _4414 _4415) (@lem224085 _4414 _4415 _4416)). Qed.
Lemma lem224087 (_4414 : nat) (_4415 : nat) (_4416 : nat) : (term420 _4416 _4414 _4415) = (term588 _4414 _4415 _4416).
Proof. exact (TRANS (@lem224079 _4414 _4415 _4416) (@lem224086 _4414 _4415 _4416)). Qed.
Lemma lem224090 (_4414 : nat) (_4415 : nat) (_4416 : nat) (h1 : term402) : term588 _4414 _4415 _4416.
Proof. exact (EQ_MP (@lem224087 _4414 _4415 _4416) (@lem223764 _4416 _4414 _4415 h1)). Qed.
Lemma lem224091 (k : nat) (m : nat) (n : nat) (p : nat) (_4416 : nat) (h1 : term402) : term589 k m n p _4416.
Proof. exact (@lem224090 k (term220 m n p) _4416 h1). Qed.
Lemma lem224094 (_4416 : nat) (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term521 k p m n) : term590 k m n p _4416.
Proof. exact (@lem224091 k m n p _4416 h1 (@lem224076 k p m n h2)). Qed.
Lemma lem224095 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term521 k p m n) : term591 k m n p.
Proof. exact (@lem224094 (term307 m n p) k p m n h1 h2). Qed.
Lemma lem224096 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term521 k p m n) : term592 k m n p.
Proof. exact (fun h0 : term593 k m n p => @lem224095 k p m n h1 h2). Qed.
Lemma lem224098 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224099 (k : nat) (m : nat) (n : nat) (p : nat) : (term592 k m n p) = (term591 k m n p).
Proof. exact (@lem224098 (term591 k m n p)). Qed.
Lemma lem224100 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term521 k p m n) : term591 k m n p.
Proof. exact (EQ_MP (@lem224099 k m n p) (@lem224096 k p m n h1 h2)). Qed.
Lemma lem224118 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224119 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term548 _4436 _4437 _4434 _4435) = (term594 _4436 _4437 _4434 _4435).
Proof. exact (@lem224118 (Peano.le _4436 _4437) (term64 _4435 _4437) (term162 _4434 _4435)). Qed.
Lemma lem224133 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem224134 (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term595 _4437 _4434 _4435) = (term596 _4434 _4435 _4437).
Proof. exact (@lem224133 (term162 _4434 _4435) (term64 _4435 _4437)). Qed.
Lemma lem224142 (_4436 : nat) (_4437 : nat) : (term597 _4436 _4437) = (term597 _4436 _4437).
Proof. exact (eq_refl (term597 _4436 _4437)). Qed.
Lemma lem224143 (_4436 : nat) (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term594 _4436 _4437 _4434 _4435) = (term598 _4436 _4434 _4435 _4437).
Proof. exact (MK_COMB (@lem224142 _4436 _4437) (@lem224134 _4434 _4435 _4437)). Qed.
Lemma lem224154 (_4436 : nat) (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term548 _4436 _4437 _4434 _4435) = (term598 _4436 _4434 _4435 _4437).
Proof. exact (TRANS (@lem224119 _4436 _4437 _4434 _4435) (@lem224143 _4436 _4434 _4435 _4437)). Qed.
Lemma lem224155 (_4434 : nat) (_4436 : nat) : (term563 _4434 _4436) = (term563 _4434 _4436).
Proof. exact (eq_refl (term563 _4434 _4436)). Qed.
Lemma lem224156 (_4436 : nat) (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term550 _4436 _4437 _4434 _4435) = (term599 _4436 _4434 _4435 _4437).
Proof. exact (MK_COMB (@lem224155 _4434 _4436) (@lem224154 _4436 _4434 _4435 _4437)). Qed.
Lemma lem224160 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224161 (_4436 : nat) (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term599 _4436 _4434 _4435 _4437) = (term600 _4436 _4434 _4435 _4437).
Proof. exact (@lem224160 (Peano.le _4436 _4437) (term64 _4434 _4436) (term596 _4434 _4435 _4437)). Qed.
Lemma lem224175 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224176 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term601 _4436 _4434 _4435 _4437) = (term602 _4434 _4436 _4435 _4437).
Proof. exact (@lem224175 (term162 _4434 _4435) (term64 _4434 _4436) (term64 _4435 _4437)). Qed.
Lemma lem224196 (_4436 : nat) (_4437 : nat) : (term597 _4436 _4437) = (term597 _4436 _4437).
Proof. exact (eq_refl (term597 _4436 _4437)). Qed.
Lemma lem224197 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term600 _4436 _4434 _4435 _4437) = (term603 _4434 _4436 _4435 _4437).
Proof. exact (MK_COMB (@lem224196 _4436 _4437) (@lem224176 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224208 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term599 _4436 _4434 _4435 _4437) = (term603 _4434 _4436 _4435 _4437).
Proof. exact (TRANS (@lem224161 _4436 _4434 _4435 _4437) (@lem224197 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224209 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term550 _4436 _4437 _4434 _4435) = (term603 _4434 _4436 _4435 _4437).
Proof. exact (TRANS (@lem224156 _4436 _4434 _4435 _4437) (@lem224208 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem224211 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term604 _4436 _4437 _4434 _4435) = (term605 _4434 _4436 _4435 _4437).
Proof. exact (MK_COMB (@lem224210) (@lem224209 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224237 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem224238 (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term595 _4437 _4434 _4435) = (term596 _4434 _4435 _4437).
Proof. exact (@lem224237 (term162 _4434 _4435) (term64 _4435 _4437)). Qed.
Lemma lem224246 (_4434 : nat) (_4436 : nat) : (term563 _4434 _4436) = (term563 _4434 _4436).
Proof. exact (eq_refl (term563 _4434 _4436)). Qed.
Lemma lem224247 (_4436 : nat) (_4434 : nat) (_4435 : nat) (_4437 : nat) : (term606 _4436 _4437 _4434 _4435) = (term601 _4436 _4434 _4435 _4437).
Proof. exact (MK_COMB (@lem224246 _4434 _4436) (@lem224238 _4434 _4435 _4437)). Qed.
Lemma lem224251 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224252 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term601 _4436 _4434 _4435 _4437) = (term602 _4434 _4436 _4435 _4437).
Proof. exact (@lem224251 (term162 _4434 _4435) (term64 _4434 _4436) (term64 _4435 _4437)). Qed.
Lemma lem224272 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term606 _4436 _4437 _4434 _4435) = (term602 _4434 _4436 _4435 _4437).
Proof. exact (TRANS (@lem224247 _4436 _4434 _4435 _4437) (@lem224252 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224273 (_4436 : nat) (_4437 : nat) : (term597 _4436 _4437) = (term597 _4436 _4437).
Proof. exact (eq_refl (term597 _4436 _4437)). Qed.
Lemma lem224274 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : (term607 _4436 _4437 _4434 _4435) = (term603 _4434 _4436 _4435 _4437).
Proof. exact (MK_COMB (@lem224273 _4436 _4437) (@lem224272 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224285 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : ((term550 _4436 _4437 _4434 _4435) = (term607 _4436 _4437 _4434 _4435)) = ((term603 _4434 _4436 _4435 _4437) = (term603 _4434 _4436 _4435 _4437)).
Proof. exact (MK_COMB (@lem224211 _4434 _4436 _4435 _4437) (@lem224274 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224287 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem224288 (x : Prop) : (x = x) = True.
Proof. exact (@lem224287 Prop x). Qed.
Lemma lem224289 (_4434 : nat) (_4436 : nat) (_4435 : nat) (_4437 : nat) : ((term603 _4434 _4436 _4435 _4437) = (term603 _4434 _4436 _4435 _4437)) = True.
Proof. exact (@lem224288 (term603 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224290 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : ((term550 _4436 _4437 _4434 _4435) = (term607 _4436 _4437 _4434 _4435)) = True.
Proof. exact (TRANS (@lem224285 _4434 _4436 _4435 _4437) (@lem224289 _4434 _4436 _4435 _4437)). Qed.
Lemma lem224291 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : True = ((term550 _4436 _4437 _4434 _4435) = (term607 _4436 _4437 _4434 _4435)).
Proof. exact (SYM (@lem224290 _4436 _4437 _4434 _4435)). Qed.
Lemma lem224292 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term550 _4436 _4437 _4434 _4435) = (term607 _4436 _4437 _4434 _4435).
Proof. exact (EQ_MP (@lem224291 _4436 _4437 _4434 _4435) (@lem0)). Qed.
Lemma lem224293 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : term607 _4436 _4437 _4434 _4435.
Proof. exact (EQ_MP (@lem224292 _4436 _4437 _4434 _4435) (@lem223840 _4436 _4437 _4434 _4435)). Qed.
Lemma lem224295 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem224296 (_4434 : nat) (_4435 : nat) (_4436 : nat) (_4437 : nat) : (term607 _4436 _4437 _4434 _4435) = (term608 _4434 _4435 _4436 _4437).
Proof. exact (@lem224295 (term606 _4436 _4437 _4434 _4435) (Peano.le _4436 _4437)). Qed.
Lemma lem224298 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem224299 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term609 _4436 _4437 _4434 _4435) = (term610 _4436 _4437 _4434 _4435).
Proof. exact (@lem224298 (term64 _4434 _4436) (term595 _4437 _4434 _4435)). Qed.
Lemma lem224301 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224302 (_4434 : nat) (_4436 : nat) : (term170 _4434 _4436) = (_4434 = _4436).
Proof. exact (@lem224301 (_4434 = _4436)). Qed.
Lemma lem224303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem224304 (_4434 : nat) (_4436 : nat) : (term572 _4434 _4436) = (term573 _4434 _4436).
Proof. exact (MK_COMB (@lem224303) (@lem224302 _4434 _4436)). Qed.
Lemma lem224306 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem224307 (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term611 _4437 _4434 _4435) = (term612 _4437 _4434 _4435).
Proof. exact (@lem224306 (term64 _4435 _4437) (term162 _4434 _4435)). Qed.
Lemma lem224309 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224310 (_4435 : nat) (_4437 : nat) : (term170 _4435 _4437) = (_4435 = _4437).
Proof. exact (@lem224309 (_4435 = _4437)). Qed.
Lemma lem224311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem224312 (_4435 : nat) (_4437 : nat) : (term572 _4435 _4437) = (term573 _4435 _4437).
Proof. exact (MK_COMB (@lem224311) (@lem224310 _4435 _4437)). Qed.
Lemma lem224314 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224315 (_4434 : nat) (_4435 : nat) : (term180 _4434 _4435) = (Peano.le _4434 _4435).
Proof. exact (@lem224314 (Peano.le _4434 _4435)). Qed.
Lemma lem224316 (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term612 _4437 _4434 _4435) = (term613 _4437 _4434 _4435).
Proof. exact (MK_COMB (@lem224312 _4435 _4437) (@lem224315 _4434 _4435)). Qed.
Lemma lem224317 (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term611 _4437 _4434 _4435) = (term613 _4437 _4434 _4435).
Proof. exact (TRANS (@lem224307 _4437 _4434 _4435) (@lem224316 _4437 _4434 _4435)). Qed.
Lemma lem224318 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term610 _4436 _4437 _4434 _4435) = (term614 _4436 _4437 _4434 _4435).
Proof. exact (MK_COMB (@lem224304 _4434 _4436) (@lem224317 _4437 _4434 _4435)). Qed.
Lemma lem224319 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term609 _4436 _4437 _4434 _4435) = (term614 _4436 _4437 _4434 _4435).
Proof. exact (TRANS (@lem224299 _4436 _4437 _4434 _4435) (@lem224318 _4436 _4437 _4434 _4435)). Qed.
Lemma lem224320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem224321 (_4436 : nat) (_4437 : nat) (_4434 : nat) (_4435 : nat) : (term615 _4436 _4437 _4434 _4435) = (term616 _4436 _4437 _4434 _4435).
Proof. exact (MK_COMB (@lem224320) (@lem224319 _4436 _4437 _4434 _4435)). Qed.
Lemma lem224322 (_4436 : nat) (_4437 : nat) : (Peano.le _4436 _4437) = (Peano.le _4436 _4437).
Proof. exact (eq_refl (Peano.le _4436 _4437)). Qed.
Lemma lem224323 (_4434 : nat) (_4435 : nat) (_4436 : nat) (_4437 : nat) : (term608 _4434 _4435 _4436 _4437) = (term617 _4434 _4435 _4436 _4437).
Proof. exact (MK_COMB (@lem224321 _4436 _4437 _4434 _4435) (@lem224322 _4436 _4437)). Qed.
Lemma lem224324 (_4434 : nat) (_4435 : nat) (_4436 : nat) (_4437 : nat) : (term607 _4436 _4437 _4434 _4435) = (term617 _4434 _4435 _4436 _4437).
Proof. exact (TRANS (@lem224296 _4434 _4435 _4436 _4437) (@lem224323 _4434 _4435 _4436 _4437)). Qed.
Lemma lem224326 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term618 k m n p.
Proof. exact (conj (@lem224069 k p m n h2 h3) (@lem224100 k p m n h1 h4)). Qed.
Lemma lem224327 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term619 k m n p.
Proof. exact (conj (@lem223910 k m n p) (@lem224326 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224329 (_4434 : nat) (_4435 : nat) (_4436 : nat) (_4437 : nat) : term617 _4434 _4435 _4436 _4437.
Proof. exact (EQ_MP (@lem224324 _4434 _4435 _4436 _4437) (@lem224293 _4436 _4437 _4434 _4435)). Qed.
Lemma lem224330 (k : nat) (p : nat) (m : nat) (n : nat) : term620 k p m n.
Proof. exact (@lem224329 (term303 k m n p) (term554 m n p) (term303 k m n p) (Nat.div m n)). Qed.
Lemma lem224333 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term250 k p m n.
Proof. exact (@lem224330 k p m n (@lem224327 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224334 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term621 k p m n.
Proof. exact (fun h0 : term541 k p m n => @lem224333 k p m n h1 h2 h3 h4). Qed.
Lemma lem224336 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224337 (k : nat) (p : nat) (m : nat) (n : nat) : (term621 k p m n) = (term250 k p m n).
Proof. exact (@lem224336 (term250 k p m n)). Qed.
Lemma lem224338 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term250 k p m n.
Proof. exact (EQ_MP (@lem224337 k p m n) (@lem224334 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224341 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem224343 (k : nat) (p : nat) (m : nat) (n : nat) : (term541 k p m n) = (term622 k p m n).
Proof. exact (@lem224341 (term250 k p m n)). Qed.
Lemma lem224346 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term521 k p m n) : term622 k p m n.
Proof. exact (EQ_MP (@lem224343 k p m n) (@lem223778 k p m n h1)). Qed.
Lemma lem224349 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : False.
Proof. exact (@lem224346 k p m n h4 (@lem224338 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224350 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term205.
Proof. exact (fun h0 : ~ False => @lem224349 k p m n h1 h2 h3 h4). Qed.
Lemma lem224352 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224353 : term205 = False.
Proof. exact (@lem224352 False). Qed.
Lemma lem224354 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : False.
Proof. exact (EQ_MP (@lem224353) (@lem224350 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224374 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem224375 (_4458 : nat) (_4460 : nat) (h1 : _4458 = _4460) : _4458 = _4460.
Proof. exact (h1). Qed.
Lemma lem224376 (_4459 : nat) (_4461 : nat) (h1 : _4459 = _4461) : _4459 = _4461.
Proof. exact (h1). Qed.
Lemma lem224377 (_4458 : nat) (_4460 : nat) (h1 : _4458 = _4460) : (Peano.le _4458) = (Peano.le _4460).
Proof. exact (MK_COMB (@lem224374) (@lem224375 _4458 _4460 h1)). Qed.
Lemma lem224378 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) (h1 : _4458 = _4460) (h2 : _4459 = _4461) : (Peano.le _4458 _4459) = (Peano.le _4460 _4461).
Proof. exact (MK_COMB (@lem224377 _4458 _4460 h1) (@lem224376 _4459 _4461 h2)). Qed.
Lemma lem224380 (b : Prop) (a : Prop) : term543 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem224381 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : term544 _4460 _4461 _4458 _4459.
Proof. exact (@lem224380 (Peano.le _4460 _4461) (Peano.le _4458 _4459)). Qed.
Lemma lem224382 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) (h1 : _4458 = _4460) (h2 : _4459 = _4461) : term545 _4460 _4461 _4458 _4459.
Proof. exact (@lem224381 _4460 _4461 _4458 _4459 (@lem224378 _4458 _4460 _4459 _4461 h1 h2)). Qed.
Lemma lem224383 (_4461 : nat) (_4459 : nat) (_4458 : nat) (_4460 : nat) (h1 : _4458 = _4460) : term546 _4460 _4461 _4458 _4459.
Proof. exact (fun h0 : _4459 = _4461 => @lem224382 _4458 _4460 _4459 _4461 h1 h0). Qed.
Lemma lem224385 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem224386 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term546 _4460 _4461 _4458 _4459) = (term548 _4460 _4461 _4458 _4459).
Proof. exact (@lem224385 (_4459 = _4461) (term545 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224387 (_4461 : nat) (_4459 : nat) (_4458 : nat) (_4460 : nat) (h1 : _4458 = _4460) : term548 _4460 _4461 _4458 _4459.
Proof. exact (EQ_MP (@lem224386 _4460 _4461 _4458 _4459) (@lem224383 _4461 _4459 _4458 _4460 h1)). Qed.
Lemma lem224388 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : term549 _4460 _4461 _4458 _4459.
Proof. exact (fun h0 : _4458 = _4460 => @lem224387 _4461 _4459 _4458 _4460 h0). Qed.
Lemma lem224390 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem224391 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term549 _4460 _4461 _4458 _4459) = (term550 _4460 _4461 _4458 _4459).
Proof. exact (@lem224390 (_4458 = _4460) (term548 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224392 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : term550 _4460 _4461 _4458 _4459.
Proof. exact (EQ_MP (@lem224391 _4460 _4461 _4458 _4459) (@lem224388 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224456 (_4423 : nat) (_4422 : nat) (h1 : term364) : (Nat.add _4422 _4423) = (Nat.add _4423 _4422).
Proof. exact (EQ_MP (@lem223735 _4423 _4422) (@lem223734 _4422 _4423 h1)). Qed.
Lemma lem224457 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) : (term623 m n p k) = (term303 k m n p).
Proof. exact (@lem224456 k (term307 m n p) h1). Qed.
Lemma lem224458 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) : term624 k m n p.
Proof. exact (fun h0 : term625 k m n p => @lem224457 k m n p h1). Qed.
Lemma lem224460 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224461 (k : nat) (m : nat) (n : nat) (p : nat) : (term624 k m n p) = ((term623 m n p k) = (term303 k m n p)).
Proof. exact (@lem224460 ((term623 m n p k) = (term303 k m n p))). Qed.
Lemma lem224462 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) : (term623 m n p k) = (term303 k m n p).
Proof. exact (EQ_MP (@lem224461 k m n p) (@lem224458 k m n p h1)). Qed.
Lemma lem224464 (_4423 : nat) (_4422 : nat) (h1 : term364) : (Nat.add _4422 _4423) = (Nat.add _4423 _4422).
Proof. exact (EQ_MP (@lem223735 _4423 _4422) (@lem223734 _4422 _4423 h1)). Qed.
Lemma lem224465 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term328 m n p) = (term554 m n p).
Proof. exact (@lem224464 (term220 m n p) (term307 m n p) h1). Qed.
Lemma lem224466 (m : nat) (n : nat) (p : nat) (h1 : term364) : term555 m n p.
Proof. exact (fun h0 : term556 m n p => @lem224465 m n p h1). Qed.
Lemma lem224468 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224469 (m : nat) (n : nat) (p : nat) : (term555 m n p) = ((term328 m n p) = (term554 m n p)).
Proof. exact (@lem224468 ((term328 m n p) = (term554 m n p))). Qed.
Lemma lem224470 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term328 m n p) = (term554 m n p).
Proof. exact (EQ_MP (@lem224469 m n p) (@lem224466 m n p h1)). Qed.
Lemma lem224472 (_4423 : nat) (_4422 : nat) (h1 : term364) : (Nat.add _4422 _4423) = (Nat.add _4423 _4422).
Proof. exact (EQ_MP (@lem223735 _4423 _4422) (@lem223734 _4422 _4423 h1)). Qed.
Lemma lem224473 (m : nat) (n : nat) (p : nat) (k : nat) (h1 : term364) : (term303 k m n p) = (term623 m n p k).
Proof. exact (@lem224472 (term307 m n p) k h1). Qed.
Lemma lem224474 (m : nat) (n : nat) (p : nat) (k : nat) (h1 : term364) : term626 m n p k.
Proof. exact (fun h0 : term627 m n p k => @lem224473 m n p k h1). Qed.
Lemma lem224476 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224477 (m : nat) (n : nat) (p : nat) (k : nat) : (term626 m n p k) = ((term303 k m n p) = (term623 m n p k)).
Proof. exact (@lem224476 ((term303 k m n p) = (term623 m n p k))). Qed.
Lemma lem224478 (m : nat) (n : nat) (p : nat) (k : nat) (h1 : term364) : (term303 k m n p) = (term623 m n p k).
Proof. exact (EQ_MP (@lem224477 m n p k) (@lem224474 m n p k h1)). Qed.
Lemma lem224480 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (Nat.div m n) = (term328 m n p).
Proof. exact (proj1 (@lem223422 k p m n h1)). Qed.
Lemma lem224481 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term557 m n p.
Proof. exact (fun h0 : term558 m n p => @lem224480 k p m n h1). Qed.
Lemma lem224483 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224484 (m : nat) (n : nat) (p : nat) : (term557 m n p) = ((Nat.div m n) = (term328 m n p)).
Proof. exact (@lem224483 ((Nat.div m n) = (term328 m n p))). Qed.
Lemma lem224485 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (Nat.div m n) = (term328 m n p).
Proof. exact (EQ_MP (@lem224484 m n p) (@lem224481 k p m n h1)). Qed.
Lemma lem224487 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term522 k p m n) : term250 k p m n.
Proof. exact (proj2 (@lem223426 k p m n h1)). Qed.
Lemma lem224488 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term522 k p m n) : term621 k p m n.
Proof. exact (fun h0 : term541 k p m n => @lem224487 k p m n h1). Qed.
Lemma lem224490 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224491 (k : nat) (p : nat) (m : nat) (n : nat) : (term621 k p m n) = (term250 k p m n).
Proof. exact (@lem224490 (term250 k p m n)). Qed.
Lemma lem224492 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term522 k p m n) : term250 k p m n.
Proof. exact (EQ_MP (@lem224491 k p m n) (@lem224488 k p m n h1)). Qed.
Lemma lem224510 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224511 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term548 _4460 _4461 _4458 _4459) = (term594 _4460 _4461 _4458 _4459).
Proof. exact (@lem224510 (Peano.le _4460 _4461) (term64 _4459 _4461) (term162 _4458 _4459)). Qed.
Lemma lem224525 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem224526 (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term595 _4461 _4458 _4459) = (term596 _4458 _4459 _4461).
Proof. exact (@lem224525 (term162 _4458 _4459) (term64 _4459 _4461)). Qed.
Lemma lem224534 (_4460 : nat) (_4461 : nat) : (term597 _4460 _4461) = (term597 _4460 _4461).
Proof. exact (eq_refl (term597 _4460 _4461)). Qed.
Lemma lem224535 (_4460 : nat) (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term594 _4460 _4461 _4458 _4459) = (term598 _4460 _4458 _4459 _4461).
Proof. exact (MK_COMB (@lem224534 _4460 _4461) (@lem224526 _4458 _4459 _4461)). Qed.
Lemma lem224546 (_4460 : nat) (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term548 _4460 _4461 _4458 _4459) = (term598 _4460 _4458 _4459 _4461).
Proof. exact (TRANS (@lem224511 _4460 _4461 _4458 _4459) (@lem224535 _4460 _4458 _4459 _4461)). Qed.
Lemma lem224547 (_4458 : nat) (_4460 : nat) : (term563 _4458 _4460) = (term563 _4458 _4460).
Proof. exact (eq_refl (term563 _4458 _4460)). Qed.
Lemma lem224548 (_4460 : nat) (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term550 _4460 _4461 _4458 _4459) = (term599 _4460 _4458 _4459 _4461).
Proof. exact (MK_COMB (@lem224547 _4458 _4460) (@lem224546 _4460 _4458 _4459 _4461)). Qed.
Lemma lem224552 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224553 (_4460 : nat) (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term599 _4460 _4458 _4459 _4461) = (term600 _4460 _4458 _4459 _4461).
Proof. exact (@lem224552 (Peano.le _4460 _4461) (term64 _4458 _4460) (term596 _4458 _4459 _4461)). Qed.
Lemma lem224567 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224568 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term601 _4460 _4458 _4459 _4461) = (term602 _4458 _4460 _4459 _4461).
Proof. exact (@lem224567 (term162 _4458 _4459) (term64 _4458 _4460) (term64 _4459 _4461)). Qed.
Lemma lem224588 (_4460 : nat) (_4461 : nat) : (term597 _4460 _4461) = (term597 _4460 _4461).
Proof. exact (eq_refl (term597 _4460 _4461)). Qed.
Lemma lem224589 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term600 _4460 _4458 _4459 _4461) = (term603 _4458 _4460 _4459 _4461).
Proof. exact (MK_COMB (@lem224588 _4460 _4461) (@lem224568 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224600 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term599 _4460 _4458 _4459 _4461) = (term603 _4458 _4460 _4459 _4461).
Proof. exact (TRANS (@lem224553 _4460 _4458 _4459 _4461) (@lem224589 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224601 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term550 _4460 _4461 _4458 _4459) = (term603 _4458 _4460 _4459 _4461).
Proof. exact (TRANS (@lem224548 _4460 _4458 _4459 _4461) (@lem224600 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem224603 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term604 _4460 _4461 _4458 _4459) = (term605 _4458 _4460 _4459 _4461).
Proof. exact (MK_COMB (@lem224602) (@lem224601 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224629 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem224630 (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term595 _4461 _4458 _4459) = (term596 _4458 _4459 _4461).
Proof. exact (@lem224629 (term162 _4458 _4459) (term64 _4459 _4461)). Qed.
Lemma lem224638 (_4458 : nat) (_4460 : nat) : (term563 _4458 _4460) = (term563 _4458 _4460).
Proof. exact (eq_refl (term563 _4458 _4460)). Qed.
Lemma lem224639 (_4460 : nat) (_4458 : nat) (_4459 : nat) (_4461 : nat) : (term606 _4460 _4461 _4458 _4459) = (term601 _4460 _4458 _4459 _4461).
Proof. exact (MK_COMB (@lem224638 _4458 _4460) (@lem224630 _4458 _4459 _4461)). Qed.
Lemma lem224643 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem224644 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term601 _4460 _4458 _4459 _4461) = (term602 _4458 _4460 _4459 _4461).
Proof. exact (@lem224643 (term162 _4458 _4459) (term64 _4458 _4460) (term64 _4459 _4461)). Qed.
Lemma lem224664 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term606 _4460 _4461 _4458 _4459) = (term602 _4458 _4460 _4459 _4461).
Proof. exact (TRANS (@lem224639 _4460 _4458 _4459 _4461) (@lem224644 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224665 (_4460 : nat) (_4461 : nat) : (term597 _4460 _4461) = (term597 _4460 _4461).
Proof. exact (eq_refl (term597 _4460 _4461)). Qed.
Lemma lem224666 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : (term607 _4460 _4461 _4458 _4459) = (term603 _4458 _4460 _4459 _4461).
Proof. exact (MK_COMB (@lem224665 _4460 _4461) (@lem224664 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224677 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : ((term550 _4460 _4461 _4458 _4459) = (term607 _4460 _4461 _4458 _4459)) = ((term603 _4458 _4460 _4459 _4461) = (term603 _4458 _4460 _4459 _4461)).
Proof. exact (MK_COMB (@lem224603 _4458 _4460 _4459 _4461) (@lem224666 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224679 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem224680 (x : Prop) : (x = x) = True.
Proof. exact (@lem224679 Prop x). Qed.
Lemma lem224681 (_4458 : nat) (_4460 : nat) (_4459 : nat) (_4461 : nat) : ((term603 _4458 _4460 _4459 _4461) = (term603 _4458 _4460 _4459 _4461)) = True.
Proof. exact (@lem224680 (term603 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224682 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : ((term550 _4460 _4461 _4458 _4459) = (term607 _4460 _4461 _4458 _4459)) = True.
Proof. exact (TRANS (@lem224677 _4458 _4460 _4459 _4461) (@lem224681 _4458 _4460 _4459 _4461)). Qed.
Lemma lem224683 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : True = ((term550 _4460 _4461 _4458 _4459) = (term607 _4460 _4461 _4458 _4459)).
Proof. exact (SYM (@lem224682 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224684 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term550 _4460 _4461 _4458 _4459) = (term607 _4460 _4461 _4458 _4459).
Proof. exact (EQ_MP (@lem224683 _4460 _4461 _4458 _4459) (@lem0)). Qed.
Lemma lem224685 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : term607 _4460 _4461 _4458 _4459.
Proof. exact (EQ_MP (@lem224684 _4460 _4461 _4458 _4459) (@lem224392 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224687 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem224688 (_4458 : nat) (_4459 : nat) (_4460 : nat) (_4461 : nat) : (term607 _4460 _4461 _4458 _4459) = (term608 _4458 _4459 _4460 _4461).
Proof. exact (@lem224687 (term606 _4460 _4461 _4458 _4459) (Peano.le _4460 _4461)). Qed.
Lemma lem224690 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem224691 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term609 _4460 _4461 _4458 _4459) = (term610 _4460 _4461 _4458 _4459).
Proof. exact (@lem224690 (term64 _4458 _4460) (term595 _4461 _4458 _4459)). Qed.
Lemma lem224693 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224694 (_4458 : nat) (_4460 : nat) : (term170 _4458 _4460) = (_4458 = _4460).
Proof. exact (@lem224693 (_4458 = _4460)). Qed.
Lemma lem224695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem224696 (_4458 : nat) (_4460 : nat) : (term572 _4458 _4460) = (term573 _4458 _4460).
Proof. exact (MK_COMB (@lem224695) (@lem224694 _4458 _4460)). Qed.
Lemma lem224698 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem224699 (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term611 _4461 _4458 _4459) = (term612 _4461 _4458 _4459).
Proof. exact (@lem224698 (term64 _4459 _4461) (term162 _4458 _4459)). Qed.
Lemma lem224701 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224702 (_4459 : nat) (_4461 : nat) : (term170 _4459 _4461) = (_4459 = _4461).
Proof. exact (@lem224701 (_4459 = _4461)). Qed.
Lemma lem224703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem224704 (_4459 : nat) (_4461 : nat) : (term572 _4459 _4461) = (term573 _4459 _4461).
Proof. exact (MK_COMB (@lem224703) (@lem224702 _4459 _4461)). Qed.
Lemma lem224706 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224707 (_4458 : nat) (_4459 : nat) : (term180 _4458 _4459) = (Peano.le _4458 _4459).
Proof. exact (@lem224706 (Peano.le _4458 _4459)). Qed.
Lemma lem224708 (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term612 _4461 _4458 _4459) = (term613 _4461 _4458 _4459).
Proof. exact (MK_COMB (@lem224704 _4459 _4461) (@lem224707 _4458 _4459)). Qed.
Lemma lem224709 (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term611 _4461 _4458 _4459) = (term613 _4461 _4458 _4459).
Proof. exact (TRANS (@lem224699 _4461 _4458 _4459) (@lem224708 _4461 _4458 _4459)). Qed.
Lemma lem224710 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term610 _4460 _4461 _4458 _4459) = (term614 _4460 _4461 _4458 _4459).
Proof. exact (MK_COMB (@lem224696 _4458 _4460) (@lem224709 _4461 _4458 _4459)). Qed.
Lemma lem224711 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term609 _4460 _4461 _4458 _4459) = (term614 _4460 _4461 _4458 _4459).
Proof. exact (TRANS (@lem224691 _4460 _4461 _4458 _4459) (@lem224710 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem224713 (_4460 : nat) (_4461 : nat) (_4458 : nat) (_4459 : nat) : (term615 _4460 _4461 _4458 _4459) = (term616 _4460 _4461 _4458 _4459).
Proof. exact (MK_COMB (@lem224712) (@lem224711 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224714 (_4460 : nat) (_4461 : nat) : (Peano.le _4460 _4461) = (Peano.le _4460 _4461).
Proof. exact (eq_refl (Peano.le _4460 _4461)). Qed.
Lemma lem224715 (_4458 : nat) (_4459 : nat) (_4460 : nat) (_4461 : nat) : (term608 _4458 _4459 _4460 _4461) = (term617 _4458 _4459 _4460 _4461).
Proof. exact (MK_COMB (@lem224713 _4460 _4461 _4458 _4459) (@lem224714 _4460 _4461)). Qed.
Lemma lem224716 (_4458 : nat) (_4459 : nat) (_4460 : nat) (_4461 : nat) : (term607 _4460 _4461 _4458 _4459) = (term617 _4458 _4459 _4460 _4461).
Proof. exact (TRANS (@lem224688 _4458 _4459 _4460 _4461) (@lem224715 _4458 _4459 _4460 _4461)). Qed.
Lemma lem224718 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) (h2 : term522 k p m n) : term628 k p m n.
Proof. exact (conj (@lem224485 k p m n h1) (@lem224492 k p m n h2)). Qed.
Lemma lem224719 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term629 k p m n.
Proof. exact (conj (@lem224478 m n p k h1) (@lem224718 k p m n h2 h3)). Qed.
Lemma lem224721 (_4458 : nat) (_4459 : nat) (_4460 : nat) (_4461 : nat) : term617 _4458 _4459 _4460 _4461.
Proof. exact (EQ_MP (@lem224716 _4458 _4459 _4460 _4461) (@lem224685 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224722 (k : nat) (m : nat) (n : nat) (p : nat) : term630 k m n p.
Proof. exact (@lem224721 (term303 k m n p) (Nat.div m n) (term623 m n p k) (term328 m n p)). Qed.
Lemma lem224725 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term631 k m n p.
Proof. exact (@lem224722 k m n p (@lem224719 k p m n h1 h2 h3)). Qed.
Lemma lem224726 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term632 k m n p.
Proof. exact (fun h0 : term633 k m n p => @lem224725 k p m n h1 h2 h3). Qed.
Lemma lem224728 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224729 (k : nat) (m : nat) (n : nat) (p : nat) : (term632 k m n p) = (term631 k m n p).
Proof. exact (@lem224728 (term631 k m n p)). Qed.
Lemma lem224730 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term631 k m n p.
Proof. exact (EQ_MP (@lem224729 k m n p) (@lem224726 k p m n h1 h2 h3)). Qed.
Lemma lem224731 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term634 k m n p.
Proof. exact (conj (@lem224470 m n p h1) (@lem224730 k p m n h1 h2 h3)). Qed.
Lemma lem224732 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term635 k m n p.
Proof. exact (conj (@lem224462 k m n p h1) (@lem224731 k p m n h1 h2 h3)). Qed.
Lemma lem224734 (_4458 : nat) (_4459 : nat) (_4460 : nat) (_4461 : nat) : term617 _4458 _4459 _4460 _4461.
Proof. exact (EQ_MP (@lem224716 _4458 _4459 _4460 _4461) (@lem224685 _4460 _4461 _4458 _4459)). Qed.
Lemma lem224735 (k : nat) (m : nat) (n : nat) (p : nat) : term636 k m n p.
Proof. exact (@lem224734 (term623 m n p k) (term328 m n p) (term303 k m n p) (term554 m n p)). Qed.
Lemma lem224738 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term591 k m n p.
Proof. exact (@lem224735 k m n p (@lem224732 k p m n h1 h2 h3)). Qed.
Lemma lem224739 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term592 k m n p.
Proof. exact (fun h0 : term593 k m n p => @lem224738 k p m n h1 h2 h3). Qed.
Lemma lem224741 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224742 (k : nat) (m : nat) (n : nat) (p : nat) : (term592 k m n p) = (term591 k m n p).
Proof. exact (@lem224741 (term591 k m n p)). Qed.
Lemma lem224743 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term364) (h2 : term357 k p m n) (h3 : term522 k p m n) : term591 k m n p.
Proof. exact (EQ_MP (@lem224742 k m n p) (@lem224739 k p m n h1 h2 h3)). Qed.
Lemma lem224749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem224750 (_4427 : nat) (_4428 : nat) (_4429 : nat) : (term424 _4429 _4427 _4428) = (term637 _4427 _4428 _4429).
Proof. exact (@lem224749 (Peano.le _4427 _4428) (term463 _4427 _4428 _4429)). Qed.
Lemma lem224756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem224757 (_4427 : nat) (_4428 : nat) (_4429 : nat) : (term638 _4429 _4427 _4428) = (term639 _4427 _4428 _4429).
Proof. exact (MK_COMB (@lem224756) (@lem224750 _4427 _4428 _4429)). Qed.
Lemma lem224763 (_4427 : nat) (_4428 : nat) (_4429 : nat) : (term637 _4427 _4428 _4429) = (term637 _4427 _4428 _4429).
Proof. exact (eq_refl (term637 _4427 _4428 _4429)). Qed.
Lemma lem224764 (_4427 : nat) (_4428 : nat) (_4429 : nat) : ((term424 _4429 _4427 _4428) = (term637 _4427 _4428 _4429)) = ((term637 _4427 _4428 _4429) = (term637 _4427 _4428 _4429)).
Proof. exact (MK_COMB (@lem224757 _4427 _4428 _4429) (@lem224763 _4427 _4428 _4429)). Qed.
Lemma lem224766 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem224767 (x : Prop) : (x = x) = True.
Proof. exact (@lem224766 Prop x). Qed.
Lemma lem224768 (_4427 : nat) (_4428 : nat) (_4429 : nat) : ((term637 _4427 _4428 _4429) = (term637 _4427 _4428 _4429)) = True.
Proof. exact (@lem224767 (term637 _4427 _4428 _4429)). Qed.
Lemma lem224769 (_4427 : nat) (_4428 : nat) (_4429 : nat) : ((term424 _4429 _4427 _4428) = (term637 _4427 _4428 _4429)) = True.
Proof. exact (TRANS (@lem224764 _4427 _4428 _4429) (@lem224768 _4427 _4428 _4429)). Qed.
Lemma lem224770 (_4427 : nat) (_4428 : nat) (_4429 : nat) : True = ((term424 _4429 _4427 _4428) = (term637 _4427 _4428 _4429)).
Proof. exact (SYM (@lem224769 _4427 _4428 _4429)). Qed.
Lemma lem224771 (_4427 : nat) (_4428 : nat) (_4429 : nat) : (term424 _4429 _4427 _4428) = (term637 _4427 _4428 _4429).
Proof. exact (EQ_MP (@lem224770 _4427 _4428 _4429) (@lem0)). Qed.
Lemma lem224772 (_4427 : nat) (_4428 : nat) (_4429 : nat) (h1 : term402) : term637 _4427 _4428 _4429.
Proof. exact (EQ_MP (@lem224771 _4427 _4428 _4429) (@lem223794 _4429 _4427 _4428 h1)). Qed.
Lemma lem224774 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem224775 (_4429 : nat) (_4427 : nat) (_4428 : nat) : (term637 _4427 _4428 _4429) = (term640 _4429 _4427 _4428).
Proof. exact (@lem224774 (term463 _4427 _4428 _4429) (Peano.le _4427 _4428)). Qed.
Lemma lem224777 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem224778 (_4427 : nat) (_4428 : nat) (_4429 : nat) : (term641 _4427 _4428 _4429) = (term396 _4427 _4428 _4429).
Proof. exact (@lem224777 (term396 _4427 _4428 _4429)). Qed.
Lemma lem224779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem224780 (_4427 : nat) (_4428 : nat) (_4429 : nat) : (term642 _4427 _4428 _4429) = (term643 _4427 _4428 _4429).
Proof. exact (MK_COMB (@lem224779) (@lem224778 _4427 _4428 _4429)). Qed.
Lemma lem224781 (_4427 : nat) (_4428 : nat) : (Peano.le _4427 _4428) = (Peano.le _4427 _4428).
Proof. exact (eq_refl (Peano.le _4427 _4428)). Qed.
Lemma lem224782 (_4429 : nat) (_4427 : nat) (_4428 : nat) : (term640 _4429 _4427 _4428) = (term644 _4429 _4427 _4428).
Proof. exact (MK_COMB (@lem224780 _4427 _4428 _4429) (@lem224781 _4427 _4428)). Qed.
Lemma lem224783 (_4429 : nat) (_4427 : nat) (_4428 : nat) : (term637 _4427 _4428 _4429) = (term644 _4429 _4427 _4428).
Proof. exact (TRANS (@lem224775 _4429 _4427 _4428) (@lem224782 _4429 _4427 _4428)). Qed.
Lemma lem224786 (_4429 : nat) (_4427 : nat) (_4428 : nat) (h1 : term402) : term644 _4429 _4427 _4428.
Proof. exact (EQ_MP (@lem224783 _4429 _4427 _4428) (@lem224772 _4427 _4428 _4429 h1)). Qed.
Lemma lem224787 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) : term645 k m n p.
Proof. exact (@lem224786 (term307 m n p) k (term220 m n p) h1). Qed.
Lemma lem224790 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : term242 k m n p.
Proof. exact (@lem224787 k m n p h1 (@lem224743 k p m n h2 h3 h4)). Qed.
Lemma lem224791 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : term586 k m n p.
Proof. exact (fun h0 : term542 k m n p => @lem224790 k p m n h1 h2 h3 h4). Qed.
Lemma lem224793 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224794 (k : nat) (m : nat) (n : nat) (p : nat) : (term586 k m n p) = (term242 k m n p).
Proof. exact (@lem224793 (term242 k m n p)). Qed.
Lemma lem224795 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : term242 k m n p.
Proof. exact (EQ_MP (@lem224794 k m n p) (@lem224791 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224798 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem224800 (k : nat) (m : nat) (n : nat) (p : nat) : (term542 k m n p) = (term646 k m n p).
Proof. exact (@lem224798 (term242 k m n p)). Qed.
Lemma lem224803 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term522 k p m n) : term646 k m n p.
Proof. exact (EQ_MP (@lem224800 k m n p) (@lem223800 k p m n h1)). Qed.
Lemma lem224806 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : False.
Proof. exact (@lem224803 k p m n h4 (@lem224795 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224807 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : term205.
Proof. exact (fun h0 : ~ False => @lem224806 k p m n h1 h2 h3 h4). Qed.
Lemma lem224809 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem224810 : term205 = False.
Proof. exact (@lem224809 False). Qed.
Lemma lem224811 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : False.
Proof. exact (EQ_MP (@lem224810) (@lem224807 k p m n h1 h2 h3 h4)). Qed.
Lemma lem224812 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : term364 = False.
Proof. exact (prop_ext (fun h5 : term364 => @lem224811 k p m n h1 h2 h3 h4) (fun h5 : False => @lem223582 h2)). Qed.
Lemma lem224813 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term522 k p m n) : False.
Proof. exact (EQ_MP (@lem224812 k p m n h1 h2 h3 h4) (@lem223582 h2)). Qed.
Lemma lem224814 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : term364 = False.
Proof. exact (prop_ext (fun h5 : term364 => @lem224354 k p m n h1 h2 h3 h4) (fun h5 : False => @lem223450 h2)). Qed.
Lemma lem224815 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) (h4 : term521 k p m n) : False.
Proof. exact (EQ_MP (@lem224814 k p m n h1 h2 h3 h4) (@lem223450 h2)). Qed.
Lemma lem224816 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) : False.
Proof. exact (or_elim (@lem223421 k p m n h3) (fun h0 : term521 k p m n => @lem224815 k p m n h1 h2 h3 h0) (fun h0 : term522 k p m n => @lem224813 k p m n h1 h2 h3 h0)). Qed.
Lemma lem224817 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) : term364 = False.
Proof. exact (prop_ext (fun h4 : term364 => @lem224816 k p m n h1 h2 h3) (fun h4 : False => @lem223418 h2)). Qed.
Lemma lem224818 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) : False.
Proof. exact (EQ_MP (@lem224817 k p m n h1 h2 h3) (@lem223418 h2)). Qed.
Lemma lem224819 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) : term364 = False.
Proof. exact (prop_ext (fun h4 : term364 => @lem224818 k p m n h1 h2 h3) (fun h4 : False => @lem223168 h2)). Qed.
Lemma lem224820 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term364) (h3 : term357 k p m n) : False.
Proof. exact (EQ_MP (@lem224819 k p m n h1 h2 h3) (@lem223168 h2)). Qed.
Lemma lem224821 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term357 k p m n) : term362.
Proof. exact (fun h0 : term364 => @lem224820 k p m n h1 h0 h2). Qed.
Lemma lem224822 : term362 = term363.
Proof. exact (@lem69 term364). Qed.
Lemma lem224823 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term357 k p m n) : term363.
Proof. exact (EQ_MP (@lem224822) (@lem224821 k p m n h1 h2)). Qed.
Lemma lem224824 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term402) (h2 : term357 k p m n) : term367.
Proof. exact (fun h0 : term395 => @lem224823 k p m n h1 h2). Qed.
Lemma lem224825 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term370.
Proof. exact (fun h0 : term402 => @lem224824 k p m n h0 h1). Qed.
Lemma lem224826 (k : nat) (p : nat) (m : nat) (n : nat) : term372 k p m n.
Proof. exact (fun h0 : term357 k p m n => @lem224825 k p m n h0). Qed.
Lemma lem224831 (p : nat) (m : nat) (n : nat) : term376 p m n.
Proof. exact (fun k : nat => @lem224826 k p m n). Qed.
Lemma lem224836 (m : nat) (n : nat) : term380 m n.
Proof. exact (fun p : nat => @lem224831 p m n). Qed.
Lemma lem224841 (n : nat) : term384 n.
Proof. exact (fun m : nat => @lem224836 m n). Qed.
Lemma lem224846 : term388.
Proof. exact (fun n : nat => @lem224841 n). Qed.
Lemma lem224847 : term387.
Proof. exact (EQ_MP (@lem222653) (@lem224846)). Qed.
Lemma lem224848 (n : nat) : term647 n.
Proof. exact (@lem224847 n). Qed.
Lemma lem224849 (n : nat) : (term647 n) = (term383 n).
Proof. exact (eq_refl (term647 n)). Qed.
Lemma lem224850 (n : nat) : term383 n.
Proof. exact (EQ_MP (@lem224849 n) (@lem224848 n)). Qed.
Lemma lem224851 (n : nat) (m : nat) : term648 n m.
Proof. exact (@lem224850 n m). Qed.
Lemma lem224852 (m : nat) (n : nat) : (term648 n m) = (term379 m n).
Proof. exact (eq_refl (term648 n m)). Qed.
Lemma lem224853 (m : nat) (n : nat) : term379 m n.
Proof. exact (EQ_MP (@lem224852 m n) (@lem224851 n m)). Qed.
Lemma lem224854 (m : nat) (n : nat) (p : nat) : term649 m n p.
Proof. exact (@lem224853 m n p). Qed.
Lemma lem224855 (p : nat) (m : nat) (n : nat) : (term649 m n p) = (term375 p m n).
Proof. exact (eq_refl (term649 m n p)). Qed.
Lemma lem224856 (p : nat) (m : nat) (n : nat) : term375 p m n.
Proof. exact (EQ_MP (@lem224855 p m n) (@lem224854 m n p)). Qed.
Lemma lem224857 (p : nat) (m : nat) (n : nat) (k : nat) : term650 p m n k.
Proof. exact (@lem224856 p m n k). Qed.
Lemma lem224858 (k : nat) (p : nat) (m : nat) (n : nat) : (term650 p m n k) = (term358 k p m n).
Proof. exact (eq_refl (term650 p m n k)). Qed.
Lemma lem224859 (k : nat) (p : nat) (m : nat) (n : nat) : term358 k p m n.
Proof. exact (EQ_MP (@lem224858 k p m n) (@lem224857 p m n k)). Qed.
Lemma lem224861 (k : nat) (p : nat) (m : nat) (n : nat) : term358 k p m n.
Proof. exact (@lem222406 k p m n (@lem224859 k p m n)). Qed.
Lemma lem224862 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term369.
Proof. exact (@lem224861 k p m n (@lem222391 k p m n h1)). Qed.
Lemma lem224863 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term366.
Proof. exact (@lem224862 k p m n h1 (@lem100973)). Qed.
Lemma lem224864 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : term362.
Proof. exact (@lem224863 k p m n h1 (@lem81820)). Qed.
Lemma lem224865 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : False.
Proof. exact (@lem224864 k p m n h1 (@lem77775)). Qed.
Lemma lem224866 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : (term357 k p m n) = False.
Proof. exact (prop_ext (fun h2 : term357 k p m n => @lem224865 k p m n h1) (fun h2 : False => @lem222391 k p m n h1)). Qed.
Lemma lem224867 (k : nat) (p : nat) (m : nat) (n : nat) (h1 : term357 k p m n) : False.
Proof. exact (EQ_MP (@lem224866 k p m n h1) (@lem222391 k p m n h1)). Qed.
Lemma lem224868 (k : nat) (p : nat) (m : nat) (n : nat) : term356 k p m n.
Proof. exact (fun h0 : term357 k p m n => @lem224867 k p m n h0). Qed.
Lemma lem224869 (k : nat) (p : nat) (m : nat) (n : nat) : term334 k p m n.
Proof. exact (EQ_MP (@lem222390 k p m n) (@lem224868 k p m n)). Qed.
Lemma lem224871 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem224872 (k : nat) (m : nat) (n : nat) (p : nat) : (term355 k m n p) = (term651 k m n p).
Proof. exact (@lem224871 (term355 k m n p)). Qed.
Lemma lem224873 (k : nat) (m : nat) (n : nat) (p : nat) : (term651 k m n p) = (term355 k m n p).
Proof. exact (SYM (@lem224872 k m n p)). Qed.
Lemma lem224874 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term652 k m n p.
Proof. exact (h1). Qed.
Lemma lem224877 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term653 k m n p) : term653 k m n p.
Proof. exact (h1). Qed.
Lemma lem224878 (k : nat) (m : nat) (n : nat) (p : nat) : term654 k m n p.
Proof. exact (fun h0 : term653 k m n p => @lem224877 k m n p h0). Qed.
Lemma lem224879 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term654 k m n p) : term654 k m n p.
Proof. exact (h1). Qed.
Lemma lem224880 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term653 k m n p) : term653 k m n p.
Proof. exact (h1). Qed.
Lemma lem224881 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term653 k m n p) (h2 : term654 k m n p) : term653 k m n p.
Proof. exact (@lem224879 k m n p h2 (@lem224880 k m n p h1)). Qed.
Lemma lem224882 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term653 k m n p) : term655 k m n p.
Proof. exact (fun h0 : term654 k m n p => @lem224881 k m n p h1 h0). Qed.
Lemma lem224883 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term654 k m n p) : term654 k m n p.
Proof. exact (h1). Qed.
Lemma lem224884 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term653 k m n p) (h2 : term654 k m n p) : term653 k m n p.
Proof. exact (@lem224882 k m n p h1 (@lem224883 k m n p h2)). Qed.
Lemma lem224885 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term654 k m n p) : term654 k m n p.
Proof. exact (fun h0 : term653 k m n p => @lem224884 k m n p h0 h1). Qed.
Lemma lem224886 (k : nat) (m : nat) (n : nat) (p : nat) : term656 k m n p.
Proof. exact (fun h0 : term654 k m n p => @lem224885 k m n p h0). Qed.
Lemma lem224889 (k : nat) (m : nat) (n : nat) (p : nat) : term654 k m n p.
Proof. exact (@lem224886 k m n p (@lem224878 k m n p)). Qed.
Lemma lem224937 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem224938 : term362 = term363.
Proof. exact (@lem224937 term364). Qed.
Lemma lem224947 : term365 = term365.
Proof. exact (eq_refl term365). Qed.
Lemma lem224948 : term366 = term367.
Proof. exact (MK_COMB (@lem224947) (@lem224938)). Qed.
Lemma lem224951 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem224952 : term369 = term370.
Proof. exact (MK_COMB (@lem224951) (@lem224948)). Qed.
Lemma lem224955 (k : nat) (m : nat) (n : nat) (p : nat) : (term657 k m n p) = (term657 k m n p).
Proof. exact (eq_refl (term657 k m n p)). Qed.
Lemma lem224956 (k : nat) (m : nat) (n : nat) (p : nat) : (term653 k m n p) = (term658 k m n p).
Proof. exact (MK_COMB (@lem224955 k m n p) (@lem224952)). Qed.
Lemma lem224959 (m : nat) (n : nat) (p : nat) : (term659 m n p) = (term660 m n p).
Proof. exact (fun_ext (fun k : nat => @lem224956 k m n p)). Qed.
Lemma lem224960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem224961 (m : nat) (n : nat) (p : nat) : (term661 m n p) = (term662 m n p).
Proof. exact (MK_COMB (@lem224960) (@lem224959 m n p)). Qed.
Lemma lem224966 (n : nat) (p : nat) : (term663 n p) = (term664 n p).
Proof. exact (fun_ext (fun m : nat => @lem224961 m n p)). Qed.
Lemma lem224967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem224968 (n : nat) (p : nat) : (term665 n p) = (term666 n p).
Proof. exact (MK_COMB (@lem224967) (@lem224966 n p)). Qed.
Lemma lem224973 (p : nat) : (term667 p) = (term668 p).
Proof. exact (fun_ext (fun n : nat => @lem224968 n p)). Qed.
Lemma lem224974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem224975 (p : nat) : (term669 p) = (term670 p).
Proof. exact (MK_COMB (@lem224974) (@lem224973 p)). Qed.
Lemma lem224980 : term671 = term672.
Proof. exact (fun_ext (fun p : nat => @lem224975 p)). Qed.
Lemma lem224981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem224990 : term673 = term674.
Proof. exact (MK_COMB (@lem224981) (@lem224980)). Qed.
Lemma lem224991 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem224992 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem224991 n m)). Qed.
Lemma lem224993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem224994 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem224993) (@lem224992 m)). Qed.
Lemma lem224995 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem224994 m)). Qed.
Lemma lem224996 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem224997 : term364 = term364.
Proof. exact (MK_COMB (@lem224996) (@lem224995)). Qed.
Lemma lem224998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem224999 : term363 = term363.
Proof. exact (MK_COMB (@lem224998) (@lem224997)). Qed.
Lemma lem225000 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem225001 (m : nat) : (term392 m) = (term392 m).
Proof. exact (fun_ext (fun n : nat => @lem225000 n m)). Qed.
Lemma lem225002 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225003 (m : nat) : (term393 m) = (term393 m).
Proof. exact (MK_COMB (@lem225002) (@lem225001 m)). Qed.
Lemma lem225004 : term394 = term394.
Proof. exact (fun_ext (fun m : nat => @lem225003 m)). Qed.
Lemma lem225005 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225006 : term395 = term395.
Proof. exact (MK_COMB (@lem225005) (@lem225004)). Qed.
Lemma lem225007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem225008 : term365 = term365.
Proof. exact (MK_COMB (@lem225007) (@lem225006)). Qed.
Lemma lem225009 : term367 = term367.
Proof. exact (MK_COMB (@lem225008) (@lem224999)). Qed.
Lemma lem225014 (p : nat) (m : nat) (n : nat) : ((term396 m n p) = (Peano.le m n)) = ((term396 m n p) = (Peano.le m n)).
Proof. exact (eq_refl ((term396 m n p) = (Peano.le m n))). Qed.
Lemma lem225015 (m : nat) (n : nat) : (term397 m n) = (term397 m n).
Proof. exact (fun_ext (fun p : nat => @lem225014 p m n)). Qed.
Lemma lem225016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225017 (m : nat) (n : nat) : (term398 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem225016) (@lem225015 m n)). Qed.
Lemma lem225018 (m : nat) : (term399 m) = (term399 m).
Proof. exact (fun_ext (fun n : nat => @lem225017 m n)). Qed.
Lemma lem225019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225020 (m : nat) : (term400 m) = (term400 m).
Proof. exact (MK_COMB (@lem225019) (@lem225018 m)). Qed.
Lemma lem225021 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem225020 m)). Qed.
Lemma lem225022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225023 : term402 = term402.
Proof. exact (MK_COMB (@lem225022) (@lem225021)). Qed.
Lemma lem225024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem225025 : term368 = term368.
Proof. exact (MK_COMB (@lem225024) (@lem225023)). Qed.
Lemma lem225026 : term370 = term370.
Proof. exact (MK_COMB (@lem225025) (@lem225009)). Qed.
Lemma lem225043 (k : nat) (m : nat) (n : nat) (p : nat) : (term657 k m n p) = (term657 k m n p).
Proof. exact (eq_refl (term657 k m n p)). Qed.
Lemma lem225044 (k : nat) (m : nat) (n : nat) (p : nat) : (term658 k m n p) = (term658 k m n p).
Proof. exact (MK_COMB (@lem225043 k m n p) (@lem225026)). Qed.
Lemma lem225045 (m : nat) (n : nat) (p : nat) : (term660 m n p) = (term660 m n p).
Proof. exact (fun_ext (fun k : nat => @lem225044 k m n p)). Qed.
Lemma lem225046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225047 (m : nat) (n : nat) (p : nat) : (term662 m n p) = (term662 m n p).
Proof. exact (MK_COMB (@lem225046) (@lem225045 m n p)). Qed.
Lemma lem225048 (n : nat) (p : nat) : (term664 n p) = (term664 n p).
Proof. exact (fun_ext (fun m : nat => @lem225047 m n p)). Qed.
Lemma lem225049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225050 (n : nat) (p : nat) : (term666 n p) = (term666 n p).
Proof. exact (MK_COMB (@lem225049) (@lem225048 n p)). Qed.
Lemma lem225051 (p : nat) : (term668 p) = (term668 p).
Proof. exact (fun_ext (fun n : nat => @lem225050 n p)). Qed.
Lemma lem225052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225053 (p : nat) : (term670 p) = (term670 p).
Proof. exact (MK_COMB (@lem225052) (@lem225051 p)). Qed.
Lemma lem225054 : term672 = term672.
Proof. exact (fun_ext (fun p : nat => @lem225053 p)). Qed.
Lemma lem225055 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225056 : term674 = term674.
Proof. exact (MK_COMB (@lem225055) (@lem225054)). Qed.
Lemma lem225135 : term673 = term674.
Proof. exact (TRANS (@lem224990) (@lem225056)). Qed.
Lemma lem225136 : term674 = term673.
Proof. exact (SYM (@lem225135)). Qed.
Lemma lem225137 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term652 k m n p.
Proof. exact (h1). Qed.
Lemma lem225138 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem225140 (h1 : term364) : term364.
Proof. exact (h1). Qed.
Lemma lem225160 (k : nat) (m : nat) (n : nat) (p : nat) : (term675 k m n p) = (term676 k m n p).
Proof. exact (@lem17646 (term351 k n p m) (term354 k m n p)). Qed.
Lemma lem225162 (m : nat) (n : nat) (p : nat) : (term677 m n p) = (term677 m n p).
Proof. exact (eq_refl (term677 m n p)). Qed.
Lemma lem225163 (k : nat) (m : nat) (n : nat) (p : nat) : (term678 k m n p) = (term679 k m n p).
Proof. exact (MK_COMB (@lem225162 m n p) (@lem225160 k m n p)). Qed.
Lemma lem225164 (k : nat) (m : nat) (n : nat) (p : nat) : (term652 k m n p) = (term678 k m n p).
Proof. exact (@lem17362 (term346 m n p) ((term351 k n p m) = (term354 k m n p))). Qed.
Lemma lem225169 (k : nat) (m : nat) (n : nat) (p : nat) : (term652 k m n p) = (term679 k m n p).
Proof. exact (TRANS (@lem225164 k m n p) (@lem225163 k m n p)). Qed.
Lemma lem225185 (p : nat) (m : nat) (n : nat) : ((term396 m n p) = (Peano.le m n)) = (term408 p m n).
Proof. exact (@lem17784 (term396 m n p) (Peano.le m n)). Qed.
Lemma lem225186 (m : nat) (n : nat) : (term397 m n) = (term409 m n).
Proof. exact (fun_ext (fun p : nat => @lem225185 p m n)). Qed.
Lemma lem225187 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225188 (m : nat) (n : nat) : (term398 m n) = (term410 m n).
Proof. exact (MK_COMB (@lem225187) (@lem225186 m n)). Qed.
Lemma lem225189 (m : nat) : (term399 m) = (term411 m).
Proof. exact (fun_ext (fun n : nat => @lem225188 m n)). Qed.
Lemma lem225190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225191 (m : nat) : (term400 m) = (term412 m).
Proof. exact (MK_COMB (@lem225190) (@lem225189 m)). Qed.
Lemma lem225192 : term401 = term413.
Proof. exact (fun_ext (fun m : nat => @lem225191 m)). Qed.
Lemma lem225193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225194 : term402 = term414.
Proof. exact (MK_COMB (@lem225193) (@lem225192)). Qed.
Lemma lem225204 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem225205 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem225204 nat P Q). Qed.
Lemma lem225206 (m : nat) (n : nat) : (term415 m n) = (term416 m n).
Proof. exact (@lem225205 (term417 m n) (term418 m n)). Qed.
Lemma lem225207 (p : nat) (m : nat) (n : nat) : (term419 m n p) = (term420 p m n).
Proof. exact (eq_refl (term419 m n p)). Qed.
Lemma lem225208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225209 (p : nat) (m : nat) (n : nat) : (term421 m n p) = (term422 p m n).
Proof. exact (MK_COMB (@lem225208) (@lem225207 p m n)). Qed.
Lemma lem225210 (p : nat) (m : nat) (n : nat) : (term423 m n p) = (term424 p m n).
Proof. exact (eq_refl (term423 m n p)). Qed.
Lemma lem225211 (p : nat) (m : nat) (n : nat) : (term425 m n p) = (term408 p m n).
Proof. exact (MK_COMB (@lem225209 p m n) (@lem225210 p m n)). Qed.
Lemma lem225212 (m : nat) (n : nat) : (term426 m n) = (term409 m n).
Proof. exact (fun_ext (fun p : nat => @lem225211 p m n)). Qed.
Lemma lem225213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225214 (m : nat) (n : nat) : (term415 m n) = (term410 m n).
Proof. exact (MK_COMB (@lem225213) (@lem225212 m n)). Qed.
Lemma lem225215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem225216 (m : nat) (n : nat) : (term427 m n) = (term428 m n).
Proof. exact (MK_COMB (@lem225215) (@lem225214 m n)). Qed.
Lemma lem225217 (p : nat) (m : nat) (n : nat) : (term419 m n p) = (term420 p m n).
Proof. exact (eq_refl (term419 m n p)). Qed.
Lemma lem225218 (m : nat) (n : nat) : (term429 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem225217 p m n)). Qed.
Lemma lem225219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225220 (m : nat) (n : nat) : (term430 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem225219) (@lem225218 m n)). Qed.
Lemma lem225221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225222 (m : nat) (n : nat) : (term432 m n) = (term433 m n).
Proof. exact (MK_COMB (@lem225221) (@lem225220 m n)). Qed.
Lemma lem225223 (p : nat) (m : nat) (n : nat) : (term423 m n p) = (term424 p m n).
Proof. exact (eq_refl (term423 m n p)). Qed.
Lemma lem225224 (m : nat) (n : nat) : (term434 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem225223 p m n)). Qed.
Lemma lem225225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225226 (m : nat) (n : nat) : (term435 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem225225) (@lem225224 m n)). Qed.
Lemma lem225227 (m : nat) (n : nat) : (term416 m n) = (term437 m n).
Proof. exact (MK_COMB (@lem225222 m n) (@lem225226 m n)). Qed.
Lemma lem225228 (m : nat) (n : nat) : ((term415 m n) = (term416 m n)) = ((term410 m n) = (term437 m n)).
Proof. exact (MK_COMB (@lem225216 m n) (@lem225227 m n)). Qed.
Lemma lem225229 (m : nat) (n : nat) : (term410 m n) = (term437 m n).
Proof. exact (EQ_MP (@lem225228 m n) (@lem225206 m n)). Qed.
Lemma lem225251 {A : Type'} (P : A -> Prop) (Q : Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem225252 (P : nat -> Prop) (Q : Prop) : (term440 P Q) = (term441 P Q).
Proof. exact (@lem225251 nat P Q). Qed.
Lemma lem225253 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (@lem225252 (term444 m n) (term162 m n)). Qed.
Lemma lem225254 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem225255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem225256 (m : nat) (n : nat) (p : nat) : (term446 m n p) = (term447 m n p).
Proof. exact (MK_COMB (@lem225255) (@lem225254 m n p)). Qed.
Lemma lem225257 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem225258 (p : nat) (m : nat) (n : nat) : (term448 p m n) = (term420 p m n).
Proof. exact (MK_COMB (@lem225256 m n p) (@lem225257 m n)). Qed.
Lemma lem225259 (m : nat) (n : nat) : (term449 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem225258 p m n)). Qed.
Lemma lem225260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225261 (m : nat) (n : nat) : (term442 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem225260) (@lem225259 m n)). Qed.
Lemma lem225262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem225263 (m : nat) (n : nat) : (term450 m n) = (term451 m n).
Proof. exact (MK_COMB (@lem225262) (@lem225261 m n)). Qed.
Lemma lem225264 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem225265 (m : nat) (n : nat) : (term452 m n) = (term444 m n).
Proof. exact (fun_ext (fun p : nat => @lem225264 m n p)). Qed.
Lemma lem225266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225267 (m : nat) (n : nat) : (term453 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem225266) (@lem225265 m n)). Qed.
Lemma lem225268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem225269 (m : nat) (n : nat) : (term455 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem225268) (@lem225267 m n)). Qed.
Lemma lem225270 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem225271 (m : nat) (n : nat) : (term443 m n) = (term457 m n).
Proof. exact (MK_COMB (@lem225269 m n) (@lem225270 m n)). Qed.
Lemma lem225272 (m : nat) (n : nat) : ((term442 m n) = (term443 m n)) = ((term431 m n) = (term457 m n)).
Proof. exact (MK_COMB (@lem225263 m n) (@lem225271 m n)). Qed.
Lemma lem225273 (m : nat) (n : nat) : (term431 m n) = (term457 m n).
Proof. exact (EQ_MP (@lem225272 m n) (@lem225253 m n)). Qed.
Lemma lem225278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225279 (m : nat) (n : nat) : (term433 m n) = (term458 m n).
Proof. exact (MK_COMB (@lem225278) (@lem225273 m n)). Qed.
Lemma lem225301 {A : Type'} (P : A -> Prop) (Q : Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem225302 (P : nat -> Prop) (Q : Prop) : (term440 P Q) = (term441 P Q).
Proof. exact (@lem225301 nat P Q). Qed.
Lemma lem225303 (m : nat) (n : nat) : (term459 m n) = (term460 m n).
Proof. exact (@lem225302 (term461 m n) (Peano.le m n)). Qed.
Lemma lem225304 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem225305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem225306 (m : nat) (n : nat) (p : nat) : (term464 m n p) = (term465 m n p).
Proof. exact (MK_COMB (@lem225305) (@lem225304 m n p)). Qed.
Lemma lem225307 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem225308 (p : nat) (m : nat) (n : nat) : (term466 p m n) = (term424 p m n).
Proof. exact (MK_COMB (@lem225306 m n p) (@lem225307 m n)). Qed.
Lemma lem225309 (m : nat) (n : nat) : (term467 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem225308 p m n)). Qed.
Lemma lem225310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225311 (m : nat) (n : nat) : (term459 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem225310) (@lem225309 m n)). Qed.
Lemma lem225312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem225313 (m : nat) (n : nat) : (term468 m n) = (term469 m n).
Proof. exact (MK_COMB (@lem225312) (@lem225311 m n)). Qed.
Lemma lem225314 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem225315 (m : nat) (n : nat) : (term470 m n) = (term461 m n).
Proof. exact (fun_ext (fun p : nat => @lem225314 m n p)). Qed.
Lemma lem225316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225317 (m : nat) (n : nat) : (term471 m n) = (term472 m n).
Proof. exact (MK_COMB (@lem225316) (@lem225315 m n)). Qed.
Lemma lem225318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem225319 (m : nat) (n : nat) : (term473 m n) = (term474 m n).
Proof. exact (MK_COMB (@lem225318) (@lem225317 m n)). Qed.
Lemma lem225320 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem225321 (m : nat) (n : nat) : (term460 m n) = (term475 m n).
Proof. exact (MK_COMB (@lem225319 m n) (@lem225320 m n)). Qed.
Lemma lem225322 (m : nat) (n : nat) : ((term459 m n) = (term460 m n)) = ((term436 m n) = (term475 m n)).
Proof. exact (MK_COMB (@lem225313 m n) (@lem225321 m n)). Qed.
Lemma lem225323 (m : nat) (n : nat) : (term436 m n) = (term475 m n).
Proof. exact (EQ_MP (@lem225322 m n) (@lem225303 m n)). Qed.
Lemma lem225328 (m : nat) (n : nat) : (term437 m n) = (term476 m n).
Proof. exact (MK_COMB (@lem225279 m n) (@lem225323 m n)). Qed.
Lemma lem225329 (m : nat) (n : nat) : (term410 m n) = (term476 m n).
Proof. exact (TRANS (@lem225229 m n) (@lem225328 m n)). Qed.
Lemma lem225330 (m : nat) : (term411 m) = (term477 m).
Proof. exact (fun_ext (fun n : nat => @lem225329 m n)). Qed.
Lemma lem225331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225332 (m : nat) : (term412 m) = (term478 m).
Proof. exact (MK_COMB (@lem225331) (@lem225330 m)). Qed.
Lemma lem225334 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem225335 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem225334 nat P Q). Qed.
Lemma lem225336 (m : nat) : (term479 m) = (term480 m).
Proof. exact (@lem225335 (term481 m) (term482 m)). Qed.
Lemma lem225337 (m : nat) (n : nat) : (term483 m n) = (term457 m n).
Proof. exact (eq_refl (term483 m n)). Qed.
Lemma lem225338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225339 (m : nat) (n : nat) : (term484 m n) = (term458 m n).
Proof. exact (MK_COMB (@lem225338) (@lem225337 m n)). Qed.
Lemma lem225340 (m : nat) (n : nat) : (term485 m n) = (term475 m n).
Proof. exact (eq_refl (term485 m n)). Qed.
Lemma lem225341 (m : nat) (n : nat) : (term486 m n) = (term476 m n).
Proof. exact (MK_COMB (@lem225339 m n) (@lem225340 m n)). Qed.
Lemma lem225342 (m : nat) : (term487 m) = (term477 m).
Proof. exact (fun_ext (fun n : nat => @lem225341 m n)). Qed.
Lemma lem225343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225344 (m : nat) : (term479 m) = (term478 m).
Proof. exact (MK_COMB (@lem225343) (@lem225342 m)). Qed.
Lemma lem225345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem225346 (m : nat) : (term488 m) = (term489 m).
Proof. exact (MK_COMB (@lem225345) (@lem225344 m)). Qed.
Lemma lem225347 (m : nat) (n : nat) : (term483 m n) = (term457 m n).
Proof. exact (eq_refl (term483 m n)). Qed.
Lemma lem225348 (m : nat) : (term490 m) = (term481 m).
Proof. exact (fun_ext (fun n : nat => @lem225347 m n)). Qed.
Lemma lem225349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225350 (m : nat) : (term491 m) = (term492 m).
Proof. exact (MK_COMB (@lem225349) (@lem225348 m)). Qed.
Lemma lem225351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225352 (m : nat) : (term493 m) = (term494 m).
Proof. exact (MK_COMB (@lem225351) (@lem225350 m)). Qed.
Lemma lem225353 (m : nat) (n : nat) : (term485 m n) = (term475 m n).
Proof. exact (eq_refl (term485 m n)). Qed.
Lemma lem225354 (m : nat) : (term495 m) = (term482 m).
Proof. exact (fun_ext (fun n : nat => @lem225353 m n)). Qed.
Lemma lem225355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225356 (m : nat) : (term496 m) = (term497 m).
Proof. exact (MK_COMB (@lem225355) (@lem225354 m)). Qed.
Lemma lem225357 (m : nat) : (term480 m) = (term498 m).
Proof. exact (MK_COMB (@lem225352 m) (@lem225356 m)). Qed.
Lemma lem225358 (m : nat) : ((term479 m) = (term480 m)) = ((term478 m) = (term498 m)).
Proof. exact (MK_COMB (@lem225346 m) (@lem225357 m)). Qed.
Lemma lem225359 (m : nat) : (term478 m) = (term498 m).
Proof. exact (EQ_MP (@lem225358 m) (@lem225336 m)). Qed.
Lemma lem225464 (m : nat) : (term412 m) = (term498 m).
Proof. exact (TRANS (@lem225332 m) (@lem225359 m)). Qed.
Lemma lem225465 : term413 = term499.
Proof. exact (fun_ext (fun m : nat => @lem225464 m)). Qed.
Lemma lem225466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225467 : term414 = term500.
Proof. exact (MK_COMB (@lem225466) (@lem225465)). Qed.
Lemma lem225469 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem225470 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem225469 nat P Q). Qed.
Lemma lem225471 : term501 = term502.
Proof. exact (@lem225470 term503 term504). Qed.
Lemma lem225472 (m : nat) : (term505 m) = (term492 m).
Proof. exact (eq_refl (term505 m)). Qed.
Lemma lem225473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225474 (m : nat) : (term506 m) = (term494 m).
Proof. exact (MK_COMB (@lem225473) (@lem225472 m)). Qed.
Lemma lem225475 (m : nat) : (term507 m) = (term497 m).
Proof. exact (eq_refl (term507 m)). Qed.
Lemma lem225476 (m : nat) : (term508 m) = (term498 m).
Proof. exact (MK_COMB (@lem225474 m) (@lem225475 m)). Qed.
Lemma lem225477 : term509 = term499.
Proof. exact (fun_ext (fun m : nat => @lem225476 m)). Qed.
Lemma lem225478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225479 : term501 = term500.
Proof. exact (MK_COMB (@lem225478) (@lem225477)). Qed.
Lemma lem225480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem225481 : term510 = term511.
Proof. exact (MK_COMB (@lem225480) (@lem225479)). Qed.
Lemma lem225482 (m : nat) : (term505 m) = (term492 m).
Proof. exact (eq_refl (term505 m)). Qed.
Lemma lem225483 : term512 = term503.
Proof. exact (fun_ext (fun m : nat => @lem225482 m)). Qed.
Lemma lem225484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225485 : term513 = term514.
Proof. exact (MK_COMB (@lem225484) (@lem225483)). Qed.
Lemma lem225486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225487 : term515 = term516.
Proof. exact (MK_COMB (@lem225486) (@lem225485)). Qed.
Lemma lem225488 (m : nat) : (term507 m) = (term497 m).
Proof. exact (eq_refl (term507 m)). Qed.
Lemma lem225489 : term517 = term504.
Proof. exact (fun_ext (fun m : nat => @lem225488 m)). Qed.
Lemma lem225490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225491 : term518 = term519.
Proof. exact (MK_COMB (@lem225490) (@lem225489)). Qed.
Lemma lem225492 : term502 = term520.
Proof. exact (MK_COMB (@lem225487) (@lem225491)). Qed.
Lemma lem225493 : (term501 = term502) = (term500 = term520).
Proof. exact (MK_COMB (@lem225481) (@lem225492)). Qed.
Lemma lem225494 : term500 = term520.
Proof. exact (EQ_MP (@lem225493) (@lem225471)). Qed.
Lemma lem225609 : term414 = term520.
Proof. exact (TRANS (@lem225467) (@lem225494)). Qed.
Lemma lem225610 : term402 = term520.
Proof. exact (TRANS (@lem225194) (@lem225609)). Qed.
Lemma lem225611 (h1 : term402) : term520.
Proof. exact (EQ_MP (@lem225610) (@lem225138 h1)). Qed.
Lemma lem225632 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem225633 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem225632 n m)). Qed.
Lemma lem225634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225635 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem225634) (@lem225633 m)). Qed.
Lemma lem225636 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem225635 m)). Qed.
Lemma lem225637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225650 : term364 = term364.
Proof. exact (MK_COMB (@lem225637) (@lem225636)). Qed.
Lemma lem225651 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem225650) (@lem225140 h1)). Qed.
Lemma lem225813 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term679 k m n p.
Proof. exact (EQ_MP (@lem225169 k m n p) (@lem225137 k m n p h1)). Qed.
Lemma lem225818 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem225833 (m : nat) (n : nat) (p : nat) : (term463 m n p) = (term463 m n p).
Proof. exact (eq_refl (term463 m n p)). Qed.
Lemma lem225834 (m : nat) (n : nat) : (term461 m n) = (term461 m n).
Proof. exact (fun_ext (fun p : nat => @lem225833 m n p)). Qed.
Lemma lem225835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225836 (m : nat) (n : nat) : (term472 m n) = (term472 m n).
Proof. exact (MK_COMB (@lem225835) (@lem225834 m n)). Qed.
Lemma lem225837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem225838 (m : nat) (n : nat) : (term474 m n) = (term474 m n).
Proof. exact (MK_COMB (@lem225837) (@lem225836 m n)). Qed.
Lemma lem225839 (m : nat) (n : nat) : (term475 m n) = (term475 m n).
Proof. exact (MK_COMB (@lem225838 m n) (@lem225818 m n)). Qed.
Lemma lem225840 (m : nat) : (term482 m) = (term482 m).
Proof. exact (fun_ext (fun n : nat => @lem225839 m n)). Qed.
Lemma lem225841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225842 (m : nat) : (term497 m) = (term497 m).
Proof. exact (MK_COMB (@lem225841) (@lem225840 m)). Qed.
Lemma lem225843 : term504 = term504.
Proof. exact (fun_ext (fun m : nat => @lem225842 m)). Qed.
Lemma lem225844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225845 : term519 = term519.
Proof. exact (MK_COMB (@lem225844) (@lem225843)). Qed.
Lemma lem225852 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem225865 (m : nat) (n : nat) (p : nat) : (term396 m n p) = (term396 m n p).
Proof. exact (eq_refl (term396 m n p)). Qed.
Lemma lem225866 (m : nat) (n : nat) : (term444 m n) = (term444 m n).
Proof. exact (fun_ext (fun p : nat => @lem225865 m n p)). Qed.
Lemma lem225867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225868 (m : nat) (n : nat) : (term454 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem225867) (@lem225866 m n)). Qed.
Lemma lem225869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem225870 (m : nat) (n : nat) : (term456 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem225869) (@lem225868 m n)). Qed.
Lemma lem225871 (m : nat) (n : nat) : (term457 m n) = (term457 m n).
Proof. exact (MK_COMB (@lem225870 m n) (@lem225852 m n)). Qed.
Lemma lem225872 (m : nat) : (term481 m) = (term481 m).
Proof. exact (fun_ext (fun n : nat => @lem225871 m n)). Qed.
Lemma lem225873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225874 (m : nat) : (term492 m) = (term492 m).
Proof. exact (MK_COMB (@lem225873) (@lem225872 m)). Qed.
Lemma lem225875 : term503 = term503.
Proof. exact (fun_ext (fun m : nat => @lem225874 m)). Qed.
Lemma lem225876 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225877 : term514 = term514.
Proof. exact (MK_COMB (@lem225876) (@lem225875)). Qed.
Lemma lem225878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem225879 : term516 = term516.
Proof. exact (MK_COMB (@lem225878) (@lem225877)). Qed.
Lemma lem225880 : term520 = term520.
Proof. exact (MK_COMB (@lem225879) (@lem225845)). Qed.
Lemma lem225881 (h1 : term402) : term520.
Proof. exact (EQ_MP (@lem225880) (@lem225611 h1)). Qed.
Lemma lem225914 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem225915 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem225914 n m)). Qed.
Lemma lem225916 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225917 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem225916) (@lem225915 m)). Qed.
Lemma lem225918 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem225917 m)). Qed.
Lemma lem225919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225920 : term364 = term364.
Proof. exact (MK_COMB (@lem225919) (@lem225918)). Qed.
Lemma lem225921 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem225920) (@lem225651 h1)). Qed.
Lemma lem225922 (h1 : term402) : term519.
Proof. exact (proj2 (@lem225881 h1)). Qed.
Lemma lem225923 (h1 : term402) : term514.
Proof. exact (proj1 (@lem225881 h1)). Qed.
Lemma lem225924 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term676 k m n p.
Proof. exact (proj2 (@lem225813 k m n p h1)). Qed.
Lemma lem225925 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term346 m n p.
Proof. exact (proj1 (@lem225813 k m n p h1)). Qed.
Lemma lem225928 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term680 k m n p) : term680 k m n p.
Proof. exact (h1). Qed.
Lemma lem225929 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term681 k m n p) : term681 k m n p.
Proof. exact (h1). Qed.
Lemma lem225945 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem225946 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem225945 n m)). Qed.
Lemma lem225947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225948 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem225947) (@lem225946 m)). Qed.
Lemma lem225949 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem225948 m)). Qed.
Lemma lem225950 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem225952 : term364 = term364.
Proof. exact (MK_COMB (@lem225950) (@lem225949)). Qed.
Lemma lem225953 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem225952) (@lem225921 h1)). Qed.
Lemma lem226003 {A : Type'} (P : A -> Prop) (Q : Prop) : (term439 A P Q) = (term438 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem226004 (P : nat -> Prop) (Q : Prop) : (term441 P Q) = (term440 P Q).
Proof. exact (@lem226003 nat P Q). Qed.
Lemma lem226005 (m : nat) (n : nat) : (term460 m n) = (term459 m n).
Proof. exact (@lem226004 (term461 m n) (Peano.le m n)). Qed.
Lemma lem226006 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem226007 (m : nat) (n : nat) : (term470 m n) = (term461 m n).
Proof. exact (fun_ext (fun p : nat => @lem226006 m n p)). Qed.
Lemma lem226008 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226009 (m : nat) (n : nat) : (term471 m n) = (term472 m n).
Proof. exact (MK_COMB (@lem226008) (@lem226007 m n)). Qed.
Lemma lem226010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem226011 (m : nat) (n : nat) : (term473 m n) = (term474 m n).
Proof. exact (MK_COMB (@lem226010) (@lem226009 m n)). Qed.
Lemma lem226012 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem226013 (m : nat) (n : nat) : (term460 m n) = (term475 m n).
Proof. exact (MK_COMB (@lem226011 m n) (@lem226012 m n)). Qed.
Lemma lem226014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem226015 (m : nat) (n : nat) : (term529 m n) = (term530 m n).
Proof. exact (MK_COMB (@lem226014) (@lem226013 m n)). Qed.
Lemma lem226016 (m : nat) (n : nat) (p : nat) : (term462 m n p) = (term463 m n p).
Proof. exact (eq_refl (term462 m n p)). Qed.
Lemma lem226017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem226018 (m : nat) (n : nat) (p : nat) : (term464 m n p) = (term465 m n p).
Proof. exact (MK_COMB (@lem226017) (@lem226016 m n p)). Qed.
Lemma lem226019 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem226020 (p : nat) (m : nat) (n : nat) : (term466 p m n) = (term424 p m n).
Proof. exact (MK_COMB (@lem226018 m n p) (@lem226019 m n)). Qed.
Lemma lem226021 (m : nat) (n : nat) : (term467 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem226020 p m n)). Qed.
Lemma lem226022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226023 (m : nat) (n : nat) : (term459 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem226022) (@lem226021 m n)). Qed.
Lemma lem226024 (m : nat) (n : nat) : ((term460 m n) = (term459 m n)) = ((term475 m n) = (term436 m n)).
Proof. exact (MK_COMB (@lem226015 m n) (@lem226023 m n)). Qed.
Lemma lem226025 (m : nat) (n : nat) : (term475 m n) = (term436 m n).
Proof. exact (EQ_MP (@lem226024 m n) (@lem226005 m n)). Qed.
Lemma lem226026 (m : nat) : (term482 m) = (term531 m).
Proof. exact (fun_ext (fun n : nat => @lem226025 m n)). Qed.
Lemma lem226027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226028 (m : nat) : (term497 m) = (term532 m).
Proof. exact (MK_COMB (@lem226027) (@lem226026 m)). Qed.
Lemma lem226029 : term504 = term533.
Proof. exact (fun_ext (fun m : nat => @lem226028 m)). Qed.
Lemma lem226030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226031 : term519 = term534.
Proof. exact (MK_COMB (@lem226030) (@lem226029)). Qed.
Lemma lem226038 (p : nat) (m : nat) (n : nat) : (term424 p m n) = (term424 p m n).
Proof. exact (eq_refl (term424 p m n)). Qed.
Lemma lem226039 (m : nat) (n : nat) : (term418 m n) = (term418 m n).
Proof. exact (fun_ext (fun p : nat => @lem226038 p m n)). Qed.
Lemma lem226040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226041 (m : nat) (n : nat) : (term436 m n) = (term436 m n).
Proof. exact (MK_COMB (@lem226040) (@lem226039 m n)). Qed.
Lemma lem226042 (m : nat) : (term531 m) = (term531 m).
Proof. exact (fun_ext (fun n : nat => @lem226041 m n)). Qed.
Lemma lem226043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226044 (m : nat) : (term532 m) = (term532 m).
Proof. exact (MK_COMB (@lem226043) (@lem226042 m)). Qed.
Lemma lem226045 : term533 = term533.
Proof. exact (fun_ext (fun m : nat => @lem226044 m)). Qed.
Lemma lem226046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226047 : term534 = term534.
Proof. exact (MK_COMB (@lem226046) (@lem226045)). Qed.
Lemma lem226048 : term519 = term534.
Proof. exact (TRANS (@lem226031) (@lem226047)). Qed.
Lemma lem226049 (h1 : term402) : term534.
Proof. exact (EQ_MP (@lem226048) (@lem225922 h1)). Qed.
Lemma lem226077 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem226078 (m : nat) : (term389 m) = (term389 m).
Proof. exact (fun_ext (fun n : nat => @lem226077 n m)). Qed.
Lemma lem226079 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226080 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem226079) (@lem226078 m)). Qed.
Lemma lem226081 : term391 = term391.
Proof. exact (fun_ext (fun m : nat => @lem226080 m)). Qed.
Lemma lem226082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226084 : term364 = term364.
Proof. exact (MK_COMB (@lem226082) (@lem226081)). Qed.
Lemma lem226085 (h1 : term364) : term364.
Proof. exact (EQ_MP (@lem226084) (@lem225921 h1)). Qed.
Lemma lem226087 {A : Type'} (P : A -> Prop) (Q : Prop) : (term439 A P Q) = (term438 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem226088 (P : nat -> Prop) (Q : Prop) : (term441 P Q) = (term440 P Q).
Proof. exact (@lem226087 nat P Q). Qed.
Lemma lem226089 (m : nat) (n : nat) : (term443 m n) = (term442 m n).
Proof. exact (@lem226088 (term444 m n) (term162 m n)). Qed.
Lemma lem226090 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem226091 (m : nat) (n : nat) : (term452 m n) = (term444 m n).
Proof. exact (fun_ext (fun p : nat => @lem226090 m n p)). Qed.
Lemma lem226092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226093 (m : nat) (n : nat) : (term453 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem226092) (@lem226091 m n)). Qed.
Lemma lem226094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem226095 (m : nat) (n : nat) : (term455 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem226094) (@lem226093 m n)). Qed.
Lemma lem226096 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem226097 (m : nat) (n : nat) : (term443 m n) = (term457 m n).
Proof. exact (MK_COMB (@lem226095 m n) (@lem226096 m n)). Qed.
Lemma lem226098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem226099 (m : nat) (n : nat) : (term523 m n) = (term524 m n).
Proof. exact (MK_COMB (@lem226098) (@lem226097 m n)). Qed.
Lemma lem226100 (m : nat) (n : nat) (p : nat) : (term445 m n p) = (term396 m n p).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem226101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem226102 (m : nat) (n : nat) (p : nat) : (term446 m n p) = (term447 m n p).
Proof. exact (MK_COMB (@lem226101) (@lem226100 m n p)). Qed.
Lemma lem226103 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem226104 (p : nat) (m : nat) (n : nat) : (term448 p m n) = (term420 p m n).
Proof. exact (MK_COMB (@lem226102 m n p) (@lem226103 m n)). Qed.
Lemma lem226105 (m : nat) (n : nat) : (term449 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem226104 p m n)). Qed.
Lemma lem226106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226107 (m : nat) (n : nat) : (term442 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem226106) (@lem226105 m n)). Qed.
Lemma lem226108 (m : nat) (n : nat) : ((term443 m n) = (term442 m n)) = ((term457 m n) = (term431 m n)).
Proof. exact (MK_COMB (@lem226099 m n) (@lem226107 m n)). Qed.
Lemma lem226109 (m : nat) (n : nat) : (term457 m n) = (term431 m n).
Proof. exact (EQ_MP (@lem226108 m n) (@lem226089 m n)). Qed.
Lemma lem226110 (m : nat) : (term481 m) = (term525 m).
Proof. exact (fun_ext (fun n : nat => @lem226109 m n)). Qed.
Lemma lem226111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226112 (m : nat) : (term492 m) = (term526 m).
Proof. exact (MK_COMB (@lem226111) (@lem226110 m)). Qed.
Lemma lem226113 : term503 = term527.
Proof. exact (fun_ext (fun m : nat => @lem226112 m)). Qed.
Lemma lem226114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226115 : term514 = term528.
Proof. exact (MK_COMB (@lem226114) (@lem226113)). Qed.
Lemma lem226122 (p : nat) (m : nat) (n : nat) : (term420 p m n) = (term420 p m n).
Proof. exact (eq_refl (term420 p m n)). Qed.
Lemma lem226123 (m : nat) (n : nat) : (term417 m n) = (term417 m n).
Proof. exact (fun_ext (fun p : nat => @lem226122 p m n)). Qed.
Lemma lem226124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226125 (m : nat) (n : nat) : (term431 m n) = (term431 m n).
Proof. exact (MK_COMB (@lem226124) (@lem226123 m n)). Qed.
Lemma lem226126 (m : nat) : (term525 m) = (term525 m).
Proof. exact (fun_ext (fun n : nat => @lem226125 m n)). Qed.
Lemma lem226127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226128 (m : nat) : (term526 m) = (term526 m).
Proof. exact (MK_COMB (@lem226127) (@lem226126 m)). Qed.
Lemma lem226129 : term527 = term527.
Proof. exact (fun_ext (fun m : nat => @lem226128 m)). Qed.
Lemma lem226130 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem226131 : term528 = term528.
Proof. exact (MK_COMB (@lem226130) (@lem226129)). Qed.
Lemma lem226132 : term514 = term528.
Proof. exact (TRANS (@lem226115) (@lem226131)). Qed.
Lemma lem226133 (h1 : term402) : term528.
Proof. exact (EQ_MP (@lem226132) (@lem225923 h1)). Qed.
Lemma lem226204 (_4480 : nat) (h1 : term364) : term535 _4480.
Proof. exact (@lem225953 h1 _4480). Qed.
Lemma lem226205 (_4480 : nat) : (term535 _4480) = (term390 _4480).
Proof. exact (eq_refl (term535 _4480)). Qed.
Lemma lem226206 (_4480 : nat) (h1 : term364) : term390 _4480.
Proof. exact (EQ_MP (@lem226205 _4480) (@lem226204 _4480 h1)). Qed.
Lemma lem226207 (_4480 : nat) (_4481 : nat) (h1 : term364) : term536 _4480 _4481.
Proof. exact (@lem226206 _4480 h1 _4481). Qed.
Lemma lem226208 (_4481 : nat) (_4480 : nat) : (term536 _4480 _4481) = ((Nat.add _4480 _4481) = (Nat.add _4481 _4480)).
Proof. exact (eq_refl (term536 _4480 _4481)). Qed.
Lemma lem226219 (_4485 : nat) (h1 : term402) : term539 _4485.
Proof. exact (@lem226049 h1 _4485). Qed.
Lemma lem226220 (_4485 : nat) : (term539 _4485) = (term532 _4485).
Proof. exact (eq_refl (term539 _4485)). Qed.
Lemma lem226221 (_4485 : nat) (h1 : term402) : term532 _4485.
Proof. exact (EQ_MP (@lem226220 _4485) (@lem226219 _4485 h1)). Qed.
Lemma lem226222 (_4485 : nat) (_4486 : nat) (h1 : term402) : term540 _4485 _4486.
Proof. exact (@lem226221 _4485 h1 _4486). Qed.
Lemma lem226223 (_4485 : nat) (_4486 : nat) : (term540 _4485 _4486) = (term436 _4485 _4486).
Proof. exact (eq_refl (term540 _4485 _4486)). Qed.
Lemma lem226224 (_4485 : nat) (_4486 : nat) (h1 : term402) : term436 _4485 _4486.
Proof. exact (EQ_MP (@lem226223 _4485 _4486) (@lem226222 _4485 _4486 h1)). Qed.
Lemma lem226225 (_4485 : nat) (_4486 : nat) (_4487 : nat) (h1 : term402) : term423 _4485 _4486 _4487.
Proof. exact (@lem226224 _4485 _4486 h1 _4487). Qed.
Lemma lem226226 (_4487 : nat) (_4485 : nat) (_4486 : nat) : (term423 _4485 _4486 _4487) = (term424 _4487 _4485 _4486).
Proof. exact (eq_refl (term423 _4485 _4486 _4487)). Qed.
Lemma lem226234 (_4490 : nat) (h1 : term364) : term535 _4490.
Proof. exact (@lem226085 h1 _4490). Qed.
Lemma lem226235 (_4490 : nat) : (term535 _4490) = (term390 _4490).
Proof. exact (eq_refl (term535 _4490)). Qed.
Lemma lem226236 (_4490 : nat) (h1 : term364) : term390 _4490.
Proof. exact (EQ_MP (@lem226235 _4490) (@lem226234 _4490 h1)). Qed.
Lemma lem226237 (_4490 : nat) (_4491 : nat) (h1 : term364) : term536 _4490 _4491.
Proof. exact (@lem226236 _4490 h1 _4491). Qed.
Lemma lem226238 (_4491 : nat) (_4490 : nat) : (term536 _4490 _4491) = ((Nat.add _4490 _4491) = (Nat.add _4491 _4490)).
Proof. exact (eq_refl (term536 _4490 _4491)). Qed.
Lemma lem226240 (_4492 : nat) (h1 : term402) : term537 _4492.
Proof. exact (@lem226133 h1 _4492). Qed.
Lemma lem226241 (_4492 : nat) : (term537 _4492) = (term526 _4492).
Proof. exact (eq_refl (term537 _4492)). Qed.
Lemma lem226242 (_4492 : nat) (h1 : term402) : term526 _4492.
Proof. exact (EQ_MP (@lem226241 _4492) (@lem226240 _4492 h1)). Qed.
Lemma lem226243 (_4492 : nat) (_4493 : nat) (h1 : term402) : term538 _4492 _4493.
Proof. exact (@lem226242 _4492 h1 _4493). Qed.
Lemma lem226244 (_4492 : nat) (_4493 : nat) : (term538 _4492 _4493) = (term431 _4492 _4493).
Proof. exact (eq_refl (term538 _4492 _4493)). Qed.
Lemma lem226245 (_4492 : nat) (_4493 : nat) (h1 : term402) : term431 _4492 _4493.
Proof. exact (EQ_MP (@lem226244 _4492 _4493) (@lem226243 _4492 _4493 h1)). Qed.
Lemma lem226246 (_4492 : nat) (_4493 : nat) (_4494 : nat) (h1 : term402) : term419 _4492 _4493 _4494.
Proof. exact (@lem226245 _4492 _4493 h1 _4494). Qed.
Lemma lem226247 (_4494 : nat) (_4492 : nat) (_4493 : nat) : (term419 _4492 _4493 _4494) = (term420 _4494 _4492 _4493).
Proof. exact (eq_refl (term419 _4492 _4493 _4494)). Qed.
Lemma lem226273 (_4487 : nat) (_4485 : nat) (_4486 : nat) (h1 : term402) : term424 _4487 _4485 _4486.
Proof. exact (EQ_MP (@lem226226 _4487 _4485 _4486) (@lem226225 _4485 _4486 _4487 h1)). Qed.
Lemma lem226281 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term680 k m n p) : term682 k m n p.
Proof. exact (proj2 (@lem225928 k m n p h1)). Qed.
Lemma lem226291 (_4494 : nat) (_4492 : nat) (_4493 : nat) (h1 : term402) : term420 _4494 _4492 _4493.
Proof. exact (EQ_MP (@lem226247 _4494 _4492 _4493) (@lem226246 _4492 _4493 _4494 h1)). Qed.
Lemma lem226303 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term681 k m n p) : term683 k n p m.
Proof. exact (proj1 (@lem225929 k m n p h1)). Qed.
Lemma lem226325 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem226326 (_4502 : nat) (_4504 : nat) (h1 : _4502 = _4504) : _4502 = _4504.
Proof. exact (h1). Qed.
Lemma lem226327 (_4503 : nat) (_4505 : nat) (h1 : _4503 = _4505) : _4503 = _4505.
Proof. exact (h1). Qed.
Lemma lem226328 (_4502 : nat) (_4504 : nat) (h1 : _4502 = _4504) : (Peano.le _4502) = (Peano.le _4504).
Proof. exact (MK_COMB (@lem226325) (@lem226326 _4502 _4504 h1)). Qed.
Lemma lem226329 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) (h1 : _4502 = _4504) (h2 : _4503 = _4505) : (Peano.le _4502 _4503) = (Peano.le _4504 _4505).
Proof. exact (MK_COMB (@lem226328 _4502 _4504 h1) (@lem226327 _4503 _4505 h2)). Qed.
Lemma lem226331 (b : Prop) (a : Prop) : term543 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem226332 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : term544 _4504 _4505 _4502 _4503.
Proof. exact (@lem226331 (Peano.le _4504 _4505) (Peano.le _4502 _4503)). Qed.
Lemma lem226333 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) (h1 : _4502 = _4504) (h2 : _4503 = _4505) : term545 _4504 _4505 _4502 _4503.
Proof. exact (@lem226332 _4504 _4505 _4502 _4503 (@lem226329 _4502 _4504 _4503 _4505 h1 h2)). Qed.
Lemma lem226334 (_4505 : nat) (_4503 : nat) (_4502 : nat) (_4504 : nat) (h1 : _4502 = _4504) : term546 _4504 _4505 _4502 _4503.
Proof. exact (fun h0 : _4503 = _4505 => @lem226333 _4502 _4504 _4503 _4505 h1 h0). Qed.
Lemma lem226336 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem226337 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term546 _4504 _4505 _4502 _4503) = (term548 _4504 _4505 _4502 _4503).
Proof. exact (@lem226336 (_4503 = _4505) (term545 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226338 (_4505 : nat) (_4503 : nat) (_4502 : nat) (_4504 : nat) (h1 : _4502 = _4504) : term548 _4504 _4505 _4502 _4503.
Proof. exact (EQ_MP (@lem226337 _4504 _4505 _4502 _4503) (@lem226334 _4505 _4503 _4502 _4504 h1)). Qed.
Lemma lem226339 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : term549 _4504 _4505 _4502 _4503.
Proof. exact (fun h0 : _4502 = _4504 => @lem226338 _4505 _4503 _4502 _4504 h0). Qed.
Lemma lem226341 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem226342 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term549 _4504 _4505 _4502 _4503) = (term550 _4504 _4505 _4502 _4503).
Proof. exact (@lem226341 (_4502 = _4504) (term548 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226343 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : term550 _4504 _4505 _4502 _4503.
Proof. exact (EQ_MP (@lem226342 _4504 _4505 _4502 _4503) (@lem226339 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226407 (_4481 : nat) (_4480 : nat) (h1 : term364) : (Nat.add _4480 _4481) = (Nat.add _4481 _4480).
Proof. exact (EQ_MP (@lem226208 _4481 _4480) (@lem226207 _4480 _4481 h1)). Qed.
Lemma lem226408 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) : (term684 m p k n) = (term349 k m n p).
Proof. exact (@lem226407 (Nat.mul k n) (term310 m n p) h1). Qed.
Lemma lem226409 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) : term685 k m n p.
Proof. exact (fun h0 : term686 k m n p => @lem226408 k m n p h1). Qed.
Lemma lem226411 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226412 (k : nat) (m : nat) (n : nat) (p : nat) : (term685 k m n p) = ((term684 m p k n) = (term349 k m n p)).
Proof. exact (@lem226411 ((term684 m p k n) = (term349 k m n p))). Qed.
Lemma lem226413 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) : (term684 m p k n) = (term349 k m n p).
Proof. exact (EQ_MP (@lem226412 k m n p) (@lem226409 k m n p h1)). Qed.
Lemma lem226415 (_4481 : nat) (_4480 : nat) (h1 : term364) : (Nat.add _4480 _4481) = (Nat.add _4481 _4480).
Proof. exact (EQ_MP (@lem226208 _4481 _4480) (@lem226207 _4480 _4481 h1)). Qed.
Lemma lem226416 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term342 m n p) = (term687 m n p).
Proof. exact (@lem226415 (term224 m n p) (term310 m n p) h1). Qed.
Lemma lem226417 (m : nat) (n : nat) (p : nat) (h1 : term364) : term688 m n p.
Proof. exact (fun h0 : term689 m n p => @lem226416 m n p h1). Qed.
Lemma lem226419 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226420 (m : nat) (n : nat) (p : nat) : (term688 m n p) = ((term342 m n p) = (term687 m n p)).
Proof. exact (@lem226419 ((term342 m n p) = (term687 m n p))). Qed.
Lemma lem226421 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term342 m n p) = (term687 m n p).
Proof. exact (EQ_MP (@lem226420 m n p) (@lem226417 m n p h1)). Qed.
Lemma lem226423 (_4481 : nat) (_4480 : nat) (h1 : term364) : (Nat.add _4480 _4481) = (Nat.add _4481 _4480).
Proof. exact (EQ_MP (@lem226208 _4481 _4480) (@lem226207 _4480 _4481 h1)). Qed.
Lemma lem226424 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term364) : (term349 k m n p) = (term684 m p k n).
Proof. exact (@lem226423 (term310 m n p) (Nat.mul k n) h1). Qed.
Lemma lem226425 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term364) : term690 m p k n.
Proof. exact (fun h0 : term691 m p k n => @lem226424 m p k n h1). Qed.
Lemma lem226427 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226428 (m : nat) (p : nat) (k : nat) (n : nat) : (term690 m p k n) = ((term349 k m n p) = (term684 m p k n)).
Proof. exact (@lem226427 ((term349 k m n p) = (term684 m p k n))). Qed.
Lemma lem226429 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term364) : (term349 k m n p) = (term684 m p k n).
Proof. exact (EQ_MP (@lem226428 m p k n) (@lem226425 m p k n h1)). Qed.
Lemma lem226431 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : m = (term342 m n p).
Proof. exact (proj1 (@lem225925 k m n p h1)). Qed.
Lemma lem226432 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term692 m n p.
Proof. exact (fun h0 : term693 m n p => @lem226431 k m n p h1). Qed.
Lemma lem226434 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226435 (m : nat) (n : nat) (p : nat) : (term692 m n p) = (m = (term342 m n p)).
Proof. exact (@lem226434 (m = (term342 m n p))). Qed.
Lemma lem226436 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : m = (term342 m n p).
Proof. exact (EQ_MP (@lem226435 m n p) (@lem226432 k m n p h1)). Qed.
Lemma lem226438 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term680 k m n p) : term351 k n p m.
Proof. exact (proj1 (@lem225928 k m n p h1)). Qed.
Lemma lem226439 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term680 k m n p) : term694 k n p m.
Proof. exact (fun h0 : term683 k n p m => @lem226438 k m n p h1). Qed.
Lemma lem226441 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226442 (k : nat) (n : nat) (p : nat) (m : nat) : (term694 k n p m) = (term351 k n p m).
Proof. exact (@lem226441 (term351 k n p m)). Qed.
Lemma lem226443 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term680 k m n p) : term351 k n p m.
Proof. exact (EQ_MP (@lem226442 k n p m) (@lem226439 k m n p h1)). Qed.
Lemma lem226461 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem226462 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term548 _4504 _4505 _4502 _4503) = (term594 _4504 _4505 _4502 _4503).
Proof. exact (@lem226461 (Peano.le _4504 _4505) (term64 _4503 _4505) (term162 _4502 _4503)). Qed.
Lemma lem226476 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem226477 (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term595 _4505 _4502 _4503) = (term596 _4502 _4503 _4505).
Proof. exact (@lem226476 (term162 _4502 _4503) (term64 _4503 _4505)). Qed.
Lemma lem226485 (_4504 : nat) (_4505 : nat) : (term597 _4504 _4505) = (term597 _4504 _4505).
Proof. exact (eq_refl (term597 _4504 _4505)). Qed.
Lemma lem226486 (_4504 : nat) (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term594 _4504 _4505 _4502 _4503) = (term598 _4504 _4502 _4503 _4505).
Proof. exact (MK_COMB (@lem226485 _4504 _4505) (@lem226477 _4502 _4503 _4505)). Qed.
Lemma lem226497 (_4504 : nat) (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term548 _4504 _4505 _4502 _4503) = (term598 _4504 _4502 _4503 _4505).
Proof. exact (TRANS (@lem226462 _4504 _4505 _4502 _4503) (@lem226486 _4504 _4502 _4503 _4505)). Qed.
Lemma lem226498 (_4502 : nat) (_4504 : nat) : (term563 _4502 _4504) = (term563 _4502 _4504).
Proof. exact (eq_refl (term563 _4502 _4504)). Qed.
Lemma lem226499 (_4504 : nat) (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term550 _4504 _4505 _4502 _4503) = (term599 _4504 _4502 _4503 _4505).
Proof. exact (MK_COMB (@lem226498 _4502 _4504) (@lem226497 _4504 _4502 _4503 _4505)). Qed.
Lemma lem226503 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem226504 (_4504 : nat) (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term599 _4504 _4502 _4503 _4505) = (term600 _4504 _4502 _4503 _4505).
Proof. exact (@lem226503 (Peano.le _4504 _4505) (term64 _4502 _4504) (term596 _4502 _4503 _4505)). Qed.
Lemma lem226518 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem226519 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term601 _4504 _4502 _4503 _4505) = (term602 _4502 _4504 _4503 _4505).
Proof. exact (@lem226518 (term162 _4502 _4503) (term64 _4502 _4504) (term64 _4503 _4505)). Qed.
Lemma lem226539 (_4504 : nat) (_4505 : nat) : (term597 _4504 _4505) = (term597 _4504 _4505).
Proof. exact (eq_refl (term597 _4504 _4505)). Qed.
Lemma lem226540 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term600 _4504 _4502 _4503 _4505) = (term603 _4502 _4504 _4503 _4505).
Proof. exact (MK_COMB (@lem226539 _4504 _4505) (@lem226519 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226551 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term599 _4504 _4502 _4503 _4505) = (term603 _4502 _4504 _4503 _4505).
Proof. exact (TRANS (@lem226504 _4504 _4502 _4503 _4505) (@lem226540 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226552 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term550 _4504 _4505 _4502 _4503) = (term603 _4502 _4504 _4503 _4505).
Proof. exact (TRANS (@lem226499 _4504 _4502 _4503 _4505) (@lem226551 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem226554 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term604 _4504 _4505 _4502 _4503) = (term605 _4502 _4504 _4503 _4505).
Proof. exact (MK_COMB (@lem226553) (@lem226552 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226580 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem226581 (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term595 _4505 _4502 _4503) = (term596 _4502 _4503 _4505).
Proof. exact (@lem226580 (term162 _4502 _4503) (term64 _4503 _4505)). Qed.
Lemma lem226589 (_4502 : nat) (_4504 : nat) : (term563 _4502 _4504) = (term563 _4502 _4504).
Proof. exact (eq_refl (term563 _4502 _4504)). Qed.
Lemma lem226590 (_4504 : nat) (_4502 : nat) (_4503 : nat) (_4505 : nat) : (term606 _4504 _4505 _4502 _4503) = (term601 _4504 _4502 _4503 _4505).
Proof. exact (MK_COMB (@lem226589 _4502 _4504) (@lem226581 _4502 _4503 _4505)). Qed.
Lemma lem226594 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem226595 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term601 _4504 _4502 _4503 _4505) = (term602 _4502 _4504 _4503 _4505).
Proof. exact (@lem226594 (term162 _4502 _4503) (term64 _4502 _4504) (term64 _4503 _4505)). Qed.
Lemma lem226615 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term606 _4504 _4505 _4502 _4503) = (term602 _4502 _4504 _4503 _4505).
Proof. exact (TRANS (@lem226590 _4504 _4502 _4503 _4505) (@lem226595 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226616 (_4504 : nat) (_4505 : nat) : (term597 _4504 _4505) = (term597 _4504 _4505).
Proof. exact (eq_refl (term597 _4504 _4505)). Qed.
Lemma lem226617 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : (term607 _4504 _4505 _4502 _4503) = (term603 _4502 _4504 _4503 _4505).
Proof. exact (MK_COMB (@lem226616 _4504 _4505) (@lem226615 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226628 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : ((term550 _4504 _4505 _4502 _4503) = (term607 _4504 _4505 _4502 _4503)) = ((term603 _4502 _4504 _4503 _4505) = (term603 _4502 _4504 _4503 _4505)).
Proof. exact (MK_COMB (@lem226554 _4502 _4504 _4503 _4505) (@lem226617 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226630 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem226631 (x : Prop) : (x = x) = True.
Proof. exact (@lem226630 Prop x). Qed.
Lemma lem226632 (_4502 : nat) (_4504 : nat) (_4503 : nat) (_4505 : nat) : ((term603 _4502 _4504 _4503 _4505) = (term603 _4502 _4504 _4503 _4505)) = True.
Proof. exact (@lem226631 (term603 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226633 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : ((term550 _4504 _4505 _4502 _4503) = (term607 _4504 _4505 _4502 _4503)) = True.
Proof. exact (TRANS (@lem226628 _4502 _4504 _4503 _4505) (@lem226632 _4502 _4504 _4503 _4505)). Qed.
Lemma lem226634 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : True = ((term550 _4504 _4505 _4502 _4503) = (term607 _4504 _4505 _4502 _4503)).
Proof. exact (SYM (@lem226633 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226635 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term550 _4504 _4505 _4502 _4503) = (term607 _4504 _4505 _4502 _4503).
Proof. exact (EQ_MP (@lem226634 _4504 _4505 _4502 _4503) (@lem0)). Qed.
Lemma lem226636 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : term607 _4504 _4505 _4502 _4503.
Proof. exact (EQ_MP (@lem226635 _4504 _4505 _4502 _4503) (@lem226343 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226638 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem226639 (_4502 : nat) (_4503 : nat) (_4504 : nat) (_4505 : nat) : (term607 _4504 _4505 _4502 _4503) = (term608 _4502 _4503 _4504 _4505).
Proof. exact (@lem226638 (term606 _4504 _4505 _4502 _4503) (Peano.le _4504 _4505)). Qed.
Lemma lem226641 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem226642 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term609 _4504 _4505 _4502 _4503) = (term610 _4504 _4505 _4502 _4503).
Proof. exact (@lem226641 (term64 _4502 _4504) (term595 _4505 _4502 _4503)). Qed.
Lemma lem226644 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem226645 (_4502 : nat) (_4504 : nat) : (term170 _4502 _4504) = (_4502 = _4504).
Proof. exact (@lem226644 (_4502 = _4504)). Qed.
Lemma lem226646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem226647 (_4502 : nat) (_4504 : nat) : (term572 _4502 _4504) = (term573 _4502 _4504).
Proof. exact (MK_COMB (@lem226646) (@lem226645 _4502 _4504)). Qed.
Lemma lem226649 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem226650 (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term611 _4505 _4502 _4503) = (term612 _4505 _4502 _4503).
Proof. exact (@lem226649 (term64 _4503 _4505) (term162 _4502 _4503)). Qed.
Lemma lem226652 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem226653 (_4503 : nat) (_4505 : nat) : (term170 _4503 _4505) = (_4503 = _4505).
Proof. exact (@lem226652 (_4503 = _4505)). Qed.
Lemma lem226654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem226655 (_4503 : nat) (_4505 : nat) : (term572 _4503 _4505) = (term573 _4503 _4505).
Proof. exact (MK_COMB (@lem226654) (@lem226653 _4503 _4505)). Qed.
Lemma lem226657 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem226658 (_4502 : nat) (_4503 : nat) : (term180 _4502 _4503) = (Peano.le _4502 _4503).
Proof. exact (@lem226657 (Peano.le _4502 _4503)). Qed.
Lemma lem226659 (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term612 _4505 _4502 _4503) = (term613 _4505 _4502 _4503).
Proof. exact (MK_COMB (@lem226655 _4503 _4505) (@lem226658 _4502 _4503)). Qed.
Lemma lem226660 (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term611 _4505 _4502 _4503) = (term613 _4505 _4502 _4503).
Proof. exact (TRANS (@lem226650 _4505 _4502 _4503) (@lem226659 _4505 _4502 _4503)). Qed.
Lemma lem226661 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term610 _4504 _4505 _4502 _4503) = (term614 _4504 _4505 _4502 _4503).
Proof. exact (MK_COMB (@lem226647 _4502 _4504) (@lem226660 _4505 _4502 _4503)). Qed.
Lemma lem226662 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term609 _4504 _4505 _4502 _4503) = (term614 _4504 _4505 _4502 _4503).
Proof. exact (TRANS (@lem226642 _4504 _4505 _4502 _4503) (@lem226661 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226663 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem226664 (_4504 : nat) (_4505 : nat) (_4502 : nat) (_4503 : nat) : (term615 _4504 _4505 _4502 _4503) = (term616 _4504 _4505 _4502 _4503).
Proof. exact (MK_COMB (@lem226663) (@lem226662 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226665 (_4504 : nat) (_4505 : nat) : (Peano.le _4504 _4505) = (Peano.le _4504 _4505).
Proof. exact (eq_refl (Peano.le _4504 _4505)). Qed.
Lemma lem226666 (_4502 : nat) (_4503 : nat) (_4504 : nat) (_4505 : nat) : (term608 _4502 _4503 _4504 _4505) = (term617 _4502 _4503 _4504 _4505).
Proof. exact (MK_COMB (@lem226664 _4504 _4505 _4502 _4503) (@lem226665 _4504 _4505)). Qed.
Lemma lem226667 (_4502 : nat) (_4503 : nat) (_4504 : nat) (_4505 : nat) : (term607 _4504 _4505 _4502 _4503) = (term617 _4502 _4503 _4504 _4505).
Proof. exact (TRANS (@lem226639 _4502 _4503 _4504 _4505) (@lem226666 _4502 _4503 _4504 _4505)). Qed.
Lemma lem226669 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) (h2 : term680 k m n p) : term695 k n p m.
Proof. exact (conj (@lem226436 k m n p h1) (@lem226443 k m n p h2)). Qed.
Lemma lem226670 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term696 k n p m.
Proof. exact (conj (@lem226429 m p k n h1) (@lem226669 k m n p h2 h3)). Qed.
Lemma lem226672 (_4502 : nat) (_4503 : nat) (_4504 : nat) (_4505 : nat) : term617 _4502 _4503 _4504 _4505.
Proof. exact (EQ_MP (@lem226667 _4502 _4503 _4504 _4505) (@lem226636 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226673 (k : nat) (m : nat) (n : nat) (p : nat) : term697 k m n p.
Proof. exact (@lem226672 (term349 k m n p) m (term684 m p k n) (term342 m n p)). Qed.
Lemma lem226676 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term698 k m n p.
Proof. exact (@lem226673 k m n p (@lem226670 k m n p h1 h2 h3)). Qed.
Lemma lem226677 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term699 k m n p.
Proof. exact (fun h0 : term700 k m n p => @lem226676 k m n p h1 h2 h3). Qed.
Lemma lem226679 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226680 (k : nat) (m : nat) (n : nat) (p : nat) : (term699 k m n p) = (term698 k m n p).
Proof. exact (@lem226679 (term698 k m n p)). Qed.
Lemma lem226681 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term698 k m n p.
Proof. exact (EQ_MP (@lem226680 k m n p) (@lem226677 k m n p h1 h2 h3)). Qed.
Lemma lem226682 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term701 k m n p.
Proof. exact (conj (@lem226421 m n p h1) (@lem226681 k m n p h1 h2 h3)). Qed.
Lemma lem226683 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term702 k m n p.
Proof. exact (conj (@lem226413 k m n p h1) (@lem226682 k m n p h1 h2 h3)). Qed.
Lemma lem226685 (_4502 : nat) (_4503 : nat) (_4504 : nat) (_4505 : nat) : term617 _4502 _4503 _4504 _4505.
Proof. exact (EQ_MP (@lem226667 _4502 _4503 _4504 _4505) (@lem226636 _4504 _4505 _4502 _4503)). Qed.
Lemma lem226686 (k : nat) (m : nat) (n : nat) (p : nat) : term703 k m n p.
Proof. exact (@lem226685 (term684 m p k n) (term342 m n p) (term349 k m n p) (term687 m n p)). Qed.
Lemma lem226689 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term704 k m n p.
Proof. exact (@lem226686 k m n p (@lem226683 k m n p h1 h2 h3)). Qed.
Lemma lem226690 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term705 k m n p.
Proof. exact (fun h0 : term706 k m n p => @lem226689 k m n p h1 h2 h3). Qed.
Lemma lem226692 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226693 (k : nat) (m : nat) (n : nat) (p : nat) : (term705 k m n p) = (term704 k m n p).
Proof. exact (@lem226692 (term704 k m n p)). Qed.
Lemma lem226694 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) (h3 : term680 k m n p) : term704 k m n p.
Proof. exact (EQ_MP (@lem226693 k m n p) (@lem226690 k m n p h1 h2 h3)). Qed.
Lemma lem226700 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem226701 (_4485 : nat) (_4486 : nat) (_4487 : nat) : (term424 _4487 _4485 _4486) = (term637 _4485 _4486 _4487).
Proof. exact (@lem226700 (Peano.le _4485 _4486) (term463 _4485 _4486 _4487)). Qed.
Lemma lem226707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem226708 (_4485 : nat) (_4486 : nat) (_4487 : nat) : (term638 _4487 _4485 _4486) = (term639 _4485 _4486 _4487).
Proof. exact (MK_COMB (@lem226707) (@lem226701 _4485 _4486 _4487)). Qed.
Lemma lem226714 (_4485 : nat) (_4486 : nat) (_4487 : nat) : (term637 _4485 _4486 _4487) = (term637 _4485 _4486 _4487).
Proof. exact (eq_refl (term637 _4485 _4486 _4487)). Qed.
Lemma lem226715 (_4485 : nat) (_4486 : nat) (_4487 : nat) : ((term424 _4487 _4485 _4486) = (term637 _4485 _4486 _4487)) = ((term637 _4485 _4486 _4487) = (term637 _4485 _4486 _4487)).
Proof. exact (MK_COMB (@lem226708 _4485 _4486 _4487) (@lem226714 _4485 _4486 _4487)). Qed.
Lemma lem226717 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem226718 (x : Prop) : (x = x) = True.
Proof. exact (@lem226717 Prop x). Qed.
Lemma lem226719 (_4485 : nat) (_4486 : nat) (_4487 : nat) : ((term637 _4485 _4486 _4487) = (term637 _4485 _4486 _4487)) = True.
Proof. exact (@lem226718 (term637 _4485 _4486 _4487)). Qed.
Lemma lem226720 (_4485 : nat) (_4486 : nat) (_4487 : nat) : ((term424 _4487 _4485 _4486) = (term637 _4485 _4486 _4487)) = True.
Proof. exact (TRANS (@lem226715 _4485 _4486 _4487) (@lem226719 _4485 _4486 _4487)). Qed.
Lemma lem226721 (_4485 : nat) (_4486 : nat) (_4487 : nat) : True = ((term424 _4487 _4485 _4486) = (term637 _4485 _4486 _4487)).
Proof. exact (SYM (@lem226720 _4485 _4486 _4487)). Qed.
Lemma lem226722 (_4485 : nat) (_4486 : nat) (_4487 : nat) : (term424 _4487 _4485 _4486) = (term637 _4485 _4486 _4487).
Proof. exact (EQ_MP (@lem226721 _4485 _4486 _4487) (@lem0)). Qed.
Lemma lem226723 (_4485 : nat) (_4486 : nat) (_4487 : nat) (h1 : term402) : term637 _4485 _4486 _4487.
Proof. exact (EQ_MP (@lem226722 _4485 _4486 _4487) (@lem226273 _4487 _4485 _4486 h1)). Qed.
Lemma lem226725 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem226726 (_4487 : nat) (_4485 : nat) (_4486 : nat) : (term637 _4485 _4486 _4487) = (term640 _4487 _4485 _4486).
Proof. exact (@lem226725 (term463 _4485 _4486 _4487) (Peano.le _4485 _4486)). Qed.
Lemma lem226728 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem226729 (_4485 : nat) (_4486 : nat) (_4487 : nat) : (term641 _4485 _4486 _4487) = (term396 _4485 _4486 _4487).
Proof. exact (@lem226728 (term396 _4485 _4486 _4487)). Qed.
Lemma lem226730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem226731 (_4485 : nat) (_4486 : nat) (_4487 : nat) : (term642 _4485 _4486 _4487) = (term643 _4485 _4486 _4487).
Proof. exact (MK_COMB (@lem226730) (@lem226729 _4485 _4486 _4487)). Qed.
Lemma lem226732 (_4485 : nat) (_4486 : nat) : (Peano.le _4485 _4486) = (Peano.le _4485 _4486).
Proof. exact (eq_refl (Peano.le _4485 _4486)). Qed.
Lemma lem226733 (_4487 : nat) (_4485 : nat) (_4486 : nat) : (term640 _4487 _4485 _4486) = (term644 _4487 _4485 _4486).
Proof. exact (MK_COMB (@lem226731 _4485 _4486 _4487) (@lem226732 _4485 _4486)). Qed.
Lemma lem226734 (_4487 : nat) (_4485 : nat) (_4486 : nat) : (term637 _4485 _4486 _4487) = (term644 _4487 _4485 _4486).
Proof. exact (TRANS (@lem226726 _4487 _4485 _4486) (@lem226733 _4487 _4485 _4486)). Qed.
Lemma lem226737 (_4487 : nat) (_4485 : nat) (_4486 : nat) (h1 : term402) : term644 _4487 _4485 _4486.
Proof. exact (EQ_MP (@lem226734 _4487 _4485 _4486) (@lem226723 _4485 _4486 _4487 h1)). Qed.
Lemma lem226738 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) : term707 k m n p.
Proof. exact (@lem226737 (term310 m n p) (Nat.mul k n) (term224 m n p) h1). Qed.
Lemma lem226741 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : term354 k m n p.
Proof. exact (@lem226738 k m n p h1 (@lem226694 k m n p h2 h3 h4)). Qed.
Lemma lem226742 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : term708 k m n p.
Proof. exact (fun h0 : term682 k m n p => @lem226741 k m n p h1 h2 h3 h4). Qed.
Lemma lem226744 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226745 (k : nat) (m : nat) (n : nat) (p : nat) : (term708 k m n p) = (term354 k m n p).
Proof. exact (@lem226744 (term354 k m n p)). Qed.
Lemma lem226746 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : term354 k m n p.
Proof. exact (EQ_MP (@lem226745 k m n p) (@lem226742 k m n p h1 h2 h3 h4)). Qed.
Lemma lem226749 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem226751 (k : nat) (m : nat) (n : nat) (p : nat) : (term682 k m n p) = (term709 k m n p).
Proof. exact (@lem226749 (term354 k m n p)). Qed.
Lemma lem226754 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term680 k m n p) : term709 k m n p.
Proof. exact (EQ_MP (@lem226751 k m n p) (@lem226281 k m n p h1)). Qed.
Lemma lem226757 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : False.
Proof. exact (@lem226754 k m n p h4 (@lem226746 k m n p h1 h2 h3 h4)). Qed.
Lemma lem226758 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : term205.
Proof. exact (fun h0 : ~ False => @lem226757 k m n p h1 h2 h3 h4). Qed.
Lemma lem226760 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226761 : term205 = False.
Proof. exact (@lem226760 False). Qed.
Lemma lem226762 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : False.
Proof. exact (EQ_MP (@lem226761) (@lem226758 k m n p h1 h2 h3 h4)). Qed.
Lemma lem226782 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem226783 (_4526 : nat) (_4528 : nat) (h1 : _4526 = _4528) : _4526 = _4528.
Proof. exact (h1). Qed.
Lemma lem226784 (_4527 : nat) (_4529 : nat) (h1 : _4527 = _4529) : _4527 = _4529.
Proof. exact (h1). Qed.
Lemma lem226785 (_4526 : nat) (_4528 : nat) (h1 : _4526 = _4528) : (Peano.le _4526) = (Peano.le _4528).
Proof. exact (MK_COMB (@lem226782) (@lem226783 _4526 _4528 h1)). Qed.
Lemma lem226786 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) (h1 : _4526 = _4528) (h2 : _4527 = _4529) : (Peano.le _4526 _4527) = (Peano.le _4528 _4529).
Proof. exact (MK_COMB (@lem226785 _4526 _4528 h1) (@lem226784 _4527 _4529 h2)). Qed.
Lemma lem226788 (b : Prop) (a : Prop) : term543 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem226789 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : term544 _4528 _4529 _4526 _4527.
Proof. exact (@lem226788 (Peano.le _4528 _4529) (Peano.le _4526 _4527)). Qed.
Lemma lem226790 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) (h1 : _4526 = _4528) (h2 : _4527 = _4529) : term545 _4528 _4529 _4526 _4527.
Proof. exact (@lem226789 _4528 _4529 _4526 _4527 (@lem226786 _4526 _4528 _4527 _4529 h1 h2)). Qed.
Lemma lem226791 (_4529 : nat) (_4527 : nat) (_4526 : nat) (_4528 : nat) (h1 : _4526 = _4528) : term546 _4528 _4529 _4526 _4527.
Proof. exact (fun h0 : _4527 = _4529 => @lem226790 _4526 _4528 _4527 _4529 h1 h0). Qed.
Lemma lem226793 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem226794 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term546 _4528 _4529 _4526 _4527) = (term548 _4528 _4529 _4526 _4527).
Proof. exact (@lem226793 (_4527 = _4529) (term545 _4528 _4529 _4526 _4527)). Qed.
Lemma lem226795 (_4529 : nat) (_4527 : nat) (_4526 : nat) (_4528 : nat) (h1 : _4526 = _4528) : term548 _4528 _4529 _4526 _4527.
Proof. exact (EQ_MP (@lem226794 _4528 _4529 _4526 _4527) (@lem226791 _4529 _4527 _4526 _4528 h1)). Qed.
Lemma lem226796 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : term549 _4528 _4529 _4526 _4527.
Proof. exact (fun h0 : _4526 = _4528 => @lem226795 _4529 _4527 _4526 _4528 h0). Qed.
Lemma lem226798 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem226799 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term549 _4528 _4529 _4526 _4527) = (term550 _4528 _4529 _4526 _4527).
Proof. exact (@lem226798 (_4526 = _4528) (term548 _4528 _4529 _4526 _4527)). Qed.
Lemma lem226800 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : term550 _4528 _4529 _4526 _4527.
Proof. exact (EQ_MP (@lem226799 _4528 _4529 _4526 _4527) (@lem226796 _4528 _4529 _4526 _4527)). Qed.
Lemma lem226862 (x : nat) (y : nat) (z : nat) : term551 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem226864 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem226865 (k : nat) (m : nat) (n : nat) (p : nat) : (term349 k m n p) = (term349 k m n p).
Proof. exact (@lem226864 (term349 k m n p)). Qed.
Lemma lem226866 (k : nat) (m : nat) (n : nat) (p : nat) : term710 k m n p.
Proof. exact (fun h0 : term711 k m n p => @lem226865 k m n p). Qed.
Lemma lem226868 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226869 (k : nat) (m : nat) (n : nat) (p : nat) : (term710 k m n p) = ((term349 k m n p) = (term349 k m n p)).
Proof. exact (@lem226868 ((term349 k m n p) = (term349 k m n p))). Qed.
Lemma lem226870 (k : nat) (m : nat) (n : nat) (p : nat) : (term349 k m n p) = (term349 k m n p).
Proof. exact (EQ_MP (@lem226869 k m n p) (@lem226866 k m n p)). Qed.
Lemma lem226872 (_4491 : nat) (_4490 : nat) (h1 : term364) : (Nat.add _4490 _4491) = (Nat.add _4491 _4490).
Proof. exact (EQ_MP (@lem226238 _4491 _4490) (@lem226237 _4490 _4491 h1)). Qed.
Lemma lem226873 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term342 m n p) = (term687 m n p).
Proof. exact (@lem226872 (term224 m n p) (term310 m n p) h1). Qed.
Lemma lem226874 (m : nat) (n : nat) (p : nat) (h1 : term364) : term688 m n p.
Proof. exact (fun h0 : term689 m n p => @lem226873 m n p h1). Qed.
Lemma lem226876 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226877 (m : nat) (n : nat) (p : nat) : (term688 m n p) = ((term342 m n p) = (term687 m n p)).
Proof. exact (@lem226876 ((term342 m n p) = (term687 m n p))). Qed.
Lemma lem226878 (m : nat) (n : nat) (p : nat) (h1 : term364) : (term342 m n p) = (term687 m n p).
Proof. exact (EQ_MP (@lem226877 m n p) (@lem226874 m n p h1)). Qed.
Lemma lem226880 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : m = (term342 m n p).
Proof. exact (proj1 (@lem225925 k m n p h1)). Qed.
Lemma lem226881 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term692 m n p.
Proof. exact (fun h0 : term693 m n p => @lem226880 k m n p h1). Qed.
Lemma lem226883 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226884 (m : nat) (n : nat) (p : nat) : (term692 m n p) = (m = (term342 m n p)).
Proof. exact (@lem226883 (m = (term342 m n p))). Qed.
Lemma lem226885 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : m = (term342 m n p).
Proof. exact (EQ_MP (@lem226884 m n p) (@lem226881 k m n p h1)). Qed.
Lemma lem226887 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem226888 (m : nat) : m = m.
Proof. exact (@lem226887 m). Qed.
Lemma lem226889 (m : nat) : term164 m.
Proof. exact (fun h0 : term165 m => @lem226888 m). Qed.
Lemma lem226891 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem226892 (m : nat) : (term164 m) = (m = m).
Proof. exact (@lem226891 (m = m)). Qed.
Lemma lem226893 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem226892 m) (@lem226889 m)). Qed.
Lemma lem226911 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem226912 (y : nat) (x : nat) (z : nat) : (term561 x y z) = (term562 y x z).
Proof. exact (@lem226911 (y = z) (term64 x z)). Qed.
Lemma lem226922 (x : nat) (y : nat) : (term563 x y) = (term563 x y).
Proof. exact (eq_refl (term563 x y)). Qed.
Lemma lem226923 (y : nat) (x : nat) (z : nat) : (term551 x y z) = (term564 y x z).
Proof. exact (MK_COMB (@lem226922 x y) (@lem226912 y x z)). Qed.
Lemma lem226927 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem226928 (y : nat) (x : nat) (z : nat) : (term564 y x z) = (term565 y x z).
Proof. exact (@lem226927 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem226950 (y : nat) (x : nat) (z : nat) : (term551 x y z) = (term565 y x z).
Proof. exact (TRANS (@lem226923 y x z) (@lem226928 y x z)). Qed.
Lemma lem226951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem226952 (y : nat) (x : nat) (z : nat) : (term566 x y z) = (term567 y x z).
Proof. exact (MK_COMB (@lem226951) (@lem226950 y x z)). Qed.
Lemma lem226974 (y : nat) (x : nat) (z : nat) : (term565 y x z) = (term565 y x z).
Proof. exact (eq_refl (term565 y x z)). Qed.
Lemma lem226975 (y : nat) (x : nat) (z : nat) : ((term551 x y z) = (term565 y x z)) = ((term565 y x z) = (term565 y x z)).
Proof. exact (MK_COMB (@lem226952 y x z) (@lem226974 y x z)). Qed.
Lemma lem226977 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem226978 (x : Prop) : (x = x) = True.
Proof. exact (@lem226977 Prop x). Qed.
Lemma lem226979 (y : nat) (x : nat) (z : nat) : ((term565 y x z) = (term565 y x z)) = True.
Proof. exact (@lem226978 (term565 y x z)). Qed.
Lemma lem226980 (y : nat) (x : nat) (z : nat) : ((term551 x y z) = (term565 y x z)) = True.
Proof. exact (TRANS (@lem226975 y x z) (@lem226979 y x z)). Qed.
Lemma lem226981 (y : nat) (x : nat) (z : nat) : True = ((term551 x y z) = (term565 y x z)).
Proof. exact (SYM (@lem226980 y x z)). Qed.
Lemma lem226982 (y : nat) (x : nat) (z : nat) : (term551 x y z) = (term565 y x z).
Proof. exact (EQ_MP (@lem226981 y x z) (@lem0)). Qed.
Lemma lem226983 (y : nat) (x : nat) (z : nat) : term565 y x z.
Proof. exact (EQ_MP (@lem226982 y x z) (@lem226862 x y z)). Qed.
Lemma lem226985 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem226986 (x : nat) (y : nat) (z : nat) : (term565 y x z) = (term568 x y z).
Proof. exact (@lem226985 (term569 y x z) (y = z)). Qed.
Lemma lem226988 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem226989 (y : nat) (x : nat) (z : nat) : (term570 y x z) = (term571 y x z).
Proof. exact (@lem226988 (term64 x y) (term64 x z)). Qed.
Lemma lem226991 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem226992 (x : nat) (y : nat) : (term170 x y) = (x = y).
Proof. exact (@lem226991 (x = y)). Qed.
Lemma lem226993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem226994 (x : nat) (y : nat) : (term572 x y) = (term573 x y).
Proof. exact (MK_COMB (@lem226993) (@lem226992 x y)). Qed.
Lemma lem226996 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem226997 (x : nat) (z : nat) : (term170 x z) = (x = z).
Proof. exact (@lem226996 (x = z)). Qed.
Lemma lem226998 (y : nat) (x : nat) (z : nat) : (term571 y x z) = (term574 y x z).
Proof. exact (MK_COMB (@lem226994 x y) (@lem226997 x z)). Qed.
Lemma lem226999 (y : nat) (x : nat) (z : nat) : (term570 y x z) = (term574 y x z).
Proof. exact (TRANS (@lem226989 y x z) (@lem226998 y x z)). Qed.
Lemma lem227000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem227001 (y : nat) (x : nat) (z : nat) : (term575 y x z) = (term576 y x z).
Proof. exact (MK_COMB (@lem227000) (@lem226999 y x z)). Qed.
Lemma lem227002 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem227003 (x : nat) (y : nat) (z : nat) : (term568 x y z) = (term577 x y z).
Proof. exact (MK_COMB (@lem227001 y x z) (@lem227002 y z)). Qed.
Lemma lem227004 (x : nat) (y : nat) (z : nat) : (term565 y x z) = (term577 x y z).
Proof. exact (TRANS (@lem226986 x y z) (@lem227003 x y z)). Qed.
Lemma lem227006 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term712 n p m.
Proof. exact (conj (@lem226885 k m n p h1) (@lem226893 m)). Qed.
Lemma lem227008 (x : nat) (y : nat) (z : nat) : term577 x y z.
Proof. exact (EQ_MP (@lem227004 x y z) (@lem226983 y x z)). Qed.
Lemma lem227009 (n : nat) (p : nat) (m : nat) : term713 n p m.
Proof. exact (@lem227008 m (term342 m n p) m). Qed.
Lemma lem227012 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : (term342 m n p) = m.
Proof. exact (@lem227009 n p m (@lem227006 k m n p h1)). Qed.
Lemma lem227013 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term714 n p m.
Proof. exact (fun h0 : term715 n p m => @lem227012 k m n p h1). Qed.
Lemma lem227015 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem227016 (n : nat) (p : nat) (m : nat) : (term714 n p m) = ((term342 m n p) = m).
Proof. exact (@lem227015 ((term342 m n p) = m)). Qed.
Lemma lem227017 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : (term342 m n p) = m.
Proof. exact (EQ_MP (@lem227016 n p m) (@lem227013 k m n p h1)). Qed.
Lemma lem227018 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) : term716 n p m.
Proof. exact (conj (@lem226878 m n p h1) (@lem227017 k m n p h2)). Qed.
Lemma lem227020 (x : nat) (y : nat) (z : nat) : term577 x y z.
Proof. exact (EQ_MP (@lem227004 x y z) (@lem226983 y x z)). Qed.
Lemma lem227021 (n : nat) (p : nat) (m : nat) : term717 n p m.
Proof. exact (@lem227020 (term342 m n p) (term687 m n p) m). Qed.
Lemma lem227024 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) : (term687 m n p) = m.
Proof. exact (@lem227021 n p m (@lem227018 k m n p h1 h2)). Qed.
Lemma lem227025 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) : term718 n p m.
Proof. exact (fun h0 : term719 n p m => @lem227024 k m n p h1 h2). Qed.
Lemma lem227027 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem227028 (n : nat) (p : nat) (m : nat) : (term718 n p m) = ((term687 m n p) = m).
Proof. exact (@lem227027 ((term687 m n p) = m)). Qed.
Lemma lem227029 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term364) (h2 : term652 k m n p) : (term687 m n p) = m.
Proof. exact (EQ_MP (@lem227028 n p m) (@lem227025 k m n p h1 h2)). Qed.
Lemma lem227031 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term681 k m n p) : term354 k m n p.
Proof. exact (proj2 (@lem225929 k m n p h1)). Qed.
Lemma lem227032 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term681 k m n p) : term708 k m n p.
Proof. exact (fun h0 : term682 k m n p => @lem227031 k m n p h1). Qed.
Lemma lem227034 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem227035 (k : nat) (m : nat) (n : nat) (p : nat) : (term708 k m n p) = (term354 k m n p).
Proof. exact (@lem227034 (term354 k m n p)). Qed.
Lemma lem227036 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term681 k m n p) : term354 k m n p.
Proof. exact (EQ_MP (@lem227035 k m n p) (@lem227032 k m n p h1)). Qed.
Lemma lem227038 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem227039 (_4492 : nat) (_4493 : nat) (_4494 : nat) : (term420 _4494 _4492 _4493) = (term587 _4492 _4493 _4494).
Proof. exact (@lem227038 (term162 _4492 _4493) (term396 _4492 _4493 _4494)). Qed.
Lemma lem227041 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem227042 (_4492 : nat) (_4493 : nat) : (term180 _4492 _4493) = (Peano.le _4492 _4493).
Proof. exact (@lem227041 (Peano.le _4492 _4493)). Qed.
Lemma lem227043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem227044 (_4492 : nat) (_4493 : nat) : (term181 _4492 _4493) = (term182 _4492 _4493).
Proof. exact (MK_COMB (@lem227043) (@lem227042 _4492 _4493)). Qed.
Lemma lem227045 (_4492 : nat) (_4493 : nat) (_4494 : nat) : (term396 _4492 _4493 _4494) = (term396 _4492 _4493 _4494).
Proof. exact (eq_refl (term396 _4492 _4493 _4494)). Qed.
Lemma lem227046 (_4492 : nat) (_4493 : nat) (_4494 : nat) : (term587 _4492 _4493 _4494) = (term588 _4492 _4493 _4494).
Proof. exact (MK_COMB (@lem227044 _4492 _4493) (@lem227045 _4492 _4493 _4494)). Qed.
Lemma lem227047 (_4492 : nat) (_4493 : nat) (_4494 : nat) : (term420 _4494 _4492 _4493) = (term588 _4492 _4493 _4494).
Proof. exact (TRANS (@lem227039 _4492 _4493 _4494) (@lem227046 _4492 _4493 _4494)). Qed.
Lemma lem227050 (_4492 : nat) (_4493 : nat) (_4494 : nat) (h1 : term402) : term588 _4492 _4493 _4494.
Proof. exact (EQ_MP (@lem227047 _4492 _4493 _4494) (@lem226291 _4494 _4492 _4493 h1)). Qed.
Lemma lem227051 (k : nat) (m : nat) (n : nat) (p : nat) (_4494 : nat) (h1 : term402) : term720 k m n p _4494.
Proof. exact (@lem227050 (Nat.mul k n) (term224 m n p) _4494 h1). Qed.
Lemma lem227054 (_4494 : nat) (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term681 k m n p) : term721 k m n p _4494.
Proof. exact (@lem227051 k m n p _4494 h1 (@lem227036 k m n p h2)). Qed.
Lemma lem227055 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term681 k m n p) : term704 k m n p.
Proof. exact (@lem227054 (term310 m n p) k m n p h1 h2). Qed.
Lemma lem227056 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term681 k m n p) : term705 k m n p.
Proof. exact (fun h0 : term706 k m n p => @lem227055 k m n p h1 h2). Qed.
Lemma lem227058 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem227059 (k : nat) (m : nat) (n : nat) (p : nat) : (term705 k m n p) = (term704 k m n p).
Proof. exact (@lem227058 (term704 k m n p)). Qed.
Lemma lem227060 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term681 k m n p) : term704 k m n p.
Proof. exact (EQ_MP (@lem227059 k m n p) (@lem227056 k m n p h1 h2)). Qed.
Lemma lem227078 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem227079 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term548 _4528 _4529 _4526 _4527) = (term594 _4528 _4529 _4526 _4527).
Proof. exact (@lem227078 (Peano.le _4528 _4529) (term64 _4527 _4529) (term162 _4526 _4527)). Qed.
Lemma lem227093 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem227094 (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term595 _4529 _4526 _4527) = (term596 _4526 _4527 _4529).
Proof. exact (@lem227093 (term162 _4526 _4527) (term64 _4527 _4529)). Qed.
Lemma lem227102 (_4528 : nat) (_4529 : nat) : (term597 _4528 _4529) = (term597 _4528 _4529).
Proof. exact (eq_refl (term597 _4528 _4529)). Qed.
Lemma lem227103 (_4528 : nat) (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term594 _4528 _4529 _4526 _4527) = (term598 _4528 _4526 _4527 _4529).
Proof. exact (MK_COMB (@lem227102 _4528 _4529) (@lem227094 _4526 _4527 _4529)). Qed.
Lemma lem227114 (_4528 : nat) (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term548 _4528 _4529 _4526 _4527) = (term598 _4528 _4526 _4527 _4529).
Proof. exact (TRANS (@lem227079 _4528 _4529 _4526 _4527) (@lem227103 _4528 _4526 _4527 _4529)). Qed.
Lemma lem227115 (_4526 : nat) (_4528 : nat) : (term563 _4526 _4528) = (term563 _4526 _4528).
Proof. exact (eq_refl (term563 _4526 _4528)). Qed.
Lemma lem227116 (_4528 : nat) (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term550 _4528 _4529 _4526 _4527) = (term599 _4528 _4526 _4527 _4529).
Proof. exact (MK_COMB (@lem227115 _4526 _4528) (@lem227114 _4528 _4526 _4527 _4529)). Qed.
Lemma lem227120 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem227121 (_4528 : nat) (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term599 _4528 _4526 _4527 _4529) = (term600 _4528 _4526 _4527 _4529).
Proof. exact (@lem227120 (Peano.le _4528 _4529) (term64 _4526 _4528) (term596 _4526 _4527 _4529)). Qed.
Lemma lem227135 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem227136 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term601 _4528 _4526 _4527 _4529) = (term602 _4526 _4528 _4527 _4529).
Proof. exact (@lem227135 (term162 _4526 _4527) (term64 _4526 _4528) (term64 _4527 _4529)). Qed.
Lemma lem227156 (_4528 : nat) (_4529 : nat) : (term597 _4528 _4529) = (term597 _4528 _4529).
Proof. exact (eq_refl (term597 _4528 _4529)). Qed.
Lemma lem227157 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term600 _4528 _4526 _4527 _4529) = (term603 _4526 _4528 _4527 _4529).
Proof. exact (MK_COMB (@lem227156 _4528 _4529) (@lem227136 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227168 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term599 _4528 _4526 _4527 _4529) = (term603 _4526 _4528 _4527 _4529).
Proof. exact (TRANS (@lem227121 _4528 _4526 _4527 _4529) (@lem227157 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227169 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term550 _4528 _4529 _4526 _4527) = (term603 _4526 _4528 _4527 _4529).
Proof. exact (TRANS (@lem227116 _4528 _4526 _4527 _4529) (@lem227168 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem227171 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term604 _4528 _4529 _4526 _4527) = (term605 _4526 _4528 _4527 _4529).
Proof. exact (MK_COMB (@lem227170) (@lem227169 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem227198 (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term595 _4529 _4526 _4527) = (term596 _4526 _4527 _4529).
Proof. exact (@lem227197 (term162 _4526 _4527) (term64 _4527 _4529)). Qed.
Lemma lem227206 (_4526 : nat) (_4528 : nat) : (term563 _4526 _4528) = (term563 _4526 _4528).
Proof. exact (eq_refl (term563 _4526 _4528)). Qed.
Lemma lem227207 (_4528 : nat) (_4526 : nat) (_4527 : nat) (_4529 : nat) : (term606 _4528 _4529 _4526 _4527) = (term601 _4528 _4526 _4527 _4529).
Proof. exact (MK_COMB (@lem227206 _4526 _4528) (@lem227198 _4526 _4527 _4529)). Qed.
Lemma lem227211 (q : Prop) (p : Prop) (r : Prop) : (term31 p q r) = (term31 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem227212 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term601 _4528 _4526 _4527 _4529) = (term602 _4526 _4528 _4527 _4529).
Proof. exact (@lem227211 (term162 _4526 _4527) (term64 _4526 _4528) (term64 _4527 _4529)). Qed.
Lemma lem227232 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term606 _4528 _4529 _4526 _4527) = (term602 _4526 _4528 _4527 _4529).
Proof. exact (TRANS (@lem227207 _4528 _4526 _4527 _4529) (@lem227212 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227233 (_4528 : nat) (_4529 : nat) : (term597 _4528 _4529) = (term597 _4528 _4529).
Proof. exact (eq_refl (term597 _4528 _4529)). Qed.
Lemma lem227234 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : (term607 _4528 _4529 _4526 _4527) = (term603 _4526 _4528 _4527 _4529).
Proof. exact (MK_COMB (@lem227233 _4528 _4529) (@lem227232 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227245 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : ((term550 _4528 _4529 _4526 _4527) = (term607 _4528 _4529 _4526 _4527)) = ((term603 _4526 _4528 _4527 _4529) = (term603 _4526 _4528 _4527 _4529)).
Proof. exact (MK_COMB (@lem227171 _4526 _4528 _4527 _4529) (@lem227234 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227247 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem227248 (x : Prop) : (x = x) = True.
Proof. exact (@lem227247 Prop x). Qed.
Lemma lem227249 (_4526 : nat) (_4528 : nat) (_4527 : nat) (_4529 : nat) : ((term603 _4526 _4528 _4527 _4529) = (term603 _4526 _4528 _4527 _4529)) = True.
Proof. exact (@lem227248 (term603 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227250 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : ((term550 _4528 _4529 _4526 _4527) = (term607 _4528 _4529 _4526 _4527)) = True.
Proof. exact (TRANS (@lem227245 _4526 _4528 _4527 _4529) (@lem227249 _4526 _4528 _4527 _4529)). Qed.
Lemma lem227251 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : True = ((term550 _4528 _4529 _4526 _4527) = (term607 _4528 _4529 _4526 _4527)).
Proof. exact (SYM (@lem227250 _4528 _4529 _4526 _4527)). Qed.
Lemma lem227252 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term550 _4528 _4529 _4526 _4527) = (term607 _4528 _4529 _4526 _4527).
Proof. exact (EQ_MP (@lem227251 _4528 _4529 _4526 _4527) (@lem0)). Qed.
Lemma lem227253 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : term607 _4528 _4529 _4526 _4527.
Proof. exact (EQ_MP (@lem227252 _4528 _4529 _4526 _4527) (@lem226800 _4528 _4529 _4526 _4527)). Qed.
Lemma lem227255 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem227256 (_4526 : nat) (_4527 : nat) (_4528 : nat) (_4529 : nat) : (term607 _4528 _4529 _4526 _4527) = (term608 _4526 _4527 _4528 _4529).
Proof. exact (@lem227255 (term606 _4528 _4529 _4526 _4527) (Peano.le _4528 _4529)). Qed.
Lemma lem227258 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem227259 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term609 _4528 _4529 _4526 _4527) = (term610 _4528 _4529 _4526 _4527).
Proof. exact (@lem227258 (term64 _4526 _4528) (term595 _4529 _4526 _4527)). Qed.
Lemma lem227261 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem227262 (_4526 : nat) (_4528 : nat) : (term170 _4526 _4528) = (_4526 = _4528).
Proof. exact (@lem227261 (_4526 = _4528)). Qed.
Lemma lem227263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227264 (_4526 : nat) (_4528 : nat) : (term572 _4526 _4528) = (term573 _4526 _4528).
Proof. exact (MK_COMB (@lem227263) (@lem227262 _4526 _4528)). Qed.
Lemma lem227266 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem227267 (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term611 _4529 _4526 _4527) = (term612 _4529 _4526 _4527).
Proof. exact (@lem227266 (term64 _4527 _4529) (term162 _4526 _4527)). Qed.
Lemma lem227269 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem227270 (_4527 : nat) (_4529 : nat) : (term170 _4527 _4529) = (_4527 = _4529).
Proof. exact (@lem227269 (_4527 = _4529)). Qed.
Lemma lem227271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227272 (_4527 : nat) (_4529 : nat) : (term572 _4527 _4529) = (term573 _4527 _4529).
Proof. exact (MK_COMB (@lem227271) (@lem227270 _4527 _4529)). Qed.
Lemma lem227274 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem227275 (_4526 : nat) (_4527 : nat) : (term180 _4526 _4527) = (Peano.le _4526 _4527).
Proof. exact (@lem227274 (Peano.le _4526 _4527)). Qed.
Lemma lem227276 (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term612 _4529 _4526 _4527) = (term613 _4529 _4526 _4527).
Proof. exact (MK_COMB (@lem227272 _4527 _4529) (@lem227275 _4526 _4527)). Qed.
Lemma lem227277 (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term611 _4529 _4526 _4527) = (term613 _4529 _4526 _4527).
Proof. exact (TRANS (@lem227267 _4529 _4526 _4527) (@lem227276 _4529 _4526 _4527)). Qed.
Lemma lem227278 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term610 _4528 _4529 _4526 _4527) = (term614 _4528 _4529 _4526 _4527).
Proof. exact (MK_COMB (@lem227264 _4526 _4528) (@lem227277 _4529 _4526 _4527)). Qed.
Lemma lem227279 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term609 _4528 _4529 _4526 _4527) = (term614 _4528 _4529 _4526 _4527).
Proof. exact (TRANS (@lem227259 _4528 _4529 _4526 _4527) (@lem227278 _4528 _4529 _4526 _4527)). Qed.
Lemma lem227280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem227281 (_4528 : nat) (_4529 : nat) (_4526 : nat) (_4527 : nat) : (term615 _4528 _4529 _4526 _4527) = (term616 _4528 _4529 _4526 _4527).
Proof. exact (MK_COMB (@lem227280) (@lem227279 _4528 _4529 _4526 _4527)). Qed.
Lemma lem227282 (_4528 : nat) (_4529 : nat) : (Peano.le _4528 _4529) = (Peano.le _4528 _4529).
Proof. exact (eq_refl (Peano.le _4528 _4529)). Qed.
Lemma lem227283 (_4526 : nat) (_4527 : nat) (_4528 : nat) (_4529 : nat) : (term608 _4526 _4527 _4528 _4529) = (term617 _4526 _4527 _4528 _4529).
Proof. exact (MK_COMB (@lem227281 _4528 _4529 _4526 _4527) (@lem227282 _4528 _4529)). Qed.
Lemma lem227284 (_4526 : nat) (_4527 : nat) (_4528 : nat) (_4529 : nat) : (term607 _4528 _4529 _4526 _4527) = (term617 _4526 _4527 _4528 _4529).
Proof. exact (TRANS (@lem227256 _4526 _4527 _4528 _4529) (@lem227283 _4526 _4527 _4528 _4529)). Qed.
Lemma lem227286 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term722 k m n p.
Proof. exact (conj (@lem227029 k m n p h2 h3) (@lem227060 k m n p h1 h4)). Qed.
Lemma lem227287 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term723 k m n p.
Proof. exact (conj (@lem226870 k m n p) (@lem227286 k m n p h1 h2 h3 h4)). Qed.
Lemma lem227289 (_4526 : nat) (_4527 : nat) (_4528 : nat) (_4529 : nat) : term617 _4526 _4527 _4528 _4529.
Proof. exact (EQ_MP (@lem227284 _4526 _4527 _4528 _4529) (@lem227253 _4528 _4529 _4526 _4527)). Qed.
Lemma lem227290 (k : nat) (n : nat) (p : nat) (m : nat) : term724 k n p m.
Proof. exact (@lem227289 (term349 k m n p) (term687 m n p) (term349 k m n p) m). Qed.
Lemma lem227293 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term351 k n p m.
Proof. exact (@lem227290 k n p m (@lem227287 k m n p h1 h2 h3 h4)). Qed.
Lemma lem227294 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term694 k n p m.
Proof. exact (fun h0 : term683 k n p m => @lem227293 k m n p h1 h2 h3 h4). Qed.
Lemma lem227296 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem227297 (k : nat) (n : nat) (p : nat) (m : nat) : (term694 k n p m) = (term351 k n p m).
Proof. exact (@lem227296 (term351 k n p m)). Qed.
Lemma lem227298 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term351 k n p m.
Proof. exact (EQ_MP (@lem227297 k n p m) (@lem227294 k m n p h1 h2 h3 h4)). Qed.
Lemma lem227301 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem227303 (k : nat) (n : nat) (p : nat) (m : nat) : (term683 k n p m) = (term725 k n p m).
Proof. exact (@lem227301 (term351 k n p m)). Qed.
Lemma lem227306 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term681 k m n p) : term725 k n p m.
Proof. exact (EQ_MP (@lem227303 k n p m) (@lem226303 k m n p h1)). Qed.
Lemma lem227309 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : False.
Proof. exact (@lem227306 k m n p h4 (@lem227298 k m n p h1 h2 h3 h4)). Qed.
Lemma lem227310 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term205.
Proof. exact (fun h0 : ~ False => @lem227309 k m n p h1 h2 h3 h4). Qed.
Lemma lem227312 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem227313 : term205 = False.
Proof. exact (@lem227312 False). Qed.
Lemma lem227314 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : False.
Proof. exact (EQ_MP (@lem227313) (@lem227310 k m n p h1 h2 h3 h4)). Qed.
Lemma lem227315 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : term364 = False.
Proof. exact (prop_ext (fun h5 : term364 => @lem227314 k m n p h1 h2 h3 h4) (fun h5 : False => @lem226085 h2)). Qed.
Lemma lem227316 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term681 k m n p) : False.
Proof. exact (EQ_MP (@lem227315 k m n p h1 h2 h3 h4) (@lem226085 h2)). Qed.
Lemma lem227317 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : term364 = False.
Proof. exact (prop_ext (fun h5 : term364 => @lem226762 k m n p h1 h2 h3 h4) (fun h5 : False => @lem225953 h2)). Qed.
Lemma lem227318 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) (h4 : term680 k m n p) : False.
Proof. exact (EQ_MP (@lem227317 k m n p h1 h2 h3 h4) (@lem225953 h2)). Qed.
Lemma lem227319 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) : False.
Proof. exact (or_elim (@lem225924 k m n p h3) (fun h0 : term680 k m n p => @lem227318 k m n p h1 h2 h3 h0) (fun h0 : term681 k m n p => @lem227316 k m n p h1 h2 h3 h0)). Qed.
Lemma lem227320 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) : term364 = False.
Proof. exact (prop_ext (fun h4 : term364 => @lem227319 k m n p h1 h2 h3) (fun h4 : False => @lem225921 h2)). Qed.
Lemma lem227321 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) : False.
Proof. exact (EQ_MP (@lem227320 k m n p h1 h2 h3) (@lem225921 h2)). Qed.
Lemma lem227322 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) : term364 = False.
Proof. exact (prop_ext (fun h4 : term364 => @lem227321 k m n p h1 h2 h3) (fun h4 : False => @lem225651 h2)). Qed.
Lemma lem227323 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term364) (h3 : term652 k m n p) : False.
Proof. exact (EQ_MP (@lem227322 k m n p h1 h2 h3) (@lem225651 h2)). Qed.
Lemma lem227324 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term652 k m n p) : term362.
Proof. exact (fun h0 : term364 => @lem227323 k m n p h1 h0 h2). Qed.
Lemma lem227325 : term362 = term363.
Proof. exact (@lem69 term364). Qed.
Lemma lem227326 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term652 k m n p) : term363.
Proof. exact (EQ_MP (@lem227325) (@lem227324 k m n p h1 h2)). Qed.
Lemma lem227327 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term402) (h2 : term652 k m n p) : term367.
Proof. exact (fun h0 : term395 => @lem227326 k m n p h1 h2). Qed.
Lemma lem227328 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term370.
Proof. exact (fun h0 : term402 => @lem227327 k m n p h0 h1). Qed.
Lemma lem227329 (k : nat) (m : nat) (n : nat) (p : nat) : term658 k m n p.
Proof. exact (fun h0 : term652 k m n p => @lem227328 k m n p h0). Qed.
Lemma lem227334 (m : nat) (n : nat) (p : nat) : term662 m n p.
Proof. exact (fun k : nat => @lem227329 k m n p). Qed.
Lemma lem227339 (n : nat) (p : nat) : term666 n p.
Proof. exact (fun m : nat => @lem227334 m n p). Qed.
Lemma lem227344 (p : nat) : term670 p.
Proof. exact (fun n : nat => @lem227339 n p). Qed.
Lemma lem227349 : term674.
Proof. exact (fun p : nat => @lem227344 p). Qed.
Lemma lem227350 : term673.
Proof. exact (EQ_MP (@lem225136) (@lem227349)). Qed.
Lemma lem227351 (p : nat) : term726 p.
Proof. exact (@lem227350 p). Qed.
Lemma lem227352 (p : nat) : (term726 p) = (term669 p).
Proof. exact (eq_refl (term726 p)). Qed.
Lemma lem227353 (p : nat) : term669 p.
Proof. exact (EQ_MP (@lem227352 p) (@lem227351 p)). Qed.
Lemma lem227354 (p : nat) (n : nat) : term727 p n.
Proof. exact (@lem227353 p n). Qed.
Lemma lem227355 (n : nat) (p : nat) : (term727 p n) = (term665 n p).
Proof. exact (eq_refl (term727 p n)). Qed.
Lemma lem227356 (n : nat) (p : nat) : term665 n p.
Proof. exact (EQ_MP (@lem227355 n p) (@lem227354 p n)). Qed.
Lemma lem227357 (n : nat) (p : nat) (m : nat) : term728 n p m.
Proof. exact (@lem227356 n p m). Qed.
Lemma lem227358 (m : nat) (n : nat) (p : nat) : (term728 n p m) = (term661 m n p).
Proof. exact (eq_refl (term728 n p m)). Qed.
Lemma lem227359 (m : nat) (n : nat) (p : nat) : term661 m n p.
Proof. exact (EQ_MP (@lem227358 m n p) (@lem227357 n p m)). Qed.
Lemma lem227360 (m : nat) (n : nat) (p : nat) (k : nat) : term729 m n p k.
Proof. exact (@lem227359 m n p k). Qed.
Lemma lem227361 (k : nat) (m : nat) (n : nat) (p : nat) : (term729 m n p k) = (term653 k m n p).
Proof. exact (eq_refl (term729 m n p k)). Qed.
Lemma lem227362 (k : nat) (m : nat) (n : nat) (p : nat) : term653 k m n p.
Proof. exact (EQ_MP (@lem227361 k m n p) (@lem227360 m n p k)). Qed.
Lemma lem227364 (k : nat) (m : nat) (n : nat) (p : nat) : term653 k m n p.
Proof. exact (@lem224889 k m n p (@lem227362 k m n p)). Qed.
Lemma lem227365 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term369.
Proof. exact (@lem227364 k m n p (@lem224874 k m n p h1)). Qed.
Lemma lem227366 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term366.
Proof. exact (@lem227365 k m n p h1 (@lem100973)). Qed.
Lemma lem227367 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : term362.
Proof. exact (@lem227366 k m n p h1 (@lem81820)). Qed.
Lemma lem227368 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : False.
Proof. exact (@lem227367 k m n p h1 (@lem77775)). Qed.
Lemma lem227369 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : (term652 k m n p) = False.
Proof. exact (prop_ext (fun h2 : term652 k m n p => @lem227368 k m n p h1) (fun h2 : False => @lem224874 k m n p h1)). Qed.
Lemma lem227370 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term652 k m n p) : False.
Proof. exact (EQ_MP (@lem227369 k m n p h1) (@lem224874 k m n p h1)). Qed.
Lemma lem227371 (k : nat) (m : nat) (n : nat) (p : nat) : term651 k m n p.
Proof. exact (fun h0 : term652 k m n p => @lem227370 k m n p h0). Qed.
Lemma lem227372 (k : nat) (m : nat) (n : nat) (p : nat) : term355 k m n p.
Proof. exact (EQ_MP (@lem224873 k m n p) (@lem227371 k m n p)). Qed.
Lemma lem227373 (k : nat) (m : nat) (n : nat) (p : nat) : term323 k m n p.
Proof. exact (EQ_MP (@lem222386 k m n p) (@lem227372 k m n p)). Qed.
Lemma lem227374 (k : nat) (p : nat) (m : nat) (n : nat) : term252 k p m n.
Proof. exact (EQ_MP (@lem222278 k p m n) (@lem224869 k p m n)). Qed.
Lemma lem227375 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term322 k m p n.
Proof. exact (EQ_MP (@lem222240 k m n p h1 h2) (@lem227373 k m n p)). Qed.
Lemma lem227376 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term250 k p m n) = (term243 k m p n).
Proof. exact (@lem227375 k m n p h1 h2 (@lem220370 m n p)). Qed.
Lemma lem227377 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 p) : term251 k p m n.
Proof. exact (EQ_MP (@lem221967 k m n p h1) (@lem227374 k p m n)). Qed.
Lemma lem227378 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term242 k m n p) = (term250 k p m n).
Proof. exact (@lem227377 k m n p h1 (@lem220376 m n p)). Qed.
Lemma lem227379 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term730 k m p n.
Proof. exact (conj (@lem227378 k m n p h2) (@lem227376 k m n p h1 h2)). Qed.
Lemma lem227380 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term731 k m p n.
Proof. exact (ex_intro (term732 k m p n) (term250 k p m n) (@lem227379 k m n p h1 h2)). Qed.
Lemma lem227381 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term242 k m n p) = (term243 k m p n).
Proof. exact (@lem221905 k m p n (@lem227380 k m n p h1 h2)). Qed.
Lemma lem227386 (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : term733 m p n.
Proof. exact (fun k : nat => @lem227381 k m n p h1 h2). Qed.
Lemma lem227388 (m : nat) (n : nat) (p : nat) (h1 : term212 n) (h2 : term212 p) : (term220 m n p) = (term226 m p n).
Proof. exact (@lem221901 m p n (@lem227386 m n p h1 h2)). Qed.
Lemma lem227390 (m : nat) (n : nat) (p : nat) (h1 : term212 p) : (term220 m n p) = (term226 m p n).
Proof. exact (or_elim (@lem221590 n) (fun h0 : n = (NUMERAL 0) => @lem221828 m p n h0) (fun h0 : term212 n => @lem227388 m n p h0 h1)). Qed.
Lemma lem227391 (m : nat) (p : nat) (n : nat) : (term220 m n p) = (term226 m p n).
Proof. exact (or_elim (@lem221595 p) (fun h0 : p = (NUMERAL 0) => @lem221672 m n p h0) (fun h0 : term212 p => @lem227390 m n p h0)). Qed.
Lemma lem227396 (m : nat) (n : nat) : term734 m n.
Proof. exact (fun p : nat => @lem227391 m p n). Qed.
Lemma lem227401 (m : nat) : term735 m.
Proof. exact (fun n : nat => @lem227396 m n). Qed.
Lemma lem227406 : term736.
Proof. exact (fun m : nat => @lem227401 m). Qed.
