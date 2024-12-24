Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WLOG_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LE_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem108260 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem108261 (P : type1605) : (term1 P) = (term2 P).
Proof. exact (@lem108260 (term1 P)). Qed.
Lemma lem108262 (P : type1605) : (term2 P) = (term1 P).
Proof. exact (SYM (@lem108261 P)). Qed.
Lemma lem108263 (P : type1605) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem108266 (P : type1605) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem108267 (P : type1605) : term5 P.
Proof. exact (fun h0 : term4 P => @lem108266 P h0). Qed.
Lemma lem108268 (P : type1605) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem108269 (P : type1605) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem108270 (P : type1605) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem108268 P h2 (@lem108269 P h1)). Qed.
Lemma lem108271 (P : type1605) (h1 : term4 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem108270 P h1 h0). Qed.
Lemma lem108272 (P : type1605) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem108273 (P : type1605) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem108271 P h1 (@lem108272 P h2)). Qed.
Lemma lem108274 (P : type1605) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term4 P => @lem108273 P h0 h1). Qed.
Lemma lem108275 (P : type1605) : term7 P.
Proof. exact (fun h0 : term5 P => @lem108274 P h0). Qed.
Lemma lem108278 (P : type1605) : term5 P.
Proof. exact (@lem108275 P (@lem108267 P)). Qed.
Lemma lem108316 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem108317 : term8 = term9.
Proof. exact (@lem108316 term10). Qed.
Lemma lem108372 (P : type1605) : (term11 P) = (term11 P).
Proof. exact (eq_refl (term11 P)). Qed.
Lemma lem108373 (P : type1605) : (term4 P) = (term12 P).
Proof. exact (MK_COMB (@lem108372 P) (@lem108317)). Qed.
Lemma lem108376 : term13 = term14.
Proof. exact (fun_ext (fun P : type1605 => @lem108373 P)). Qed.
Lemma lem108377 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem108386 : term15 = term16.
Proof. exact (MK_COMB (@lem108377) (@lem108376)). Qed.
Lemma lem108391 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem108392 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem108391 n m)). Qed.
Lemma lem108393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108394 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem108393) (@lem108392 m)). Qed.
Lemma lem108395 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem108394 m)). Qed.
Lemma lem108396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108397 : term10 = term10.
Proof. exact (MK_COMB (@lem108396) (@lem108395)). Qed.
Lemma lem108398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem108399 : term9 = term9.
Proof. exact (MK_COMB (@lem108398) (@lem108397)). Qed.
Lemma lem108400 (P : type1605) (m : nat) (n : nat) : (P m n) = (P m n).
Proof. exact (eq_refl (P m n)). Qed.
Lemma lem108401 (P : type1605) (m : nat) : (term21 P m) = (term21 P m).
Proof. exact (fun_ext (fun n : nat => @lem108400 P m n)). Qed.
Lemma lem108402 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108403 (P : type1605) (m : nat) : (term22 P m) = (term22 P m).
Proof. exact (MK_COMB (@lem108402) (@lem108401 P m)). Qed.
Lemma lem108404 (P : type1605) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun m : nat => @lem108403 P m)). Qed.
Lemma lem108405 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108406 (P : type1605) : (term24 P) = (term24 P).
Proof. exact (MK_COMB (@lem108405) (@lem108404 P)). Qed.
Lemma lem108411 (P : type1605) (m : nat) (n : nat) : (term25 P m n) = (term25 P m n).
Proof. exact (eq_refl (term25 P m n)). Qed.
Lemma lem108412 (P : type1605) (m : nat) : (term26 P m) = (term26 P m).
Proof. exact (fun_ext (fun n : nat => @lem108411 P m n)). Qed.
Lemma lem108413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108414 (P : type1605) (m : nat) : (term27 P m) = (term27 P m).
Proof. exact (MK_COMB (@lem108413) (@lem108412 P m)). Qed.
Lemma lem108415 (P : type1605) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun m : nat => @lem108414 P m)). Qed.
Lemma lem108416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108417 (P : type1605) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem108416) (@lem108415 P)). Qed.
Lemma lem108422 (P : type1605) (n : nat) (m : nat) : ((P m n) = (P n m)) = ((P m n) = (P n m)).
Proof. exact (eq_refl ((P m n) = (P n m))). Qed.
Lemma lem108423 (P : type1605) (m : nat) : (term30 P m) = (term30 P m).
Proof. exact (fun_ext (fun n : nat => @lem108422 P n m)). Qed.
Lemma lem108424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108425 (P : type1605) (m : nat) : (term31 P m) = (term31 P m).
Proof. exact (MK_COMB (@lem108424) (@lem108423 P m)). Qed.
Lemma lem108426 (P : type1605) : (term32 P) = (term32 P).
Proof. exact (fun_ext (fun m : nat => @lem108425 P m)). Qed.
Lemma lem108427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108428 (P : type1605) : (term33 P) = (term33 P).
Proof. exact (MK_COMB (@lem108427) (@lem108426 P)). Qed.
Lemma lem108429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108430 (P : type1605) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem108429) (@lem108428 P)). Qed.
Lemma lem108431 (P : type1605) : (term35 P) = (term35 P).
Proof. exact (MK_COMB (@lem108430 P) (@lem108417 P)). Qed.
Lemma lem108432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem108433 (P : type1605) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem108432) (@lem108431 P)). Qed.
Lemma lem108434 (P : type1605) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem108433 P) (@lem108406 P)). Qed.
Lemma lem108435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem108436 (P : type1605) : (term3 P) = (term3 P).
Proof. exact (MK_COMB (@lem108435) (@lem108434 P)). Qed.
Lemma lem108437 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem108438 (P : type1605) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem108437) (@lem108436 P)). Qed.
Lemma lem108439 (P : type1605) : (term12 P) = (term12 P).
Proof. exact (MK_COMB (@lem108438 P) (@lem108399)). Qed.
Lemma lem108440 : term14 = term14.
Proof. exact (fun_ext (fun P : type1605 => @lem108439 P)). Qed.
Lemma lem108441 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem108442 : term16 = term16.
Proof. exact (MK_COMB (@lem108441) (@lem108440)). Qed.
Lemma lem108509 : term15 = term16.
Proof. exact (TRANS (@lem108386) (@lem108442)). Qed.
Lemma lem108510 : term16 = term15.
Proof. exact (SYM (@lem108509)). Qed.
Lemma lem108511 (P : type1605) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem108512 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem108527 (P : type1605) (n : nat) (m : nat) : ((P m n) = (P n m)) = (term37 P n m).
Proof. exact (@lem17784 (P m n) (P n m)). Qed.
Lemma lem108528 (P : type1605) (m : nat) : (term30 P m) = (term38 P m).
Proof. exact (fun_ext (fun n : nat => @lem108527 P n m)). Qed.
Lemma lem108529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108530 (P : type1605) (m : nat) : (term31 P m) = (term39 P m).
Proof. exact (MK_COMB (@lem108529) (@lem108528 P m)). Qed.
Lemma lem108531 (P : type1605) : (term32 P) = (term40 P).
Proof. exact (fun_ext (fun m : nat => @lem108530 P m)). Qed.
Lemma lem108532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108533 (P : type1605) : (term33 P) = (term41 P).
Proof. exact (MK_COMB (@lem108532) (@lem108531 P)). Qed.
Lemma lem108540 (P : type1605) (m : nat) (n : nat) : (term25 P m n) = (term42 P m n).
Proof. exact (@lem17265 (Peano.le m n) (P m n)). Qed.
Lemma lem108541 (P : type1605) (m : nat) : (term26 P m) = (term43 P m).
Proof. exact (fun_ext (fun n : nat => @lem108540 P m n)). Qed.
Lemma lem108542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108543 (P : type1605) (m : nat) : (term27 P m) = (term44 P m).
Proof. exact (MK_COMB (@lem108542) (@lem108541 P m)). Qed.
Lemma lem108544 (P : type1605) : (term28 P) = (term45 P).
Proof. exact (fun_ext (fun m : nat => @lem108543 P m)). Qed.
Lemma lem108545 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108546 (P : type1605) : (term29 P) = (term46 P).
Proof. exact (MK_COMB (@lem108545) (@lem108544 P)). Qed.
Lemma lem108547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108548 (P : type1605) : (term34 P) = (term47 P).
Proof. exact (MK_COMB (@lem108547) (@lem108533 P)). Qed.
Lemma lem108549 (P : type1605) : (term35 P) = (term48 P).
Proof. exact (MK_COMB (@lem108548 P) (@lem108546 P)). Qed.
Lemma lem108551 (P : nat -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem108552 (P : type1605) (m : nat) : (term51 P m) = (term52 P m).
Proof. exact (@lem108551 (term21 P m)). Qed.
Lemma lem108553 (P : type1605) (m : nat) (n : nat) : (term53 P m n) = (P m n).
Proof. exact (eq_refl (term53 P m n)). Qed.
Lemma lem108554 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem108556 (P : type1605) (m : nat) (n : nat) : (term54 P m n) = (term55 P m n).
Proof. exact (MK_COMB (@lem108554) (@lem108553 P m n)). Qed.
Lemma lem108557 (P : type1605) (m : nat) : (term56 P m) = (term57 P m).
Proof. exact (fun_ext (fun n : nat => @lem108556 P m n)). Qed.
Lemma lem108558 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108559 (P : type1605) (m : nat) : (term52 P m) = (term58 P m).
Proof. exact (MK_COMB (@lem108558) (@lem108557 P m)). Qed.
Lemma lem108560 (P : type1605) (m : nat) : (term51 P m) = (term58 P m).
Proof. exact (TRANS (@lem108552 P m) (@lem108559 P m)). Qed.
Lemma lem108561 (P : nat -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem108562 (P : type1605) : (term59 P) = (term60 P).
Proof. exact (@lem108561 (term23 P)). Qed.
Lemma lem108563 (P : type1605) (m : nat) : (term61 P m) = (term22 P m).
Proof. exact (eq_refl (term61 P m)). Qed.
Lemma lem108564 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem108565 (P : type1605) (m : nat) : (term62 P m) = (term51 P m).
Proof. exact (MK_COMB (@lem108564) (@lem108563 P m)). Qed.
Lemma lem108566 (P : type1605) (m : nat) : (term62 P m) = (term58 P m).
Proof. exact (TRANS (@lem108565 P m) (@lem108560 P m)). Qed.
Lemma lem108567 (P : type1605) : (term63 P) = (term64 P).
Proof. exact (fun_ext (fun m : nat => @lem108566 P m)). Qed.
Lemma lem108568 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108569 (P : type1605) : (term60 P) = (term65 P).
Proof. exact (MK_COMB (@lem108568) (@lem108567 P)). Qed.
Lemma lem108570 (P : type1605) : (term59 P) = (term65 P).
Proof. exact (TRANS (@lem108562 P) (@lem108569 P)). Qed.
Lemma lem108571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108572 (P : type1605) : (term66 P) = (term67 P).
Proof. exact (MK_COMB (@lem108571) (@lem108549 P)). Qed.
Lemma lem108573 (P : type1605) : (term68 P) = (term69 P).
Proof. exact (MK_COMB (@lem108572 P) (@lem108570 P)). Qed.
Lemma lem108574 (P : type1605) : (term3 P) = (term68 P).
Proof. exact (@lem17362 (term35 P) (term24 P)). Qed.
Lemma lem108575 (P : type1605) : (term3 P) = (term69 P).
Proof. exact (TRANS (@lem108574 P) (@lem108573 P)). Qed.
Lemma lem108581 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem108582 (P : nat -> Prop) (Q : nat -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem108581 nat P Q). Qed.
Lemma lem108583 (P : type1605) (m : nat) : (term74 P m) = (term75 P m).
Proof. exact (@lem108582 (term76 P m) (term77 P m)). Qed.
Lemma lem108584 (P : type1605) (n : nat) (m : nat) : (term78 P m n) = (term79 P n m).
Proof. exact (eq_refl (term78 P m n)). Qed.
Lemma lem108585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108586 (P : type1605) (n : nat) (m : nat) : (term80 P m n) = (term81 P n m).
Proof. exact (MK_COMB (@lem108585) (@lem108584 P n m)). Qed.
Lemma lem108587 (P : type1605) (n : nat) (m : nat) : (term82 P m n) = (term83 P n m).
Proof. exact (eq_refl (term82 P m n)). Qed.
Lemma lem108588 (P : type1605) (n : nat) (m : nat) : (term84 P m n) = (term37 P n m).
Proof. exact (MK_COMB (@lem108586 P n m) (@lem108587 P n m)). Qed.
Lemma lem108589 (P : type1605) (m : nat) : (term85 P m) = (term38 P m).
Proof. exact (fun_ext (fun n : nat => @lem108588 P n m)). Qed.
Lemma lem108590 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108591 (P : type1605) (m : nat) : (term74 P m) = (term39 P m).
Proof. exact (MK_COMB (@lem108590) (@lem108589 P m)). Qed.
Lemma lem108592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem108593 (P : type1605) (m : nat) : (term86 P m) = (term87 P m).
Proof. exact (MK_COMB (@lem108592) (@lem108591 P m)). Qed.
Lemma lem108594 (P : type1605) (n : nat) (m : nat) : (term78 P m n) = (term79 P n m).
Proof. exact (eq_refl (term78 P m n)). Qed.
Lemma lem108595 (P : type1605) (m : nat) : (term88 P m) = (term76 P m).
Proof. exact (fun_ext (fun n : nat => @lem108594 P n m)). Qed.
Lemma lem108596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108597 (P : type1605) (m : nat) : (term89 P m) = (term90 P m).
Proof. exact (MK_COMB (@lem108596) (@lem108595 P m)). Qed.
Lemma lem108598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108599 (P : type1605) (m : nat) : (term91 P m) = (term92 P m).
Proof. exact (MK_COMB (@lem108598) (@lem108597 P m)). Qed.
Lemma lem108600 (P : type1605) (n : nat) (m : nat) : (term82 P m n) = (term83 P n m).
Proof. exact (eq_refl (term82 P m n)). Qed.
Lemma lem108601 (P : type1605) (m : nat) : (term93 P m) = (term77 P m).
Proof. exact (fun_ext (fun n : nat => @lem108600 P n m)). Qed.
Lemma lem108602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108603 (P : type1605) (m : nat) : (term94 P m) = (term95 P m).
Proof. exact (MK_COMB (@lem108602) (@lem108601 P m)). Qed.
Lemma lem108604 (P : type1605) (m : nat) : (term75 P m) = (term96 P m).
Proof. exact (MK_COMB (@lem108599 P m) (@lem108603 P m)). Qed.
Lemma lem108605 (P : type1605) (m : nat) : ((term74 P m) = (term75 P m)) = ((term39 P m) = (term96 P m)).
Proof. exact (MK_COMB (@lem108593 P m) (@lem108604 P m)). Qed.
Lemma lem108606 (P : type1605) (m : nat) : (term39 P m) = (term96 P m).
Proof. exact (EQ_MP (@lem108605 P m) (@lem108583 P m)). Qed.
Lemma lem108703 (P : type1605) : (term40 P) = (term97 P).
Proof. exact (fun_ext (fun m : nat => @lem108606 P m)). Qed.
Lemma lem108704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108705 (P : type1605) : (term41 P) = (term98 P).
Proof. exact (MK_COMB (@lem108704) (@lem108703 P)). Qed.
Lemma lem108707 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem108708 (P : nat -> Prop) (Q : nat -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem108707 nat P Q). Qed.
Lemma lem108709 (P : type1605) : (term99 P) = (term100 P).
Proof. exact (@lem108708 (term101 P) (term102 P)). Qed.
Lemma lem108710 (P : type1605) (m : nat) : (term103 P m) = (term90 P m).
Proof. exact (eq_refl (term103 P m)). Qed.
Lemma lem108711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108712 (P : type1605) (m : nat) : (term104 P m) = (term92 P m).
Proof. exact (MK_COMB (@lem108711) (@lem108710 P m)). Qed.
Lemma lem108713 (P : type1605) (m : nat) : (term105 P m) = (term95 P m).
Proof. exact (eq_refl (term105 P m)). Qed.
Lemma lem108714 (P : type1605) (m : nat) : (term106 P m) = (term96 P m).
Proof. exact (MK_COMB (@lem108712 P m) (@lem108713 P m)). Qed.
Lemma lem108715 (P : type1605) : (term107 P) = (term97 P).
Proof. exact (fun_ext (fun m : nat => @lem108714 P m)). Qed.
Lemma lem108716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108717 (P : type1605) : (term99 P) = (term98 P).
Proof. exact (MK_COMB (@lem108716) (@lem108715 P)). Qed.
Lemma lem108718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem108719 (P : type1605) : (term108 P) = (term109 P).
Proof. exact (MK_COMB (@lem108718) (@lem108717 P)). Qed.
Lemma lem108720 (P : type1605) (m : nat) : (term103 P m) = (term90 P m).
Proof. exact (eq_refl (term103 P m)). Qed.
Lemma lem108721 (P : type1605) : (term110 P) = (term101 P).
Proof. exact (fun_ext (fun m : nat => @lem108720 P m)). Qed.
Lemma lem108722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108723 (P : type1605) : (term111 P) = (term112 P).
Proof. exact (MK_COMB (@lem108722) (@lem108721 P)). Qed.
Lemma lem108724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108725 (P : type1605) : (term113 P) = (term114 P).
Proof. exact (MK_COMB (@lem108724) (@lem108723 P)). Qed.
Lemma lem108726 (P : type1605) (m : nat) : (term105 P m) = (term95 P m).
Proof. exact (eq_refl (term105 P m)). Qed.
Lemma lem108727 (P : type1605) : (term115 P) = (term102 P).
Proof. exact (fun_ext (fun m : nat => @lem108726 P m)). Qed.
Lemma lem108728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108729 (P : type1605) : (term116 P) = (term117 P).
Proof. exact (MK_COMB (@lem108728) (@lem108727 P)). Qed.
Lemma lem108730 (P : type1605) : (term100 P) = (term118 P).
Proof. exact (MK_COMB (@lem108725 P) (@lem108729 P)). Qed.
Lemma lem108731 (P : type1605) : ((term99 P) = (term100 P)) = ((term98 P) = (term118 P)).
Proof. exact (MK_COMB (@lem108719 P) (@lem108730 P)). Qed.
Lemma lem108732 (P : type1605) : (term98 P) = (term118 P).
Proof. exact (EQ_MP (@lem108731 P) (@lem108709 P)). Qed.
Lemma lem108837 (P : type1605) : (term41 P) = (term118 P).
Proof. exact (TRANS (@lem108705 P) (@lem108732 P)). Qed.
Lemma lem108838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108839 (P : type1605) : (term47 P) = (term119 P).
Proof. exact (MK_COMB (@lem108838) (@lem108837 P)). Qed.
Lemma lem108892 (P : type1605) : (term46 P) = (term46 P).
Proof. exact (eq_refl (term46 P)). Qed.
Lemma lem108893 (P : type1605) : (term48 P) = (term120 P).
Proof. exact (MK_COMB (@lem108839 P) (@lem108892 P)). Qed.
Lemma lem108894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem108895 (P : type1605) : (term67 P) = (term121 P).
Proof. exact (MK_COMB (@lem108894) (@lem108893 P)). Qed.
Lemma lem108904 (P : type1605) : (term65 P) = (term65 P).
Proof. exact (eq_refl (term65 P)). Qed.
Lemma lem108905 (P : type1605) : (term69 P) = (term122 P).
Proof. exact (MK_COMB (@lem108895 P) (@lem108904 P)). Qed.
Lemma lem108907 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem108908 (P : Prop) (Q : nat -> Prop) : (term125 P Q) = (term126 P Q).
Proof. exact (@lem108907 nat P Q). Qed.
Lemma lem108909 (P : type1605) : (term127 P) = (term128 P).
Proof. exact (@lem108908 (term120 P) (term64 P)). Qed.
Lemma lem108910 (P : type1605) (m : nat) : (term129 P m) = (term58 P m).
Proof. exact (eq_refl (term129 P m)). Qed.
Lemma lem108911 (P : type1605) : (term130 P) = (term64 P).
Proof. exact (fun_ext (fun m : nat => @lem108910 P m)). Qed.
Lemma lem108912 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108913 (P : type1605) : (term131 P) = (term65 P).
Proof. exact (MK_COMB (@lem108912) (@lem108911 P)). Qed.
Lemma lem108914 (P : type1605) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem108915 (P : type1605) : (term127 P) = (term122 P).
Proof. exact (MK_COMB (@lem108914 P) (@lem108913 P)). Qed.
Lemma lem108916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem108917 (P : type1605) : (term132 P) = (term133 P).
Proof. exact (MK_COMB (@lem108916) (@lem108915 P)). Qed.
Lemma lem108918 (P : type1605) (m : nat) : (term129 P m) = (term58 P m).
Proof. exact (eq_refl (term129 P m)). Qed.
Lemma lem108919 (P : type1605) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem108920 (P : type1605) (m : nat) : (term134 P m) = (term135 P m).
Proof. exact (MK_COMB (@lem108919 P) (@lem108918 P m)). Qed.
Lemma lem108921 (P : type1605) : (term136 P) = (term137 P).
Proof. exact (fun_ext (fun m : nat => @lem108920 P m)). Qed.
Lemma lem108922 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108923 (P : type1605) : (term128 P) = (term138 P).
Proof. exact (MK_COMB (@lem108922) (@lem108921 P)). Qed.
Lemma lem108924 (P : type1605) : ((term127 P) = (term128 P)) = ((term122 P) = (term138 P)).
Proof. exact (MK_COMB (@lem108917 P) (@lem108923 P)). Qed.
Lemma lem108925 (P : type1605) : (term122 P) = (term138 P).
Proof. exact (EQ_MP (@lem108924 P) (@lem108909 P)). Qed.
Lemma lem108927 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem108928 (P : Prop) (Q : nat -> Prop) : (term125 P Q) = (term126 P Q).
Proof. exact (@lem108927 nat P Q). Qed.
Lemma lem108929 (P : type1605) (m : nat) : (term139 P m) = (term140 P m).
Proof. exact (@lem108928 (term120 P) (term57 P m)). Qed.
Lemma lem108930 (P : type1605) (m : nat) (n : nat) : (term141 P m n) = (term55 P m n).
Proof. exact (eq_refl (term141 P m n)). Qed.
Lemma lem108931 (P : type1605) (m : nat) : (term142 P m) = (term57 P m).
Proof. exact (fun_ext (fun n : nat => @lem108930 P m n)). Qed.
Lemma lem108932 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108933 (P : type1605) (m : nat) : (term143 P m) = (term58 P m).
Proof. exact (MK_COMB (@lem108932) (@lem108931 P m)). Qed.
Lemma lem108934 (P : type1605) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem108935 (P : type1605) (m : nat) : (term139 P m) = (term135 P m).
Proof. exact (MK_COMB (@lem108934 P) (@lem108933 P m)). Qed.
Lemma lem108936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem108937 (P : type1605) (m : nat) : (term144 P m) = (term145 P m).
Proof. exact (MK_COMB (@lem108936) (@lem108935 P m)). Qed.
Lemma lem108938 (P : type1605) (m : nat) (n : nat) : (term141 P m n) = (term55 P m n).
Proof. exact (eq_refl (term141 P m n)). Qed.
Lemma lem108939 (P : type1605) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem108940 (P : type1605) (m : nat) (n : nat) : (term146 P m n) = (term147 P m n).
Proof. exact (MK_COMB (@lem108939 P) (@lem108938 P m n)). Qed.
Lemma lem108941 (P : type1605) (m : nat) : (term148 P m) = (term149 P m).
Proof. exact (fun_ext (fun n : nat => @lem108940 P m n)). Qed.
Lemma lem108942 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108943 (P : type1605) (m : nat) : (term140 P m) = (term150 P m).
Proof. exact (MK_COMB (@lem108942) (@lem108941 P m)). Qed.
Lemma lem108944 (P : type1605) (m : nat) : ((term139 P m) = (term140 P m)) = ((term135 P m) = (term150 P m)).
Proof. exact (MK_COMB (@lem108937 P m) (@lem108943 P m)). Qed.
Lemma lem108945 (P : type1605) (m : nat) : (term135 P m) = (term150 P m).
Proof. exact (EQ_MP (@lem108944 P m) (@lem108929 P m)). Qed.
Lemma lem108946 (P : type1605) : (term137 P) = (term151 P).
Proof. exact (fun_ext (fun m : nat => @lem108945 P m)). Qed.
Lemma lem108947 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem108948 (P : type1605) : (term138 P) = (term152 P).
Proof. exact (MK_COMB (@lem108947) (@lem108946 P)). Qed.
Lemma lem108949 (P : type1605) : (term122 P) = (term152 P).
Proof. exact (TRANS (@lem108925 P) (@lem108948 P)). Qed.
Lemma lem108950 (P : type1605) : (term69 P) = (term152 P).
Proof. exact (TRANS (@lem108905 P) (@lem108949 P)). Qed.
Lemma lem108951 (P : type1605) : (term3 P) = (term152 P).
Proof. exact (TRANS (@lem108575 P) (@lem108950 P)). Qed.
Lemma lem108952 (P : type1605) (h1 : term3 P) : term152 P.
Proof. exact (EQ_MP (@lem108951 P) (@lem108511 P h1)). Qed.
Lemma lem108957 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem108958 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem108957 n m)). Qed.
Lemma lem108959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem108960 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem108959) (@lem108958 m)). Qed.
Lemma lem108961 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem108960 m)). Qed.
Lemma lem108962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109019 : term10 = term10.
Proof. exact (MK_COMB (@lem108962) (@lem108961)). Qed.
Lemma lem109020 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem109019) (@lem108512 h1)). Qed.
Lemma lem109021 (P : type1605) (m : nat) (h1 : term150 P m) : term150 P m.
Proof. exact (h1). Qed.
Lemma lem109022 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term147 P m n.
Proof. exact (h1). Qed.
Lemma lem109035 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem109036 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem109035 n m)). Qed.
Lemma lem109037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109038 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem109037) (@lem109036 m)). Qed.
Lemma lem109039 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem109038 m)). Qed.
Lemma lem109040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109041 : term10 = term10.
Proof. exact (MK_COMB (@lem109040) (@lem109039)). Qed.
Lemma lem109042 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem109041) (@lem109020 h1)). Qed.
Lemma lem109049 (P : type1605) (m : nat) (n : nat) : (term55 P m n) = (term55 P m n).
Proof. exact (eq_refl (term55 P m n)). Qed.
Lemma lem109064 (P : type1605) (m : nat) (n : nat) : (term42 P m n) = (term42 P m n).
Proof. exact (eq_refl (term42 P m n)). Qed.
Lemma lem109065 (P : type1605) (m : nat) : (term43 P m) = (term43 P m).
Proof. exact (fun_ext (fun n : nat => @lem109064 P m n)). Qed.
Lemma lem109066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109067 (P : type1605) (m : nat) : (term44 P m) = (term44 P m).
Proof. exact (MK_COMB (@lem109066) (@lem109065 P m)). Qed.
Lemma lem109068 (P : type1605) : (term45 P) = (term45 P).
Proof. exact (fun_ext (fun m : nat => @lem109067 P m)). Qed.
Lemma lem109069 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109070 (P : type1605) : (term46 P) = (term46 P).
Proof. exact (MK_COMB (@lem109069) (@lem109068 P)). Qed.
Lemma lem109085 (P : type1605) (n : nat) (m : nat) : (term83 P n m) = (term83 P n m).
Proof. exact (eq_refl (term83 P n m)). Qed.
Lemma lem109086 (P : type1605) (m : nat) : (term77 P m) = (term77 P m).
Proof. exact (fun_ext (fun n : nat => @lem109085 P n m)). Qed.
Lemma lem109087 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109088 (P : type1605) (m : nat) : (term95 P m) = (term95 P m).
Proof. exact (MK_COMB (@lem109087) (@lem109086 P m)). Qed.
Lemma lem109089 (P : type1605) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun m : nat => @lem109088 P m)). Qed.
Lemma lem109090 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109091 (P : type1605) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem109090) (@lem109089 P)). Qed.
Lemma lem109106 (P : type1605) (n : nat) (m : nat) : (term79 P n m) = (term79 P n m).
Proof. exact (eq_refl (term79 P n m)). Qed.
Lemma lem109107 (P : type1605) (m : nat) : (term76 P m) = (term76 P m).
Proof. exact (fun_ext (fun n : nat => @lem109106 P n m)). Qed.
Lemma lem109108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109109 (P : type1605) (m : nat) : (term90 P m) = (term90 P m).
Proof. exact (MK_COMB (@lem109108) (@lem109107 P m)). Qed.
Lemma lem109110 (P : type1605) : (term101 P) = (term101 P).
Proof. exact (fun_ext (fun m : nat => @lem109109 P m)). Qed.
Lemma lem109111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109112 (P : type1605) : (term112 P) = (term112 P).
Proof. exact (MK_COMB (@lem109111) (@lem109110 P)). Qed.
Lemma lem109113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109114 (P : type1605) : (term114 P) = (term114 P).
Proof. exact (MK_COMB (@lem109113) (@lem109112 P)). Qed.
Lemma lem109115 (P : type1605) : (term118 P) = (term118 P).
Proof. exact (MK_COMB (@lem109114 P) (@lem109091 P)). Qed.
Lemma lem109116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109117 (P : type1605) : (term119 P) = (term119 P).
Proof. exact (MK_COMB (@lem109116) (@lem109115 P)). Qed.
Lemma lem109118 (P : type1605) : (term120 P) = (term120 P).
Proof. exact (MK_COMB (@lem109117 P) (@lem109070 P)). Qed.
Lemma lem109119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109120 (P : type1605) : (term121 P) = (term121 P).
Proof. exact (MK_COMB (@lem109119) (@lem109118 P)). Qed.
Lemma lem109121 (P : type1605) (m : nat) (n : nat) : (term147 P m n) = (term147 P m n).
Proof. exact (MK_COMB (@lem109120 P) (@lem109049 P m n)). Qed.
Lemma lem109122 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term147 P m n.
Proof. exact (EQ_MP (@lem109121 P m n) (@lem109022 P m n h1)). Qed.
Lemma lem109124 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term120 P.
Proof. exact (proj1 (@lem109122 P m n h1)). Qed.
Lemma lem109125 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term46 P.
Proof. exact (proj2 (@lem109124 P m n h1)). Qed.
Lemma lem109126 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term118 P.
Proof. exact (proj1 (@lem109124 P m n h1)). Qed.
Lemma lem109127 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term117 P.
Proof. exact (proj2 (@lem109126 P m n h1)). Qed.
Lemma lem109136 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem109137 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem109136 n m)). Qed.
Lemma lem109138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109139 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem109138) (@lem109137 m)). Qed.
Lemma lem109140 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem109139 m)). Qed.
Lemma lem109141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109143 : term10 = term10.
Proof. exact (MK_COMB (@lem109141) (@lem109140)). Qed.
Lemma lem109144 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem109143) (@lem109042 h1)). Qed.
Lemma lem109156 (P : type1605) (m : nat) (n : nat) : (term42 P m n) = (term42 P m n).
Proof. exact (eq_refl (term42 P m n)). Qed.
Lemma lem109157 (P : type1605) (m : nat) : (term43 P m) = (term43 P m).
Proof. exact (fun_ext (fun n : nat => @lem109156 P m n)). Qed.
Lemma lem109158 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109159 (P : type1605) (m : nat) : (term44 P m) = (term44 P m).
Proof. exact (MK_COMB (@lem109158) (@lem109157 P m)). Qed.
Lemma lem109160 (P : type1605) : (term45 P) = (term45 P).
Proof. exact (fun_ext (fun m : nat => @lem109159 P m)). Qed.
Lemma lem109161 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109163 (P : type1605) : (term46 P) = (term46 P).
Proof. exact (MK_COMB (@lem109161) (@lem109160 P)). Qed.
Lemma lem109164 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term46 P.
Proof. exact (EQ_MP (@lem109163 P) (@lem109125 P m n h1)). Qed.
Lemma lem109188 (P : type1605) (n : nat) (m : nat) : (term83 P n m) = (term83 P n m).
Proof. exact (eq_refl (term83 P n m)). Qed.
Lemma lem109189 (P : type1605) (m : nat) : (term77 P m) = (term77 P m).
Proof. exact (fun_ext (fun n : nat => @lem109188 P n m)). Qed.
Lemma lem109190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109191 (P : type1605) (m : nat) : (term95 P m) = (term95 P m).
Proof. exact (MK_COMB (@lem109190) (@lem109189 P m)). Qed.
Lemma lem109192 (P : type1605) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun m : nat => @lem109191 P m)). Qed.
Lemma lem109193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109195 (P : type1605) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem109193) (@lem109192 P)). Qed.
Lemma lem109196 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term117 P.
Proof. exact (EQ_MP (@lem109195 P) (@lem109127 P m n h1)). Qed.
Lemma lem109197 (_2357 : nat) (h1 : term10) : term153 _2357.
Proof. exact (@lem109144 h1 _2357). Qed.
Lemma lem109198 (_2357 : nat) : (term153 _2357) = (term19 _2357).
Proof. exact (eq_refl (term153 _2357)). Qed.
Lemma lem109199 (_2357 : nat) (h1 : term10) : term19 _2357.
Proof. exact (EQ_MP (@lem109198 _2357) (@lem109197 _2357 h1)). Qed.
Lemma lem109200 (_2357 : nat) (_2358 : nat) (h1 : term10) : term154 _2357 _2358.
Proof. exact (@lem109199 _2357 h1 _2358). Qed.
Lemma lem109201 (_2358 : nat) (_2357 : nat) : (term154 _2357 _2358) = (term17 _2358 _2357).
Proof. exact (eq_refl (term154 _2357 _2358)). Qed.
Lemma lem109203 (_2359 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term155 P _2359.
Proof. exact (@lem109164 P m n h1 _2359). Qed.
Lemma lem109204 (P : type1605) (_2359 : nat) : (term155 P _2359) = (term44 P _2359).
Proof. exact (eq_refl (term155 P _2359)). Qed.
Lemma lem109205 (_2359 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term44 P _2359.
Proof. exact (EQ_MP (@lem109204 P _2359) (@lem109203 _2359 P m n h1)). Qed.
Lemma lem109206 (_2359 : nat) (_2360 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term156 P _2359 _2360.
Proof. exact (@lem109205 _2359 P m n h1 _2360). Qed.
Lemma lem109207 (P : type1605) (_2359 : nat) (_2360 : nat) : (term156 P _2359 _2360) = (term42 P _2359 _2360).
Proof. exact (eq_refl (term156 P _2359 _2360)). Qed.
Lemma lem109215 (_2363 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term105 P _2363.
Proof. exact (@lem109196 P m n h1 _2363). Qed.
Lemma lem109216 (P : type1605) (_2363 : nat) : (term105 P _2363) = (term95 P _2363).
Proof. exact (eq_refl (term105 P _2363)). Qed.
Lemma lem109217 (_2363 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term95 P _2363.
Proof. exact (EQ_MP (@lem109216 P _2363) (@lem109215 _2363 P m n h1)). Qed.
Lemma lem109218 (_2363 : nat) (_2364 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term82 P _2363 _2364.
Proof. exact (@lem109217 _2363 P m n h1 _2364). Qed.
Lemma lem109219 (P : type1605) (_2364 : nat) (_2363 : nat) : (term82 P _2363 _2364) = (term83 P _2364 _2363).
Proof. exact (eq_refl (term82 P _2363 _2364)). Qed.
Lemma lem109226 (_2358 : nat) (_2357 : nat) (h1 : term10) : term17 _2358 _2357.
Proof. exact (EQ_MP (@lem109201 _2358 _2357) (@lem109200 _2357 _2358 h1)). Qed.
Lemma lem109228 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term55 P m n.
Proof. exact (proj2 (@lem109122 P m n h1)). Qed.
Lemma lem109234 (_2359 : nat) (_2360 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term42 P _2359 _2360.
Proof. exact (EQ_MP (@lem109207 P _2359 _2360) (@lem109206 _2359 _2360 P m n h1)). Qed.
Lemma lem109246 (_2364 : nat) (_2363 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term83 P _2364 _2363.
Proof. exact (EQ_MP (@lem109219 P _2364 _2363) (@lem109218 _2363 _2364 P m n h1)). Qed.
Lemma lem109249 (P : type1605) (m : nat) (n : nat) (h1 : term55 P m n) : term55 P m n.
Proof. exact (h1). Qed.
Lemma lem109250 (P : type1605) (m : nat) (n : nat) (h1 : term55 P m n) : term157 P m n.
Proof. exact (fun h0 : P m n => @lem109249 P m n h1). Qed.
Lemma lem109252 (p : Prop) : (term158 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem109253 (P : type1605) (m : nat) (n : nat) : (term157 P m n) = (term55 P m n).
Proof. exact (@lem109252 (P m n)). Qed.
Lemma lem109254 (P : type1605) (m : nat) (n : nat) (h1 : term55 P m n) : term55 P m n.
Proof. exact (EQ_MP (@lem109253 P m n) (@lem109250 P m n h1)). Qed.
Lemma lem109256 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem109259 (P : type1605) (_2359 : nat) (_2360 : nat) : (term42 P _2359 _2360) = (term160 P _2359 _2360).
Proof. exact (@lem109256 (P _2359 _2360) (term161 _2359 _2360)). Qed.
Lemma lem109262 (_2359 : nat) (_2360 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term160 P _2359 _2360.
Proof. exact (EQ_MP (@lem109259 P _2359 _2360) (@lem109234 _2359 _2360 P m n h1)). Qed.
Lemma lem109263 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term160 P m n.
Proof. exact (@lem109262 m n P m n h1). Qed.
Lemma lem109266 (P : type1605) (m : nat) (n : nat) (h1 : term55 P m n) (h2 : term147 P m n) : term161 m n.
Proof. exact (@lem109263 P m n h2 (@lem109254 P m n h1)). Qed.
Lemma lem109267 (P : type1605) (m : nat) (n : nat) (h1 : term55 P m n) (h2 : term147 P m n) : term162 m n.
Proof. exact (fun h0 : Peano.le m n => @lem109266 P m n h1 h2). Qed.
Lemma lem109269 (p : Prop) : (term158 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem109270 (m : nat) (n : nat) : (term162 m n) = (term161 m n).
Proof. exact (@lem109269 (Peano.le m n)). Qed.
Lemma lem109271 (P : type1605) (m : nat) (n : nat) (h1 : term55 P m n) (h2 : term147 P m n) : term161 m n.
Proof. exact (EQ_MP (@lem109270 m n) (@lem109267 P m n h1 h2)). Qed.
Lemma lem109282 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem109283 (_2358 : nat) (_2357 : nat) : (term17 _2357 _2358) = (term17 _2358 _2357).
Proof. exact (@lem109282 (Peano.le _2357 _2358) (Peano.le _2358 _2357)). Qed.
Lemma lem109289 (_2358 : nat) (_2357 : nat) : (term163 _2358 _2357) = (term163 _2358 _2357).
Proof. exact (eq_refl (term163 _2358 _2357)). Qed.
Lemma lem109290 (_2358 : nat) (_2357 : nat) : ((term17 _2358 _2357) = (term17 _2357 _2358)) = ((term17 _2358 _2357) = (term17 _2358 _2357)).
Proof. exact (MK_COMB (@lem109289 _2358 _2357) (@lem109283 _2358 _2357)). Qed.
Lemma lem109292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem109293 (x : Prop) : (x = x) = True.
Proof. exact (@lem109292 Prop x). Qed.
Lemma lem109294 (_2358 : nat) (_2357 : nat) : ((term17 _2358 _2357) = (term17 _2358 _2357)) = True.
Proof. exact (@lem109293 (term17 _2358 _2357)). Qed.
Lemma lem109295 (_2357 : nat) (_2358 : nat) : ((term17 _2358 _2357) = (term17 _2357 _2358)) = True.
Proof. exact (TRANS (@lem109290 _2358 _2357) (@lem109294 _2358 _2357)). Qed.
Lemma lem109296 (_2357 : nat) (_2358 : nat) : True = ((term17 _2358 _2357) = (term17 _2357 _2358)).
Proof. exact (SYM (@lem109295 _2357 _2358)). Qed.
Lemma lem109297 (_2357 : nat) (_2358 : nat) : (term17 _2358 _2357) = (term17 _2357 _2358).
Proof. exact (EQ_MP (@lem109296 _2357 _2358) (@lem0)). Qed.
Lemma lem109298 (_2357 : nat) (_2358 : nat) (h1 : term10) : term17 _2357 _2358.
Proof. exact (EQ_MP (@lem109297 _2357 _2358) (@lem109226 _2358 _2357 h1)). Qed.
Lemma lem109300 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem109303 (_2358 : nat) (_2357 : nat) : (term17 _2357 _2358) = (term164 _2358 _2357).
Proof. exact (@lem109300 (Peano.le _2357 _2358) (Peano.le _2358 _2357)). Qed.
Lemma lem109306 (_2358 : nat) (_2357 : nat) (h1 : term10) : term164 _2358 _2357.
Proof. exact (EQ_MP (@lem109303 _2358 _2357) (@lem109298 _2357 _2358 h1)). Qed.
Lemma lem109307 (n : nat) (m : nat) (h1 : term10) : term164 n m.
Proof. exact (@lem109306 n m h1). Qed.
Lemma lem109310 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : Peano.le n m.
Proof. exact (@lem109307 n m h1 (@lem109271 P m n h2 h3)). Qed.
Lemma lem109311 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : term165 n m.
Proof. exact (fun h0 : term161 n m => @lem109310 P m n h1 h2 h3). Qed.
Lemma lem109313 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem109314 (n : nat) (m : nat) : (term165 n m) = (Peano.le n m).
Proof. exact (@lem109313 (Peano.le n m)). Qed.
Lemma lem109315 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : Peano.le n m.
Proof. exact (EQ_MP (@lem109314 n m) (@lem109311 P m n h1 h2 h3)). Qed.
Lemma lem109321 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem109322 (P : type1605) (_2359 : nat) (_2360 : nat) : (term42 P _2359 _2360) = (term167 P _2359 _2360).
Proof. exact (@lem109321 (P _2359 _2360) (term161 _2359 _2360)). Qed.
Lemma lem109328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem109329 (P : type1605) (_2359 : nat) (_2360 : nat) : (term168 P _2359 _2360) = (term169 P _2359 _2360).
Proof. exact (MK_COMB (@lem109328) (@lem109322 P _2359 _2360)). Qed.
Lemma lem109335 (P : type1605) (_2359 : nat) (_2360 : nat) : (term167 P _2359 _2360) = (term167 P _2359 _2360).
Proof. exact (eq_refl (term167 P _2359 _2360)). Qed.
Lemma lem109336 (P : type1605) (_2359 : nat) (_2360 : nat) : ((term42 P _2359 _2360) = (term167 P _2359 _2360)) = ((term167 P _2359 _2360) = (term167 P _2359 _2360)).
Proof. exact (MK_COMB (@lem109329 P _2359 _2360) (@lem109335 P _2359 _2360)). Qed.
Lemma lem109338 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem109339 (x : Prop) : (x = x) = True.
Proof. exact (@lem109338 Prop x). Qed.
Lemma lem109340 (P : type1605) (_2359 : nat) (_2360 : nat) : ((term167 P _2359 _2360) = (term167 P _2359 _2360)) = True.
Proof. exact (@lem109339 (term167 P _2359 _2360)). Qed.
Lemma lem109341 (P : type1605) (_2359 : nat) (_2360 : nat) : ((term42 P _2359 _2360) = (term167 P _2359 _2360)) = True.
Proof. exact (TRANS (@lem109336 P _2359 _2360) (@lem109340 P _2359 _2360)). Qed.
Lemma lem109342 (P : type1605) (_2359 : nat) (_2360 : nat) : True = ((term42 P _2359 _2360) = (term167 P _2359 _2360)).
Proof. exact (SYM (@lem109341 P _2359 _2360)). Qed.
Lemma lem109343 (P : type1605) (_2359 : nat) (_2360 : nat) : (term42 P _2359 _2360) = (term167 P _2359 _2360).
Proof. exact (EQ_MP (@lem109342 P _2359 _2360) (@lem0)). Qed.
Lemma lem109344 (_2359 : nat) (_2360 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term167 P _2359 _2360.
Proof. exact (EQ_MP (@lem109343 P _2359 _2360) (@lem109234 _2359 _2360 P m n h1)). Qed.
Lemma lem109346 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem109347 (P : type1605) (_2359 : nat) (_2360 : nat) : (term167 P _2359 _2360) = (term170 P _2359 _2360).
Proof. exact (@lem109346 (term161 _2359 _2360) (P _2359 _2360)). Qed.
Lemma lem109349 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem109350 (_2359 : nat) (_2360 : nat) : (term172 _2359 _2360) = (Peano.le _2359 _2360).
Proof. exact (@lem109349 (Peano.le _2359 _2360)). Qed.
Lemma lem109351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem109352 (_2359 : nat) (_2360 : nat) : (term173 _2359 _2360) = (term174 _2359 _2360).
Proof. exact (MK_COMB (@lem109351) (@lem109350 _2359 _2360)). Qed.
Lemma lem109353 (P : type1605) (_2359 : nat) (_2360 : nat) : (P _2359 _2360) = (P _2359 _2360).
Proof. exact (eq_refl (P _2359 _2360)). Qed.
Lemma lem109354 (P : type1605) (_2359 : nat) (_2360 : nat) : (term170 P _2359 _2360) = (term25 P _2359 _2360).
Proof. exact (MK_COMB (@lem109352 _2359 _2360) (@lem109353 P _2359 _2360)). Qed.
Lemma lem109355 (P : type1605) (_2359 : nat) (_2360 : nat) : (term167 P _2359 _2360) = (term25 P _2359 _2360).
Proof. exact (TRANS (@lem109347 P _2359 _2360) (@lem109354 P _2359 _2360)). Qed.
Lemma lem109358 (_2359 : nat) (_2360 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term25 P _2359 _2360.
Proof. exact (EQ_MP (@lem109355 P _2359 _2360) (@lem109344 _2359 _2360 P m n h1)). Qed.
Lemma lem109359 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term25 P n m.
Proof. exact (@lem109358 n m P m n h1). Qed.
Lemma lem109362 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : P n m.
Proof. exact (@lem109359 P m n h3 (@lem109315 P m n h1 h2 h3)). Qed.
Lemma lem109363 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : term175 P n m.
Proof. exact (fun h0 : term55 P n m => @lem109362 P m n h1 h2 h3). Qed.
Lemma lem109365 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem109366 (P : type1605) (n : nat) (m : nat) : (term175 P n m) = (P n m).
Proof. exact (@lem109365 (P n m)). Qed.
Lemma lem109367 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : P n m.
Proof. exact (EQ_MP (@lem109366 P n m) (@lem109363 P m n h1 h2 h3)). Qed.
Lemma lem109373 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem109374 (P : type1605) (_2363 : nat) (_2364 : nat) : (term83 P _2364 _2363) = (term79 P _2363 _2364).
Proof. exact (@lem109373 (P _2364 _2363) (term55 P _2363 _2364)). Qed.
Lemma lem109380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem109381 (P : type1605) (_2363 : nat) (_2364 : nat) : (term176 P _2364 _2363) = (term177 P _2363 _2364).
Proof. exact (MK_COMB (@lem109380) (@lem109374 P _2363 _2364)). Qed.
Lemma lem109387 (P : type1605) (_2363 : nat) (_2364 : nat) : (term79 P _2363 _2364) = (term79 P _2363 _2364).
Proof. exact (eq_refl (term79 P _2363 _2364)). Qed.
Lemma lem109388 (P : type1605) (_2363 : nat) (_2364 : nat) : ((term83 P _2364 _2363) = (term79 P _2363 _2364)) = ((term79 P _2363 _2364) = (term79 P _2363 _2364)).
Proof. exact (MK_COMB (@lem109381 P _2363 _2364) (@lem109387 P _2363 _2364)). Qed.
Lemma lem109390 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem109391 (x : Prop) : (x = x) = True.
Proof. exact (@lem109390 Prop x). Qed.
Lemma lem109392 (P : type1605) (_2363 : nat) (_2364 : nat) : ((term79 P _2363 _2364) = (term79 P _2363 _2364)) = True.
Proof. exact (@lem109391 (term79 P _2363 _2364)). Qed.
Lemma lem109393 (P : type1605) (_2363 : nat) (_2364 : nat) : ((term83 P _2364 _2363) = (term79 P _2363 _2364)) = True.
Proof. exact (TRANS (@lem109388 P _2363 _2364) (@lem109392 P _2363 _2364)). Qed.
Lemma lem109394 (P : type1605) (_2363 : nat) (_2364 : nat) : True = ((term83 P _2364 _2363) = (term79 P _2363 _2364)).
Proof. exact (SYM (@lem109393 P _2363 _2364)). Qed.
Lemma lem109395 (P : type1605) (_2363 : nat) (_2364 : nat) : (term83 P _2364 _2363) = (term79 P _2363 _2364).
Proof. exact (EQ_MP (@lem109394 P _2363 _2364) (@lem0)). Qed.
Lemma lem109396 (_2363 : nat) (_2364 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term79 P _2363 _2364.
Proof. exact (EQ_MP (@lem109395 P _2363 _2364) (@lem109246 _2364 _2363 P m n h1)). Qed.
Lemma lem109398 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem109399 (P : type1605) (_2364 : nat) (_2363 : nat) : (term79 P _2363 _2364) = (term178 P _2364 _2363).
Proof. exact (@lem109398 (term55 P _2363 _2364) (P _2364 _2363)). Qed.
Lemma lem109401 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem109402 (P : type1605) (_2363 : nat) (_2364 : nat) : (term179 P _2363 _2364) = (P _2363 _2364).
Proof. exact (@lem109401 (P _2363 _2364)). Qed.
Lemma lem109403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem109404 (P : type1605) (_2363 : nat) (_2364 : nat) : (term180 P _2363 _2364) = (term181 P _2363 _2364).
Proof. exact (MK_COMB (@lem109403) (@lem109402 P _2363 _2364)). Qed.
Lemma lem109405 (P : type1605) (_2364 : nat) (_2363 : nat) : (P _2364 _2363) = (P _2364 _2363).
Proof. exact (eq_refl (P _2364 _2363)). Qed.
Lemma lem109406 (P : type1605) (_2364 : nat) (_2363 : nat) : (term178 P _2364 _2363) = (term182 P _2364 _2363).
Proof. exact (MK_COMB (@lem109404 P _2363 _2364) (@lem109405 P _2364 _2363)). Qed.
Lemma lem109407 (P : type1605) (_2364 : nat) (_2363 : nat) : (term79 P _2363 _2364) = (term182 P _2364 _2363).
Proof. exact (TRANS (@lem109399 P _2364 _2363) (@lem109406 P _2364 _2363)). Qed.
Lemma lem109410 (_2364 : nat) (_2363 : nat) (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term182 P _2364 _2363.
Proof. exact (EQ_MP (@lem109407 P _2364 _2363) (@lem109396 _2363 _2364 P m n h1)). Qed.
Lemma lem109411 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term182 P m n.
Proof. exact (@lem109410 m n P m n h1). Qed.
Lemma lem109414 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term55 P m n) (h3 : term147 P m n) : P m n.
Proof. exact (@lem109411 P m n h3 (@lem109367 P m n h1 h2 h3)). Qed.
Lemma lem109415 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : term175 P m n.
Proof. exact (fun h0 : term55 P m n => @lem109414 P m n h1 h0 h2). Qed.
Lemma lem109417 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem109418 (P : type1605) (m : nat) (n : nat) : (term175 P m n) = (P m n).
Proof. exact (@lem109417 (P m n)). Qed.
Lemma lem109419 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : P m n.
Proof. exact (EQ_MP (@lem109418 P m n) (@lem109415 P m n h1 h2)). Qed.
Lemma lem109422 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem109424 (P : type1605) (m : nat) (n : nat) : (term55 P m n) = (term183 P m n).
Proof. exact (@lem109422 (P m n)). Qed.
Lemma lem109427 (P : type1605) (m : nat) (n : nat) (h1 : term147 P m n) : term183 P m n.
Proof. exact (EQ_MP (@lem109424 P m n) (@lem109228 P m n h1)). Qed.
Lemma lem109430 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : False.
Proof. exact (@lem109427 P m n h2 (@lem109419 P m n h1 h2)). Qed.
Lemma lem109431 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : term184.
Proof. exact (fun h0 : ~ False => @lem109430 P m n h1 h2). Qed.
Lemma lem109433 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem109434 : term184 = False.
Proof. exact (@lem109433 False). Qed.
Lemma lem109435 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : False.
Proof. exact (EQ_MP (@lem109434) (@lem109431 P m n h1 h2)). Qed.
Lemma lem109436 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem109435 P m n h1 h2) (fun h3 : False => @lem109144 h1)). Qed.
Lemma lem109437 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : False.
Proof. exact (EQ_MP (@lem109436 P m n h1 h2) (@lem109144 h1)). Qed.
Lemma lem109438 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : (term147 P m n) = False.
Proof. exact (prop_ext (fun h3 : term147 P m n => @lem109437 P m n h1 h2) (fun h3 : False => @lem109122 P m n h2)). Qed.
Lemma lem109439 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : False.
Proof. exact (EQ_MP (@lem109438 P m n h1 h2) (@lem109122 P m n h2)). Qed.
Lemma lem109440 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem109439 P m n h1 h2) (fun h3 : False => @lem109042 h1)). Qed.
Lemma lem109441 (P : type1605) (m : nat) (n : nat) (h1 : term10) (h2 : term147 P m n) : False.
Proof. exact (EQ_MP (@lem109440 P m n h1 h2) (@lem109042 h1)). Qed.
Lemma lem109442 (P : type1605) (m : nat) (h1 : term10) (h2 : term150 P m) : False.
Proof. exact (ex_elim (@lem109021 P m h2) (fun n : nat => fun h0 : term149 P m n => @lem109441 P m n h1 h0)). Qed.
Lemma lem109443 (P : type1605) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem108952 P h2) (fun m : nat => fun h0 : term151 P m => @lem109442 P m h1 h0)). Qed.
Lemma lem109444 (P : type1605) (h1 : term10) (h2 : term3 P) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem109443 P h1 h2) (fun h3 : False => @lem109020 h1)). Qed.
Lemma lem109445 (P : type1605) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (EQ_MP (@lem109444 P h1 h2) (@lem109020 h1)). Qed.
Lemma lem109446 (P : type1605) (h1 : term3 P) : term8.
Proof. exact (fun h0 : term10 => @lem109445 P h0 h1). Qed.
Lemma lem109447 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem109448 (P : type1605) (h1 : term3 P) : term9.
Proof. exact (EQ_MP (@lem109447) (@lem109446 P h1)). Qed.
Lemma lem109449 (P : type1605) : term12 P.
Proof. exact (fun h0 : term3 P => @lem109448 P h0). Qed.
Lemma lem109454 : term16.
Proof. exact (fun P : type1605 => @lem109449 P). Qed.
Lemma lem109455 : term15.
Proof. exact (EQ_MP (@lem108510) (@lem109454)). Qed.
Lemma lem109456 (P : type1605) : term185 P.
Proof. exact (@lem109455 P). Qed.
Lemma lem109457 (P : type1605) : (term185 P) = (term4 P).
Proof. exact (eq_refl (term185 P)). Qed.
Lemma lem109458 (P : type1605) : term4 P.
Proof. exact (EQ_MP (@lem109457 P) (@lem109456 P)). Qed.
Lemma lem109460 (P : type1605) : term4 P.
Proof. exact (@lem108278 P (@lem109458 P)). Qed.
Lemma lem109461 (P : type1605) (h1 : term3 P) : term8.
Proof. exact (@lem109460 P (@lem108263 P h1)). Qed.
Lemma lem109462 (P : type1605) (h1 : term3 P) : False.
Proof. exact (@lem109461 P h1 (@lem96155)). Qed.
Lemma lem109463 (P : type1605) (h1 : term3 P) : (term3 P) = False.
Proof. exact (prop_ext (fun h2 : term3 P => @lem109462 P h1) (fun h2 : False => @lem108263 P h1)). Qed.
Lemma lem109464 (P : type1605) (h1 : term3 P) : False.
Proof. exact (EQ_MP (@lem109463 P h1) (@lem108263 P h1)). Qed.
Lemma lem109465 (P : type1605) : term2 P.
Proof. exact (fun h0 : term3 P => @lem109464 P h0). Qed.
Lemma lem109466 (P : type1605) : term1 P.
Proof. exact (EQ_MP (@lem108262 P) (@lem109465 P)). Qed.
