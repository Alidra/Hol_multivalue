Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_ZERO_term_abbrevs.
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
Lemma lem157273 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem157274 : term1 = term2.
Proof. exact (@lem157273 term1). Qed.
Lemma lem157275 : term2 = term1.
Proof. exact (SYM (@lem157274)). Qed.
Lemma lem157276 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem157279 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem157280 : term5.
Proof. exact (fun h0 : term4 => @lem157279 h0). Qed.
Lemma lem157281 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem157282 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem157283 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem157281 h2 (@lem157282 h1)). Qed.
Lemma lem157284 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem157283 h1 h0). Qed.
Lemma lem157285 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem157286 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem157284 h1 (@lem157285 h2)). Qed.
Lemma lem157287 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem157286 h0 h1). Qed.
Lemma lem157288 : term7.
Proof. exact (fun h0 : term5 => @lem157287 h0). Qed.
Lemma lem157291 : term5.
Proof. exact (@lem157288 (@lem157280)). Qed.
Lemma lem157299 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem157300 : term8 = term9.
Proof. exact (@lem157299 term10). Qed.
Lemma lem157313 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem157320 : term4 = term12.
Proof. exact (MK_COMB (@lem157313) (@lem157300)). Qed.
Lemma lem157324 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem157325 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem157326 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term13 n) = (@COND Prop False).
Proof. exact (MK_COMB (@lem157325) (@lem157324 n h1)). Qed.
Lemma lem157333 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem157334 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term15 n m) = (term16 n m).
Proof. exact (MK_COMB (@lem157326 n h1) (@lem157333 n m)). Qed.
Lemma lem157339 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem157340 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem157334 m n h1) (@lem157339 m n)). Qed.
Lemma lem157342 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem157343 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem157342 Prop t1 t2). Qed.
Lemma lem157344 (m : nat) (n : nat) : (term19 m n) = (term17 m n).
Proof. exact (@lem157343 (term14 n m) (term17 m n)). Qed.
Lemma lem157347 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 m n) = (term17 m n).
Proof. exact (TRANS (@lem157340 m n h1) (@lem157344 m n)). Qed.
Lemma lem157348 (m : nat) (n : nat) : term20 m n.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = False => @lem157347 m n h0). Qed.
Lemma lem157350 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem157351 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem157352 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term13 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem157351) (@lem157350 n h1)). Qed.
Lemma lem157359 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem157360 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term15 n m) = (term21 n m).
Proof. exact (MK_COMB (@lem157352 n h1) (@lem157359 n m)). Qed.
Lemma lem157365 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem157366 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem157360 m n h1) (@lem157365 m n)). Qed.
Lemma lem157368 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem157369 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem157368 Prop t2 t1). Qed.
Lemma lem157370 (n : nat) (m : nat) : (term22 m n) = (term14 n m).
Proof. exact (@lem157369 (term17 m n) (term14 n m)). Qed.
Lemma lem157373 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 m n) = (term14 n m).
Proof. exact (TRANS (@lem157366 m n h1) (@lem157370 n m)). Qed.
Lemma lem157374 (n : nat) (m : nat) : term23 n m.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = True => @lem157373 m n h0). Qed.
Lemma lem157375 (n : nat) (m : nat) : term24 n m.
Proof. exact (conj (@lem157348 m n) (@lem157374 n m)). Qed.
Lemma lem157377 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term25 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem157378 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem157377 (term18 m n) (term14 n m) (n = (NUMERAL 0)) (term17 m n)). Qed.
Lemma lem157419 (m : nat) (n : nat) : (term18 m n) = (term27 m n).
Proof. exact (@lem157378 m n (@lem157375 n m)). Qed.
Lemma lem157420 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem157419 m n)). Qed.
Lemma lem157421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157422 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem157421) (@lem157420 m)). Qed.
Lemma lem157423 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem157422 m)). Qed.
Lemma lem157424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157425 : term10 = term34.
Proof. exact (MK_COMB (@lem157424) (@lem157423)). Qed.
Lemma lem157426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem157427 : term9 = term35.
Proof. exact (MK_COMB (@lem157426) (@lem157425)). Qed.
Lemma lem157428 (n : nat) : ((term36 n) = (NUMERAL 0)) = ((term36 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term36 n) = (NUMERAL 0))). Qed.
Lemma lem157429 : term37 = term37.
Proof. exact (fun_ext (fun n : nat => @lem157428 n)). Qed.
Lemma lem157430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157431 : term1 = term1.
Proof. exact (MK_COMB (@lem157430) (@lem157429)). Qed.
Lemma lem157432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem157433 : term3 = term3.
Proof. exact (MK_COMB (@lem157432) (@lem157431)). Qed.
Lemma lem157434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem157435 : term11 = term11.
Proof. exact (MK_COMB (@lem157434) (@lem157433)). Qed.
Lemma lem157436 : term12 = term38.
Proof. exact (MK_COMB (@lem157435) (@lem157427)). Qed.
Lemma lem157469 : term4 = term38.
Proof. exact (TRANS (@lem157320) (@lem157436)). Qed.
Lemma lem157470 : term38 = term4.
Proof. exact (SYM (@lem157469)). Qed.
Lemma lem157471 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem157472 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem157474 (P : nat -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem157475 : term3 = term41.
Proof. exact (@lem157474 term37). Qed.
Lemma lem157476 (n : nat) : (term42 n) = ((term36 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem157477 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem157479 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem157477) (@lem157476 n)). Qed.
Lemma lem157480 : term45 = term46.
Proof. exact (fun_ext (fun n : nat => @lem157479 n)). Qed.
Lemma lem157481 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem157482 : term41 = term47.
Proof. exact (MK_COMB (@lem157481) (@lem157480)). Qed.
Lemma lem157491 : term3 = term47.
Proof. exact (TRANS (@lem157475) (@lem157482)). Qed.
Lemma lem157492 (h1 : term3) : term47.
Proof. exact (EQ_MP (@lem157491) (@lem157471 h1)). Qed.
Lemma lem157513 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem157514 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem157513 m n)). Qed.
Lemma lem157515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157516 (m : nat) : (term31 m) = (term31 m).
Proof. exact (MK_COMB (@lem157515) (@lem157514 m)). Qed.
Lemma lem157517 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem157516 m)). Qed.
Lemma lem157518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157519 : term34 = term34.
Proof. exact (MK_COMB (@lem157518) (@lem157517)). Qed.
Lemma lem157525 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem157526 (P : nat -> Prop) (Q : nat -> Prop) : (term50 P Q) = (term51 P Q).
Proof. exact (@lem157525 nat P Q). Qed.
Lemma lem157527 (m : nat) : (term52 m) = (term53 m).
Proof. exact (@lem157526 (term54 m) (term55 m)). Qed.
Lemma lem157528 (n : nat) (m : nat) : (term56 m n) = (term57 n m).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem157529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem157530 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem157529) (@lem157528 n m)). Qed.
Lemma lem157531 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem157532 (m : nat) (n : nat) : (term62 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem157530 n m) (@lem157531 m n)). Qed.
Lemma lem157533 (m : nat) : (term63 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem157532 m n)). Qed.
Lemma lem157534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157535 (m : nat) : (term52 m) = (term31 m).
Proof. exact (MK_COMB (@lem157534) (@lem157533 m)). Qed.
Lemma lem157536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem157537 (m : nat) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem157536) (@lem157535 m)). Qed.
Lemma lem157538 (n : nat) (m : nat) : (term56 m n) = (term57 n m).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem157539 (m : nat) : (term66 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem157538 n m)). Qed.
Lemma lem157540 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157541 (m : nat) : (term67 m) = (term68 m).
Proof. exact (MK_COMB (@lem157540) (@lem157539 m)). Qed.
Lemma lem157542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem157543 (m : nat) : (term69 m) = (term70 m).
Proof. exact (MK_COMB (@lem157542) (@lem157541 m)). Qed.
Lemma lem157544 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem157545 (m : nat) : (term71 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem157544 m n)). Qed.
Lemma lem157546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157547 (m : nat) : (term72 m) = (term73 m).
Proof. exact (MK_COMB (@lem157546) (@lem157545 m)). Qed.
Lemma lem157548 (m : nat) : (term53 m) = (term74 m).
Proof. exact (MK_COMB (@lem157543 m) (@lem157547 m)). Qed.
Lemma lem157549 (m : nat) : ((term52 m) = (term53 m)) = ((term31 m) = (term74 m)).
Proof. exact (MK_COMB (@lem157537 m) (@lem157548 m)). Qed.
Lemma lem157550 (m : nat) : (term31 m) = (term74 m).
Proof. exact (EQ_MP (@lem157549 m) (@lem157527 m)). Qed.
Lemma lem157647 : term33 = term75.
Proof. exact (fun_ext (fun m : nat => @lem157550 m)). Qed.
Lemma lem157648 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157649 : term34 = term76.
Proof. exact (MK_COMB (@lem157648) (@lem157647)). Qed.
Lemma lem157651 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem157652 (P : nat -> Prop) (Q : nat -> Prop) : (term50 P Q) = (term51 P Q).
Proof. exact (@lem157651 nat P Q). Qed.
Lemma lem157653 : term77 = term78.
Proof. exact (@lem157652 term79 term80). Qed.
Lemma lem157654 (m : nat) : (term81 m) = (term68 m).
Proof. exact (eq_refl (term81 m)). Qed.
Lemma lem157655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem157656 (m : nat) : (term82 m) = (term70 m).
Proof. exact (MK_COMB (@lem157655) (@lem157654 m)). Qed.
Lemma lem157657 (m : nat) : (term83 m) = (term73 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem157658 (m : nat) : (term84 m) = (term74 m).
Proof. exact (MK_COMB (@lem157656 m) (@lem157657 m)). Qed.
Lemma lem157659 : term85 = term75.
Proof. exact (fun_ext (fun m : nat => @lem157658 m)). Qed.
Lemma lem157660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157661 : term77 = term76.
Proof. exact (MK_COMB (@lem157660) (@lem157659)). Qed.
Lemma lem157662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem157663 : term86 = term87.
Proof. exact (MK_COMB (@lem157662) (@lem157661)). Qed.
Lemma lem157664 (m : nat) : (term81 m) = (term68 m).
Proof. exact (eq_refl (term81 m)). Qed.
Lemma lem157665 : term88 = term79.
Proof. exact (fun_ext (fun m : nat => @lem157664 m)). Qed.
Lemma lem157666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157667 : term89 = term90.
Proof. exact (MK_COMB (@lem157666) (@lem157665)). Qed.
Lemma lem157668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem157669 : term91 = term92.
Proof. exact (MK_COMB (@lem157668) (@lem157667)). Qed.
Lemma lem157670 (m : nat) : (term83 m) = (term73 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem157671 : term93 = term80.
Proof. exact (fun_ext (fun m : nat => @lem157670 m)). Qed.
Lemma lem157672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157673 : term94 = term95.
Proof. exact (MK_COMB (@lem157672) (@lem157671)). Qed.
Lemma lem157674 : term78 = term96.
Proof. exact (MK_COMB (@lem157669) (@lem157673)). Qed.
Lemma lem157675 : (term77 = term78) = (term76 = term96).
Proof. exact (MK_COMB (@lem157663) (@lem157674)). Qed.
Lemma lem157676 : term76 = term96.
Proof. exact (EQ_MP (@lem157675) (@lem157653)). Qed.
Lemma lem157783 : term34 = term96.
Proof. exact (TRANS (@lem157649) (@lem157676)). Qed.
Lemma lem157784 : term34 = term96.
Proof. exact (TRANS (@lem157519) (@lem157783)). Qed.
Lemma lem157785 (h1 : term34) : term96.
Proof. exact (EQ_MP (@lem157784) (@lem157472 h1)). Qed.
Lemma lem157829 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem157830 (m : nat) : (term55 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem157829 m n)). Qed.
Lemma lem157831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157832 (m : nat) : (term73 m) = (term73 m).
Proof. exact (MK_COMB (@lem157831) (@lem157830 m)). Qed.
Lemma lem157833 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem157832 m)). Qed.
Lemma lem157834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157835 : term95 = term95.
Proof. exact (MK_COMB (@lem157834) (@lem157833)). Qed.
Lemma lem157870 (n : nat) (m : nat) : (term57 n m) = (term57 n m).
Proof. exact (eq_refl (term57 n m)). Qed.
Lemma lem157871 (m : nat) : (term54 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem157870 n m)). Qed.
Lemma lem157872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157873 (m : nat) : (term68 m) = (term68 m).
Proof. exact (MK_COMB (@lem157872) (@lem157871 m)). Qed.
Lemma lem157874 : term79 = term79.
Proof. exact (fun_ext (fun m : nat => @lem157873 m)). Qed.
Lemma lem157875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157876 : term90 = term90.
Proof. exact (MK_COMB (@lem157875) (@lem157874)). Qed.
Lemma lem157877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem157878 : term92 = term92.
Proof. exact (MK_COMB (@lem157877) (@lem157876)). Qed.
Lemma lem157879 : term96 = term96.
Proof. exact (MK_COMB (@lem157878) (@lem157835)). Qed.
Lemma lem157880 (h1 : term34) : term96.
Proof. exact (EQ_MP (@lem157879) (@lem157785 h1)). Qed.
Lemma lem157896 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem157898 (h1 : term34) : term90.
Proof. exact (proj1 (@lem157880 h1)). Qed.
Lemma lem157902 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem157920 (n : nat) (m : nat) : (term57 n m) = (term97 n m).
Proof. exact (@lem19490 ((Nat.div m n) = (NUMERAL 0)) (term98 n) ((Nat.modulo m n) = m)). Qed.
Lemma lem157921 (m : nat) : (term54 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem157920 n m)). Qed.
Lemma lem157922 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157923 (m : nat) : (term68 m) = (term100 m).
Proof. exact (MK_COMB (@lem157922) (@lem157921 m)). Qed.
Lemma lem157924 : term79 = term101.
Proof. exact (fun_ext (fun m : nat => @lem157923 m)). Qed.
Lemma lem157925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem157927 : term90 = term102.
Proof. exact (MK_COMB (@lem157925) (@lem157924)). Qed.
Lemma lem157928 (h1 : term34) : term102.
Proof. exact (EQ_MP (@lem157927) (@lem157898 h1)). Qed.
Lemma lem157955 (_3140 : nat) (h1 : term34) : term103 _3140.
Proof. exact (@lem157928 h1 _3140). Qed.
Lemma lem157956 (_3140 : nat) : (term103 _3140) = (term100 _3140).
Proof. exact (eq_refl (term103 _3140)). Qed.
Lemma lem157957 (_3140 : nat) (h1 : term34) : term100 _3140.
Proof. exact (EQ_MP (@lem157956 _3140) (@lem157955 _3140 h1)). Qed.
Lemma lem157958 (_3140 : nat) (_3141 : nat) (h1 : term34) : term104 _3140 _3141.
Proof. exact (@lem157957 _3140 h1 _3141). Qed.
Lemma lem157959 (_3141 : nat) (_3140 : nat) : (term104 _3140 _3141) = (term97 _3141 _3140).
Proof. exact (eq_refl (term104 _3140 _3141)). Qed.
Lemma lem157960 (_3141 : nat) (_3140 : nat) (h1 : term34) : term97 _3141 _3140.
Proof. exact (EQ_MP (@lem157959 _3141 _3140) (@lem157958 _3140 _3141 h1)). Qed.
Lemma lem157972 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem157990 (_3140 : nat) (_3141 : nat) (h1 : term34) : term105 _3140 _3141.
Proof. exact (proj1 (@lem157960 _3141 _3140 h1)). Qed.
Lemma lem158087 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem158088 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem158087 (NUMERAL 0)). Qed.
Lemma lem158089 : term106.
Proof. exact (fun h0 : term107 => @lem158088). Qed.
Lemma lem158091 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem158092 : term106 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem158091 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem158093 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem158092) (@lem158089)). Qed.
Lemma lem158099 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem158100 (_3140 : nat) (_3141 : nat) : (term105 _3140 _3141) = (term109 _3140 _3141).
Proof. exact (@lem158099 ((Nat.div _3140 _3141) = (NUMERAL 0)) (term98 _3141)). Qed.
Lemma lem158110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem158111 (_3140 : nat) (_3141 : nat) : (term110 _3140 _3141) = (term111 _3140 _3141).
Proof. exact (MK_COMB (@lem158110) (@lem158100 _3140 _3141)). Qed.
Lemma lem158121 (_3140 : nat) (_3141 : nat) : (term109 _3140 _3141) = (term109 _3140 _3141).
Proof. exact (eq_refl (term109 _3140 _3141)). Qed.
Lemma lem158122 (_3140 : nat) (_3141 : nat) : ((term105 _3140 _3141) = (term109 _3140 _3141)) = ((term109 _3140 _3141) = (term109 _3140 _3141)).
Proof. exact (MK_COMB (@lem158111 _3140 _3141) (@lem158121 _3140 _3141)). Qed.
Lemma lem158124 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem158125 (x : Prop) : (x = x) = True.
Proof. exact (@lem158124 Prop x). Qed.
Lemma lem158126 (_3140 : nat) (_3141 : nat) : ((term109 _3140 _3141) = (term109 _3140 _3141)) = True.
Proof. exact (@lem158125 (term109 _3140 _3141)). Qed.
Lemma lem158127 (_3140 : nat) (_3141 : nat) : ((term105 _3140 _3141) = (term109 _3140 _3141)) = True.
Proof. exact (TRANS (@lem158122 _3140 _3141) (@lem158126 _3140 _3141)). Qed.
Lemma lem158128 (_3140 : nat) (_3141 : nat) : True = ((term105 _3140 _3141) = (term109 _3140 _3141)).
Proof. exact (SYM (@lem158127 _3140 _3141)). Qed.
Lemma lem158129 (_3140 : nat) (_3141 : nat) : (term105 _3140 _3141) = (term109 _3140 _3141).
Proof. exact (EQ_MP (@lem158128 _3140 _3141) (@lem0)). Qed.
Lemma lem158130 (_3140 : nat) (_3141 : nat) (h1 : term34) : term109 _3140 _3141.
Proof. exact (EQ_MP (@lem158129 _3140 _3141) (@lem157990 _3140 _3141 h1)). Qed.
Lemma lem158132 (b : Prop) (a : Prop) : (a \/ b) = (term112 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem158133 (_3140 : nat) (_3141 : nat) : (term109 _3140 _3141) = (term113 _3140 _3141).
Proof. exact (@lem158132 (term98 _3141) ((Nat.div _3140 _3141) = (NUMERAL 0))). Qed.
Lemma lem158135 (a : Prop) : (term114 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem158136 (_3141 : nat) : (term115 _3141) = (_3141 = (NUMERAL 0)).
Proof. exact (@lem158135 (_3141 = (NUMERAL 0))). Qed.
Lemma lem158137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem158138 (_3141 : nat) : (term116 _3141) = (term117 _3141).
Proof. exact (MK_COMB (@lem158137) (@lem158136 _3141)). Qed.
Lemma lem158139 (_3140 : nat) (_3141 : nat) : ((Nat.div _3140 _3141) = (NUMERAL 0)) = ((Nat.div _3140 _3141) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.div _3140 _3141) = (NUMERAL 0))). Qed.
Lemma lem158140 (_3140 : nat) (_3141 : nat) : (term113 _3140 _3141) = (term118 _3140 _3141).
Proof. exact (MK_COMB (@lem158138 _3141) (@lem158139 _3140 _3141)). Qed.
Lemma lem158141 (_3140 : nat) (_3141 : nat) : (term109 _3140 _3141) = (term118 _3140 _3141).
Proof. exact (TRANS (@lem158133 _3140 _3141) (@lem158140 _3140 _3141)). Qed.
Lemma lem158144 (_3140 : nat) (_3141 : nat) (h1 : term34) : term118 _3140 _3141.
Proof. exact (EQ_MP (@lem158141 _3140 _3141) (@lem158130 _3140 _3141 h1)). Qed.
Lemma lem158145 (_3140 : nat) (h1 : term34) : term119 _3140.
Proof. exact (@lem158144 _3140 (NUMERAL 0) h1). Qed.
Lemma lem158148 (_3140 : nat) (h1 : term34) : (term36 _3140) = (NUMERAL 0).
Proof. exact (@lem158145 _3140 h1 (@lem158093)). Qed.
Lemma lem158149 (n : nat) (h1 : term34) : (term36 n) = (NUMERAL 0).
Proof. exact (@lem158148 n h1). Qed.
Lemma lem158150 (n : nat) (h1 : term34) : term120 n.
Proof. exact (fun h0 : term44 n => @lem158149 n h1). Qed.
Lemma lem158152 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem158153 (n : nat) : (term120 n) = ((term36 n) = (NUMERAL 0)).
Proof. exact (@lem158152 ((term36 n) = (NUMERAL 0))). Qed.
Lemma lem158154 (n : nat) (h1 : term34) : (term36 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem158153 n) (@lem158150 n h1)). Qed.
Lemma lem158157 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem158159 (n : nat) : (term44 n) = (term121 n).
Proof. exact (@lem158157 ((term36 n) = (NUMERAL 0))). Qed.
Lemma lem158162 (n : nat) (h1 : term44 n) : term121 n.
Proof. exact (EQ_MP (@lem158159 n) (@lem157972 n h1)). Qed.
Lemma lem158165 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (@lem158162 n h2 (@lem158154 n h1)). Qed.
Lemma lem158166 (n : nat) (h1 : term34) (h2 : term44 n) : term122.
Proof. exact (fun h0 : ~ False => @lem158165 n h1 h2). Qed.
Lemma lem158168 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem158169 : term122 = False.
Proof. exact (@lem158168 False). Qed.
Lemma lem158170 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem158169) (@lem158166 n h1 h2)). Qed.
Lemma lem158171 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem158170 n h1 h2) (fun h3 : False => @lem157972 n h2)). Qed.
Lemma lem158172 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem158171 n h1 h2) (@lem157972 n h2)). Qed.
Lemma lem158173 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem158172 n h1 h2) (fun h3 : False => @lem157902 n h2)). Qed.
Lemma lem158174 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem158173 n h1 h2) (@lem157902 n h2)). Qed.
Lemma lem158175 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem158174 n h1 h2) (fun h3 : False => @lem157902 n h2)). Qed.
Lemma lem158176 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem158175 n h1 h2) (@lem157902 n h2)). Qed.
Lemma lem158177 (n : nat) (h1 : term34) (h2 : term44 n) : (term44 n) = False.
Proof. exact (prop_ext (fun h3 : term44 n => @lem158176 n h1 h2) (fun h3 : False => @lem157896 n h2)). Qed.
Lemma lem158178 (n : nat) (h1 : term34) (h2 : term44 n) : False.
Proof. exact (EQ_MP (@lem158177 n h1 h2) (@lem157896 n h2)). Qed.
Lemma lem158179 (h1 : term34) (h2 : term3) : False.
Proof. exact (ex_elim (@lem157492 h2) (fun n : nat => fun h0 : term46 n => @lem158178 n h1 h0)). Qed.
Lemma lem158180 (h1 : term3) : term123.
Proof. exact (fun h0 : term34 => @lem158179 h0 h1). Qed.
Lemma lem158181 : term123 = term35.
Proof. exact (@lem69 term34). Qed.
Lemma lem158182 (h1 : term3) : term35.
Proof. exact (EQ_MP (@lem158181) (@lem158180 h1)). Qed.
Lemma lem158183 : term38.
Proof. exact (fun h0 : term3 => @lem158182 h0). Qed.
Lemma lem158184 : term4.
Proof. exact (EQ_MP (@lem157470) (@lem158183)). Qed.
Lemma lem158186 : term4.
Proof. exact (@lem157291 (@lem158184)). Qed.
Lemma lem158187 (h1 : term3) : term8.
Proof. exact (@lem158186 (@lem157276 h1)). Qed.
Lemma lem158188 (h1 : term3) : False.
Proof. exact (@lem158187 h1 (@lem155916)). Qed.
Lemma lem158189 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem158188 h1) (fun h2 : False => @lem157276 h1)). Qed.
Lemma lem158190 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem158189 h1) (@lem157276 h1)). Qed.
Lemma lem158191 : term2.
Proof. exact (fun h0 : term3 => @lem158190 h0). Qed.
Lemma lem158192 : term1.
Proof. exact (EQ_MP (@lem157275) (@lem158191)). Qed.
