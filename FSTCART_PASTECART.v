Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FSTCART_PASTECART_term_abbrevs.
Require Import CART_EQ_spec.
Require Import INT_POS_spec.
Require Import LAMBDA_BETA_spec.
Require Import fstcart_spec.
Require Import pastecart_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7640410_spec.
Require Import thm7640437_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7640489 (a : nat) (b : nat) (c : nat) : (term0 a b c) = (term1 a b c).
Proof. exact (@lem17265 (Peano.le a b) (term2 a b c)). Qed.
Lemma lem7640491 (m : nat) (n : nat) : (Peano.le m n) = (term3 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7640492 (a : nat) (b : nat) : (Peano.le a b) = (term3 a b).
Proof. exact (@lem7640491 a b). Qed.
Lemma lem7640493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7640494 (a : nat) (b : nat) : (term4 a b) = (term5 a b).
Proof. exact (MK_COMB (@lem7640493) (@lem7640492 a b)). Qed.
Lemma lem7640495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7640496 (a : nat) (b : nat) : (term6 a b) = (term7 a b).
Proof. exact (MK_COMB (@lem7640495) (@lem7640494 a b)). Qed.
Lemma lem7640498 (m : nat) (n : nat) : (Peano.le m n) = (term3 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7640499 (a : nat) (b : nat) (c : nat) : (term2 a b c) = (term8 a b c).
Proof. exact (@lem7640498 a (Nat.add b c)). Qed.
Lemma lem7640501 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7640502 (b : nat) (c : nat) : (term9 b c) = (term10 b c).
Proof. exact (@lem7640501 b c). Qed.
Lemma lem7640503 (a : nat) : (term11 a) = (term11 a).
Proof. exact (eq_refl (term11 a)). Qed.
Lemma lem7640504 (a : nat) (b : nat) (c : nat) : (term8 a b c) = (term12 a b c).
Proof. exact (MK_COMB (@lem7640503 a) (@lem7640502 b c)). Qed.
Lemma lem7640505 (a : nat) (b : nat) (c : nat) : (term2 a b c) = (term12 a b c).
Proof. exact (TRANS (@lem7640499 a b c) (@lem7640504 a b c)). Qed.
Lemma lem7640506 (a : nat) (b : nat) (c : nat) : (term1 a b c) = (term13 a b c).
Proof. exact (MK_COMB (@lem7640496 a b) (@lem7640505 a b c)). Qed.
Lemma lem7640507 (a : nat) (b : nat) (c : nat) : (term0 a b c) = (term13 a b c).
Proof. exact (TRANS (@lem7640489 a b c) (@lem7640506 a b c)). Qed.
Lemma lem7640508 (a : nat) : term14 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7640509 (a : nat) : (term14 a) = (term15 a).
Proof. exact (eq_refl (term14 a)). Qed.
Lemma lem7640510 (a : nat) : term15 a.
Proof. exact (EQ_MP (@lem7640509 a) (@lem7640508 a)). Qed.
Lemma lem7640511 (b : nat) : term14 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem7640512 (b : nat) : (term14 b) = (term15 b).
Proof. exact (eq_refl (term14 b)). Qed.
Lemma lem7640513 (b : nat) : term15 b.
Proof. exact (EQ_MP (@lem7640512 b) (@lem7640511 b)). Qed.
Lemma lem7640514 (c : nat) : term14 c.
Proof. exact (@lem2307535 c). Qed.
Lemma lem7640515 (c : nat) : (term14 c) = (term15 c).
Proof. exact (eq_refl (term14 c)). Qed.
Lemma lem7640516 (c : nat) : term15 c.
Proof. exact (EQ_MP (@lem7640515 c) (@lem7640514 c)). Qed.
Lemma lem7640517 (_98486 : int) (_98487 : int) (_98488 : int) : (term16 _98486 _98487 _98488) = (term17 _98486 _98487 _98488).
Proof. exact (@lem2318604 (term17 _98486 _98487 _98488)). Qed.
Lemma lem7640536 (_98486 : int) (_98487 : int) : (term18 _98486 _98487) = (int_le _98486 _98487).
Proof. exact (@lem16933 (int_le _98486 _98487)). Qed.
Lemma lem7640537 (_98486 : int) (_98487 : int) (_98488 : int) : (term19 _98486 _98487 _98488) = (term19 _98486 _98487 _98488).
Proof. exact (eq_refl (term19 _98486 _98487 _98488)). Qed.
Lemma lem7640538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640539 (_98486 : int) (_98487 : int) : (term20 _98486 _98487) = (term21 _98486 _98487).
Proof. exact (MK_COMB (@lem7640538) (@lem7640536 _98486 _98487)). Qed.
Lemma lem7640540 (_98486 : int) (_98487 : int) (_98488 : int) : (term22 _98486 _98487 _98488) = (term23 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640539 _98486 _98487) (@lem7640537 _98486 _98487 _98488)). Qed.
Lemma lem7640541 (_98486 : int) (_98487 : int) (_98488 : int) : (term24 _98486 _98487 _98488) = (term22 _98486 _98487 _98488).
Proof. exact (@lem17160 (term25 _98486 _98487) (term26 _98486 _98487 _98488)). Qed.
Lemma lem7640542 (_98486 : int) (_98487 : int) (_98488 : int) : (term24 _98486 _98487 _98488) = (term23 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640541 _98486 _98487 _98488) (@lem7640540 _98486 _98487 _98488)). Qed.
Lemma lem7640544 (_98488 : int) : (term27 _98488) = (term27 _98488).
Proof. exact (eq_refl (term27 _98488)). Qed.
Lemma lem7640545 (_98486 : int) (_98487 : int) (_98488 : int) : (term28 _98486 _98487 _98488) = (term29 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640544 _98488) (@lem7640542 _98486 _98487 _98488)). Qed.
Lemma lem7640546 (_98486 : int) (_98487 : int) (_98488 : int) : (term30 _98486 _98487 _98488) = (term28 _98486 _98487 _98488).
Proof. exact (@lem17362 (term31 _98488) (term32 _98486 _98487 _98488)). Qed.
Lemma lem7640547 (_98486 : int) (_98487 : int) (_98488 : int) : (term30 _98486 _98487 _98488) = (term29 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640546 _98486 _98487 _98488) (@lem7640545 _98486 _98487 _98488)). Qed.
Lemma lem7640549 (_98487 : int) : (term27 _98487) = (term27 _98487).
Proof. exact (eq_refl (term27 _98487)). Qed.
Lemma lem7640550 (_98486 : int) (_98487 : int) (_98488 : int) : (term33 _98486 _98487 _98488) = (term34 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640549 _98487) (@lem7640547 _98486 _98487 _98488)). Qed.
Lemma lem7640551 (_98486 : int) (_98487 : int) (_98488 : int) : (term35 _98486 _98487 _98488) = (term33 _98486 _98487 _98488).
Proof. exact (@lem17362 (term31 _98487) (term36 _98486 _98487 _98488)). Qed.
Lemma lem7640552 (_98486 : int) (_98487 : int) (_98488 : int) : (term35 _98486 _98487 _98488) = (term34 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640551 _98486 _98487 _98488) (@lem7640550 _98486 _98487 _98488)). Qed.
Lemma lem7640554 (_98486 : int) : (term27 _98486) = (term27 _98486).
Proof. exact (eq_refl (term27 _98486)). Qed.
Lemma lem7640555 (_98486 : int) (_98487 : int) (_98488 : int) : (term37 _98486 _98487 _98488) = (term38 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640554 _98486) (@lem7640552 _98486 _98487 _98488)). Qed.
Lemma lem7640556 (_98486 : int) (_98487 : int) (_98488 : int) : (term39 _98486 _98487 _98488) = (term37 _98486 _98487 _98488).
Proof. exact (@lem17362 (term31 _98486) (term40 _98486 _98487 _98488)). Qed.
Lemma lem7640578 (_98486 : int) (_98487 : int) (_98488 : int) : (term39 _98486 _98487 _98488) = (term38 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640556 _98486 _98487 _98488) (@lem7640555 _98486 _98487 _98488)). Qed.
Lemma lem7640581 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7640582 (_98486 : int) : (term31 _98486) = (term42 _98486).
Proof. exact (@lem7640581 term43 _98486). Qed.
Lemma lem7640584 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7640585 : term45 = term46.
Proof. exact (@lem7640584 (NUMERAL 0)). Qed.
Lemma lem7640586 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7640587 : term47 = term48.
Proof. exact (MK_COMB (@lem7640586) (@lem7640585)). Qed.
Lemma lem7640588 (_98486 : int) : (real_of_int _98486) = (real_of_int _98486).
Proof. exact (eq_refl (real_of_int _98486)). Qed.
Lemma lem7640589 (_98486 : int) : (term42 _98486) = (term49 _98486).
Proof. exact (MK_COMB (@lem7640587) (@lem7640588 _98486)). Qed.
Lemma lem7640591 (_98486 : int) : (term31 _98486) = (term49 _98486).
Proof. exact (TRANS (@lem7640582 _98486) (@lem7640589 _98486)). Qed.
Lemma lem7640594 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7640595 (_98487 : int) : (term31 _98487) = (term42 _98487).
Proof. exact (@lem7640594 term43 _98487). Qed.
Lemma lem7640597 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7640598 : term45 = term46.
Proof. exact (@lem7640597 (NUMERAL 0)). Qed.
Lemma lem7640599 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7640600 : term47 = term48.
Proof. exact (MK_COMB (@lem7640599) (@lem7640598)). Qed.
Lemma lem7640601 (_98487 : int) : (real_of_int _98487) = (real_of_int _98487).
Proof. exact (eq_refl (real_of_int _98487)). Qed.
Lemma lem7640602 (_98487 : int) : (term42 _98487) = (term49 _98487).
Proof. exact (MK_COMB (@lem7640600) (@lem7640601 _98487)). Qed.
Lemma lem7640604 (_98487 : int) : (term31 _98487) = (term49 _98487).
Proof. exact (TRANS (@lem7640595 _98487) (@lem7640602 _98487)). Qed.
Lemma lem7640607 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7640608 (_98488 : int) : (term31 _98488) = (term42 _98488).
Proof. exact (@lem7640607 term43 _98488). Qed.
Lemma lem7640610 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7640611 : term45 = term46.
Proof. exact (@lem7640610 (NUMERAL 0)). Qed.
Lemma lem7640612 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7640613 : term47 = term48.
Proof. exact (MK_COMB (@lem7640612) (@lem7640611)). Qed.
Lemma lem7640614 (_98488 : int) : (real_of_int _98488) = (real_of_int _98488).
Proof. exact (eq_refl (real_of_int _98488)). Qed.
Lemma lem7640615 (_98488 : int) : (term42 _98488) = (term49 _98488).
Proof. exact (MK_COMB (@lem7640613) (@lem7640614 _98488)). Qed.
Lemma lem7640617 (_98488 : int) : (term31 _98488) = (term49 _98488).
Proof. exact (TRANS (@lem7640608 _98488) (@lem7640615 _98488)). Qed.
Lemma lem7640620 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7640622 (_98486 : int) (_98487 : int) : (int_le _98486 _98487) = (term41 _98486 _98487).
Proof. exact (@lem7640620 _98486 _98487). Qed.
Lemma lem7640624 (y : int) (x : int) : (term25 x y) = (term50 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7640625 (_98487 : int) (_98488 : int) (_98486 : int) : (term19 _98486 _98487 _98488) = (term51 _98487 _98488 _98486).
Proof. exact (@lem7640624 (int_add _98487 _98488) _98486). Qed.
Lemma lem7640627 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7640628 (_98487 : int) (_98488 : int) (_98486 : int) : (term51 _98487 _98488 _98486) = (term52 _98487 _98488 _98486).
Proof. exact (@lem7640627 (term53 _98487 _98488) _98486). Qed.
Lemma lem7640630 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7640631 (_98487 : int) (_98488 : int) : (term56 _98487 _98488) = (term57 _98487 _98488).
Proof. exact (@lem7640630 (int_add _98487 _98488) term58). Qed.
Lemma lem7640633 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7640634 (_98487 : int) (_98488 : int) : (term54 _98487 _98488) = (term55 _98487 _98488).
Proof. exact (@lem7640633 _98487 _98488). Qed.
Lemma lem7640635 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7640636 (_98487 : int) (_98488 : int) : (term59 _98487 _98488) = (term60 _98487 _98488).
Proof. exact (MK_COMB (@lem7640635) (@lem7640634 _98487 _98488)). Qed.
Lemma lem7640638 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7640639 : term61 = term62.
Proof. exact (@lem7640638 term63). Qed.
Lemma lem7640640 (_98487 : int) (_98488 : int) : (term57 _98487 _98488) = (term64 _98487 _98488).
Proof. exact (MK_COMB (@lem7640636 _98487 _98488) (@lem7640639)). Qed.
Lemma lem7640641 (_98487 : int) (_98488 : int) : (term56 _98487 _98488) = (term64 _98487 _98488).
Proof. exact (TRANS (@lem7640631 _98487 _98488) (@lem7640640 _98487 _98488)). Qed.
Lemma lem7640642 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7640643 (_98487 : int) (_98488 : int) : (term65 _98487 _98488) = (term66 _98487 _98488).
Proof. exact (MK_COMB (@lem7640642) (@lem7640641 _98487 _98488)). Qed.
Lemma lem7640644 (_98486 : int) : (real_of_int _98486) = (real_of_int _98486).
Proof. exact (eq_refl (real_of_int _98486)). Qed.
Lemma lem7640645 (_98487 : int) (_98488 : int) (_98486 : int) : (term52 _98487 _98488 _98486) = (term67 _98487 _98488 _98486).
Proof. exact (MK_COMB (@lem7640643 _98487 _98488) (@lem7640644 _98486)). Qed.
Lemma lem7640646 (_98487 : int) (_98488 : int) (_98486 : int) : (term51 _98487 _98488 _98486) = (term67 _98487 _98488 _98486).
Proof. exact (TRANS (@lem7640628 _98487 _98488 _98486) (@lem7640645 _98487 _98488 _98486)). Qed.
Lemma lem7640647 (_98487 : int) (_98488 : int) (_98486 : int) : (term19 _98486 _98487 _98488) = (term67 _98487 _98488 _98486).
Proof. exact (TRANS (@lem7640625 _98487 _98488 _98486) (@lem7640646 _98487 _98488 _98486)). Qed.
Lemma lem7640648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640649 (_98486 : int) (_98487 : int) : (term21 _98486 _98487) = (term68 _98486 _98487).
Proof. exact (MK_COMB (@lem7640648) (@lem7640622 _98486 _98487)). Qed.
Lemma lem7640650 (_98487 : int) (_98488 : int) (_98486 : int) : (term23 _98486 _98487 _98488) = (term69 _98487 _98488 _98486).
Proof. exact (MK_COMB (@lem7640649 _98486 _98487) (@lem7640647 _98487 _98488 _98486)). Qed.
Lemma lem7640651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640652 (_98488 : int) : (term27 _98488) = (term70 _98488).
Proof. exact (MK_COMB (@lem7640651) (@lem7640617 _98488)). Qed.
Lemma lem7640653 (_98487 : int) (_98488 : int) (_98486 : int) : (term29 _98486 _98487 _98488) = (term71 _98487 _98488 _98486).
Proof. exact (MK_COMB (@lem7640652 _98488) (@lem7640650 _98487 _98488 _98486)). Qed.
Lemma lem7640654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640655 (_98487 : int) : (term27 _98487) = (term70 _98487).
Proof. exact (MK_COMB (@lem7640654) (@lem7640604 _98487)). Qed.
Lemma lem7640656 (_98487 : int) (_98488 : int) (_98486 : int) : (term34 _98486 _98487 _98488) = (term72 _98487 _98488 _98486).
Proof. exact (MK_COMB (@lem7640655 _98487) (@lem7640653 _98487 _98488 _98486)). Qed.
Lemma lem7640657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640658 (_98486 : int) : (term27 _98486) = (term70 _98486).
Proof. exact (MK_COMB (@lem7640657) (@lem7640591 _98486)). Qed.
Lemma lem7640659 (_98487 : int) (_98488 : int) (_98486 : int) : (term38 _98486 _98487 _98488) = (term73 _98487 _98488 _98486).
Proof. exact (MK_COMB (@lem7640658 _98486) (@lem7640656 _98487 _98488 _98486)). Qed.
Lemma lem7640660 (_98487 : int) (_98488 : int) (_98486 : int) : (term39 _98486 _98487 _98488) = (term73 _98487 _98488 _98486).
Proof. exact (TRANS (@lem7640578 _98486 _98487 _98488) (@lem7640659 _98487 _98488 _98486)). Qed.
Lemma lem7640664 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7640710 (_98487 : int) (_98488 : int) (_98486 : int) : (term75 _98487 _98488 _98486) = (term73 _98487 _98488 _98486).
Proof. exact (@lem7640664 (term73 _98487 _98488 _98486)). Qed.
Lemma lem7640711 (_98486 : int) : (term49 _98486) = (term76 _98486).
Proof. exact (@lem1988287 (real_of_int _98486) term46). Qed.
Lemma lem7640717 (_98486 : int) : (term77 _98486) = (term78 _98486).
Proof. exact (@lem1982792 (real_of_int _98486) term46). Qed.
Lemma lem7640719 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7640720 : term46 = term80.
Proof. exact (@lem7640719 (NUMERAL 0)). Qed.
Lemma lem7640722 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7640723 : term83 = term84.
Proof. exact (@lem7640722 term63). Qed.
Lemma lem7640724 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7640725 : term85 = term86.
Proof. exact (MK_COMB (@lem7640724) (@lem7640723)). Qed.
Lemma lem7640726 : term87 = term88.
Proof. exact (MK_COMB (@lem7640725) (@lem7640720)). Qed.
Lemma lem7640727 : term88 = term89.
Proof. exact (@lem1981613 term83 term46 term62 term62). Qed.
Lemma lem7640729 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7640730 : term92 = term93.
Proof. exact (@lem7640729 term63 term63). Qed.
Lemma lem7640731 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7640732 : term95 = term63.
Proof. exact (EQ_MP (@lem7640731) (@lem940073)). Qed.
Lemma lem7640733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7640734 : term93 = term62.
Proof. exact (MK_COMB (@lem7640733) (@lem7640732)). Qed.
Lemma lem7640735 : term92 = term62.
Proof. exact (TRANS (@lem7640730) (@lem7640734)). Qed.
Lemma lem7640737 (x : nat) : (term96 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7640738 : term87 = term46.
Proof. exact (@lem7640737 term63). Qed.
Lemma lem7640739 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7640740 : term97 = term98.
Proof. exact (MK_COMB (@lem7640739) (@lem7640738)). Qed.
Lemma lem7640741 : term89 = term80.
Proof. exact (MK_COMB (@lem7640740) (@lem7640735)). Qed.
Lemma lem7640742 : term88 = term80.
Proof. exact (TRANS (@lem7640727) (@lem7640741)). Qed.
Lemma lem7640743 : term87 = term80.
Proof. exact (TRANS (@lem7640726) (@lem7640742)). Qed.
Lemma lem7640745 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7640746 : term80 = term46.
Proof. exact (@lem7640745 term46). Qed.
Lemma lem7640747 : term87 = term46.
Proof. exact (TRANS (@lem7640743) (@lem7640746)). Qed.
Lemma lem7640748 (_98486 : int) : (term100 _98486) = (term100 _98486).
Proof. exact (eq_refl (term100 _98486)). Qed.
Lemma lem7640749 (_98486 : int) : (term78 _98486) = (term101 _98486).
Proof. exact (MK_COMB (@lem7640748 _98486) (@lem7640747)). Qed.
Lemma lem7640750 (_98486 : int) : (term101 _98486) = (real_of_int _98486).
Proof. exact (@lem1982723 (real_of_int _98486)). Qed.
Lemma lem7640751 (_98486 : int) : (term78 _98486) = (real_of_int _98486).
Proof. exact (TRANS (@lem7640749 _98486) (@lem7640750 _98486)). Qed.
Lemma lem7640753 (_98486 : int) : (term77 _98486) = (real_of_int _98486).
Proof. exact (TRANS (@lem7640717 _98486) (@lem7640751 _98486)). Qed.
Lemma lem7640754 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7640755 (_98486 : int) : (term102 _98486) = (term103 _98486).
Proof. exact (MK_COMB (@lem7640754) (@lem7640753 _98486)). Qed.
Lemma lem7640756 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7640757 (_98486 : int) : (term76 _98486) = (term104 _98486).
Proof. exact (MK_COMB (@lem7640755 _98486) (@lem7640756)). Qed.
Lemma lem7640758 (_98486 : int) : (term49 _98486) = (term104 _98486).
Proof. exact (TRANS (@lem7640711 _98486) (@lem7640757 _98486)). Qed.
Lemma lem7640759 (_98487 : int) : (term49 _98487) = (term76 _98487).
Proof. exact (@lem1988287 (real_of_int _98487) term46). Qed.
Lemma lem7640765 (_98487 : int) : (term77 _98487) = (term78 _98487).
Proof. exact (@lem1982792 (real_of_int _98487) term46). Qed.
Lemma lem7640767 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7640768 : term46 = term80.
Proof. exact (@lem7640767 (NUMERAL 0)). Qed.
Lemma lem7640770 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7640771 : term83 = term84.
Proof. exact (@lem7640770 term63). Qed.
Lemma lem7640772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7640773 : term85 = term86.
Proof. exact (MK_COMB (@lem7640772) (@lem7640771)). Qed.
Lemma lem7640774 : term87 = term88.
Proof. exact (MK_COMB (@lem7640773) (@lem7640768)). Qed.
Lemma lem7640775 : term88 = term89.
Proof. exact (@lem1981613 term83 term46 term62 term62). Qed.
Lemma lem7640777 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7640778 : term92 = term93.
Proof. exact (@lem7640777 term63 term63). Qed.
Lemma lem7640779 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7640780 : term95 = term63.
Proof. exact (EQ_MP (@lem7640779) (@lem940073)). Qed.
Lemma lem7640781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7640782 : term93 = term62.
Proof. exact (MK_COMB (@lem7640781) (@lem7640780)). Qed.
Lemma lem7640783 : term92 = term62.
Proof. exact (TRANS (@lem7640778) (@lem7640782)). Qed.
Lemma lem7640785 (x : nat) : (term96 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7640786 : term87 = term46.
Proof. exact (@lem7640785 term63). Qed.
Lemma lem7640787 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7640788 : term97 = term98.
Proof. exact (MK_COMB (@lem7640787) (@lem7640786)). Qed.
Lemma lem7640789 : term89 = term80.
Proof. exact (MK_COMB (@lem7640788) (@lem7640783)). Qed.
Lemma lem7640790 : term88 = term80.
Proof. exact (TRANS (@lem7640775) (@lem7640789)). Qed.
Lemma lem7640791 : term87 = term80.
Proof. exact (TRANS (@lem7640774) (@lem7640790)). Qed.
Lemma lem7640793 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7640794 : term80 = term46.
Proof. exact (@lem7640793 term46). Qed.
Lemma lem7640795 : term87 = term46.
Proof. exact (TRANS (@lem7640791) (@lem7640794)). Qed.
Lemma lem7640796 (_98487 : int) : (term100 _98487) = (term100 _98487).
Proof. exact (eq_refl (term100 _98487)). Qed.
Lemma lem7640797 (_98487 : int) : (term78 _98487) = (term101 _98487).
Proof. exact (MK_COMB (@lem7640796 _98487) (@lem7640795)). Qed.
Lemma lem7640798 (_98487 : int) : (term101 _98487) = (real_of_int _98487).
Proof. exact (@lem1982723 (real_of_int _98487)). Qed.
Lemma lem7640799 (_98487 : int) : (term78 _98487) = (real_of_int _98487).
Proof. exact (TRANS (@lem7640797 _98487) (@lem7640798 _98487)). Qed.
Lemma lem7640801 (_98487 : int) : (term77 _98487) = (real_of_int _98487).
Proof. exact (TRANS (@lem7640765 _98487) (@lem7640799 _98487)). Qed.
Lemma lem7640802 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7640803 (_98487 : int) : (term102 _98487) = (term103 _98487).
Proof. exact (MK_COMB (@lem7640802) (@lem7640801 _98487)). Qed.
Lemma lem7640804 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7640805 (_98487 : int) : (term76 _98487) = (term104 _98487).
Proof. exact (MK_COMB (@lem7640803 _98487) (@lem7640804)). Qed.
Lemma lem7640806 (_98487 : int) : (term49 _98487) = (term104 _98487).
Proof. exact (TRANS (@lem7640759 _98487) (@lem7640805 _98487)). Qed.
Lemma lem7640807 (_98488 : int) : (term49 _98488) = (term76 _98488).
Proof. exact (@lem1988287 (real_of_int _98488) term46). Qed.
Lemma lem7640813 (_98488 : int) : (term77 _98488) = (term78 _98488).
Proof. exact (@lem1982792 (real_of_int _98488) term46). Qed.
Lemma lem7640815 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7640816 : term46 = term80.
Proof. exact (@lem7640815 (NUMERAL 0)). Qed.
Lemma lem7640818 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7640819 : term83 = term84.
Proof. exact (@lem7640818 term63). Qed.
Lemma lem7640820 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7640821 : term85 = term86.
Proof. exact (MK_COMB (@lem7640820) (@lem7640819)). Qed.
Lemma lem7640822 : term87 = term88.
Proof. exact (MK_COMB (@lem7640821) (@lem7640816)). Qed.
Lemma lem7640823 : term88 = term89.
Proof. exact (@lem1981613 term83 term46 term62 term62). Qed.
Lemma lem7640825 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7640826 : term92 = term93.
Proof. exact (@lem7640825 term63 term63). Qed.
Lemma lem7640827 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7640828 : term95 = term63.
Proof. exact (EQ_MP (@lem7640827) (@lem940073)). Qed.
Lemma lem7640829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7640830 : term93 = term62.
Proof. exact (MK_COMB (@lem7640829) (@lem7640828)). Qed.
Lemma lem7640831 : term92 = term62.
Proof. exact (TRANS (@lem7640826) (@lem7640830)). Qed.
Lemma lem7640833 (x : nat) : (term96 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7640834 : term87 = term46.
Proof. exact (@lem7640833 term63). Qed.
Lemma lem7640835 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7640836 : term97 = term98.
Proof. exact (MK_COMB (@lem7640835) (@lem7640834)). Qed.
Lemma lem7640837 : term89 = term80.
Proof. exact (MK_COMB (@lem7640836) (@lem7640831)). Qed.
Lemma lem7640838 : term88 = term80.
Proof. exact (TRANS (@lem7640823) (@lem7640837)). Qed.
Lemma lem7640839 : term87 = term80.
Proof. exact (TRANS (@lem7640822) (@lem7640838)). Qed.
Lemma lem7640841 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7640842 : term80 = term46.
Proof. exact (@lem7640841 term46). Qed.
Lemma lem7640843 : term87 = term46.
Proof. exact (TRANS (@lem7640839) (@lem7640842)). Qed.
Lemma lem7640844 (_98488 : int) : (term100 _98488) = (term100 _98488).
Proof. exact (eq_refl (term100 _98488)). Qed.
Lemma lem7640845 (_98488 : int) : (term78 _98488) = (term101 _98488).
Proof. exact (MK_COMB (@lem7640844 _98488) (@lem7640843)). Qed.
Lemma lem7640846 (_98488 : int) : (term101 _98488) = (real_of_int _98488).
Proof. exact (@lem1982723 (real_of_int _98488)). Qed.
Lemma lem7640847 (_98488 : int) : (term78 _98488) = (real_of_int _98488).
Proof. exact (TRANS (@lem7640845 _98488) (@lem7640846 _98488)). Qed.
Lemma lem7640849 (_98488 : int) : (term77 _98488) = (real_of_int _98488).
Proof. exact (TRANS (@lem7640813 _98488) (@lem7640847 _98488)). Qed.
Lemma lem7640850 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7640851 (_98488 : int) : (term102 _98488) = (term103 _98488).
Proof. exact (MK_COMB (@lem7640850) (@lem7640849 _98488)). Qed.
Lemma lem7640852 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7640853 (_98488 : int) : (term76 _98488) = (term104 _98488).
Proof. exact (MK_COMB (@lem7640851 _98488) (@lem7640852)). Qed.
Lemma lem7640854 (_98488 : int) : (term49 _98488) = (term104 _98488).
Proof. exact (TRANS (@lem7640807 _98488) (@lem7640853 _98488)). Qed.
Lemma lem7640855 (_98487 : int) (_98486 : int) : (term41 _98486 _98487) = (term105 _98487 _98486).
Proof. exact (@lem1988287 (real_of_int _98487) (real_of_int _98486)). Qed.
Lemma lem7640861 (_98487 : int) (_98486 : int) : (term106 _98487 _98486) = (term107 _98487 _98486).
Proof. exact (@lem1982792 (real_of_int _98487) (real_of_int _98486)). Qed.
Lemma lem7640866 (_98486 : int) (_98487 : int) : (term107 _98487 _98486) = (term108 _98486 _98487).
Proof. exact (@lem1982761 (term109 _98486) (real_of_int _98487)). Qed.
Lemma lem7640868 (_98486 : int) (_98487 : int) : (term106 _98487 _98486) = (term108 _98486 _98487).
Proof. exact (TRANS (@lem7640861 _98487 _98486) (@lem7640866 _98486 _98487)). Qed.
Lemma lem7640869 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7640870 (_98486 : int) (_98487 : int) : (term110 _98487 _98486) = (term111 _98486 _98487).
Proof. exact (MK_COMB (@lem7640869) (@lem7640868 _98486 _98487)). Qed.
Lemma lem7640871 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7640872 (_98486 : int) (_98487 : int) : (term105 _98487 _98486) = (term112 _98486 _98487).
Proof. exact (MK_COMB (@lem7640870 _98486 _98487) (@lem7640871)). Qed.
Lemma lem7640873 (_98486 : int) (_98487 : int) : (term41 _98486 _98487) = (term112 _98486 _98487).
Proof. exact (TRANS (@lem7640855 _98487 _98486) (@lem7640872 _98486 _98487)). Qed.
Lemma lem7640874 (_98486 : int) (_98487 : int) (_98488 : int) : (term67 _98487 _98488 _98486) = (term113 _98486 _98487 _98488).
Proof. exact (@lem1988287 (real_of_int _98486) (term64 _98487 _98488)). Qed.
Lemma lem7640891 (_98487 : int) (_98488 : int) : (term64 _98487 _98488) = (term114 _98487 _98488).
Proof. exact (@lem1982755 (real_of_int _98487) (real_of_int _98488) term62). Qed.
Lemma lem7640894 (_98486 : int) : (term115 _98486) = (term115 _98486).
Proof. exact (eq_refl (term115 _98486)). Qed.
Lemma lem7640895 (_98486 : int) (_98487 : int) (_98488 : int) : (term116 _98486 _98487 _98488) = (term117 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640894 _98486) (@lem7640891 _98487 _98488)). Qed.
Lemma lem7640896 (_98486 : int) (_98487 : int) (_98488 : int) : (term117 _98486 _98487 _98488) = (term118 _98486 _98487 _98488).
Proof. exact (@lem1982792 (real_of_int _98486) (term114 _98487 _98488)). Qed.
Lemma lem7640897 (_98487 : int) (_98488 : int) : (term119 _98487 _98488) = (term120 _98487 _98488).
Proof. exact (@lem1982781 (real_of_int _98487) term83 (term121 _98488)). Qed.
Lemma lem7640898 (_98488 : int) : (term122 _98488) = (term123 _98488).
Proof. exact (@lem1982781 (real_of_int _98488) term83 term62). Qed.
Lemma lem7640900 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7640901 : term62 = term124.
Proof. exact (@lem7640900 term63). Qed.
Lemma lem7640903 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7640904 : term83 = term84.
Proof. exact (@lem7640903 term63). Qed.
Lemma lem7640905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7640906 : term85 = term86.
Proof. exact (MK_COMB (@lem7640905) (@lem7640904)). Qed.
Lemma lem7640907 : term125 = term126.
Proof. exact (MK_COMB (@lem7640906) (@lem7640901)). Qed.
Lemma lem7640908 : term126 = term127.
Proof. exact (@lem1981613 term83 term62 term62 term62). Qed.
Lemma lem7640910 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7640911 : term92 = term93.
Proof. exact (@lem7640910 term63 term63). Qed.
Lemma lem7640912 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7640913 : term95 = term63.
Proof. exact (EQ_MP (@lem7640912) (@lem940073)). Qed.
Lemma lem7640914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7640915 : term93 = term62.
Proof. exact (MK_COMB (@lem7640914) (@lem7640913)). Qed.
Lemma lem7640916 : term92 = term62.
Proof. exact (TRANS (@lem7640911) (@lem7640915)). Qed.
Lemma lem7640918 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7640919 : term125 = term130.
Proof. exact (@lem7640918 term63 term63). Qed.
Lemma lem7640920 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7640921 : term95 = term63.
Proof. exact (EQ_MP (@lem7640920) (@lem940073)). Qed.
Lemma lem7640922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7640923 : term93 = term62.
Proof. exact (MK_COMB (@lem7640922) (@lem7640921)). Qed.
Lemma lem7640924 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7640925 : term130 = term83.
Proof. exact (MK_COMB (@lem7640924) (@lem7640923)). Qed.
Lemma lem7640926 : term125 = term83.
Proof. exact (TRANS (@lem7640919) (@lem7640925)). Qed.
Lemma lem7640927 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7640928 : term131 = term132.
Proof. exact (MK_COMB (@lem7640927) (@lem7640926)). Qed.
Lemma lem7640929 : term127 = term84.
Proof. exact (MK_COMB (@lem7640928) (@lem7640916)). Qed.
Lemma lem7640930 : term126 = term84.
Proof. exact (TRANS (@lem7640908) (@lem7640929)). Qed.
Lemma lem7640931 : term125 = term84.
Proof. exact (TRANS (@lem7640907) (@lem7640930)). Qed.
Lemma lem7640933 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7640934 : term84 = term83.
Proof. exact (@lem7640933 term83). Qed.
Lemma lem7640935 : term125 = term83.
Proof. exact (TRANS (@lem7640931) (@lem7640934)). Qed.
Lemma lem7640938 (_98488 : int) : (term133 _98488) = (term133 _98488).
Proof. exact (eq_refl (term133 _98488)). Qed.
Lemma lem7640939 (_98488 : int) : (term123 _98488) = (term134 _98488).
Proof. exact (MK_COMB (@lem7640938 _98488) (@lem7640935)). Qed.
Lemma lem7640940 (_98488 : int) : (term122 _98488) = (term134 _98488).
Proof. exact (TRANS (@lem7640898 _98488) (@lem7640939 _98488)). Qed.
Lemma lem7640943 (_98487 : int) : (term133 _98487) = (term133 _98487).
Proof. exact (eq_refl (term133 _98487)). Qed.
Lemma lem7640944 (_98487 : int) (_98488 : int) : (term120 _98487 _98488) = (term135 _98487 _98488).
Proof. exact (MK_COMB (@lem7640943 _98487) (@lem7640940 _98488)). Qed.
Lemma lem7640945 (_98487 : int) (_98488 : int) : (term119 _98487 _98488) = (term135 _98487 _98488).
Proof. exact (TRANS (@lem7640897 _98487 _98488) (@lem7640944 _98487 _98488)). Qed.
Lemma lem7640946 (_98486 : int) : (term100 _98486) = (term100 _98486).
Proof. exact (eq_refl (term100 _98486)). Qed.
Lemma lem7640949 (_98486 : int) (_98487 : int) (_98488 : int) : (term118 _98486 _98487 _98488) = (term136 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640946 _98486) (@lem7640945 _98487 _98488)). Qed.
Lemma lem7640950 (_98486 : int) (_98487 : int) (_98488 : int) : (term117 _98486 _98487 _98488) = (term136 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640896 _98486 _98487 _98488) (@lem7640949 _98486 _98487 _98488)). Qed.
Lemma lem7640951 (_98486 : int) (_98487 : int) (_98488 : int) : (term116 _98486 _98487 _98488) = (term136 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640895 _98486 _98487 _98488) (@lem7640950 _98486 _98487 _98488)). Qed.
Lemma lem7640952 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7640953 (_98486 : int) (_98487 : int) (_98488 : int) : (term137 _98486 _98487 _98488) = (term138 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640952) (@lem7640951 _98486 _98487 _98488)). Qed.
Lemma lem7640954 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7640955 (_98486 : int) (_98487 : int) (_98488 : int) : (term113 _98486 _98487 _98488) = (term139 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640953 _98486 _98487 _98488) (@lem7640954)). Qed.
Lemma lem7640956 (_98486 : int) (_98487 : int) (_98488 : int) : (term67 _98487 _98488 _98486) = (term139 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640874 _98486 _98487 _98488) (@lem7640955 _98486 _98487 _98488)). Qed.
Lemma lem7640957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640958 (_98486 : int) (_98487 : int) : (term68 _98486 _98487) = (term140 _98486 _98487).
Proof. exact (MK_COMB (@lem7640957) (@lem7640873 _98486 _98487)). Qed.
Lemma lem7640959 (_98486 : int) (_98487 : int) (_98488 : int) : (term69 _98487 _98488 _98486) = (term141 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640958 _98486 _98487) (@lem7640956 _98486 _98487 _98488)). Qed.
Lemma lem7640960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640961 (_98488 : int) : (term70 _98488) = (term142 _98488).
Proof. exact (MK_COMB (@lem7640960) (@lem7640854 _98488)). Qed.
Lemma lem7640962 (_98486 : int) (_98487 : int) (_98488 : int) : (term71 _98487 _98488 _98486) = (term143 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640961 _98488) (@lem7640959 _98486 _98487 _98488)). Qed.
Lemma lem7640963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640964 (_98487 : int) : (term70 _98487) = (term142 _98487).
Proof. exact (MK_COMB (@lem7640963) (@lem7640806 _98487)). Qed.
Lemma lem7640965 (_98486 : int) (_98487 : int) (_98488 : int) : (term72 _98487 _98488 _98486) = (term144 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640964 _98487) (@lem7640962 _98486 _98487 _98488)). Qed.
Lemma lem7640966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7640967 (_98486 : int) : (term70 _98486) = (term142 _98486).
Proof. exact (MK_COMB (@lem7640966) (@lem7640758 _98486)). Qed.
Lemma lem7640968 (_98486 : int) (_98487 : int) (_98488 : int) : (term73 _98487 _98488 _98486) = (term145 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7640967 _98486) (@lem7640965 _98486 _98487 _98488)). Qed.
Lemma lem7641001 (_98486 : int) (_98487 : int) (_98488 : int) : (term75 _98487 _98488 _98486) = (term145 _98486 _98487 _98488).
Proof. exact (TRANS (@lem7640710 _98487 _98488 _98486) (@lem7640968 _98486 _98487 _98488)). Qed.
Lemma lem7641005 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term145 _98486 _98487 _98488.
Proof. exact (h1). Qed.
Lemma lem7641006 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term144 _98486 _98487 _98488.
Proof. exact (proj2 (@lem7641005 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641008 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term143 _98486 _98487 _98488.
Proof. exact (proj2 (@lem7641006 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641010 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term141 _98486 _98487 _98488.
Proof. exact (proj2 (@lem7641008 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641011 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term104 _98488.
Proof. exact (proj1 (@lem7641008 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641012 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term139 _98486 _98487 _98488.
Proof. exact (proj2 (@lem7641010 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641013 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term112 _98486 _98487.
Proof. exact (proj1 (@lem7641010 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641015 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7641016 : term146 = term147.
Proof. exact (@lem7641015 term46 term62). Qed.
Lemma lem7641018 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641019 : term62 = term124.
Proof. exact (@lem7641018 term63). Qed.
Lemma lem7641021 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641022 : term46 = term80.
Proof. exact (@lem7641021 (NUMERAL 0)). Qed.
Lemma lem7641023 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641024 : term148 = term149.
Proof. exact (MK_COMB (@lem7641023) (@lem7641022)). Qed.
Lemma lem7641025 : term147 = term150.
Proof. exact (MK_COMB (@lem7641024) (@lem7641019)). Qed.
Lemma lem7641026 : term151.
Proof. exact (@lem1980255 term46 term62 term62 term62). Qed.
Lemma lem7641028 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641029 : term147 = term153.
Proof. exact (@lem7641028 (NUMERAL 0) term63). Qed.
Lemma lem7641030 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641031 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641032 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641031 h1) (fun h1 : term153 = True => @lem7641030)). Qed.
Lemma lem7641033 : term153 = True.
Proof. exact (EQ_MP (@lem7641032) (@lem7641030)). Qed.
Lemma lem7641034 : term147 = True.
Proof. exact (TRANS (@lem7641029) (@lem7641033)). Qed.
Lemma lem7641035 : True = term147.
Proof. exact (SYM (@lem7641034)). Qed.
Lemma lem7641036 : term147.
Proof. exact (EQ_MP (@lem7641035) (@lem0)). Qed.
Lemma lem7641037 : term155.
Proof. exact (@lem7641026 (@lem7641036)). Qed.
Lemma lem7641039 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641040 : term147 = term153.
Proof. exact (@lem7641039 (NUMERAL 0) term63). Qed.
Lemma lem7641041 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641042 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641043 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641042 h1) (fun h1 : term153 = True => @lem7641041)). Qed.
Lemma lem7641044 : term153 = True.
Proof. exact (EQ_MP (@lem7641043) (@lem7641041)). Qed.
Lemma lem7641045 : term147 = True.
Proof. exact (TRANS (@lem7641040) (@lem7641044)). Qed.
Lemma lem7641046 : True = term147.
Proof. exact (SYM (@lem7641045)). Qed.
Lemma lem7641047 : term147.
Proof. exact (EQ_MP (@lem7641046) (@lem0)). Qed.
Lemma lem7641048 : term150 = term156.
Proof. exact (@lem7641037 (@lem7641047)). Qed.
Lemma lem7641050 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641051 : term92 = term93.
Proof. exact (@lem7641050 term63 term63). Qed.
Lemma lem7641052 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641053 : term95 = term63.
Proof. exact (EQ_MP (@lem7641052) (@lem940073)). Qed.
Lemma lem7641054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641055 : term93 = term62.
Proof. exact (MK_COMB (@lem7641054) (@lem7641053)). Qed.
Lemma lem7641056 : term92 = term62.
Proof. exact (TRANS (@lem7641051) (@lem7641055)). Qed.
Lemma lem7641058 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641059 : term158 = term46.
Proof. exact (@lem7641058 term63). Qed.
Lemma lem7641060 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641061 : term159 = term148.
Proof. exact (MK_COMB (@lem7641060) (@lem7641059)). Qed.
Lemma lem7641062 : term156 = term147.
Proof. exact (MK_COMB (@lem7641061) (@lem7641056)). Qed.
Lemma lem7641064 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641065 : term147 = term153.
Proof. exact (@lem7641064 (NUMERAL 0) term63). Qed.
Lemma lem7641066 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641067 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641068 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641067 h1) (fun h1 : term153 = True => @lem7641066)). Qed.
Lemma lem7641069 : term153 = True.
Proof. exact (EQ_MP (@lem7641068) (@lem7641066)). Qed.
Lemma lem7641070 : term147 = True.
Proof. exact (TRANS (@lem7641065) (@lem7641069)). Qed.
Lemma lem7641071 : term156 = True.
Proof. exact (TRANS (@lem7641062) (@lem7641070)). Qed.
Lemma lem7641072 : term150 = True.
Proof. exact (TRANS (@lem7641048) (@lem7641071)). Qed.
Lemma lem7641073 : term147 = True.
Proof. exact (TRANS (@lem7641025) (@lem7641072)). Qed.
Lemma lem7641074 : term146 = True.
Proof. exact (TRANS (@lem7641016) (@lem7641073)). Qed.
Lemma lem7641075 : True = term146.
Proof. exact (SYM (@lem7641074)). Qed.
Lemma lem7641076 : term146.
Proof. exact (EQ_MP (@lem7641075) (@lem0)). Qed.
Lemma lem7641077 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term160 _98488.
Proof. exact (conj (@lem7641076) (@lem7641011 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641079 (x : real) (y : real) : term161 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7641080 (_98488 : int) : term162 _98488.
Proof. exact (@lem7641079 term62 (real_of_int _98488)). Qed.
Lemma lem7641081 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term163 _98488.
Proof. exact (@lem7641080 _98488 (@lem7641077 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641082 (_98488 : int) : (term164 _98488) = (real_of_int _98488).
Proof. exact (@lem1982733 (real_of_int _98488)). Qed.
Lemma lem7641083 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7641084 (_98488 : int) : (term165 _98488) = (term103 _98488).
Proof. exact (MK_COMB (@lem7641083) (@lem7641082 _98488)). Qed.
Lemma lem7641085 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7641086 (_98488 : int) : (term163 _98488) = (term104 _98488).
Proof. exact (MK_COMB (@lem7641084 _98488) (@lem7641085)). Qed.
Lemma lem7641087 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term104 _98488.
Proof. exact (EQ_MP (@lem7641086 _98488) (@lem7641081 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641089 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7641090 : term146 = term147.
Proof. exact (@lem7641089 term46 term62). Qed.
Lemma lem7641092 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641093 : term62 = term124.
Proof. exact (@lem7641092 term63). Qed.
Lemma lem7641095 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641096 : term46 = term80.
Proof. exact (@lem7641095 (NUMERAL 0)). Qed.
Lemma lem7641097 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641098 : term148 = term149.
Proof. exact (MK_COMB (@lem7641097) (@lem7641096)). Qed.
Lemma lem7641099 : term147 = term150.
Proof. exact (MK_COMB (@lem7641098) (@lem7641093)). Qed.
Lemma lem7641100 : term151.
Proof. exact (@lem1980255 term46 term62 term62 term62). Qed.
Lemma lem7641102 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641103 : term147 = term153.
Proof. exact (@lem7641102 (NUMERAL 0) term63). Qed.
Lemma lem7641104 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641105 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641106 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641105 h1) (fun h1 : term153 = True => @lem7641104)). Qed.
Lemma lem7641107 : term153 = True.
Proof. exact (EQ_MP (@lem7641106) (@lem7641104)). Qed.
Lemma lem7641108 : term147 = True.
Proof. exact (TRANS (@lem7641103) (@lem7641107)). Qed.
Lemma lem7641109 : True = term147.
Proof. exact (SYM (@lem7641108)). Qed.
Lemma lem7641110 : term147.
Proof. exact (EQ_MP (@lem7641109) (@lem0)). Qed.
Lemma lem7641111 : term155.
Proof. exact (@lem7641100 (@lem7641110)). Qed.
Lemma lem7641113 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641114 : term147 = term153.
Proof. exact (@lem7641113 (NUMERAL 0) term63). Qed.
Lemma lem7641115 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641116 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641117 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641116 h1) (fun h1 : term153 = True => @lem7641115)). Qed.
Lemma lem7641118 : term153 = True.
Proof. exact (EQ_MP (@lem7641117) (@lem7641115)). Qed.
Lemma lem7641119 : term147 = True.
Proof. exact (TRANS (@lem7641114) (@lem7641118)). Qed.
Lemma lem7641120 : True = term147.
Proof. exact (SYM (@lem7641119)). Qed.
Lemma lem7641121 : term147.
Proof. exact (EQ_MP (@lem7641120) (@lem0)). Qed.
Lemma lem7641122 : term150 = term156.
Proof. exact (@lem7641111 (@lem7641121)). Qed.
Lemma lem7641124 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641125 : term92 = term93.
Proof. exact (@lem7641124 term63 term63). Qed.
Lemma lem7641126 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641127 : term95 = term63.
Proof. exact (EQ_MP (@lem7641126) (@lem940073)). Qed.
Lemma lem7641128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641129 : term93 = term62.
Proof. exact (MK_COMB (@lem7641128) (@lem7641127)). Qed.
Lemma lem7641130 : term92 = term62.
Proof. exact (TRANS (@lem7641125) (@lem7641129)). Qed.
Lemma lem7641132 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641133 : term158 = term46.
Proof. exact (@lem7641132 term63). Qed.
Lemma lem7641134 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641135 : term159 = term148.
Proof. exact (MK_COMB (@lem7641134) (@lem7641133)). Qed.
Lemma lem7641136 : term156 = term147.
Proof. exact (MK_COMB (@lem7641135) (@lem7641130)). Qed.
Lemma lem7641138 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641139 : term147 = term153.
Proof. exact (@lem7641138 (NUMERAL 0) term63). Qed.
Lemma lem7641140 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641141 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641142 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641141 h1) (fun h1 : term153 = True => @lem7641140)). Qed.
Lemma lem7641143 : term153 = True.
Proof. exact (EQ_MP (@lem7641142) (@lem7641140)). Qed.
Lemma lem7641144 : term147 = True.
Proof. exact (TRANS (@lem7641139) (@lem7641143)). Qed.
Lemma lem7641145 : term156 = True.
Proof. exact (TRANS (@lem7641136) (@lem7641144)). Qed.
Lemma lem7641146 : term150 = True.
Proof. exact (TRANS (@lem7641122) (@lem7641145)). Qed.
Lemma lem7641147 : term147 = True.
Proof. exact (TRANS (@lem7641099) (@lem7641146)). Qed.
Lemma lem7641148 : term146 = True.
Proof. exact (TRANS (@lem7641090) (@lem7641147)). Qed.
Lemma lem7641149 : True = term146.
Proof. exact (SYM (@lem7641148)). Qed.
Lemma lem7641150 : term146.
Proof. exact (EQ_MP (@lem7641149) (@lem0)). Qed.
Lemma lem7641151 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term166 _98486 _98487 _98488.
Proof. exact (conj (@lem7641150) (@lem7641012 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641153 (x : real) (y : real) : term161 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7641154 (_98486 : int) (_98487 : int) (_98488 : int) : term167 _98486 _98487 _98488.
Proof. exact (@lem7641153 term62 (term136 _98486 _98487 _98488)). Qed.
Lemma lem7641155 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term168 _98486 _98487 _98488.
Proof. exact (@lem7641154 _98486 _98487 _98488 (@lem7641151 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641156 (_98486 : int) (_98487 : int) (_98488 : int) : (term169 _98486 _98487 _98488) = (term136 _98486 _98487 _98488).
Proof. exact (@lem1982733 (term136 _98486 _98487 _98488)). Qed.
Lemma lem7641157 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7641158 (_98486 : int) (_98487 : int) (_98488 : int) : (term170 _98486 _98487 _98488) = (term138 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7641157) (@lem7641156 _98486 _98487 _98488)). Qed.
Lemma lem7641159 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7641160 (_98486 : int) (_98487 : int) (_98488 : int) : (term168 _98486 _98487 _98488) = (term139 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7641158 _98486 _98487 _98488) (@lem7641159)). Qed.
Lemma lem7641161 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term139 _98486 _98487 _98488.
Proof. exact (EQ_MP (@lem7641160 _98486 _98487 _98488) (@lem7641155 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641162 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term171 _98486 _98487 _98488.
Proof. exact (conj (@lem7641161 _98486 _98487 _98488 h1) (@lem7641087 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641164 (x : real) (y : real) : term172 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7641165 (_98486 : int) (_98487 : int) (_98488 : int) : term173 _98486 _98487 _98488.
Proof. exact (@lem7641164 (term136 _98486 _98487 _98488) (real_of_int _98488)). Qed.
Lemma lem7641166 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term174 _98486 _98487 _98488.
Proof. exact (@lem7641165 _98486 _98487 _98488 (@lem7641162 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641167 (_98486 : int) (_98487 : int) (_98488 : int) : (term175 _98486 _98487 _98488) = (term176 _98486 _98487 _98488).
Proof. exact (@lem1982755 (real_of_int _98486) (term135 _98487 _98488) (real_of_int _98488)). Qed.
Lemma lem7641168 (_98487 : int) (_98488 : int) : (term177 _98487 _98488) = (term178 _98487 _98488).
Proof. exact (@lem1982755 (term109 _98487) (term134 _98488) (real_of_int _98488)). Qed.
Lemma lem7641169 (_98488 : int) : (term179 _98488) = (term180 _98488).
Proof. exact (@lem1982759 (term109 _98488) (real_of_int _98488) term83). Qed.
Lemma lem7641170 (_98488 : int) : (term181 _98488) = (term182 _98488).
Proof. exact (@lem1982713 term83 (real_of_int _98488)). Qed.
Lemma lem7641172 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641173 : term62 = term124.
Proof. exact (@lem7641172 term63). Qed.
Lemma lem7641175 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7641176 : term83 = term84.
Proof. exact (@lem7641175 term63). Qed.
Lemma lem7641177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641178 : term183 = term184.
Proof. exact (MK_COMB (@lem7641177) (@lem7641176)). Qed.
Lemma lem7641179 : term185 = term186.
Proof. exact (MK_COMB (@lem7641178) (@lem7641173)). Qed.
Lemma lem7641180 : term187.
Proof. exact (@lem1981473 term83 term62 term62 term62 term46 term62). Qed.
Lemma lem7641182 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641183 : term147 = term153.
Proof. exact (@lem7641182 (NUMERAL 0) term63). Qed.
Lemma lem7641184 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641185 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641186 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641185 h1) (fun h1 : term153 = True => @lem7641184)). Qed.
Lemma lem7641187 : term153 = True.
Proof. exact (EQ_MP (@lem7641186) (@lem7641184)). Qed.
Lemma lem7641188 : term147 = True.
Proof. exact (TRANS (@lem7641183) (@lem7641187)). Qed.
Lemma lem7641189 : True = term147.
Proof. exact (SYM (@lem7641188)). Qed.
Lemma lem7641190 : term147.
Proof. exact (EQ_MP (@lem7641189) (@lem0)). Qed.
Lemma lem7641191 : term188.
Proof. exact (@lem7641180 (@lem7641190)). Qed.
Lemma lem7641193 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641194 : term147 = term153.
Proof. exact (@lem7641193 (NUMERAL 0) term63). Qed.
Lemma lem7641195 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641196 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641197 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641196 h1) (fun h1 : term153 = True => @lem7641195)). Qed.
Lemma lem7641198 : term153 = True.
Proof. exact (EQ_MP (@lem7641197) (@lem7641195)). Qed.
Lemma lem7641199 : term147 = True.
Proof. exact (TRANS (@lem7641194) (@lem7641198)). Qed.
Lemma lem7641200 : True = term147.
Proof. exact (SYM (@lem7641199)). Qed.
Lemma lem7641201 : term147.
Proof. exact (EQ_MP (@lem7641200) (@lem0)). Qed.
Lemma lem7641202 : term189.
Proof. exact (@lem7641191 (@lem7641201)). Qed.
Lemma lem7641204 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641205 : term147 = term153.
Proof. exact (@lem7641204 (NUMERAL 0) term63). Qed.
Lemma lem7641206 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641207 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641208 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641207 h1) (fun h1 : term153 = True => @lem7641206)). Qed.
Lemma lem7641209 : term153 = True.
Proof. exact (EQ_MP (@lem7641208) (@lem7641206)). Qed.
Lemma lem7641210 : term147 = True.
Proof. exact (TRANS (@lem7641205) (@lem7641209)). Qed.
Lemma lem7641211 : True = term147.
Proof. exact (SYM (@lem7641210)). Qed.
Lemma lem7641212 : term147.
Proof. exact (EQ_MP (@lem7641211) (@lem0)). Qed.
Lemma lem7641213 : term190.
Proof. exact (@lem7641202 (@lem7641212)). Qed.
Lemma lem7641215 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641216 : term92 = term93.
Proof. exact (@lem7641215 term63 term63). Qed.
Lemma lem7641217 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641218 : term95 = term63.
Proof. exact (EQ_MP (@lem7641217) (@lem940073)). Qed.
Lemma lem7641219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641220 : term93 = term62.
Proof. exact (MK_COMB (@lem7641219) (@lem7641218)). Qed.
Lemma lem7641221 : term92 = term62.
Proof. exact (TRANS (@lem7641216) (@lem7641220)). Qed.
Lemma lem7641223 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7641224 : term125 = term130.
Proof. exact (@lem7641223 term63 term63). Qed.
Lemma lem7641225 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641226 : term95 = term63.
Proof. exact (EQ_MP (@lem7641225) (@lem940073)). Qed.
Lemma lem7641227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641228 : term93 = term62.
Proof. exact (MK_COMB (@lem7641227) (@lem7641226)). Qed.
Lemma lem7641229 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7641230 : term130 = term83.
Proof. exact (MK_COMB (@lem7641229) (@lem7641228)). Qed.
Lemma lem7641231 : term125 = term83.
Proof. exact (TRANS (@lem7641224) (@lem7641230)). Qed.
Lemma lem7641232 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641233 : term191 = term183.
Proof. exact (MK_COMB (@lem7641232) (@lem7641231)). Qed.
Lemma lem7641234 : term192 = term185.
Proof. exact (MK_COMB (@lem7641233) (@lem7641221)). Qed.
Lemma lem7641236 (m : nat) : (term193 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7641237 : term185 = term46.
Proof. exact (@lem7641236 term63). Qed.
Lemma lem7641238 : term192 = term46.
Proof. exact (TRANS (@lem7641234) (@lem7641237)). Qed.
Lemma lem7641239 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7641240 : term194 = term195.
Proof. exact (MK_COMB (@lem7641239) (@lem7641238)). Qed.
Lemma lem7641241 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7641242 : term196 = term158.
Proof. exact (MK_COMB (@lem7641240) (@lem7641241)). Qed.
Lemma lem7641244 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641245 : term158 = term46.
Proof. exact (@lem7641244 term63). Qed.
Lemma lem7641246 : term196 = term46.
Proof. exact (TRANS (@lem7641242) (@lem7641245)). Qed.
Lemma lem7641248 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641249 : term92 = term93.
Proof. exact (@lem7641248 term63 term63). Qed.
Lemma lem7641250 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641251 : term95 = term63.
Proof. exact (EQ_MP (@lem7641250) (@lem940073)). Qed.
Lemma lem7641252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641253 : term93 = term62.
Proof. exact (MK_COMB (@lem7641252) (@lem7641251)). Qed.
Lemma lem7641254 : term92 = term62.
Proof. exact (TRANS (@lem7641249) (@lem7641253)). Qed.
Lemma lem7641255 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem7641256 : term197 = term158.
Proof. exact (MK_COMB (@lem7641255) (@lem7641254)). Qed.
Lemma lem7641258 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641259 : term158 = term46.
Proof. exact (@lem7641258 term63). Qed.
Lemma lem7641260 : term197 = term46.
Proof. exact (TRANS (@lem7641256) (@lem7641259)). Qed.
Lemma lem7641261 : term46 = term197.
Proof. exact (SYM (@lem7641260)). Qed.
Lemma lem7641262 : term196 = term197.
Proof. exact (TRANS (@lem7641246) (@lem7641261)). Qed.
Lemma lem7641263 : term186 = term80.
Proof. exact (@lem7641213 (@lem7641262)). Qed.
Lemma lem7641264 : term185 = term80.
Proof. exact (TRANS (@lem7641179) (@lem7641263)). Qed.
Lemma lem7641266 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7641267 : term80 = term46.
Proof. exact (@lem7641266 term46). Qed.
Lemma lem7641268 : term185 = term46.
Proof. exact (TRANS (@lem7641264) (@lem7641267)). Qed.
Lemma lem7641269 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7641270 : term198 = term195.
Proof. exact (MK_COMB (@lem7641269) (@lem7641268)). Qed.
Lemma lem7641271 (_98488 : int) : (real_of_int _98488) = (real_of_int _98488).
Proof. exact (eq_refl (real_of_int _98488)). Qed.
Lemma lem7641272 (_98488 : int) : (term182 _98488) = (term199 _98488).
Proof. exact (MK_COMB (@lem7641270) (@lem7641271 _98488)). Qed.
Lemma lem7641273 (_98488 : int) : (term181 _98488) = (term199 _98488).
Proof. exact (TRANS (@lem7641170 _98488) (@lem7641272 _98488)). Qed.
Lemma lem7641274 (_98488 : int) : (term199 _98488) = term46.
Proof. exact (@lem1982719 (real_of_int _98488)). Qed.
Lemma lem7641275 (_98488 : int) : (term181 _98488) = term46.
Proof. exact (TRANS (@lem7641273 _98488) (@lem7641274 _98488)). Qed.
Lemma lem7641276 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641277 (_98488 : int) : (term200 _98488) = term201.
Proof. exact (MK_COMB (@lem7641276) (@lem7641275 _98488)). Qed.
Lemma lem7641278 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem7641279 (_98488 : int) : (term180 _98488) = term202.
Proof. exact (MK_COMB (@lem7641277 _98488) (@lem7641278)). Qed.
Lemma lem7641280 (_98488 : int) : (term179 _98488) = term202.
Proof. exact (TRANS (@lem7641169 _98488) (@lem7641279 _98488)). Qed.
Lemma lem7641281 : term202 = term83.
Proof. exact (@lem1982721 term83). Qed.
Lemma lem7641282 (_98488 : int) : (term179 _98488) = term83.
Proof. exact (TRANS (@lem7641280 _98488) (@lem7641281)). Qed.
Lemma lem7641283 (_98487 : int) : (term133 _98487) = (term133 _98487).
Proof. exact (eq_refl (term133 _98487)). Qed.
Lemma lem7641284 (_98488 : int) (_98487 : int) : (term178 _98487 _98488) = (term134 _98487).
Proof. exact (MK_COMB (@lem7641283 _98487) (@lem7641282 _98488)). Qed.
Lemma lem7641285 (_98488 : int) (_98487 : int) : (term177 _98487 _98488) = (term134 _98487).
Proof. exact (TRANS (@lem7641168 _98487 _98488) (@lem7641284 _98488 _98487)). Qed.
Lemma lem7641286 (_98486 : int) : (term100 _98486) = (term100 _98486).
Proof. exact (eq_refl (term100 _98486)). Qed.
Lemma lem7641287 (_98488 : int) (_98486 : int) (_98487 : int) : (term176 _98486 _98487 _98488) = (term203 _98486 _98487).
Proof. exact (MK_COMB (@lem7641286 _98486) (@lem7641285 _98488 _98487)). Qed.
Lemma lem7641288 (_98488 : int) (_98486 : int) (_98487 : int) : (term175 _98486 _98487 _98488) = (term203 _98486 _98487).
Proof. exact (TRANS (@lem7641167 _98486 _98487 _98488) (@lem7641287 _98488 _98486 _98487)). Qed.
Lemma lem7641289 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7641290 (_98488 : int) (_98486 : int) (_98487 : int) : (term204 _98486 _98487 _98488) = (term205 _98486 _98487).
Proof. exact (MK_COMB (@lem7641289) (@lem7641288 _98488 _98486 _98487)). Qed.
Lemma lem7641291 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7641292 (_98488 : int) (_98486 : int) (_98487 : int) : (term174 _98486 _98487 _98488) = (term206 _98486 _98487).
Proof. exact (MK_COMB (@lem7641290 _98488 _98486 _98487) (@lem7641291)). Qed.
Lemma lem7641293 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term206 _98486 _98487.
Proof. exact (EQ_MP (@lem7641292 _98488 _98486 _98487) (@lem7641166 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641295 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7641296 : term146 = term147.
Proof. exact (@lem7641295 term46 term62). Qed.
Lemma lem7641298 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641299 : term62 = term124.
Proof. exact (@lem7641298 term63). Qed.
Lemma lem7641301 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641302 : term46 = term80.
Proof. exact (@lem7641301 (NUMERAL 0)). Qed.
Lemma lem7641303 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641304 : term148 = term149.
Proof. exact (MK_COMB (@lem7641303) (@lem7641302)). Qed.
Lemma lem7641305 : term147 = term150.
Proof. exact (MK_COMB (@lem7641304) (@lem7641299)). Qed.
Lemma lem7641306 : term151.
Proof. exact (@lem1980255 term46 term62 term62 term62). Qed.
Lemma lem7641308 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641309 : term147 = term153.
Proof. exact (@lem7641308 (NUMERAL 0) term63). Qed.
Lemma lem7641310 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641311 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641312 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641311 h1) (fun h1 : term153 = True => @lem7641310)). Qed.
Lemma lem7641313 : term153 = True.
Proof. exact (EQ_MP (@lem7641312) (@lem7641310)). Qed.
Lemma lem7641314 : term147 = True.
Proof. exact (TRANS (@lem7641309) (@lem7641313)). Qed.
Lemma lem7641315 : True = term147.
Proof. exact (SYM (@lem7641314)). Qed.
Lemma lem7641316 : term147.
Proof. exact (EQ_MP (@lem7641315) (@lem0)). Qed.
Lemma lem7641317 : term155.
Proof. exact (@lem7641306 (@lem7641316)). Qed.
Lemma lem7641319 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641320 : term147 = term153.
Proof. exact (@lem7641319 (NUMERAL 0) term63). Qed.
Lemma lem7641321 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641322 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641323 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641322 h1) (fun h1 : term153 = True => @lem7641321)). Qed.
Lemma lem7641324 : term153 = True.
Proof. exact (EQ_MP (@lem7641323) (@lem7641321)). Qed.
Lemma lem7641325 : term147 = True.
Proof. exact (TRANS (@lem7641320) (@lem7641324)). Qed.
Lemma lem7641326 : True = term147.
Proof. exact (SYM (@lem7641325)). Qed.
Lemma lem7641327 : term147.
Proof. exact (EQ_MP (@lem7641326) (@lem0)). Qed.
Lemma lem7641328 : term150 = term156.
Proof. exact (@lem7641317 (@lem7641327)). Qed.
Lemma lem7641330 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641331 : term92 = term93.
Proof. exact (@lem7641330 term63 term63). Qed.
Lemma lem7641332 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641333 : term95 = term63.
Proof. exact (EQ_MP (@lem7641332) (@lem940073)). Qed.
Lemma lem7641334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641335 : term93 = term62.
Proof. exact (MK_COMB (@lem7641334) (@lem7641333)). Qed.
Lemma lem7641336 : term92 = term62.
Proof. exact (TRANS (@lem7641331) (@lem7641335)). Qed.
Lemma lem7641338 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641339 : term158 = term46.
Proof. exact (@lem7641338 term63). Qed.
Lemma lem7641340 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641341 : term159 = term148.
Proof. exact (MK_COMB (@lem7641340) (@lem7641339)). Qed.
Lemma lem7641342 : term156 = term147.
Proof. exact (MK_COMB (@lem7641341) (@lem7641336)). Qed.
Lemma lem7641344 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641345 : term147 = term153.
Proof. exact (@lem7641344 (NUMERAL 0) term63). Qed.
Lemma lem7641346 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641347 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641348 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641347 h1) (fun h1 : term153 = True => @lem7641346)). Qed.
Lemma lem7641349 : term153 = True.
Proof. exact (EQ_MP (@lem7641348) (@lem7641346)). Qed.
Lemma lem7641350 : term147 = True.
Proof. exact (TRANS (@lem7641345) (@lem7641349)). Qed.
Lemma lem7641351 : term156 = True.
Proof. exact (TRANS (@lem7641342) (@lem7641350)). Qed.
Lemma lem7641352 : term150 = True.
Proof. exact (TRANS (@lem7641328) (@lem7641351)). Qed.
Lemma lem7641353 : term147 = True.
Proof. exact (TRANS (@lem7641305) (@lem7641352)). Qed.
Lemma lem7641354 : term146 = True.
Proof. exact (TRANS (@lem7641296) (@lem7641353)). Qed.
Lemma lem7641355 : True = term146.
Proof. exact (SYM (@lem7641354)). Qed.
Lemma lem7641356 : term146.
Proof. exact (EQ_MP (@lem7641355) (@lem0)). Qed.
Lemma lem7641357 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term207 _98486 _98487.
Proof. exact (conj (@lem7641356) (@lem7641293 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641359 (x : real) (y : real) : term161 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7641360 (_98486 : int) (_98487 : int) : term208 _98486 _98487.
Proof. exact (@lem7641359 term62 (term203 _98486 _98487)). Qed.
Lemma lem7641361 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term209 _98486 _98487.
Proof. exact (@lem7641360 _98486 _98487 (@lem7641357 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641362 (_98486 : int) (_98487 : int) : (term210 _98486 _98487) = (term203 _98486 _98487).
Proof. exact (@lem1982733 (term203 _98486 _98487)). Qed.
Lemma lem7641363 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7641364 (_98486 : int) (_98487 : int) : (term211 _98486 _98487) = (term205 _98486 _98487).
Proof. exact (MK_COMB (@lem7641363) (@lem7641362 _98486 _98487)). Qed.
Lemma lem7641365 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7641366 (_98486 : int) (_98487 : int) : (term209 _98486 _98487) = (term206 _98486 _98487).
Proof. exact (MK_COMB (@lem7641364 _98486 _98487) (@lem7641365)). Qed.
Lemma lem7641367 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term206 _98486 _98487.
Proof. exact (EQ_MP (@lem7641366 _98486 _98487) (@lem7641361 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641369 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7641370 : term146 = term147.
Proof. exact (@lem7641369 term46 term62). Qed.
Lemma lem7641372 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641373 : term62 = term124.
Proof. exact (@lem7641372 term63). Qed.
Lemma lem7641375 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641376 : term46 = term80.
Proof. exact (@lem7641375 (NUMERAL 0)). Qed.
Lemma lem7641377 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641378 : term148 = term149.
Proof. exact (MK_COMB (@lem7641377) (@lem7641376)). Qed.
Lemma lem7641379 : term147 = term150.
Proof. exact (MK_COMB (@lem7641378) (@lem7641373)). Qed.
Lemma lem7641380 : term151.
Proof. exact (@lem1980255 term46 term62 term62 term62). Qed.
Lemma lem7641382 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641383 : term147 = term153.
Proof. exact (@lem7641382 (NUMERAL 0) term63). Qed.
Lemma lem7641384 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641385 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641386 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641385 h1) (fun h1 : term153 = True => @lem7641384)). Qed.
Lemma lem7641387 : term153 = True.
Proof. exact (EQ_MP (@lem7641386) (@lem7641384)). Qed.
Lemma lem7641388 : term147 = True.
Proof. exact (TRANS (@lem7641383) (@lem7641387)). Qed.
Lemma lem7641389 : True = term147.
Proof. exact (SYM (@lem7641388)). Qed.
Lemma lem7641390 : term147.
Proof. exact (EQ_MP (@lem7641389) (@lem0)). Qed.
Lemma lem7641391 : term155.
Proof. exact (@lem7641380 (@lem7641390)). Qed.
Lemma lem7641393 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641394 : term147 = term153.
Proof. exact (@lem7641393 (NUMERAL 0) term63). Qed.
Lemma lem7641395 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641396 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641397 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641396 h1) (fun h1 : term153 = True => @lem7641395)). Qed.
Lemma lem7641398 : term153 = True.
Proof. exact (EQ_MP (@lem7641397) (@lem7641395)). Qed.
Lemma lem7641399 : term147 = True.
Proof. exact (TRANS (@lem7641394) (@lem7641398)). Qed.
Lemma lem7641400 : True = term147.
Proof. exact (SYM (@lem7641399)). Qed.
Lemma lem7641401 : term147.
Proof. exact (EQ_MP (@lem7641400) (@lem0)). Qed.
Lemma lem7641402 : term150 = term156.
Proof. exact (@lem7641391 (@lem7641401)). Qed.
Lemma lem7641404 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641405 : term92 = term93.
Proof. exact (@lem7641404 term63 term63). Qed.
Lemma lem7641406 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641407 : term95 = term63.
Proof. exact (EQ_MP (@lem7641406) (@lem940073)). Qed.
Lemma lem7641408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641409 : term93 = term62.
Proof. exact (MK_COMB (@lem7641408) (@lem7641407)). Qed.
Lemma lem7641410 : term92 = term62.
Proof. exact (TRANS (@lem7641405) (@lem7641409)). Qed.
Lemma lem7641412 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641413 : term158 = term46.
Proof. exact (@lem7641412 term63). Qed.
Lemma lem7641414 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7641415 : term159 = term148.
Proof. exact (MK_COMB (@lem7641414) (@lem7641413)). Qed.
Lemma lem7641416 : term156 = term147.
Proof. exact (MK_COMB (@lem7641415) (@lem7641410)). Qed.
Lemma lem7641418 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641419 : term147 = term153.
Proof. exact (@lem7641418 (NUMERAL 0) term63). Qed.
Lemma lem7641420 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641421 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641422 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641421 h1) (fun h1 : term153 = True => @lem7641420)). Qed.
Lemma lem7641423 : term153 = True.
Proof. exact (EQ_MP (@lem7641422) (@lem7641420)). Qed.
Lemma lem7641424 : term147 = True.
Proof. exact (TRANS (@lem7641419) (@lem7641423)). Qed.
Lemma lem7641425 : term156 = True.
Proof. exact (TRANS (@lem7641416) (@lem7641424)). Qed.
Lemma lem7641426 : term150 = True.
Proof. exact (TRANS (@lem7641402) (@lem7641425)). Qed.
Lemma lem7641427 : term147 = True.
Proof. exact (TRANS (@lem7641379) (@lem7641426)). Qed.
Lemma lem7641428 : term146 = True.
Proof. exact (TRANS (@lem7641370) (@lem7641427)). Qed.
Lemma lem7641429 : True = term146.
Proof. exact (SYM (@lem7641428)). Qed.
Lemma lem7641430 : term146.
Proof. exact (EQ_MP (@lem7641429) (@lem0)). Qed.
Lemma lem7641431 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term212 _98486 _98487.
Proof. exact (conj (@lem7641430) (@lem7641013 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641433 (x : real) (y : real) : term161 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7641434 (_98486 : int) (_98487 : int) : term213 _98486 _98487.
Proof. exact (@lem7641433 term62 (term108 _98486 _98487)). Qed.
Lemma lem7641435 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term214 _98486 _98487.
Proof. exact (@lem7641434 _98486 _98487 (@lem7641431 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641436 (_98486 : int) (_98487 : int) : (term215 _98486 _98487) = (term108 _98486 _98487).
Proof. exact (@lem1982733 (term108 _98486 _98487)). Qed.
Lemma lem7641437 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7641438 (_98486 : int) (_98487 : int) : (term216 _98486 _98487) = (term111 _98486 _98487).
Proof. exact (MK_COMB (@lem7641437) (@lem7641436 _98486 _98487)). Qed.
Lemma lem7641439 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7641440 (_98486 : int) (_98487 : int) : (term214 _98486 _98487) = (term112 _98486 _98487).
Proof. exact (MK_COMB (@lem7641438 _98486 _98487) (@lem7641439)). Qed.
Lemma lem7641441 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term112 _98486 _98487.
Proof. exact (EQ_MP (@lem7641440 _98486 _98487) (@lem7641435 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641442 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term217 _98486 _98487.
Proof. exact (conj (@lem7641441 _98486 _98487 _98488 h1) (@lem7641367 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641444 (x : real) (y : real) : term172 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7641445 (_98486 : int) (_98487 : int) : term218 _98486 _98487.
Proof. exact (@lem7641444 (term108 _98486 _98487) (term203 _98486 _98487)). Qed.
Lemma lem7641446 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term219 _98486 _98487.
Proof. exact (@lem7641445 _98486 _98487 (@lem7641442 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641447 (_98486 : int) (_98487 : int) : (term220 _98486 _98487) = (term221 _98486 _98487).
Proof. exact (@lem1982753 (term109 _98486) (real_of_int _98486) (real_of_int _98487) (term134 _98487)). Qed.
Lemma lem7641448 (_98486 : int) : (term181 _98486) = (term182 _98486).
Proof. exact (@lem1982713 term83 (real_of_int _98486)). Qed.
Lemma lem7641450 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641451 : term62 = term124.
Proof. exact (@lem7641450 term63). Qed.
Lemma lem7641453 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7641454 : term83 = term84.
Proof. exact (@lem7641453 term63). Qed.
Lemma lem7641455 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641456 : term183 = term184.
Proof. exact (MK_COMB (@lem7641455) (@lem7641454)). Qed.
Lemma lem7641457 : term185 = term186.
Proof. exact (MK_COMB (@lem7641456) (@lem7641451)). Qed.
Lemma lem7641458 : term187.
Proof. exact (@lem1981473 term83 term62 term62 term62 term46 term62). Qed.
Lemma lem7641460 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641461 : term147 = term153.
Proof. exact (@lem7641460 (NUMERAL 0) term63). Qed.
Lemma lem7641462 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641463 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641464 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641463 h1) (fun h1 : term153 = True => @lem7641462)). Qed.
Lemma lem7641465 : term153 = True.
Proof. exact (EQ_MP (@lem7641464) (@lem7641462)). Qed.
Lemma lem7641466 : term147 = True.
Proof. exact (TRANS (@lem7641461) (@lem7641465)). Qed.
Lemma lem7641467 : True = term147.
Proof. exact (SYM (@lem7641466)). Qed.
Lemma lem7641468 : term147.
Proof. exact (EQ_MP (@lem7641467) (@lem0)). Qed.
Lemma lem7641469 : term188.
Proof. exact (@lem7641458 (@lem7641468)). Qed.
Lemma lem7641471 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641472 : term147 = term153.
Proof. exact (@lem7641471 (NUMERAL 0) term63). Qed.
Lemma lem7641473 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641474 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641475 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641474 h1) (fun h1 : term153 = True => @lem7641473)). Qed.
Lemma lem7641476 : term153 = True.
Proof. exact (EQ_MP (@lem7641475) (@lem7641473)). Qed.
Lemma lem7641477 : term147 = True.
Proof. exact (TRANS (@lem7641472) (@lem7641476)). Qed.
Lemma lem7641478 : True = term147.
Proof. exact (SYM (@lem7641477)). Qed.
Lemma lem7641479 : term147.
Proof. exact (EQ_MP (@lem7641478) (@lem0)). Qed.
Lemma lem7641480 : term189.
Proof. exact (@lem7641469 (@lem7641479)). Qed.
Lemma lem7641482 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641483 : term147 = term153.
Proof. exact (@lem7641482 (NUMERAL 0) term63). Qed.
Lemma lem7641484 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641485 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641486 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641485 h1) (fun h1 : term153 = True => @lem7641484)). Qed.
Lemma lem7641487 : term153 = True.
Proof. exact (EQ_MP (@lem7641486) (@lem7641484)). Qed.
Lemma lem7641488 : term147 = True.
Proof. exact (TRANS (@lem7641483) (@lem7641487)). Qed.
Lemma lem7641489 : True = term147.
Proof. exact (SYM (@lem7641488)). Qed.
Lemma lem7641490 : term147.
Proof. exact (EQ_MP (@lem7641489) (@lem0)). Qed.
Lemma lem7641491 : term190.
Proof. exact (@lem7641480 (@lem7641490)). Qed.
Lemma lem7641493 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641494 : term92 = term93.
Proof. exact (@lem7641493 term63 term63). Qed.
Lemma lem7641495 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641496 : term95 = term63.
Proof. exact (EQ_MP (@lem7641495) (@lem940073)). Qed.
Lemma lem7641497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641498 : term93 = term62.
Proof. exact (MK_COMB (@lem7641497) (@lem7641496)). Qed.
Lemma lem7641499 : term92 = term62.
Proof. exact (TRANS (@lem7641494) (@lem7641498)). Qed.
Lemma lem7641501 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7641502 : term125 = term130.
Proof. exact (@lem7641501 term63 term63). Qed.
Lemma lem7641503 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641504 : term95 = term63.
Proof. exact (EQ_MP (@lem7641503) (@lem940073)). Qed.
Lemma lem7641505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641506 : term93 = term62.
Proof. exact (MK_COMB (@lem7641505) (@lem7641504)). Qed.
Lemma lem7641507 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7641508 : term130 = term83.
Proof. exact (MK_COMB (@lem7641507) (@lem7641506)). Qed.
Lemma lem7641509 : term125 = term83.
Proof. exact (TRANS (@lem7641502) (@lem7641508)). Qed.
Lemma lem7641510 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641511 : term191 = term183.
Proof. exact (MK_COMB (@lem7641510) (@lem7641509)). Qed.
Lemma lem7641512 : term192 = term185.
Proof. exact (MK_COMB (@lem7641511) (@lem7641499)). Qed.
Lemma lem7641514 (m : nat) : (term193 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7641515 : term185 = term46.
Proof. exact (@lem7641514 term63). Qed.
Lemma lem7641516 : term192 = term46.
Proof. exact (TRANS (@lem7641512) (@lem7641515)). Qed.
Lemma lem7641517 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7641518 : term194 = term195.
Proof. exact (MK_COMB (@lem7641517) (@lem7641516)). Qed.
Lemma lem7641519 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7641520 : term196 = term158.
Proof. exact (MK_COMB (@lem7641518) (@lem7641519)). Qed.
Lemma lem7641522 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641523 : term158 = term46.
Proof. exact (@lem7641522 term63). Qed.
Lemma lem7641524 : term196 = term46.
Proof. exact (TRANS (@lem7641520) (@lem7641523)). Qed.
Lemma lem7641526 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641527 : term92 = term93.
Proof. exact (@lem7641526 term63 term63). Qed.
Lemma lem7641528 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641529 : term95 = term63.
Proof. exact (EQ_MP (@lem7641528) (@lem940073)). Qed.
Lemma lem7641530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641531 : term93 = term62.
Proof. exact (MK_COMB (@lem7641530) (@lem7641529)). Qed.
Lemma lem7641532 : term92 = term62.
Proof. exact (TRANS (@lem7641527) (@lem7641531)). Qed.
Lemma lem7641533 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem7641534 : term197 = term158.
Proof. exact (MK_COMB (@lem7641533) (@lem7641532)). Qed.
Lemma lem7641536 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641537 : term158 = term46.
Proof. exact (@lem7641536 term63). Qed.
Lemma lem7641538 : term197 = term46.
Proof. exact (TRANS (@lem7641534) (@lem7641537)). Qed.
Lemma lem7641539 : term46 = term197.
Proof. exact (SYM (@lem7641538)). Qed.
Lemma lem7641540 : term196 = term197.
Proof. exact (TRANS (@lem7641524) (@lem7641539)). Qed.
Lemma lem7641541 : term186 = term80.
Proof. exact (@lem7641491 (@lem7641540)). Qed.
Lemma lem7641542 : term185 = term80.
Proof. exact (TRANS (@lem7641457) (@lem7641541)). Qed.
Lemma lem7641544 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7641545 : term80 = term46.
Proof. exact (@lem7641544 term46). Qed.
Lemma lem7641546 : term185 = term46.
Proof. exact (TRANS (@lem7641542) (@lem7641545)). Qed.
Lemma lem7641547 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7641548 : term198 = term195.
Proof. exact (MK_COMB (@lem7641547) (@lem7641546)). Qed.
Lemma lem7641549 (_98486 : int) : (real_of_int _98486) = (real_of_int _98486).
Proof. exact (eq_refl (real_of_int _98486)). Qed.
Lemma lem7641550 (_98486 : int) : (term182 _98486) = (term199 _98486).
Proof. exact (MK_COMB (@lem7641548) (@lem7641549 _98486)). Qed.
Lemma lem7641551 (_98486 : int) : (term181 _98486) = (term199 _98486).
Proof. exact (TRANS (@lem7641448 _98486) (@lem7641550 _98486)). Qed.
Lemma lem7641552 (_98486 : int) : (term199 _98486) = term46.
Proof. exact (@lem1982719 (real_of_int _98486)). Qed.
Lemma lem7641553 (_98486 : int) : (term181 _98486) = term46.
Proof. exact (TRANS (@lem7641551 _98486) (@lem7641552 _98486)). Qed.
Lemma lem7641554 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641555 (_98486 : int) : (term200 _98486) = term201.
Proof. exact (MK_COMB (@lem7641554) (@lem7641553 _98486)). Qed.
Lemma lem7641556 (_98487 : int) : (term222 _98487) = (term223 _98487).
Proof. exact (@lem1982763 (real_of_int _98487) (term109 _98487) term83). Qed.
Lemma lem7641557 (_98487 : int) : (term224 _98487) = (term182 _98487).
Proof. exact (@lem1982715 term83 (real_of_int _98487)). Qed.
Lemma lem7641559 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641560 : term62 = term124.
Proof. exact (@lem7641559 term63). Qed.
Lemma lem7641562 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7641563 : term83 = term84.
Proof. exact (@lem7641562 term63). Qed.
Lemma lem7641564 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641565 : term183 = term184.
Proof. exact (MK_COMB (@lem7641564) (@lem7641563)). Qed.
Lemma lem7641566 : term185 = term186.
Proof. exact (MK_COMB (@lem7641565) (@lem7641560)). Qed.
Lemma lem7641567 : term187.
Proof. exact (@lem1981473 term83 term62 term62 term62 term46 term62). Qed.
Lemma lem7641569 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641570 : term147 = term153.
Proof. exact (@lem7641569 (NUMERAL 0) term63). Qed.
Lemma lem7641571 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641572 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641573 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641572 h1) (fun h1 : term153 = True => @lem7641571)). Qed.
Lemma lem7641574 : term153 = True.
Proof. exact (EQ_MP (@lem7641573) (@lem7641571)). Qed.
Lemma lem7641575 : term147 = True.
Proof. exact (TRANS (@lem7641570) (@lem7641574)). Qed.
Lemma lem7641576 : True = term147.
Proof. exact (SYM (@lem7641575)). Qed.
Lemma lem7641577 : term147.
Proof. exact (EQ_MP (@lem7641576) (@lem0)). Qed.
Lemma lem7641578 : term188.
Proof. exact (@lem7641567 (@lem7641577)). Qed.
Lemma lem7641580 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641581 : term147 = term153.
Proof. exact (@lem7641580 (NUMERAL 0) term63). Qed.
Lemma lem7641582 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641583 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641584 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641583 h1) (fun h1 : term153 = True => @lem7641582)). Qed.
Lemma lem7641585 : term153 = True.
Proof. exact (EQ_MP (@lem7641584) (@lem7641582)). Qed.
Lemma lem7641586 : term147 = True.
Proof. exact (TRANS (@lem7641581) (@lem7641585)). Qed.
Lemma lem7641587 : True = term147.
Proof. exact (SYM (@lem7641586)). Qed.
Lemma lem7641588 : term147.
Proof. exact (EQ_MP (@lem7641587) (@lem0)). Qed.
Lemma lem7641589 : term189.
Proof. exact (@lem7641578 (@lem7641588)). Qed.
Lemma lem7641591 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641592 : term147 = term153.
Proof. exact (@lem7641591 (NUMERAL 0) term63). Qed.
Lemma lem7641593 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641594 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641595 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641594 h1) (fun h1 : term153 = True => @lem7641593)). Qed.
Lemma lem7641596 : term153 = True.
Proof. exact (EQ_MP (@lem7641595) (@lem7641593)). Qed.
Lemma lem7641597 : term147 = True.
Proof. exact (TRANS (@lem7641592) (@lem7641596)). Qed.
Lemma lem7641598 : True = term147.
Proof. exact (SYM (@lem7641597)). Qed.
Lemma lem7641599 : term147.
Proof. exact (EQ_MP (@lem7641598) (@lem0)). Qed.
Lemma lem7641600 : term190.
Proof. exact (@lem7641589 (@lem7641599)). Qed.
Lemma lem7641602 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641603 : term92 = term93.
Proof. exact (@lem7641602 term63 term63). Qed.
Lemma lem7641604 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641605 : term95 = term63.
Proof. exact (EQ_MP (@lem7641604) (@lem940073)). Qed.
Lemma lem7641606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641607 : term93 = term62.
Proof. exact (MK_COMB (@lem7641606) (@lem7641605)). Qed.
Lemma lem7641608 : term92 = term62.
Proof. exact (TRANS (@lem7641603) (@lem7641607)). Qed.
Lemma lem7641610 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7641611 : term125 = term130.
Proof. exact (@lem7641610 term63 term63). Qed.
Lemma lem7641612 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641613 : term95 = term63.
Proof. exact (EQ_MP (@lem7641612) (@lem940073)). Qed.
Lemma lem7641614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641615 : term93 = term62.
Proof. exact (MK_COMB (@lem7641614) (@lem7641613)). Qed.
Lemma lem7641616 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7641617 : term130 = term83.
Proof. exact (MK_COMB (@lem7641616) (@lem7641615)). Qed.
Lemma lem7641618 : term125 = term83.
Proof. exact (TRANS (@lem7641611) (@lem7641617)). Qed.
Lemma lem7641619 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641620 : term191 = term183.
Proof. exact (MK_COMB (@lem7641619) (@lem7641618)). Qed.
Lemma lem7641621 : term192 = term185.
Proof. exact (MK_COMB (@lem7641620) (@lem7641608)). Qed.
Lemma lem7641623 (m : nat) : (term193 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7641624 : term185 = term46.
Proof. exact (@lem7641623 term63). Qed.
Lemma lem7641625 : term192 = term46.
Proof. exact (TRANS (@lem7641621) (@lem7641624)). Qed.
Lemma lem7641626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7641627 : term194 = term195.
Proof. exact (MK_COMB (@lem7641626) (@lem7641625)). Qed.
Lemma lem7641628 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7641629 : term196 = term158.
Proof. exact (MK_COMB (@lem7641627) (@lem7641628)). Qed.
Lemma lem7641631 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641632 : term158 = term46.
Proof. exact (@lem7641631 term63). Qed.
Lemma lem7641633 : term196 = term46.
Proof. exact (TRANS (@lem7641629) (@lem7641632)). Qed.
Lemma lem7641635 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7641636 : term92 = term93.
Proof. exact (@lem7641635 term63 term63). Qed.
Lemma lem7641637 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641638 : term95 = term63.
Proof. exact (EQ_MP (@lem7641637) (@lem940073)). Qed.
Lemma lem7641639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641640 : term93 = term62.
Proof. exact (MK_COMB (@lem7641639) (@lem7641638)). Qed.
Lemma lem7641641 : term92 = term62.
Proof. exact (TRANS (@lem7641636) (@lem7641640)). Qed.
Lemma lem7641642 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem7641643 : term197 = term158.
Proof. exact (MK_COMB (@lem7641642) (@lem7641641)). Qed.
Lemma lem7641645 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641646 : term158 = term46.
Proof. exact (@lem7641645 term63). Qed.
Lemma lem7641647 : term197 = term46.
Proof. exact (TRANS (@lem7641643) (@lem7641646)). Qed.
Lemma lem7641648 : term46 = term197.
Proof. exact (SYM (@lem7641647)). Qed.
Lemma lem7641649 : term196 = term197.
Proof. exact (TRANS (@lem7641633) (@lem7641648)). Qed.
Lemma lem7641650 : term186 = term80.
Proof. exact (@lem7641600 (@lem7641649)). Qed.
Lemma lem7641651 : term185 = term80.
Proof. exact (TRANS (@lem7641566) (@lem7641650)). Qed.
Lemma lem7641653 (x : real) : (term99 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7641654 : term80 = term46.
Proof. exact (@lem7641653 term46). Qed.
Lemma lem7641655 : term185 = term46.
Proof. exact (TRANS (@lem7641651) (@lem7641654)). Qed.
Lemma lem7641656 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7641657 : term198 = term195.
Proof. exact (MK_COMB (@lem7641656) (@lem7641655)). Qed.
Lemma lem7641658 (_98487 : int) : (real_of_int _98487) = (real_of_int _98487).
Proof. exact (eq_refl (real_of_int _98487)). Qed.
Lemma lem7641659 (_98487 : int) : (term182 _98487) = (term199 _98487).
Proof. exact (MK_COMB (@lem7641657) (@lem7641658 _98487)). Qed.
Lemma lem7641660 (_98487 : int) : (term224 _98487) = (term199 _98487).
Proof. exact (TRANS (@lem7641557 _98487) (@lem7641659 _98487)). Qed.
Lemma lem7641661 (_98487 : int) : (term199 _98487) = term46.
Proof. exact (@lem1982719 (real_of_int _98487)). Qed.
Lemma lem7641662 (_98487 : int) : (term224 _98487) = term46.
Proof. exact (TRANS (@lem7641660 _98487) (@lem7641661 _98487)). Qed.
Lemma lem7641663 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7641664 (_98487 : int) : (term225 _98487) = term201.
Proof. exact (MK_COMB (@lem7641663) (@lem7641662 _98487)). Qed.
Lemma lem7641665 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem7641666 (_98487 : int) : (term223 _98487) = term202.
Proof. exact (MK_COMB (@lem7641664 _98487) (@lem7641665)). Qed.
Lemma lem7641667 (_98487 : int) : (term222 _98487) = term202.
Proof. exact (TRANS (@lem7641556 _98487) (@lem7641666 _98487)). Qed.
Lemma lem7641668 : term202 = term83.
Proof. exact (@lem1982721 term83). Qed.
Lemma lem7641669 (_98487 : int) : (term222 _98487) = term83.
Proof. exact (TRANS (@lem7641667 _98487) (@lem7641668)). Qed.
Lemma lem7641670 (_98486 : int) (_98487 : int) : (term221 _98486 _98487) = term202.
Proof. exact (MK_COMB (@lem7641555 _98486) (@lem7641669 _98487)). Qed.
Lemma lem7641671 (_98486 : int) (_98487 : int) : (term220 _98486 _98487) = term202.
Proof. exact (TRANS (@lem7641447 _98486 _98487) (@lem7641670 _98486 _98487)). Qed.
Lemma lem7641672 : term202 = term83.
Proof. exact (@lem1982721 term83). Qed.
Lemma lem7641673 (_98486 : int) (_98487 : int) : (term220 _98486 _98487) = term83.
Proof. exact (TRANS (@lem7641671 _98486 _98487) (@lem7641672)). Qed.
Lemma lem7641674 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7641675 (_98486 : int) (_98487 : int) : (term226 _98486 _98487) = term227.
Proof. exact (MK_COMB (@lem7641674) (@lem7641673 _98486 _98487)). Qed.
Lemma lem7641676 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7641677 (_98486 : int) (_98487 : int) : (term219 _98486 _98487) = term228.
Proof. exact (MK_COMB (@lem7641675 _98486 _98487) (@lem7641676)). Qed.
Lemma lem7641678 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term228.
Proof. exact (EQ_MP (@lem7641677 _98486 _98487) (@lem7641446 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641680 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7641681 : term228 = term229.
Proof. exact (@lem7641680 term46 term83). Qed.
Lemma lem7641683 (x : nat) : (term81 x) = (term82 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7641684 : term83 = term84.
Proof. exact (@lem7641683 term63). Qed.
Lemma lem7641686 (x : nat) : (real_of_num x) = (term79 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7641687 : term46 = term80.
Proof. exact (@lem7641686 (NUMERAL 0)). Qed.
Lemma lem7641688 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7641689 : term48 = term230.
Proof. exact (MK_COMB (@lem7641688) (@lem7641687)). Qed.
Lemma lem7641690 : term229 = term231.
Proof. exact (MK_COMB (@lem7641689) (@lem7641684)). Qed.
Lemma lem7641691 : term232.
Proof. exact (@lem1980026 term46 term62 term83 term62). Qed.
Lemma lem7641693 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641694 : term147 = term153.
Proof. exact (@lem7641693 (NUMERAL 0) term63). Qed.
Lemma lem7641695 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641696 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641697 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641696 h1) (fun h1 : term153 = True => @lem7641695)). Qed.
Lemma lem7641698 : term153 = True.
Proof. exact (EQ_MP (@lem7641697) (@lem7641695)). Qed.
Lemma lem7641699 : term147 = True.
Proof. exact (TRANS (@lem7641694) (@lem7641698)). Qed.
Lemma lem7641700 : True = term147.
Proof. exact (SYM (@lem7641699)). Qed.
Lemma lem7641701 : term147.
Proof. exact (EQ_MP (@lem7641700) (@lem0)). Qed.
Lemma lem7641702 : term233.
Proof. exact (@lem7641691 (@lem7641701)). Qed.
Lemma lem7641704 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7641705 : term147 = term153.
Proof. exact (@lem7641704 (NUMERAL 0) term63). Qed.
Lemma lem7641706 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641707 (h1 : term154 = (BIT1 0)) : term153 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7641708 : (term154 = (BIT1 0)) = (term153 = True).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641707 h1) (fun h1 : term153 = True => @lem7641706)). Qed.
Lemma lem7641709 : term153 = True.
Proof. exact (EQ_MP (@lem7641708) (@lem7641706)). Qed.
Lemma lem7641710 : term147 = True.
Proof. exact (TRANS (@lem7641705) (@lem7641709)). Qed.
Lemma lem7641711 : True = term147.
Proof. exact (SYM (@lem7641710)). Qed.
Lemma lem7641712 : term147.
Proof. exact (EQ_MP (@lem7641711) (@lem0)). Qed.
Lemma lem7641713 : term231 = term234.
Proof. exact (@lem7641702 (@lem7641712)). Qed.
Lemma lem7641715 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7641716 : term125 = term130.
Proof. exact (@lem7641715 term63 term63). Qed.
Lemma lem7641717 : (term94 = (BIT1 0)) = (term95 = term63).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7641718 : term95 = term63.
Proof. exact (EQ_MP (@lem7641717) (@lem940073)). Qed.
Lemma lem7641719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7641720 : term93 = term62.
Proof. exact (MK_COMB (@lem7641719) (@lem7641718)). Qed.
Lemma lem7641721 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7641722 : term130 = term83.
Proof. exact (MK_COMB (@lem7641721) (@lem7641720)). Qed.
Lemma lem7641723 : term125 = term83.
Proof. exact (TRANS (@lem7641716) (@lem7641722)). Qed.
Lemma lem7641725 (x : nat) : (term157 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7641726 : term158 = term46.
Proof. exact (@lem7641725 term63). Qed.
Lemma lem7641727 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7641728 : term235 = term48.
Proof. exact (MK_COMB (@lem7641727) (@lem7641726)). Qed.
Lemma lem7641729 : term234 = term229.
Proof. exact (MK_COMB (@lem7641728) (@lem7641723)). Qed.
Lemma lem7641731 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7641732 : term229 = term238.
Proof. exact (@lem7641731 (NUMERAL 0) term63). Qed.
Lemma lem7641733 : term154 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7641734 (h1 : term154 = (BIT1 0)) : (term63 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7641735 : (term154 = (BIT1 0)) = ((term63 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term154 = (BIT1 0) => @lem7641734 h1) (fun h1 : (term63 = (NUMERAL 0)) = False => @lem7641733)). Qed.
Lemma lem7641736 : (term63 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7641735) (@lem7641733)). Qed.
Lemma lem7641737 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7641738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7641739 : term239 = (and True).
Proof. exact (MK_COMB (@lem7641738) (@lem7641737)). Qed.
Lemma lem7641740 : term238 = (True /\ False).
Proof. exact (MK_COMB (@lem7641739) (@lem7641736)). Qed.
Lemma lem7641742 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7641743 : term238 = False.
Proof. exact (TRANS (@lem7641740) (@lem7641742)). Qed.
Lemma lem7641744 : term229 = False.
Proof. exact (TRANS (@lem7641732) (@lem7641743)). Qed.
Lemma lem7641745 : term234 = False.
Proof. exact (TRANS (@lem7641729) (@lem7641744)). Qed.
Lemma lem7641746 : term231 = False.
Proof. exact (TRANS (@lem7641713) (@lem7641745)). Qed.
Lemma lem7641747 : term229 = False.
Proof. exact (TRANS (@lem7641690) (@lem7641746)). Qed.
Lemma lem7641748 : term228 = False.
Proof. exact (TRANS (@lem7641681) (@lem7641747)). Qed.
Lemma lem7641749 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : False.
Proof. exact (EQ_MP (@lem7641748) (@lem7641678 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641751 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : term145 _98486 _98487 _98488.
Proof. exact (h1). Qed.
Lemma lem7641752 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : (term145 _98486 _98487 _98488) = False.
Proof. exact (prop_ext (fun h2 : term145 _98486 _98487 _98488 => @lem7641749 _98486 _98487 _98488 h1) (fun h2 : False => @lem7641751 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641753 (_98486 : int) (_98487 : int) (_98488 : int) (h1 : term145 _98486 _98487 _98488) : False.
Proof. exact (EQ_MP (@lem7641752 _98486 _98487 _98488 h1) (@lem7641751 _98486 _98487 _98488 h1)). Qed.
Lemma lem7641754 (_98487 : int) (_98488 : int) (_98486 : int) (h1 : term75 _98487 _98488 _98486) : term75 _98487 _98488 _98486.
Proof. exact (h1). Qed.
Lemma lem7641755 (_98487 : int) (_98488 : int) (_98486 : int) (h1 : term75 _98487 _98488 _98486) : term145 _98486 _98487 _98488.
Proof. exact (EQ_MP (@lem7641001 _98486 _98487 _98488) (@lem7641754 _98487 _98488 _98486 h1)). Qed.
Lemma lem7641756 (_98487 : int) (_98488 : int) (_98486 : int) (h1 : term75 _98487 _98488 _98486) : (term145 _98486 _98487 _98488) = False.
Proof. exact (prop_ext (fun h2 : term145 _98486 _98487 _98488 => @lem7641753 _98486 _98487 _98488 h2) (fun h2 : False => @lem7641755 _98487 _98488 _98486 h1)). Qed.
Lemma lem7641757 (_98487 : int) (_98488 : int) (_98486 : int) (h1 : term75 _98487 _98488 _98486) : False.
Proof. exact (EQ_MP (@lem7641756 _98487 _98488 _98486 h1) (@lem7641755 _98487 _98488 _98486 h1)). Qed.
Lemma lem7641758 (_98487 : int) (_98488 : int) (_98486 : int) : term240 _98487 _98488 _98486.
Proof. exact (fun h0 : term75 _98487 _98488 _98486 => @lem7641757 _98487 _98488 _98486 h0). Qed.
Lemma lem7641759 (_98487 : int) (_98488 : int) (_98486 : int) : term241 _98487 _98488 _98486.
Proof. exact (@lem1386578 (term242 _98487 _98488 _98486)). Qed.
Lemma lem7641762 (_98487 : int) (_98488 : int) (_98486 : int) : term242 _98487 _98488 _98486.
Proof. exact (@lem7641759 _98487 _98488 _98486 (@lem7641758 _98487 _98488 _98486)). Qed.
Lemma lem7641763 (_98486 : int) (_98487 : int) (_98488 : int) : (term73 _98487 _98488 _98486) = (term39 _98486 _98487 _98488).
Proof. exact (SYM (@lem7640660 _98487 _98488 _98486)). Qed.
Lemma lem7641764 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7641765 (_98486 : int) (_98487 : int) (_98488 : int) : (term242 _98487 _98488 _98486) = (term16 _98486 _98487 _98488).
Proof. exact (MK_COMB (@lem7641764) (@lem7641763 _98486 _98487 _98488)). Qed.
Lemma lem7641766 (_98486 : int) (_98487 : int) (_98488 : int) : term16 _98486 _98487 _98488.
Proof. exact (EQ_MP (@lem7641765 _98486 _98487 _98488) (@lem7641762 _98487 _98488 _98486)). Qed.
Lemma lem7641767 (_98486 : int) (_98487 : int) (_98488 : int) : term17 _98486 _98487 _98488.
Proof. exact (EQ_MP (@lem7640517 _98486 _98487 _98488) (@lem7641766 _98486 _98487 _98488)). Qed.
Lemma lem7641768 (a : nat) (b : nat) (c : nat) : term243 a b c.
Proof. exact (@lem7641767 (int_of_num a) (int_of_num b) (int_of_num c)). Qed.
Lemma lem7641769 (a : nat) (b : nat) (c : nat) : term244 a b c.
Proof. exact (@lem7641768 a b c (@lem7640510 a)). Qed.
Lemma lem7641770 (a : nat) (b : nat) (c : nat) : term245 a b c.
Proof. exact (@lem7641769 a b c (@lem7640513 b)). Qed.
Lemma lem7641771 (a : nat) (b : nat) (c : nat) : term13 a b c.
Proof. exact (@lem7641770 a b c (@lem7640516 c)). Qed.
Lemma lem7641772 (a : nat) (b : nat) (c : nat) : (term13 a b c) = (term0 a b c).
Proof. exact (SYM (@lem7640507 a b c)). Qed.
Lemma lem7641773 (a : nat) (b : nat) (c : nat) : term0 a b c.
Proof. exact (EQ_MP (@lem7641772 a b c) (@lem7641771 a b c)). Qed.
Lemma lem7641774 (a : nat) (b : nat) (h1 : Peano.le a b) : Peano.le a b.
Proof. exact (h1). Qed.
Lemma lem7641775 (c : nat) (a : nat) (b : nat) (h1 : Peano.le a b) : term2 a b c.
Proof. exact (@lem7641773 a b c (@lem7641774 a b h1)). Qed.
Lemma lem7641776 (a : nat) (b : nat) (c : nat) : (term2 a b c) = ((term2 a b c) = True).
Proof. exact (@lem7 (term2 a b c)). Qed.
Lemma lem7641777 (c : nat) (a : nat) (b : nat) (h1 : Peano.le a b) : (term2 a b c) = True.
Proof. exact (EQ_MP (@lem7641776 a b c) (@lem7641775 c a b h1)). Qed.
Lemma lem7641783 {A B : Type'} (g : nat -> A) (i : nat) : term246 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7641784 {A B : Type'} (g : nat -> A) (i : nat) : (term246 A B g i) = (term247 A B g i).
Proof. exact (eq_refl (term246 A B g i)). Qed.
Lemma lem7641785 {A B : Type'} (g : nat -> A) (i : nat) : term247 A B g i.
Proof. exact (EQ_MP (@lem7641784 A B g i) (@lem7641783 A B g i)). Qed.
Lemma lem7641786 {B : Type'} (i : nat) (h1 : term248 B i) : term248 B i.
Proof. exact (h1). Qed.
Lemma lem7641787 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term248 B i) : (term249 A B g i) = (g i).
Proof. exact (@lem7641785 A B g i (@lem7641786 B i h1)). Qed.
Lemma lem7641793 {A B : Type'} (x : cart A B) : term250 A B x.
Proof. exact (@lem7617066 A B x). Qed.
Lemma lem7641794 {A B : Type'} (x : cart A B) : (term250 A B x) = (term251 A B x).
Proof. exact (eq_refl (term250 A B x)). Qed.
Lemma lem7641795 {A B : Type'} (x : cart A B) : term251 A B x.
Proof. exact (EQ_MP (@lem7641794 A B x) (@lem7641793 A B x)). Qed.
Lemma lem7641796 {A B : Type'} (x : cart A B) (y : cart A B) : term252 A B x y.
Proof. exact (@lem7641795 A B x y). Qed.
Lemma lem7641797 {A B : Type'} (x : cart A B) (y : cart A B) : (term252 A B x y) = ((x = y) = (term253 A B x y)).
Proof. exact (eq_refl (term252 A B x y)). Qed.
Lemma lem7641799 {A M N : Type'} (f : type2 A M N) : term254 A M N f.
Proof. exact (@lem7633949 A M N f). Qed.
Lemma lem7641800 {A M N : Type'} (f : type2 A M N) : (term254 A M N f) = ((@fstcart A M N f) = (term255 A M N f)).
Proof. exact (eq_refl (term254 A M N f)). Qed.
Lemma lem7641802 {A M N : Type'} (f : cart A M) : term256 A M N f.
Proof. exact (@lem7632649 A M N f). Qed.
Lemma lem7641803 {A M N : Type'} (f : cart A M) : (term256 A M N f) = (term257 A M N f).
Proof. exact (eq_refl (term256 A M N f)). Qed.
Lemma lem7641804 {A M N : Type'} (f : cart A M) : term257 A M N f.
Proof. exact (EQ_MP (@lem7641803 A M N f) (@lem7641802 A M N f)). Qed.
Lemma lem7641805 {A M N : Type'} (f : cart A M) (g : cart A N) : term258 A M N f g.
Proof. exact (@lem7641804 A M N f g). Qed.
Lemma lem7641806 {A M N : Type'} (f : cart A M) (g : cart A N) : (term258 A M N f g) = ((@pastecart A M N f g) = (term259 A M N f g)).
Proof. exact (eq_refl (term258 A M N f g)). Qed.
Lemma lem7641819 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term253 A B x y).
Proof. exact (EQ_MP (@lem7641797 A B x y) (@lem7641796 A B x y)). Qed.
Lemma lem7641820 {A M : Type'} (x : cart A M) (y : cart A M) : (x = y) = (term253 A M x y).
Proof. exact (@lem7641819 A M x y). Qed.
Lemma lem7641821 {A M N : Type'} (y : cart A N) (x : cart A M) : ((term260 A M N x y) = x) = (term261 A M N y x).
Proof. exact (@lem7641820 A M (term260 A M N x y) x). Qed.
Lemma lem7641829 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term262 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7641830 (p : Prop) (q : Prop) (p' : Prop) : term263 p q p'.
Proof. exact (fun q' : Prop => @lem7641829 p q p' q'). Qed.
Lemma lem7641831 (p : Prop) (q : Prop) : term264 p q.
Proof. exact (fun p' : Prop => @lem7641830 p q p'). Qed.
Lemma lem7641832 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) : term265 A M N y x i.
Proof. exact (@lem7641831 (term248 M i) ((term266 A M N x y i) = (@dollar A M x i))). Qed.
Lemma lem7641833 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (p' : Prop) : term267 A M N y x i p'.
Proof. exact (@lem7641832 A M N y x i p'). Qed.
Lemma lem7641834 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (p' : Prop) : (term267 A M N y x i p') = (term268 A M N y x i p').
Proof. exact (eq_refl (term267 A M N y x i p')). Qed.
Lemma lem7641835 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (p' : Prop) : term268 A M N y x i p'.
Proof. exact (EQ_MP (@lem7641834 A M N y x i p') (@lem7641833 A M N y x i p')). Qed.
Lemma lem7641836 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (p' : Prop) (q' : Prop) : term269 A M N y x i p' q'.
Proof. exact (@lem7641835 A M N y x i p' q'). Qed.
Lemma lem7641837 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (p' : Prop) (q' : Prop) : (term269 A M N y x i p' q') = (term270 A M N y x i p' q').
Proof. exact (eq_refl (term269 A M N y x i p' q')). Qed.
Lemma lem7641838 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (p' : Prop) (q' : Prop) : term270 A M N y x i p' q'.
Proof. exact (EQ_MP (@lem7641837 A M N y x i p' q') (@lem7641836 A M N y x i p' q')). Qed.
Lemma lem7641843 {M : Type'} (i : nat) : (term248 M i) = (term248 M i).
Proof. exact (eq_refl (term248 M i)). Qed.
Lemma lem7641844 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (q' : Prop) : term271 A M N y x i q'.
Proof. exact (@lem7641838 A M N y x i (term248 M i) q'). Qed.
Lemma lem7641845 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (q' : Prop) : term272 A M N y x i q'.
Proof. exact (@lem7641844 A M N y x i q' (@lem7641843 M i)). Qed.
Lemma lem7641846 {M : Type'} (i : nat) (h1 : term248 M i) : term248 M i.
Proof. exact (h1). Qed.
Lemma lem7641847 {M : Type'} (i : nat) (h1 : term248 M i) : term273 M i.
Proof. exact (proj2 (@lem7641846 M i h1)). Qed.
Lemma lem7641848 {M : Type'} (i : nat) : (term273 M i) = ((term273 M i) = True).
Proof. exact (@lem7 (term273 M i)). Qed.
Lemma lem7641850 {M : Type'} (i : nat) (h1 : term248 M i) : term274 i.
Proof. exact (proj1 (@lem7641846 M i h1)). Qed.
Lemma lem7641851 (i : nat) : (term274 i) = ((term274 i) = True).
Proof. exact (@lem7 (term274 i)). Qed.
Lemma lem7641858 {A M N : Type'} (f : type2 A M N) : (@fstcart A M N f) = (term255 A M N f).
Proof. exact (EQ_MP (@lem7641800 A M N f) (@lem7641799 A M N f)). Qed.
Lemma lem7641859 {A M N : Type'} (f : type2 A M N) : (@fstcart A M N f) = (term255 A M N f).
Proof. exact (@lem7641858 A M N f). Qed.
Lemma lem7641860 {A M N : Type'} (x : cart A M) (y : cart A N) : (term260 A M N x y) = (term275 A M N x y).
Proof. exact (@lem7641859 A M N (@pastecart A M N x y)). Qed.
Lemma lem7642135 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term259 A M N f g).
Proof. exact (EQ_MP (@lem7641806 A M N f g) (@lem7641805 A M N f g)). Qed.
Lemma lem7642136 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term259 A M N f g).
Proof. exact (@lem7642135 A M N f g). Qed.
Lemma lem7642137 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pastecart A M N x y) = (term259 A M N x y).
Proof. exact (@lem7642136 A M N x y). Qed.
Lemma lem7642222 {A M N : Type'} : (@dollar A (finite_sum M N)) = (@dollar A (finite_sum M N)).
Proof. exact (eq_refl (@dollar A (finite_sum M N))). Qed.
Lemma lem7642223 {A M N : Type'} (x : cart A M) (y : cart A N) : (term276 A M N x y) = (term277 A M N x y).
Proof. exact (MK_COMB (@lem7642222 A M N) (@lem7642137 A M N x y)). Qed.
Lemma lem7642308 (_98494 : nat) : _98494 = _98494.
Proof. exact (eq_refl _98494). Qed.
Lemma lem7642309 {A M N : Type'} (x : cart A M) (y : cart A N) (_98494 : nat) : (term278 A M N x y _98494) = (term279 A M N x y _98494).
Proof. exact (MK_COMB (@lem7642223 A M N x y) (@lem7642308 _98494)). Qed.
Lemma lem7642437 {A M N : Type'} (x : cart A M) (y : cart A N) : (term280 A M N x y) = (term281 A M N x y).
Proof. exact (fun_ext (fun _98494 : nat => @lem7642309 A M N x y _98494)). Qed.
Lemma lem7642659 {A M : Type'} : (@lambda A M) = (@lambda A M).
Proof. exact (eq_refl (@lambda A M)). Qed.
Lemma lem7642660 {A M N : Type'} (x : cart A M) (y : cart A N) : (term275 A M N x y) = (term282 A M N x y).
Proof. exact (MK_COMB (@lem7642659 A M) (@lem7642437 A M N x y)). Qed.
Lemma lem7642882 {A M N : Type'} (x : cart A M) (y : cart A N) : (term260 A M N x y) = (term282 A M N x y).
Proof. exact (TRANS (@lem7641860 A M N x y) (@lem7642660 A M N x y)). Qed.
Lemma lem7642883 {A M : Type'} : (@dollar A M) = (@dollar A M).
Proof. exact (eq_refl (@dollar A M)). Qed.
Lemma lem7642884 {A M N : Type'} (x : cart A M) (y : cart A N) : (term283 A M N x y) = (term284 A M N x y).
Proof. exact (MK_COMB (@lem7642883 A M) (@lem7642882 A M N x y)). Qed.
Lemma lem7643106 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7643107 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term266 A M N x y i) = (term285 A M N x y i).
Proof. exact (MK_COMB (@lem7642884 A M N x y) (@lem7643106 i)). Qed.
Lemma lem7643109 {A B : Type'} (g : nat -> A) (i : nat) : term247 A B g i.
Proof. exact (fun h0 : term248 B i => @lem7641787 A B g i h0). Qed.
Lemma lem7643110 {A M : Type'} (g : nat -> A) (i : nat) : term247 A M g i.
Proof. exact (@lem7643109 A M g i). Qed.
Lemma lem7643111 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term286 A M N x y i.
Proof. exact (@lem7643110 A M (term281 A M N x y) i). Qed.
Lemma lem7643115 {M : Type'} (i : nat) (h1 : term248 M i) : (term274 i) = True.
Proof. exact (EQ_MP (@lem7641851 i) (@lem7641850 M i h1)). Qed.
Lemma lem7643116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643117 {M : Type'} (i : nat) (h1 : term248 M i) : (term287 i) = (and True).
Proof. exact (MK_COMB (@lem7643116) (@lem7643115 M i h1)). Qed.
Lemma lem7643119 {M : Type'} (i : nat) (h1 : term248 M i) : (term273 M i) = True.
Proof. exact (EQ_MP (@lem7641848 M i) (@lem7641847 M i h1)). Qed.
Lemma lem7643120 {M : Type'} (i : nat) (h1 : term248 M i) : (term248 M i) = (True /\ True).
Proof. exact (MK_COMB (@lem7643117 M i h1) (@lem7643119 M i h1)). Qed.
Lemma lem7643122 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7643123 : (True /\ True) = True.
Proof. exact (@lem7643122 True). Qed.
Lemma lem7643124 {M : Type'} (i : nat) (h1 : term248 M i) : (term248 M i) = True.
Proof. exact (TRANS (@lem7643120 M i h1) (@lem7643123)). Qed.
Lemma lem7643125 {M : Type'} (i : nat) (h1 : term248 M i) : True = (term248 M i).
Proof. exact (SYM (@lem7643124 M i h1)). Qed.
Lemma lem7643126 {M : Type'} (i : nat) (h1 : term248 M i) : term248 M i.
Proof. exact (EQ_MP (@lem7643125 M i h1) (@lem0)). Qed.
Lemma lem7643127 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term248 M i) : (term285 A M N x y i) = (term288 A M N x y i).
Proof. exact (@lem7643111 A M N x y i (@lem7643126 M i h1)). Qed.
Lemma lem7643129 {A B : Type'} (f : A -> B) (y : A) : (term289 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7643130 {A : Type'} (f : nat -> A) (y : nat) : (term290 A f y) = (f y).
Proof. exact (@lem7643129 nat A f y). Qed.
Lemma lem7643131 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term291 A M N x y i) = (term288 A M N x y i).
Proof. exact (@lem7643130 A (term281 A M N x y) i). Qed.
Lemma lem7643132 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term288 A M N x y i) = (term279 A M N x y i).
Proof. exact (eq_refl (term288 A M N x y i)). Qed.
Lemma lem7643133 {A M N : Type'} (x : cart A M) (y : cart A N) : (term292 A M N x y) = (term281 A M N x y).
Proof. exact (fun_ext (fun i : nat => @lem7643132 A M N x y i)). Qed.
Lemma lem7643134 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7643135 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term291 A M N x y i) = (term288 A M N x y i).
Proof. exact (MK_COMB (@lem7643133 A M N x y) (@lem7643134 i)). Qed.
Lemma lem7643136 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7643137 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term293 A M N x y i) = (term294 A M N x y i).
Proof. exact (MK_COMB (@lem7643136 A) (@lem7643135 A M N x y i)). Qed.
Lemma lem7643138 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term288 A M N x y i) = (term279 A M N x y i).
Proof. exact (eq_refl (term288 A M N x y i)). Qed.
Lemma lem7643139 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term291 A M N x y i) = (term288 A M N x y i)) = ((term288 A M N x y i) = (term279 A M N x y i)).
Proof. exact (MK_COMB (@lem7643137 A M N x y i) (@lem7643138 A M N x y i)). Qed.
Lemma lem7643140 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term288 A M N x y i) = (term279 A M N x y i).
Proof. exact (EQ_MP (@lem7643139 A M N x y i) (@lem7643131 A M N x y i)). Qed.
Lemma lem7643142 {A B : Type'} (g : nat -> A) (i : nat) : term247 A B g i.
Proof. exact (fun h0 : term248 B i => @lem7641787 A B g i h0). Qed.
Lemma lem7643143 {A M N : Type'} (g : nat -> A) (i : nat) : term295 A M N g i.
Proof. exact (@lem7643142 A (finite_sum M N) g i). Qed.
Lemma lem7643144 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term296 A M N x y i.
Proof. exact (@lem7643143 A M N (term297 A M N x y) i). Qed.
Lemma lem7643148 {M : Type'} (i : nat) (h1 : term248 M i) : (term274 i) = True.
Proof. exact (EQ_MP (@lem7641851 i) (@lem7641850 M i h1)). Qed.
Lemma lem7643149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643150 {M : Type'} (i : nat) (h1 : term248 M i) : (term287 i) = (and True).
Proof. exact (MK_COMB (@lem7643149) (@lem7643148 M i h1)). Qed.
Lemma lem7643155 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term298 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
Lemma lem7643160 (i : nat) : (Peano.le i) = (Peano.le i).
Proof. exact (eq_refl (Peano.le i)). Qed.
Lemma lem7643161 {M N : Type'} (i : nat) : (term299 M N i) = (term300 M N i).
Proof. exact (MK_COMB (@lem7643160 i) (@lem7643155 M N)). Qed.
Lemma lem7643163 (a : nat) (b : nat) (c : nat) : term301 a b c.
Proof. exact (fun h0 : Peano.le a b => @lem7641777 c a b h0). Qed.
Lemma lem7643164 {M N : Type'} (i : nat) : term302 M N i.
Proof. exact (@lem7643163 i (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))). Qed.
Lemma lem7643166 {M : Type'} (i : nat) (h1 : term248 M i) : (term273 M i) = True.
Proof. exact (EQ_MP (@lem7641848 M i) (@lem7641847 M i h1)). Qed.
Lemma lem7643167 {M : Type'} (i : nat) (h1 : term248 M i) : True = (term273 M i).
Proof. exact (SYM (@lem7643166 M i h1)). Qed.
Lemma lem7643168 {M : Type'} (i : nat) (h1 : term248 M i) : term273 M i.
Proof. exact (EQ_MP (@lem7643167 M i h1) (@lem0)). Qed.
Lemma lem7643169 {M N : Type'} (i : nat) (h1 : term248 M i) : (term300 M N i) = True.
Proof. exact (@lem7643164 M N i (@lem7643168 M i h1)). Qed.
Lemma lem7643170 {M N : Type'} (i : nat) (h1 : term248 M i) : (term299 M N i) = True.
Proof. exact (TRANS (@lem7643161 M N i) (@lem7643169 M N i h1)). Qed.
Lemma lem7643171 {M N : Type'} (i : nat) (h1 : term248 M i) : (term303 M N i) = (True /\ True).
Proof. exact (MK_COMB (@lem7643150 M i h1) (@lem7643170 M N i h1)). Qed.
Lemma lem7643173 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7643174 : (True /\ True) = True.
Proof. exact (@lem7643173 True). Qed.
Lemma lem7643175 {M N : Type'} (i : nat) (h1 : term248 M i) : (term303 M N i) = True.
Proof. exact (TRANS (@lem7643171 M N i h1) (@lem7643174)). Qed.
Lemma lem7643176 {M N : Type'} (i : nat) (h1 : term248 M i) : True = (term303 M N i).
Proof. exact (SYM (@lem7643175 M N i h1)). Qed.
Lemma lem7643177 {M N : Type'} (i : nat) (h1 : term248 M i) : term303 M N i.
Proof. exact (EQ_MP (@lem7643176 M N i h1) (@lem0)). Qed.
Lemma lem7643178 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term248 M i) : (term279 A M N x y i) = (term304 A M N x y i).
Proof. exact (@lem7643144 A M N x y i (@lem7643177 M N i h1)). Qed.
Lemma lem7643180 {A B : Type'} (f : A -> B) (y : A) : (term289 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7643181 {A : Type'} (f : nat -> A) (y : nat) : (term290 A f y) = (f y).
Proof. exact (@lem7643180 nat A f y). Qed.
Lemma lem7643182 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term305 A M N x y i) = (term304 A M N x y i).
Proof. exact (@lem7643181 A (term297 A M N x y) i). Qed.
Lemma lem7643183 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term304 A M N x y i) = (term306 A M N x y i).
Proof. exact (eq_refl (term304 A M N x y i)). Qed.
Lemma lem7643184 {A M N : Type'} (x : cart A M) (y : cart A N) : (term307 A M N x y) = (term297 A M N x y).
Proof. exact (fun_ext (fun i : nat => @lem7643183 A M N x y i)). Qed.
Lemma lem7643185 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7643186 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term305 A M N x y i) = (term304 A M N x y i).
Proof. exact (MK_COMB (@lem7643184 A M N x y) (@lem7643185 i)). Qed.
Lemma lem7643187 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7643188 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term308 A M N x y i) = (term309 A M N x y i).
Proof. exact (MK_COMB (@lem7643187 A) (@lem7643186 A M N x y i)). Qed.
Lemma lem7643189 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term304 A M N x y i) = (term306 A M N x y i).
Proof. exact (eq_refl (term304 A M N x y i)). Qed.
Lemma lem7643190 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term305 A M N x y i) = (term304 A M N x y i)) = ((term304 A M N x y i) = (term306 A M N x y i)).
Proof. exact (MK_COMB (@lem7643188 A M N x y i) (@lem7643189 A M N x y i)). Qed.
Lemma lem7643191 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term304 A M N x y i) = (term306 A M N x y i).
Proof. exact (EQ_MP (@lem7643190 A M N x y i) (@lem7643182 A M N x y i)). Qed.
Lemma lem7643193 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term310 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7643194 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term311 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7643193 _2963 g t e g' t' e'). Qed.
Lemma lem7643195 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term312 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7643194 _2963 g t e g' t'). Qed.
Lemma lem7643196 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term313 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7643195 _2963 g t e g'). Qed.
Lemma lem7643197 {A : Type'} (g : Prop) (t : A) (e : A) : term313 A g t e.
Proof. exact (@lem7643196 A g t e). Qed.
Lemma lem7643198 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term314 A M N x y i.
Proof. exact (@lem7643197 A (term273 M i) (@dollar A M x i) (term315 A M N y i)). Qed.
Lemma lem7643199 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) : term316 A M N x y i g'.
Proof. exact (@lem7643198 A M N x y i g'). Qed.
Lemma lem7643200 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) : (term316 A M N x y i g') = (term317 A M N x y i g').
Proof. exact (eq_refl (term316 A M N x y i g')). Qed.
Lemma lem7643201 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) : term317 A M N x y i g'.
Proof. exact (EQ_MP (@lem7643200 A M N x y i g') (@lem7643199 A M N x y i g')). Qed.
Lemma lem7643202 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) : term318 A M N x y i g' t'.
Proof. exact (@lem7643201 A M N x y i g' t'). Qed.
Lemma lem7643203 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) : (term318 A M N x y i g' t') = (term319 A M N x y i g' t').
Proof. exact (eq_refl (term318 A M N x y i g' t')). Qed.
Lemma lem7643204 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) : term319 A M N x y i g' t'.
Proof. exact (EQ_MP (@lem7643203 A M N x y i g' t') (@lem7643202 A M N x y i g' t')). Qed.
Lemma lem7643205 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : term320 A M N x y i g' t' e'.
Proof. exact (@lem7643204 A M N x y i g' t' e'). Qed.
Lemma lem7643206 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : (term320 A M N x y i g' t' e') = (term321 A M N x y i g' t' e').
Proof. exact (eq_refl (term320 A M N x y i g' t' e')). Qed.
Lemma lem7643207 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : term321 A M N x y i g' t' e'.
Proof. exact (EQ_MP (@lem7643206 A M N x y i g' t' e') (@lem7643205 A M N x y i g' t' e')). Qed.
Lemma lem7643209 {M : Type'} (i : nat) (h1 : term248 M i) : (term273 M i) = True.
Proof. exact (EQ_MP (@lem7641848 M i) (@lem7641847 M i h1)). Qed.
Lemma lem7643210 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (t' : A) (e' : A) : term322 A M N x y i t' e'.
Proof. exact (@lem7643207 A M N x y i True t' e'). Qed.
Lemma lem7643211 {A M N : Type'} (x : cart A M) (y : cart A N) (t' : A) (e' : A) (i : nat) (h1 : term248 M i) : term323 A M N x y i t' e'.
Proof. exact (@lem7643210 A M N x y i t' e' (@lem7643209 M i h1)). Qed.
Lemma lem7643217 {A M : Type'} (x : cart A M) (i : nat) : (@dollar A M x i) = (@dollar A M x i).
Proof. exact (eq_refl (@dollar A M x i)). Qed.
Lemma lem7643218 {A M : Type'} (x : cart A M) (i : nat) : term324 A M x i.
Proof. exact (fun h0 : True => @lem7643217 A M x i). Qed.
Lemma lem7643219 {A M N : Type'} (y : cart A N) (x : cart A M) (e' : A) (i : nat) (h1 : term248 M i) : term325 A M N y x i e'.
Proof. exact (@lem7643211 A M N x y (@dollar A M x i) e' i h1). Qed.
Lemma lem7643220 {A M N : Type'} (y : cart A N) (x : cart A M) (e' : A) (i : nat) (h1 : term248 M i) : term326 A M N y x i e'.
Proof. exact (@lem7643219 A M N y x e' i h1 (@lem7643218 A M x i)). Qed.
Lemma lem7643226 {A M N : Type'} (y : cart A N) (i : nat) : (term315 A M N y i) = (term315 A M N y i).
Proof. exact (eq_refl (term315 A M N y i)). Qed.
Lemma lem7643227 {A M N : Type'} (y : cart A N) (i : nat) : term327 A M N y i.
Proof. exact (fun h0 : ~ True => @lem7643226 A M N y i). Qed.
Lemma lem7643228 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term248 M i) : term328 A M N x y i.
Proof. exact (@lem7643220 A M N y x (term315 A M N y i) i h1). Qed.
Lemma lem7643229 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term248 M i) : (term306 A M N x y i) = (term329 A M N x y i).
Proof. exact (@lem7643228 A M N x y i h1 (@lem7643227 A M N y i)). Qed.
Lemma lem7643231 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7643232 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem7643231 A t2 t1). Qed.
Lemma lem7643233 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) : (term329 A M N x y i) = (@dollar A M x i).
Proof. exact (@lem7643232 A (term315 A M N y i) (@dollar A M x i)). Qed.
Lemma lem7643234 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term306 A M N x y i) = (@dollar A M x i).
Proof. exact (TRANS (@lem7643229 A M N x y i h1) (@lem7643233 A M N y x i)). Qed.
Lemma lem7643235 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term304 A M N x y i) = (@dollar A M x i).
Proof. exact (TRANS (@lem7643191 A M N x y i) (@lem7643234 A M N y x i h1)). Qed.
Lemma lem7643236 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term279 A M N x y i) = (@dollar A M x i).
Proof. exact (TRANS (@lem7643178 A M N x y i h1) (@lem7643235 A M N y x i h1)). Qed.
Lemma lem7643237 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term288 A M N x y i) = (@dollar A M x i).
Proof. exact (TRANS (@lem7643140 A M N x y i) (@lem7643236 A M N y x i h1)). Qed.
Lemma lem7643238 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term285 A M N x y i) = (@dollar A M x i).
Proof. exact (TRANS (@lem7643127 A M N x y i h1) (@lem7643237 A M N y x i h1)). Qed.
Lemma lem7643239 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term266 A M N x y i) = (@dollar A M x i).
Proof. exact (TRANS (@lem7643107 A M N x y i) (@lem7643238 A M N y x i h1)). Qed.
Lemma lem7643240 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7643241 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : (term330 A M N x y i) = (term331 A M x i).
Proof. exact (MK_COMB (@lem7643240 A) (@lem7643239 A M N y x i h1)). Qed.
Lemma lem7643242 {A M : Type'} (x : cart A M) (i : nat) : (@dollar A M x i) = (@dollar A M x i).
Proof. exact (eq_refl (@dollar A M x i)). Qed.
Lemma lem7643243 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : ((term266 A M N x y i) = (@dollar A M x i)) = ((@dollar A M x i) = (@dollar A M x i)).
Proof. exact (MK_COMB (@lem7643241 A M N y x i h1) (@lem7643242 A M x i)). Qed.
Lemma lem7643245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7643246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7643245 A x). Qed.
Lemma lem7643247 {A M : Type'} (x : cart A M) (i : nat) : ((@dollar A M x i) = (@dollar A M x i)) = True.
Proof. exact (@lem7643246 A (@dollar A M x i)). Qed.
Lemma lem7643248 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) (h1 : term248 M i) : ((term266 A M N x y i) = (@dollar A M x i)) = True.
Proof. exact (TRANS (@lem7643243 A M N y x i h1) (@lem7643247 A M x i)). Qed.
Lemma lem7643249 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) : term332 A M N y x i.
Proof. exact (fun h0 : term248 M i => @lem7643248 A M N y x i h0). Qed.
Lemma lem7643250 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) : term333 A M N y x i.
Proof. exact (@lem7641845 A M N y x i True). Qed.
Lemma lem7643251 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) : (term334 A M N y x i) = (term335 M i).
Proof. exact (@lem7643250 A M N y x i (@lem7643249 A M N y x i)). Qed.
Lemma lem7643253 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7643254 {M : Type'} (i : nat) : (term335 M i) = True.
Proof. exact (@lem7643253 (term248 M i)). Qed.
Lemma lem7643255 {A M N : Type'} (y : cart A N) (x : cart A M) (i : nat) : (term334 A M N y x i) = True.
Proof. exact (TRANS (@lem7643251 A M N y x i) (@lem7643254 M i)). Qed.
Lemma lem7643256 {A M N : Type'} (y : cart A N) (x : cart A M) : (term336 A M N y x) = term337.
Proof. exact (fun_ext (fun i : nat => @lem7643255 A M N y x i)). Qed.
Lemma lem7643257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7643258 {A M N : Type'} (y : cart A N) (x : cart A M) : (term261 A M N y x) = term338.
Proof. exact (MK_COMB (@lem7643257) (@lem7643256 A M N y x)). Qed.
Lemma lem7643260 {A : Type'} (t : Prop) : (term339 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7643261 (t : Prop) : (term340 t) = t.
Proof. exact (@lem7643260 nat t). Qed.
Lemma lem7643262 : term338 = True.
Proof. exact (@lem7643261 True). Qed.
Lemma lem7643263 {A M N : Type'} (y : cart A N) (x : cart A M) : (term261 A M N y x) = True.
Proof. exact (TRANS (@lem7643258 A M N y x) (@lem7643262)). Qed.
Lemma lem7643264 {A M N : Type'} (y : cart A N) (x : cart A M) : ((term260 A M N x y) = x) = True.
Proof. exact (TRANS (@lem7641821 A M N y x) (@lem7643263 A M N y x)). Qed.
Lemma lem7643265 {A M N : Type'} (x : cart A M) : (term341 A M N x) = (term342 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem7643264 A M N y x)). Qed.
Lemma lem7643266 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7643267 {A M N : Type'} (x : cart A M) : (term343 A M N x) = (term344 A N).
Proof. exact (MK_COMB (@lem7643266 A N) (@lem7643265 A M N x)). Qed.
Lemma lem7643269 {A : Type'} (t : Prop) : (term339 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7643270 {A N : Type'} (t : Prop) : (term345 A N t) = t.
Proof. exact (@lem7643269 (cart A N) t). Qed.
Lemma lem7643271 {A N : Type'} : (term344 A N) = True.
Proof. exact (@lem7643270 A N True). Qed.
Lemma lem7643272 {A M N : Type'} (x : cart A M) : (term343 A M N x) = True.
Proof. exact (TRANS (@lem7643267 A M N x) (@lem7643271 A N)). Qed.
Lemma lem7643273 {A M N : Type'} : (term346 A M N) = (term342 A M).
Proof. exact (fun_ext (fun x : cart A M => @lem7643272 A M N x)). Qed.
Lemma lem7643274 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem7643275 {A M N : Type'} : (term347 A M N) = (term344 A M).
Proof. exact (MK_COMB (@lem7643274 A M) (@lem7643273 A M N)). Qed.
Lemma lem7643277 {A : Type'} (t : Prop) : (term339 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7643278 {A M : Type'} (t : Prop) : (term345 A M t) = t.
Proof. exact (@lem7643277 (cart A M) t). Qed.
Lemma lem7643279 {A M : Type'} : (term344 A M) = True.
Proof. exact (@lem7643278 A M True). Qed.
Lemma lem7643280 {A M N : Type'} : (term347 A M N) = True.
Proof. exact (TRANS (@lem7643275 A M N) (@lem7643279 A M)). Qed.
Lemma lem7643281 {A M N : Type'} : True = (term347 A M N).
Proof. exact (SYM (@lem7643280 A M N)). Qed.
Lemma lem7643282 {A M N : Type'} : term347 A M N.
Proof. exact (EQ_MP (@lem7643281 A M N) (@lem0)). Qed.
