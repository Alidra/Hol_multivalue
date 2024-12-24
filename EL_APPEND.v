Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_APPEND_term_abbrevs.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import SUB_0_spec.
Require Import SUB_SUC_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1095962_spec.
Require Import thm1097080_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm12653_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89994_spec.
Lemma lem1205493 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1205494 (m : nat) : term1 m.
Proof. exact (@lem1205493 m). Qed.
Lemma lem1205495 (m : nat) : (term1 m) = ((term2 m) = False).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1205497 (n : nat) : term3 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem1205498 (n : nat) : (term3 n) = (term4 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1205499 (n : nat) : term4 n.
Proof. exact (EQ_MP (@lem1205498 n) (@lem1205497 n)). Qed.
Lemma lem1205500 (n : nat) : (term4 n) = ((term4 n) = True).
Proof. exact (@lem7 (term4 n)). Qed.
Lemma lem1205504 (m : nat) : term5 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem1205505 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1205506 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem1205505 m) (@lem1205504 m)). Qed.
Lemma lem1205509 {A : Type'} : term7 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1205510 {A : Type'} (h : A) : term8 A h.
Proof. exact (@lem1205509 A h). Qed.
Lemma lem1205511 {A : Type'} (h : A) : (term8 A h) = (term9 A h).
Proof. exact (eq_refl (term8 A h)). Qed.
Lemma lem1205512 {A : Type'} (h : A) : term9 A h.
Proof. exact (EQ_MP (@lem1205511 A h) (@lem1205510 A h)). Qed.
Lemma lem1205513 {A : Type'} (h : A) (t : list A) : term10 A h t.
Proof. exact (@lem1205512 A h t). Qed.
Lemma lem1205514 {A : Type'} (h : A) (t : list A) : (term10 A h t) = ((term11 A h t) = (term12 A t)).
Proof. exact (eq_refl (term10 A h t)). Qed.
Lemma lem1205517 {A : Type'} : term13 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1205518 {A : Type'} (h : A) : term14 A h.
Proof. exact (@lem1205517 A h). Qed.
Lemma lem1205519 {A : Type'} (h : A) : (term14 A h) = (term15 A h).
Proof. exact (eq_refl (term14 A h)). Qed.
Lemma lem1205520 {A : Type'} (h : A) : term15 A h.
Proof. exact (EQ_MP (@lem1205519 A h) (@lem1205518 A h)). Qed.
Lemma lem1205521 {A : Type'} (h : A) (t : list A) : term16 A h t.
Proof. exact (@lem1205520 A h t). Qed.
Lemma lem1205522 {A : Type'} (h : A) (t : list A) : (term16 A h t) = (term17 A h t).
Proof. exact (eq_refl (term16 A h t)). Qed.
Lemma lem1205523 {A : Type'} (h : A) (t : list A) : term17 A h t.
Proof. exact (EQ_MP (@lem1205522 A h t) (@lem1205521 A h t)). Qed.
Lemma lem1205524 {A : Type'} (h : A) (t : list A) (l : list A) : term18 A h t l.
Proof. exact (@lem1205523 A h t l). Qed.
Lemma lem1205525 {A : Type'} (h : A) (t : list A) (l : list A) : (term18 A h t l) = ((term19 A h t l) = (term20 A h t l)).
Proof. exact (eq_refl (term18 A h t l)). Qed.
Lemma lem1205527 {A : Type'} : term21 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1205528 {A : Type'} (l : list A) : term22 A l.
Proof. exact (@lem1205527 A l). Qed.
Lemma lem1205529 {A : Type'} (l : list A) : (term22 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term22 A l)). Qed.
Lemma lem1205534 (P : nat -> Prop) : term23 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1205535 {_28192 : Type'} : term24 _28192.
Proof. exact (@lem1205534 (term25 _28192)). Qed.
Lemma lem1205536 {_28192 : Type'} : (term26 _28192) = (term27 _28192).
Proof. exact (eq_refl (term26 _28192)). Qed.
Lemma lem1205537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1205538 {_28192 : Type'} : (term28 _28192) = (term29 _28192).
Proof. exact (MK_COMB (@lem1205537) (@lem1205536 _28192)). Qed.
Lemma lem1205539 {_28192 : Type'} (k : nat) : (term30 _28192 k) = (term31 _28192 k).
Proof. exact (eq_refl (term30 _28192 k)). Qed.
Lemma lem1205540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205541 {_28192 : Type'} (k : nat) : (term32 _28192 k) = (term33 _28192 k).
Proof. exact (MK_COMB (@lem1205540) (@lem1205539 _28192 k)). Qed.
Lemma lem1205542 {_28192 : Type'} (k : nat) : (term34 _28192 k) = (term35 _28192 k).
Proof. exact (eq_refl (term34 _28192 k)). Qed.
Lemma lem1205543 {_28192 : Type'} (k : nat) : (term36 _28192 k) = (term37 _28192 k).
Proof. exact (MK_COMB (@lem1205541 _28192 k) (@lem1205542 _28192 k)). Qed.
Lemma lem1205544 {_28192 : Type'} : (term38 _28192) = (term39 _28192).
Proof. exact (fun_ext (fun k : nat => @lem1205543 _28192 k)). Qed.
Lemma lem1205545 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1205546 {_28192 : Type'} : (term40 _28192) = (term41 _28192).
Proof. exact (MK_COMB (@lem1205545) (@lem1205544 _28192)). Qed.
Lemma lem1205547 {_28192 : Type'} : (term42 _28192) = (term43 _28192).
Proof. exact (MK_COMB (@lem1205538 _28192) (@lem1205546 _28192)). Qed.
Lemma lem1205548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205549 {_28192 : Type'} : (term44 _28192) = (term45 _28192).
Proof. exact (MK_COMB (@lem1205548) (@lem1205547 _28192)). Qed.
Lemma lem1205550 {_28192 : Type'} (k : nat) : (term30 _28192 k) = (term31 _28192 k).
Proof. exact (eq_refl (term30 _28192 k)). Qed.
Lemma lem1205551 {_28192 : Type'} : (term46 _28192) = (term25 _28192).
Proof. exact (fun_ext (fun k : nat => @lem1205550 _28192 k)). Qed.
Lemma lem1205552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1205553 {_28192 : Type'} : (term47 _28192) = (term48 _28192).
Proof. exact (MK_COMB (@lem1205552) (@lem1205551 _28192)). Qed.
Lemma lem1205554 {_28192 : Type'} : (term24 _28192) = (term49 _28192).
Proof. exact (MK_COMB (@lem1205549 _28192) (@lem1205553 _28192)). Qed.
Lemma lem1205555 {_28192 : Type'} : term49 _28192.
Proof. exact (EQ_MP (@lem1205554 _28192) (@lem1205535 _28192)). Qed.
Lemma lem1205556 {_28192 : Type'} (k : nat) (h1 : term31 _28192 k) : term31 _28192 k.
Proof. exact (h1). Qed.
Lemma lem1205568 {_25569 : Type'} (l : list _25569) : (term50 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1205569 {_28192 : Type'} (l : list _28192) : (term50 _28192 l) = (@hd _28192 l).
Proof. exact (@lem1205568 _28192 l). Qed.
Lemma lem1205570 {_28192 : Type'} (l : list _28192) (m : list _28192) : (term51 _28192 l m) = (term52 _28192 l m).
Proof. exact (@lem1205569 _28192 (@List.app _28192 l m)). Qed.
Lemma lem1205571 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205572 {_28192 : Type'} (l : list _28192) (m : list _28192) : (term53 _28192 l m) = (term54 _28192 l m).
Proof. exact (MK_COMB (@lem1205571 _28192) (@lem1205570 _28192 l m)). Qed.
Lemma lem1205574 {_25569 : Type'} (l : list _25569) : (term50 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1205575 {_28192 : Type'} (l : list _28192) : (term50 _28192 l) = (@hd _28192 l).
Proof. exact (@lem1205574 _28192 l). Qed.
Lemma lem1205576 {_28192 : Type'} (l : list _28192) : (term55 _28192 l) = (term55 _28192 l).
Proof. exact (eq_refl (term55 _28192 l)). Qed.
Lemma lem1205577 {_28192 : Type'} (l : list _28192) : (term56 _28192 l) = (term57 _28192 l).
Proof. exact (MK_COMB (@lem1205576 _28192 l) (@lem1205575 _28192 l)). Qed.
Lemma lem1205578 {_28192 : Type'} (l : list _28192) (m : list _28192) : (term58 _28192 l m) = (term58 _28192 l m).
Proof. exact (eq_refl (term58 _28192 l m)). Qed.
Lemma lem1205579 {_28192 : Type'} (l : list _28192) (m : list _28192) : (term59 _28192 l m) = (term60 _28192 l m).
Proof. exact (MK_COMB (@lem1205577 _28192 l) (@lem1205578 _28192 l m)). Qed.
Lemma lem1205580 {_28192 : Type'} (l : list _28192) (m : list _28192) : ((term51 _28192 l m) = (term59 _28192 l m)) = ((term52 _28192 l m) = (term60 _28192 l m)).
Proof. exact (MK_COMB (@lem1205572 _28192 l m) (@lem1205579 _28192 l m)). Qed.
Lemma lem1205583 {_28192 : Type'} (l : list _28192) : (term61 _28192 l) = (term62 _28192 l).
Proof. exact (fun_ext (fun m : list _28192 => @lem1205580 _28192 l m)). Qed.
Lemma lem1205584 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205585 {_28192 : Type'} (l : list _28192) : (term63 _28192 l) = (term64 _28192 l).
Proof. exact (MK_COMB (@lem1205584 _28192) (@lem1205583 _28192 l)). Qed.
Lemma lem1205590 {_28192 : Type'} : (term65 _28192) = (term66 _28192).
Proof. exact (fun_ext (fun l : list _28192 => @lem1205585 _28192 l)). Qed.
Lemma lem1205591 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205592 {_28192 : Type'} : (term27 _28192) = (term67 _28192).
Proof. exact (MK_COMB (@lem1205591 _28192) (@lem1205590 _28192)). Qed.
Lemma lem1205597 {_28192 : Type'} : (term67 _28192) = (term27 _28192).
Proof. exact (SYM (@lem1205592 _28192)). Qed.
Lemma lem1205609 {_25569 : Type'} (n : nat) (l : list _25569) : (term68 _25569 n l) = (term69 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1205610 {_28192 : Type'} (n : nat) (l : list _28192) : (term68 _28192 n l) = (term69 _28192 n l).
Proof. exact (@lem1205609 _28192 n l). Qed.
Lemma lem1205611 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term70 _28192 k l m) = (term71 _28192 k l m).
Proof. exact (@lem1205610 _28192 k (@List.app _28192 l m)). Qed.
Lemma lem1205612 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205613 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term72 _28192 k l m) = (term73 _28192 k l m).
Proof. exact (MK_COMB (@lem1205612 _28192) (@lem1205611 _28192 k l m)). Qed.
Lemma lem1205615 {_25569 : Type'} (n : nat) (l : list _25569) : (term68 _25569 n l) = (term69 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1205616 {_28192 : Type'} (n : nat) (l : list _28192) : (term68 _28192 n l) = (term69 _28192 n l).
Proof. exact (@lem1205615 _28192 n l). Qed.
Lemma lem1205617 {_28192 : Type'} (k : nat) (l : list _28192) : (term68 _28192 k l) = (term69 _28192 k l).
Proof. exact (@lem1205616 _28192 k l). Qed.
Lemma lem1205618 {_28192 : Type'} (k : nat) (l : list _28192) : (term74 _28192 k l) = (term74 _28192 k l).
Proof. exact (eq_refl (term74 _28192 k l)). Qed.
Lemma lem1205619 {_28192 : Type'} (k : nat) (l : list _28192) : (term75 _28192 k l) = (term76 _28192 k l).
Proof. exact (MK_COMB (@lem1205618 _28192 k l) (@lem1205617 _28192 k l)). Qed.
Lemma lem1205620 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term77 _28192 k l m) = (term77 _28192 k l m).
Proof. exact (eq_refl (term77 _28192 k l m)). Qed.
Lemma lem1205621 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term78 _28192 k l m) = (term79 _28192 k l m).
Proof. exact (MK_COMB (@lem1205619 _28192 k l) (@lem1205620 _28192 k l m)). Qed.
Lemma lem1205622 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : ((term70 _28192 k l m) = (term78 _28192 k l m)) = ((term71 _28192 k l m) = (term79 _28192 k l m)).
Proof. exact (MK_COMB (@lem1205613 _28192 k l m) (@lem1205621 _28192 k l m)). Qed.
Lemma lem1205625 {_28192 : Type'} (k : nat) (l : list _28192) : (term80 _28192 k l) = (term81 _28192 k l).
Proof. exact (fun_ext (fun m : list _28192 => @lem1205622 _28192 k l m)). Qed.
Lemma lem1205626 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205627 {_28192 : Type'} (k : nat) (l : list _28192) : (term82 _28192 k l) = (term83 _28192 k l).
Proof. exact (MK_COMB (@lem1205626 _28192) (@lem1205625 _28192 k l)). Qed.
Lemma lem1205632 {_28192 : Type'} (k : nat) : (term84 _28192 k) = (term85 _28192 k).
Proof. exact (fun_ext (fun l : list _28192 => @lem1205627 _28192 k l)). Qed.
Lemma lem1205633 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205634 {_28192 : Type'} (k : nat) : (term35 _28192 k) = (term86 _28192 k).
Proof. exact (MK_COMB (@lem1205633 _28192) (@lem1205632 _28192 k)). Qed.
Lemma lem1205639 {_28192 : Type'} (k : nat) : (term86 _28192 k) = (term35 _28192 k).
Proof. exact (SYM (@lem1205634 _28192 k)). Qed.
Lemma lem1205641 {A : Type'} (P : type1143 A) : term87 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1205642 {_28192 : Type'} (P : type1143 _28192) : term87 _28192 P.
Proof. exact (@lem1205641 _28192 P). Qed.
Lemma lem1205643 {_28192 : Type'} : term88 _28192.
Proof. exact (@lem1205642 _28192 (term66 _28192)). Qed.
Lemma lem1205644 {_28192 : Type'} : (term89 _28192) = (term90 _28192).
Proof. exact (eq_refl (term89 _28192)). Qed.
Lemma lem1205645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1205646 {_28192 : Type'} : (term91 _28192) = (term92 _28192).
Proof. exact (MK_COMB (@lem1205645) (@lem1205644 _28192)). Qed.
Lemma lem1205647 {_28192 : Type'} (t : list _28192) : (term93 _28192 t) = (term64 _28192 t).
Proof. exact (eq_refl (term93 _28192 t)). Qed.
Lemma lem1205648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205649 {_28192 : Type'} (t : list _28192) : (term94 _28192 t) = (term95 _28192 t).
Proof. exact (MK_COMB (@lem1205648) (@lem1205647 _28192 t)). Qed.
Lemma lem1205650 {_28192 : Type'} (h : _28192) (t : list _28192) : (term96 _28192 h t) = (term97 _28192 h t).
Proof. exact (eq_refl (term96 _28192 h t)). Qed.
Lemma lem1205651 {_28192 : Type'} (h : _28192) (t : list _28192) : (term98 _28192 h t) = (term99 _28192 h t).
Proof. exact (MK_COMB (@lem1205649 _28192 t) (@lem1205650 _28192 h t)). Qed.
Lemma lem1205652 {_28192 : Type'} (h : _28192) : (term100 _28192 h) = (term101 _28192 h).
Proof. exact (fun_ext (fun t : list _28192 => @lem1205651 _28192 h t)). Qed.
Lemma lem1205653 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205654 {_28192 : Type'} (h : _28192) : (term102 _28192 h) = (term103 _28192 h).
Proof. exact (MK_COMB (@lem1205653 _28192) (@lem1205652 _28192 h)). Qed.
Lemma lem1205655 {_28192 : Type'} : (term104 _28192) = (term105 _28192).
Proof. exact (fun_ext (fun h : _28192 => @lem1205654 _28192 h)). Qed.
Lemma lem1205656 {_28192 : Type'} : (@all _28192) = (@all _28192).
Proof. exact (eq_refl (@all _28192)). Qed.
Lemma lem1205657 {_28192 : Type'} : (term106 _28192) = (term107 _28192).
Proof. exact (MK_COMB (@lem1205656 _28192) (@lem1205655 _28192)). Qed.
Lemma lem1205658 {_28192 : Type'} : (term108 _28192) = (term109 _28192).
Proof. exact (MK_COMB (@lem1205646 _28192) (@lem1205657 _28192)). Qed.
Lemma lem1205659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205660 {_28192 : Type'} : (term110 _28192) = (term111 _28192).
Proof. exact (MK_COMB (@lem1205659) (@lem1205658 _28192)). Qed.
Lemma lem1205661 {_28192 : Type'} (l : list _28192) : (term93 _28192 l) = (term64 _28192 l).
Proof. exact (eq_refl (term93 _28192 l)). Qed.
Lemma lem1205662 {_28192 : Type'} : (term112 _28192) = (term66 _28192).
Proof. exact (fun_ext (fun l : list _28192 => @lem1205661 _28192 l)). Qed.
Lemma lem1205663 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205664 {_28192 : Type'} : (term113 _28192) = (term67 _28192).
Proof. exact (MK_COMB (@lem1205663 _28192) (@lem1205662 _28192)). Qed.
Lemma lem1205665 {_28192 : Type'} : (term88 _28192) = (term114 _28192).
Proof. exact (MK_COMB (@lem1205660 _28192) (@lem1205664 _28192)). Qed.
Lemma lem1205666 {_28192 : Type'} : term114 _28192.
Proof. exact (EQ_MP (@lem1205665 _28192) (@lem1205643 _28192)). Qed.
Lemma lem1205669 {A : Type'} (P : type1143 A) : term87 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1205670 {_28192 : Type'} (P : type1143 _28192) : term87 _28192 P.
Proof. exact (@lem1205669 _28192 P). Qed.
Lemma lem1205671 {_28192 : Type'} (k : nat) : term115 _28192 k.
Proof. exact (@lem1205670 _28192 (term85 _28192 k)). Qed.
Lemma lem1205672 {_28192 : Type'} (k : nat) : (term116 _28192 k) = (term117 _28192 k).
Proof. exact (eq_refl (term116 _28192 k)). Qed.
Lemma lem1205673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1205674 {_28192 : Type'} (k : nat) : (term118 _28192 k) = (term119 _28192 k).
Proof. exact (MK_COMB (@lem1205673) (@lem1205672 _28192 k)). Qed.
Lemma lem1205675 {_28192 : Type'} (k : nat) (t : list _28192) : (term120 _28192 k t) = (term83 _28192 k t).
Proof. exact (eq_refl (term120 _28192 k t)). Qed.
Lemma lem1205676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205677 {_28192 : Type'} (k : nat) (t : list _28192) : (term121 _28192 k t) = (term122 _28192 k t).
Proof. exact (MK_COMB (@lem1205676) (@lem1205675 _28192 k t)). Qed.
Lemma lem1205678 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) : (term123 _28192 k h t) = (term124 _28192 k h t).
Proof. exact (eq_refl (term123 _28192 k h t)). Qed.
Lemma lem1205679 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) : (term125 _28192 k h t) = (term126 _28192 k h t).
Proof. exact (MK_COMB (@lem1205677 _28192 k t) (@lem1205678 _28192 k h t)). Qed.
Lemma lem1205680 {_28192 : Type'} (k : nat) (h : _28192) : (term127 _28192 k h) = (term128 _28192 k h).
Proof. exact (fun_ext (fun t : list _28192 => @lem1205679 _28192 k h t)). Qed.
Lemma lem1205681 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205682 {_28192 : Type'} (k : nat) (h : _28192) : (term129 _28192 k h) = (term130 _28192 k h).
Proof. exact (MK_COMB (@lem1205681 _28192) (@lem1205680 _28192 k h)). Qed.
Lemma lem1205683 {_28192 : Type'} (k : nat) : (term131 _28192 k) = (term132 _28192 k).
Proof. exact (fun_ext (fun h : _28192 => @lem1205682 _28192 k h)). Qed.
Lemma lem1205684 {_28192 : Type'} : (@all _28192) = (@all _28192).
Proof. exact (eq_refl (@all _28192)). Qed.
Lemma lem1205685 {_28192 : Type'} (k : nat) : (term133 _28192 k) = (term134 _28192 k).
Proof. exact (MK_COMB (@lem1205684 _28192) (@lem1205683 _28192 k)). Qed.
Lemma lem1205686 {_28192 : Type'} (k : nat) : (term135 _28192 k) = (term136 _28192 k).
Proof. exact (MK_COMB (@lem1205674 _28192 k) (@lem1205685 _28192 k)). Qed.
Lemma lem1205687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205688 {_28192 : Type'} (k : nat) : (term137 _28192 k) = (term138 _28192 k).
Proof. exact (MK_COMB (@lem1205687) (@lem1205686 _28192 k)). Qed.
Lemma lem1205689 {_28192 : Type'} (k : nat) (l : list _28192) : (term120 _28192 k l) = (term83 _28192 k l).
Proof. exact (eq_refl (term120 _28192 k l)). Qed.
Lemma lem1205690 {_28192 : Type'} (k : nat) : (term139 _28192 k) = (term85 _28192 k).
Proof. exact (fun_ext (fun l : list _28192 => @lem1205689 _28192 k l)). Qed.
Lemma lem1205691 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205692 {_28192 : Type'} (k : nat) : (term140 _28192 k) = (term86 _28192 k).
Proof. exact (MK_COMB (@lem1205691 _28192) (@lem1205690 _28192 k)). Qed.
Lemma lem1205693 {_28192 : Type'} (k : nat) : (term115 _28192 k) = (term141 _28192 k).
Proof. exact (MK_COMB (@lem1205688 _28192 k) (@lem1205692 _28192 k)). Qed.
Lemma lem1205694 {_28192 : Type'} (k : nat) : term141 _28192 k.
Proof. exact (EQ_MP (@lem1205693 _28192 k) (@lem1205671 _28192 k)). Qed.
Lemma lem1205703 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1205529 A l) (@lem1205528 A l)). Qed.
Lemma lem1205704 {_28192 : Type'} (l : list _28192) : (@List.app _28192 (@nil _28192) l) = l.
Proof. exact (@lem1205703 _28192 l). Qed.
Lemma lem1205705 {_28192 : Type'} (m : list _28192) : (@List.app _28192 (@nil _28192) m) = m.
Proof. exact (@lem1205704 _28192 m). Qed.
Lemma lem1205706 {_28192 : Type'} : (@hd _28192) = (@hd _28192).
Proof. exact (eq_refl (@hd _28192)). Qed.
Lemma lem1205707 {_28192 : Type'} (m : list _28192) : (term142 _28192 m) = (@hd _28192 m).
Proof. exact (MK_COMB (@lem1205706 _28192) (@lem1205705 _28192 m)). Qed.
Lemma lem1205708 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205709 {_28192 : Type'} (m : list _28192) : (term143 _28192 m) = (term144 _28192 m).
Proof. exact (MK_COMB (@lem1205708 _28192) (@lem1205707 _28192 m)). Qed.
Lemma lem1205711 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1205712 {_28192 : Type'} : (@List.length _28192 (@nil _28192)) = (NUMERAL 0).
Proof. exact (@lem1205711 _28192). Qed.
Lemma lem1205713 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem1205714 {_28192 : Type'} : (term146 _28192) = term147.
Proof. exact (MK_COMB (@lem1205713) (@lem1205712 _28192)). Qed.
Lemma lem1205716 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem1205495 m) (@lem1205494 m)). Qed.
Lemma lem1205717 : term147 = False.
Proof. exact (@lem1205716 (NUMERAL 0)). Qed.
Lemma lem1205718 {_28192 : Type'} : (term146 _28192) = False.
Proof. exact (TRANS (@lem1205714 _28192) (@lem1205717)). Qed.
Lemma lem1205719 {_28192 : Type'} : (@COND _28192) = (@COND _28192).
Proof. exact (eq_refl (@COND _28192)). Qed.
Lemma lem1205720 {_28192 : Type'} : (term148 _28192) = (@COND _28192 False).
Proof. exact (MK_COMB (@lem1205719 _28192) (@lem1205718 _28192)). Qed.
Lemma lem1205721 {_28192 : Type'} : (@hd _28192 (@nil _28192)) = (@hd _28192 (@nil _28192)).
Proof. exact (eq_refl (@hd _28192 (@nil _28192))). Qed.
Lemma lem1205722 {_28192 : Type'} : (term149 _28192) = (term150 _28192).
Proof. exact (MK_COMB (@lem1205720 _28192) (@lem1205721 _28192)). Qed.
Lemma lem1205724 (m : nat) : (term151 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem1205506 m)). Qed.
Lemma lem1205725 {_28192 : Type'} : (term152 _28192) = (NUMERAL 0).
Proof. exact (@lem1205724 (@List.length _28192 (@nil _28192))). Qed.
Lemma lem1205726 {_28192 : Type'} : (@EL _28192) = (@EL _28192).
Proof. exact (eq_refl (@EL _28192)). Qed.
Lemma lem1205727 {_28192 : Type'} : (term153 _28192) = (term154 _28192).
Proof. exact (MK_COMB (@lem1205726 _28192) (@lem1205725 _28192)). Qed.
Lemma lem1205728 {_28192 : Type'} (m : list _28192) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1205729 {_28192 : Type'} (m : list _28192) : (term155 _28192 m) = (term50 _28192 m).
Proof. exact (MK_COMB (@lem1205727 _28192) (@lem1205728 _28192 m)). Qed.
Lemma lem1205731 {_25569 : Type'} (l : list _25569) : (term50 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1205732 {_28192 : Type'} (l : list _28192) : (term50 _28192 l) = (@hd _28192 l).
Proof. exact (@lem1205731 _28192 l). Qed.
Lemma lem1205733 {_28192 : Type'} (m : list _28192) : (term50 _28192 m) = (@hd _28192 m).
Proof. exact (@lem1205732 _28192 m). Qed.
Lemma lem1205734 {_28192 : Type'} (m : list _28192) : (term155 _28192 m) = (@hd _28192 m).
Proof. exact (TRANS (@lem1205729 _28192 m) (@lem1205733 _28192 m)). Qed.
Lemma lem1205735 {_28192 : Type'} (m : list _28192) : (term156 _28192 m) = (term157 _28192 m).
Proof. exact (MK_COMB (@lem1205722 _28192) (@lem1205734 _28192 m)). Qed.
Lemma lem1205737 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1205738 {_28192 : Type'} (t1 : _28192) (t2 : _28192) : (@COND _28192 False t1 t2) = t2.
Proof. exact (@lem1205737 _28192 t1 t2). Qed.
Lemma lem1205739 {_28192 : Type'} (m : list _28192) : (term157 _28192 m) = (@hd _28192 m).
Proof. exact (@lem1205738 _28192 (@hd _28192 (@nil _28192)) (@hd _28192 m)). Qed.
Lemma lem1205740 {_28192 : Type'} (m : list _28192) : (term156 _28192 m) = (@hd _28192 m).
Proof. exact (TRANS (@lem1205735 _28192 m) (@lem1205739 _28192 m)). Qed.
Lemma lem1205741 {_28192 : Type'} (m : list _28192) : ((term142 _28192 m) = (term156 _28192 m)) = ((@hd _28192 m) = (@hd _28192 m)).
Proof. exact (MK_COMB (@lem1205709 _28192 m) (@lem1205740 _28192 m)). Qed.
Lemma lem1205743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1205744 {_28192 : Type'} (x : _28192) : (x = x) = True.
Proof. exact (@lem1205743 _28192 x). Qed.
Lemma lem1205745 {_28192 : Type'} (m : list _28192) : ((@hd _28192 m) = (@hd _28192 m)) = True.
Proof. exact (@lem1205744 _28192 (@hd _28192 m)). Qed.
Lemma lem1205746 {_28192 : Type'} (m : list _28192) : ((term142 _28192 m) = (term156 _28192 m)) = True.
Proof. exact (TRANS (@lem1205741 _28192 m) (@lem1205745 _28192 m)). Qed.
Lemma lem1205747 {_28192 : Type'} : (term158 _28192) = (term159 _28192).
Proof. exact (fun_ext (fun m : list _28192 => @lem1205746 _28192 m)). Qed.
Lemma lem1205748 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205749 {_28192 : Type'} : (term90 _28192) = (term160 _28192).
Proof. exact (MK_COMB (@lem1205748 _28192) (@lem1205747 _28192)). Qed.
Lemma lem1205751 {A : Type'} (t : Prop) : (term161 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1205752 {_28192 : Type'} (t : Prop) : (term162 _28192 t) = t.
Proof. exact (@lem1205751 (list _28192) t). Qed.
Lemma lem1205753 {_28192 : Type'} : (term160 _28192) = True.
Proof. exact (@lem1205752 _28192 True). Qed.
Lemma lem1205754 {_28192 : Type'} : (term90 _28192) = True.
Proof. exact (TRANS (@lem1205749 _28192) (@lem1205753 _28192)). Qed.
Lemma lem1205755 {_28192 : Type'} : True = (term90 _28192).
Proof. exact (SYM (@lem1205754 _28192)). Qed.
Lemma lem1205756 {_28192 : Type'} : term90 _28192.
Proof. exact (EQ_MP (@lem1205755 _28192) (@lem0)). Qed.
Lemma lem1205764 {A : Type'} (h : A) (t : list A) (l : list A) : (term19 A h t l) = (term20 A h t l).
Proof. exact (EQ_MP (@lem1205525 A h t l) (@lem1205524 A h t l)). Qed.
Lemma lem1205765 {_28192 : Type'} (h : _28192) (t : list _28192) (l : list _28192) : (term19 _28192 h t l) = (term20 _28192 h t l).
Proof. exact (@lem1205764 _28192 h t l). Qed.
Lemma lem1205766 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term19 _28192 h t m) = (term20 _28192 h t m).
Proof. exact (@lem1205765 _28192 h t m). Qed.
Lemma lem1205767 {_28192 : Type'} : (@hd _28192) = (@hd _28192).
Proof. exact (eq_refl (@hd _28192)). Qed.
Lemma lem1205768 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term163 _28192 h t m) = (term164 _28192 h t m).
Proof. exact (MK_COMB (@lem1205767 _28192) (@lem1205766 _28192 h t m)). Qed.
Lemma lem1205770 {A : Type'} (t : list A) (h : A) : (term165 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1205771 {_28192 : Type'} (t : list _28192) (h : _28192) : (term165 _28192 h t) = h.
Proof. exact (@lem1205770 _28192 t h). Qed.
Lemma lem1205772 {_28192 : Type'} (t : list _28192) (m : list _28192) (h : _28192) : (term164 _28192 h t m) = h.
Proof. exact (@lem1205771 _28192 (@List.app _28192 t m) h). Qed.
Lemma lem1205773 {_28192 : Type'} (t : list _28192) (m : list _28192) (h : _28192) : (term163 _28192 h t m) = h.
Proof. exact (TRANS (@lem1205768 _28192 h t m) (@lem1205772 _28192 t m h)). Qed.
Lemma lem1205774 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205775 {_28192 : Type'} (t : list _28192) (m : list _28192) (h : _28192) : (term166 _28192 h t m) = (@eq _28192 h).
Proof. exact (MK_COMB (@lem1205774 _28192) (@lem1205773 _28192 t m h)). Qed.
Lemma lem1205777 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A t).
Proof. exact (EQ_MP (@lem1205514 A h t) (@lem1205513 A h t)). Qed.
Lemma lem1205778 {_28192 : Type'} (h : _28192) (t : list _28192) : (term11 _28192 h t) = (term12 _28192 t).
Proof. exact (@lem1205777 _28192 h t). Qed.
Lemma lem1205779 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem1205780 {_28192 : Type'} (h : _28192) (t : list _28192) : (term167 _28192 h t) = (term168 _28192 t).
Proof. exact (MK_COMB (@lem1205779) (@lem1205778 _28192 h t)). Qed.
Lemma lem1205782 (n : nat) : (term4 n) = True.
Proof. exact (EQ_MP (@lem1205500 n) (@lem1205499 n)). Qed.
Lemma lem1205783 {_28192 : Type'} (t : list _28192) : (term168 _28192 t) = True.
Proof. exact (@lem1205782 (@List.length _28192 t)). Qed.
Lemma lem1205784 {_28192 : Type'} (h : _28192) (t : list _28192) : (term167 _28192 h t) = True.
Proof. exact (TRANS (@lem1205780 _28192 h t) (@lem1205783 _28192 t)). Qed.
Lemma lem1205785 {_28192 : Type'} : (@COND _28192) = (@COND _28192).
Proof. exact (eq_refl (@COND _28192)). Qed.
Lemma lem1205786 {_28192 : Type'} (h : _28192) (t : list _28192) : (term169 _28192 h t) = (@COND _28192 True).
Proof. exact (MK_COMB (@lem1205785 _28192) (@lem1205784 _28192 h t)). Qed.
Lemma lem1205788 {A : Type'} (t : list A) (h : A) : (term165 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1205789 {_28192 : Type'} (t : list _28192) (h : _28192) : (term165 _28192 h t) = h.
Proof. exact (@lem1205788 _28192 t h). Qed.
Lemma lem1205790 {_28192 : Type'} (t : list _28192) (h : _28192) : (term170 _28192 h t) = (@COND _28192 True h).
Proof. exact (MK_COMB (@lem1205786 _28192 h t) (@lem1205789 _28192 t h)). Qed.
Lemma lem1205792 (m : nat) : (term151 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem1205506 m)). Qed.
Lemma lem1205793 {_28192 : Type'} (h : _28192) (t : list _28192) : (term171 _28192 h t) = (NUMERAL 0).
Proof. exact (@lem1205792 (term11 _28192 h t)). Qed.
Lemma lem1205794 {_28192 : Type'} : (@EL _28192) = (@EL _28192).
Proof. exact (eq_refl (@EL _28192)). Qed.
Lemma lem1205795 {_28192 : Type'} (h : _28192) (t : list _28192) : (term172 _28192 h t) = (term154 _28192).
Proof. exact (MK_COMB (@lem1205794 _28192) (@lem1205793 _28192 h t)). Qed.
Lemma lem1205796 {_28192 : Type'} (m : list _28192) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1205797 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term173 _28192 h t m) = (term50 _28192 m).
Proof. exact (MK_COMB (@lem1205795 _28192 h t) (@lem1205796 _28192 m)). Qed.
Lemma lem1205799 {_25569 : Type'} (l : list _25569) : (term50 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1205800 {_28192 : Type'} (l : list _28192) : (term50 _28192 l) = (@hd _28192 l).
Proof. exact (@lem1205799 _28192 l). Qed.
Lemma lem1205801 {_28192 : Type'} (m : list _28192) : (term50 _28192 m) = (@hd _28192 m).
Proof. exact (@lem1205800 _28192 m). Qed.
Lemma lem1205802 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term173 _28192 h t m) = (@hd _28192 m).
Proof. exact (TRANS (@lem1205797 _28192 h t m) (@lem1205801 _28192 m)). Qed.
Lemma lem1205803 {_28192 : Type'} (t : list _28192) (h : _28192) (m : list _28192) : (term174 _28192 h t m) = (term175 _28192 h m).
Proof. exact (MK_COMB (@lem1205790 _28192 t h) (@lem1205802 _28192 h t m)). Qed.
Lemma lem1205805 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1205806 {_28192 : Type'} (t2 : _28192) (t1 : _28192) : (@COND _28192 True t1 t2) = t1.
Proof. exact (@lem1205805 _28192 t2 t1). Qed.
Lemma lem1205807 {_28192 : Type'} (m : list _28192) (h : _28192) : (term175 _28192 h m) = h.
Proof. exact (@lem1205806 _28192 (@hd _28192 m) h). Qed.
Lemma lem1205808 {_28192 : Type'} (t : list _28192) (m : list _28192) (h : _28192) : (term174 _28192 h t m) = h.
Proof. exact (TRANS (@lem1205803 _28192 t h m) (@lem1205807 _28192 m h)). Qed.
Lemma lem1205809 {_28192 : Type'} (t : list _28192) (m : list _28192) (h : _28192) : ((term163 _28192 h t m) = (term174 _28192 h t m)) = (h = h).
Proof. exact (MK_COMB (@lem1205775 _28192 t m h) (@lem1205808 _28192 t m h)). Qed.
Lemma lem1205811 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1205812 {_28192 : Type'} (x : _28192) : (x = x) = True.
Proof. exact (@lem1205811 _28192 x). Qed.
Lemma lem1205813 {_28192 : Type'} (h : _28192) : (h = h) = True.
Proof. exact (@lem1205812 _28192 h). Qed.
Lemma lem1205814 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : ((term163 _28192 h t m) = (term174 _28192 h t m)) = True.
Proof. exact (TRANS (@lem1205809 _28192 t m h) (@lem1205813 _28192 h)). Qed.
Lemma lem1205815 {_28192 : Type'} (h : _28192) (t : list _28192) : (term176 _28192 h t) = (term159 _28192).
Proof. exact (fun_ext (fun m : list _28192 => @lem1205814 _28192 h t m)). Qed.
Lemma lem1205816 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205817 {_28192 : Type'} (h : _28192) (t : list _28192) : (term97 _28192 h t) = (term160 _28192).
Proof. exact (MK_COMB (@lem1205816 _28192) (@lem1205815 _28192 h t)). Qed.
Lemma lem1205819 {A : Type'} (t : Prop) : (term161 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1205820 {_28192 : Type'} (t : Prop) : (term162 _28192 t) = t.
Proof. exact (@lem1205819 (list _28192) t). Qed.
Lemma lem1205821 {_28192 : Type'} : (term160 _28192) = True.
Proof. exact (@lem1205820 _28192 True). Qed.
Lemma lem1205822 {_28192 : Type'} (h : _28192) (t : list _28192) : (term97 _28192 h t) = True.
Proof. exact (TRANS (@lem1205817 _28192 h t) (@lem1205821 _28192)). Qed.
Lemma lem1205823 {_28192 : Type'} (h : _28192) (t : list _28192) : True = (term97 _28192 h t).
Proof. exact (SYM (@lem1205822 _28192 h t)). Qed.
Lemma lem1205824 {_28192 : Type'} (h : _28192) (t : list _28192) : term97 _28192 h t.
Proof. exact (EQ_MP (@lem1205823 _28192 h t) (@lem0)). Qed.
Lemma lem1205832 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1205529 A l) (@lem1205528 A l)). Qed.
Lemma lem1205833 {_28192 : Type'} (l : list _28192) : (@List.app _28192 (@nil _28192) l) = l.
Proof. exact (@lem1205832 _28192 l). Qed.
Lemma lem1205834 {_28192 : Type'} (m : list _28192) : (@List.app _28192 (@nil _28192) m) = m.
Proof. exact (@lem1205833 _28192 m). Qed.
Lemma lem1205835 {_28192 : Type'} : (@tl _28192) = (@tl _28192).
Proof. exact (eq_refl (@tl _28192)). Qed.
Lemma lem1205836 {_28192 : Type'} (m : list _28192) : (term177 _28192 m) = (@tl _28192 m).
Proof. exact (MK_COMB (@lem1205835 _28192) (@lem1205834 _28192 m)). Qed.
Lemma lem1205837 {_28192 : Type'} (k : nat) : (@EL _28192 k) = (@EL _28192 k).
Proof. exact (eq_refl (@EL _28192 k)). Qed.
Lemma lem1205838 {_28192 : Type'} (k : nat) (m : list _28192) : (term178 _28192 k m) = (term69 _28192 k m).
Proof. exact (MK_COMB (@lem1205837 _28192 k) (@lem1205836 _28192 m)). Qed.
Lemma lem1205839 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205840 {_28192 : Type'} (k : nat) (m : list _28192) : (term179 _28192 k m) = (term180 _28192 k m).
Proof. exact (MK_COMB (@lem1205839 _28192) (@lem1205838 _28192 k m)). Qed.
Lemma lem1205842 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1205843 {_28192 : Type'} : (@List.length _28192 (@nil _28192)) = (NUMERAL 0).
Proof. exact (@lem1205842 _28192). Qed.
Lemma lem1205844 (k : nat) : (term181 k) = (term181 k).
Proof. exact (eq_refl (term181 k)). Qed.
Lemma lem1205845 {_28192 : Type'} (k : nat) : (term182 _28192 k) = (term183 k).
Proof. exact (MK_COMB (@lem1205844 k) (@lem1205843 _28192)). Qed.
Lemma lem1205847 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem1205495 m) (@lem1205494 m)). Qed.
Lemma lem1205848 (k : nat) : (term183 k) = False.
Proof. exact (@lem1205847 (S k)). Qed.
Lemma lem1205849 {_28192 : Type'} (k : nat) : (term182 _28192 k) = False.
Proof. exact (TRANS (@lem1205845 _28192 k) (@lem1205848 k)). Qed.
Lemma lem1205850 {_28192 : Type'} : (@COND _28192) = (@COND _28192).
Proof. exact (eq_refl (@COND _28192)). Qed.
Lemma lem1205851 {_28192 : Type'} (k : nat) : (term184 _28192 k) = (@COND _28192 False).
Proof. exact (MK_COMB (@lem1205850 _28192) (@lem1205849 _28192 k)). Qed.
Lemma lem1205852 {_28192 : Type'} (k : nat) : (term185 _28192 k) = (term185 _28192 k).
Proof. exact (eq_refl (term185 _28192 k)). Qed.
Lemma lem1205853 {_28192 : Type'} (k : nat) : (term186 _28192 k) = (term187 _28192 k).
Proof. exact (MK_COMB (@lem1205851 _28192 k) (@lem1205852 _28192 k)). Qed.
Lemma lem1205855 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1205856 {_28192 : Type'} : (@List.length _28192 (@nil _28192)) = (NUMERAL 0).
Proof. exact (@lem1205855 _28192). Qed.
Lemma lem1205857 (k : nat) : (term188 k) = (term188 k).
Proof. exact (eq_refl (term188 k)). Qed.
Lemma lem1205858 {_28192 : Type'} (k : nat) : (term189 _28192 k) = (term190 k).
Proof. exact (MK_COMB (@lem1205857 k) (@lem1205856 _28192)). Qed.
Lemma lem1205860 (m : nat) : (term191 m) = m.
Proof. exact (proj2 (@lem1205506 m)). Qed.
Lemma lem1205861 (k : nat) : (term190 k) = (S k).
Proof. exact (@lem1205860 (S k)). Qed.
Lemma lem1205862 {_28192 : Type'} (k : nat) : (term189 _28192 k) = (S k).
Proof. exact (TRANS (@lem1205858 _28192 k) (@lem1205861 k)). Qed.
Lemma lem1205863 {_28192 : Type'} : (@EL _28192) = (@EL _28192).
Proof. exact (eq_refl (@EL _28192)). Qed.
Lemma lem1205864 {_28192 : Type'} (k : nat) : (term192 _28192 k) = (term193 _28192 k).
Proof. exact (MK_COMB (@lem1205863 _28192) (@lem1205862 _28192 k)). Qed.
Lemma lem1205865 {_28192 : Type'} (m : list _28192) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1205866 {_28192 : Type'} (k : nat) (m : list _28192) : (term194 _28192 k m) = (term68 _28192 k m).
Proof. exact (MK_COMB (@lem1205864 _28192 k) (@lem1205865 _28192 m)). Qed.
Lemma lem1205868 {_25569 : Type'} (n : nat) (l : list _25569) : (term68 _25569 n l) = (term69 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1205869 {_28192 : Type'} (n : nat) (l : list _28192) : (term68 _28192 n l) = (term69 _28192 n l).
Proof. exact (@lem1205868 _28192 n l). Qed.
Lemma lem1205870 {_28192 : Type'} (k : nat) (m : list _28192) : (term68 _28192 k m) = (term69 _28192 k m).
Proof. exact (@lem1205869 _28192 k m). Qed.
Lemma lem1205871 {_28192 : Type'} (k : nat) (m : list _28192) : (term194 _28192 k m) = (term69 _28192 k m).
Proof. exact (TRANS (@lem1205866 _28192 k m) (@lem1205870 _28192 k m)). Qed.
Lemma lem1205872 {_28192 : Type'} (k : nat) (m : list _28192) : (term195 _28192 k m) = (term196 _28192 k m).
Proof. exact (MK_COMB (@lem1205853 _28192 k) (@lem1205871 _28192 k m)). Qed.
Lemma lem1205874 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1205875 {_28192 : Type'} (t1 : _28192) (t2 : _28192) : (@COND _28192 False t1 t2) = t2.
Proof. exact (@lem1205874 _28192 t1 t2). Qed.
Lemma lem1205876 {_28192 : Type'} (k : nat) (m : list _28192) : (term196 _28192 k m) = (term69 _28192 k m).
Proof. exact (@lem1205875 _28192 (term185 _28192 k) (term69 _28192 k m)). Qed.
Lemma lem1205877 {_28192 : Type'} (k : nat) (m : list _28192) : (term195 _28192 k m) = (term69 _28192 k m).
Proof. exact (TRANS (@lem1205872 _28192 k m) (@lem1205876 _28192 k m)). Qed.
Lemma lem1205878 {_28192 : Type'} (k : nat) (m : list _28192) : ((term178 _28192 k m) = (term195 _28192 k m)) = ((term69 _28192 k m) = (term69 _28192 k m)).
Proof. exact (MK_COMB (@lem1205840 _28192 k m) (@lem1205877 _28192 k m)). Qed.
Lemma lem1205880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1205881 {_28192 : Type'} (x : _28192) : (x = x) = True.
Proof. exact (@lem1205880 _28192 x). Qed.
Lemma lem1205882 {_28192 : Type'} (k : nat) (m : list _28192) : ((term69 _28192 k m) = (term69 _28192 k m)) = True.
Proof. exact (@lem1205881 _28192 (term69 _28192 k m)). Qed.
Lemma lem1205883 {_28192 : Type'} (k : nat) (m : list _28192) : ((term178 _28192 k m) = (term195 _28192 k m)) = True.
Proof. exact (TRANS (@lem1205878 _28192 k m) (@lem1205882 _28192 k m)). Qed.
Lemma lem1205884 {_28192 : Type'} (k : nat) : (term197 _28192 k) = (term159 _28192).
Proof. exact (fun_ext (fun m : list _28192 => @lem1205883 _28192 k m)). Qed.
Lemma lem1205885 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205886 {_28192 : Type'} (k : nat) : (term117 _28192 k) = (term160 _28192).
Proof. exact (MK_COMB (@lem1205885 _28192) (@lem1205884 _28192 k)). Qed.
Lemma lem1205888 {A : Type'} (t : Prop) : (term161 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1205889 {_28192 : Type'} (t : Prop) : (term162 _28192 t) = t.
Proof. exact (@lem1205888 (list _28192) t). Qed.
Lemma lem1205890 {_28192 : Type'} : (term160 _28192) = True.
Proof. exact (@lem1205889 _28192 True). Qed.
Lemma lem1205891 {_28192 : Type'} (k : nat) : (term117 _28192 k) = True.
Proof. exact (TRANS (@lem1205886 _28192 k) (@lem1205890 _28192)). Qed.
Lemma lem1205892 {_28192 : Type'} (k : nat) : True = (term117 _28192 k).
Proof. exact (SYM (@lem1205891 _28192 k)). Qed.
Lemma lem1205893 {_28192 : Type'} (k : nat) : term117 _28192 k.
Proof. exact (EQ_MP (@lem1205892 _28192 k) (@lem0)). Qed.
Lemma lem1205901 {A : Type'} (h : A) (t : list A) (l : list A) : (term19 A h t l) = (term20 A h t l).
Proof. exact (EQ_MP (@lem1205525 A h t l) (@lem1205524 A h t l)). Qed.
Lemma lem1205902 {_28192 : Type'} (h : _28192) (t : list _28192) (l : list _28192) : (term19 _28192 h t l) = (term20 _28192 h t l).
Proof. exact (@lem1205901 _28192 h t l). Qed.
Lemma lem1205903 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term19 _28192 h t m) = (term20 _28192 h t m).
Proof. exact (@lem1205902 _28192 h t m). Qed.
Lemma lem1205904 {_28192 : Type'} : (@tl _28192) = (@tl _28192).
Proof. exact (eq_refl (@tl _28192)). Qed.
Lemma lem1205905 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term198 _28192 h t m) = (term199 _28192 h t m).
Proof. exact (MK_COMB (@lem1205904 _28192) (@lem1205903 _28192 h t m)). Qed.
Lemma lem1205906 {_28192 : Type'} (k : nat) : (@EL _28192 k) = (@EL _28192 k).
Proof. exact (eq_refl (@EL _28192 k)). Qed.
Lemma lem1205907 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) (m : list _28192) : (term200 _28192 k h t m) = (term201 _28192 k h t m).
Proof. exact (MK_COMB (@lem1205906 _28192 k) (@lem1205905 _28192 h t m)). Qed.
Lemma lem1205908 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205909 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) (m : list _28192) : (term202 _28192 k h t m) = (term203 _28192 k h t m).
Proof. exact (MK_COMB (@lem1205908 _28192) (@lem1205907 _28192 k h t m)). Qed.
Lemma lem1205911 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A t).
Proof. exact (EQ_MP (@lem1205514 A h t) (@lem1205513 A h t)). Qed.
Lemma lem1205912 {_28192 : Type'} (h : _28192) (t : list _28192) : (term11 _28192 h t) = (term12 _28192 t).
Proof. exact (@lem1205911 _28192 h t). Qed.
Lemma lem1205913 (k : nat) : (term181 k) = (term181 k).
Proof. exact (eq_refl (term181 k)). Qed.
Lemma lem1205914 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term204 _28192 k h t) = (term205 _28192 k t).
Proof. exact (MK_COMB (@lem1205913 k) (@lem1205912 _28192 h t)). Qed.
Lemma lem1205915 {_28192 : Type'} : (@COND _28192) = (@COND _28192).
Proof. exact (eq_refl (@COND _28192)). Qed.
Lemma lem1205916 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term206 _28192 k h t) = (term207 _28192 k t).
Proof. exact (MK_COMB (@lem1205915 _28192) (@lem1205914 _28192 h k t)). Qed.
Lemma lem1205917 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) : (term208 _28192 k h t) = (term208 _28192 k h t).
Proof. exact (eq_refl (term208 _28192 k h t)). Qed.
Lemma lem1205918 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) : (term209 _28192 k h t) = (term210 _28192 k h t).
Proof. exact (MK_COMB (@lem1205916 _28192 h k t) (@lem1205917 _28192 k h t)). Qed.
Lemma lem1205920 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A t).
Proof. exact (EQ_MP (@lem1205514 A h t) (@lem1205513 A h t)). Qed.
Lemma lem1205921 {_28192 : Type'} (h : _28192) (t : list _28192) : (term11 _28192 h t) = (term12 _28192 t).
Proof. exact (@lem1205920 _28192 h t). Qed.
Lemma lem1205922 (k : nat) : (term188 k) = (term188 k).
Proof. exact (eq_refl (term188 k)). Qed.
Lemma lem1205923 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term211 _28192 k h t) = (term212 _28192 k t).
Proof. exact (MK_COMB (@lem1205922 k) (@lem1205921 _28192 h t)). Qed.
Lemma lem1205924 {_28192 : Type'} : (@EL _28192) = (@EL _28192).
Proof. exact (eq_refl (@EL _28192)). Qed.
Lemma lem1205925 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term213 _28192 k h t) = (term214 _28192 k t).
Proof. exact (MK_COMB (@lem1205924 _28192) (@lem1205923 _28192 h k t)). Qed.
Lemma lem1205926 {_28192 : Type'} (m : list _28192) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1205927 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) (m : list _28192) : (term215 _28192 k h t m) = (term216 _28192 k t m).
Proof. exact (MK_COMB (@lem1205925 _28192 h k t) (@lem1205926 _28192 m)). Qed.
Lemma lem1205928 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) (m : list _28192) : (term217 _28192 k h t m) = (term218 _28192 h k t m).
Proof. exact (MK_COMB (@lem1205918 _28192 k h t) (@lem1205927 _28192 h k t m)). Qed.
Lemma lem1205929 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) (m : list _28192) : ((term200 _28192 k h t m) = (term217 _28192 k h t m)) = ((term201 _28192 k h t m) = (term218 _28192 h k t m)).
Proof. exact (MK_COMB (@lem1205909 _28192 k h t m) (@lem1205928 _28192 h k t m)). Qed.
Lemma lem1205932 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term219 _28192 k h t) = (term220 _28192 h k t).
Proof. exact (fun_ext (fun m : list _28192 => @lem1205929 _28192 h k t m)). Qed.
Lemma lem1205933 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1205934 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term124 _28192 k h t) = (term221 _28192 h k t).
Proof. exact (MK_COMB (@lem1205933 _28192) (@lem1205932 _28192 h k t)). Qed.
Lemma lem1205939 {_28192 : Type'} (k : nat) (h : _28192) (t : list _28192) : (term221 _28192 h k t) = (term124 _28192 k h t).
Proof. exact (SYM (@lem1205934 _28192 h k t)). Qed.
Lemma lem1205940 (m : nat) : term222 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem1205941 (m : nat) : (term222 m) = (term223 m).
Proof. exact (eq_refl (term222 m)). Qed.
Lemma lem1205942 (m : nat) : term223 m.
Proof. exact (EQ_MP (@lem1205941 m) (@lem1205940 m)). Qed.
Lemma lem1205943 (m : nat) (n : nat) : term224 m n.
Proof. exact (@lem1205942 m n). Qed.
Lemma lem1205944 (m : nat) (n : nat) : (term224 m n) = ((term225 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term224 m n)). Qed.
Lemma lem1205946 (m : nat) : term226 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem1205947 (m : nat) : (term226 m) = (term227 m).
Proof. exact (eq_refl (term226 m)). Qed.
Lemma lem1205948 (m : nat) : term227 m.
Proof. exact (EQ_MP (@lem1205947 m) (@lem1205946 m)). Qed.
Lemma lem1205949 (m : nat) (n : nat) : term228 m n.
Proof. exact (@lem1205948 m n). Qed.
Lemma lem1205950 (m : nat) (n : nat) : (term228 m n) = ((term229 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term228 m n)). Qed.
Lemma lem1205952 {_28192 : Type'} (l : list _28192) (k : nat) (h1 : term31 _28192 k) : term230 _28192 k l.
Proof. exact (@lem1205556 _28192 k h1 l). Qed.
Lemma lem1205953 {_28192 : Type'} (k : nat) (l : list _28192) : (term230 _28192 k l) = (term231 _28192 k l).
Proof. exact (eq_refl (term230 _28192 k l)). Qed.
Lemma lem1205954 {_28192 : Type'} (l : list _28192) (k : nat) (h1 : term31 _28192 k) : term231 _28192 k l.
Proof. exact (EQ_MP (@lem1205953 _28192 k l) (@lem1205952 _28192 l k h1)). Qed.
Lemma lem1205955 {_28192 : Type'} (l : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : term232 _28192 k l m.
Proof. exact (@lem1205954 _28192 l k h1 m). Qed.
Lemma lem1205956 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term232 _28192 k l m) = ((term233 _28192 k l m) = (term234 _28192 k l m)).
Proof. exact (eq_refl (term232 _28192 k l m)). Qed.
Lemma lem1205968 {A : Type'} (h : A) (t : list A) : (term235 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1205969 {_28192 : Type'} (h : _28192) (t : list _28192) : (term235 _28192 h t) = t.
Proof. exact (@lem1205968 _28192 h t). Qed.
Lemma lem1205970 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) : (term199 _28192 h t m) = (@List.app _28192 t m).
Proof. exact (@lem1205969 _28192 h (@List.app _28192 t m)). Qed.
Lemma lem1205971 {_28192 : Type'} (k : nat) : (@EL _28192 k) = (@EL _28192 k).
Proof. exact (eq_refl (@EL _28192 k)). Qed.
Lemma lem1205972 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) (m : list _28192) : (term201 _28192 k h t m) = (term233 _28192 k t m).
Proof. exact (MK_COMB (@lem1205971 _28192 k) (@lem1205970 _28192 h t m)). Qed.
Lemma lem1205974 {_28192 : Type'} (l : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : (term233 _28192 k l m) = (term234 _28192 k l m).
Proof. exact (EQ_MP (@lem1205956 _28192 k l m) (@lem1205955 _28192 l m k h1)). Qed.
Lemma lem1205975 {_28192 : Type'} (l : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : (term233 _28192 k l m) = (term234 _28192 k l m).
Proof. exact (@lem1205974 _28192 l m k h1). Qed.
Lemma lem1205976 {_28192 : Type'} (t : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : (term233 _28192 k t m) = (term234 _28192 k t m).
Proof. exact (@lem1205975 _28192 t m k h1). Qed.
Lemma lem1205977 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : (term201 _28192 k h t m) = (term234 _28192 k t m).
Proof. exact (TRANS (@lem1205972 _28192 h k t m) (@lem1205976 _28192 t m k h1)). Qed.
Lemma lem1205978 {_28192 : Type'} : (@eq _28192) = (@eq _28192).
Proof. exact (eq_refl (@eq _28192)). Qed.
Lemma lem1205979 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : (term203 _28192 k h t m) = (term236 _28192 k t m).
Proof. exact (MK_COMB (@lem1205978 _28192) (@lem1205977 _28192 h t m k h1)). Qed.
Lemma lem1205981 (m : nat) (n : nat) : (term229 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1205950 m n) (@lem1205949 m n)). Qed.
Lemma lem1205982 {_28192 : Type'} (k : nat) (t : list _28192) : (term205 _28192 k t) = (term237 _28192 k t).
Proof. exact (@lem1205981 k (@List.length _28192 t)). Qed.
Lemma lem1205983 {_28192 : Type'} : (@COND _28192) = (@COND _28192).
Proof. exact (eq_refl (@COND _28192)). Qed.
Lemma lem1205984 {_28192 : Type'} (k : nat) (t : list _28192) : (term207 _28192 k t) = (term238 _28192 k t).
Proof. exact (MK_COMB (@lem1205983 _28192) (@lem1205982 _28192 k t)). Qed.
Lemma lem1205986 {A : Type'} (h : A) (t : list A) : (term235 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1205987 {_28192 : Type'} (h : _28192) (t : list _28192) : (term235 _28192 h t) = t.
Proof. exact (@lem1205986 _28192 h t). Qed.
Lemma lem1205988 {_28192 : Type'} (k : nat) : (@EL _28192 k) = (@EL _28192 k).
Proof. exact (eq_refl (@EL _28192 k)). Qed.
Lemma lem1205989 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term208 _28192 k h t) = (@EL _28192 k t).
Proof. exact (MK_COMB (@lem1205988 _28192 k) (@lem1205987 _28192 h t)). Qed.
Lemma lem1205990 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) : (term210 _28192 k h t) = (term239 _28192 k t).
Proof. exact (MK_COMB (@lem1205984 _28192 k t) (@lem1205989 _28192 h k t)). Qed.
Lemma lem1205992 (m : nat) (n : nat) : (term225 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem1205944 m n) (@lem1205943 m n)). Qed.
Lemma lem1205993 {_28192 : Type'} (k : nat) (t : list _28192) : (term212 _28192 k t) = (term240 _28192 k t).
Proof. exact (@lem1205992 k (@List.length _28192 t)). Qed.
Lemma lem1205994 {_28192 : Type'} : (@EL _28192) = (@EL _28192).
Proof. exact (eq_refl (@EL _28192)). Qed.
Lemma lem1205995 {_28192 : Type'} (k : nat) (t : list _28192) : (term214 _28192 k t) = (term241 _28192 k t).
Proof. exact (MK_COMB (@lem1205994 _28192) (@lem1205993 _28192 k t)). Qed.
Lemma lem1205996 {_28192 : Type'} (m : list _28192) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1205997 {_28192 : Type'} (k : nat) (t : list _28192) (m : list _28192) : (term216 _28192 k t m) = (term242 _28192 k t m).
Proof. exact (MK_COMB (@lem1205995 _28192 k t) (@lem1205996 _28192 m)). Qed.
Lemma lem1205998 {_28192 : Type'} (h : _28192) (k : nat) (t : list _28192) (m : list _28192) : (term218 _28192 h k t m) = (term234 _28192 k t m).
Proof. exact (MK_COMB (@lem1205990 _28192 h k t) (@lem1205997 _28192 k t m)). Qed.
Lemma lem1205999 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : ((term201 _28192 k h t m) = (term218 _28192 h k t m)) = ((term234 _28192 k t m) = (term234 _28192 k t m)).
Proof. exact (MK_COMB (@lem1205979 _28192 h t m k h1) (@lem1205998 _28192 h k t m)). Qed.
Lemma lem1206001 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206002 {_28192 : Type'} (x : _28192) : (x = x) = True.
Proof. exact (@lem1206001 _28192 x). Qed.
Lemma lem1206003 {_28192 : Type'} (k : nat) (t : list _28192) (m : list _28192) : ((term234 _28192 k t m) = (term234 _28192 k t m)) = True.
Proof. exact (@lem1206002 _28192 (term234 _28192 k t m)). Qed.
Lemma lem1206004 {_28192 : Type'} (h : _28192) (t : list _28192) (m : list _28192) (k : nat) (h1 : term31 _28192 k) : ((term201 _28192 k h t m) = (term218 _28192 h k t m)) = True.
Proof. exact (TRANS (@lem1205999 _28192 h t m k h1) (@lem1206003 _28192 k t m)). Qed.
Lemma lem1206005 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : (term220 _28192 h k t) = (term159 _28192).
Proof. exact (fun_ext (fun m : list _28192 => @lem1206004 _28192 h t m k h1)). Qed.
Lemma lem1206006 {_28192 : Type'} : (@all (list _28192)) = (@all (list _28192)).
Proof. exact (eq_refl (@all (list _28192))). Qed.
Lemma lem1206007 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : (term221 _28192 h k t) = (term160 _28192).
Proof. exact (MK_COMB (@lem1206006 _28192) (@lem1206005 _28192 h t k h1)). Qed.
Lemma lem1206009 {A : Type'} (t : Prop) : (term161 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206010 {_28192 : Type'} (t : Prop) : (term162 _28192 t) = t.
Proof. exact (@lem1206009 (list _28192) t). Qed.
Lemma lem1206011 {_28192 : Type'} : (term160 _28192) = True.
Proof. exact (@lem1206010 _28192 True). Qed.
Lemma lem1206012 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : (term221 _28192 h k t) = True.
Proof. exact (TRANS (@lem1206007 _28192 h t k h1) (@lem1206011 _28192)). Qed.
Lemma lem1206013 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : True = (term221 _28192 h k t).
Proof. exact (SYM (@lem1206012 _28192 h t k h1)). Qed.
Lemma lem1206014 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : term221 _28192 h k t.
Proof. exact (EQ_MP (@lem1206013 _28192 h t k h1) (@lem0)). Qed.
Lemma lem1206015 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : term124 _28192 k h t.
Proof. exact (EQ_MP (@lem1205939 _28192 k h t) (@lem1206014 _28192 h t k h1)). Qed.
Lemma lem1206016 {_28192 : Type'} (h : _28192) (t : list _28192) (k : nat) (h1 : term31 _28192 k) : term126 _28192 k h t.
Proof. exact (fun h0 : term83 _28192 k t => @lem1206015 _28192 h t k h1). Qed.
Lemma lem1206021 {_28192 : Type'} (h : _28192) (k : nat) (h1 : term31 _28192 k) : term130 _28192 k h.
Proof. exact (fun t : list _28192 => @lem1206016 _28192 h t k h1). Qed.
Lemma lem1206026 {_28192 : Type'} (k : nat) (h1 : term31 _28192 k) : term134 _28192 k.
Proof. exact (fun h : _28192 => @lem1206021 _28192 h k h1). Qed.
Lemma lem1206027 {_28192 : Type'} (k : nat) (h1 : term31 _28192 k) : term136 _28192 k.
Proof. exact (conj (@lem1205893 _28192 k) (@lem1206026 _28192 k h1)). Qed.
Lemma lem1206028 {_28192 : Type'} (k : nat) (h1 : term31 _28192 k) : term86 _28192 k.
Proof. exact (@lem1205694 _28192 k (@lem1206027 _28192 k h1)). Qed.
Lemma lem1206029 {_28192 : Type'} (h : _28192) (t : list _28192) : term99 _28192 h t.
Proof. exact (fun h0 : term64 _28192 t => @lem1205824 _28192 h t). Qed.
Lemma lem1206034 {_28192 : Type'} (h : _28192) : term103 _28192 h.
Proof. exact (fun t : list _28192 => @lem1206029 _28192 h t). Qed.
Lemma lem1206039 {_28192 : Type'} : term107 _28192.
Proof. exact (fun h : _28192 => @lem1206034 _28192 h). Qed.
Lemma lem1206040 {_28192 : Type'} : term109 _28192.
Proof. exact (conj (@lem1205756 _28192) (@lem1206039 _28192)). Qed.
Lemma lem1206041 {_28192 : Type'} : term67 _28192.
Proof. exact (@lem1205666 _28192 (@lem1206040 _28192)). Qed.
Lemma lem1206042 {_28192 : Type'} (k : nat) (h1 : term31 _28192 k) : term35 _28192 k.
Proof. exact (EQ_MP (@lem1205639 _28192 k) (@lem1206028 _28192 k h1)). Qed.
Lemma lem1206043 {_28192 : Type'} : term27 _28192.
Proof. exact (EQ_MP (@lem1205597 _28192) (@lem1206041 _28192)). Qed.
Lemma lem1206044 {_28192 : Type'} (k : nat) : term37 _28192 k.
Proof. exact (fun h0 : term31 _28192 k => @lem1206042 _28192 k h0). Qed.
Lemma lem1206049 {_28192 : Type'} : term41 _28192.
Proof. exact (fun k : nat => @lem1206044 _28192 k). Qed.
Lemma lem1206050 {_28192 : Type'} : term43 _28192.
Proof. exact (conj (@lem1206043 _28192) (@lem1206049 _28192)). Qed.
Lemma lem1206051 {_28192 : Type'} : term48 _28192.
Proof. exact (@lem1205555 _28192 (@lem1206050 _28192)). Qed.
