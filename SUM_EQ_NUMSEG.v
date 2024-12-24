Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_NUMSEG_spec.
Require Import IN_NUMSEG_spec.
Require Import SUM_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7210449 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7210450 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7210451 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7210450 t1) (@lem7210449 t1)). Qed.
Lemma lem7210452 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7210451 t1 t2). Qed.
Lemma lem7210453 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7210454 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7210453 t1 t2) (@lem7210452 t1 t2)). Qed.
Lemma lem7210455 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7210454 t1 t2 t3). Qed.
Lemma lem7210456 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7210457 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7210456 t1 t2 t3) (@lem7210455 t1 t2 t3)). Qed.
Lemma lem7210458 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7210457 t1 t2 t3)). Qed.
Lemma lem7210460 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7210461 : term8 = term9.
Proof. exact (@lem7210460 term8). Qed.
Lemma lem7210462 : term9 = term8.
Proof. exact (SYM (@lem7210461)). Qed.
Lemma lem7210463 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7210464 : term11.
Proof. exact (@lem7081239 nat). Qed.
Lemma lem7210467 {_132349 : Type'} (h1 : term12 _132349) : term12 _132349.
Proof. exact (h1). Qed.
Lemma lem7210468 {_132349 : Type'} : term13 _132349.
Proof. exact (fun h0 : term12 _132349 => @lem7210467 _132349 h0). Qed.
Lemma lem7210469 {_132349 : Type'} (h1 : term13 _132349) : term13 _132349.
Proof. exact (h1). Qed.
Lemma lem7210470 {_132349 : Type'} (h1 : term12 _132349) : term12 _132349.
Proof. exact (h1). Qed.
Lemma lem7210471 {_132349 : Type'} (h1 : term12 _132349) (h2 : term13 _132349) : term12 _132349.
Proof. exact (@lem7210469 _132349 h2 (@lem7210470 _132349 h1)). Qed.
Lemma lem7210472 {_132349 : Type'} (h1 : term12 _132349) : term14 _132349.
Proof. exact (fun h0 : term13 _132349 => @lem7210471 _132349 h1 h0). Qed.
Lemma lem7210473 {_132349 : Type'} (h1 : term13 _132349) : term13 _132349.
Proof. exact (h1). Qed.
Lemma lem7210474 {_132349 : Type'} (h1 : term12 _132349) (h2 : term13 _132349) : term12 _132349.
Proof. exact (@lem7210472 _132349 h1 (@lem7210473 _132349 h2)). Qed.
Lemma lem7210475 {_132349 : Type'} (h1 : term13 _132349) : term13 _132349.
Proof. exact (fun h0 : term12 _132349 => @lem7210474 _132349 h0 h1). Qed.
Lemma lem7210476 {_132349 : Type'} : term15 _132349.
Proof. exact (fun h0 : term13 _132349 => @lem7210475 _132349 h0). Qed.
Lemma lem7210479 {_132349 : Type'} : term13 _132349.
Proof. exact (@lem7210476 _132349 (@lem7210468 _132349)). Qed.
Lemma lem7210480 {_132349 : Type'} : term13 _132349.
Proof. exact (@lem7210479 _132349). Qed.
Lemma lem7210558 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7210559 : term16 = term17.
Proof. exact (@lem7210558 term11). Qed.
Lemma lem7210580 {_132349 : Type'} : (term18 _132349) = (term18 _132349).
Proof. exact (eq_refl (term18 _132349)). Qed.
Lemma lem7210581 {_132349 : Type'} : (term19 _132349) = (term20 _132349).
Proof. exact (MK_COMB (@lem7210580 _132349) (@lem7210559)). Qed.
Lemma lem7210584 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7210585 {_132349 : Type'} : (term22 _132349) = (term23 _132349).
Proof. exact (MK_COMB (@lem7210584) (@lem7210581 _132349)). Qed.
Lemma lem7210588 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7210589 {_132349 : Type'} : (term25 _132349) = (term26 _132349).
Proof. exact (MK_COMB (@lem7210588) (@lem7210585 _132349)). Qed.
Lemma lem7210592 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem7210599 {_132349 : Type'} : (term12 _132349) = (term28 _132349).
Proof. exact (MK_COMB (@lem7210592) (@lem7210589 _132349)). Qed.
Lemma lem7210600 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : ((@sum nat s f) = (@sum nat s g)) = ((@sum nat s f) = (@sum nat s g)).
Proof. exact (eq_refl ((@sum nat s f) = (@sum nat s g))). Qed.
Lemma lem7210605 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term29 s f g x) = (term29 s f g x).
Proof. exact (eq_refl (term29 s f g x)). Qed.
Lemma lem7210606 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term30 s f g) = (term30 s f g).
Proof. exact (fun_ext (fun x : nat => @lem7210605 s f g x)). Qed.
Lemma lem7210607 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210608 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term31 s f g) = (term31 s f g).
Proof. exact (MK_COMB (@lem7210607) (@lem7210606 s f g)). Qed.
Lemma lem7210609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210610 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term32 s f g) = (term32 s f g).
Proof. exact (MK_COMB (@lem7210609) (@lem7210608 s f g)). Qed.
Lemma lem7210611 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term33 f s g) = (term33 f s g).
Proof. exact (MK_COMB (@lem7210610 s f g) (@lem7210600 f s g)). Qed.
Lemma lem7210612 (f : nat -> real) (g : nat -> real) : (term34 f g) = (term34 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7210611 f s g)). Qed.
Lemma lem7210613 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7210614 (f : nat -> real) (g : nat -> real) : (term35 f g) = (term35 f g).
Proof. exact (MK_COMB (@lem7210613) (@lem7210612 f g)). Qed.
Lemma lem7210615 (f : nat -> real) : (term36 f) = (term36 f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7210614 f g)). Qed.
Lemma lem7210616 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210617 (f : nat -> real) : (term37 f) = (term37 f).
Proof. exact (MK_COMB (@lem7210616) (@lem7210615 f)). Qed.
Lemma lem7210618 : term38 = term38.
Proof. exact (fun_ext (fun f : nat -> real => @lem7210617 f)). Qed.
Lemma lem7210619 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210620 : term11 = term11.
Proof. exact (MK_COMB (@lem7210619) (@lem7210618)). Qed.
Lemma lem7210621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7210622 : term17 = term17.
Proof. exact (MK_COMB (@lem7210621) (@lem7210620)). Qed.
Lemma lem7210623 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7210628 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term39 _132349 s f g x) = (term39 _132349 s f g x).
Proof. exact (eq_refl (term39 _132349 s f g x)). Qed.
Lemma lem7210629 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term40 _132349 s f g) = (term40 _132349 s f g).
Proof. exact (fun_ext (fun x : _132349 => @lem7210628 _132349 s f g x)). Qed.
Lemma lem7210630 {_132349 : Type'} : (@all _132349) = (@all _132349).
Proof. exact (eq_refl (@all _132349)). Qed.
Lemma lem7210631 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term41 _132349 s f g) = (term41 _132349 s f g).
Proof. exact (MK_COMB (@lem7210630 _132349) (@lem7210629 _132349 s f g)). Qed.
Lemma lem7210632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210633 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term42 _132349 s f g) = (term42 _132349 s f g).
Proof. exact (MK_COMB (@lem7210632) (@lem7210631 _132349 s f g)). Qed.
Lemma lem7210634 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term43 _132349 f s g) = (term43 _132349 f s g).
Proof. exact (MK_COMB (@lem7210633 _132349 s f g) (@lem7210623 _132349 f s g)). Qed.
Lemma lem7210635 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term44 _132349 f g) = (term44 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7210634 _132349 f s g)). Qed.
Lemma lem7210636 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7210637 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term45 _132349 f g) = (term45 _132349 f g).
Proof. exact (MK_COMB (@lem7210636 _132349) (@lem7210635 _132349 f g)). Qed.
Lemma lem7210638 {_132349 : Type'} (f : _132349 -> real) : (term46 _132349 f) = (term46 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7210637 _132349 f g)). Qed.
Lemma lem7210639 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7210640 {_132349 : Type'} (f : _132349 -> real) : (term47 _132349 f) = (term47 _132349 f).
Proof. exact (MK_COMB (@lem7210639 _132349) (@lem7210638 _132349 f)). Qed.
Lemma lem7210641 {_132349 : Type'} : (term48 _132349) = (term48 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7210640 _132349 f)). Qed.
Lemma lem7210642 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7210643 {_132349 : Type'} : (term49 _132349) = (term49 _132349).
Proof. exact (MK_COMB (@lem7210642 _132349) (@lem7210641 _132349)). Qed.
Lemma lem7210644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210645 {_132349 : Type'} : (term18 _132349) = (term18 _132349).
Proof. exact (MK_COMB (@lem7210644) (@lem7210643 _132349)). Qed.
Lemma lem7210646 {_132349 : Type'} : (term20 _132349) = (term20 _132349).
Proof. exact (MK_COMB (@lem7210645 _132349) (@lem7210622)). Qed.
Lemma lem7210647 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem7210648 (m : nat) : (term51 m) = (term51 m).
Proof. exact (fun_ext (fun n : nat => @lem7210647 m n)). Qed.
Lemma lem7210649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210650 (m : nat) : (term52 m) = (term52 m).
Proof. exact (MK_COMB (@lem7210649) (@lem7210648 m)). Qed.
Lemma lem7210651 : term53 = term53.
Proof. exact (fun_ext (fun m : nat => @lem7210650 m)). Qed.
Lemma lem7210652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210653 : term54 = term54.
Proof. exact (MK_COMB (@lem7210652) (@lem7210651)). Qed.
Lemma lem7210654 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210655 : term21 = term21.
Proof. exact (MK_COMB (@lem7210654) (@lem7210653)). Qed.
Lemma lem7210656 {_132349 : Type'} : (term23 _132349) = (term23 _132349).
Proof. exact (MK_COMB (@lem7210655) (@lem7210646 _132349)). Qed.
Lemma lem7210665 (m : nat) (p : nat) (n : nat) : ((term55 p m n) = (term56 m p n)) = ((term55 p m n) = (term56 m p n)).
Proof. exact (eq_refl ((term55 p m n) = (term56 m p n))). Qed.
Lemma lem7210666 (m : nat) (n : nat) : (term57 m n) = (term57 m n).
Proof. exact (fun_ext (fun p : nat => @lem7210665 m p n)). Qed.
Lemma lem7210667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210668 (m : nat) (n : nat) : (term58 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem7210667) (@lem7210666 m n)). Qed.
Lemma lem7210669 (m : nat) : (term59 m) = (term59 m).
Proof. exact (fun_ext (fun n : nat => @lem7210668 m n)). Qed.
Lemma lem7210670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210671 (m : nat) : (term60 m) = (term60 m).
Proof. exact (MK_COMB (@lem7210670) (@lem7210669 m)). Qed.
Lemma lem7210672 : term61 = term61.
Proof. exact (fun_ext (fun m : nat => @lem7210671 m)). Qed.
Lemma lem7210673 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210674 : term62 = term62.
Proof. exact (MK_COMB (@lem7210673) (@lem7210672)). Qed.
Lemma lem7210675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210676 : term24 = term24.
Proof. exact (MK_COMB (@lem7210675) (@lem7210674)). Qed.
Lemma lem7210677 {_132349 : Type'} : (term26 _132349) = (term26 _132349).
Proof. exact (MK_COMB (@lem7210676) (@lem7210656 _132349)). Qed.
Lemma lem7210678 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term63 m n f) = (term63 m n g)) = ((term63 m n f) = (term63 m n g)).
Proof. exact (eq_refl ((term63 m n f) = (term63 m n g))). Qed.
Lemma lem7210687 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term64 m n f g i) = (term64 m n f g i).
Proof. exact (eq_refl (term64 m n f g i)). Qed.
Lemma lem7210688 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term65 m n f g) = (term65 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7210687 m n f g i)). Qed.
Lemma lem7210689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210690 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term66 m n f g) = (term66 m n f g).
Proof. exact (MK_COMB (@lem7210689) (@lem7210688 m n f g)). Qed.
Lemma lem7210691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210692 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term67 m n f g) = (term67 m n f g).
Proof. exact (MK_COMB (@lem7210691) (@lem7210690 m n f g)). Qed.
Lemma lem7210693 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term68 f m n g) = (term68 f m n g).
Proof. exact (MK_COMB (@lem7210692 m n f g) (@lem7210678 f m n g)). Qed.
Lemma lem7210694 (f : nat -> real) (m : nat) (g : nat -> real) : (term69 f m g) = (term69 f m g).
Proof. exact (fun_ext (fun n : nat => @lem7210693 f m n g)). Qed.
Lemma lem7210695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210696 (f : nat -> real) (m : nat) (g : nat -> real) : (term70 f m g) = (term70 f m g).
Proof. exact (MK_COMB (@lem7210695) (@lem7210694 f m g)). Qed.
Lemma lem7210697 (f : nat -> real) (g : nat -> real) : (term71 f g) = (term71 f g).
Proof. exact (fun_ext (fun m : nat => @lem7210696 f m g)). Qed.
Lemma lem7210698 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210699 (f : nat -> real) (g : nat -> real) : (term72 f g) = (term72 f g).
Proof. exact (MK_COMB (@lem7210698) (@lem7210697 f g)). Qed.
Lemma lem7210700 (f : nat -> real) : (term73 f) = (term73 f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7210699 f g)). Qed.
Lemma lem7210701 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210702 (f : nat -> real) : (term74 f) = (term74 f).
Proof. exact (MK_COMB (@lem7210701) (@lem7210700 f)). Qed.
Lemma lem7210703 : term75 = term75.
Proof. exact (fun_ext (fun f : nat -> real => @lem7210702 f)). Qed.
Lemma lem7210704 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210705 : term8 = term8.
Proof. exact (MK_COMB (@lem7210704) (@lem7210703)). Qed.
Lemma lem7210706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7210707 : term10 = term10.
Proof. exact (MK_COMB (@lem7210706) (@lem7210705)). Qed.
Lemma lem7210708 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7210709 : term27 = term27.
Proof. exact (MK_COMB (@lem7210708) (@lem7210707)). Qed.
Lemma lem7210710 {_132349 : Type'} : (term28 _132349) = (term28 _132349).
Proof. exact (MK_COMB (@lem7210709) (@lem7210677 _132349)). Qed.
Lemma lem7210845 {_132349 : Type'} : (term12 _132349) = (term28 _132349).
Proof. exact (TRANS (@lem7210599 _132349) (@lem7210710 _132349)). Qed.
Lemma lem7210846 {_132349 : Type'} : (term28 _132349) = (term12 _132349).
Proof. exact (SYM (@lem7210845 _132349)). Qed.
Lemma lem7210847 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7210848 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem7210850 {_132349 : Type'} (h1 : term49 _132349) : term49 _132349.
Proof. exact (h1). Qed.
Lemma lem7210851 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7210858 (m : nat) (i : nat) (n : nat) : (term76 m i n) = (term77 m i n).
Proof. exact (@lem17045 (Peano.le m i) (Peano.le i n)). Qed.
Lemma lem7210859 (f : nat -> real) (g : nat -> real) (i : nat) : ((f i) = (g i)) = ((f i) = (g i)).
Proof. exact (eq_refl ((f i) = (g i))). Qed.
Lemma lem7210860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7210861 (m : nat) (i : nat) (n : nat) : (term78 m i n) = (term79 m i n).
Proof. exact (MK_COMB (@lem7210860) (@lem7210858 m i n)). Qed.
Lemma lem7210862 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term80 m n f g i) = (term81 m n f g i).
Proof. exact (MK_COMB (@lem7210861 m i n) (@lem7210859 f g i)). Qed.
Lemma lem7210863 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term64 m n f g i) = (term80 m n f g i).
Proof. exact (@lem17265 (term56 m i n) ((f i) = (g i))). Qed.
Lemma lem7210864 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term64 m n f g i) = (term81 m n f g i).
Proof. exact (TRANS (@lem7210863 m n f g i) (@lem7210862 m n f g i)). Qed.
Lemma lem7210865 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term65 m n f g) = (term82 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7210864 m n f g i)). Qed.
Lemma lem7210866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210867 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term66 m n f g) = (term83 m n f g).
Proof. exact (MK_COMB (@lem7210866) (@lem7210865 m n f g)). Qed.
Lemma lem7210868 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term84 f m n g) = (term84 f m n g).
Proof. exact (eq_refl (term84 f m n g)). Qed.
Lemma lem7210869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7210870 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term85 m n f g) = (term86 m n f g).
Proof. exact (MK_COMB (@lem7210869) (@lem7210867 m n f g)). Qed.
Lemma lem7210871 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term87 f m n g) = (term88 f m n g).
Proof. exact (MK_COMB (@lem7210870 m n f g) (@lem7210868 f m n g)). Qed.
Lemma lem7210872 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term89 f m n g) = (term87 f m n g).
Proof. exact (@lem17362 (term66 m n f g) ((term63 m n f) = (term63 m n g))). Qed.
Lemma lem7210873 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term89 f m n g) = (term88 f m n g).
Proof. exact (TRANS (@lem7210872 f m n g) (@lem7210871 f m n g)). Qed.
Lemma lem7210874 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7210875 (f : nat -> real) (m : nat) (g : nat -> real) : (term92 f m g) = (term93 f m g).
Proof. exact (@lem7210874 (term69 f m g)). Qed.
Lemma lem7210876 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term94 f m g n) = (term68 f m n g).
Proof. exact (eq_refl (term94 f m g n)). Qed.
Lemma lem7210877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7210878 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term95 f m g n) = (term89 f m n g).
Proof. exact (MK_COMB (@lem7210877) (@lem7210876 f m n g)). Qed.
Lemma lem7210879 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term95 f m g n) = (term88 f m n g).
Proof. exact (TRANS (@lem7210878 f m n g) (@lem7210873 f m n g)). Qed.
Lemma lem7210880 (f : nat -> real) (m : nat) (g : nat -> real) : (term96 f m g) = (term97 f m g).
Proof. exact (fun_ext (fun n : nat => @lem7210879 f m n g)). Qed.
Lemma lem7210881 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7210882 (f : nat -> real) (m : nat) (g : nat -> real) : (term93 f m g) = (term98 f m g).
Proof. exact (MK_COMB (@lem7210881) (@lem7210880 f m g)). Qed.
Lemma lem7210883 (f : nat -> real) (m : nat) (g : nat -> real) : (term92 f m g) = (term98 f m g).
Proof. exact (TRANS (@lem7210875 f m g) (@lem7210882 f m g)). Qed.
Lemma lem7210884 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7210885 (f : nat -> real) (g : nat -> real) : (term99 f g) = (term100 f g).
Proof. exact (@lem7210884 (term71 f g)). Qed.
Lemma lem7210886 (f : nat -> real) (m : nat) (g : nat -> real) : (term101 f g m) = (term70 f m g).
Proof. exact (eq_refl (term101 f g m)). Qed.
Lemma lem7210887 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7210888 (f : nat -> real) (m : nat) (g : nat -> real) : (term102 f g m) = (term92 f m g).
Proof. exact (MK_COMB (@lem7210887) (@lem7210886 f m g)). Qed.
Lemma lem7210889 (f : nat -> real) (m : nat) (g : nat -> real) : (term102 f g m) = (term98 f m g).
Proof. exact (TRANS (@lem7210888 f m g) (@lem7210883 f m g)). Qed.
Lemma lem7210890 (f : nat -> real) (g : nat -> real) : (term103 f g) = (term104 f g).
Proof. exact (fun_ext (fun m : nat => @lem7210889 f m g)). Qed.
Lemma lem7210891 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7210892 (f : nat -> real) (g : nat -> real) : (term100 f g) = (term105 f g).
Proof. exact (MK_COMB (@lem7210891) (@lem7210890 f g)). Qed.
Lemma lem7210893 (f : nat -> real) (g : nat -> real) : (term99 f g) = (term105 f g).
Proof. exact (TRANS (@lem7210885 f g) (@lem7210892 f g)). Qed.
Lemma lem7210894 (P : type1010) : (term106 P) = (term107 P).
Proof. exact (@lem18392 (nat -> real) P). Qed.
Lemma lem7210895 (f : nat -> real) : (term108 f) = (term109 f).
Proof. exact (@lem7210894 (term73 f)). Qed.
Lemma lem7210896 (f : nat -> real) (g : nat -> real) : (term110 f g) = (term72 f g).
Proof. exact (eq_refl (term110 f g)). Qed.
Lemma lem7210897 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7210898 (f : nat -> real) (g : nat -> real) : (term111 f g) = (term99 f g).
Proof. exact (MK_COMB (@lem7210897) (@lem7210896 f g)). Qed.
Lemma lem7210899 (f : nat -> real) (g : nat -> real) : (term111 f g) = (term105 f g).
Proof. exact (TRANS (@lem7210898 f g) (@lem7210893 f g)). Qed.
Lemma lem7210900 (f : nat -> real) : (term112 f) = (term113 f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7210899 f g)). Qed.
Lemma lem7210901 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7210902 (f : nat -> real) : (term109 f) = (term114 f).
Proof. exact (MK_COMB (@lem7210901) (@lem7210900 f)). Qed.
Lemma lem7210903 (f : nat -> real) : (term108 f) = (term114 f).
Proof. exact (TRANS (@lem7210895 f) (@lem7210902 f)). Qed.
Lemma lem7210904 (P : type1010) : (term106 P) = (term107 P).
Proof. exact (@lem18392 (nat -> real) P). Qed.
Lemma lem7210905 : term10 = term115.
Proof. exact (@lem7210904 term75). Qed.
Lemma lem7210906 (f : nat -> real) : (term116 f) = (term74 f).
Proof. exact (eq_refl (term116 f)). Qed.
Lemma lem7210907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7210908 (f : nat -> real) : (term117 f) = (term108 f).
Proof. exact (MK_COMB (@lem7210907) (@lem7210906 f)). Qed.
Lemma lem7210909 (f : nat -> real) : (term117 f) = (term114 f).
Proof. exact (TRANS (@lem7210908 f) (@lem7210903 f)). Qed.
Lemma lem7210910 : term118 = term119.
Proof. exact (fun_ext (fun f : nat -> real => @lem7210909 f)). Qed.
Lemma lem7210911 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7210912 : term115 = term120.
Proof. exact (MK_COMB (@lem7210911) (@lem7210910)). Qed.
Lemma lem7211025 : term10 = term120.
Proof. exact (TRANS (@lem7210905) (@lem7210912)). Qed.
Lemma lem7211026 (h1 : term10) : term120.
Proof. exact (EQ_MP (@lem7211025) (@lem7210847 h1)). Qed.
Lemma lem7211037 (m : nat) (p : nat) (n : nat) : (term76 m p n) = (term77 m p n).
Proof. exact (@lem17045 (Peano.le m p) (Peano.le p n)). Qed.
Lemma lem7211043 (m : nat) (p : nat) (n : nat) : (term121 m p n) = (term121 m p n).
Proof. exact (eq_refl (term121 m p n)). Qed.
Lemma lem7211045 (p : nat) (m : nat) (n : nat) : (term122 p m n) = (term122 p m n).
Proof. exact (eq_refl (term122 p m n)). Qed.
Lemma lem7211046 (m : nat) (p : nat) (n : nat) : (term123 m p n) = (term124 m p n).
Proof. exact (MK_COMB (@lem7211045 p m n) (@lem7211037 m p n)). Qed.
Lemma lem7211047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211048 (m : nat) (p : nat) (n : nat) : (term125 m p n) = (term126 m p n).
Proof. exact (MK_COMB (@lem7211047) (@lem7211046 m p n)). Qed.
Lemma lem7211049 (m : nat) (p : nat) (n : nat) : (term127 m p n) = (term128 m p n).
Proof. exact (MK_COMB (@lem7211048 m p n) (@lem7211043 m p n)). Qed.
Lemma lem7211050 (m : nat) (p : nat) (n : nat) : ((term55 p m n) = (term56 m p n)) = (term127 m p n).
Proof. exact (@lem17784 (term55 p m n) (term56 m p n)). Qed.
Lemma lem7211051 (m : nat) (p : nat) (n : nat) : ((term55 p m n) = (term56 m p n)) = (term128 m p n).
Proof. exact (TRANS (@lem7211050 m p n) (@lem7211049 m p n)). Qed.
Lemma lem7211052 (m : nat) (n : nat) : (term57 m n) = (term129 m n).
Proof. exact (fun_ext (fun p : nat => @lem7211051 m p n)). Qed.
Lemma lem7211053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211054 (m : nat) (n : nat) : (term58 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem7211053) (@lem7211052 m n)). Qed.
Lemma lem7211055 (m : nat) : (term59 m) = (term131 m).
Proof. exact (fun_ext (fun n : nat => @lem7211054 m n)). Qed.
Lemma lem7211056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211057 (m : nat) : (term60 m) = (term132 m).
Proof. exact (MK_COMB (@lem7211056) (@lem7211055 m)). Qed.
Lemma lem7211058 : term61 = term133.
Proof. exact (fun_ext (fun m : nat => @lem7211057 m)). Qed.
Lemma lem7211059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211060 : term62 = term134.
Proof. exact (MK_COMB (@lem7211059) (@lem7211058)). Qed.
Lemma lem7211070 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7211071 (P : nat -> Prop) (Q : nat -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7211070 nat P Q). Qed.
Lemma lem7211072 (m : nat) (n : nat) : (term139 m n) = (term140 m n).
Proof. exact (@lem7211071 (term141 m n) (term142 m n)). Qed.
Lemma lem7211073 (m : nat) (p : nat) (n : nat) : (term143 m n p) = (term124 m p n).
Proof. exact (eq_refl (term143 m n p)). Qed.
Lemma lem7211074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211075 (m : nat) (p : nat) (n : nat) : (term144 m n p) = (term126 m p n).
Proof. exact (MK_COMB (@lem7211074) (@lem7211073 m p n)). Qed.
Lemma lem7211076 (m : nat) (p : nat) (n : nat) : (term145 m n p) = (term121 m p n).
Proof. exact (eq_refl (term145 m n p)). Qed.
Lemma lem7211077 (m : nat) (p : nat) (n : nat) : (term146 m n p) = (term128 m p n).
Proof. exact (MK_COMB (@lem7211075 m p n) (@lem7211076 m p n)). Qed.
Lemma lem7211078 (m : nat) (n : nat) : (term147 m n) = (term129 m n).
Proof. exact (fun_ext (fun p : nat => @lem7211077 m p n)). Qed.
Lemma lem7211079 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211080 (m : nat) (n : nat) : (term139 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem7211079) (@lem7211078 m n)). Qed.
Lemma lem7211081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211082 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (MK_COMB (@lem7211081) (@lem7211080 m n)). Qed.
Lemma lem7211083 (m : nat) (p : nat) (n : nat) : (term143 m n p) = (term124 m p n).
Proof. exact (eq_refl (term143 m n p)). Qed.
Lemma lem7211084 (m : nat) (n : nat) : (term150 m n) = (term141 m n).
Proof. exact (fun_ext (fun p : nat => @lem7211083 m p n)). Qed.
Lemma lem7211085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211086 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (MK_COMB (@lem7211085) (@lem7211084 m n)). Qed.
Lemma lem7211087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211088 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem7211087) (@lem7211086 m n)). Qed.
Lemma lem7211089 (m : nat) (p : nat) (n : nat) : (term145 m n p) = (term121 m p n).
Proof. exact (eq_refl (term145 m n p)). Qed.
Lemma lem7211090 (m : nat) (n : nat) : (term155 m n) = (term142 m n).
Proof. exact (fun_ext (fun p : nat => @lem7211089 m p n)). Qed.
Lemma lem7211091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211092 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem7211091) (@lem7211090 m n)). Qed.
Lemma lem7211093 (m : nat) (n : nat) : (term140 m n) = (term158 m n).
Proof. exact (MK_COMB (@lem7211088 m n) (@lem7211092 m n)). Qed.
Lemma lem7211094 (m : nat) (n : nat) : ((term139 m n) = (term140 m n)) = ((term130 m n) = (term158 m n)).
Proof. exact (MK_COMB (@lem7211082 m n) (@lem7211093 m n)). Qed.
Lemma lem7211095 (m : nat) (n : nat) : (term130 m n) = (term158 m n).
Proof. exact (EQ_MP (@lem7211094 m n) (@lem7211072 m n)). Qed.
Lemma lem7211192 (m : nat) : (term131 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem7211095 m n)). Qed.
Lemma lem7211193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211194 (m : nat) : (term132 m) = (term160 m).
Proof. exact (MK_COMB (@lem7211193) (@lem7211192 m)). Qed.
Lemma lem7211196 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7211197 (P : nat -> Prop) (Q : nat -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7211196 nat P Q). Qed.
Lemma lem7211198 (m : nat) : (term161 m) = (term162 m).
Proof. exact (@lem7211197 (term163 m) (term164 m)). Qed.
Lemma lem7211199 (m : nat) (n : nat) : (term165 m n) = (term152 m n).
Proof. exact (eq_refl (term165 m n)). Qed.
Lemma lem7211200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211201 (m : nat) (n : nat) : (term166 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem7211200) (@lem7211199 m n)). Qed.
Lemma lem7211202 (m : nat) (n : nat) : (term167 m n) = (term157 m n).
Proof. exact (eq_refl (term167 m n)). Qed.
Lemma lem7211203 (m : nat) (n : nat) : (term168 m n) = (term158 m n).
Proof. exact (MK_COMB (@lem7211201 m n) (@lem7211202 m n)). Qed.
Lemma lem7211204 (m : nat) : (term169 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem7211203 m n)). Qed.
Lemma lem7211205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211206 (m : nat) : (term161 m) = (term160 m).
Proof. exact (MK_COMB (@lem7211205) (@lem7211204 m)). Qed.
Lemma lem7211207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211208 (m : nat) : (term170 m) = (term171 m).
Proof. exact (MK_COMB (@lem7211207) (@lem7211206 m)). Qed.
Lemma lem7211209 (m : nat) (n : nat) : (term165 m n) = (term152 m n).
Proof. exact (eq_refl (term165 m n)). Qed.
Lemma lem7211210 (m : nat) : (term172 m) = (term163 m).
Proof. exact (fun_ext (fun n : nat => @lem7211209 m n)). Qed.
Lemma lem7211211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211212 (m : nat) : (term173 m) = (term174 m).
Proof. exact (MK_COMB (@lem7211211) (@lem7211210 m)). Qed.
Lemma lem7211213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211214 (m : nat) : (term175 m) = (term176 m).
Proof. exact (MK_COMB (@lem7211213) (@lem7211212 m)). Qed.
Lemma lem7211215 (m : nat) (n : nat) : (term167 m n) = (term157 m n).
Proof. exact (eq_refl (term167 m n)). Qed.
Lemma lem7211216 (m : nat) : (term177 m) = (term164 m).
Proof. exact (fun_ext (fun n : nat => @lem7211215 m n)). Qed.
Lemma lem7211217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211218 (m : nat) : (term178 m) = (term179 m).
Proof. exact (MK_COMB (@lem7211217) (@lem7211216 m)). Qed.
Lemma lem7211219 (m : nat) : (term162 m) = (term180 m).
Proof. exact (MK_COMB (@lem7211214 m) (@lem7211218 m)). Qed.
Lemma lem7211220 (m : nat) : ((term161 m) = (term162 m)) = ((term160 m) = (term180 m)).
Proof. exact (MK_COMB (@lem7211208 m) (@lem7211219 m)). Qed.
Lemma lem7211221 (m : nat) : (term160 m) = (term180 m).
Proof. exact (EQ_MP (@lem7211220 m) (@lem7211198 m)). Qed.
Lemma lem7211326 (m : nat) : (term132 m) = (term180 m).
Proof. exact (TRANS (@lem7211194 m) (@lem7211221 m)). Qed.
Lemma lem7211327 : term133 = term181.
Proof. exact (fun_ext (fun m : nat => @lem7211326 m)). Qed.
Lemma lem7211328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211329 : term134 = term182.
Proof. exact (MK_COMB (@lem7211328) (@lem7211327)). Qed.
Lemma lem7211331 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7211332 (P : nat -> Prop) (Q : nat -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7211331 nat P Q). Qed.
Lemma lem7211333 : term183 = term184.
Proof. exact (@lem7211332 term185 term186). Qed.
Lemma lem7211334 (m : nat) : (term187 m) = (term174 m).
Proof. exact (eq_refl (term187 m)). Qed.
Lemma lem7211335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211336 (m : nat) : (term188 m) = (term176 m).
Proof. exact (MK_COMB (@lem7211335) (@lem7211334 m)). Qed.
Lemma lem7211337 (m : nat) : (term189 m) = (term179 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem7211338 (m : nat) : (term190 m) = (term180 m).
Proof. exact (MK_COMB (@lem7211336 m) (@lem7211337 m)). Qed.
Lemma lem7211339 : term191 = term181.
Proof. exact (fun_ext (fun m : nat => @lem7211338 m)). Qed.
Lemma lem7211340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211341 : term183 = term182.
Proof. exact (MK_COMB (@lem7211340) (@lem7211339)). Qed.
Lemma lem7211342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211343 : term192 = term193.
Proof. exact (MK_COMB (@lem7211342) (@lem7211341)). Qed.
Lemma lem7211344 (m : nat) : (term187 m) = (term174 m).
Proof. exact (eq_refl (term187 m)). Qed.
Lemma lem7211345 : term194 = term185.
Proof. exact (fun_ext (fun m : nat => @lem7211344 m)). Qed.
Lemma lem7211346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211347 : term195 = term196.
Proof. exact (MK_COMB (@lem7211346) (@lem7211345)). Qed.
Lemma lem7211348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7211349 : term197 = term198.
Proof. exact (MK_COMB (@lem7211348) (@lem7211347)). Qed.
Lemma lem7211350 (m : nat) : (term189 m) = (term179 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem7211351 : term199 = term186.
Proof. exact (fun_ext (fun m : nat => @lem7211350 m)). Qed.
Lemma lem7211352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7211353 : term200 = term201.
Proof. exact (MK_COMB (@lem7211352) (@lem7211351)). Qed.
Lemma lem7211354 : term184 = term202.
Proof. exact (MK_COMB (@lem7211349) (@lem7211353)). Qed.
Lemma lem7211355 : (term183 = term184) = (term182 = term202).
Proof. exact (MK_COMB (@lem7211343) (@lem7211354)). Qed.
Lemma lem7211356 : term182 = term202.
Proof. exact (EQ_MP (@lem7211355) (@lem7211333)). Qed.
Lemma lem7211471 : term134 = term202.
Proof. exact (TRANS (@lem7211329) (@lem7211356)). Qed.
Lemma lem7211472 : term62 = term202.
Proof. exact (TRANS (@lem7211060) (@lem7211471)). Qed.
Lemma lem7211473 (h1 : term62) : term202.
Proof. exact (EQ_MP (@lem7211472) (@lem7210848 h1)). Qed.
Lemma lem7211500 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term203 _132349 s f g x) = (term204 _132349 s f g x).
Proof. exact (@lem17362 (@IN _132349 x s) ((f x) = (g x))). Qed.
Lemma lem7211501 {_132349 : Type'} (P : _132349 -> Prop) : (term205 _132349 P) = (term206 _132349 P).
Proof. exact (@lem18392 _132349 P). Qed.
Lemma lem7211502 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term207 _132349 s f g) = (term208 _132349 s f g).
Proof. exact (@lem7211501 _132349 (term40 _132349 s f g)). Qed.
Lemma lem7211503 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term209 _132349 s f g x) = (term39 _132349 s f g x).
Proof. exact (eq_refl (term209 _132349 s f g x)). Qed.
Lemma lem7211504 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7211505 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term210 _132349 s f g x) = (term203 _132349 s f g x).
Proof. exact (MK_COMB (@lem7211504) (@lem7211503 _132349 s f g x)). Qed.
Lemma lem7211506 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term210 _132349 s f g x) = (term204 _132349 s f g x).
Proof. exact (TRANS (@lem7211505 _132349 s f g x) (@lem7211500 _132349 s f g x)). Qed.
Lemma lem7211507 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term211 _132349 s f g) = (term212 _132349 s f g).
Proof. exact (fun_ext (fun x : _132349 => @lem7211506 _132349 s f g x)). Qed.
Lemma lem7211508 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7211509 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term208 _132349 s f g) = (term213 _132349 s f g).
Proof. exact (MK_COMB (@lem7211508 _132349) (@lem7211507 _132349 s f g)). Qed.
Lemma lem7211510 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term207 _132349 s f g) = (term213 _132349 s f g).
Proof. exact (TRANS (@lem7211502 _132349 s f g) (@lem7211509 _132349 s f g)). Qed.
Lemma lem7211511 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7211512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7211513 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term214 _132349 s f g) = (term215 _132349 s f g).
Proof. exact (MK_COMB (@lem7211512) (@lem7211510 _132349 s f g)). Qed.
Lemma lem7211514 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term216 _132349 f s g) = (term217 _132349 f s g).
Proof. exact (MK_COMB (@lem7211513 _132349 s f g) (@lem7211511 _132349 f s g)). Qed.
Lemma lem7211515 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term43 _132349 f s g) = (term216 _132349 f s g).
Proof. exact (@lem17265 (term41 _132349 s f g) ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7211516 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term43 _132349 f s g) = (term217 _132349 f s g).
Proof. exact (TRANS (@lem7211515 _132349 f s g) (@lem7211514 _132349 f s g)). Qed.
Lemma lem7211517 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term44 _132349 f g) = (term218 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7211516 _132349 f s g)). Qed.
Lemma lem7211518 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7211519 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term45 _132349 f g) = (term219 _132349 f g).
Proof. exact (MK_COMB (@lem7211518 _132349) (@lem7211517 _132349 f g)). Qed.
Lemma lem7211520 {_132349 : Type'} (f : _132349 -> real) : (term46 _132349 f) = (term220 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7211519 _132349 f g)). Qed.
Lemma lem7211521 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211522 {_132349 : Type'} (f : _132349 -> real) : (term47 _132349 f) = (term221 _132349 f).
Proof. exact (MK_COMB (@lem7211521 _132349) (@lem7211520 _132349 f)). Qed.
Lemma lem7211523 {_132349 : Type'} : (term48 _132349) = (term222 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7211522 _132349 f)). Qed.
Lemma lem7211524 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211525 {_132349 : Type'} : (term49 _132349) = (term223 _132349).
Proof. exact (MK_COMB (@lem7211524 _132349) (@lem7211523 _132349)). Qed.
Lemma lem7211632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7211633 {_132349 : Type'} (P : _132349 -> Prop) (Q : Prop) : (term224 _132349 P Q) = (term225 _132349 P Q).
Proof. exact (@lem7211632 _132349 P Q). Qed.
Lemma lem7211634 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term226 _132349 f s g) = (term227 _132349 f s g).
Proof. exact (@lem7211633 _132349 (term212 _132349 s f g) ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7211635 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term228 _132349 s f g x) = (term204 _132349 s f g x).
Proof. exact (eq_refl (term228 _132349 s f g x)). Qed.
Lemma lem7211636 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term229 _132349 s f g) = (term212 _132349 s f g).
Proof. exact (fun_ext (fun x : _132349 => @lem7211635 _132349 s f g x)). Qed.
Lemma lem7211637 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7211638 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term230 _132349 s f g) = (term213 _132349 s f g).
Proof. exact (MK_COMB (@lem7211637 _132349) (@lem7211636 _132349 s f g)). Qed.
Lemma lem7211639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7211640 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term231 _132349 s f g) = (term215 _132349 s f g).
Proof. exact (MK_COMB (@lem7211639) (@lem7211638 _132349 s f g)). Qed.
Lemma lem7211641 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7211642 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term226 _132349 f s g) = (term217 _132349 f s g).
Proof. exact (MK_COMB (@lem7211640 _132349 s f g) (@lem7211641 _132349 f s g)). Qed.
Lemma lem7211643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211644 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term232 _132349 f s g) = (term233 _132349 f s g).
Proof. exact (MK_COMB (@lem7211643) (@lem7211642 _132349 f s g)). Qed.
Lemma lem7211645 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term228 _132349 s f g x) = (term204 _132349 s f g x).
Proof. exact (eq_refl (term228 _132349 s f g x)). Qed.
Lemma lem7211646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7211647 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term234 _132349 s f g x) = (term235 _132349 s f g x).
Proof. exact (MK_COMB (@lem7211646) (@lem7211645 _132349 s f g x)). Qed.
Lemma lem7211648 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7211649 {_132349 : Type'} (x : _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term236 _132349 x f s g) = (term237 _132349 x f s g).
Proof. exact (MK_COMB (@lem7211647 _132349 s f g x) (@lem7211648 _132349 f s g)). Qed.
Lemma lem7211650 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term238 _132349 f s g) = (term239 _132349 f s g).
Proof. exact (fun_ext (fun x : _132349 => @lem7211649 _132349 x f s g)). Qed.
Lemma lem7211651 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7211652 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term227 _132349 f s g) = (term240 _132349 f s g).
Proof. exact (MK_COMB (@lem7211651 _132349) (@lem7211650 _132349 f s g)). Qed.
Lemma lem7211653 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((term226 _132349 f s g) = (term227 _132349 f s g)) = ((term217 _132349 f s g) = (term240 _132349 f s g)).
Proof. exact (MK_COMB (@lem7211644 _132349 f s g) (@lem7211652 _132349 f s g)). Qed.
Lemma lem7211654 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term217 _132349 f s g) = (term240 _132349 f s g).
Proof. exact (EQ_MP (@lem7211653 _132349 f s g) (@lem7211634 _132349 f s g)). Qed.
Lemma lem7211655 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term218 _132349 f g) = (term241 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7211654 _132349 f s g)). Qed.
Lemma lem7211656 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7211657 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term219 _132349 f g) = (term242 _132349 f g).
Proof. exact (MK_COMB (@lem7211656 _132349) (@lem7211655 _132349 f g)). Qed.
Lemma lem7211659 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7211660 {_132349 : Type'} (P : type672 _132349) : (term245 _132349 P) = (term246 _132349 P).
Proof. exact (@lem7211659 (_132349 -> Prop) _132349 P). Qed.
Lemma lem7211661 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term247 _132349 f g) = (term248 _132349 f g).
Proof. exact (@lem7211660 _132349 (term249 _132349 f g)). Qed.
Lemma lem7211662 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term250 _132349 f g s) = (term239 _132349 f s g).
Proof. exact (eq_refl (term250 _132349 f g s)). Qed.
Lemma lem7211663 {_132349 : Type'} (x : _132349) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7211664 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (x : _132349) : (term251 _132349 f g s x) = (term252 _132349 f s g x).
Proof. exact (MK_COMB (@lem7211662 _132349 f s g) (@lem7211663 _132349 x)). Qed.
Lemma lem7211665 {_132349 : Type'} (x : _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term252 _132349 f s g x) = (term237 _132349 x f s g).
Proof. exact (eq_refl (term252 _132349 f s g x)). Qed.
Lemma lem7211666 {_132349 : Type'} (x : _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term251 _132349 f g s x) = (term237 _132349 x f s g).
Proof. exact (TRANS (@lem7211664 _132349 f s g x) (@lem7211665 _132349 x f s g)). Qed.
Lemma lem7211667 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term253 _132349 f g s) = (term239 _132349 f s g).
Proof. exact (fun_ext (fun x : _132349 => @lem7211666 _132349 x f s g)). Qed.
Lemma lem7211668 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7211669 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term254 _132349 f g s) = (term240 _132349 f s g).
Proof. exact (MK_COMB (@lem7211668 _132349) (@lem7211667 _132349 f s g)). Qed.
Lemma lem7211670 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term255 _132349 f g) = (term241 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7211669 _132349 f s g)). Qed.
Lemma lem7211671 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7211672 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term247 _132349 f g) = (term242 _132349 f g).
Proof. exact (MK_COMB (@lem7211671 _132349) (@lem7211670 _132349 f g)). Qed.
Lemma lem7211673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211674 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term256 _132349 f g) = (term257 _132349 f g).
Proof. exact (MK_COMB (@lem7211673) (@lem7211672 _132349 f g)). Qed.
Lemma lem7211675 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term250 _132349 f g s) = (term239 _132349 f s g).
Proof. exact (eq_refl (term250 _132349 f g s)). Qed.
Lemma lem7211676 {_132349 : Type'} (x : type684 _132349) (s : _132349 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7211677 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (x : type684 _132349) (s : _132349 -> Prop) : (term258 _132349 f g x s) = (term259 _132349 f g x s).
Proof. exact (MK_COMB (@lem7211675 _132349 f s g) (@lem7211676 _132349 x s)). Qed.
Lemma lem7211678 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term259 _132349 f g x s) = (term260 _132349 x f s g).
Proof. exact (eq_refl (term259 _132349 f g x s)). Qed.
Lemma lem7211679 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term258 _132349 f g x s) = (term260 _132349 x f s g).
Proof. exact (TRANS (@lem7211677 _132349 f g x s) (@lem7211678 _132349 x f s g)). Qed.
Lemma lem7211680 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term261 _132349 f g x) = (term262 _132349 x f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7211679 _132349 x f s g)). Qed.
Lemma lem7211681 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7211682 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term263 _132349 f g x) = (term264 _132349 x f g).
Proof. exact (MK_COMB (@lem7211681 _132349) (@lem7211680 _132349 x f g)). Qed.
Lemma lem7211683 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term265 _132349 f g) = (term266 _132349 f g).
Proof. exact (fun_ext (fun x : type684 _132349 => @lem7211682 _132349 x f g)). Qed.
Lemma lem7211684 {_132349 : Type'} : (@ex ((_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> Prop) -> _132349))). Qed.
Lemma lem7211685 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term248 _132349 f g) = (term267 _132349 f g).
Proof. exact (MK_COMB (@lem7211684 _132349) (@lem7211683 _132349 f g)). Qed.
Lemma lem7211686 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : ((term247 _132349 f g) = (term248 _132349 f g)) = ((term242 _132349 f g) = (term267 _132349 f g)).
Proof. exact (MK_COMB (@lem7211674 _132349 f g) (@lem7211685 _132349 f g)). Qed.
Lemma lem7211687 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term242 _132349 f g) = (term267 _132349 f g).
Proof. exact (EQ_MP (@lem7211686 _132349 f g) (@lem7211661 _132349 f g)). Qed.
Lemma lem7211688 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term219 _132349 f g) = (term267 _132349 f g).
Proof. exact (TRANS (@lem7211657 _132349 f g) (@lem7211687 _132349 f g)). Qed.
Lemma lem7211689 {_132349 : Type'} (f : _132349 -> real) : (term220 _132349 f) = (term268 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7211688 _132349 f g)). Qed.
Lemma lem7211690 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211691 {_132349 : Type'} (f : _132349 -> real) : (term221 _132349 f) = (term269 _132349 f).
Proof. exact (MK_COMB (@lem7211690 _132349) (@lem7211689 _132349 f)). Qed.
Lemma lem7211693 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7211694 {_132349 : Type'} (P : type707 _132349) : (term270 _132349 P) = (term271 _132349 P).
Proof. exact (@lem7211693 (_132349 -> real) (type684 _132349) P). Qed.
Lemma lem7211695 {_132349 : Type'} (f : _132349 -> real) : (term272 _132349 f) = (term273 _132349 f).
Proof. exact (@lem7211694 _132349 (term274 _132349 f)). Qed.
Lemma lem7211696 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term275 _132349 f g) = (term266 _132349 f g).
Proof. exact (eq_refl (term275 _132349 f g)). Qed.
Lemma lem7211697 {_132349 : Type'} (x : type684 _132349) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7211698 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (x : type684 _132349) : (term276 _132349 f g x) = (term277 _132349 f g x).
Proof. exact (MK_COMB (@lem7211696 _132349 f g) (@lem7211697 _132349 x)). Qed.
Lemma lem7211699 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term277 _132349 f g x) = (term264 _132349 x f g).
Proof. exact (eq_refl (term277 _132349 f g x)). Qed.
Lemma lem7211700 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term276 _132349 f g x) = (term264 _132349 x f g).
Proof. exact (TRANS (@lem7211698 _132349 f g x) (@lem7211699 _132349 x f g)). Qed.
Lemma lem7211701 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term278 _132349 f g) = (term266 _132349 f g).
Proof. exact (fun_ext (fun x : type684 _132349 => @lem7211700 _132349 x f g)). Qed.
Lemma lem7211702 {_132349 : Type'} : (@ex ((_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> Prop) -> _132349))). Qed.
Lemma lem7211703 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term279 _132349 f g) = (term267 _132349 f g).
Proof. exact (MK_COMB (@lem7211702 _132349) (@lem7211701 _132349 f g)). Qed.
Lemma lem7211704 {_132349 : Type'} (f : _132349 -> real) : (term280 _132349 f) = (term268 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7211703 _132349 f g)). Qed.
Lemma lem7211705 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211706 {_132349 : Type'} (f : _132349 -> real) : (term272 _132349 f) = (term269 _132349 f).
Proof. exact (MK_COMB (@lem7211705 _132349) (@lem7211704 _132349 f)). Qed.
Lemma lem7211707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211708 {_132349 : Type'} (f : _132349 -> real) : (term281 _132349 f) = (term282 _132349 f).
Proof. exact (MK_COMB (@lem7211707) (@lem7211706 _132349 f)). Qed.
Lemma lem7211709 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term275 _132349 f g) = (term266 _132349 f g).
Proof. exact (eq_refl (term275 _132349 f g)). Qed.
Lemma lem7211710 {_132349 : Type'} (x : type710 _132349) (g : _132349 -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7211711 {_132349 : Type'} (f : _132349 -> real) (x : type710 _132349) (g : _132349 -> real) : (term283 _132349 f x g) = (term284 _132349 f x g).
Proof. exact (MK_COMB (@lem7211709 _132349 f g) (@lem7211710 _132349 x g)). Qed.
Lemma lem7211712 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term284 _132349 f x g) = (term285 _132349 x f g).
Proof. exact (eq_refl (term284 _132349 f x g)). Qed.
Lemma lem7211713 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term283 _132349 f x g) = (term285 _132349 x f g).
Proof. exact (TRANS (@lem7211711 _132349 f x g) (@lem7211712 _132349 x f g)). Qed.
Lemma lem7211714 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term286 _132349 f x) = (term287 _132349 x f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7211713 _132349 x f g)). Qed.
Lemma lem7211715 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211716 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term288 _132349 f x) = (term289 _132349 x f).
Proof. exact (MK_COMB (@lem7211715 _132349) (@lem7211714 _132349 x f)). Qed.
Lemma lem7211717 {_132349 : Type'} (f : _132349 -> real) : (term290 _132349 f) = (term291 _132349 f).
Proof. exact (fun_ext (fun x : type710 _132349 => @lem7211716 _132349 x f)). Qed.
Lemma lem7211718 {_132349 : Type'} : (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349))). Qed.
Lemma lem7211719 {_132349 : Type'} (f : _132349 -> real) : (term273 _132349 f) = (term292 _132349 f).
Proof. exact (MK_COMB (@lem7211718 _132349) (@lem7211717 _132349 f)). Qed.
Lemma lem7211720 {_132349 : Type'} (f : _132349 -> real) : ((term272 _132349 f) = (term273 _132349 f)) = ((term269 _132349 f) = (term292 _132349 f)).
Proof. exact (MK_COMB (@lem7211708 _132349 f) (@lem7211719 _132349 f)). Qed.
Lemma lem7211721 {_132349 : Type'} (f : _132349 -> real) : (term269 _132349 f) = (term292 _132349 f).
Proof. exact (EQ_MP (@lem7211720 _132349 f) (@lem7211695 _132349 f)). Qed.
Lemma lem7211722 {_132349 : Type'} (f : _132349 -> real) : (term221 _132349 f) = (term292 _132349 f).
Proof. exact (TRANS (@lem7211691 _132349 f) (@lem7211721 _132349 f)). Qed.
Lemma lem7211723 {_132349 : Type'} : (term222 _132349) = (term293 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7211722 _132349 f)). Qed.
Lemma lem7211724 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211725 {_132349 : Type'} : (term223 _132349) = (term294 _132349).
Proof. exact (MK_COMB (@lem7211724 _132349) (@lem7211723 _132349)). Qed.
Lemma lem7211727 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7211728 {_132349 : Type'} (P : type708 _132349) : (term295 _132349 P) = (term296 _132349 P).
Proof. exact (@lem7211727 (_132349 -> real) (type710 _132349) P). Qed.
Lemma lem7211729 {_132349 : Type'} : (term297 _132349) = (term298 _132349).
Proof. exact (@lem7211728 _132349 (term299 _132349)). Qed.
Lemma lem7211730 {_132349 : Type'} (f : _132349 -> real) : (term300 _132349 f) = (term291 _132349 f).
Proof. exact (eq_refl (term300 _132349 f)). Qed.
Lemma lem7211731 {_132349 : Type'} (x : type710 _132349) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7211732 {_132349 : Type'} (f : _132349 -> real) (x : type710 _132349) : (term301 _132349 f x) = (term302 _132349 f x).
Proof. exact (MK_COMB (@lem7211730 _132349 f) (@lem7211731 _132349 x)). Qed.
Lemma lem7211733 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term302 _132349 f x) = (term289 _132349 x f).
Proof. exact (eq_refl (term302 _132349 f x)). Qed.
Lemma lem7211734 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term301 _132349 f x) = (term289 _132349 x f).
Proof. exact (TRANS (@lem7211732 _132349 f x) (@lem7211733 _132349 x f)). Qed.
Lemma lem7211735 {_132349 : Type'} (f : _132349 -> real) : (term303 _132349 f) = (term291 _132349 f).
Proof. exact (fun_ext (fun x : type710 _132349 => @lem7211734 _132349 x f)). Qed.
Lemma lem7211736 {_132349 : Type'} : (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349))). Qed.
Lemma lem7211737 {_132349 : Type'} (f : _132349 -> real) : (term304 _132349 f) = (term292 _132349 f).
Proof. exact (MK_COMB (@lem7211736 _132349) (@lem7211735 _132349 f)). Qed.
Lemma lem7211738 {_132349 : Type'} : (term305 _132349) = (term293 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7211737 _132349 f)). Qed.
Lemma lem7211739 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211740 {_132349 : Type'} : (term297 _132349) = (term294 _132349).
Proof. exact (MK_COMB (@lem7211739 _132349) (@lem7211738 _132349)). Qed.
Lemma lem7211741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211742 {_132349 : Type'} : (term306 _132349) = (term307 _132349).
Proof. exact (MK_COMB (@lem7211741) (@lem7211740 _132349)). Qed.
Lemma lem7211743 {_132349 : Type'} (f : _132349 -> real) : (term300 _132349 f) = (term291 _132349 f).
Proof. exact (eq_refl (term300 _132349 f)). Qed.
Lemma lem7211744 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7211745 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (term308 _132349 x f) = (term309 _132349 x f).
Proof. exact (MK_COMB (@lem7211743 _132349 f) (@lem7211744 _132349 x f)). Qed.
Lemma lem7211746 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (term309 _132349 x f) = (term310 _132349 x f).
Proof. exact (eq_refl (term309 _132349 x f)). Qed.
Lemma lem7211747 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (term308 _132349 x f) = (term310 _132349 x f).
Proof. exact (TRANS (@lem7211745 _132349 x f) (@lem7211746 _132349 x f)). Qed.
Lemma lem7211748 {_132349 : Type'} (x : type711 _132349) : (term311 _132349 x) = (term312 _132349 x).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7211747 _132349 x f)). Qed.
Lemma lem7211749 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7211750 {_132349 : Type'} (x : type711 _132349) : (term313 _132349 x) = (term314 _132349 x).
Proof. exact (MK_COMB (@lem7211749 _132349) (@lem7211748 _132349 x)). Qed.
Lemma lem7211751 {_132349 : Type'} : (term315 _132349) = (term316 _132349).
Proof. exact (fun_ext (fun x : type711 _132349 => @lem7211750 _132349 x)). Qed.
Lemma lem7211752 {_132349 : Type'} : (@ex ((_132349 -> real) -> (_132349 -> real) -> (_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> real) -> (_132349 -> real) -> (_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> real) -> (_132349 -> real) -> (_132349 -> Prop) -> _132349))). Qed.
Lemma lem7211753 {_132349 : Type'} : (term298 _132349) = (term317 _132349).
Proof. exact (MK_COMB (@lem7211752 _132349) (@lem7211751 _132349)). Qed.
Lemma lem7211754 {_132349 : Type'} : ((term297 _132349) = (term298 _132349)) = ((term294 _132349) = (term317 _132349)).
Proof. exact (MK_COMB (@lem7211742 _132349) (@lem7211753 _132349)). Qed.
Lemma lem7211755 {_132349 : Type'} : (term294 _132349) = (term317 _132349).
Proof. exact (EQ_MP (@lem7211754 _132349) (@lem7211729 _132349)). Qed.
Lemma lem7211757 {_132349 : Type'} : (term223 _132349) = (term317 _132349).
Proof. exact (TRANS (@lem7211725 _132349) (@lem7211755 _132349)). Qed.
Lemma lem7211758 {_132349 : Type'} : (term49 _132349) = (term317 _132349).
Proof. exact (TRANS (@lem7211525 _132349) (@lem7211757 _132349)). Qed.
Lemma lem7211759 {_132349 : Type'} (h1 : term49 _132349) : term317 _132349.
Proof. exact (EQ_MP (@lem7211758 _132349) (@lem7210850 _132349 h1)). Qed.
Lemma lem7211766 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term318 s f g x) = (term319 s f g x).
Proof. exact (@lem17362 (@IN nat x s) ((f x) = (g x))). Qed.
Lemma lem7211767 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7211768 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term320 s f g) = (term321 s f g).
Proof. exact (@lem7211767 (term30 s f g)). Qed.
Lemma lem7211769 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term322 s f g x) = (term29 s f g x).
Proof. exact (eq_refl (term322 s f g x)). Qed.
Lemma lem7211770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7211771 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term323 s f g x) = (term318 s f g x).
Proof. exact (MK_COMB (@lem7211770) (@lem7211769 s f g x)). Qed.
Lemma lem7211772 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term323 s f g x) = (term319 s f g x).
Proof. exact (TRANS (@lem7211771 s f g x) (@lem7211766 s f g x)). Qed.
Lemma lem7211773 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term324 s f g) = (term325 s f g).
Proof. exact (fun_ext (fun x : nat => @lem7211772 s f g x)). Qed.
Lemma lem7211774 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7211775 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term321 s f g) = (term326 s f g).
Proof. exact (MK_COMB (@lem7211774) (@lem7211773 s f g)). Qed.
Lemma lem7211776 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term320 s f g) = (term326 s f g).
Proof. exact (TRANS (@lem7211768 s f g) (@lem7211775 s f g)). Qed.
Lemma lem7211777 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : ((@sum nat s f) = (@sum nat s g)) = ((@sum nat s f) = (@sum nat s g)).
Proof. exact (eq_refl ((@sum nat s f) = (@sum nat s g))). Qed.
Lemma lem7211778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7211779 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term327 s f g) = (term328 s f g).
Proof. exact (MK_COMB (@lem7211778) (@lem7211776 s f g)). Qed.
Lemma lem7211780 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term329 f s g) = (term330 f s g).
Proof. exact (MK_COMB (@lem7211779 s f g) (@lem7211777 f s g)). Qed.
Lemma lem7211781 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term33 f s g) = (term329 f s g).
Proof. exact (@lem17265 (term31 s f g) ((@sum nat s f) = (@sum nat s g))). Qed.
Lemma lem7211782 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term33 f s g) = (term330 f s g).
Proof. exact (TRANS (@lem7211781 f s g) (@lem7211780 f s g)). Qed.
Lemma lem7211783 (f : nat -> real) (g : nat -> real) : (term34 f g) = (term331 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7211782 f s g)). Qed.
Lemma lem7211784 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7211785 (f : nat -> real) (g : nat -> real) : (term35 f g) = (term332 f g).
Proof. exact (MK_COMB (@lem7211784) (@lem7211783 f g)). Qed.
Lemma lem7211786 (f : nat -> real) : (term36 f) = (term333 f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7211785 f g)). Qed.
Lemma lem7211787 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7211788 (f : nat -> real) : (term37 f) = (term334 f).
Proof. exact (MK_COMB (@lem7211787) (@lem7211786 f)). Qed.
Lemma lem7211789 : term38 = term335.
Proof. exact (fun_ext (fun f : nat -> real => @lem7211788 f)). Qed.
Lemma lem7211790 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7211791 : term11 = term336.
Proof. exact (MK_COMB (@lem7211790) (@lem7211789)). Qed.
Lemma lem7211898 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7211899 (P : nat -> Prop) (Q : Prop) : (term337 P Q) = (term338 P Q).
Proof. exact (@lem7211898 nat P Q). Qed.
Lemma lem7211900 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term339 f s g) = (term340 f s g).
Proof. exact (@lem7211899 (term325 s f g) ((@sum nat s f) = (@sum nat s g))). Qed.
Lemma lem7211901 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term341 s f g x) = (term319 s f g x).
Proof. exact (eq_refl (term341 s f g x)). Qed.
Lemma lem7211902 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term342 s f g) = (term325 s f g).
Proof. exact (fun_ext (fun x : nat => @lem7211901 s f g x)). Qed.
Lemma lem7211903 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7211904 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term343 s f g) = (term326 s f g).
Proof. exact (MK_COMB (@lem7211903) (@lem7211902 s f g)). Qed.
Lemma lem7211905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7211906 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) : (term344 s f g) = (term328 s f g).
Proof. exact (MK_COMB (@lem7211905) (@lem7211904 s f g)). Qed.
Lemma lem7211907 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : ((@sum nat s f) = (@sum nat s g)) = ((@sum nat s f) = (@sum nat s g)).
Proof. exact (eq_refl ((@sum nat s f) = (@sum nat s g))). Qed.
Lemma lem7211908 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term339 f s g) = (term330 f s g).
Proof. exact (MK_COMB (@lem7211906 s f g) (@lem7211907 f s g)). Qed.
Lemma lem7211909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211910 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term345 f s g) = (term346 f s g).
Proof. exact (MK_COMB (@lem7211909) (@lem7211908 f s g)). Qed.
Lemma lem7211911 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term341 s f g x) = (term319 s f g x).
Proof. exact (eq_refl (term341 s f g x)). Qed.
Lemma lem7211912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7211913 (s : nat -> Prop) (f : nat -> real) (g : nat -> real) (x : nat) : (term347 s f g x) = (term348 s f g x).
Proof. exact (MK_COMB (@lem7211912) (@lem7211911 s f g x)). Qed.
Lemma lem7211914 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : ((@sum nat s f) = (@sum nat s g)) = ((@sum nat s f) = (@sum nat s g)).
Proof. exact (eq_refl ((@sum nat s f) = (@sum nat s g))). Qed.
Lemma lem7211915 (x : nat) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term349 x f s g) = (term350 x f s g).
Proof. exact (MK_COMB (@lem7211913 s f g x) (@lem7211914 f s g)). Qed.
Lemma lem7211916 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term351 f s g) = (term352 f s g).
Proof. exact (fun_ext (fun x : nat => @lem7211915 x f s g)). Qed.
Lemma lem7211917 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7211918 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term340 f s g) = (term353 f s g).
Proof. exact (MK_COMB (@lem7211917) (@lem7211916 f s g)). Qed.
Lemma lem7211919 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : ((term339 f s g) = (term340 f s g)) = ((term330 f s g) = (term353 f s g)).
Proof. exact (MK_COMB (@lem7211910 f s g) (@lem7211918 f s g)). Qed.
Lemma lem7211920 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term330 f s g) = (term353 f s g).
Proof. exact (EQ_MP (@lem7211919 f s g) (@lem7211900 f s g)). Qed.
Lemma lem7211921 (f : nat -> real) (g : nat -> real) : (term331 f g) = (term354 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7211920 f s g)). Qed.
Lemma lem7211922 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7211923 (f : nat -> real) (g : nat -> real) : (term332 f g) = (term355 f g).
Proof. exact (MK_COMB (@lem7211922) (@lem7211921 f g)). Qed.
Lemma lem7211925 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7211926 (P : type991) : (term356 P) = (term357 P).
Proof. exact (@lem7211925 (nat -> Prop) nat P). Qed.
Lemma lem7211927 (f : nat -> real) (g : nat -> real) : (term358 f g) = (term359 f g).
Proof. exact (@lem7211926 (term360 f g)). Qed.
Lemma lem7211928 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term361 f g s) = (term352 f s g).
Proof. exact (eq_refl (term361 f g s)). Qed.
Lemma lem7211929 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7211930 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) (x : nat) : (term362 f g s x) = (term363 f s g x).
Proof. exact (MK_COMB (@lem7211928 f s g) (@lem7211929 x)). Qed.
Lemma lem7211931 (x : nat) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term363 f s g x) = (term350 x f s g).
Proof. exact (eq_refl (term363 f s g x)). Qed.
Lemma lem7211932 (x : nat) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term362 f g s x) = (term350 x f s g).
Proof. exact (TRANS (@lem7211930 f s g x) (@lem7211931 x f s g)). Qed.
Lemma lem7211933 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term364 f g s) = (term352 f s g).
Proof. exact (fun_ext (fun x : nat => @lem7211932 x f s g)). Qed.
Lemma lem7211934 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7211935 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term365 f g s) = (term353 f s g).
Proof. exact (MK_COMB (@lem7211934) (@lem7211933 f s g)). Qed.
Lemma lem7211936 (f : nat -> real) (g : nat -> real) : (term366 f g) = (term354 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7211935 f s g)). Qed.
Lemma lem7211937 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7211938 (f : nat -> real) (g : nat -> real) : (term358 f g) = (term355 f g).
Proof. exact (MK_COMB (@lem7211937) (@lem7211936 f g)). Qed.
Lemma lem7211939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211940 (f : nat -> real) (g : nat -> real) : (term367 f g) = (term368 f g).
Proof. exact (MK_COMB (@lem7211939) (@lem7211938 f g)). Qed.
Lemma lem7211941 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term361 f g s) = (term352 f s g).
Proof. exact (eq_refl (term361 f g s)). Qed.
Lemma lem7211942 (x : type994) (s : nat -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7211943 (f : nat -> real) (g : nat -> real) (x : type994) (s : nat -> Prop) : (term369 f g x s) = (term370 f g x s).
Proof. exact (MK_COMB (@lem7211941 f s g) (@lem7211942 x s)). Qed.
Lemma lem7211944 (x : type994) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term370 f g x s) = (term371 x f s g).
Proof. exact (eq_refl (term370 f g x s)). Qed.
Lemma lem7211945 (x : type994) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term369 f g x s) = (term371 x f s g).
Proof. exact (TRANS (@lem7211943 f g x s) (@lem7211944 x f s g)). Qed.
Lemma lem7211946 (x : type994) (f : nat -> real) (g : nat -> real) : (term372 f g x) = (term373 x f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7211945 x f s g)). Qed.
Lemma lem7211947 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7211948 (x : type994) (f : nat -> real) (g : nat -> real) : (term374 f g x) = (term375 x f g).
Proof. exact (MK_COMB (@lem7211947) (@lem7211946 x f g)). Qed.
Lemma lem7211949 (f : nat -> real) (g : nat -> real) : (term376 f g) = (term377 f g).
Proof. exact (fun_ext (fun x : type994 => @lem7211948 x f g)). Qed.
Lemma lem7211950 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem7211951 (f : nat -> real) (g : nat -> real) : (term359 f g) = (term378 f g).
Proof. exact (MK_COMB (@lem7211950) (@lem7211949 f g)). Qed.
Lemma lem7211952 (f : nat -> real) (g : nat -> real) : ((term358 f g) = (term359 f g)) = ((term355 f g) = (term378 f g)).
Proof. exact (MK_COMB (@lem7211940 f g) (@lem7211951 f g)). Qed.
Lemma lem7211953 (f : nat -> real) (g : nat -> real) : (term355 f g) = (term378 f g).
Proof. exact (EQ_MP (@lem7211952 f g) (@lem7211927 f g)). Qed.
Lemma lem7211954 (f : nat -> real) (g : nat -> real) : (term332 f g) = (term378 f g).
Proof. exact (TRANS (@lem7211923 f g) (@lem7211953 f g)). Qed.
Lemma lem7211955 (f : nat -> real) : (term333 f) = (term379 f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7211954 f g)). Qed.
Lemma lem7211956 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7211957 (f : nat -> real) : (term334 f) = (term380 f).
Proof. exact (MK_COMB (@lem7211956) (@lem7211955 f)). Qed.
Lemma lem7211959 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7211960 (P : type1004) : (term381 P) = (term382 P).
Proof. exact (@lem7211959 (nat -> real) type994 P). Qed.
Lemma lem7211961 (f : nat -> real) : (term383 f) = (term384 f).
Proof. exact (@lem7211960 (term385 f)). Qed.
Lemma lem7211962 (f : nat -> real) (g : nat -> real) : (term386 f g) = (term377 f g).
Proof. exact (eq_refl (term386 f g)). Qed.
Lemma lem7211963 (x : type994) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7211964 (f : nat -> real) (g : nat -> real) (x : type994) : (term387 f g x) = (term388 f g x).
Proof. exact (MK_COMB (@lem7211962 f g) (@lem7211963 x)). Qed.
Lemma lem7211965 (x : type994) (f : nat -> real) (g : nat -> real) : (term388 f g x) = (term375 x f g).
Proof. exact (eq_refl (term388 f g x)). Qed.
Lemma lem7211966 (x : type994) (f : nat -> real) (g : nat -> real) : (term387 f g x) = (term375 x f g).
Proof. exact (TRANS (@lem7211964 f g x) (@lem7211965 x f g)). Qed.
Lemma lem7211967 (f : nat -> real) (g : nat -> real) : (term389 f g) = (term377 f g).
Proof. exact (fun_ext (fun x : type994 => @lem7211966 x f g)). Qed.
Lemma lem7211968 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem7211969 (f : nat -> real) (g : nat -> real) : (term390 f g) = (term378 f g).
Proof. exact (MK_COMB (@lem7211968) (@lem7211967 f g)). Qed.
Lemma lem7211970 (f : nat -> real) : (term391 f) = (term379 f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7211969 f g)). Qed.
Lemma lem7211971 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7211972 (f : nat -> real) : (term383 f) = (term380 f).
Proof. exact (MK_COMB (@lem7211971) (@lem7211970 f)). Qed.
Lemma lem7211973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7211974 (f : nat -> real) : (term392 f) = (term393 f).
Proof. exact (MK_COMB (@lem7211973) (@lem7211972 f)). Qed.
Lemma lem7211975 (f : nat -> real) (g : nat -> real) : (term386 f g) = (term377 f g).
Proof. exact (eq_refl (term386 f g)). Qed.
Lemma lem7211976 (x : type1007) (g : nat -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7211977 (f : nat -> real) (x : type1007) (g : nat -> real) : (term394 f x g) = (term395 f x g).
Proof. exact (MK_COMB (@lem7211975 f g) (@lem7211976 x g)). Qed.
Lemma lem7211978 (x : type1007) (f : nat -> real) (g : nat -> real) : (term395 f x g) = (term396 x f g).
Proof. exact (eq_refl (term395 f x g)). Qed.
Lemma lem7211979 (x : type1007) (f : nat -> real) (g : nat -> real) : (term394 f x g) = (term396 x f g).
Proof. exact (TRANS (@lem7211977 f x g) (@lem7211978 x f g)). Qed.
Lemma lem7211980 (x : type1007) (f : nat -> real) : (term397 f x) = (term398 x f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7211979 x f g)). Qed.
Lemma lem7211981 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7211982 (x : type1007) (f : nat -> real) : (term399 f x) = (term400 x f).
Proof. exact (MK_COMB (@lem7211981) (@lem7211980 x f)). Qed.
Lemma lem7211983 (f : nat -> real) : (term401 f) = (term402 f).
Proof. exact (fun_ext (fun x : type1007 => @lem7211982 x f)). Qed.
Lemma lem7211984 : (@ex ((nat -> real) -> (nat -> Prop) -> nat)) = (@ex ((nat -> real) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> real) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7211985 (f : nat -> real) : (term384 f) = (term403 f).
Proof. exact (MK_COMB (@lem7211984) (@lem7211983 f)). Qed.
Lemma lem7211986 (f : nat -> real) : ((term383 f) = (term384 f)) = ((term380 f) = (term403 f)).
Proof. exact (MK_COMB (@lem7211974 f) (@lem7211985 f)). Qed.
Lemma lem7211987 (f : nat -> real) : (term380 f) = (term403 f).
Proof. exact (EQ_MP (@lem7211986 f) (@lem7211961 f)). Qed.
Lemma lem7211988 (f : nat -> real) : (term334 f) = (term403 f).
Proof. exact (TRANS (@lem7211957 f) (@lem7211987 f)). Qed.
Lemma lem7211989 : term335 = term404.
Proof. exact (fun_ext (fun f : nat -> real => @lem7211988 f)). Qed.
Lemma lem7211990 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7211991 : term336 = term405.
Proof. exact (MK_COMB (@lem7211990) (@lem7211989)). Qed.
Lemma lem7211993 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7211994 (P : type1005) : (term406 P) = (term407 P).
Proof. exact (@lem7211993 (nat -> real) type1007 P). Qed.
Lemma lem7211995 : term408 = term409.
Proof. exact (@lem7211994 term410). Qed.
Lemma lem7211996 (f : nat -> real) : (term411 f) = (term402 f).
Proof. exact (eq_refl (term411 f)). Qed.
Lemma lem7211997 (x : type1007) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7211998 (f : nat -> real) (x : type1007) : (term412 f x) = (term413 f x).
Proof. exact (MK_COMB (@lem7211996 f) (@lem7211997 x)). Qed.
Lemma lem7211999 (x : type1007) (f : nat -> real) : (term413 f x) = (term400 x f).
Proof. exact (eq_refl (term413 f x)). Qed.
Lemma lem7212000 (x : type1007) (f : nat -> real) : (term412 f x) = (term400 x f).
Proof. exact (TRANS (@lem7211998 f x) (@lem7211999 x f)). Qed.
Lemma lem7212001 (f : nat -> real) : (term414 f) = (term402 f).
Proof. exact (fun_ext (fun x : type1007 => @lem7212000 x f)). Qed.
Lemma lem7212002 : (@ex ((nat -> real) -> (nat -> Prop) -> nat)) = (@ex ((nat -> real) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> real) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7212003 (f : nat -> real) : (term415 f) = (term403 f).
Proof. exact (MK_COMB (@lem7212002) (@lem7212001 f)). Qed.
Lemma lem7212004 : term416 = term404.
Proof. exact (fun_ext (fun f : nat -> real => @lem7212003 f)). Qed.
Lemma lem7212005 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7212006 : term408 = term405.
Proof. exact (MK_COMB (@lem7212005) (@lem7212004)). Qed.
Lemma lem7212007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7212008 : term417 = term418.
Proof. exact (MK_COMB (@lem7212007) (@lem7212006)). Qed.
Lemma lem7212009 (f : nat -> real) : (term411 f) = (term402 f).
Proof. exact (eq_refl (term411 f)). Qed.
Lemma lem7212010 (x : type1008) (f : nat -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7212011 (x : type1008) (f : nat -> real) : (term419 x f) = (term420 x f).
Proof. exact (MK_COMB (@lem7212009 f) (@lem7212010 x f)). Qed.
Lemma lem7212012 (x : type1008) (f : nat -> real) : (term420 x f) = (term421 x f).
Proof. exact (eq_refl (term420 x f)). Qed.
Lemma lem7212013 (x : type1008) (f : nat -> real) : (term419 x f) = (term421 x f).
Proof. exact (TRANS (@lem7212011 x f) (@lem7212012 x f)). Qed.
Lemma lem7212014 (x : type1008) : (term422 x) = (term423 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7212013 x f)). Qed.
Lemma lem7212015 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7212016 (x : type1008) : (term424 x) = (term425 x).
Proof. exact (MK_COMB (@lem7212015) (@lem7212014 x)). Qed.
Lemma lem7212017 : term426 = term427.
Proof. exact (fun_ext (fun x : type1008 => @lem7212016 x)). Qed.
Lemma lem7212018 : (@ex ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat)) = (@ex ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7212019 : term409 = term428.
Proof. exact (MK_COMB (@lem7212018) (@lem7212017)). Qed.
Lemma lem7212020 : (term408 = term409) = (term405 = term428).
Proof. exact (MK_COMB (@lem7212008) (@lem7212019)). Qed.
Lemma lem7212021 : term405 = term428.
Proof. exact (EQ_MP (@lem7212020) (@lem7211995)). Qed.
Lemma lem7212023 : term336 = term428.
Proof. exact (TRANS (@lem7211991) (@lem7212021)). Qed.
Lemma lem7212024 : term11 = term428.
Proof. exact (TRANS (@lem7211791) (@lem7212023)). Qed.
Lemma lem7212025 (h1 : term11) : term428.
Proof. exact (EQ_MP (@lem7212024) (@lem7210851 h1)). Qed.
Lemma lem7212026 (x : type1008) (h1 : term425 x) : term425 x.
Proof. exact (h1). Qed.
Lemma lem7212028 (f : nat -> real) (h1 : term114 f) : term114 f.
Proof. exact (h1). Qed.
Lemma lem7212029 (f : nat -> real) (g : nat -> real) (h1 : term105 f g) : term105 f g.
Proof. exact (h1). Qed.
Lemma lem7212030 (f : nat -> real) (m : nat) (g : nat -> real) (h1 : term98 f m g) : term98 f m g.
Proof. exact (h1). Qed.
Lemma lem7212031 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term88 f m n g.
Proof. exact (h1). Qed.
Lemma lem7212038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212039 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212038 nat (nat -> Prop) f x). Qed.
Lemma lem7212040 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7212039 Peano.le p). Qed.
Lemma lem7212041 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212042 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7212040 p) (@lem7212041 n)). Qed.
Lemma lem7212044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212045 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7212044 nat Prop f x). Qed.
Lemma lem7212046 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term429 p n).
Proof. exact (@lem7212045 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7212048 (p : nat) (n : nat) : (Peano.le p n) = (term429 p n).
Proof. exact (TRANS (@lem7212042 p n) (@lem7212046 p n)). Qed.
Lemma lem7212055 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212056 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212055 nat (nat -> Prop) f x). Qed.
Lemma lem7212057 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7212056 Peano.le m). Qed.
Lemma lem7212058 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7212059 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7212057 m) (@lem7212058 p)). Qed.
Lemma lem7212061 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212062 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7212061 nat Prop f x). Qed.
Lemma lem7212063 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term429 m p).
Proof. exact (@lem7212062 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7212065 (m : nat) (p : nat) : (Peano.le m p) = (term429 m p).
Proof. exact (TRANS (@lem7212059 m p) (@lem7212063 m p)). Qed.
Lemma lem7212066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7212067 (m : nat) (p : nat) : (term430 m p) = (term431 m p).
Proof. exact (MK_COMB (@lem7212066) (@lem7212065 m p)). Qed.
Lemma lem7212068 (m : nat) (p : nat) (n : nat) : (term56 m p n) = (term432 m p n).
Proof. exact (MK_COMB (@lem7212067 m p) (@lem7212048 p n)). Qed.
Lemma lem7212069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212078 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212079 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7212078 nat type1605 f x). Qed.
Lemma lem7212080 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7212079 dotdot m). Qed.
Lemma lem7212081 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212082 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7212080 m) (@lem7212081 n)). Qed.
Lemma lem7212084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212085 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212084 nat (nat -> Prop) f x). Qed.
Lemma lem7212086 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7212085 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7212088 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7212082 m n) (@lem7212086 m n)). Qed.
Lemma lem7212089 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem7212090 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term434 p m n).
Proof. exact (MK_COMB (@lem7212089 p) (@lem7212088 m n)). Qed.
Lemma lem7212092 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212093 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7212092 nat type993 f x). Qed.
Lemma lem7212094 (p : nat) : (@IN nat p) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p).
Proof. exact (@lem7212093 (@IN nat) p). Qed.
Lemma lem7212095 (m : nat) (n : nat) : (term433 m n) = (term433 m n).
Proof. exact (eq_refl (term433 m n)). Qed.
Lemma lem7212096 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term435 p m n).
Proof. exact (MK_COMB (@lem7212094 p) (@lem7212095 m n)). Qed.
Lemma lem7212098 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212099 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7212098 (nat -> Prop) Prop f x). Qed.
Lemma lem7212100 (p : nat) (m : nat) (n : nat) : (term435 p m n) = (term436 p m n).
Proof. exact (@lem7212099 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p) (term433 m n)). Qed.
Lemma lem7212101 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7212096 p m n) (@lem7212100 p m n)). Qed.
Lemma lem7212102 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7212090 p m n) (@lem7212101 p m n)). Qed.
Lemma lem7212103 (p : nat) (m : nat) (n : nat) : (term437 p m n) = (term438 p m n).
Proof. exact (MK_COMB (@lem7212069) (@lem7212102 p m n)). Qed.
Lemma lem7212104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7212105 (p : nat) (m : nat) (n : nat) : (term439 p m n) = (term440 p m n).
Proof. exact (MK_COMB (@lem7212104) (@lem7212103 p m n)). Qed.
Lemma lem7212106 (m : nat) (p : nat) (n : nat) : (term121 m p n) = (term441 m p n).
Proof. exact (MK_COMB (@lem7212105 p m n) (@lem7212068 m p n)). Qed.
Lemma lem7212107 (m : nat) (n : nat) : (term142 m n) = (term442 m n).
Proof. exact (fun_ext (fun p : nat => @lem7212106 m p n)). Qed.
Lemma lem7212108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212109 (m : nat) (n : nat) : (term157 m n) = (term443 m n).
Proof. exact (MK_COMB (@lem7212108) (@lem7212107 m n)). Qed.
Lemma lem7212110 (m : nat) : (term164 m) = (term444 m).
Proof. exact (fun_ext (fun n : nat => @lem7212109 m n)). Qed.
Lemma lem7212111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212112 (m : nat) : (term179 m) = (term445 m).
Proof. exact (MK_COMB (@lem7212111) (@lem7212110 m)). Qed.
Lemma lem7212113 : term186 = term446.
Proof. exact (fun_ext (fun m : nat => @lem7212112 m)). Qed.
Lemma lem7212114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212115 : term201 = term447.
Proof. exact (MK_COMB (@lem7212114) (@lem7212113)). Qed.
Lemma lem7212116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212124 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212123 nat (nat -> Prop) f x). Qed.
Lemma lem7212125 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7212124 Peano.le p). Qed.
Lemma lem7212126 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212127 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7212125 p) (@lem7212126 n)). Qed.
Lemma lem7212129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212130 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7212129 nat Prop f x). Qed.
Lemma lem7212131 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term429 p n).
Proof. exact (@lem7212130 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7212133 (p : nat) (n : nat) : (Peano.le p n) = (term429 p n).
Proof. exact (TRANS (@lem7212127 p n) (@lem7212131 p n)). Qed.
Lemma lem7212134 (p : nat) (n : nat) : (term448 p n) = (term449 p n).
Proof. exact (MK_COMB (@lem7212116) (@lem7212133 p n)). Qed.
Lemma lem7212135 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212143 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212142 nat (nat -> Prop) f x). Qed.
Lemma lem7212144 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7212143 Peano.le m). Qed.
Lemma lem7212145 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7212146 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7212144 m) (@lem7212145 p)). Qed.
Lemma lem7212148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212149 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7212148 nat Prop f x). Qed.
Lemma lem7212150 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term429 m p).
Proof. exact (@lem7212149 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7212152 (m : nat) (p : nat) : (Peano.le m p) = (term429 m p).
Proof. exact (TRANS (@lem7212146 m p) (@lem7212150 m p)). Qed.
Lemma lem7212153 (m : nat) (p : nat) : (term448 m p) = (term449 m p).
Proof. exact (MK_COMB (@lem7212135) (@lem7212152 m p)). Qed.
Lemma lem7212154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7212155 (m : nat) (p : nat) : (term450 m p) = (term451 m p).
Proof. exact (MK_COMB (@lem7212154) (@lem7212153 m p)). Qed.
Lemma lem7212156 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term452 m p n).
Proof. exact (MK_COMB (@lem7212155 m p) (@lem7212134 p n)). Qed.
Lemma lem7212165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212166 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7212165 nat type1605 f x). Qed.
Lemma lem7212167 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7212166 dotdot m). Qed.
Lemma lem7212168 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212169 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7212167 m) (@lem7212168 n)). Qed.
Lemma lem7212171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212172 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212171 nat (nat -> Prop) f x). Qed.
Lemma lem7212173 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7212172 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7212175 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7212169 m n) (@lem7212173 m n)). Qed.
Lemma lem7212176 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem7212177 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term434 p m n).
Proof. exact (MK_COMB (@lem7212176 p) (@lem7212175 m n)). Qed.
Lemma lem7212179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212180 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7212179 nat type993 f x). Qed.
Lemma lem7212181 (p : nat) : (@IN nat p) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p).
Proof. exact (@lem7212180 (@IN nat) p). Qed.
Lemma lem7212182 (m : nat) (n : nat) : (term433 m n) = (term433 m n).
Proof. exact (eq_refl (term433 m n)). Qed.
Lemma lem7212183 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term435 p m n).
Proof. exact (MK_COMB (@lem7212181 p) (@lem7212182 m n)). Qed.
Lemma lem7212185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212186 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7212185 (nat -> Prop) Prop f x). Qed.
Lemma lem7212187 (p : nat) (m : nat) (n : nat) : (term435 p m n) = (term436 p m n).
Proof. exact (@lem7212186 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p) (term433 m n)). Qed.
Lemma lem7212188 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7212183 p m n) (@lem7212187 p m n)). Qed.
Lemma lem7212189 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7212177 p m n) (@lem7212188 p m n)). Qed.
Lemma lem7212190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7212191 (p : nat) (m : nat) (n : nat) : (term122 p m n) = (term453 p m n).
Proof. exact (MK_COMB (@lem7212190) (@lem7212189 p m n)). Qed.
Lemma lem7212192 (m : nat) (p : nat) (n : nat) : (term124 m p n) = (term454 m p n).
Proof. exact (MK_COMB (@lem7212191 p m n) (@lem7212156 m p n)). Qed.
Lemma lem7212193 (m : nat) (n : nat) : (term141 m n) = (term455 m n).
Proof. exact (fun_ext (fun p : nat => @lem7212192 m p n)). Qed.
Lemma lem7212194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212195 (m : nat) (n : nat) : (term152 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem7212194) (@lem7212193 m n)). Qed.
Lemma lem7212196 (m : nat) : (term163 m) = (term457 m).
Proof. exact (fun_ext (fun n : nat => @lem7212195 m n)). Qed.
Lemma lem7212197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212198 (m : nat) : (term174 m) = (term458 m).
Proof. exact (MK_COMB (@lem7212197) (@lem7212196 m)). Qed.
Lemma lem7212199 : term185 = term459.
Proof. exact (fun_ext (fun m : nat => @lem7212198 m)). Qed.
Lemma lem7212200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212201 : term196 = term460.
Proof. exact (MK_COMB (@lem7212200) (@lem7212199)). Qed.
Lemma lem7212202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7212203 : term198 = term461.
Proof. exact (MK_COMB (@lem7212202) (@lem7212201)). Qed.
Lemma lem7212204 : term202 = term462.
Proof. exact (MK_COMB (@lem7212203) (@lem7212115)). Qed.
Lemma lem7212205 (h1 : term62) : term462.
Proof. exact (EQ_MP (@lem7212204) (@lem7211473 h1)). Qed.
Lemma lem7212237 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7212244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212245 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7212244 (nat -> Prop) type1011 f x). Qed.
Lemma lem7212246 (s : nat -> Prop) : (@sum nat s) = (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s).
Proof. exact (@lem7212245 (@sum nat) s). Qed.
Lemma lem7212247 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7212248 (s : nat -> Prop) (f : nat -> real) : (@sum nat s f) = (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s f).
Proof. exact (MK_COMB (@lem7212246 s) (@lem7212247 f)). Qed.
Lemma lem7212250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212251 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7212250 (nat -> real) real f x). Qed.
Lemma lem7212252 (s : nat -> Prop) (f : nat -> real) : (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s f) = (term463 s f).
Proof. exact (@lem7212251 (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s) f). Qed.
Lemma lem7212254 (s : nat -> Prop) (f : nat -> real) : (@sum nat s f) = (term463 s f).
Proof. exact (TRANS (@lem7212248 s f) (@lem7212252 s f)). Qed.
Lemma lem7212261 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212262 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7212261 (nat -> Prop) type1011 f x). Qed.
Lemma lem7212263 (s : nat -> Prop) : (@sum nat s) = (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s).
Proof. exact (@lem7212262 (@sum nat) s). Qed.
Lemma lem7212264 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212265 (s : nat -> Prop) (g : nat -> real) : (@sum nat s g) = (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s g).
Proof. exact (MK_COMB (@lem7212263 s) (@lem7212264 g)). Qed.
Lemma lem7212267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212268 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7212267 (nat -> real) real f x). Qed.
Lemma lem7212269 (s : nat -> Prop) (g : nat -> real) : (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s g) = (term463 s g).
Proof. exact (@lem7212268 (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s) g). Qed.
Lemma lem7212271 (s : nat -> Prop) (g : nat -> real) : (@sum nat s g) = (term463 s g).
Proof. exact (TRANS (@lem7212265 s g) (@lem7212269 s g)). Qed.
Lemma lem7212272 (s : nat -> Prop) (f : nat -> real) : (term464 s f) = (term465 s f).
Proof. exact (MK_COMB (@lem7212237) (@lem7212254 s f)). Qed.
Lemma lem7212273 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : ((@sum nat s f) = (@sum nat s g)) = ((term463 s f) = (term463 s g)).
Proof. exact (MK_COMB (@lem7212272 s f) (@lem7212271 s g)). Qed.
Lemma lem7212274 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212275 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7212276 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7212285 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212286 (f : type1008) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7212285 (nat -> real) type1007 f x). Qed.
Lemma lem7212287 (x : type1008) (f : nat -> real) : (x f) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7212286 x f). Qed.
Lemma lem7212288 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212289 (x : type1008) (f : nat -> real) (g : nat -> real) : (x f g) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f g).
Proof. exact (MK_COMB (@lem7212287 x f) (@lem7212288 g)). Qed.
Lemma lem7212291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212292 (f : type1007) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7212291 (nat -> real) type994 f x). Qed.
Lemma lem7212293 (x : type1008) (f : nat -> real) (g : nat -> real) : (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f g) = (term466 x f g).
Proof. exact (@lem7212292 (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f) g). Qed.
Lemma lem7212294 (x : type1008) (f : nat -> real) (g : nat -> real) : (x f g) = (term466 x f g).
Proof. exact (TRANS (@lem7212289 x f g) (@lem7212293 x f g)). Qed.
Lemma lem7212295 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7212296 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (x f g s) = (term467 x f g s).
Proof. exact (MK_COMB (@lem7212294 x f g) (@lem7212295 s)). Qed.
Lemma lem7212298 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212299 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7212298 (nat -> Prop) nat f x). Qed.
Lemma lem7212300 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term467 x f g s) = (term468 x f g s).
Proof. exact (@lem7212299 (term466 x f g) s). Qed.
Lemma lem7212302 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (x f g s) = (term468 x f g s).
Proof. exact (TRANS (@lem7212296 x f g s) (@lem7212300 x f g s)). Qed.
Lemma lem7212303 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term469 x f g s) = (term470 x f g s).
Proof. exact (MK_COMB (@lem7212276 f) (@lem7212302 x f g s)). Qed.
Lemma lem7212305 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212306 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7212305 nat real f x). Qed.
Lemma lem7212307 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term470 x f g s) = (term471 x f g s).
Proof. exact (@lem7212306 f (term468 x f g s)). Qed.
Lemma lem7212308 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term469 x f g s) = (term471 x f g s).
Proof. exact (TRANS (@lem7212303 x f g s) (@lem7212307 x f g s)). Qed.
Lemma lem7212309 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212319 (f : type1008) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7212318 (nat -> real) type1007 f x). Qed.
Lemma lem7212320 (x : type1008) (f : nat -> real) : (x f) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7212319 x f). Qed.
Lemma lem7212321 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212322 (x : type1008) (f : nat -> real) (g : nat -> real) : (x f g) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f g).
Proof. exact (MK_COMB (@lem7212320 x f) (@lem7212321 g)). Qed.
Lemma lem7212324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212325 (f : type1007) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7212324 (nat -> real) type994 f x). Qed.
Lemma lem7212326 (x : type1008) (f : nat -> real) (g : nat -> real) : (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f g) = (term466 x f g).
Proof. exact (@lem7212325 (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f) g). Qed.
Lemma lem7212327 (x : type1008) (f : nat -> real) (g : nat -> real) : (x f g) = (term466 x f g).
Proof. exact (TRANS (@lem7212322 x f g) (@lem7212326 x f g)). Qed.
Lemma lem7212328 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7212329 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (x f g s) = (term467 x f g s).
Proof. exact (MK_COMB (@lem7212327 x f g) (@lem7212328 s)). Qed.
Lemma lem7212331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212332 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7212331 (nat -> Prop) nat f x). Qed.
Lemma lem7212333 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term467 x f g s) = (term468 x f g s).
Proof. exact (@lem7212332 (term466 x f g) s). Qed.
Lemma lem7212335 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (x f g s) = (term468 x f g s).
Proof. exact (TRANS (@lem7212329 x f g s) (@lem7212333 x f g s)). Qed.
Lemma lem7212336 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term472 x f g s) = (term473 x f g s).
Proof. exact (MK_COMB (@lem7212309 g) (@lem7212335 x f g s)). Qed.
Lemma lem7212338 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212339 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7212338 nat real f x). Qed.
Lemma lem7212340 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term473 x f g s) = (term474 x f g s).
Proof. exact (@lem7212339 g (term468 x f g s)). Qed.
Lemma lem7212341 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term472 x f g s) = (term474 x f g s).
Proof. exact (TRANS (@lem7212336 x f g s) (@lem7212340 x f g s)). Qed.
Lemma lem7212342 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term475 x f g s) = (term476 x f g s).
Proof. exact (MK_COMB (@lem7212275) (@lem7212308 x f g s)). Qed.
Lemma lem7212343 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : ((term469 x f g s) = (term472 x f g s)) = ((term471 x f g s) = (term474 x f g s)).
Proof. exact (MK_COMB (@lem7212342 x f g s) (@lem7212341 x f g s)). Qed.
Lemma lem7212344 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term477 x f g s) = (term478 x f g s).
Proof. exact (MK_COMB (@lem7212274) (@lem7212343 x f g s)). Qed.
Lemma lem7212345 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem7212354 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212355 (f : type1008) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7212354 (nat -> real) type1007 f x). Qed.
Lemma lem7212356 (x : type1008) (f : nat -> real) : (x f) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7212355 x f). Qed.
Lemma lem7212357 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212358 (x : type1008) (f : nat -> real) (g : nat -> real) : (x f g) = (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f g).
Proof. exact (MK_COMB (@lem7212356 x f) (@lem7212357 g)). Qed.
Lemma lem7212360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212361 (f : type1007) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7212360 (nat -> real) type994 f x). Qed.
Lemma lem7212362 (x : type1008) (f : nat -> real) (g : nat -> real) : (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f g) = (term466 x f g).
Proof. exact (@lem7212361 (@I ((nat -> real) -> (nat -> real) -> (nat -> Prop) -> nat) x f) g). Qed.
Lemma lem7212363 (x : type1008) (f : nat -> real) (g : nat -> real) : (x f g) = (term466 x f g).
Proof. exact (TRANS (@lem7212358 x f g) (@lem7212362 x f g)). Qed.
Lemma lem7212364 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7212365 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (x f g s) = (term467 x f g s).
Proof. exact (MK_COMB (@lem7212363 x f g) (@lem7212364 s)). Qed.
Lemma lem7212367 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212368 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7212367 (nat -> Prop) nat f x). Qed.
Lemma lem7212369 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term467 x f g s) = (term468 x f g s).
Proof. exact (@lem7212368 (term466 x f g) s). Qed.
Lemma lem7212371 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (x f g s) = (term468 x f g s).
Proof. exact (TRANS (@lem7212365 x f g s) (@lem7212369 x f g s)). Qed.
Lemma lem7212372 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7212373 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term479 x f g s) = (term480 x f g s).
Proof. exact (MK_COMB (@lem7212345) (@lem7212371 x f g s)). Qed.
Lemma lem7212374 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term481 x f g s) = (term482 x f g s).
Proof. exact (MK_COMB (@lem7212373 x f g s) (@lem7212372 s)). Qed.
Lemma lem7212376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212377 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7212376 nat type993 f x). Qed.
Lemma lem7212378 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term480 x f g s) = (term483 x f g s).
Proof. exact (@lem7212377 (@IN nat) (term468 x f g s)). Qed.
Lemma lem7212379 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7212380 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term482 x f g s) = (term484 x f g s).
Proof. exact (MK_COMB (@lem7212378 x f g s) (@lem7212379 s)). Qed.
Lemma lem7212382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212383 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7212382 (nat -> Prop) Prop f x). Qed.
Lemma lem7212384 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term484 x f g s) = (term485 x f g s).
Proof. exact (@lem7212383 (term483 x f g s) s). Qed.
Lemma lem7212385 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term482 x f g s) = (term485 x f g s).
Proof. exact (TRANS (@lem7212380 x f g s) (@lem7212384 x f g s)). Qed.
Lemma lem7212386 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term481 x f g s) = (term485 x f g s).
Proof. exact (TRANS (@lem7212374 x f g s) (@lem7212385 x f g s)). Qed.
Lemma lem7212387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7212388 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term486 x f g s) = (term487 x f g s).
Proof. exact (MK_COMB (@lem7212387) (@lem7212386 x f g s)). Qed.
Lemma lem7212389 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term488 x f g s) = (term489 x f g s).
Proof. exact (MK_COMB (@lem7212388 x f g s) (@lem7212344 x f g s)). Qed.
Lemma lem7212390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7212391 (x : type1008) (f : nat -> real) (g : nat -> real) (s : nat -> Prop) : (term490 x f g s) = (term491 x f g s).
Proof. exact (MK_COMB (@lem7212390) (@lem7212389 x f g s)). Qed.
Lemma lem7212392 (x : type1008) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term492 x f s g) = (term493 x f s g).
Proof. exact (MK_COMB (@lem7212391 x f g s) (@lem7212273 f s g)). Qed.
Lemma lem7212393 (x : type1008) (f : nat -> real) (g : nat -> real) : (term494 x f g) = (term495 x f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7212392 x f s g)). Qed.
Lemma lem7212394 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7212395 (x : type1008) (f : nat -> real) (g : nat -> real) : (term496 x f g) = (term497 x f g).
Proof. exact (MK_COMB (@lem7212394) (@lem7212393 x f g)). Qed.
Lemma lem7212396 (x : type1008) (f : nat -> real) : (term498 x f) = (term499 x f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7212395 x f g)). Qed.
Lemma lem7212397 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7212398 (x : type1008) (f : nat -> real) : (term421 x f) = (term500 x f).
Proof. exact (MK_COMB (@lem7212397) (@lem7212396 x f)). Qed.
Lemma lem7212399 (x : type1008) : (term423 x) = (term501 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7212398 x f)). Qed.
Lemma lem7212400 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7212401 (x : type1008) : (term425 x) = (term502 x).
Proof. exact (MK_COMB (@lem7212400) (@lem7212399 x)). Qed.
Lemma lem7212402 (x : type1008) (h1 : term425 x) : term502 x.
Proof. exact (EQ_MP (@lem7212401 x) (@lem7212026 x h1)). Qed.
Lemma lem7212569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212570 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7212571 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7212578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212579 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7212578 nat type1605 f x). Qed.
Lemma lem7212580 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7212579 dotdot m). Qed.
Lemma lem7212581 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212582 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7212580 m) (@lem7212581 n)). Qed.
Lemma lem7212584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212585 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212584 nat (nat -> Prop) f x). Qed.
Lemma lem7212586 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7212585 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7212588 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7212582 m n) (@lem7212586 m n)). Qed.
Lemma lem7212589 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7212590 (m : nat) (n : nat) : (term503 m n) = (term504 m n).
Proof. exact (MK_COMB (@lem7212571) (@lem7212588 m n)). Qed.
Lemma lem7212591 (m : nat) (n : nat) (f : nat -> real) : (term63 m n f) = (term505 m n f).
Proof. exact (MK_COMB (@lem7212590 m n) (@lem7212589 f)). Qed.
Lemma lem7212593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212594 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7212593 (nat -> Prop) type1011 f x). Qed.
Lemma lem7212595 (m : nat) (n : nat) : (term504 m n) = (term506 m n).
Proof. exact (@lem7212594 (@sum nat) (term433 m n)). Qed.
Lemma lem7212596 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7212597 (m : nat) (n : nat) (f : nat -> real) : (term505 m n f) = (term507 m n f).
Proof. exact (MK_COMB (@lem7212595 m n) (@lem7212596 f)). Qed.
Lemma lem7212599 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212600 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7212599 (nat -> real) real f x). Qed.
Lemma lem7212601 (m : nat) (n : nat) (f : nat -> real) : (term507 m n f) = (term508 m n f).
Proof. exact (@lem7212600 (term506 m n) f). Qed.
Lemma lem7212602 (m : nat) (n : nat) (f : nat -> real) : (term505 m n f) = (term508 m n f).
Proof. exact (TRANS (@lem7212597 m n f) (@lem7212601 m n f)). Qed.
Lemma lem7212603 (m : nat) (n : nat) (f : nat -> real) : (term63 m n f) = (term508 m n f).
Proof. exact (TRANS (@lem7212591 m n f) (@lem7212602 m n f)). Qed.
Lemma lem7212604 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7212611 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212612 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7212611 nat type1605 f x). Qed.
Lemma lem7212613 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7212612 dotdot m). Qed.
Lemma lem7212614 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212615 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7212613 m) (@lem7212614 n)). Qed.
Lemma lem7212617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212618 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212617 nat (nat -> Prop) f x). Qed.
Lemma lem7212619 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7212618 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7212621 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7212615 m n) (@lem7212619 m n)). Qed.
Lemma lem7212622 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212623 (m : nat) (n : nat) : (term503 m n) = (term504 m n).
Proof. exact (MK_COMB (@lem7212604) (@lem7212621 m n)). Qed.
Lemma lem7212624 (m : nat) (n : nat) (g : nat -> real) : (term63 m n g) = (term505 m n g).
Proof. exact (MK_COMB (@lem7212623 m n) (@lem7212622 g)). Qed.
Lemma lem7212626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212627 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7212626 (nat -> Prop) type1011 f x). Qed.
Lemma lem7212628 (m : nat) (n : nat) : (term504 m n) = (term506 m n).
Proof. exact (@lem7212627 (@sum nat) (term433 m n)). Qed.
Lemma lem7212629 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7212630 (m : nat) (n : nat) (g : nat -> real) : (term505 m n g) = (term507 m n g).
Proof. exact (MK_COMB (@lem7212628 m n) (@lem7212629 g)). Qed.
Lemma lem7212632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212633 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7212632 (nat -> real) real f x). Qed.
Lemma lem7212634 (m : nat) (n : nat) (g : nat -> real) : (term507 m n g) = (term508 m n g).
Proof. exact (@lem7212633 (term506 m n) g). Qed.
Lemma lem7212635 (m : nat) (n : nat) (g : nat -> real) : (term505 m n g) = (term508 m n g).
Proof. exact (TRANS (@lem7212630 m n g) (@lem7212634 m n g)). Qed.
Lemma lem7212636 (m : nat) (n : nat) (g : nat -> real) : (term63 m n g) = (term508 m n g).
Proof. exact (TRANS (@lem7212624 m n g) (@lem7212635 m n g)). Qed.
Lemma lem7212637 (m : nat) (n : nat) (f : nat -> real) : (term509 m n f) = (term510 m n f).
Proof. exact (MK_COMB (@lem7212570) (@lem7212603 m n f)). Qed.
Lemma lem7212638 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term63 m n f) = (term63 m n g)) = ((term508 m n f) = (term508 m n g)).
Proof. exact (MK_COMB (@lem7212637 m n f) (@lem7212636 m n g)). Qed.
Lemma lem7212639 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term84 f m n g) = (term511 f m n g).
Proof. exact (MK_COMB (@lem7212569) (@lem7212638 f m n g)). Qed.
Lemma lem7212640 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7212645 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212646 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7212645 nat real f x). Qed.
Lemma lem7212648 (f : nat -> real) (i : nat) : (f i) = (@I (nat -> real) f i).
Proof. exact (@lem7212646 f i). Qed.
Lemma lem7212653 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212654 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7212653 nat real f x). Qed.
Lemma lem7212656 (g : nat -> real) (i : nat) : (g i) = (@I (nat -> real) g i).
Proof. exact (@lem7212654 g i). Qed.
Lemma lem7212657 (f : nat -> real) (i : nat) : (term512 f i) = (term513 f i).
Proof. exact (MK_COMB (@lem7212640) (@lem7212648 f i)). Qed.
Lemma lem7212658 (f : nat -> real) (g : nat -> real) (i : nat) : ((f i) = (g i)) = ((@I (nat -> real) f i) = (@I (nat -> real) g i)).
Proof. exact (MK_COMB (@lem7212657 f i) (@lem7212656 g i)). Qed.
Lemma lem7212659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212667 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212666 nat (nat -> Prop) f x). Qed.
Lemma lem7212668 (i : nat) : (Peano.le i) = (@I (nat -> nat -> Prop) Peano.le i).
Proof. exact (@lem7212667 Peano.le i). Qed.
Lemma lem7212669 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7212670 (i : nat) (n : nat) : (Peano.le i n) = (@I (nat -> nat -> Prop) Peano.le i n).
Proof. exact (MK_COMB (@lem7212668 i) (@lem7212669 n)). Qed.
Lemma lem7212672 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212673 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7212672 nat Prop f x). Qed.
Lemma lem7212674 (i : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le i n) = (term429 i n).
Proof. exact (@lem7212673 (@I (nat -> nat -> Prop) Peano.le i) n). Qed.
Lemma lem7212676 (i : nat) (n : nat) : (Peano.le i n) = (term429 i n).
Proof. exact (TRANS (@lem7212670 i n) (@lem7212674 i n)). Qed.
Lemma lem7212677 (i : nat) (n : nat) : (term448 i n) = (term449 i n).
Proof. exact (MK_COMB (@lem7212659) (@lem7212676 i n)). Qed.
Lemma lem7212678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7212685 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212686 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7212685 nat (nat -> Prop) f x). Qed.
Lemma lem7212687 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7212686 Peano.le m). Qed.
Lemma lem7212688 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7212689 (m : nat) (i : nat) : (Peano.le m i) = (@I (nat -> nat -> Prop) Peano.le m i).
Proof. exact (MK_COMB (@lem7212687 m) (@lem7212688 i)). Qed.
Lemma lem7212691 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7212692 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7212691 nat Prop f x). Qed.
Lemma lem7212693 (m : nat) (i : nat) : (@I (nat -> nat -> Prop) Peano.le m i) = (term429 m i).
Proof. exact (@lem7212692 (@I (nat -> nat -> Prop) Peano.le m) i). Qed.
Lemma lem7212695 (m : nat) (i : nat) : (Peano.le m i) = (term429 m i).
Proof. exact (TRANS (@lem7212689 m i) (@lem7212693 m i)). Qed.
Lemma lem7212696 (m : nat) (i : nat) : (term448 m i) = (term449 m i).
Proof. exact (MK_COMB (@lem7212678) (@lem7212695 m i)). Qed.
Lemma lem7212697 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7212698 (m : nat) (i : nat) : (term450 m i) = (term451 m i).
Proof. exact (MK_COMB (@lem7212697) (@lem7212696 m i)). Qed.
Lemma lem7212699 (m : nat) (i : nat) (n : nat) : (term77 m i n) = (term452 m i n).
Proof. exact (MK_COMB (@lem7212698 m i) (@lem7212677 i n)). Qed.
Lemma lem7212700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7212701 (m : nat) (i : nat) (n : nat) : (term79 m i n) = (term514 m i n).
Proof. exact (MK_COMB (@lem7212700) (@lem7212699 m i n)). Qed.
Lemma lem7212702 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term81 m n f g i) = (term515 m n f g i).
Proof. exact (MK_COMB (@lem7212701 m i n) (@lem7212658 f g i)). Qed.
Lemma lem7212703 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term82 m n f g) = (term516 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7212702 m n f g i)). Qed.
Lemma lem7212704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212705 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term83 m n f g) = (term517 m n f g).
Proof. exact (MK_COMB (@lem7212704) (@lem7212703 m n f g)). Qed.
Lemma lem7212706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7212707 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term86 m n f g) = (term518 m n f g).
Proof. exact (MK_COMB (@lem7212706) (@lem7212705 m n f g)). Qed.
Lemma lem7212708 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term88 f m n g) = (term519 f m n g).
Proof. exact (MK_COMB (@lem7212707 m n f g) (@lem7212639 f m n g)). Qed.
Lemma lem7212709 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term519 f m n g.
Proof. exact (EQ_MP (@lem7212708 f m n g) (@lem7212031 f m n g h1)). Qed.
Lemma lem7212711 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term517 m n f g.
Proof. exact (proj1 (@lem7212709 f m n g h1)). Qed.
Lemma lem7212712 (h1 : term62) : term447.
Proof. exact (proj2 (@lem7212205 h1)). Qed.
Lemma lem7212741 (x : type1008) (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : (term493 x f s g) = (term520 x f s g).
Proof. exact (@lem19699 (term485 x f g s) (term478 x f g s) ((term463 s f) = (term463 s g))). Qed.
Lemma lem7212742 (x : type1008) (f : nat -> real) (g : nat -> real) : (term495 x f g) = (term521 x f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7212741 x f s g)). Qed.
Lemma lem7212743 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7212744 (x : type1008) (f : nat -> real) (g : nat -> real) : (term497 x f g) = (term522 x f g).
Proof. exact (MK_COMB (@lem7212743) (@lem7212742 x f g)). Qed.
Lemma lem7212745 (x : type1008) (f : nat -> real) : (term499 x f) = (term523 x f).
Proof. exact (fun_ext (fun g : nat -> real => @lem7212744 x f g)). Qed.
Lemma lem7212746 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7212747 (x : type1008) (f : nat -> real) : (term500 x f) = (term524 x f).
Proof. exact (MK_COMB (@lem7212746) (@lem7212745 x f)). Qed.
Lemma lem7212748 (x : type1008) : (term501 x) = (term525 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7212747 x f)). Qed.
Lemma lem7212749 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7212751 (x : type1008) : (term502 x) = (term526 x).
Proof. exact (MK_COMB (@lem7212749) (@lem7212748 x)). Qed.
Lemma lem7212752 (x : type1008) (h1 : term425 x) : term526 x.
Proof. exact (EQ_MP (@lem7212751 x) (@lem7212402 x h1)). Qed.
Lemma lem7212795 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term515 m n f g i) = (term515 m n f g i).
Proof. exact (eq_refl (term515 m n f g i)). Qed.
Lemma lem7212796 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term516 m n f g) = (term516 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7212795 m n f g i)). Qed.
Lemma lem7212797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212799 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term517 m n f g) = (term517 m n f g).
Proof. exact (MK_COMB (@lem7212797) (@lem7212796 m n f g)). Qed.
Lemma lem7212800 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term517 m n f g.
Proof. exact (EQ_MP (@lem7212799 m n f g) (@lem7212711 f m n g h1)). Qed.
Lemma lem7212847 (m : nat) (p : nat) (n : nat) : (term441 m p n) = (term527 m p n).
Proof. exact (@lem19490 (term429 m p) (term438 p m n) (term429 p n)). Qed.
Lemma lem7212848 (m : nat) (n : nat) : (term442 m n) = (term528 m n).
Proof. exact (fun_ext (fun p : nat => @lem7212847 m p n)). Qed.
Lemma lem7212849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212850 (m : nat) (n : nat) : (term443 m n) = (term529 m n).
Proof. exact (MK_COMB (@lem7212849) (@lem7212848 m n)). Qed.
Lemma lem7212851 (m : nat) : (term444 m) = (term530 m).
Proof. exact (fun_ext (fun n : nat => @lem7212850 m n)). Qed.
Lemma lem7212852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212853 (m : nat) : (term445 m) = (term531 m).
Proof. exact (MK_COMB (@lem7212852) (@lem7212851 m)). Qed.
Lemma lem7212854 : term446 = term532.
Proof. exact (fun_ext (fun m : nat => @lem7212853 m)). Qed.
Lemma lem7212855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7212857 : term447 = term533.
Proof. exact (MK_COMB (@lem7212855) (@lem7212854)). Qed.
Lemma lem7212858 (h1 : term62) : term533.
Proof. exact (EQ_MP (@lem7212857) (@lem7212712 h1)). Qed.
Lemma lem7212865 (_96607 : nat -> real) (x : type1008) (h1 : term425 x) : term534 x _96607.
Proof. exact (@lem7212752 x h1 _96607). Qed.
Lemma lem7212866 (x : type1008) (_96607 : nat -> real) : (term534 x _96607) = (term524 x _96607).
Proof. exact (eq_refl (term534 x _96607)). Qed.
Lemma lem7212867 (_96607 : nat -> real) (x : type1008) (h1 : term425 x) : term524 x _96607.
Proof. exact (EQ_MP (@lem7212866 x _96607) (@lem7212865 _96607 x h1)). Qed.
Lemma lem7212868 (_96607 : nat -> real) (_96608 : nat -> real) (x : type1008) (h1 : term425 x) : term535 x _96607 _96608.
Proof. exact (@lem7212867 _96607 x h1 _96608). Qed.
Lemma lem7212869 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) : (term535 x _96607 _96608) = (term522 x _96607 _96608).
Proof. exact (eq_refl (term535 x _96607 _96608)). Qed.
Lemma lem7212870 (_96607 : nat -> real) (_96608 : nat -> real) (x : type1008) (h1 : term425 x) : term522 x _96607 _96608.
Proof. exact (EQ_MP (@lem7212869 x _96607 _96608) (@lem7212868 _96607 _96608 x h1)). Qed.
Lemma lem7212871 (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) (x : type1008) (h1 : term425 x) : term536 x _96607 _96608 _96609.
Proof. exact (@lem7212870 _96607 _96608 x h1 _96609). Qed.
Lemma lem7212872 (x : type1008) (_96607 : nat -> real) (_96609 : nat -> Prop) (_96608 : nat -> real) : (term536 x _96607 _96608 _96609) = (term520 x _96607 _96609 _96608).
Proof. exact (eq_refl (term536 x _96607 _96608 _96609)). Qed.
Lemma lem7212873 (_96607 : nat -> real) (_96609 : nat -> Prop) (_96608 : nat -> real) (x : type1008) (h1 : term425 x) : term520 x _96607 _96609 _96608.
Proof. exact (EQ_MP (@lem7212872 x _96607 _96609 _96608) (@lem7212871 _96607 _96608 _96609 x h1)). Qed.
Lemma lem7212883 (_96613 : nat) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term537 m n f g _96613.
Proof. exact (@lem7212800 f m n g h1 _96613). Qed.
Lemma lem7212884 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term537 m n f g _96613) = (term515 m n f g _96613).
Proof. exact (eq_refl (term537 m n f g _96613)). Qed.
Lemma lem7212885 (_96613 : nat) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term515 m n f g _96613.
Proof. exact (EQ_MP (@lem7212884 m n f g _96613) (@lem7212883 _96613 f m n g h1)). Qed.
Lemma lem7212895 (_96617 : nat) (h1 : term62) : term538 _96617.
Proof. exact (@lem7212858 h1 _96617). Qed.
Lemma lem7212896 (_96617 : nat) : (term538 _96617) = (term531 _96617).
Proof. exact (eq_refl (term538 _96617)). Qed.
Lemma lem7212897 (_96617 : nat) (h1 : term62) : term531 _96617.
Proof. exact (EQ_MP (@lem7212896 _96617) (@lem7212895 _96617 h1)). Qed.
Lemma lem7212898 (_96617 : nat) (_96618 : nat) (h1 : term62) : term539 _96617 _96618.
Proof. exact (@lem7212897 _96617 h1 _96618). Qed.
Lemma lem7212899 (_96617 : nat) (_96618 : nat) : (term539 _96617 _96618) = (term529 _96617 _96618).
Proof. exact (eq_refl (term539 _96617 _96618)). Qed.
Lemma lem7212900 (_96617 : nat) (_96618 : nat) (h1 : term62) : term529 _96617 _96618.
Proof. exact (EQ_MP (@lem7212899 _96617 _96618) (@lem7212898 _96617 _96618 h1)). Qed.
Lemma lem7212901 (_96617 : nat) (_96618 : nat) (_96619 : nat) (h1 : term62) : term540 _96617 _96618 _96619.
Proof. exact (@lem7212900 _96617 _96618 h1 _96619). Qed.
Lemma lem7212902 (_96617 : nat) (_96619 : nat) (_96618 : nat) : (term540 _96617 _96618 _96619) = (term527 _96617 _96619 _96618).
Proof. exact (eq_refl (term540 _96617 _96618 _96619)). Qed.
Lemma lem7212903 (_96617 : nat) (_96619 : nat) (_96618 : nat) (h1 : term62) : term527 _96617 _96619 _96618.
Proof. exact (EQ_MP (@lem7212902 _96617 _96619 _96618) (@lem7212901 _96617 _96618 _96619 h1)). Qed.
Lemma lem7212922 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term515 m n f g _96613) = (term541 m n f g _96613).
Proof. exact (@lem7210458 (term449 m _96613) (term449 _96613 n) ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613))). Qed.
Lemma lem7212923 (_96613 : nat) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term541 m n f g _96613.
Proof. exact (EQ_MP (@lem7212922 m n f g _96613) (@lem7212885 _96613 f m n g h1)). Qed.
Lemma lem7212925 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term511 f m n g.
Proof. exact (proj2 (@lem7212709 f m n g h1)). Qed.
Lemma lem7212941 (_96618 : nat) (_96617 : nat) (_96619 : nat) (h1 : term62) : term542 _96618 _96617 _96619.
Proof. exact (proj1 (@lem7212903 _96617 _96619 _96618 h1)). Qed.
Lemma lem7212947 (_96617 : nat) (_96619 : nat) (_96618 : nat) (h1 : term62) : term543 _96617 _96619 _96618.
Proof. exact (proj2 (@lem7212903 _96617 _96619 _96618 h1)). Qed.
Lemma lem7212965 (_96607 : nat -> real) (_96609 : nat -> Prop) (_96608 : nat -> real) (x : type1008) (h1 : term425 x) : term544 x _96607 _96609 _96608.
Proof. exact (proj1 (@lem7212873 _96607 _96609 _96608 x h1)). Qed.
Lemma lem7212971 (_96607 : nat -> real) (_96609 : nat -> Prop) (_96608 : nat -> real) (x : type1008) (h1 : term425 x) : term545 x _96607 _96609 _96608.
Proof. exact (proj2 (@lem7212873 _96607 _96609 _96608 x h1)). Qed.
Lemma lem7213317 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (h1). Qed.
Lemma lem7213318 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term511 f m n g) : term546 f m n g.
Proof. exact (fun h0 : (term508 m n f) = (term508 m n g) => @lem7213317 f m n g h1). Qed.
Lemma lem7213320 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7213321 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term546 f m n g) = (term511 f m n g).
Proof. exact (@lem7213320 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7213322 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (EQ_MP (@lem7213321 f m n g) (@lem7213318 f m n g h1)). Qed.
Lemma lem7213324 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7213327 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : (term544 x _96607 _96609 _96608) = (term549 x _96607 _96608 _96609).
Proof. exact (@lem7213324 ((term463 _96609 _96607) = (term463 _96609 _96608)) (term485 x _96607 _96608 _96609)). Qed.
Lemma lem7213330 (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) (x : type1008) (h1 : term425 x) : term549 x _96607 _96608 _96609.
Proof. exact (EQ_MP (@lem7213327 x _96607 _96608 _96609) (@lem7212965 _96607 _96609 _96608 x h1)). Qed.
Lemma lem7213331 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (x : type1008) (h1 : term425 x) : term550 x f g m n.
Proof. exact (@lem7213330 f g (term433 m n) x h1). Qed.
Lemma lem7213334 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term511 f m n g) : term551 x f g m n.
Proof. exact (@lem7213331 f g m n x h1 (@lem7213322 f m n g h2)). Qed.
Lemma lem7213335 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term511 f m n g) : term552 x f g m n.
Proof. exact (fun h0 : term553 x f g m n => @lem7213334 x f m n g h1 h2). Qed.
Lemma lem7213337 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7213338 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) : (term552 x f g m n) = (term551 x f g m n).
Proof. exact (@lem7213337 (term551 x f g m n)). Qed.
Lemma lem7213339 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term511 f m n g) : term551 x f g m n.
Proof. exact (EQ_MP (@lem7213338 x f g m n) (@lem7213335 x f m n g h1 h2)). Qed.
Lemma lem7213345 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7213346 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term542 _96618 _96617 _96619) = (term555 _96619 _96617 _96618).
Proof. exact (@lem7213345 (term429 _96617 _96619) (term438 _96619 _96617 _96618)). Qed.
Lemma lem7213352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7213353 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term556 _96618 _96617 _96619) = (term557 _96619 _96617 _96618).
Proof. exact (MK_COMB (@lem7213352) (@lem7213346 _96619 _96617 _96618)). Qed.
Lemma lem7213359 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term555 _96619 _96617 _96618) = (term555 _96619 _96617 _96618).
Proof. exact (eq_refl (term555 _96619 _96617 _96618)). Qed.
Lemma lem7213360 (_96619 : nat) (_96617 : nat) (_96618 : nat) : ((term542 _96618 _96617 _96619) = (term555 _96619 _96617 _96618)) = ((term555 _96619 _96617 _96618) = (term555 _96619 _96617 _96618)).
Proof. exact (MK_COMB (@lem7213353 _96619 _96617 _96618) (@lem7213359 _96619 _96617 _96618)). Qed.
Lemma lem7213362 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7213363 (x : Prop) : (x = x) = True.
Proof. exact (@lem7213362 Prop x). Qed.
Lemma lem7213364 (_96619 : nat) (_96617 : nat) (_96618 : nat) : ((term555 _96619 _96617 _96618) = (term555 _96619 _96617 _96618)) = True.
Proof. exact (@lem7213363 (term555 _96619 _96617 _96618)). Qed.
Lemma lem7213365 (_96619 : nat) (_96617 : nat) (_96618 : nat) : ((term542 _96618 _96617 _96619) = (term555 _96619 _96617 _96618)) = True.
Proof. exact (TRANS (@lem7213360 _96619 _96617 _96618) (@lem7213364 _96619 _96617 _96618)). Qed.
Lemma lem7213366 (_96619 : nat) (_96617 : nat) (_96618 : nat) : True = ((term542 _96618 _96617 _96619) = (term555 _96619 _96617 _96618)).
Proof. exact (SYM (@lem7213365 _96619 _96617 _96618)). Qed.
Lemma lem7213367 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term542 _96618 _96617 _96619) = (term555 _96619 _96617 _96618).
Proof. exact (EQ_MP (@lem7213366 _96619 _96617 _96618) (@lem0)). Qed.
Lemma lem7213368 (_96619 : nat) (_96617 : nat) (_96618 : nat) (h1 : term62) : term555 _96619 _96617 _96618.
Proof. exact (EQ_MP (@lem7213367 _96619 _96617 _96618) (@lem7212941 _96618 _96617 _96619 h1)). Qed.
Lemma lem7213370 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7213371 (_96618 : nat) (_96617 : nat) (_96619 : nat) : (term555 _96619 _96617 _96618) = (term558 _96618 _96617 _96619).
Proof. exact (@lem7213370 (term438 _96619 _96617 _96618) (term429 _96617 _96619)). Qed.
Lemma lem7213373 (a : Prop) : (term559 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7213374 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term560 _96619 _96617 _96618) = (term436 _96619 _96617 _96618).
Proof. exact (@lem7213373 (term436 _96619 _96617 _96618)). Qed.
Lemma lem7213375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7213376 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term561 _96619 _96617 _96618) = (term562 _96619 _96617 _96618).
Proof. exact (MK_COMB (@lem7213375) (@lem7213374 _96619 _96617 _96618)). Qed.
Lemma lem7213377 (_96617 : nat) (_96619 : nat) : (term429 _96617 _96619) = (term429 _96617 _96619).
Proof. exact (eq_refl (term429 _96617 _96619)). Qed.
Lemma lem7213378 (_96618 : nat) (_96617 : nat) (_96619 : nat) : (term558 _96618 _96617 _96619) = (term563 _96618 _96617 _96619).
Proof. exact (MK_COMB (@lem7213376 _96619 _96617 _96618) (@lem7213377 _96617 _96619)). Qed.
Lemma lem7213379 (_96618 : nat) (_96617 : nat) (_96619 : nat) : (term555 _96619 _96617 _96618) = (term563 _96618 _96617 _96619).
Proof. exact (TRANS (@lem7213371 _96618 _96617 _96619) (@lem7213378 _96618 _96617 _96619)). Qed.
Lemma lem7213382 (_96618 : nat) (_96617 : nat) (_96619 : nat) (h1 : term62) : term563 _96618 _96617 _96619.
Proof. exact (EQ_MP (@lem7213379 _96618 _96617 _96619) (@lem7213368 _96619 _96617 _96618 h1)). Qed.
Lemma lem7213383 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term62) : term564 x f g m n.
Proof. exact (@lem7213382 n m (term565 x f g m n) h1). Qed.
Lemma lem7213386 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term566 x f g m n.
Proof. exact (@lem7213383 x f g m n h2 (@lem7213339 x f m n g h1 h3)). Qed.
Lemma lem7213387 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term567 x f g m n.
Proof. exact (fun h0 : term568 x f g m n => @lem7213386 x f m n g h1 h2 h3). Qed.
Lemma lem7213389 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7213390 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) : (term567 x f g m n) = (term566 x f g m n).
Proof. exact (@lem7213389 (term566 x f g m n)). Qed.
Lemma lem7213391 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term566 x f g m n.
Proof. exact (EQ_MP (@lem7213390 x f g m n) (@lem7213387 x f m n g h1 h2 h3)). Qed.
Lemma lem7213394 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (h1). Qed.
Lemma lem7213395 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term511 f m n g) : term546 f m n g.
Proof. exact (fun h0 : (term508 m n f) = (term508 m n g) => @lem7213394 f m n g h1). Qed.
Lemma lem7213397 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7213398 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term546 f m n g) = (term511 f m n g).
Proof. exact (@lem7213397 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7213399 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (EQ_MP (@lem7213398 f m n g) (@lem7213395 f m n g h1)). Qed.
Lemma lem7213401 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7213404 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : (term545 x _96607 _96609 _96608) = (term569 x _96607 _96608 _96609).
Proof. exact (@lem7213401 ((term463 _96609 _96607) = (term463 _96609 _96608)) (term478 x _96607 _96608 _96609)). Qed.
Lemma lem7213407 (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) (x : type1008) (h1 : term425 x) : term569 x _96607 _96608 _96609.
Proof. exact (EQ_MP (@lem7213404 x _96607 _96608 _96609) (@lem7212971 _96607 _96609 _96608 x h1)). Qed.
Lemma lem7213408 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (x : type1008) (h1 : term425 x) : term570 x f g m n.
Proof. exact (@lem7213407 f g (term433 m n) x h1). Qed.
Lemma lem7213411 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term511 f m n g) : term571 x f g m n.
Proof. exact (@lem7213408 f g m n x h1 (@lem7213399 f m n g h2)). Qed.
Lemma lem7213412 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term511 f m n g) : term572 x f g m n.
Proof. exact (fun h0 : (term573 x f g m n) = (term574 x f g m n) => @lem7213411 x f m n g h1 h2). Qed.
Lemma lem7213414 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7213415 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) : (term572 x f g m n) = (term571 x f g m n).
Proof. exact (@lem7213414 ((term573 x f g m n) = (term574 x f g m n))). Qed.
Lemma lem7213416 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term511 f m n g) : term571 x f g m n.
Proof. exact (EQ_MP (@lem7213415 x f g m n) (@lem7213412 x f m n g h1 h2)). Qed.
Lemma lem7213422 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7213423 (n : nat) (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term541 m n f g _96613) = (term575 n m f g _96613).
Proof. exact (@lem7213422 (term449 _96613 n) (term449 m _96613) ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613))). Qed.
Lemma lem7213437 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7213438 (f : nat -> real) (g : nat -> real) (m : nat) (_96613 : nat) : (term576 m f g _96613) = (term577 f g m _96613).
Proof. exact (@lem7213437 ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613)) (term449 m _96613)). Qed.
Lemma lem7213446 (_96613 : nat) (n : nat) : (term451 _96613 n) = (term451 _96613 n).
Proof. exact (eq_refl (term451 _96613 n)). Qed.
Lemma lem7213447 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) (_96613 : nat) : (term575 n m f g _96613) = (term578 n f g m _96613).
Proof. exact (MK_COMB (@lem7213446 _96613 n) (@lem7213438 f g m _96613)). Qed.
Lemma lem7213451 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7213452 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : (term578 n f g m _96613) = (term579 f g n m _96613).
Proof. exact (@lem7213451 ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613)) (term449 _96613 n) (term449 m _96613)). Qed.
Lemma lem7213470 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : (term575 n m f g _96613) = (term579 f g n m _96613).
Proof. exact (TRANS (@lem7213447 n f g m _96613) (@lem7213452 f g n m _96613)). Qed.
Lemma lem7213471 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : (term541 m n f g _96613) = (term579 f g n m _96613).
Proof. exact (TRANS (@lem7213423 n m f g _96613) (@lem7213470 f g n m _96613)). Qed.
Lemma lem7213472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7213473 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : (term580 m n f g _96613) = (term581 f g n m _96613).
Proof. exact (MK_COMB (@lem7213472) (@lem7213471 f g n m _96613)). Qed.
Lemma lem7213487 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7213488 (f : nat -> real) (g : nat -> real) (m : nat) (_96613 : nat) : (term576 m f g _96613) = (term577 f g m _96613).
Proof. exact (@lem7213487 ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613)) (term449 m _96613)). Qed.
Lemma lem7213496 (_96613 : nat) (n : nat) : (term451 _96613 n) = (term451 _96613 n).
Proof. exact (eq_refl (term451 _96613 n)). Qed.
Lemma lem7213497 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) (_96613 : nat) : (term575 n m f g _96613) = (term578 n f g m _96613).
Proof. exact (MK_COMB (@lem7213496 _96613 n) (@lem7213488 f g m _96613)). Qed.
Lemma lem7213501 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7213502 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : (term578 n f g m _96613) = (term579 f g n m _96613).
Proof. exact (@lem7213501 ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613)) (term449 _96613 n) (term449 m _96613)). Qed.
Lemma lem7213520 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : (term575 n m f g _96613) = (term579 f g n m _96613).
Proof. exact (TRANS (@lem7213497 n f g m _96613) (@lem7213502 f g n m _96613)). Qed.
Lemma lem7213521 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : ((term541 m n f g _96613) = (term575 n m f g _96613)) = ((term579 f g n m _96613) = (term579 f g n m _96613)).
Proof. exact (MK_COMB (@lem7213473 f g n m _96613) (@lem7213520 f g n m _96613)). Qed.
Lemma lem7213523 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7213524 (x : Prop) : (x = x) = True.
Proof. exact (@lem7213523 Prop x). Qed.
Lemma lem7213525 (f : nat -> real) (g : nat -> real) (n : nat) (m : nat) (_96613 : nat) : ((term579 f g n m _96613) = (term579 f g n m _96613)) = True.
Proof. exact (@lem7213524 (term579 f g n m _96613)). Qed.
Lemma lem7213526 (n : nat) (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : ((term541 m n f g _96613) = (term575 n m f g _96613)) = True.
Proof. exact (TRANS (@lem7213521 f g n m _96613) (@lem7213525 f g n m _96613)). Qed.
Lemma lem7213527 (n : nat) (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : True = ((term541 m n f g _96613) = (term575 n m f g _96613)).
Proof. exact (SYM (@lem7213526 n m f g _96613)). Qed.
Lemma lem7213528 (n : nat) (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term541 m n f g _96613) = (term575 n m f g _96613).
Proof. exact (EQ_MP (@lem7213527 n m f g _96613) (@lem0)). Qed.
Lemma lem7213529 (_96613 : nat) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term575 n m f g _96613.
Proof. exact (EQ_MP (@lem7213528 n m f g _96613) (@lem7212923 _96613 f m n g h1)). Qed.
Lemma lem7213531 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7213532 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) (n : nat) : (term575 n m f g _96613) = (term582 m f g _96613 n).
Proof. exact (@lem7213531 (term576 m f g _96613) (term449 _96613 n)). Qed.
Lemma lem7213534 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7213535 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term585 m f g _96613) = (term586 m f g _96613).
Proof. exact (@lem7213534 (term449 m _96613) ((@I (nat -> real) f _96613) = (@I (nat -> real) g _96613))). Qed.
Lemma lem7213537 (a : Prop) : (term559 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7213538 (m : nat) (_96613 : nat) : (term587 m _96613) = (term429 m _96613).
Proof. exact (@lem7213537 (term429 m _96613)). Qed.
Lemma lem7213539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7213540 (m : nat) (_96613 : nat) : (term588 m _96613) = (term431 m _96613).
Proof. exact (MK_COMB (@lem7213539) (@lem7213538 m _96613)). Qed.
Lemma lem7213541 (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term589 f g _96613) = (term589 f g _96613).
Proof. exact (eq_refl (term589 f g _96613)). Qed.
Lemma lem7213542 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term586 m f g _96613) = (term590 m f g _96613).
Proof. exact (MK_COMB (@lem7213540 m _96613) (@lem7213541 f g _96613)). Qed.
Lemma lem7213543 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term585 m f g _96613) = (term590 m f g _96613).
Proof. exact (TRANS (@lem7213535 m f g _96613) (@lem7213542 m f g _96613)). Qed.
Lemma lem7213544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7213545 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) : (term591 m f g _96613) = (term592 m f g _96613).
Proof. exact (MK_COMB (@lem7213544) (@lem7213543 m f g _96613)). Qed.
Lemma lem7213546 (_96613 : nat) (n : nat) : (term449 _96613 n) = (term449 _96613 n).
Proof. exact (eq_refl (term449 _96613 n)). Qed.
Lemma lem7213547 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) (n : nat) : (term582 m f g _96613 n) = (term593 m f g _96613 n).
Proof. exact (MK_COMB (@lem7213545 m f g _96613) (@lem7213546 _96613 n)). Qed.
Lemma lem7213548 (m : nat) (f : nat -> real) (g : nat -> real) (_96613 : nat) (n : nat) : (term575 n m f g _96613) = (term593 m f g _96613 n).
Proof. exact (TRANS (@lem7213532 m f g _96613 n) (@lem7213547 m f g _96613 n)). Qed.
Lemma lem7213550 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term594 x f g m n.
Proof. exact (conj (@lem7213391 x f m n g h1 h2 h3) (@lem7213416 x f m n g h1 h3)). Qed.
Lemma lem7213552 (_96613 : nat) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term593 m f g _96613 n.
Proof. exact (EQ_MP (@lem7213548 m f g _96613 n) (@lem7213529 _96613 f m n g h1)). Qed.
Lemma lem7213553 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term595 x f g m n.
Proof. exact (@lem7213552 (term565 x f g m n) f m n g h1). Qed.
Lemma lem7213556 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term596 x f g m n.
Proof. exact (@lem7213553 x f m n g h4 (@lem7213550 x f m n g h1 h2 h3)). Qed.
Lemma lem7213557 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term597 x f g m n.
Proof. exact (fun h0 : term598 x f g m n => @lem7213556 x f m n g h1 h2 h3 h4). Qed.
Lemma lem7213559 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7213560 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) : (term597 x f g m n) = (term596 x f g m n).
Proof. exact (@lem7213559 (term598 x f g m n)). Qed.
Lemma lem7213561 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term596 x f g m n.
Proof. exact (EQ_MP (@lem7213560 x f g m n) (@lem7213557 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7213563 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7213566 (_96619 : nat) (_96617 : nat) (_96618 : nat) : (term543 _96617 _96619 _96618) = (term599 _96619 _96617 _96618).
Proof. exact (@lem7213563 (term429 _96619 _96618) (term438 _96619 _96617 _96618)). Qed.
Lemma lem7213569 (_96619 : nat) (_96617 : nat) (_96618 : nat) (h1 : term62) : term599 _96619 _96617 _96618.
Proof. exact (EQ_MP (@lem7213566 _96619 _96617 _96618) (@lem7212947 _96617 _96619 _96618 h1)). Qed.
Lemma lem7213570 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (_96617 : nat) (n : nat) (h1 : term62) : term600 x f g m _96617 n.
Proof. exact (@lem7213569 (term565 x f g m n) _96617 n h1). Qed.
Lemma lem7213573 (_96617 : nat) (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term601 x f g m _96617 n.
Proof. exact (@lem7213570 x f g m _96617 n h2 (@lem7213561 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7213574 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term553 x f g m n.
Proof. exact (@lem7213573 m x f m n g h1 h2 h3 h4). Qed.
Lemma lem7213575 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term602 x f g m n.
Proof. exact (fun h0 : term551 x f g m n => @lem7213574 x f m n g h1 h2 h3 h4). Qed.
Lemma lem7213577 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7213578 (x : type1008) (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) : (term602 x f g m n) = (term553 x f g m n).
Proof. exact (@lem7213577 (term551 x f g m n)). Qed.
Lemma lem7213579 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term553 x f g m n.
Proof. exact (EQ_MP (@lem7213578 x f g m n) (@lem7213575 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7213585 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7213586 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : (term544 x _96607 _96609 _96608) = (term603 x _96607 _96608 _96609).
Proof. exact (@lem7213585 ((term463 _96609 _96607) = (term463 _96609 _96608)) (term485 x _96607 _96608 _96609)). Qed.
Lemma lem7213594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7213595 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : (term604 x _96607 _96609 _96608) = (term605 x _96607 _96608 _96609).
Proof. exact (MK_COMB (@lem7213594) (@lem7213586 x _96607 _96608 _96609)). Qed.
Lemma lem7213603 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : (term603 x _96607 _96608 _96609) = (term603 x _96607 _96608 _96609).
Proof. exact (eq_refl (term603 x _96607 _96608 _96609)). Qed.
Lemma lem7213604 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : ((term544 x _96607 _96609 _96608) = (term603 x _96607 _96608 _96609)) = ((term603 x _96607 _96608 _96609) = (term603 x _96607 _96608 _96609)).
Proof. exact (MK_COMB (@lem7213595 x _96607 _96608 _96609) (@lem7213603 x _96607 _96608 _96609)). Qed.
Lemma lem7213606 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7213607 (x : Prop) : (x = x) = True.
Proof. exact (@lem7213606 Prop x). Qed.
Lemma lem7213608 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : ((term603 x _96607 _96608 _96609) = (term603 x _96607 _96608 _96609)) = True.
Proof. exact (@lem7213607 (term603 x _96607 _96608 _96609)). Qed.
Lemma lem7213609 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : ((term544 x _96607 _96609 _96608) = (term603 x _96607 _96608 _96609)) = True.
Proof. exact (TRANS (@lem7213604 x _96607 _96608 _96609) (@lem7213608 x _96607 _96608 _96609)). Qed.
Lemma lem7213610 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : True = ((term544 x _96607 _96609 _96608) = (term603 x _96607 _96608 _96609)).
Proof. exact (SYM (@lem7213609 x _96607 _96608 _96609)). Qed.
Lemma lem7213611 (x : type1008) (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) : (term544 x _96607 _96609 _96608) = (term603 x _96607 _96608 _96609).
Proof. exact (EQ_MP (@lem7213610 x _96607 _96608 _96609) (@lem0)). Qed.
Lemma lem7213612 (_96607 : nat -> real) (_96608 : nat -> real) (_96609 : nat -> Prop) (x : type1008) (h1 : term425 x) : term603 x _96607 _96608 _96609.
Proof. exact (EQ_MP (@lem7213611 x _96607 _96608 _96609) (@lem7212965 _96607 _96609 _96608 x h1)). Qed.
Lemma lem7213614 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7213617 (x : type1008) (_96607 : nat -> real) (_96609 : nat -> Prop) (_96608 : nat -> real) : (term603 x _96607 _96608 _96609) = (term606 x _96607 _96609 _96608).
Proof. exact (@lem7213614 (term485 x _96607 _96608 _96609) ((term463 _96609 _96607) = (term463 _96609 _96608))). Qed.
Lemma lem7213620 (_96607 : nat -> real) (_96609 : nat -> Prop) (_96608 : nat -> real) (x : type1008) (h1 : term425 x) : term606 x _96607 _96609 _96608.
Proof. exact (EQ_MP (@lem7213617 x _96607 _96609 _96608) (@lem7213612 _96607 _96608 _96609 x h1)). Qed.
Lemma lem7213621 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (x : type1008) (h1 : term425 x) : term607 x f m n g.
Proof. exact (@lem7213620 f (term433 m n) g x h1). Qed.
Lemma lem7213624 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : (term508 m n f) = (term508 m n g).
Proof. exact (@lem7213621 f m n g x h1 (@lem7213579 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7213625 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : term608 f m n g.
Proof. exact (fun h0 : term511 f m n g => @lem7213624 x f m n g h1 h2 h0 h3). Qed.
Lemma lem7213627 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7213628 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term608 f m n g) = ((term508 m n f) = (term508 m n g)).
Proof. exact (@lem7213627 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7213629 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : (term508 m n f) = (term508 m n g).
Proof. exact (EQ_MP (@lem7213628 f m n g) (@lem7213625 x f m n g h1 h2 h3)). Qed.
Lemma lem7213632 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7213634 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term511 f m n g) = (term609 f m n g).
Proof. exact (@lem7213632 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7213637 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term88 f m n g) : term609 f m n g.
Proof. exact (EQ_MP (@lem7213634 f m n g) (@lem7212925 f m n g h1)). Qed.
Lemma lem7213640 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : False.
Proof. exact (@lem7213637 f m n g h3 (@lem7213629 x f m n g h1 h2 h3)). Qed.
Lemma lem7213641 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : term610.
Proof. exact (fun h0 : ~ False => @lem7213640 x f m n g h1 h2 h3). Qed.
Lemma lem7213643 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7213644 : term610 = False.
Proof. exact (@lem7213643 False). Qed.
Lemma lem7213645 (x : type1008) (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : False.
Proof. exact (EQ_MP (@lem7213644) (@lem7213641 x f m n g h1 h2 h3)). Qed.
Lemma lem7213646 (x : type1008) (f : nat -> real) (m : nat) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term98 f m g) : False.
Proof. exact (ex_elim (@lem7212030 f m g h3) (fun n : nat => fun h0 : term97 f m g n => @lem7213645 x f m n g h1 h2 h0)). Qed.
Lemma lem7213647 (x : type1008) (f : nat -> real) (g : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term105 f g) : False.
Proof. exact (ex_elim (@lem7212029 f g h3) (fun m : nat => fun h0 : term104 f g m => @lem7213646 x f m g h1 h2 h0)). Qed.
Lemma lem7213648 (x : type1008) (f : nat -> real) (h1 : term425 x) (h2 : term62) (h3 : term114 f) : False.
Proof. exact (ex_elim (@lem7212028 f h3) (fun g : nat -> real => fun h0 : term113 f g => @lem7213647 x f g h1 h2 h0)). Qed.
Lemma lem7213649 (x : type1008) (h1 : term425 x) (h2 : term62) (h3 : term10) : False.
Proof. exact (ex_elim (@lem7211026 h3) (fun f : nat -> real => fun h0 : term119 f => @lem7213648 x f h1 h2 h0)). Qed.
Lemma lem7213650 {_132349 : Type'} (x : type1008) (h1 : term49 _132349) (h2 : term425 x) (h3 : term62) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7211759 _132349 h1) (fun x' : type711 _132349 => fun h0 : term316 _132349 x' => @lem7213649 x h2 h3 h4)). Qed.
Lemma lem7213651 {_132349 : Type'} (h1 : term49 _132349) (h2 : term11) (h3 : term62) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7212025 h2) (fun x : type1008 => fun h0 : term427 x => @lem7213650 _132349 x h1 h0 h3 h4)). Qed.
Lemma lem7213652 {_132349 : Type'} (h1 : term49 _132349) (h2 : term62) (h3 : term10) : term16.
Proof. exact (fun h0 : term11 => @lem7213651 _132349 h1 h0 h2 h3). Qed.
Lemma lem7213653 : term16 = term17.
Proof. exact (@lem69 term11). Qed.
Lemma lem7213654 {_132349 : Type'} (h1 : term49 _132349) (h2 : term62) (h3 : term10) : term17.
Proof. exact (EQ_MP (@lem7213653) (@lem7213652 _132349 h1 h2 h3)). Qed.
Lemma lem7213655 {_132349 : Type'} (h1 : term62) (h2 : term10) : term20 _132349.
Proof. exact (fun h0 : term49 _132349 => @lem7213654 _132349 h0 h1 h2). Qed.
Lemma lem7213656 {_132349 : Type'} (h1 : term62) (h2 : term10) : term23 _132349.
Proof. exact (fun h0 : term54 => @lem7213655 _132349 h1 h2). Qed.
Lemma lem7213657 {_132349 : Type'} (h1 : term10) : term26 _132349.
Proof. exact (fun h0 : term62 => @lem7213656 _132349 h0 h1). Qed.
Lemma lem7213658 {_132349 : Type'} : term28 _132349.
Proof. exact (fun h0 : term10 => @lem7213657 _132349 h0). Qed.
Lemma lem7213659 {_132349 : Type'} : term12 _132349.
Proof. exact (EQ_MP (@lem7210846 _132349) (@lem7213658 _132349)). Qed.
Lemma lem7213661 {_132349 : Type'} : term12 _132349.
Proof. exact (@lem7210480 _132349 (@lem7213659 _132349)). Qed.
Lemma lem7213662 {_132349 : Type'} (h1 : term10) : term25 _132349.
Proof. exact (@lem7213661 _132349 (@lem7210463 h1)). Qed.
Lemma lem7213663 {_132349 : Type'} (h1 : term10) : term22 _132349.
Proof. exact (@lem7213662 _132349 h1 (@lem5371273)). Qed.
Lemma lem7213664 {_132349 : Type'} (h1 : term10) : term19 _132349.
Proof. exact (@lem7213663 _132349 h1 (@lem5329299)). Qed.
Lemma lem7213665 (h1 : term10) : term16.
Proof. exact (@lem7213664 Prop h1 (@lem7081239 Prop)). Qed.
Lemma lem7213666 (h1 : term10) : False.
Proof. exact (@lem7213665 h1 (@lem7210464)). Qed.
Lemma lem7213667 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem7213666 h1) (fun h2 : False => @lem7210463 h1)). Qed.
Lemma lem7213668 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem7213667 h1) (@lem7210463 h1)). Qed.
Lemma lem7213669 : term9.
Proof. exact (fun h0 : term10 => @lem7213668 h0). Qed.
Lemma lem7213670 : term8.
Proof. exact (EQ_MP (@lem7210462) (@lem7213669)). Qed.
