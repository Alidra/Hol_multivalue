Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_EQ_0_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_NUMSEG_spec.
Require Import IN_NUMSEG_spec.
Require Import SUM_POS_EQ_0_spec.
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
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Lemma lem7216413 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7216414 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7216415 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7216414 t1) (@lem7216413 t1)). Qed.
Lemma lem7216416 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7216415 t1 t2). Qed.
Lemma lem7216417 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7216418 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7216417 t1 t2) (@lem7216416 t1 t2)). Qed.
Lemma lem7216419 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7216418 t1 t2 t3). Qed.
Lemma lem7216420 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7216421 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7216420 t1 t2 t3) (@lem7216419 t1 t2 t3)). Qed.
Lemma lem7216422 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7216421 t1 t2 t3)). Qed.
Lemma lem7216424 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7216425 : term8 = term9.
Proof. exact (@lem7216424 term8). Qed.
Lemma lem7216426 : term9 = term8.
Proof. exact (SYM (@lem7216425)). Qed.
Lemma lem7216427 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7216428 : term11.
Proof. exact (@lem7114167 nat). Qed.
Lemma lem7216431 {_132718 : Type'} (h1 : term12 _132718) : term12 _132718.
Proof. exact (h1). Qed.
Lemma lem7216432 {_132718 : Type'} : term13 _132718.
Proof. exact (fun h0 : term12 _132718 => @lem7216431 _132718 h0). Qed.
Lemma lem7216433 {_132718 : Type'} (h1 : term13 _132718) : term13 _132718.
Proof. exact (h1). Qed.
Lemma lem7216434 {_132718 : Type'} (h1 : term12 _132718) : term12 _132718.
Proof. exact (h1). Qed.
Lemma lem7216435 {_132718 : Type'} (h1 : term12 _132718) (h2 : term13 _132718) : term12 _132718.
Proof. exact (@lem7216433 _132718 h2 (@lem7216434 _132718 h1)). Qed.
Lemma lem7216436 {_132718 : Type'} (h1 : term12 _132718) : term14 _132718.
Proof. exact (fun h0 : term13 _132718 => @lem7216435 _132718 h1 h0). Qed.
Lemma lem7216437 {_132718 : Type'} (h1 : term13 _132718) : term13 _132718.
Proof. exact (h1). Qed.
Lemma lem7216438 {_132718 : Type'} (h1 : term12 _132718) (h2 : term13 _132718) : term12 _132718.
Proof. exact (@lem7216436 _132718 h1 (@lem7216437 _132718 h2)). Qed.
Lemma lem7216439 {_132718 : Type'} (h1 : term13 _132718) : term13 _132718.
Proof. exact (fun h0 : term12 _132718 => @lem7216438 _132718 h0 h1). Qed.
Lemma lem7216440 {_132718 : Type'} : term15 _132718.
Proof. exact (fun h0 : term13 _132718 => @lem7216439 _132718 h0). Qed.
Lemma lem7216443 {_132718 : Type'} : term13 _132718.
Proof. exact (@lem7216440 _132718 (@lem7216432 _132718)). Qed.
Lemma lem7216444 {_132718 : Type'} : term13 _132718.
Proof. exact (@lem7216443 _132718). Qed.
Lemma lem7216534 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7216535 : term16 = term17.
Proof. exact (@lem7216534 term11). Qed.
Lemma lem7216562 {_132718 : Type'} : (term18 _132718) = (term18 _132718).
Proof. exact (eq_refl (term18 _132718)). Qed.
Lemma lem7216563 {_132718 : Type'} : (term19 _132718) = (term20 _132718).
Proof. exact (MK_COMB (@lem7216562 _132718) (@lem7216535)). Qed.
Lemma lem7216566 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7216567 {_132718 : Type'} : (term22 _132718) = (term23 _132718).
Proof. exact (MK_COMB (@lem7216566) (@lem7216563 _132718)). Qed.
Lemma lem7216570 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7216571 {_132718 : Type'} : (term25 _132718) = (term26 _132718).
Proof. exact (MK_COMB (@lem7216570) (@lem7216567 _132718)). Qed.
Lemma lem7216574 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem7216581 {_132718 : Type'} : (term12 _132718) = (term28 _132718).
Proof. exact (MK_COMB (@lem7216574) (@lem7216571 _132718)). Qed.
Lemma lem7216586 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term29 s f x) = (term29 s f x).
Proof. exact (eq_refl (term29 s f x)). Qed.
Lemma lem7216587 (s : nat -> Prop) (f : nat -> real) : (term30 s f) = (term30 s f).
Proof. exact (fun_ext (fun x : nat => @lem7216586 s f x)). Qed.
Lemma lem7216588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216589 (s : nat -> Prop) (f : nat -> real) : (term31 s f) = (term31 s f).
Proof. exact (MK_COMB (@lem7216588) (@lem7216587 s f)). Qed.
Lemma lem7216590 (s : nat -> Prop) (f : nat -> real) : ((@sum nat s f) = term32) = ((@sum nat s f) = term32).
Proof. exact (eq_refl ((@sum nat s f) = term32)). Qed.
Lemma lem7216595 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term33 s f x) = (term33 s f x).
Proof. exact (eq_refl (term33 s f x)). Qed.
Lemma lem7216596 (s : nat -> Prop) (f : nat -> real) : (term34 s f) = (term34 s f).
Proof. exact (fun_ext (fun x : nat => @lem7216595 s f x)). Qed.
Lemma lem7216597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216598 (s : nat -> Prop) (f : nat -> real) : (term35 s f) = (term35 s f).
Proof. exact (MK_COMB (@lem7216597) (@lem7216596 s f)). Qed.
Lemma lem7216599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216600 (s : nat -> Prop) (f : nat -> real) : (term36 s f) = (term36 s f).
Proof. exact (MK_COMB (@lem7216599) (@lem7216598 s f)). Qed.
Lemma lem7216601 (s : nat -> Prop) (f : nat -> real) : (term37 s f) = (term37 s f).
Proof. exact (MK_COMB (@lem7216600 s f) (@lem7216590 s f)). Qed.
Lemma lem7216604 (s : nat -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem7216605 (s : nat -> Prop) (f : nat -> real) : (term39 s f) = (term39 s f).
Proof. exact (MK_COMB (@lem7216604 s) (@lem7216601 s f)). Qed.
Lemma lem7216606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216607 (s : nat -> Prop) (f : nat -> real) : (term40 s f) = (term40 s f).
Proof. exact (MK_COMB (@lem7216606) (@lem7216605 s f)). Qed.
Lemma lem7216608 (s : nat -> Prop) (f : nat -> real) : (term41 s f) = (term41 s f).
Proof. exact (MK_COMB (@lem7216607 s f) (@lem7216589 s f)). Qed.
Lemma lem7216609 (f : nat -> real) : (term42 f) = (term42 f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7216608 s f)). Qed.
Lemma lem7216610 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7216611 (f : nat -> real) : (term43 f) = (term43 f).
Proof. exact (MK_COMB (@lem7216610) (@lem7216609 f)). Qed.
Lemma lem7216612 : term44 = term44.
Proof. exact (fun_ext (fun f : nat -> real => @lem7216611 f)). Qed.
Lemma lem7216613 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7216614 : term11 = term11.
Proof. exact (MK_COMB (@lem7216613) (@lem7216612)). Qed.
Lemma lem7216615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7216616 : term17 = term17.
Proof. exact (MK_COMB (@lem7216615) (@lem7216614)). Qed.
Lemma lem7216621 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term45 _132718 s f x) = (term45 _132718 s f x).
Proof. exact (eq_refl (term45 _132718 s f x)). Qed.
Lemma lem7216622 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term46 _132718 s f) = (term46 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7216621 _132718 s f x)). Qed.
Lemma lem7216623 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7216624 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term47 _132718 s f) = (term47 _132718 s f).
Proof. exact (MK_COMB (@lem7216623 _132718) (@lem7216622 _132718 s f)). Qed.
Lemma lem7216625 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((@sum _132718 s f) = term32) = ((@sum _132718 s f) = term32).
Proof. exact (eq_refl ((@sum _132718 s f) = term32)). Qed.
Lemma lem7216630 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term48 _132718 s f x) = (term48 _132718 s f x).
Proof. exact (eq_refl (term48 _132718 s f x)). Qed.
Lemma lem7216631 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term49 _132718 s f) = (term49 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7216630 _132718 s f x)). Qed.
Lemma lem7216632 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7216633 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term50 _132718 s f) = (term50 _132718 s f).
Proof. exact (MK_COMB (@lem7216632 _132718) (@lem7216631 _132718 s f)). Qed.
Lemma lem7216634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216635 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term51 _132718 s f) = (term51 _132718 s f).
Proof. exact (MK_COMB (@lem7216634) (@lem7216633 _132718 s f)). Qed.
Lemma lem7216636 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term52 _132718 s f) = (term52 _132718 s f).
Proof. exact (MK_COMB (@lem7216635 _132718 s f) (@lem7216625 _132718 s f)). Qed.
Lemma lem7216639 {_132718 : Type'} (s : _132718 -> Prop) : (term53 _132718 s) = (term53 _132718 s).
Proof. exact (eq_refl (term53 _132718 s)). Qed.
Lemma lem7216640 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term54 _132718 s f) = (term54 _132718 s f).
Proof. exact (MK_COMB (@lem7216639 _132718 s) (@lem7216636 _132718 s f)). Qed.
Lemma lem7216641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216642 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term55 _132718 s f) = (term55 _132718 s f).
Proof. exact (MK_COMB (@lem7216641) (@lem7216640 _132718 s f)). Qed.
Lemma lem7216643 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term56 _132718 s f) = (term56 _132718 s f).
Proof. exact (MK_COMB (@lem7216642 _132718 s f) (@lem7216624 _132718 s f)). Qed.
Lemma lem7216644 {_132718 : Type'} (f : _132718 -> real) : (term57 _132718 f) = (term57 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7216643 _132718 s f)). Qed.
Lemma lem7216645 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7216646 {_132718 : Type'} (f : _132718 -> real) : (term58 _132718 f) = (term58 _132718 f).
Proof. exact (MK_COMB (@lem7216645 _132718) (@lem7216644 _132718 f)). Qed.
Lemma lem7216647 {_132718 : Type'} : (term59 _132718) = (term59 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7216646 _132718 f)). Qed.
Lemma lem7216648 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7216649 {_132718 : Type'} : (term60 _132718) = (term60 _132718).
Proof. exact (MK_COMB (@lem7216648 _132718) (@lem7216647 _132718)). Qed.
Lemma lem7216650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216651 {_132718 : Type'} : (term18 _132718) = (term18 _132718).
Proof. exact (MK_COMB (@lem7216650) (@lem7216649 _132718)). Qed.
Lemma lem7216652 {_132718 : Type'} : (term20 _132718) = (term20 _132718).
Proof. exact (MK_COMB (@lem7216651 _132718) (@lem7216616)). Qed.
Lemma lem7216653 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem7216654 (m : nat) : (term62 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem7216653 m n)). Qed.
Lemma lem7216655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216656 (m : nat) : (term63 m) = (term63 m).
Proof. exact (MK_COMB (@lem7216655) (@lem7216654 m)). Qed.
Lemma lem7216657 : term64 = term64.
Proof. exact (fun_ext (fun m : nat => @lem7216656 m)). Qed.
Lemma lem7216658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216659 : term65 = term65.
Proof. exact (MK_COMB (@lem7216658) (@lem7216657)). Qed.
Lemma lem7216660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216661 : term21 = term21.
Proof. exact (MK_COMB (@lem7216660) (@lem7216659)). Qed.
Lemma lem7216662 {_132718 : Type'} : (term23 _132718) = (term23 _132718).
Proof. exact (MK_COMB (@lem7216661) (@lem7216652 _132718)). Qed.
Lemma lem7216671 (m : nat) (p : nat) (n : nat) : ((term66 p m n) = (term67 m p n)) = ((term66 p m n) = (term67 m p n)).
Proof. exact (eq_refl ((term66 p m n) = (term67 m p n))). Qed.
Lemma lem7216672 (m : nat) (n : nat) : (term68 m n) = (term68 m n).
Proof. exact (fun_ext (fun p : nat => @lem7216671 m p n)). Qed.
Lemma lem7216673 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216674 (m : nat) (n : nat) : (term69 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem7216673) (@lem7216672 m n)). Qed.
Lemma lem7216675 (m : nat) : (term70 m) = (term70 m).
Proof. exact (fun_ext (fun n : nat => @lem7216674 m n)). Qed.
Lemma lem7216676 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216677 (m : nat) : (term71 m) = (term71 m).
Proof. exact (MK_COMB (@lem7216676) (@lem7216675 m)). Qed.
Lemma lem7216678 : term72 = term72.
Proof. exact (fun_ext (fun m : nat => @lem7216677 m)). Qed.
Lemma lem7216679 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216680 : term73 = term73.
Proof. exact (MK_COMB (@lem7216679) (@lem7216678)). Qed.
Lemma lem7216681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216682 : term24 = term24.
Proof. exact (MK_COMB (@lem7216681) (@lem7216680)). Qed.
Lemma lem7216683 {_132718 : Type'} : (term26 _132718) = (term26 _132718).
Proof. exact (MK_COMB (@lem7216682) (@lem7216662 _132718)). Qed.
Lemma lem7216692 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term74 m n f p) = (term74 m n f p).
Proof. exact (eq_refl (term74 m n f p)). Qed.
Lemma lem7216693 (m : nat) (n : nat) (f : nat -> real) : (term75 m n f) = (term75 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7216692 m n f p)). Qed.
Lemma lem7216694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216695 (m : nat) (n : nat) (f : nat -> real) : (term76 m n f) = (term76 m n f).
Proof. exact (MK_COMB (@lem7216694) (@lem7216693 m n f)). Qed.
Lemma lem7216696 (m : nat) (n : nat) (f : nat -> real) : ((term77 m n f) = term32) = ((term77 m n f) = term32).
Proof. exact (eq_refl ((term77 m n f) = term32)). Qed.
Lemma lem7216705 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term78 m n f p) = (term78 m n f p).
Proof. exact (eq_refl (term78 m n f p)). Qed.
Lemma lem7216706 (m : nat) (n : nat) (f : nat -> real) : (term79 m n f) = (term79 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7216705 m n f p)). Qed.
Lemma lem7216707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216708 (m : nat) (n : nat) (f : nat -> real) : (term80 m n f) = (term80 m n f).
Proof. exact (MK_COMB (@lem7216707) (@lem7216706 m n f)). Qed.
Lemma lem7216709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216710 (m : nat) (n : nat) (f : nat -> real) : (term81 m n f) = (term81 m n f).
Proof. exact (MK_COMB (@lem7216709) (@lem7216708 m n f)). Qed.
Lemma lem7216711 (m : nat) (n : nat) (f : nat -> real) : (term82 m n f) = (term82 m n f).
Proof. exact (MK_COMB (@lem7216710 m n f) (@lem7216696 m n f)). Qed.
Lemma lem7216712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216713 (m : nat) (n : nat) (f : nat -> real) : (term83 m n f) = (term83 m n f).
Proof. exact (MK_COMB (@lem7216712) (@lem7216711 m n f)). Qed.
Lemma lem7216714 (m : nat) (n : nat) (f : nat -> real) : (term84 m n f) = (term84 m n f).
Proof. exact (MK_COMB (@lem7216713 m n f) (@lem7216695 m n f)). Qed.
Lemma lem7216715 (m : nat) (f : nat -> real) : (term85 m f) = (term85 m f).
Proof. exact (fun_ext (fun n : nat => @lem7216714 m n f)). Qed.
Lemma lem7216716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216717 (m : nat) (f : nat -> real) : (term86 m f) = (term86 m f).
Proof. exact (MK_COMB (@lem7216716) (@lem7216715 m f)). Qed.
Lemma lem7216718 (f : nat -> real) : (term87 f) = (term87 f).
Proof. exact (fun_ext (fun m : nat => @lem7216717 m f)). Qed.
Lemma lem7216719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216720 (f : nat -> real) : (term88 f) = (term88 f).
Proof. exact (MK_COMB (@lem7216719) (@lem7216718 f)). Qed.
Lemma lem7216721 : term89 = term89.
Proof. exact (fun_ext (fun f : nat -> real => @lem7216720 f)). Qed.
Lemma lem7216722 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7216723 : term8 = term8.
Proof. exact (MK_COMB (@lem7216722) (@lem7216721)). Qed.
Lemma lem7216724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7216725 : term10 = term10.
Proof. exact (MK_COMB (@lem7216724) (@lem7216723)). Qed.
Lemma lem7216726 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216727 : term27 = term27.
Proof. exact (MK_COMB (@lem7216726) (@lem7216725)). Qed.
Lemma lem7216728 {_132718 : Type'} : (term28 _132718) = (term28 _132718).
Proof. exact (MK_COMB (@lem7216727) (@lem7216683 _132718)). Qed.
Lemma lem7216881 {_132718 : Type'} : (term12 _132718) = (term28 _132718).
Proof. exact (TRANS (@lem7216581 _132718) (@lem7216728 _132718)). Qed.
Lemma lem7216882 {_132718 : Type'} : (term28 _132718) = (term12 _132718).
Proof. exact (SYM (@lem7216881 _132718)). Qed.
Lemma lem7216883 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7216884 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem7216885 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem7216886 {_132718 : Type'} (h1 : term60 _132718) : term60 _132718.
Proof. exact (h1). Qed.
Lemma lem7216887 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7216894 (m : nat) (p : nat) (n : nat) : (term90 m p n) = (term91 m p n).
Proof. exact (@lem17045 (Peano.le m p) (Peano.le p n)). Qed.
Lemma lem7216895 (f : nat -> real) (p : nat) : (term92 f p) = (term92 f p).
Proof. exact (eq_refl (term92 f p)). Qed.
Lemma lem7216896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7216897 (m : nat) (p : nat) (n : nat) : (term93 m p n) = (term94 m p n).
Proof. exact (MK_COMB (@lem7216896) (@lem7216894 m p n)). Qed.
Lemma lem7216898 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term95 m n f p) = (term96 m n f p).
Proof. exact (MK_COMB (@lem7216897 m p n) (@lem7216895 f p)). Qed.
Lemma lem7216899 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term78 m n f p) = (term95 m n f p).
Proof. exact (@lem17265 (term67 m p n) (term92 f p)). Qed.
Lemma lem7216900 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term78 m n f p) = (term96 m n f p).
Proof. exact (TRANS (@lem7216899 m n f p) (@lem7216898 m n f p)). Qed.
Lemma lem7216901 (m : nat) (n : nat) (f : nat -> real) : (term79 m n f) = (term97 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7216900 m n f p)). Qed.
Lemma lem7216902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216903 (m : nat) (n : nat) (f : nat -> real) : (term80 m n f) = (term98 m n f).
Proof. exact (MK_COMB (@lem7216902) (@lem7216901 m n f)). Qed.
Lemma lem7216904 (m : nat) (n : nat) (f : nat -> real) : ((term77 m n f) = term32) = ((term77 m n f) = term32).
Proof. exact (eq_refl ((term77 m n f) = term32)). Qed.
Lemma lem7216905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216906 (m : nat) (n : nat) (f : nat -> real) : (term81 m n f) = (term99 m n f).
Proof. exact (MK_COMB (@lem7216905) (@lem7216903 m n f)). Qed.
Lemma lem7216907 (m : nat) (n : nat) (f : nat -> real) : (term82 m n f) = (term100 m n f).
Proof. exact (MK_COMB (@lem7216906 m n f) (@lem7216904 m n f)). Qed.
Lemma lem7216918 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term101 m n f p) = (term102 m n f p).
Proof. exact (@lem17362 (term67 m p n) ((f p) = term32)). Qed.
Lemma lem7216919 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7216920 (m : nat) (n : nat) (f : nat -> real) : (term105 m n f) = (term106 m n f).
Proof. exact (@lem7216919 (term75 m n f)). Qed.
Lemma lem7216921 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term107 m n f p) = (term74 m n f p).
Proof. exact (eq_refl (term107 m n f p)). Qed.
Lemma lem7216922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7216923 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term108 m n f p) = (term101 m n f p).
Proof. exact (MK_COMB (@lem7216922) (@lem7216921 m n f p)). Qed.
Lemma lem7216924 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term108 m n f p) = (term102 m n f p).
Proof. exact (TRANS (@lem7216923 m n f p) (@lem7216918 m n f p)). Qed.
Lemma lem7216925 (m : nat) (n : nat) (f : nat -> real) : (term109 m n f) = (term110 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7216924 m n f p)). Qed.
Lemma lem7216926 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7216927 (m : nat) (n : nat) (f : nat -> real) : (term106 m n f) = (term111 m n f).
Proof. exact (MK_COMB (@lem7216926) (@lem7216925 m n f)). Qed.
Lemma lem7216928 (m : nat) (n : nat) (f : nat -> real) : (term105 m n f) = (term111 m n f).
Proof. exact (TRANS (@lem7216920 m n f) (@lem7216927 m n f)). Qed.
Lemma lem7216929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216930 (m : nat) (n : nat) (f : nat -> real) : (term112 m n f) = (term113 m n f).
Proof. exact (MK_COMB (@lem7216929) (@lem7216907 m n f)). Qed.
Lemma lem7216931 (m : nat) (n : nat) (f : nat -> real) : (term114 m n f) = (term115 m n f).
Proof. exact (MK_COMB (@lem7216930 m n f) (@lem7216928 m n f)). Qed.
Lemma lem7216932 (m : nat) (n : nat) (f : nat -> real) : (term116 m n f) = (term114 m n f).
Proof. exact (@lem17362 (term82 m n f) (term76 m n f)). Qed.
Lemma lem7216933 (m : nat) (n : nat) (f : nat -> real) : (term116 m n f) = (term115 m n f).
Proof. exact (TRANS (@lem7216932 m n f) (@lem7216931 m n f)). Qed.
Lemma lem7216934 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7216935 (m : nat) (f : nat -> real) : (term117 m f) = (term118 m f).
Proof. exact (@lem7216934 (term85 m f)). Qed.
Lemma lem7216936 (m : nat) (n : nat) (f : nat -> real) : (term119 m f n) = (term84 m n f).
Proof. exact (eq_refl (term119 m f n)). Qed.
Lemma lem7216937 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7216938 (m : nat) (n : nat) (f : nat -> real) : (term120 m f n) = (term116 m n f).
Proof. exact (MK_COMB (@lem7216937) (@lem7216936 m n f)). Qed.
Lemma lem7216939 (m : nat) (n : nat) (f : nat -> real) : (term120 m f n) = (term115 m n f).
Proof. exact (TRANS (@lem7216938 m n f) (@lem7216933 m n f)). Qed.
Lemma lem7216940 (m : nat) (f : nat -> real) : (term121 m f) = (term122 m f).
Proof. exact (fun_ext (fun n : nat => @lem7216939 m n f)). Qed.
Lemma lem7216941 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7216942 (m : nat) (f : nat -> real) : (term118 m f) = (term123 m f).
Proof. exact (MK_COMB (@lem7216941) (@lem7216940 m f)). Qed.
Lemma lem7216943 (m : nat) (f : nat -> real) : (term117 m f) = (term123 m f).
Proof. exact (TRANS (@lem7216935 m f) (@lem7216942 m f)). Qed.
Lemma lem7216944 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7216945 (f : nat -> real) : (term124 f) = (term125 f).
Proof. exact (@lem7216944 (term87 f)). Qed.
Lemma lem7216946 (m : nat) (f : nat -> real) : (term126 f m) = (term86 m f).
Proof. exact (eq_refl (term126 f m)). Qed.
Lemma lem7216947 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7216948 (m : nat) (f : nat -> real) : (term127 f m) = (term117 m f).
Proof. exact (MK_COMB (@lem7216947) (@lem7216946 m f)). Qed.
Lemma lem7216949 (m : nat) (f : nat -> real) : (term127 f m) = (term123 m f).
Proof. exact (TRANS (@lem7216948 m f) (@lem7216943 m f)). Qed.
Lemma lem7216950 (f : nat -> real) : (term128 f) = (term129 f).
Proof. exact (fun_ext (fun m : nat => @lem7216949 m f)). Qed.
Lemma lem7216951 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7216952 (f : nat -> real) : (term125 f) = (term130 f).
Proof. exact (MK_COMB (@lem7216951) (@lem7216950 f)). Qed.
Lemma lem7216953 (f : nat -> real) : (term124 f) = (term130 f).
Proof. exact (TRANS (@lem7216945 f) (@lem7216952 f)). Qed.
Lemma lem7216954 (P : type1010) : (term131 P) = (term132 P).
Proof. exact (@lem18392 (nat -> real) P). Qed.
Lemma lem7216955 : term10 = term133.
Proof. exact (@lem7216954 term89). Qed.
Lemma lem7216956 (f : nat -> real) : (term134 f) = (term88 f).
Proof. exact (eq_refl (term134 f)). Qed.
Lemma lem7216957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7216958 (f : nat -> real) : (term135 f) = (term124 f).
Proof. exact (MK_COMB (@lem7216957) (@lem7216956 f)). Qed.
Lemma lem7216959 (f : nat -> real) : (term135 f) = (term130 f).
Proof. exact (TRANS (@lem7216958 f) (@lem7216953 f)). Qed.
Lemma lem7216960 : term136 = term137.
Proof. exact (fun_ext (fun f : nat -> real => @lem7216959 f)). Qed.
Lemma lem7216961 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7216962 : term133 = term138.
Proof. exact (MK_COMB (@lem7216961) (@lem7216960)). Qed.
Lemma lem7216963 : term10 = term138.
Proof. exact (TRANS (@lem7216955) (@lem7216962)). Qed.
Lemma lem7217118 {A : Type'} (P : Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7217119 (P : Prop) (Q : nat -> Prop) : (term141 P Q) = (term142 P Q).
Proof. exact (@lem7217118 nat P Q). Qed.
Lemma lem7217120 (m : nat) (n : nat) (f : nat -> real) : (term143 m n f) = (term144 m n f).
Proof. exact (@lem7217119 (term100 m n f) (term110 m n f)). Qed.
Lemma lem7217121 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term145 m n f p) = (term102 m n f p).
Proof. exact (eq_refl (term145 m n f p)). Qed.
Lemma lem7217122 (m : nat) (n : nat) (f : nat -> real) : (term146 m n f) = (term110 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7217121 m n f p)). Qed.
Lemma lem7217123 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7217124 (m : nat) (n : nat) (f : nat -> real) : (term147 m n f) = (term111 m n f).
Proof. exact (MK_COMB (@lem7217123) (@lem7217122 m n f)). Qed.
Lemma lem7217125 (m : nat) (n : nat) (f : nat -> real) : (term113 m n f) = (term113 m n f).
Proof. exact (eq_refl (term113 m n f)). Qed.
Lemma lem7217126 (m : nat) (n : nat) (f : nat -> real) : (term143 m n f) = (term115 m n f).
Proof. exact (MK_COMB (@lem7217125 m n f) (@lem7217124 m n f)). Qed.
Lemma lem7217127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217128 (m : nat) (n : nat) (f : nat -> real) : (term148 m n f) = (term149 m n f).
Proof. exact (MK_COMB (@lem7217127) (@lem7217126 m n f)). Qed.
Lemma lem7217129 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term145 m n f p) = (term102 m n f p).
Proof. exact (eq_refl (term145 m n f p)). Qed.
Lemma lem7217130 (m : nat) (n : nat) (f : nat -> real) : (term113 m n f) = (term113 m n f).
Proof. exact (eq_refl (term113 m n f)). Qed.
Lemma lem7217131 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term150 m n f p) = (term151 m n f p).
Proof. exact (MK_COMB (@lem7217130 m n f) (@lem7217129 m n f p)). Qed.
Lemma lem7217132 (m : nat) (n : nat) (f : nat -> real) : (term152 m n f) = (term153 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7217131 m n f p)). Qed.
Lemma lem7217133 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7217134 (m : nat) (n : nat) (f : nat -> real) : (term144 m n f) = (term154 m n f).
Proof. exact (MK_COMB (@lem7217133) (@lem7217132 m n f)). Qed.
Lemma lem7217135 (m : nat) (n : nat) (f : nat -> real) : ((term143 m n f) = (term144 m n f)) = ((term115 m n f) = (term154 m n f)).
Proof. exact (MK_COMB (@lem7217128 m n f) (@lem7217134 m n f)). Qed.
Lemma lem7217136 (m : nat) (n : nat) (f : nat -> real) : (term115 m n f) = (term154 m n f).
Proof. exact (EQ_MP (@lem7217135 m n f) (@lem7217120 m n f)). Qed.
Lemma lem7217137 (m : nat) (f : nat -> real) : (term122 m f) = (term155 m f).
Proof. exact (fun_ext (fun n : nat => @lem7217136 m n f)). Qed.
Lemma lem7217138 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7217139 (m : nat) (f : nat -> real) : (term123 m f) = (term156 m f).
Proof. exact (MK_COMB (@lem7217138) (@lem7217137 m f)). Qed.
Lemma lem7217140 (f : nat -> real) : (term129 f) = (term157 f).
Proof. exact (fun_ext (fun m : nat => @lem7217139 m f)). Qed.
Lemma lem7217141 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7217142 (f : nat -> real) : (term130 f) = (term158 f).
Proof. exact (MK_COMB (@lem7217141) (@lem7217140 f)). Qed.
Lemma lem7217143 : term137 = term159.
Proof. exact (fun_ext (fun f : nat -> real => @lem7217142 f)). Qed.
Lemma lem7217144 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7217146 : term138 = term160.
Proof. exact (MK_COMB (@lem7217144) (@lem7217143)). Qed.
Lemma lem7217147 : term10 = term160.
Proof. exact (TRANS (@lem7216963) (@lem7217146)). Qed.
Lemma lem7217148 (h1 : term10) : term160.
Proof. exact (EQ_MP (@lem7217147) (@lem7216883 h1)). Qed.
Lemma lem7217159 (m : nat) (p : nat) (n : nat) : (term90 m p n) = (term91 m p n).
Proof. exact (@lem17045 (Peano.le m p) (Peano.le p n)). Qed.
Lemma lem7217165 (m : nat) (p : nat) (n : nat) : (term161 m p n) = (term161 m p n).
Proof. exact (eq_refl (term161 m p n)). Qed.
Lemma lem7217167 (p : nat) (m : nat) (n : nat) : (term162 p m n) = (term162 p m n).
Proof. exact (eq_refl (term162 p m n)). Qed.
Lemma lem7217168 (m : nat) (p : nat) (n : nat) : (term163 m p n) = (term164 m p n).
Proof. exact (MK_COMB (@lem7217167 p m n) (@lem7217159 m p n)). Qed.
Lemma lem7217169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217170 (m : nat) (p : nat) (n : nat) : (term165 m p n) = (term166 m p n).
Proof. exact (MK_COMB (@lem7217169) (@lem7217168 m p n)). Qed.
Lemma lem7217171 (m : nat) (p : nat) (n : nat) : (term167 m p n) = (term168 m p n).
Proof. exact (MK_COMB (@lem7217170 m p n) (@lem7217165 m p n)). Qed.
Lemma lem7217172 (m : nat) (p : nat) (n : nat) : ((term66 p m n) = (term67 m p n)) = (term167 m p n).
Proof. exact (@lem17784 (term66 p m n) (term67 m p n)). Qed.
Lemma lem7217173 (m : nat) (p : nat) (n : nat) : ((term66 p m n) = (term67 m p n)) = (term168 m p n).
Proof. exact (TRANS (@lem7217172 m p n) (@lem7217171 m p n)). Qed.
Lemma lem7217174 (m : nat) (n : nat) : (term68 m n) = (term169 m n).
Proof. exact (fun_ext (fun p : nat => @lem7217173 m p n)). Qed.
Lemma lem7217175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217176 (m : nat) (n : nat) : (term69 m n) = (term170 m n).
Proof. exact (MK_COMB (@lem7217175) (@lem7217174 m n)). Qed.
Lemma lem7217177 (m : nat) : (term70 m) = (term171 m).
Proof. exact (fun_ext (fun n : nat => @lem7217176 m n)). Qed.
Lemma lem7217178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217179 (m : nat) : (term71 m) = (term172 m).
Proof. exact (MK_COMB (@lem7217178) (@lem7217177 m)). Qed.
Lemma lem7217180 : term72 = term173.
Proof. exact (fun_ext (fun m : nat => @lem7217179 m)). Qed.
Lemma lem7217181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217182 : term73 = term174.
Proof. exact (MK_COMB (@lem7217181) (@lem7217180)). Qed.
Lemma lem7217192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7217193 (P : nat -> Prop) (Q : nat -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem7217192 nat P Q). Qed.
Lemma lem7217194 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (@lem7217193 (term181 m n) (term182 m n)). Qed.
Lemma lem7217195 (m : nat) (p : nat) (n : nat) : (term183 m n p) = (term164 m p n).
Proof. exact (eq_refl (term183 m n p)). Qed.
Lemma lem7217196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217197 (m : nat) (p : nat) (n : nat) : (term184 m n p) = (term166 m p n).
Proof. exact (MK_COMB (@lem7217196) (@lem7217195 m p n)). Qed.
Lemma lem7217198 (m : nat) (p : nat) (n : nat) : (term185 m n p) = (term161 m p n).
Proof. exact (eq_refl (term185 m n p)). Qed.
Lemma lem7217199 (m : nat) (p : nat) (n : nat) : (term186 m n p) = (term168 m p n).
Proof. exact (MK_COMB (@lem7217197 m p n) (@lem7217198 m p n)). Qed.
Lemma lem7217200 (m : nat) (n : nat) : (term187 m n) = (term169 m n).
Proof. exact (fun_ext (fun p : nat => @lem7217199 m p n)). Qed.
Lemma lem7217201 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217202 (m : nat) (n : nat) : (term179 m n) = (term170 m n).
Proof. exact (MK_COMB (@lem7217201) (@lem7217200 m n)). Qed.
Lemma lem7217203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217204 (m : nat) (n : nat) : (term188 m n) = (term189 m n).
Proof. exact (MK_COMB (@lem7217203) (@lem7217202 m n)). Qed.
Lemma lem7217205 (m : nat) (p : nat) (n : nat) : (term183 m n p) = (term164 m p n).
Proof. exact (eq_refl (term183 m n p)). Qed.
Lemma lem7217206 (m : nat) (n : nat) : (term190 m n) = (term181 m n).
Proof. exact (fun_ext (fun p : nat => @lem7217205 m p n)). Qed.
Lemma lem7217207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217208 (m : nat) (n : nat) : (term191 m n) = (term192 m n).
Proof. exact (MK_COMB (@lem7217207) (@lem7217206 m n)). Qed.
Lemma lem7217209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217210 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (MK_COMB (@lem7217209) (@lem7217208 m n)). Qed.
Lemma lem7217211 (m : nat) (p : nat) (n : nat) : (term185 m n p) = (term161 m p n).
Proof. exact (eq_refl (term185 m n p)). Qed.
Lemma lem7217212 (m : nat) (n : nat) : (term195 m n) = (term182 m n).
Proof. exact (fun_ext (fun p : nat => @lem7217211 m p n)). Qed.
Lemma lem7217213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217214 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (MK_COMB (@lem7217213) (@lem7217212 m n)). Qed.
Lemma lem7217215 (m : nat) (n : nat) : (term180 m n) = (term198 m n).
Proof. exact (MK_COMB (@lem7217210 m n) (@lem7217214 m n)). Qed.
Lemma lem7217216 (m : nat) (n : nat) : ((term179 m n) = (term180 m n)) = ((term170 m n) = (term198 m n)).
Proof. exact (MK_COMB (@lem7217204 m n) (@lem7217215 m n)). Qed.
Lemma lem7217217 (m : nat) (n : nat) : (term170 m n) = (term198 m n).
Proof. exact (EQ_MP (@lem7217216 m n) (@lem7217194 m n)). Qed.
Lemma lem7217314 (m : nat) : (term171 m) = (term199 m).
Proof. exact (fun_ext (fun n : nat => @lem7217217 m n)). Qed.
Lemma lem7217315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217316 (m : nat) : (term172 m) = (term200 m).
Proof. exact (MK_COMB (@lem7217315) (@lem7217314 m)). Qed.
Lemma lem7217318 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7217319 (P : nat -> Prop) (Q : nat -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem7217318 nat P Q). Qed.
Lemma lem7217320 (m : nat) : (term201 m) = (term202 m).
Proof. exact (@lem7217319 (term203 m) (term204 m)). Qed.
Lemma lem7217321 (m : nat) (n : nat) : (term205 m n) = (term192 m n).
Proof. exact (eq_refl (term205 m n)). Qed.
Lemma lem7217322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217323 (m : nat) (n : nat) : (term206 m n) = (term194 m n).
Proof. exact (MK_COMB (@lem7217322) (@lem7217321 m n)). Qed.
Lemma lem7217324 (m : nat) (n : nat) : (term207 m n) = (term197 m n).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem7217325 (m : nat) (n : nat) : (term208 m n) = (term198 m n).
Proof. exact (MK_COMB (@lem7217323 m n) (@lem7217324 m n)). Qed.
Lemma lem7217326 (m : nat) : (term209 m) = (term199 m).
Proof. exact (fun_ext (fun n : nat => @lem7217325 m n)). Qed.
Lemma lem7217327 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217328 (m : nat) : (term201 m) = (term200 m).
Proof. exact (MK_COMB (@lem7217327) (@lem7217326 m)). Qed.
Lemma lem7217329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217330 (m : nat) : (term210 m) = (term211 m).
Proof. exact (MK_COMB (@lem7217329) (@lem7217328 m)). Qed.
Lemma lem7217331 (m : nat) (n : nat) : (term205 m n) = (term192 m n).
Proof. exact (eq_refl (term205 m n)). Qed.
Lemma lem7217332 (m : nat) : (term212 m) = (term203 m).
Proof. exact (fun_ext (fun n : nat => @lem7217331 m n)). Qed.
Lemma lem7217333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217334 (m : nat) : (term213 m) = (term214 m).
Proof. exact (MK_COMB (@lem7217333) (@lem7217332 m)). Qed.
Lemma lem7217335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217336 (m : nat) : (term215 m) = (term216 m).
Proof. exact (MK_COMB (@lem7217335) (@lem7217334 m)). Qed.
Lemma lem7217337 (m : nat) (n : nat) : (term207 m n) = (term197 m n).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem7217338 (m : nat) : (term217 m) = (term204 m).
Proof. exact (fun_ext (fun n : nat => @lem7217337 m n)). Qed.
Lemma lem7217339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217340 (m : nat) : (term218 m) = (term219 m).
Proof. exact (MK_COMB (@lem7217339) (@lem7217338 m)). Qed.
Lemma lem7217341 (m : nat) : (term202 m) = (term220 m).
Proof. exact (MK_COMB (@lem7217336 m) (@lem7217340 m)). Qed.
Lemma lem7217342 (m : nat) : ((term201 m) = (term202 m)) = ((term200 m) = (term220 m)).
Proof. exact (MK_COMB (@lem7217330 m) (@lem7217341 m)). Qed.
Lemma lem7217343 (m : nat) : (term200 m) = (term220 m).
Proof. exact (EQ_MP (@lem7217342 m) (@lem7217320 m)). Qed.
Lemma lem7217448 (m : nat) : (term172 m) = (term220 m).
Proof. exact (TRANS (@lem7217316 m) (@lem7217343 m)). Qed.
Lemma lem7217449 : term173 = term221.
Proof. exact (fun_ext (fun m : nat => @lem7217448 m)). Qed.
Lemma lem7217450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217451 : term174 = term222.
Proof. exact (MK_COMB (@lem7217450) (@lem7217449)). Qed.
Lemma lem7217453 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7217454 (P : nat -> Prop) (Q : nat -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem7217453 nat P Q). Qed.
Lemma lem7217455 : term223 = term224.
Proof. exact (@lem7217454 term225 term226). Qed.
Lemma lem7217456 (m : nat) : (term227 m) = (term214 m).
Proof. exact (eq_refl (term227 m)). Qed.
Lemma lem7217457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217458 (m : nat) : (term228 m) = (term216 m).
Proof. exact (MK_COMB (@lem7217457) (@lem7217456 m)). Qed.
Lemma lem7217459 (m : nat) : (term229 m) = (term219 m).
Proof. exact (eq_refl (term229 m)). Qed.
Lemma lem7217460 (m : nat) : (term230 m) = (term220 m).
Proof. exact (MK_COMB (@lem7217458 m) (@lem7217459 m)). Qed.
Lemma lem7217461 : term231 = term221.
Proof. exact (fun_ext (fun m : nat => @lem7217460 m)). Qed.
Lemma lem7217462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217463 : term223 = term222.
Proof. exact (MK_COMB (@lem7217462) (@lem7217461)). Qed.
Lemma lem7217464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217465 : term232 = term233.
Proof. exact (MK_COMB (@lem7217464) (@lem7217463)). Qed.
Lemma lem7217466 (m : nat) : (term227 m) = (term214 m).
Proof. exact (eq_refl (term227 m)). Qed.
Lemma lem7217467 : term234 = term225.
Proof. exact (fun_ext (fun m : nat => @lem7217466 m)). Qed.
Lemma lem7217468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217469 : term235 = term236.
Proof. exact (MK_COMB (@lem7217468) (@lem7217467)). Qed.
Lemma lem7217470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7217471 : term237 = term238.
Proof. exact (MK_COMB (@lem7217470) (@lem7217469)). Qed.
Lemma lem7217472 (m : nat) : (term229 m) = (term219 m).
Proof. exact (eq_refl (term229 m)). Qed.
Lemma lem7217473 : term239 = term226.
Proof. exact (fun_ext (fun m : nat => @lem7217472 m)). Qed.
Lemma lem7217474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217475 : term240 = term241.
Proof. exact (MK_COMB (@lem7217474) (@lem7217473)). Qed.
Lemma lem7217476 : term224 = term242.
Proof. exact (MK_COMB (@lem7217471) (@lem7217475)). Qed.
Lemma lem7217477 : (term223 = term224) = (term222 = term242).
Proof. exact (MK_COMB (@lem7217465) (@lem7217476)). Qed.
Lemma lem7217478 : term222 = term242.
Proof. exact (EQ_MP (@lem7217477) (@lem7217455)). Qed.
Lemma lem7217593 : term174 = term242.
Proof. exact (TRANS (@lem7217451) (@lem7217478)). Qed.
Lemma lem7217594 : term73 = term242.
Proof. exact (TRANS (@lem7217182) (@lem7217593)). Qed.
Lemma lem7217595 (h1 : term73) : term242.
Proof. exact (EQ_MP (@lem7217594) (@lem7216884 h1)). Qed.
Lemma lem7217596 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem7217597 (m : nat) : (term62 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem7217596 m n)). Qed.
Lemma lem7217598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217599 (m : nat) : (term63 m) = (term63 m).
Proof. exact (MK_COMB (@lem7217598) (@lem7217597 m)). Qed.
Lemma lem7217600 : term64 = term64.
Proof. exact (fun_ext (fun m : nat => @lem7217599 m)). Qed.
Lemma lem7217601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7217614 : term65 = term65.
Proof. exact (MK_COMB (@lem7217601) (@lem7217600)). Qed.
Lemma lem7217615 (h1 : term65) : term65.
Proof. exact (EQ_MP (@lem7217614) (@lem7216885 h1)). Qed.
Lemma lem7217623 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term243 _132718 s f x) = (term244 _132718 s f x).
Proof. exact (@lem17362 (@IN _132718 x s) (term245 _132718 f x)). Qed.
Lemma lem7217624 {_132718 : Type'} (P : _132718 -> Prop) : (term246 _132718 P) = (term247 _132718 P).
Proof. exact (@lem18392 _132718 P). Qed.
Lemma lem7217625 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term248 _132718 s f) = (term249 _132718 s f).
Proof. exact (@lem7217624 _132718 (term49 _132718 s f)). Qed.
Lemma lem7217626 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term250 _132718 s f x) = (term48 _132718 s f x).
Proof. exact (eq_refl (term250 _132718 s f x)). Qed.
Lemma lem7217627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7217628 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term251 _132718 s f x) = (term243 _132718 s f x).
Proof. exact (MK_COMB (@lem7217627) (@lem7217626 _132718 s f x)). Qed.
Lemma lem7217629 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term251 _132718 s f x) = (term244 _132718 s f x).
Proof. exact (TRANS (@lem7217628 _132718 s f x) (@lem7217623 _132718 s f x)). Qed.
Lemma lem7217630 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term252 _132718 s f) = (term253 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217629 _132718 s f x)). Qed.
Lemma lem7217631 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217632 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term249 _132718 s f) = (term254 _132718 s f).
Proof. exact (MK_COMB (@lem7217631 _132718) (@lem7217630 _132718 s f)). Qed.
Lemma lem7217633 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term248 _132718 s f) = (term254 _132718 s f).
Proof. exact (TRANS (@lem7217625 _132718 s f) (@lem7217632 _132718 s f)). Qed.
Lemma lem7217634 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term255 _132718 s f) = (term255 _132718 s f).
Proof. exact (eq_refl (term255 _132718 s f)). Qed.
Lemma lem7217635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217636 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term256 _132718 s f) = (term257 _132718 s f).
Proof. exact (MK_COMB (@lem7217635) (@lem7217633 _132718 s f)). Qed.
Lemma lem7217637 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term258 _132718 s f) = (term259 _132718 s f).
Proof. exact (MK_COMB (@lem7217636 _132718 s f) (@lem7217634 _132718 s f)). Qed.
Lemma lem7217638 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term260 _132718 s f) = (term258 _132718 s f).
Proof. exact (@lem17045 (term50 _132718 s f) ((@sum _132718 s f) = term32)). Qed.
Lemma lem7217639 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term260 _132718 s f) = (term259 _132718 s f).
Proof. exact (TRANS (@lem7217638 _132718 s f) (@lem7217637 _132718 s f)). Qed.
Lemma lem7217641 {_132718 : Type'} (s : _132718 -> Prop) : (term261 _132718 s) = (term261 _132718 s).
Proof. exact (eq_refl (term261 _132718 s)). Qed.
Lemma lem7217642 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term262 _132718 s f) = (term263 _132718 s f).
Proof. exact (MK_COMB (@lem7217641 _132718 s) (@lem7217639 _132718 s f)). Qed.
Lemma lem7217643 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term264 _132718 s f) = (term262 _132718 s f).
Proof. exact (@lem17045 (@FINITE _132718 s) (term52 _132718 s f)). Qed.
Lemma lem7217644 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term264 _132718 s f) = (term263 _132718 s f).
Proof. exact (TRANS (@lem7217643 _132718 s f) (@lem7217642 _132718 s f)). Qed.
Lemma lem7217651 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term45 _132718 s f x) = (term265 _132718 s f x).
Proof. exact (@lem17265 (@IN _132718 x s) ((f x) = term32)). Qed.
Lemma lem7217652 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term46 _132718 s f) = (term266 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217651 _132718 s f x)). Qed.
Lemma lem7217653 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7217654 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term47 _132718 s f) = (term267 _132718 s f).
Proof. exact (MK_COMB (@lem7217653 _132718) (@lem7217652 _132718 s f)). Qed.
Lemma lem7217655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217656 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term268 _132718 s f) = (term269 _132718 s f).
Proof. exact (MK_COMB (@lem7217655) (@lem7217644 _132718 s f)). Qed.
Lemma lem7217657 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term270 _132718 s f) = (term271 _132718 s f).
Proof. exact (MK_COMB (@lem7217656 _132718 s f) (@lem7217654 _132718 s f)). Qed.
Lemma lem7217658 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term56 _132718 s f) = (term270 _132718 s f).
Proof. exact (@lem17265 (term54 _132718 s f) (term47 _132718 s f)). Qed.
Lemma lem7217659 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term56 _132718 s f) = (term271 _132718 s f).
Proof. exact (TRANS (@lem7217658 _132718 s f) (@lem7217657 _132718 s f)). Qed.
Lemma lem7217660 {_132718 : Type'} (f : _132718 -> real) : (term57 _132718 f) = (term272 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7217659 _132718 s f)). Qed.
Lemma lem7217661 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7217662 {_132718 : Type'} (f : _132718 -> real) : (term58 _132718 f) = (term273 _132718 f).
Proof. exact (MK_COMB (@lem7217661 _132718) (@lem7217660 _132718 f)). Qed.
Lemma lem7217663 {_132718 : Type'} : (term59 _132718) = (term274 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7217662 _132718 f)). Qed.
Lemma lem7217664 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7217665 {_132718 : Type'} : (term60 _132718) = (term275 _132718).
Proof. exact (MK_COMB (@lem7217664 _132718) (@lem7217663 _132718)). Qed.
Lemma lem7217816 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7217817 {_132718 : Type'} (P : _132718 -> Prop) (Q : Prop) : (term276 _132718 P Q) = (term277 _132718 P Q).
Proof. exact (@lem7217816 _132718 P Q). Qed.
Lemma lem7217818 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term278 _132718 s f) = (term279 _132718 s f).
Proof. exact (@lem7217817 _132718 (term253 _132718 s f) (term255 _132718 s f)). Qed.
Lemma lem7217819 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term280 _132718 s f x) = (term244 _132718 s f x).
Proof. exact (eq_refl (term280 _132718 s f x)). Qed.
Lemma lem7217820 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term281 _132718 s f) = (term253 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217819 _132718 s f x)). Qed.
Lemma lem7217821 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217822 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term282 _132718 s f) = (term254 _132718 s f).
Proof. exact (MK_COMB (@lem7217821 _132718) (@lem7217820 _132718 s f)). Qed.
Lemma lem7217823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217824 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term283 _132718 s f) = (term257 _132718 s f).
Proof. exact (MK_COMB (@lem7217823) (@lem7217822 _132718 s f)). Qed.
Lemma lem7217825 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term255 _132718 s f) = (term255 _132718 s f).
Proof. exact (eq_refl (term255 _132718 s f)). Qed.
Lemma lem7217826 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term278 _132718 s f) = (term259 _132718 s f).
Proof. exact (MK_COMB (@lem7217824 _132718 s f) (@lem7217825 _132718 s f)). Qed.
Lemma lem7217827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217828 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term284 _132718 s f) = (term285 _132718 s f).
Proof. exact (MK_COMB (@lem7217827) (@lem7217826 _132718 s f)). Qed.
Lemma lem7217829 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term280 _132718 s f x) = (term244 _132718 s f x).
Proof. exact (eq_refl (term280 _132718 s f x)). Qed.
Lemma lem7217830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217831 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term286 _132718 s f x) = (term287 _132718 s f x).
Proof. exact (MK_COMB (@lem7217830) (@lem7217829 _132718 s f x)). Qed.
Lemma lem7217832 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term255 _132718 s f) = (term255 _132718 s f).
Proof. exact (eq_refl (term255 _132718 s f)). Qed.
Lemma lem7217833 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term288 _132718 x s f) = (term289 _132718 x s f).
Proof. exact (MK_COMB (@lem7217831 _132718 s f x) (@lem7217832 _132718 s f)). Qed.
Lemma lem7217834 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term290 _132718 s f) = (term291 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217833 _132718 x s f)). Qed.
Lemma lem7217835 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217836 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term279 _132718 s f) = (term292 _132718 s f).
Proof. exact (MK_COMB (@lem7217835 _132718) (@lem7217834 _132718 s f)). Qed.
Lemma lem7217837 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((term278 _132718 s f) = (term279 _132718 s f)) = ((term259 _132718 s f) = (term292 _132718 s f)).
Proof. exact (MK_COMB (@lem7217828 _132718 s f) (@lem7217836 _132718 s f)). Qed.
Lemma lem7217838 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term259 _132718 s f) = (term292 _132718 s f).
Proof. exact (EQ_MP (@lem7217837 _132718 s f) (@lem7217818 _132718 s f)). Qed.
Lemma lem7217839 {_132718 : Type'} (s : _132718 -> Prop) : (term261 _132718 s) = (term261 _132718 s).
Proof. exact (eq_refl (term261 _132718 s)). Qed.
Lemma lem7217840 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term263 _132718 s f) = (term293 _132718 s f).
Proof. exact (MK_COMB (@lem7217839 _132718 s) (@lem7217838 _132718 s f)). Qed.
Lemma lem7217842 {A : Type'} (P : Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7217843 {_132718 : Type'} (P : Prop) (Q : _132718 -> Prop) : (term294 _132718 P Q) = (term295 _132718 P Q).
Proof. exact (@lem7217842 _132718 P Q). Qed.
Lemma lem7217844 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term296 _132718 s f) = (term297 _132718 s f).
Proof. exact (@lem7217843 _132718 (term298 _132718 s) (term291 _132718 s f)). Qed.
Lemma lem7217845 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term299 _132718 s f x) = (term289 _132718 x s f).
Proof. exact (eq_refl (term299 _132718 s f x)). Qed.
Lemma lem7217846 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term300 _132718 s f) = (term291 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217845 _132718 x s f)). Qed.
Lemma lem7217847 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217848 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term301 _132718 s f) = (term292 _132718 s f).
Proof. exact (MK_COMB (@lem7217847 _132718) (@lem7217846 _132718 s f)). Qed.
Lemma lem7217849 {_132718 : Type'} (s : _132718 -> Prop) : (term261 _132718 s) = (term261 _132718 s).
Proof. exact (eq_refl (term261 _132718 s)). Qed.
Lemma lem7217850 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term296 _132718 s f) = (term293 _132718 s f).
Proof. exact (MK_COMB (@lem7217849 _132718 s) (@lem7217848 _132718 s f)). Qed.
Lemma lem7217851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217852 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term302 _132718 s f) = (term303 _132718 s f).
Proof. exact (MK_COMB (@lem7217851) (@lem7217850 _132718 s f)). Qed.
Lemma lem7217853 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term299 _132718 s f x) = (term289 _132718 x s f).
Proof. exact (eq_refl (term299 _132718 s f x)). Qed.
Lemma lem7217854 {_132718 : Type'} (s : _132718 -> Prop) : (term261 _132718 s) = (term261 _132718 s).
Proof. exact (eq_refl (term261 _132718 s)). Qed.
Lemma lem7217855 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term304 _132718 s f x) = (term305 _132718 x s f).
Proof. exact (MK_COMB (@lem7217854 _132718 s) (@lem7217853 _132718 x s f)). Qed.
Lemma lem7217856 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term306 _132718 s f) = (term307 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217855 _132718 x s f)). Qed.
Lemma lem7217857 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217858 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term297 _132718 s f) = (term308 _132718 s f).
Proof. exact (MK_COMB (@lem7217857 _132718) (@lem7217856 _132718 s f)). Qed.
Lemma lem7217859 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((term296 _132718 s f) = (term297 _132718 s f)) = ((term293 _132718 s f) = (term308 _132718 s f)).
Proof. exact (MK_COMB (@lem7217852 _132718 s f) (@lem7217858 _132718 s f)). Qed.
Lemma lem7217860 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term293 _132718 s f) = (term308 _132718 s f).
Proof. exact (EQ_MP (@lem7217859 _132718 s f) (@lem7217844 _132718 s f)). Qed.
Lemma lem7217861 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term263 _132718 s f) = (term308 _132718 s f).
Proof. exact (TRANS (@lem7217840 _132718 s f) (@lem7217860 _132718 s f)). Qed.
Lemma lem7217862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217863 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term269 _132718 s f) = (term309 _132718 s f).
Proof. exact (MK_COMB (@lem7217862) (@lem7217861 _132718 s f)). Qed.
Lemma lem7217864 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term267 _132718 s f) = (term267 _132718 s f).
Proof. exact (eq_refl (term267 _132718 s f)). Qed.
Lemma lem7217865 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term271 _132718 s f) = (term310 _132718 s f).
Proof. exact (MK_COMB (@lem7217863 _132718 s f) (@lem7217864 _132718 s f)). Qed.
Lemma lem7217867 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7217868 {_132718 : Type'} (P : _132718 -> Prop) (Q : Prop) : (term276 _132718 P Q) = (term277 _132718 P Q).
Proof. exact (@lem7217867 _132718 P Q). Qed.
Lemma lem7217869 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term311 _132718 s f) = (term312 _132718 s f).
Proof. exact (@lem7217868 _132718 (term307 _132718 s f) (term267 _132718 s f)). Qed.
Lemma lem7217870 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term313 _132718 s f x) = (term305 _132718 x s f).
Proof. exact (eq_refl (term313 _132718 s f x)). Qed.
Lemma lem7217871 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term314 _132718 s f) = (term307 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217870 _132718 x s f)). Qed.
Lemma lem7217872 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217873 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term315 _132718 s f) = (term308 _132718 s f).
Proof. exact (MK_COMB (@lem7217872 _132718) (@lem7217871 _132718 s f)). Qed.
Lemma lem7217874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217875 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term316 _132718 s f) = (term309 _132718 s f).
Proof. exact (MK_COMB (@lem7217874) (@lem7217873 _132718 s f)). Qed.
Lemma lem7217876 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term267 _132718 s f) = (term267 _132718 s f).
Proof. exact (eq_refl (term267 _132718 s f)). Qed.
Lemma lem7217877 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term311 _132718 s f) = (term310 _132718 s f).
Proof. exact (MK_COMB (@lem7217875 _132718 s f) (@lem7217876 _132718 s f)). Qed.
Lemma lem7217878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217879 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term317 _132718 s f) = (term318 _132718 s f).
Proof. exact (MK_COMB (@lem7217878) (@lem7217877 _132718 s f)). Qed.
Lemma lem7217880 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term313 _132718 s f x) = (term305 _132718 x s f).
Proof. exact (eq_refl (term313 _132718 s f x)). Qed.
Lemma lem7217881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217882 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term319 _132718 s f x) = (term320 _132718 x s f).
Proof. exact (MK_COMB (@lem7217881) (@lem7217880 _132718 x s f)). Qed.
Lemma lem7217883 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term267 _132718 s f) = (term267 _132718 s f).
Proof. exact (eq_refl (term267 _132718 s f)). Qed.
Lemma lem7217884 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term321 _132718 x s f) = (term322 _132718 x s f).
Proof. exact (MK_COMB (@lem7217882 _132718 x s f) (@lem7217883 _132718 s f)). Qed.
Lemma lem7217885 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term323 _132718 s f) = (term324 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217884 _132718 x s f)). Qed.
Lemma lem7217886 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217887 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term312 _132718 s f) = (term325 _132718 s f).
Proof. exact (MK_COMB (@lem7217886 _132718) (@lem7217885 _132718 s f)). Qed.
Lemma lem7217888 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((term311 _132718 s f) = (term312 _132718 s f)) = ((term310 _132718 s f) = (term325 _132718 s f)).
Proof. exact (MK_COMB (@lem7217879 _132718 s f) (@lem7217887 _132718 s f)). Qed.
Lemma lem7217889 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term310 _132718 s f) = (term325 _132718 s f).
Proof. exact (EQ_MP (@lem7217888 _132718 s f) (@lem7217869 _132718 s f)). Qed.
Lemma lem7217890 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term271 _132718 s f) = (term325 _132718 s f).
Proof. exact (TRANS (@lem7217865 _132718 s f) (@lem7217889 _132718 s f)). Qed.
Lemma lem7217891 {_132718 : Type'} (f : _132718 -> real) : (term272 _132718 f) = (term326 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7217890 _132718 s f)). Qed.
Lemma lem7217892 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7217893 {_132718 : Type'} (f : _132718 -> real) : (term273 _132718 f) = (term327 _132718 f).
Proof. exact (MK_COMB (@lem7217892 _132718) (@lem7217891 _132718 f)). Qed.
Lemma lem7217895 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7217896 {_132718 : Type'} (P : type672 _132718) : (term330 _132718 P) = (term331 _132718 P).
Proof. exact (@lem7217895 (_132718 -> Prop) _132718 P). Qed.
Lemma lem7217897 {_132718 : Type'} (f : _132718 -> real) : (term332 _132718 f) = (term333 _132718 f).
Proof. exact (@lem7217896 _132718 (term334 _132718 f)). Qed.
Lemma lem7217898 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term335 _132718 f s) = (term324 _132718 s f).
Proof. exact (eq_refl (term335 _132718 f s)). Qed.
Lemma lem7217899 {_132718 : Type'} (x : _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7217900 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term336 _132718 f s x) = (term337 _132718 s f x).
Proof. exact (MK_COMB (@lem7217898 _132718 s f) (@lem7217899 _132718 x)). Qed.
Lemma lem7217901 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term337 _132718 s f x) = (term322 _132718 x s f).
Proof. exact (eq_refl (term337 _132718 s f x)). Qed.
Lemma lem7217902 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term336 _132718 f s x) = (term322 _132718 x s f).
Proof. exact (TRANS (@lem7217900 _132718 s f x) (@lem7217901 _132718 x s f)). Qed.
Lemma lem7217903 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term338 _132718 f s) = (term324 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7217902 _132718 x s f)). Qed.
Lemma lem7217904 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7217905 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term339 _132718 f s) = (term325 _132718 s f).
Proof. exact (MK_COMB (@lem7217904 _132718) (@lem7217903 _132718 s f)). Qed.
Lemma lem7217906 {_132718 : Type'} (f : _132718 -> real) : (term340 _132718 f) = (term326 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7217905 _132718 s f)). Qed.
Lemma lem7217907 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7217908 {_132718 : Type'} (f : _132718 -> real) : (term332 _132718 f) = (term327 _132718 f).
Proof. exact (MK_COMB (@lem7217907 _132718) (@lem7217906 _132718 f)). Qed.
Lemma lem7217909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217910 {_132718 : Type'} (f : _132718 -> real) : (term341 _132718 f) = (term342 _132718 f).
Proof. exact (MK_COMB (@lem7217909) (@lem7217908 _132718 f)). Qed.
Lemma lem7217911 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term335 _132718 f s) = (term324 _132718 s f).
Proof. exact (eq_refl (term335 _132718 f s)). Qed.
Lemma lem7217912 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7217913 {_132718 : Type'} (f : _132718 -> real) (x : type684 _132718) (s : _132718 -> Prop) : (term343 _132718 f x s) = (term344 _132718 f x s).
Proof. exact (MK_COMB (@lem7217911 _132718 s f) (@lem7217912 _132718 x s)). Qed.
Lemma lem7217914 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term344 _132718 f x s) = (term345 _132718 x s f).
Proof. exact (eq_refl (term344 _132718 f x s)). Qed.
Lemma lem7217915 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term343 _132718 f x s) = (term345 _132718 x s f).
Proof. exact (TRANS (@lem7217913 _132718 f x s) (@lem7217914 _132718 x s f)). Qed.
Lemma lem7217916 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term346 _132718 f x) = (term347 _132718 x f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7217915 _132718 x s f)). Qed.
Lemma lem7217917 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7217918 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term348 _132718 f x) = (term349 _132718 x f).
Proof. exact (MK_COMB (@lem7217917 _132718) (@lem7217916 _132718 x f)). Qed.
Lemma lem7217919 {_132718 : Type'} (f : _132718 -> real) : (term350 _132718 f) = (term351 _132718 f).
Proof. exact (fun_ext (fun x : type684 _132718 => @lem7217918 _132718 x f)). Qed.
Lemma lem7217920 {_132718 : Type'} : (@ex ((_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> Prop) -> _132718))). Qed.
Lemma lem7217921 {_132718 : Type'} (f : _132718 -> real) : (term333 _132718 f) = (term352 _132718 f).
Proof. exact (MK_COMB (@lem7217920 _132718) (@lem7217919 _132718 f)). Qed.
Lemma lem7217922 {_132718 : Type'} (f : _132718 -> real) : ((term332 _132718 f) = (term333 _132718 f)) = ((term327 _132718 f) = (term352 _132718 f)).
Proof. exact (MK_COMB (@lem7217910 _132718 f) (@lem7217921 _132718 f)). Qed.
Lemma lem7217923 {_132718 : Type'} (f : _132718 -> real) : (term327 _132718 f) = (term352 _132718 f).
Proof. exact (EQ_MP (@lem7217922 _132718 f) (@lem7217897 _132718 f)). Qed.
Lemma lem7217924 {_132718 : Type'} (f : _132718 -> real) : (term273 _132718 f) = (term352 _132718 f).
Proof. exact (TRANS (@lem7217893 _132718 f) (@lem7217923 _132718 f)). Qed.
Lemma lem7217925 {_132718 : Type'} : (term274 _132718) = (term353 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7217924 _132718 f)). Qed.
Lemma lem7217926 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7217927 {_132718 : Type'} : (term275 _132718) = (term354 _132718).
Proof. exact (MK_COMB (@lem7217926 _132718) (@lem7217925 _132718)). Qed.
Lemma lem7217929 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7217930 {_132718 : Type'} (P : type707 _132718) : (term355 _132718 P) = (term356 _132718 P).
Proof. exact (@lem7217929 (_132718 -> real) (type684 _132718) P). Qed.
Lemma lem7217931 {_132718 : Type'} : (term357 _132718) = (term358 _132718).
Proof. exact (@lem7217930 _132718 (term359 _132718)). Qed.
Lemma lem7217932 {_132718 : Type'} (f : _132718 -> real) : (term360 _132718 f) = (term351 _132718 f).
Proof. exact (eq_refl (term360 _132718 f)). Qed.
Lemma lem7217933 {_132718 : Type'} (x : type684 _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7217934 {_132718 : Type'} (f : _132718 -> real) (x : type684 _132718) : (term361 _132718 f x) = (term362 _132718 f x).
Proof. exact (MK_COMB (@lem7217932 _132718 f) (@lem7217933 _132718 x)). Qed.
Lemma lem7217935 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term362 _132718 f x) = (term349 _132718 x f).
Proof. exact (eq_refl (term362 _132718 f x)). Qed.
Lemma lem7217936 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term361 _132718 f x) = (term349 _132718 x f).
Proof. exact (TRANS (@lem7217934 _132718 f x) (@lem7217935 _132718 x f)). Qed.
Lemma lem7217937 {_132718 : Type'} (f : _132718 -> real) : (term363 _132718 f) = (term351 _132718 f).
Proof. exact (fun_ext (fun x : type684 _132718 => @lem7217936 _132718 x f)). Qed.
Lemma lem7217938 {_132718 : Type'} : (@ex ((_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> Prop) -> _132718))). Qed.
Lemma lem7217939 {_132718 : Type'} (f : _132718 -> real) : (term364 _132718 f) = (term352 _132718 f).
Proof. exact (MK_COMB (@lem7217938 _132718) (@lem7217937 _132718 f)). Qed.
Lemma lem7217940 {_132718 : Type'} : (term365 _132718) = (term353 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7217939 _132718 f)). Qed.
Lemma lem7217941 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7217942 {_132718 : Type'} : (term357 _132718) = (term354 _132718).
Proof. exact (MK_COMB (@lem7217941 _132718) (@lem7217940 _132718)). Qed.
Lemma lem7217943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7217944 {_132718 : Type'} : (term366 _132718) = (term367 _132718).
Proof. exact (MK_COMB (@lem7217943) (@lem7217942 _132718)). Qed.
Lemma lem7217945 {_132718 : Type'} (f : _132718 -> real) : (term360 _132718 f) = (term351 _132718 f).
Proof. exact (eq_refl (term360 _132718 f)). Qed.
Lemma lem7217946 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7217947 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (term368 _132718 x f) = (term369 _132718 x f).
Proof. exact (MK_COMB (@lem7217945 _132718 f) (@lem7217946 _132718 x f)). Qed.
Lemma lem7217948 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (term369 _132718 x f) = (term370 _132718 x f).
Proof. exact (eq_refl (term369 _132718 x f)). Qed.
Lemma lem7217949 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (term368 _132718 x f) = (term370 _132718 x f).
Proof. exact (TRANS (@lem7217947 _132718 x f) (@lem7217948 _132718 x f)). Qed.
Lemma lem7217950 {_132718 : Type'} (x : type710 _132718) : (term371 _132718 x) = (term372 _132718 x).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7217949 _132718 x f)). Qed.
Lemma lem7217951 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7217952 {_132718 : Type'} (x : type710 _132718) : (term373 _132718 x) = (term374 _132718 x).
Proof. exact (MK_COMB (@lem7217951 _132718) (@lem7217950 _132718 x)). Qed.
Lemma lem7217953 {_132718 : Type'} : (term375 _132718) = (term376 _132718).
Proof. exact (fun_ext (fun x : type710 _132718 => @lem7217952 _132718 x)). Qed.
Lemma lem7217954 {_132718 : Type'} : (@ex ((_132718 -> real) -> (_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> real) -> (_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> real) -> (_132718 -> Prop) -> _132718))). Qed.
Lemma lem7217955 {_132718 : Type'} : (term358 _132718) = (term377 _132718).
Proof. exact (MK_COMB (@lem7217954 _132718) (@lem7217953 _132718)). Qed.
Lemma lem7217956 {_132718 : Type'} : ((term357 _132718) = (term358 _132718)) = ((term354 _132718) = (term377 _132718)).
Proof. exact (MK_COMB (@lem7217944 _132718) (@lem7217955 _132718)). Qed.
Lemma lem7217957 {_132718 : Type'} : (term354 _132718) = (term377 _132718).
Proof. exact (EQ_MP (@lem7217956 _132718) (@lem7217931 _132718)). Qed.
Lemma lem7217959 {_132718 : Type'} : (term275 _132718) = (term377 _132718).
Proof. exact (TRANS (@lem7217927 _132718) (@lem7217957 _132718)). Qed.
Lemma lem7217960 {_132718 : Type'} : (term60 _132718) = (term377 _132718).
Proof. exact (TRANS (@lem7217665 _132718) (@lem7217959 _132718)). Qed.
Lemma lem7217961 {_132718 : Type'} (h1 : term60 _132718) : term377 _132718.
Proof. exact (EQ_MP (@lem7217960 _132718) (@lem7216886 _132718 h1)). Qed.
Lemma lem7217969 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term378 s f x) = (term379 s f x).
Proof. exact (@lem17362 (@IN nat x s) (term92 f x)). Qed.
Lemma lem7217970 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7217971 (s : nat -> Prop) (f : nat -> real) : (term380 s f) = (term381 s f).
Proof. exact (@lem7217970 (term34 s f)). Qed.
Lemma lem7217972 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term382 s f x) = (term33 s f x).
Proof. exact (eq_refl (term382 s f x)). Qed.
Lemma lem7217973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7217974 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term383 s f x) = (term378 s f x).
Proof. exact (MK_COMB (@lem7217973) (@lem7217972 s f x)). Qed.
Lemma lem7217975 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term383 s f x) = (term379 s f x).
Proof. exact (TRANS (@lem7217974 s f x) (@lem7217969 s f x)). Qed.
Lemma lem7217976 (s : nat -> Prop) (f : nat -> real) : (term384 s f) = (term385 s f).
Proof. exact (fun_ext (fun x : nat => @lem7217975 s f x)). Qed.
Lemma lem7217977 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7217978 (s : nat -> Prop) (f : nat -> real) : (term381 s f) = (term386 s f).
Proof. exact (MK_COMB (@lem7217977) (@lem7217976 s f)). Qed.
Lemma lem7217979 (s : nat -> Prop) (f : nat -> real) : (term380 s f) = (term386 s f).
Proof. exact (TRANS (@lem7217971 s f) (@lem7217978 s f)). Qed.
Lemma lem7217980 (s : nat -> Prop) (f : nat -> real) : (term387 s f) = (term387 s f).
Proof. exact (eq_refl (term387 s f)). Qed.
Lemma lem7217981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7217982 (s : nat -> Prop) (f : nat -> real) : (term388 s f) = (term389 s f).
Proof. exact (MK_COMB (@lem7217981) (@lem7217979 s f)). Qed.
Lemma lem7217983 (s : nat -> Prop) (f : nat -> real) : (term390 s f) = (term391 s f).
Proof. exact (MK_COMB (@lem7217982 s f) (@lem7217980 s f)). Qed.
Lemma lem7217984 (s : nat -> Prop) (f : nat -> real) : (term392 s f) = (term390 s f).
Proof. exact (@lem17045 (term35 s f) ((@sum nat s f) = term32)). Qed.
Lemma lem7217985 (s : nat -> Prop) (f : nat -> real) : (term392 s f) = (term391 s f).
Proof. exact (TRANS (@lem7217984 s f) (@lem7217983 s f)). Qed.
Lemma lem7217987 (s : nat -> Prop) : (term393 s) = (term393 s).
Proof. exact (eq_refl (term393 s)). Qed.
Lemma lem7217988 (s : nat -> Prop) (f : nat -> real) : (term394 s f) = (term395 s f).
Proof. exact (MK_COMB (@lem7217987 s) (@lem7217985 s f)). Qed.
Lemma lem7217989 (s : nat -> Prop) (f : nat -> real) : (term396 s f) = (term394 s f).
Proof. exact (@lem17045 (@FINITE nat s) (term37 s f)). Qed.
Lemma lem7217990 (s : nat -> Prop) (f : nat -> real) : (term396 s f) = (term395 s f).
Proof. exact (TRANS (@lem7217989 s f) (@lem7217988 s f)). Qed.
Lemma lem7217997 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term29 s f x) = (term397 s f x).
Proof. exact (@lem17265 (@IN nat x s) ((f x) = term32)). Qed.
Lemma lem7217998 (s : nat -> Prop) (f : nat -> real) : (term30 s f) = (term398 s f).
Proof. exact (fun_ext (fun x : nat => @lem7217997 s f x)). Qed.
Lemma lem7217999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218000 (s : nat -> Prop) (f : nat -> real) : (term31 s f) = (term399 s f).
Proof. exact (MK_COMB (@lem7217999) (@lem7217998 s f)). Qed.
Lemma lem7218001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218002 (s : nat -> Prop) (f : nat -> real) : (term400 s f) = (term401 s f).
Proof. exact (MK_COMB (@lem7218001) (@lem7217990 s f)). Qed.
Lemma lem7218003 (s : nat -> Prop) (f : nat -> real) : (term402 s f) = (term403 s f).
Proof. exact (MK_COMB (@lem7218002 s f) (@lem7218000 s f)). Qed.
Lemma lem7218004 (s : nat -> Prop) (f : nat -> real) : (term41 s f) = (term402 s f).
Proof. exact (@lem17265 (term39 s f) (term31 s f)). Qed.
Lemma lem7218005 (s : nat -> Prop) (f : nat -> real) : (term41 s f) = (term403 s f).
Proof. exact (TRANS (@lem7218004 s f) (@lem7218003 s f)). Qed.
Lemma lem7218006 (f : nat -> real) : (term42 f) = (term404 f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7218005 s f)). Qed.
Lemma lem7218007 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7218008 (f : nat -> real) : (term43 f) = (term405 f).
Proof. exact (MK_COMB (@lem7218007) (@lem7218006 f)). Qed.
Lemma lem7218009 : term44 = term406.
Proof. exact (fun_ext (fun f : nat -> real => @lem7218008 f)). Qed.
Lemma lem7218010 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7218011 : term11 = term407.
Proof. exact (MK_COMB (@lem7218010) (@lem7218009)). Qed.
Lemma lem7218162 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7218163 (P : nat -> Prop) (Q : Prop) : (term408 P Q) = (term409 P Q).
Proof. exact (@lem7218162 nat P Q). Qed.
Lemma lem7218164 (s : nat -> Prop) (f : nat -> real) : (term410 s f) = (term411 s f).
Proof. exact (@lem7218163 (term385 s f) (term387 s f)). Qed.
Lemma lem7218165 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term412 s f x) = (term379 s f x).
Proof. exact (eq_refl (term412 s f x)). Qed.
Lemma lem7218166 (s : nat -> Prop) (f : nat -> real) : (term413 s f) = (term385 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218165 s f x)). Qed.
Lemma lem7218167 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218168 (s : nat -> Prop) (f : nat -> real) : (term414 s f) = (term386 s f).
Proof. exact (MK_COMB (@lem7218167) (@lem7218166 s f)). Qed.
Lemma lem7218169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218170 (s : nat -> Prop) (f : nat -> real) : (term415 s f) = (term389 s f).
Proof. exact (MK_COMB (@lem7218169) (@lem7218168 s f)). Qed.
Lemma lem7218171 (s : nat -> Prop) (f : nat -> real) : (term387 s f) = (term387 s f).
Proof. exact (eq_refl (term387 s f)). Qed.
Lemma lem7218172 (s : nat -> Prop) (f : nat -> real) : (term410 s f) = (term391 s f).
Proof. exact (MK_COMB (@lem7218170 s f) (@lem7218171 s f)). Qed.
Lemma lem7218173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7218174 (s : nat -> Prop) (f : nat -> real) : (term416 s f) = (term417 s f).
Proof. exact (MK_COMB (@lem7218173) (@lem7218172 s f)). Qed.
Lemma lem7218175 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term412 s f x) = (term379 s f x).
Proof. exact (eq_refl (term412 s f x)). Qed.
Lemma lem7218176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218177 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term418 s f x) = (term419 s f x).
Proof. exact (MK_COMB (@lem7218176) (@lem7218175 s f x)). Qed.
Lemma lem7218178 (s : nat -> Prop) (f : nat -> real) : (term387 s f) = (term387 s f).
Proof. exact (eq_refl (term387 s f)). Qed.
Lemma lem7218179 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term420 x s f) = (term421 x s f).
Proof. exact (MK_COMB (@lem7218177 s f x) (@lem7218178 s f)). Qed.
Lemma lem7218180 (s : nat -> Prop) (f : nat -> real) : (term422 s f) = (term423 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218179 x s f)). Qed.
Lemma lem7218181 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218182 (s : nat -> Prop) (f : nat -> real) : (term411 s f) = (term424 s f).
Proof. exact (MK_COMB (@lem7218181) (@lem7218180 s f)). Qed.
Lemma lem7218183 (s : nat -> Prop) (f : nat -> real) : ((term410 s f) = (term411 s f)) = ((term391 s f) = (term424 s f)).
Proof. exact (MK_COMB (@lem7218174 s f) (@lem7218182 s f)). Qed.
Lemma lem7218184 (s : nat -> Prop) (f : nat -> real) : (term391 s f) = (term424 s f).
Proof. exact (EQ_MP (@lem7218183 s f) (@lem7218164 s f)). Qed.
Lemma lem7218185 (s : nat -> Prop) : (term393 s) = (term393 s).
Proof. exact (eq_refl (term393 s)). Qed.
Lemma lem7218186 (s : nat -> Prop) (f : nat -> real) : (term395 s f) = (term425 s f).
Proof. exact (MK_COMB (@lem7218185 s) (@lem7218184 s f)). Qed.
Lemma lem7218188 {A : Type'} (P : Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7218189 (P : Prop) (Q : nat -> Prop) : (term426 P Q) = (term427 P Q).
Proof. exact (@lem7218188 nat P Q). Qed.
Lemma lem7218190 (s : nat -> Prop) (f : nat -> real) : (term428 s f) = (term429 s f).
Proof. exact (@lem7218189 (term430 s) (term423 s f)). Qed.
Lemma lem7218191 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term431 s f x) = (term421 x s f).
Proof. exact (eq_refl (term431 s f x)). Qed.
Lemma lem7218192 (s : nat -> Prop) (f : nat -> real) : (term432 s f) = (term423 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218191 x s f)). Qed.
Lemma lem7218193 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218194 (s : nat -> Prop) (f : nat -> real) : (term433 s f) = (term424 s f).
Proof. exact (MK_COMB (@lem7218193) (@lem7218192 s f)). Qed.
Lemma lem7218195 (s : nat -> Prop) : (term393 s) = (term393 s).
Proof. exact (eq_refl (term393 s)). Qed.
Lemma lem7218196 (s : nat -> Prop) (f : nat -> real) : (term428 s f) = (term425 s f).
Proof. exact (MK_COMB (@lem7218195 s) (@lem7218194 s f)). Qed.
Lemma lem7218197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7218198 (s : nat -> Prop) (f : nat -> real) : (term434 s f) = (term435 s f).
Proof. exact (MK_COMB (@lem7218197) (@lem7218196 s f)). Qed.
Lemma lem7218199 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term431 s f x) = (term421 x s f).
Proof. exact (eq_refl (term431 s f x)). Qed.
Lemma lem7218200 (s : nat -> Prop) : (term393 s) = (term393 s).
Proof. exact (eq_refl (term393 s)). Qed.
Lemma lem7218201 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term436 s f x) = (term437 x s f).
Proof. exact (MK_COMB (@lem7218200 s) (@lem7218199 x s f)). Qed.
Lemma lem7218202 (s : nat -> Prop) (f : nat -> real) : (term438 s f) = (term439 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218201 x s f)). Qed.
Lemma lem7218203 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218204 (s : nat -> Prop) (f : nat -> real) : (term429 s f) = (term440 s f).
Proof. exact (MK_COMB (@lem7218203) (@lem7218202 s f)). Qed.
Lemma lem7218205 (s : nat -> Prop) (f : nat -> real) : ((term428 s f) = (term429 s f)) = ((term425 s f) = (term440 s f)).
Proof. exact (MK_COMB (@lem7218198 s f) (@lem7218204 s f)). Qed.
Lemma lem7218206 (s : nat -> Prop) (f : nat -> real) : (term425 s f) = (term440 s f).
Proof. exact (EQ_MP (@lem7218205 s f) (@lem7218190 s f)). Qed.
Lemma lem7218207 (s : nat -> Prop) (f : nat -> real) : (term395 s f) = (term440 s f).
Proof. exact (TRANS (@lem7218186 s f) (@lem7218206 s f)). Qed.
Lemma lem7218208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218209 (s : nat -> Prop) (f : nat -> real) : (term401 s f) = (term441 s f).
Proof. exact (MK_COMB (@lem7218208) (@lem7218207 s f)). Qed.
Lemma lem7218210 (s : nat -> Prop) (f : nat -> real) : (term399 s f) = (term399 s f).
Proof. exact (eq_refl (term399 s f)). Qed.
Lemma lem7218211 (s : nat -> Prop) (f : nat -> real) : (term403 s f) = (term442 s f).
Proof. exact (MK_COMB (@lem7218209 s f) (@lem7218210 s f)). Qed.
Lemma lem7218213 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7218214 (P : nat -> Prop) (Q : Prop) : (term408 P Q) = (term409 P Q).
Proof. exact (@lem7218213 nat P Q). Qed.
Lemma lem7218215 (s : nat -> Prop) (f : nat -> real) : (term443 s f) = (term444 s f).
Proof. exact (@lem7218214 (term439 s f) (term399 s f)). Qed.
Lemma lem7218216 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term445 s f x) = (term437 x s f).
Proof. exact (eq_refl (term445 s f x)). Qed.
Lemma lem7218217 (s : nat -> Prop) (f : nat -> real) : (term446 s f) = (term439 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218216 x s f)). Qed.
Lemma lem7218218 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218219 (s : nat -> Prop) (f : nat -> real) : (term447 s f) = (term440 s f).
Proof. exact (MK_COMB (@lem7218218) (@lem7218217 s f)). Qed.
Lemma lem7218220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218221 (s : nat -> Prop) (f : nat -> real) : (term448 s f) = (term441 s f).
Proof. exact (MK_COMB (@lem7218220) (@lem7218219 s f)). Qed.
Lemma lem7218222 (s : nat -> Prop) (f : nat -> real) : (term399 s f) = (term399 s f).
Proof. exact (eq_refl (term399 s f)). Qed.
Lemma lem7218223 (s : nat -> Prop) (f : nat -> real) : (term443 s f) = (term442 s f).
Proof. exact (MK_COMB (@lem7218221 s f) (@lem7218222 s f)). Qed.
Lemma lem7218224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7218225 (s : nat -> Prop) (f : nat -> real) : (term449 s f) = (term450 s f).
Proof. exact (MK_COMB (@lem7218224) (@lem7218223 s f)). Qed.
Lemma lem7218226 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term445 s f x) = (term437 x s f).
Proof. exact (eq_refl (term445 s f x)). Qed.
Lemma lem7218227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218228 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term451 s f x) = (term452 x s f).
Proof. exact (MK_COMB (@lem7218227) (@lem7218226 x s f)). Qed.
Lemma lem7218229 (s : nat -> Prop) (f : nat -> real) : (term399 s f) = (term399 s f).
Proof. exact (eq_refl (term399 s f)). Qed.
Lemma lem7218230 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term453 x s f) = (term454 x s f).
Proof. exact (MK_COMB (@lem7218228 x s f) (@lem7218229 s f)). Qed.
Lemma lem7218231 (s : nat -> Prop) (f : nat -> real) : (term455 s f) = (term456 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218230 x s f)). Qed.
Lemma lem7218232 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218233 (s : nat -> Prop) (f : nat -> real) : (term444 s f) = (term457 s f).
Proof. exact (MK_COMB (@lem7218232) (@lem7218231 s f)). Qed.
Lemma lem7218234 (s : nat -> Prop) (f : nat -> real) : ((term443 s f) = (term444 s f)) = ((term442 s f) = (term457 s f)).
Proof. exact (MK_COMB (@lem7218225 s f) (@lem7218233 s f)). Qed.
Lemma lem7218235 (s : nat -> Prop) (f : nat -> real) : (term442 s f) = (term457 s f).
Proof. exact (EQ_MP (@lem7218234 s f) (@lem7218215 s f)). Qed.
Lemma lem7218236 (s : nat -> Prop) (f : nat -> real) : (term403 s f) = (term457 s f).
Proof. exact (TRANS (@lem7218211 s f) (@lem7218235 s f)). Qed.
Lemma lem7218237 (f : nat -> real) : (term404 f) = (term458 f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7218236 s f)). Qed.
Lemma lem7218238 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7218239 (f : nat -> real) : (term405 f) = (term459 f).
Proof. exact (MK_COMB (@lem7218238) (@lem7218237 f)). Qed.
Lemma lem7218241 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7218242 (P : type991) : (term460 P) = (term461 P).
Proof. exact (@lem7218241 (nat -> Prop) nat P). Qed.
Lemma lem7218243 (f : nat -> real) : (term462 f) = (term463 f).
Proof. exact (@lem7218242 (term464 f)). Qed.
Lemma lem7218244 (s : nat -> Prop) (f : nat -> real) : (term465 f s) = (term456 s f).
Proof. exact (eq_refl (term465 f s)). Qed.
Lemma lem7218245 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7218246 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term466 f s x) = (term467 s f x).
Proof. exact (MK_COMB (@lem7218244 s f) (@lem7218245 x)). Qed.
Lemma lem7218247 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term467 s f x) = (term454 x s f).
Proof. exact (eq_refl (term467 s f x)). Qed.
Lemma lem7218248 (x : nat) (s : nat -> Prop) (f : nat -> real) : (term466 f s x) = (term454 x s f).
Proof. exact (TRANS (@lem7218246 s f x) (@lem7218247 x s f)). Qed.
Lemma lem7218249 (s : nat -> Prop) (f : nat -> real) : (term468 f s) = (term456 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218248 x s f)). Qed.
Lemma lem7218250 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7218251 (s : nat -> Prop) (f : nat -> real) : (term469 f s) = (term457 s f).
Proof. exact (MK_COMB (@lem7218250) (@lem7218249 s f)). Qed.
Lemma lem7218252 (f : nat -> real) : (term470 f) = (term458 f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7218251 s f)). Qed.
Lemma lem7218253 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7218254 (f : nat -> real) : (term462 f) = (term459 f).
Proof. exact (MK_COMB (@lem7218253) (@lem7218252 f)). Qed.
Lemma lem7218255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7218256 (f : nat -> real) : (term471 f) = (term472 f).
Proof. exact (MK_COMB (@lem7218255) (@lem7218254 f)). Qed.
Lemma lem7218257 (s : nat -> Prop) (f : nat -> real) : (term465 f s) = (term456 s f).
Proof. exact (eq_refl (term465 f s)). Qed.
Lemma lem7218258 (x : type994) (s : nat -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7218259 (f : nat -> real) (x : type994) (s : nat -> Prop) : (term473 f x s) = (term474 f x s).
Proof. exact (MK_COMB (@lem7218257 s f) (@lem7218258 x s)). Qed.
Lemma lem7218260 (x : type994) (s : nat -> Prop) (f : nat -> real) : (term474 f x s) = (term475 x s f).
Proof. exact (eq_refl (term474 f x s)). Qed.
Lemma lem7218261 (x : type994) (s : nat -> Prop) (f : nat -> real) : (term473 f x s) = (term475 x s f).
Proof. exact (TRANS (@lem7218259 f x s) (@lem7218260 x s f)). Qed.
Lemma lem7218262 (x : type994) (f : nat -> real) : (term476 f x) = (term477 x f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7218261 x s f)). Qed.
Lemma lem7218263 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7218264 (x : type994) (f : nat -> real) : (term478 f x) = (term479 x f).
Proof. exact (MK_COMB (@lem7218263) (@lem7218262 x f)). Qed.
Lemma lem7218265 (f : nat -> real) : (term480 f) = (term481 f).
Proof. exact (fun_ext (fun x : type994 => @lem7218264 x f)). Qed.
Lemma lem7218266 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem7218267 (f : nat -> real) : (term463 f) = (term482 f).
Proof. exact (MK_COMB (@lem7218266) (@lem7218265 f)). Qed.
Lemma lem7218268 (f : nat -> real) : ((term462 f) = (term463 f)) = ((term459 f) = (term482 f)).
Proof. exact (MK_COMB (@lem7218256 f) (@lem7218267 f)). Qed.
Lemma lem7218269 (f : nat -> real) : (term459 f) = (term482 f).
Proof. exact (EQ_MP (@lem7218268 f) (@lem7218243 f)). Qed.
Lemma lem7218270 (f : nat -> real) : (term405 f) = (term482 f).
Proof. exact (TRANS (@lem7218239 f) (@lem7218269 f)). Qed.
Lemma lem7218271 : term406 = term483.
Proof. exact (fun_ext (fun f : nat -> real => @lem7218270 f)). Qed.
Lemma lem7218272 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7218273 : term407 = term484.
Proof. exact (MK_COMB (@lem7218272) (@lem7218271)). Qed.
Lemma lem7218275 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7218276 (P : type1004) : (term485 P) = (term486 P).
Proof. exact (@lem7218275 (nat -> real) type994 P). Qed.
Lemma lem7218277 : term487 = term488.
Proof. exact (@lem7218276 term489). Qed.
Lemma lem7218278 (f : nat -> real) : (term490 f) = (term481 f).
Proof. exact (eq_refl (term490 f)). Qed.
Lemma lem7218279 (x : type994) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7218280 (f : nat -> real) (x : type994) : (term491 f x) = (term492 f x).
Proof. exact (MK_COMB (@lem7218278 f) (@lem7218279 x)). Qed.
Lemma lem7218281 (x : type994) (f : nat -> real) : (term492 f x) = (term479 x f).
Proof. exact (eq_refl (term492 f x)). Qed.
Lemma lem7218282 (x : type994) (f : nat -> real) : (term491 f x) = (term479 x f).
Proof. exact (TRANS (@lem7218280 f x) (@lem7218281 x f)). Qed.
Lemma lem7218283 (f : nat -> real) : (term493 f) = (term481 f).
Proof. exact (fun_ext (fun x : type994 => @lem7218282 x f)). Qed.
Lemma lem7218284 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem7218285 (f : nat -> real) : (term494 f) = (term482 f).
Proof. exact (MK_COMB (@lem7218284) (@lem7218283 f)). Qed.
Lemma lem7218286 : term495 = term483.
Proof. exact (fun_ext (fun f : nat -> real => @lem7218285 f)). Qed.
Lemma lem7218287 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7218288 : term487 = term484.
Proof. exact (MK_COMB (@lem7218287) (@lem7218286)). Qed.
Lemma lem7218289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7218290 : term496 = term497.
Proof. exact (MK_COMB (@lem7218289) (@lem7218288)). Qed.
Lemma lem7218291 (f : nat -> real) : (term490 f) = (term481 f).
Proof. exact (eq_refl (term490 f)). Qed.
Lemma lem7218292 (x : type1007) (f : nat -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7218293 (x : type1007) (f : nat -> real) : (term498 x f) = (term499 x f).
Proof. exact (MK_COMB (@lem7218291 f) (@lem7218292 x f)). Qed.
Lemma lem7218294 (x : type1007) (f : nat -> real) : (term499 x f) = (term500 x f).
Proof. exact (eq_refl (term499 x f)). Qed.
Lemma lem7218295 (x : type1007) (f : nat -> real) : (term498 x f) = (term500 x f).
Proof. exact (TRANS (@lem7218293 x f) (@lem7218294 x f)). Qed.
Lemma lem7218296 (x : type1007) : (term501 x) = (term502 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7218295 x f)). Qed.
Lemma lem7218297 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7218298 (x : type1007) : (term503 x) = (term504 x).
Proof. exact (MK_COMB (@lem7218297) (@lem7218296 x)). Qed.
Lemma lem7218299 : term505 = term506.
Proof. exact (fun_ext (fun x : type1007 => @lem7218298 x)). Qed.
Lemma lem7218300 : (@ex ((nat -> real) -> (nat -> Prop) -> nat)) = (@ex ((nat -> real) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> real) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7218301 : term488 = term507.
Proof. exact (MK_COMB (@lem7218300) (@lem7218299)). Qed.
Lemma lem7218302 : (term487 = term488) = (term484 = term507).
Proof. exact (MK_COMB (@lem7218290) (@lem7218301)). Qed.
Lemma lem7218303 : term484 = term507.
Proof. exact (EQ_MP (@lem7218302) (@lem7218277)). Qed.
Lemma lem7218305 : term407 = term507.
Proof. exact (TRANS (@lem7218273) (@lem7218303)). Qed.
Lemma lem7218306 : term11 = term507.
Proof. exact (TRANS (@lem7218011) (@lem7218305)). Qed.
Lemma lem7218307 (h1 : term11) : term507.
Proof. exact (EQ_MP (@lem7218306) (@lem7216887 h1)). Qed.
Lemma lem7218308 (x : type1007) (h1 : term504 x) : term504 x.
Proof. exact (h1). Qed.
Lemma lem7218310 (f : nat -> real) (h1 : term158 f) : term158 f.
Proof. exact (h1). Qed.
Lemma lem7218311 (m : nat) (f : nat -> real) (h1 : term156 m f) : term156 m f.
Proof. exact (h1). Qed.
Lemma lem7218312 (m : nat) (n : nat) (f : nat -> real) (h1 : term154 m n f) : term154 m n f.
Proof. exact (h1). Qed.
Lemma lem7218313 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term151 m n f p.
Proof. exact (h1). Qed.
Lemma lem7218320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218321 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218320 nat (nat -> Prop) f x). Qed.
Lemma lem7218322 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7218321 Peano.le p). Qed.
Lemma lem7218323 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7218324 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7218322 p) (@lem7218323 n)). Qed.
Lemma lem7218326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218327 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7218326 nat Prop f x). Qed.
Lemma lem7218328 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term508 p n).
Proof. exact (@lem7218327 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7218330 (p : nat) (n : nat) : (Peano.le p n) = (term508 p n).
Proof. exact (TRANS (@lem7218324 p n) (@lem7218328 p n)). Qed.
Lemma lem7218337 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218338 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218337 nat (nat -> Prop) f x). Qed.
Lemma lem7218339 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7218338 Peano.le m). Qed.
Lemma lem7218340 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7218341 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7218339 m) (@lem7218340 p)). Qed.
Lemma lem7218343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218344 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7218343 nat Prop f x). Qed.
Lemma lem7218345 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term508 m p).
Proof. exact (@lem7218344 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7218347 (m : nat) (p : nat) : (Peano.le m p) = (term508 m p).
Proof. exact (TRANS (@lem7218341 m p) (@lem7218345 m p)). Qed.
Lemma lem7218348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7218349 (m : nat) (p : nat) : (term509 m p) = (term510 m p).
Proof. exact (MK_COMB (@lem7218348) (@lem7218347 m p)). Qed.
Lemma lem7218350 (m : nat) (p : nat) (n : nat) : (term67 m p n) = (term511 m p n).
Proof. exact (MK_COMB (@lem7218349 m p) (@lem7218330 p n)). Qed.
Lemma lem7218351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218361 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7218360 nat type1605 f x). Qed.
Lemma lem7218362 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7218361 dotdot m). Qed.
Lemma lem7218363 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7218364 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7218362 m) (@lem7218363 n)). Qed.
Lemma lem7218366 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218367 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218366 nat (nat -> Prop) f x). Qed.
Lemma lem7218368 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term512 m n).
Proof. exact (@lem7218367 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7218370 (m : nat) (n : nat) : (dotdot m n) = (term512 m n).
Proof. exact (TRANS (@lem7218364 m n) (@lem7218368 m n)). Qed.
Lemma lem7218371 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem7218372 (p : nat) (m : nat) (n : nat) : (term66 p m n) = (term513 p m n).
Proof. exact (MK_COMB (@lem7218371 p) (@lem7218370 m n)). Qed.
Lemma lem7218374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218375 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218374 nat type993 f x). Qed.
Lemma lem7218376 (p : nat) : (@IN nat p) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p).
Proof. exact (@lem7218375 (@IN nat) p). Qed.
Lemma lem7218377 (m : nat) (n : nat) : (term512 m n) = (term512 m n).
Proof. exact (eq_refl (term512 m n)). Qed.
Lemma lem7218378 (p : nat) (m : nat) (n : nat) : (term513 p m n) = (term514 p m n).
Proof. exact (MK_COMB (@lem7218376 p) (@lem7218377 m n)). Qed.
Lemma lem7218380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218381 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218380 (nat -> Prop) Prop f x). Qed.
Lemma lem7218382 (p : nat) (m : nat) (n : nat) : (term514 p m n) = (term515 p m n).
Proof. exact (@lem7218381 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p) (term512 m n)). Qed.
Lemma lem7218383 (p : nat) (m : nat) (n : nat) : (term513 p m n) = (term515 p m n).
Proof. exact (TRANS (@lem7218378 p m n) (@lem7218382 p m n)). Qed.
Lemma lem7218384 (p : nat) (m : nat) (n : nat) : (term66 p m n) = (term515 p m n).
Proof. exact (TRANS (@lem7218372 p m n) (@lem7218383 p m n)). Qed.
Lemma lem7218385 (p : nat) (m : nat) (n : nat) : (term516 p m n) = (term517 p m n).
Proof. exact (MK_COMB (@lem7218351) (@lem7218384 p m n)). Qed.
Lemma lem7218386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218387 (p : nat) (m : nat) (n : nat) : (term518 p m n) = (term519 p m n).
Proof. exact (MK_COMB (@lem7218386) (@lem7218385 p m n)). Qed.
Lemma lem7218388 (m : nat) (p : nat) (n : nat) : (term161 m p n) = (term520 m p n).
Proof. exact (MK_COMB (@lem7218387 p m n) (@lem7218350 m p n)). Qed.
Lemma lem7218389 (m : nat) (n : nat) : (term182 m n) = (term521 m n).
Proof. exact (fun_ext (fun p : nat => @lem7218388 m p n)). Qed.
Lemma lem7218390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218391 (m : nat) (n : nat) : (term197 m n) = (term522 m n).
Proof. exact (MK_COMB (@lem7218390) (@lem7218389 m n)). Qed.
Lemma lem7218392 (m : nat) : (term204 m) = (term523 m).
Proof. exact (fun_ext (fun n : nat => @lem7218391 m n)). Qed.
Lemma lem7218393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218394 (m : nat) : (term219 m) = (term524 m).
Proof. exact (MK_COMB (@lem7218393) (@lem7218392 m)). Qed.
Lemma lem7218395 : term226 = term525.
Proof. exact (fun_ext (fun m : nat => @lem7218394 m)). Qed.
Lemma lem7218396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218397 : term241 = term526.
Proof. exact (MK_COMB (@lem7218396) (@lem7218395)). Qed.
Lemma lem7218398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218405 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218406 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218405 nat (nat -> Prop) f x). Qed.
Lemma lem7218407 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7218406 Peano.le p). Qed.
Lemma lem7218408 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7218409 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7218407 p) (@lem7218408 n)). Qed.
Lemma lem7218411 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218412 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7218411 nat Prop f x). Qed.
Lemma lem7218413 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term508 p n).
Proof. exact (@lem7218412 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7218415 (p : nat) (n : nat) : (Peano.le p n) = (term508 p n).
Proof. exact (TRANS (@lem7218409 p n) (@lem7218413 p n)). Qed.
Lemma lem7218416 (p : nat) (n : nat) : (term527 p n) = (term528 p n).
Proof. exact (MK_COMB (@lem7218398) (@lem7218415 p n)). Qed.
Lemma lem7218417 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218425 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218424 nat (nat -> Prop) f x). Qed.
Lemma lem7218426 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7218425 Peano.le m). Qed.
Lemma lem7218427 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7218428 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7218426 m) (@lem7218427 p)). Qed.
Lemma lem7218430 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218431 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7218430 nat Prop f x). Qed.
Lemma lem7218432 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term508 m p).
Proof. exact (@lem7218431 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7218434 (m : nat) (p : nat) : (Peano.le m p) = (term508 m p).
Proof. exact (TRANS (@lem7218428 m p) (@lem7218432 m p)). Qed.
Lemma lem7218435 (m : nat) (p : nat) : (term527 m p) = (term528 m p).
Proof. exact (MK_COMB (@lem7218417) (@lem7218434 m p)). Qed.
Lemma lem7218436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218437 (m : nat) (p : nat) : (term529 m p) = (term530 m p).
Proof. exact (MK_COMB (@lem7218436) (@lem7218435 m p)). Qed.
Lemma lem7218438 (m : nat) (p : nat) (n : nat) : (term91 m p n) = (term531 m p n).
Proof. exact (MK_COMB (@lem7218437 m p) (@lem7218416 p n)). Qed.
Lemma lem7218447 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218448 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7218447 nat type1605 f x). Qed.
Lemma lem7218449 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7218448 dotdot m). Qed.
Lemma lem7218450 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7218451 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7218449 m) (@lem7218450 n)). Qed.
Lemma lem7218453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218454 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218453 nat (nat -> Prop) f x). Qed.
Lemma lem7218455 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term512 m n).
Proof. exact (@lem7218454 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7218457 (m : nat) (n : nat) : (dotdot m n) = (term512 m n).
Proof. exact (TRANS (@lem7218451 m n) (@lem7218455 m n)). Qed.
Lemma lem7218458 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem7218459 (p : nat) (m : nat) (n : nat) : (term66 p m n) = (term513 p m n).
Proof. exact (MK_COMB (@lem7218458 p) (@lem7218457 m n)). Qed.
Lemma lem7218461 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218462 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218461 nat type993 f x). Qed.
Lemma lem7218463 (p : nat) : (@IN nat p) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p).
Proof. exact (@lem7218462 (@IN nat) p). Qed.
Lemma lem7218464 (m : nat) (n : nat) : (term512 m n) = (term512 m n).
Proof. exact (eq_refl (term512 m n)). Qed.
Lemma lem7218465 (p : nat) (m : nat) (n : nat) : (term513 p m n) = (term514 p m n).
Proof. exact (MK_COMB (@lem7218463 p) (@lem7218464 m n)). Qed.
Lemma lem7218467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218468 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218467 (nat -> Prop) Prop f x). Qed.
Lemma lem7218469 (p : nat) (m : nat) (n : nat) : (term514 p m n) = (term515 p m n).
Proof. exact (@lem7218468 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p) (term512 m n)). Qed.
Lemma lem7218470 (p : nat) (m : nat) (n : nat) : (term513 p m n) = (term515 p m n).
Proof. exact (TRANS (@lem7218465 p m n) (@lem7218469 p m n)). Qed.
Lemma lem7218471 (p : nat) (m : nat) (n : nat) : (term66 p m n) = (term515 p m n).
Proof. exact (TRANS (@lem7218459 p m n) (@lem7218470 p m n)). Qed.
Lemma lem7218472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218473 (p : nat) (m : nat) (n : nat) : (term162 p m n) = (term532 p m n).
Proof. exact (MK_COMB (@lem7218472) (@lem7218471 p m n)). Qed.
Lemma lem7218474 (m : nat) (p : nat) (n : nat) : (term164 m p n) = (term533 m p n).
Proof. exact (MK_COMB (@lem7218473 p m n) (@lem7218438 m p n)). Qed.
Lemma lem7218475 (m : nat) (n : nat) : (term181 m n) = (term534 m n).
Proof. exact (fun_ext (fun p : nat => @lem7218474 m p n)). Qed.
Lemma lem7218476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218477 (m : nat) (n : nat) : (term192 m n) = (term535 m n).
Proof. exact (MK_COMB (@lem7218476) (@lem7218475 m n)). Qed.
Lemma lem7218478 (m : nat) : (term203 m) = (term536 m).
Proof. exact (fun_ext (fun n : nat => @lem7218477 m n)). Qed.
Lemma lem7218479 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218480 (m : nat) : (term214 m) = (term537 m).
Proof. exact (MK_COMB (@lem7218479) (@lem7218478 m)). Qed.
Lemma lem7218481 : term225 = term538.
Proof. exact (fun_ext (fun m : nat => @lem7218480 m)). Qed.
Lemma lem7218482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218483 : term236 = term539.
Proof. exact (MK_COMB (@lem7218482) (@lem7218481)). Qed.
Lemma lem7218484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7218485 : term238 = term540.
Proof. exact (MK_COMB (@lem7218484) (@lem7218483)). Qed.
Lemma lem7218486 : term242 = term541.
Proof. exact (MK_COMB (@lem7218485) (@lem7218397)). Qed.
Lemma lem7218487 (h1 : term73) : term541.
Proof. exact (EQ_MP (@lem7218486) (@lem7217595 h1)). Qed.
Lemma lem7218488 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem7218495 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218496 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7218495 nat type1605 f x). Qed.
Lemma lem7218497 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7218496 dotdot m). Qed.
Lemma lem7218498 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7218499 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7218497 m) (@lem7218498 n)). Qed.
Lemma lem7218501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218502 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218501 nat (nat -> Prop) f x). Qed.
Lemma lem7218503 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term512 m n).
Proof. exact (@lem7218502 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7218505 (m : nat) (n : nat) : (dotdot m n) = (term512 m n).
Proof. exact (TRANS (@lem7218499 m n) (@lem7218503 m n)). Qed.
Lemma lem7218506 (m : nat) (n : nat) : (term61 m n) = (term542 m n).
Proof. exact (MK_COMB (@lem7218488) (@lem7218505 m n)). Qed.
Lemma lem7218508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218509 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218508 (nat -> Prop) Prop f x). Qed.
Lemma lem7218510 (m : nat) (n : nat) : (term542 m n) = (term543 m n).
Proof. exact (@lem7218509 (@FINITE nat) (term512 m n)). Qed.
Lemma lem7218511 (m : nat) (n : nat) : (term61 m n) = (term543 m n).
Proof. exact (TRANS (@lem7218506 m n) (@lem7218510 m n)). Qed.
Lemma lem7218512 (m : nat) : (term62 m) = (term544 m).
Proof. exact (fun_ext (fun n : nat => @lem7218511 m n)). Qed.
Lemma lem7218513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218514 (m : nat) : (term63 m) = (term545 m).
Proof. exact (MK_COMB (@lem7218513) (@lem7218512 m)). Qed.
Lemma lem7218515 : term64 = term546.
Proof. exact (fun_ext (fun m : nat => @lem7218514 m)). Qed.
Lemma lem7218516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218517 : term65 = term547.
Proof. exact (MK_COMB (@lem7218516) (@lem7218515)). Qed.
Lemma lem7218518 (h1 : term65) : term547.
Proof. exact (EQ_MP (@lem7218517) (@lem7217615 h1)). Qed.
Lemma lem7218519 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7218524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218526 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218524 nat real f x). Qed.
Lemma lem7218527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7218532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218533 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7218532 nat nat f x). Qed.
Lemma lem7218535 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7218533 NUMERAL 0). Qed.
Lemma lem7218536 : term32 = term548.
Proof. exact (MK_COMB (@lem7218527) (@lem7218535)). Qed.
Lemma lem7218538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218539 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218538 nat real f x). Qed.
Lemma lem7218540 : term548 = term549.
Proof. exact (@lem7218539 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7218541 : term32 = term549.
Proof. exact (TRANS (@lem7218536) (@lem7218540)). Qed.
Lemma lem7218542 (f : nat -> real) (x : nat) : (term550 f x) = (term551 f x).
Proof. exact (MK_COMB (@lem7218519) (@lem7218526 f x)). Qed.
Lemma lem7218543 (f : nat -> real) (x : nat) : ((f x) = term32) = ((@I (nat -> real) f x) = term549).
Proof. exact (MK_COMB (@lem7218542 f x) (@lem7218541)). Qed.
Lemma lem7218544 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218552 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218551 nat type993 f x). Qed.
Lemma lem7218553 (x : nat) : (@IN nat x) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) x).
Proof. exact (@lem7218552 (@IN nat) x). Qed.
Lemma lem7218554 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7218555 (x : nat) (s : nat -> Prop) : (@IN nat x s) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) x s).
Proof. exact (MK_COMB (@lem7218553 x) (@lem7218554 s)). Qed.
Lemma lem7218557 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218558 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218557 (nat -> Prop) Prop f x). Qed.
Lemma lem7218559 (x : nat) (s : nat -> Prop) : (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) x s) = (term552 x s).
Proof. exact (@lem7218558 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) x) s). Qed.
Lemma lem7218561 (x : nat) (s : nat -> Prop) : (@IN nat x s) = (term552 x s).
Proof. exact (TRANS (@lem7218555 x s) (@lem7218559 x s)). Qed.
Lemma lem7218562 (x : nat) (s : nat -> Prop) : (term553 x s) = (term554 x s).
Proof. exact (MK_COMB (@lem7218544) (@lem7218561 x s)). Qed.
Lemma lem7218563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218564 (x : nat) (s : nat -> Prop) : (term555 x s) = (term556 x s).
Proof. exact (MK_COMB (@lem7218563) (@lem7218562 x s)). Qed.
Lemma lem7218565 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term397 s f x) = (term557 s f x).
Proof. exact (MK_COMB (@lem7218564 x s) (@lem7218543 f x)). Qed.
Lemma lem7218566 (s : nat -> Prop) (f : nat -> real) : (term398 s f) = (term558 s f).
Proof. exact (fun_ext (fun x : nat => @lem7218565 s f x)). Qed.
Lemma lem7218567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7218568 (s : nat -> Prop) (f : nat -> real) : (term399 s f) = (term559 s f).
Proof. exact (MK_COMB (@lem7218567) (@lem7218566 s f)). Qed.
Lemma lem7218569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218570 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7218577 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218578 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7218577 (nat -> Prop) type1011 f x). Qed.
Lemma lem7218579 (s : nat -> Prop) : (@sum nat s) = (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s).
Proof. exact (@lem7218578 (@sum nat) s). Qed.
Lemma lem7218580 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7218581 (s : nat -> Prop) (f : nat -> real) : (@sum nat s f) = (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s f).
Proof. exact (MK_COMB (@lem7218579 s) (@lem7218580 f)). Qed.
Lemma lem7218583 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218584 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7218583 (nat -> real) real f x). Qed.
Lemma lem7218585 (s : nat -> Prop) (f : nat -> real) : (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s f) = (term560 s f).
Proof. exact (@lem7218584 (@I ((nat -> Prop) -> (nat -> real) -> real) (@sum nat) s) f). Qed.
Lemma lem7218587 (s : nat -> Prop) (f : nat -> real) : (@sum nat s f) = (term560 s f).
Proof. exact (TRANS (@lem7218581 s f) (@lem7218585 s f)). Qed.
Lemma lem7218588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7218593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218594 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7218593 nat nat f x). Qed.
Lemma lem7218596 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7218594 NUMERAL 0). Qed.
Lemma lem7218597 : term32 = term548.
Proof. exact (MK_COMB (@lem7218588) (@lem7218596)). Qed.
Lemma lem7218599 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218600 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218599 nat real f x). Qed.
Lemma lem7218601 : term548 = term549.
Proof. exact (@lem7218600 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7218602 : term32 = term549.
Proof. exact (TRANS (@lem7218597) (@lem7218601)). Qed.
Lemma lem7218603 (s : nat -> Prop) (f : nat -> real) : (term561 s f) = (term562 s f).
Proof. exact (MK_COMB (@lem7218570) (@lem7218587 s f)). Qed.
Lemma lem7218604 (s : nat -> Prop) (f : nat -> real) : ((@sum nat s f) = term32) = ((term560 s f) = term549).
Proof. exact (MK_COMB (@lem7218603 s f) (@lem7218602)). Qed.
Lemma lem7218605 (s : nat -> Prop) (f : nat -> real) : (term387 s f) = (term563 s f).
Proof. exact (MK_COMB (@lem7218569) (@lem7218604 s f)). Qed.
Lemma lem7218606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218607 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7218608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7218613 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218614 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7218613 nat nat f x). Qed.
Lemma lem7218616 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7218614 NUMERAL 0). Qed.
Lemma lem7218617 : term32 = term548.
Proof. exact (MK_COMB (@lem7218608) (@lem7218616)). Qed.
Lemma lem7218619 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218620 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218619 nat real f x). Qed.
Lemma lem7218621 : term548 = term549.
Proof. exact (@lem7218620 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7218622 : term32 = term549.
Proof. exact (TRANS (@lem7218617) (@lem7218621)). Qed.
Lemma lem7218623 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7218630 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218631 (f : type1007) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7218630 (nat -> real) type994 f x). Qed.
Lemma lem7218632 (x : type1007) (f : nat -> real) : (x f) = (@I ((nat -> real) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7218631 x f). Qed.
Lemma lem7218633 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7218634 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (x f s) = (@I ((nat -> real) -> (nat -> Prop) -> nat) x f s).
Proof. exact (MK_COMB (@lem7218632 x f) (@lem7218633 s)). Qed.
Lemma lem7218636 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218637 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7218636 (nat -> Prop) nat f x). Qed.
Lemma lem7218638 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (@I ((nat -> real) -> (nat -> Prop) -> nat) x f s) = (term564 x f s).
Proof. exact (@lem7218637 (@I ((nat -> real) -> (nat -> Prop) -> nat) x f) s). Qed.
Lemma lem7218640 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (x f s) = (term564 x f s).
Proof. exact (TRANS (@lem7218634 x f s) (@lem7218638 x f s)). Qed.
Lemma lem7218641 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term565 x f s) = (term566 x f s).
Proof. exact (MK_COMB (@lem7218623 f) (@lem7218640 x f s)). Qed.
Lemma lem7218643 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218644 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218643 nat real f x). Qed.
Lemma lem7218645 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term566 x f s) = (term567 x f s).
Proof. exact (@lem7218644 f (term564 x f s)). Qed.
Lemma lem7218646 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term565 x f s) = (term567 x f s).
Proof. exact (TRANS (@lem7218641 x f s) (@lem7218645 x f s)). Qed.
Lemma lem7218647 : term568 = term569.
Proof. exact (MK_COMB (@lem7218607) (@lem7218622)). Qed.
Lemma lem7218648 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term570 x f s) = (term571 x f s).
Proof. exact (MK_COMB (@lem7218647) (@lem7218646 x f s)). Qed.
Lemma lem7218650 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218651 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7218650 real (real -> Prop) f x). Qed.
Lemma lem7218652 : term569 = term572.
Proof. exact (@lem7218651 real_le term549). Qed.
Lemma lem7218653 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term567 x f s) = (term567 x f s).
Proof. exact (eq_refl (term567 x f s)). Qed.
Lemma lem7218654 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term571 x f s) = (term573 x f s).
Proof. exact (MK_COMB (@lem7218652) (@lem7218653 x f s)). Qed.
Lemma lem7218656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218657 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7218656 real Prop f x). Qed.
Lemma lem7218658 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term573 x f s) = (term574 x f s).
Proof. exact (@lem7218657 term572 (term567 x f s)). Qed.
Lemma lem7218659 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term571 x f s) = (term574 x f s).
Proof. exact (TRANS (@lem7218654 x f s) (@lem7218658 x f s)). Qed.
Lemma lem7218660 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term570 x f s) = (term574 x f s).
Proof. exact (TRANS (@lem7218648 x f s) (@lem7218659 x f s)). Qed.
Lemma lem7218661 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term575 x f s) = (term576 x f s).
Proof. exact (MK_COMB (@lem7218606) (@lem7218660 x f s)). Qed.
Lemma lem7218662 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem7218669 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218670 (f : type1007) (x : nat -> real) : (f x) = (@I ((nat -> real) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7218669 (nat -> real) type994 f x). Qed.
Lemma lem7218671 (x : type1007) (f : nat -> real) : (x f) = (@I ((nat -> real) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7218670 x f). Qed.
Lemma lem7218672 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7218673 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (x f s) = (@I ((nat -> real) -> (nat -> Prop) -> nat) x f s).
Proof. exact (MK_COMB (@lem7218671 x f) (@lem7218672 s)). Qed.
Lemma lem7218675 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218676 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7218675 (nat -> Prop) nat f x). Qed.
Lemma lem7218677 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (@I ((nat -> real) -> (nat -> Prop) -> nat) x f s) = (term564 x f s).
Proof. exact (@lem7218676 (@I ((nat -> real) -> (nat -> Prop) -> nat) x f) s). Qed.
Lemma lem7218679 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (x f s) = (term564 x f s).
Proof. exact (TRANS (@lem7218673 x f s) (@lem7218677 x f s)). Qed.
Lemma lem7218680 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7218681 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term577 x f s) = (term578 x f s).
Proof. exact (MK_COMB (@lem7218662) (@lem7218679 x f s)). Qed.
Lemma lem7218682 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term579 x f s) = (term580 x f s).
Proof. exact (MK_COMB (@lem7218681 x f s) (@lem7218680 s)). Qed.
Lemma lem7218684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218685 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218684 nat type993 f x). Qed.
Lemma lem7218686 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term578 x f s) = (term581 x f s).
Proof. exact (@lem7218685 (@IN nat) (term564 x f s)). Qed.
Lemma lem7218687 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7218688 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term580 x f s) = (term582 x f s).
Proof. exact (MK_COMB (@lem7218686 x f s) (@lem7218687 s)). Qed.
Lemma lem7218690 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218691 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218690 (nat -> Prop) Prop f x). Qed.
Lemma lem7218692 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term582 x f s) = (term583 x f s).
Proof. exact (@lem7218691 (term581 x f s) s). Qed.
Lemma lem7218693 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term580 x f s) = (term583 x f s).
Proof. exact (TRANS (@lem7218688 x f s) (@lem7218692 x f s)). Qed.
Lemma lem7218694 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term579 x f s) = (term583 x f s).
Proof. exact (TRANS (@lem7218682 x f s) (@lem7218693 x f s)). Qed.
Lemma lem7218695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7218696 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term584 x f s) = (term585 x f s).
Proof. exact (MK_COMB (@lem7218695) (@lem7218694 x f s)). Qed.
Lemma lem7218697 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term586 x f s) = (term587 x f s).
Proof. exact (MK_COMB (@lem7218696 x f s) (@lem7218661 x f s)). Qed.
Lemma lem7218698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218699 (x : type1007) (f : nat -> real) (s : nat -> Prop) : (term588 x f s) = (term589 x f s).
Proof. exact (MK_COMB (@lem7218698) (@lem7218697 x f s)). Qed.
Lemma lem7218700 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term590 x s f) = (term591 x s f).
Proof. exact (MK_COMB (@lem7218699 x f s) (@lem7218605 s f)). Qed.
Lemma lem7218701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218706 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218707 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7218706 (nat -> Prop) Prop f x). Qed.
Lemma lem7218709 (s : nat -> Prop) : (@FINITE nat s) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) s).
Proof. exact (@lem7218707 (@FINITE nat) s). Qed.
Lemma lem7218710 (s : nat -> Prop) : (term430 s) = (term592 s).
Proof. exact (MK_COMB (@lem7218701) (@lem7218709 s)). Qed.
Lemma lem7218711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218712 (s : nat -> Prop) : (term393 s) = (term593 s).
Proof. exact (MK_COMB (@lem7218711) (@lem7218710 s)). Qed.
Lemma lem7218713 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term594 x s f) = (term595 x s f).
Proof. exact (MK_COMB (@lem7218712 s) (@lem7218700 x s f)). Qed.
Lemma lem7218714 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7218715 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term596 x s f) = (term597 x s f).
Proof. exact (MK_COMB (@lem7218714) (@lem7218713 x s f)). Qed.
Lemma lem7218716 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term598 x s f) = (term599 x s f).
Proof. exact (MK_COMB (@lem7218715 x s f) (@lem7218568 s f)). Qed.
Lemma lem7218717 (x : type1007) (f : nat -> real) : (term600 x f) = (term601 x f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7218716 x s f)). Qed.
Lemma lem7218718 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7218719 (x : type1007) (f : nat -> real) : (term500 x f) = (term602 x f).
Proof. exact (MK_COMB (@lem7218718) (@lem7218717 x f)). Qed.
Lemma lem7218720 (x : type1007) : (term502 x) = (term603 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7218719 x f)). Qed.
Lemma lem7218721 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7218722 (x : type1007) : (term504 x) = (term604 x).
Proof. exact (MK_COMB (@lem7218721) (@lem7218720 x)). Qed.
Lemma lem7218723 (x : type1007) (h1 : term504 x) : term604 x.
Proof. exact (EQ_MP (@lem7218722 x) (@lem7218308 x h1)). Qed.
Lemma lem7218929 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7218930 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7218935 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218936 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218935 nat real f x). Qed.
Lemma lem7218938 (f : nat -> real) (p : nat) : (f p) = (@I (nat -> real) f p).
Proof. exact (@lem7218936 f p). Qed.
Lemma lem7218939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7218944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218945 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7218944 nat nat f x). Qed.
Lemma lem7218947 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7218945 NUMERAL 0). Qed.
Lemma lem7218948 : term32 = term548.
Proof. exact (MK_COMB (@lem7218939) (@lem7218947)). Qed.
Lemma lem7218950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218951 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7218950 nat real f x). Qed.
Lemma lem7218952 : term548 = term549.
Proof. exact (@lem7218951 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7218953 : term32 = term549.
Proof. exact (TRANS (@lem7218948) (@lem7218952)). Qed.
Lemma lem7218954 (f : nat -> real) (p : nat) : (term550 f p) = (term551 f p).
Proof. exact (MK_COMB (@lem7218930) (@lem7218938 f p)). Qed.
Lemma lem7218955 (f : nat -> real) (p : nat) : ((f p) = term32) = ((@I (nat -> real) f p) = term549).
Proof. exact (MK_COMB (@lem7218954 f p) (@lem7218953)). Qed.
Lemma lem7218956 (f : nat -> real) (p : nat) : (term605 f p) = (term606 f p).
Proof. exact (MK_COMB (@lem7218929) (@lem7218955 f p)). Qed.
Lemma lem7218963 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218964 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218963 nat (nat -> Prop) f x). Qed.
Lemma lem7218965 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7218964 Peano.le p). Qed.
Lemma lem7218966 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7218967 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7218965 p) (@lem7218966 n)). Qed.
Lemma lem7218969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218970 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7218969 nat Prop f x). Qed.
Lemma lem7218971 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term508 p n).
Proof. exact (@lem7218970 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7218973 (p : nat) (n : nat) : (Peano.le p n) = (term508 p n).
Proof. exact (TRANS (@lem7218967 p n) (@lem7218971 p n)). Qed.
Lemma lem7218980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218981 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7218980 nat (nat -> Prop) f x). Qed.
Lemma lem7218982 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7218981 Peano.le m). Qed.
Lemma lem7218983 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7218984 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7218982 m) (@lem7218983 p)). Qed.
Lemma lem7218986 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7218987 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7218986 nat Prop f x). Qed.
Lemma lem7218988 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term508 m p).
Proof. exact (@lem7218987 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7218990 (m : nat) (p : nat) : (Peano.le m p) = (term508 m p).
Proof. exact (TRANS (@lem7218984 m p) (@lem7218988 m p)). Qed.
Lemma lem7218991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7218992 (m : nat) (p : nat) : (term509 m p) = (term510 m p).
Proof. exact (MK_COMB (@lem7218991) (@lem7218990 m p)). Qed.
Lemma lem7218993 (m : nat) (p : nat) (n : nat) : (term67 m p n) = (term511 m p n).
Proof. exact (MK_COMB (@lem7218992 m p) (@lem7218973 p n)). Qed.
Lemma lem7218994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7218995 (m : nat) (p : nat) (n : nat) : (term607 m p n) = (term608 m p n).
Proof. exact (MK_COMB (@lem7218994) (@lem7218993 m p n)). Qed.
Lemma lem7218996 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term102 m n f p) = (term609 m n f p).
Proof. exact (MK_COMB (@lem7218995 m p n) (@lem7218956 f p)). Qed.
Lemma lem7218997 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7218998 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7219005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219006 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7219005 nat type1605 f x). Qed.
Lemma lem7219007 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7219006 dotdot m). Qed.
Lemma lem7219008 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7219009 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7219007 m) (@lem7219008 n)). Qed.
Lemma lem7219011 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219012 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7219011 nat (nat -> Prop) f x). Qed.
Lemma lem7219013 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term512 m n).
Proof. exact (@lem7219012 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7219015 (m : nat) (n : nat) : (dotdot m n) = (term512 m n).
Proof. exact (TRANS (@lem7219009 m n) (@lem7219013 m n)). Qed.
Lemma lem7219016 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7219017 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (MK_COMB (@lem7218998) (@lem7219015 m n)). Qed.
Lemma lem7219018 (m : nat) (n : nat) (f : nat -> real) : (term77 m n f) = (term612 m n f).
Proof. exact (MK_COMB (@lem7219017 m n) (@lem7219016 f)). Qed.
Lemma lem7219020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219021 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7219020 (nat -> Prop) type1011 f x). Qed.
Lemma lem7219022 (m : nat) (n : nat) : (term611 m n) = (term613 m n).
Proof. exact (@lem7219021 (@sum nat) (term512 m n)). Qed.
Lemma lem7219023 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7219024 (m : nat) (n : nat) (f : nat -> real) : (term612 m n f) = (term614 m n f).
Proof. exact (MK_COMB (@lem7219022 m n) (@lem7219023 f)). Qed.
Lemma lem7219026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219027 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7219026 (nat -> real) real f x). Qed.
Lemma lem7219028 (m : nat) (n : nat) (f : nat -> real) : (term614 m n f) = (term615 m n f).
Proof. exact (@lem7219027 (term613 m n) f). Qed.
Lemma lem7219029 (m : nat) (n : nat) (f : nat -> real) : (term612 m n f) = (term615 m n f).
Proof. exact (TRANS (@lem7219024 m n f) (@lem7219028 m n f)). Qed.
Lemma lem7219030 (m : nat) (n : nat) (f : nat -> real) : (term77 m n f) = (term615 m n f).
Proof. exact (TRANS (@lem7219018 m n f) (@lem7219029 m n f)). Qed.
Lemma lem7219031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7219036 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219037 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7219036 nat nat f x). Qed.
Lemma lem7219039 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7219037 NUMERAL 0). Qed.
Lemma lem7219040 : term32 = term548.
Proof. exact (MK_COMB (@lem7219031) (@lem7219039)). Qed.
Lemma lem7219042 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219043 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7219042 nat real f x). Qed.
Lemma lem7219044 : term548 = term549.
Proof. exact (@lem7219043 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7219045 : term32 = term549.
Proof. exact (TRANS (@lem7219040) (@lem7219044)). Qed.
Lemma lem7219046 (m : nat) (n : nat) (f : nat -> real) : (term616 m n f) = (term617 m n f).
Proof. exact (MK_COMB (@lem7218997) (@lem7219030 m n f)). Qed.
Lemma lem7219047 (m : nat) (n : nat) (f : nat -> real) : ((term77 m n f) = term32) = ((term615 m n f) = term549).
Proof. exact (MK_COMB (@lem7219046 m n f) (@lem7219045)). Qed.
Lemma lem7219048 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7219049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7219054 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219055 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7219054 nat nat f x). Qed.
Lemma lem7219057 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7219055 NUMERAL 0). Qed.
Lemma lem7219058 : term32 = term548.
Proof. exact (MK_COMB (@lem7219049) (@lem7219057)). Qed.
Lemma lem7219060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219061 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7219060 nat real f x). Qed.
Lemma lem7219062 : term548 = term549.
Proof. exact (@lem7219061 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7219063 : term32 = term549.
Proof. exact (TRANS (@lem7219058) (@lem7219062)). Qed.
Lemma lem7219068 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219069 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7219068 nat real f x). Qed.
Lemma lem7219071 (f : nat -> real) (p : nat) : (f p) = (@I (nat -> real) f p).
Proof. exact (@lem7219069 f p). Qed.
Lemma lem7219072 : term568 = term569.
Proof. exact (MK_COMB (@lem7219048) (@lem7219063)). Qed.
Lemma lem7219073 (f : nat -> real) (p : nat) : (term92 f p) = (term618 f p).
Proof. exact (MK_COMB (@lem7219072) (@lem7219071 f p)). Qed.
Lemma lem7219075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219076 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7219075 real (real -> Prop) f x). Qed.
Lemma lem7219077 : term569 = term572.
Proof. exact (@lem7219076 real_le term549). Qed.
Lemma lem7219078 (f : nat -> real) (p : nat) : (@I (nat -> real) f p) = (@I (nat -> real) f p).
Proof. exact (eq_refl (@I (nat -> real) f p)). Qed.
Lemma lem7219079 (f : nat -> real) (p : nat) : (term618 f p) = (term619 f p).
Proof. exact (MK_COMB (@lem7219077) (@lem7219078 f p)). Qed.
Lemma lem7219081 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219082 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7219081 real Prop f x). Qed.
Lemma lem7219083 (f : nat -> real) (p : nat) : (term619 f p) = (term620 f p).
Proof. exact (@lem7219082 term572 (@I (nat -> real) f p)). Qed.
Lemma lem7219084 (f : nat -> real) (p : nat) : (term618 f p) = (term620 f p).
Proof. exact (TRANS (@lem7219079 f p) (@lem7219083 f p)). Qed.
Lemma lem7219085 (f : nat -> real) (p : nat) : (term92 f p) = (term620 f p).
Proof. exact (TRANS (@lem7219073 f p) (@lem7219084 f p)). Qed.
Lemma lem7219086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7219093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219094 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7219093 nat (nat -> Prop) f x). Qed.
Lemma lem7219095 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7219094 Peano.le p). Qed.
Lemma lem7219096 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7219097 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7219095 p) (@lem7219096 n)). Qed.
Lemma lem7219099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219100 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7219099 nat Prop f x). Qed.
Lemma lem7219101 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term508 p n).
Proof. exact (@lem7219100 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7219103 (p : nat) (n : nat) : (Peano.le p n) = (term508 p n).
Proof. exact (TRANS (@lem7219097 p n) (@lem7219101 p n)). Qed.
Lemma lem7219104 (p : nat) (n : nat) : (term527 p n) = (term528 p n).
Proof. exact (MK_COMB (@lem7219086) (@lem7219103 p n)). Qed.
Lemma lem7219105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7219112 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219113 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7219112 nat (nat -> Prop) f x). Qed.
Lemma lem7219114 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7219113 Peano.le m). Qed.
Lemma lem7219115 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7219116 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7219114 m) (@lem7219115 p)). Qed.
Lemma lem7219118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7219119 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7219118 nat Prop f x). Qed.
Lemma lem7219120 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term508 m p).
Proof. exact (@lem7219119 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7219122 (m : nat) (p : nat) : (Peano.le m p) = (term508 m p).
Proof. exact (TRANS (@lem7219116 m p) (@lem7219120 m p)). Qed.
Lemma lem7219123 (m : nat) (p : nat) : (term527 m p) = (term528 m p).
Proof. exact (MK_COMB (@lem7219105) (@lem7219122 m p)). Qed.
Lemma lem7219124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7219125 (m : nat) (p : nat) : (term529 m p) = (term530 m p).
Proof. exact (MK_COMB (@lem7219124) (@lem7219123 m p)). Qed.
Lemma lem7219126 (m : nat) (p : nat) (n : nat) : (term91 m p n) = (term531 m p n).
Proof. exact (MK_COMB (@lem7219125 m p) (@lem7219104 p n)). Qed.
Lemma lem7219127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7219128 (m : nat) (p : nat) (n : nat) : (term94 m p n) = (term621 m p n).
Proof. exact (MK_COMB (@lem7219127) (@lem7219126 m p n)). Qed.
Lemma lem7219129 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term96 m n f p) = (term622 m n f p).
Proof. exact (MK_COMB (@lem7219128 m p n) (@lem7219085 f p)). Qed.
Lemma lem7219130 (m : nat) (n : nat) (f : nat -> real) : (term97 m n f) = (term623 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7219129 m n f p)). Qed.
Lemma lem7219131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219132 (m : nat) (n : nat) (f : nat -> real) : (term98 m n f) = (term624 m n f).
Proof. exact (MK_COMB (@lem7219131) (@lem7219130 m n f)). Qed.
Lemma lem7219133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7219134 (m : nat) (n : nat) (f : nat -> real) : (term99 m n f) = (term625 m n f).
Proof. exact (MK_COMB (@lem7219133) (@lem7219132 m n f)). Qed.
Lemma lem7219135 (m : nat) (n : nat) (f : nat -> real) : (term100 m n f) = (term626 m n f).
Proof. exact (MK_COMB (@lem7219134 m n f) (@lem7219047 m n f)). Qed.
Lemma lem7219136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7219137 (m : nat) (n : nat) (f : nat -> real) : (term113 m n f) = (term627 m n f).
Proof. exact (MK_COMB (@lem7219136) (@lem7219135 m n f)). Qed.
Lemma lem7219138 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term151 m n f p) = (term628 m n f p).
Proof. exact (MK_COMB (@lem7219137 m n f) (@lem7218996 m n f p)). Qed.
Lemma lem7219139 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term628 m n f p.
Proof. exact (EQ_MP (@lem7219138 m n f p) (@lem7218313 m n f p h1)). Qed.
Lemma lem7219140 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term609 m n f p.
Proof. exact (proj2 (@lem7219139 m n f p h1)). Qed.
Lemma lem7219141 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term626 m n f.
Proof. exact (proj1 (@lem7219139 m n f p h1)). Qed.
Lemma lem7219143 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term511 m p n.
Proof. exact (proj1 (@lem7219140 m n f p h1)). Qed.
Lemma lem7219147 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term624 m n f.
Proof. exact (proj1 (@lem7219141 m n f p h1)). Qed.
Lemma lem7219148 (h1 : term73) : term526.
Proof. exact (proj2 (@lem7218487 h1)). Qed.
Lemma lem7219149 (h1 : term73) : term539.
Proof. exact (proj1 (@lem7218487 h1)). Qed.
Lemma lem7219151 (m : nat) (n : nat) : (term543 m n) = (term543 m n).
Proof. exact (eq_refl (term543 m n)). Qed.
Lemma lem7219152 (m : nat) : (term544 m) = (term544 m).
Proof. exact (fun_ext (fun n : nat => @lem7219151 m n)). Qed.
Lemma lem7219153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219154 (m : nat) : (term545 m) = (term545 m).
Proof. exact (MK_COMB (@lem7219153) (@lem7219152 m)). Qed.
Lemma lem7219155 : term546 = term546.
Proof. exact (fun_ext (fun m : nat => @lem7219154 m)). Qed.
Lemma lem7219156 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219158 : term547 = term547.
Proof. exact (MK_COMB (@lem7219156) (@lem7219155)). Qed.
Lemma lem7219159 (h1 : term65) : term547.
Proof. exact (EQ_MP (@lem7219158) (@lem7218518 h1)). Qed.
Lemma lem7219161 {A : Type'} (P : Prop) (Q : A -> Prop) : (term629 A P Q) = (term630 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7219162 (P : Prop) (Q : nat -> Prop) : (term631 P Q) = (term632 P Q).
Proof. exact (@lem7219161 nat P Q). Qed.
Lemma lem7219163 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term633 x s f) = (term634 x s f).
Proof. exact (@lem7219162 (term595 x s f) (term558 s f)). Qed.
Lemma lem7219164 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term635 s f x) = (term557 s f x).
Proof. exact (eq_refl (term635 s f x)). Qed.
Lemma lem7219165 (s : nat -> Prop) (f : nat -> real) : (term636 s f) = (term558 s f).
Proof. exact (fun_ext (fun x : nat => @lem7219164 s f x)). Qed.
Lemma lem7219166 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219167 (s : nat -> Prop) (f : nat -> real) : (term637 s f) = (term559 s f).
Proof. exact (MK_COMB (@lem7219166) (@lem7219165 s f)). Qed.
Lemma lem7219168 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term597 x s f) = (term597 x s f).
Proof. exact (eq_refl (term597 x s f)). Qed.
Lemma lem7219169 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term633 x s f) = (term599 x s f).
Proof. exact (MK_COMB (@lem7219168 x s f) (@lem7219167 s f)). Qed.
Lemma lem7219170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7219171 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term638 x s f) = (term639 x s f).
Proof. exact (MK_COMB (@lem7219170) (@lem7219169 x s f)). Qed.
Lemma lem7219172 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term635 s f x) = (term557 s f x).
Proof. exact (eq_refl (term635 s f x)). Qed.
Lemma lem7219173 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term597 x s f) = (term597 x s f).
Proof. exact (eq_refl (term597 x s f)). Qed.
Lemma lem7219174 (x : type1007) (s : nat -> Prop) (f : nat -> real) (x' : nat) : (term640 x s f x') = (term641 x s f x').
Proof. exact (MK_COMB (@lem7219173 x s f) (@lem7219172 s f x')). Qed.
Lemma lem7219175 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term642 x s f) = (term643 x s f).
Proof. exact (fun_ext (fun x' : nat => @lem7219174 x s f x')). Qed.
Lemma lem7219176 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219177 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term634 x s f) = (term644 x s f).
Proof. exact (MK_COMB (@lem7219176) (@lem7219175 x s f)). Qed.
Lemma lem7219178 (x : type1007) (s : nat -> Prop) (f : nat -> real) : ((term633 x s f) = (term634 x s f)) = ((term599 x s f) = (term644 x s f)).
Proof. exact (MK_COMB (@lem7219171 x s f) (@lem7219177 x s f)). Qed.
Lemma lem7219179 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term599 x s f) = (term644 x s f).
Proof. exact (EQ_MP (@lem7219178 x s f) (@lem7219163 x s f)). Qed.
Lemma lem7219180 (x : type1007) (f : nat -> real) : (term601 x f) = (term645 x f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7219179 x s f)). Qed.
Lemma lem7219181 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7219182 (x : type1007) (f : nat -> real) : (term602 x f) = (term646 x f).
Proof. exact (MK_COMB (@lem7219181) (@lem7219180 x f)). Qed.
Lemma lem7219183 (x : type1007) : (term603 x) = (term647 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7219182 x f)). Qed.
Lemma lem7219184 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7219185 (x : type1007) : (term604 x) = (term648 x).
Proof. exact (MK_COMB (@lem7219184) (@lem7219183 x)). Qed.
Lemma lem7219192 (s : nat -> Prop) (f : nat -> real) (x : nat) : (term557 s f x) = (term557 s f x).
Proof. exact (eq_refl (term557 s f x)). Qed.
Lemma lem7219209 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term591 x s f) = (term649 x s f).
Proof. exact (@lem19699 (term583 x f s) (term576 x f s) (term563 s f)). Qed.
Lemma lem7219212 (s : nat -> Prop) : (term593 s) = (term593 s).
Proof. exact (eq_refl (term593 s)). Qed.
Lemma lem7219213 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term595 x s f) = (term650 x s f).
Proof. exact (MK_COMB (@lem7219212 s) (@lem7219209 x s f)). Qed.
Lemma lem7219220 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term650 x s f) = (term651 x s f).
Proof. exact (@lem19490 (term652 x s f) (term592 s) (term653 x s f)). Qed.
Lemma lem7219221 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term595 x s f) = (term651 x s f).
Proof. exact (TRANS (@lem7219213 x s f) (@lem7219220 x s f)). Qed.
Lemma lem7219222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7219223 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term597 x s f) = (term654 x s f).
Proof. exact (MK_COMB (@lem7219222) (@lem7219221 x s f)). Qed.
Lemma lem7219224 (x : type1007) (s : nat -> Prop) (f : nat -> real) (x' : nat) : (term641 x s f x') = (term655 x s f x').
Proof. exact (MK_COMB (@lem7219223 x s f) (@lem7219192 s f x')). Qed.
Lemma lem7219231 (x : type1007) (s : nat -> Prop) (f : nat -> real) (x' : nat) : (term655 x s f x') = (term656 x s f x').
Proof. exact (@lem19699 (term657 x s f) (term658 x s f) (term557 s f x')). Qed.
Lemma lem7219232 (x : type1007) (s : nat -> Prop) (f : nat -> real) (x' : nat) : (term641 x s f x') = (term656 x s f x').
Proof. exact (TRANS (@lem7219224 x s f x') (@lem7219231 x s f x')). Qed.
Lemma lem7219233 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term643 x s f) = (term659 x s f).
Proof. exact (fun_ext (fun x' : nat => @lem7219232 x s f x')). Qed.
Lemma lem7219234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219235 (x : type1007) (s : nat -> Prop) (f : nat -> real) : (term644 x s f) = (term660 x s f).
Proof. exact (MK_COMB (@lem7219234) (@lem7219233 x s f)). Qed.
Lemma lem7219236 (x : type1007) (f : nat -> real) : (term645 x f) = (term661 x f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7219235 x s f)). Qed.
Lemma lem7219237 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7219238 (x : type1007) (f : nat -> real) : (term646 x f) = (term662 x f).
Proof. exact (MK_COMB (@lem7219237) (@lem7219236 x f)). Qed.
Lemma lem7219239 (x : type1007) : (term647 x) = (term663 x).
Proof. exact (fun_ext (fun f : nat -> real => @lem7219238 x f)). Qed.
Lemma lem7219240 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7219241 (x : type1007) : (term648 x) = (term664 x).
Proof. exact (MK_COMB (@lem7219240) (@lem7219239 x)). Qed.
Lemma lem7219242 (x : type1007) : (term604 x) = (term664 x).
Proof. exact (TRANS (@lem7219185 x) (@lem7219241 x)). Qed.
Lemma lem7219243 (x : type1007) (h1 : term504 x) : term664 x.
Proof. exact (EQ_MP (@lem7219242 x) (@lem7218723 x h1)). Qed.
Lemma lem7219353 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term622 m n f p) = (term622 m n f p).
Proof. exact (eq_refl (term622 m n f p)). Qed.
Lemma lem7219354 (m : nat) (n : nat) (f : nat -> real) : (term623 m n f) = (term623 m n f).
Proof. exact (fun_ext (fun p : nat => @lem7219353 m n f p)). Qed.
Lemma lem7219355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219357 (m : nat) (n : nat) (f : nat -> real) : (term624 m n f) = (term624 m n f).
Proof. exact (MK_COMB (@lem7219355) (@lem7219354 m n f)). Qed.
Lemma lem7219358 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term624 m n f.
Proof. exact (EQ_MP (@lem7219357 m n f) (@lem7219147 m n f p h1)). Qed.
Lemma lem7219376 (m : nat) (p : nat) (n : nat) : (term533 m p n) = (term533 m p n).
Proof. exact (eq_refl (term533 m p n)). Qed.
Lemma lem7219377 (m : nat) (n : nat) : (term534 m n) = (term534 m n).
Proof. exact (fun_ext (fun p : nat => @lem7219376 m p n)). Qed.
Lemma lem7219378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219379 (m : nat) (n : nat) : (term535 m n) = (term535 m n).
Proof. exact (MK_COMB (@lem7219378) (@lem7219377 m n)). Qed.
Lemma lem7219380 (m : nat) : (term536 m) = (term536 m).
Proof. exact (fun_ext (fun n : nat => @lem7219379 m n)). Qed.
Lemma lem7219381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219382 (m : nat) : (term537 m) = (term537 m).
Proof. exact (MK_COMB (@lem7219381) (@lem7219380 m)). Qed.
Lemma lem7219383 : term538 = term538.
Proof. exact (fun_ext (fun m : nat => @lem7219382 m)). Qed.
Lemma lem7219384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219386 : term539 = term539.
Proof. exact (MK_COMB (@lem7219384) (@lem7219383)). Qed.
Lemma lem7219387 (h1 : term73) : term539.
Proof. exact (EQ_MP (@lem7219386) (@lem7219149 h1)). Qed.
Lemma lem7219405 (m : nat) (p : nat) (n : nat) : (term520 m p n) = (term665 m p n).
Proof. exact (@lem19490 (term508 m p) (term517 p m n) (term508 p n)). Qed.
Lemma lem7219406 (m : nat) (n : nat) : (term521 m n) = (term666 m n).
Proof. exact (fun_ext (fun p : nat => @lem7219405 m p n)). Qed.
Lemma lem7219407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219408 (m : nat) (n : nat) : (term522 m n) = (term667 m n).
Proof. exact (MK_COMB (@lem7219407) (@lem7219406 m n)). Qed.
Lemma lem7219409 (m : nat) : (term523 m) = (term668 m).
Proof. exact (fun_ext (fun n : nat => @lem7219408 m n)). Qed.
Lemma lem7219410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219411 (m : nat) : (term524 m) = (term669 m).
Proof. exact (MK_COMB (@lem7219410) (@lem7219409 m)). Qed.
Lemma lem7219412 : term525 = term670.
Proof. exact (fun_ext (fun m : nat => @lem7219411 m)). Qed.
Lemma lem7219413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7219415 : term526 = term671.
Proof. exact (MK_COMB (@lem7219413) (@lem7219412)). Qed.
Lemma lem7219416 (h1 : term73) : term671.
Proof. exact (EQ_MP (@lem7219415) (@lem7219148 h1)). Qed.
Lemma lem7219417 (_96742 : nat) (h1 : term65) : term672 _96742.
Proof. exact (@lem7219159 h1 _96742). Qed.
Lemma lem7219418 (_96742 : nat) : (term672 _96742) = (term545 _96742).
Proof. exact (eq_refl (term672 _96742)). Qed.
Lemma lem7219419 (_96742 : nat) (h1 : term65) : term545 _96742.
Proof. exact (EQ_MP (@lem7219418 _96742) (@lem7219417 _96742 h1)). Qed.
Lemma lem7219420 (_96742 : nat) (_96743 : nat) (h1 : term65) : term673 _96742 _96743.
Proof. exact (@lem7219419 _96742 h1 _96743). Qed.
Lemma lem7219421 (_96742 : nat) (_96743 : nat) : (term673 _96742 _96743) = (term543 _96742 _96743).
Proof. exact (eq_refl (term673 _96742 _96743)). Qed.
Lemma lem7219423 (_96744 : nat -> real) (x : type1007) (h1 : term504 x) : term674 x _96744.
Proof. exact (@lem7219243 x h1 _96744). Qed.
Lemma lem7219424 (x : type1007) (_96744 : nat -> real) : (term674 x _96744) = (term662 x _96744).
Proof. exact (eq_refl (term674 x _96744)). Qed.
Lemma lem7219425 (_96744 : nat -> real) (x : type1007) (h1 : term504 x) : term662 x _96744.
Proof. exact (EQ_MP (@lem7219424 x _96744) (@lem7219423 _96744 x h1)). Qed.
Lemma lem7219426 (_96744 : nat -> real) (_96745 : nat -> Prop) (x : type1007) (h1 : term504 x) : term675 x _96744 _96745.
Proof. exact (@lem7219425 _96744 x h1 _96745). Qed.
Lemma lem7219427 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) : (term675 x _96744 _96745) = (term660 x _96745 _96744).
Proof. exact (eq_refl (term675 x _96744 _96745)). Qed.
Lemma lem7219428 (_96745 : nat -> Prop) (_96744 : nat -> real) (x : type1007) (h1 : term504 x) : term660 x _96745 _96744.
Proof. exact (EQ_MP (@lem7219427 x _96745 _96744) (@lem7219426 _96744 _96745 x h1)). Qed.
Lemma lem7219429 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term676 x _96745 _96744 _96746.
Proof. exact (@lem7219428 _96745 _96744 x h1 _96746). Qed.
Lemma lem7219430 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term676 x _96745 _96744 _96746) = (term656 x _96745 _96744 _96746).
Proof. exact (eq_refl (term676 x _96745 _96744 _96746)). Qed.
Lemma lem7219431 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term656 x _96745 _96744 _96746.
Proof. exact (EQ_MP (@lem7219430 x _96745 _96744 _96746) (@lem7219429 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7219441 (_96750 : nat) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term677 m n f _96750.
Proof. exact (@lem7219358 m n f p h1 _96750). Qed.
Lemma lem7219442 (m : nat) (n : nat) (f : nat -> real) (_96750 : nat) : (term677 m n f _96750) = (term622 m n f _96750).
Proof. exact (eq_refl (term677 m n f _96750)). Qed.
Lemma lem7219443 (_96750 : nat) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term622 m n f _96750.
Proof. exact (EQ_MP (@lem7219442 m n f _96750) (@lem7219441 _96750 m n f p h1)). Qed.
Lemma lem7219444 (_96751 : nat) (h1 : term73) : term678 _96751.
Proof. exact (@lem7219387 h1 _96751). Qed.
Lemma lem7219445 (_96751 : nat) : (term678 _96751) = (term537 _96751).
Proof. exact (eq_refl (term678 _96751)). Qed.
Lemma lem7219446 (_96751 : nat) (h1 : term73) : term537 _96751.
Proof. exact (EQ_MP (@lem7219445 _96751) (@lem7219444 _96751 h1)). Qed.
Lemma lem7219447 (_96751 : nat) (_96752 : nat) (h1 : term73) : term679 _96751 _96752.
Proof. exact (@lem7219446 _96751 h1 _96752). Qed.
Lemma lem7219448 (_96751 : nat) (_96752 : nat) : (term679 _96751 _96752) = (term535 _96751 _96752).
Proof. exact (eq_refl (term679 _96751 _96752)). Qed.
Lemma lem7219449 (_96751 : nat) (_96752 : nat) (h1 : term73) : term535 _96751 _96752.
Proof. exact (EQ_MP (@lem7219448 _96751 _96752) (@lem7219447 _96751 _96752 h1)). Qed.
Lemma lem7219450 (_96751 : nat) (_96752 : nat) (_96753 : nat) (h1 : term73) : term680 _96751 _96752 _96753.
Proof. exact (@lem7219449 _96751 _96752 h1 _96753). Qed.
Lemma lem7219451 (_96751 : nat) (_96753 : nat) (_96752 : nat) : (term680 _96751 _96752 _96753) = (term533 _96751 _96753 _96752).
Proof. exact (eq_refl (term680 _96751 _96752 _96753)). Qed.
Lemma lem7219453 (_96754 : nat) (h1 : term73) : term681 _96754.
Proof. exact (@lem7219416 h1 _96754). Qed.
Lemma lem7219454 (_96754 : nat) : (term681 _96754) = (term669 _96754).
Proof. exact (eq_refl (term681 _96754)). Qed.
Lemma lem7219455 (_96754 : nat) (h1 : term73) : term669 _96754.
Proof. exact (EQ_MP (@lem7219454 _96754) (@lem7219453 _96754 h1)). Qed.
Lemma lem7219456 (_96754 : nat) (_96755 : nat) (h1 : term73) : term682 _96754 _96755.
Proof. exact (@lem7219455 _96754 h1 _96755). Qed.
Lemma lem7219457 (_96754 : nat) (_96755 : nat) : (term682 _96754 _96755) = (term667 _96754 _96755).
Proof. exact (eq_refl (term682 _96754 _96755)). Qed.
Lemma lem7219458 (_96754 : nat) (_96755 : nat) (h1 : term73) : term667 _96754 _96755.
Proof. exact (EQ_MP (@lem7219457 _96754 _96755) (@lem7219456 _96754 _96755 h1)). Qed.
Lemma lem7219459 (_96754 : nat) (_96755 : nat) (_96756 : nat) (h1 : term73) : term683 _96754 _96755 _96756.
Proof. exact (@lem7219458 _96754 _96755 h1 _96756). Qed.
Lemma lem7219460 (_96754 : nat) (_96756 : nat) (_96755 : nat) : (term683 _96754 _96755 _96756) = (term665 _96754 _96756 _96755).
Proof. exact (eq_refl (term683 _96754 _96755 _96756)). Qed.
Lemma lem7219461 (_96754 : nat) (_96756 : nat) (_96755 : nat) (h1 : term73) : term665 _96754 _96756 _96755.
Proof. exact (EQ_MP (@lem7219460 _96754 _96756 _96755) (@lem7219459 _96754 _96755 _96756 h1)). Qed.
Lemma lem7219466 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term684 x _96745 _96744 _96746.
Proof. exact (proj2 (@lem7219431 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7219467 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term685 x _96745 _96744 _96746.
Proof. exact (proj1 (@lem7219431 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7219471 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term606 f p.
Proof. exact (proj2 (@lem7219140 m n f p h1)). Qed.
Lemma lem7219486 (m : nat) (n : nat) (f : nat -> real) (_96750 : nat) : (term622 m n f _96750) = (term686 m n f _96750).
Proof. exact (@lem7216422 (term528 m _96750) (term528 _96750 n) (term620 f _96750)). Qed.
Lemma lem7219487 (_96750 : nat) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term686 m n f _96750.
Proof. exact (EQ_MP (@lem7219486 m n f _96750) (@lem7219443 _96750 m n f p h1)). Qed.
Lemma lem7219499 (_96751 : nat) (_96753 : nat) (_96752 : nat) (h1 : term73) : term533 _96751 _96753 _96752.
Proof. exact (EQ_MP (@lem7219451 _96751 _96753 _96752) (@lem7219450 _96751 _96752 _96753 h1)). Qed.
Lemma lem7219505 (_96755 : nat) (_96754 : nat) (_96756 : nat) (h1 : term73) : term687 _96755 _96754 _96756.
Proof. exact (proj1 (@lem7219461 _96754 _96756 _96755 h1)). Qed.
Lemma lem7219511 (_96754 : nat) (_96756 : nat) (_96755 : nat) (h1 : term73) : term688 _96754 _96756 _96755.
Proof. exact (proj2 (@lem7219461 _96754 _96756 _96755 h1)). Qed.
Lemma lem7219563 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term685 x _96745 _96744 _96746) = (term689 x _96745 _96744 _96746).
Proof. exact (@lem7216422 (term592 _96745) (term652 x _96745 _96744) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7219570 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term690 x _96745 _96744 _96746) = (term691 x _96745 _96744 _96746).
Proof. exact (@lem7216422 (term583 x _96744 _96745) (term563 _96745 _96744) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7219571 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7219574 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term689 x _96745 _96744 _96746) = (term692 x _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7219571 _96745) (@lem7219570 x _96745 _96744 _96746)). Qed.
Lemma lem7219576 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term685 x _96745 _96744 _96746) = (term692 x _96745 _96744 _96746).
Proof. exact (TRANS (@lem7219563 x _96745 _96744 _96746) (@lem7219574 x _96745 _96744 _96746)). Qed.
Lemma lem7219577 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term692 x _96745 _96744 _96746.
Proof. exact (EQ_MP (@lem7219576 x _96745 _96744 _96746) (@lem7219467 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7219585 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term684 x _96745 _96744 _96746) = (term693 x _96745 _96744 _96746).
Proof. exact (@lem7216422 (term592 _96745) (term653 x _96745 _96744) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7219592 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term694 x _96745 _96744 _96746) = (term695 x _96745 _96744 _96746).
Proof. exact (@lem7216422 (term576 x _96744 _96745) (term563 _96745 _96744) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7219593 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7219596 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term693 x _96745 _96744 _96746) = (term696 x _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7219593 _96745) (@lem7219592 x _96745 _96744 _96746)). Qed.
Lemma lem7219598 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term684 x _96745 _96744 _96746) = (term696 x _96745 _96744 _96746).
Proof. exact (TRANS (@lem7219585 x _96745 _96744 _96746) (@lem7219596 x _96745 _96744 _96746)). Qed.
Lemma lem7219599 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term696 x _96745 _96744 _96746.
Proof. exact (EQ_MP (@lem7219598 x _96745 _96744 _96746) (@lem7219466 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7219965 (_96742 : nat) (_96743 : nat) (h1 : term65) : term543 _96742 _96743.
Proof. exact (EQ_MP (@lem7219421 _96742 _96743) (@lem7219420 _96742 _96743 h1)). Qed.
Lemma lem7219966 (m : nat) (n : nat) (h1 : term65) : term543 m n.
Proof. exact (@lem7219965 m n h1). Qed.
Lemma lem7219967 (m : nat) (n : nat) (h1 : term65) : term697 m n.
Proof. exact (fun h0 : term698 m n => @lem7219966 m n h1). Qed.
Lemma lem7219969 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7219970 (m : nat) (n : nat) : (term697 m n) = (term543 m n).
Proof. exact (@lem7219969 (term543 m n)). Qed.
Lemma lem7219971 (m : nat) (n : nat) (h1 : term65) : term543 m n.
Proof. exact (EQ_MP (@lem7219970 m n) (@lem7219967 m n h1)). Qed.
Lemma lem7219973 (_96742 : nat) (_96743 : nat) (h1 : term65) : term543 _96742 _96743.
Proof. exact (EQ_MP (@lem7219421 _96742 _96743) (@lem7219420 _96742 _96743 h1)). Qed.
Lemma lem7219974 (m : nat) (n : nat) (h1 : term65) : term543 m n.
Proof. exact (@lem7219973 m n h1). Qed.
Lemma lem7219975 (m : nat) (n : nat) (h1 : term65) : term697 m n.
Proof. exact (fun h0 : term698 m n => @lem7219974 m n h1). Qed.
Lemma lem7219977 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7219978 (m : nat) (n : nat) : (term697 m n) = (term543 m n).
Proof. exact (@lem7219977 (term543 m n)). Qed.
Lemma lem7219979 (m : nat) (n : nat) (h1 : term65) : term543 m n.
Proof. exact (EQ_MP (@lem7219978 m n) (@lem7219975 m n h1)). Qed.
Lemma lem7219981 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : (term615 m n f) = term549.
Proof. exact (proj2 (@lem7219141 m n f p h1)). Qed.
Lemma lem7219982 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term700 m n f.
Proof. exact (fun h0 : term701 m n f => @lem7219981 m n f p h1). Qed.
Lemma lem7219984 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7219985 (m : nat) (n : nat) (f : nat -> real) : (term700 m n f) = ((term615 m n f) = term549).
Proof. exact (@lem7219984 ((term615 m n f) = term549)). Qed.
Lemma lem7219986 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : (term615 m n f) = term549.
Proof. exact (EQ_MP (@lem7219985 m n f) (@lem7219982 m n f p h1)). Qed.
Lemma lem7219988 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 m p.
Proof. exact (proj1 (@lem7219143 m n f p h1)). Qed.
Lemma lem7219989 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term702 m p.
Proof. exact (fun h0 : term528 m p => @lem7219988 m n f p h1). Qed.
Lemma lem7219991 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7219992 (m : nat) (p : nat) : (term702 m p) = (term508 m p).
Proof. exact (@lem7219991 (term508 m p)). Qed.
Lemma lem7219993 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 m p.
Proof. exact (EQ_MP (@lem7219992 m p) (@lem7219989 m n f p h1)). Qed.
Lemma lem7219995 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 p n.
Proof. exact (proj2 (@lem7219143 m n f p h1)). Qed.
Lemma lem7219996 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term702 p n.
Proof. exact (fun h0 : term528 p n => @lem7219995 m n f p h1). Qed.
Lemma lem7219998 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7219999 (p : nat) (n : nat) : (term702 p n) = (term508 p n).
Proof. exact (@lem7219998 (term508 p n)). Qed.
Lemma lem7220000 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 p n.
Proof. exact (EQ_MP (@lem7219999 p n) (@lem7219996 m n f p h1)). Qed.
Lemma lem7220002 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7220003 (_96753 : nat) (_96751 : nat) (_96752 : nat) : (term533 _96751 _96753 _96752) = (term704 _96753 _96751 _96752).
Proof. exact (@lem7220002 (term531 _96751 _96753 _96752) (term515 _96753 _96751 _96752)). Qed.
Lemma lem7220005 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220006 (_96751 : nat) (_96753 : nat) (_96752 : nat) : (term707 _96751 _96753 _96752) = (term708 _96751 _96753 _96752).
Proof. exact (@lem7220005 (term528 _96751 _96753) (term528 _96753 _96752)). Qed.
Lemma lem7220008 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220009 (_96751 : nat) (_96753 : nat) : (term710 _96751 _96753) = (term508 _96751 _96753).
Proof. exact (@lem7220008 (term508 _96751 _96753)). Qed.
Lemma lem7220010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220011 (_96751 : nat) (_96753 : nat) : (term711 _96751 _96753) = (term510 _96751 _96753).
Proof. exact (MK_COMB (@lem7220010) (@lem7220009 _96751 _96753)). Qed.
Lemma lem7220013 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220014 (_96753 : nat) (_96752 : nat) : (term710 _96753 _96752) = (term508 _96753 _96752).
Proof. exact (@lem7220013 (term508 _96753 _96752)). Qed.
Lemma lem7220015 (_96751 : nat) (_96753 : nat) (_96752 : nat) : (term708 _96751 _96753 _96752) = (term511 _96751 _96753 _96752).
Proof. exact (MK_COMB (@lem7220011 _96751 _96753) (@lem7220014 _96753 _96752)). Qed.
Lemma lem7220016 (_96751 : nat) (_96753 : nat) (_96752 : nat) : (term707 _96751 _96753 _96752) = (term511 _96751 _96753 _96752).
Proof. exact (TRANS (@lem7220006 _96751 _96753 _96752) (@lem7220015 _96751 _96753 _96752)). Qed.
Lemma lem7220017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7220018 (_96751 : nat) (_96753 : nat) (_96752 : nat) : (term712 _96751 _96753 _96752) = (term713 _96751 _96753 _96752).
Proof. exact (MK_COMB (@lem7220017) (@lem7220016 _96751 _96753 _96752)). Qed.
Lemma lem7220019 (_96753 : nat) (_96751 : nat) (_96752 : nat) : (term515 _96753 _96751 _96752) = (term515 _96753 _96751 _96752).
Proof. exact (eq_refl (term515 _96753 _96751 _96752)). Qed.
Lemma lem7220020 (_96753 : nat) (_96751 : nat) (_96752 : nat) : (term704 _96753 _96751 _96752) = (term714 _96753 _96751 _96752).
Proof. exact (MK_COMB (@lem7220018 _96751 _96753 _96752) (@lem7220019 _96753 _96751 _96752)). Qed.
Lemma lem7220021 (_96753 : nat) (_96751 : nat) (_96752 : nat) : (term533 _96751 _96753 _96752) = (term714 _96753 _96751 _96752).
Proof. exact (TRANS (@lem7220003 _96753 _96751 _96752) (@lem7220020 _96753 _96751 _96752)). Qed.
Lemma lem7220023 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term511 m p n.
Proof. exact (conj (@lem7219993 m n f p h1) (@lem7220000 m n f p h1)). Qed.
Lemma lem7220025 (_96753 : nat) (_96751 : nat) (_96752 : nat) (h1 : term73) : term714 _96753 _96751 _96752.
Proof. exact (EQ_MP (@lem7220021 _96753 _96751 _96752) (@lem7219499 _96751 _96753 _96752 h1)). Qed.
Lemma lem7220026 (p : nat) (m : nat) (n : nat) (h1 : term73) : term714 p m n.
Proof. exact (@lem7220025 p m n h1). Qed.
Lemma lem7220029 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term515 p m n.
Proof. exact (@lem7220026 p m n h1 (@lem7220023 m n f p h2)). Qed.
Lemma lem7220030 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term715 p m n.
Proof. exact (fun h0 : term517 p m n => @lem7220029 m n f p h1 h2). Qed.
Lemma lem7220032 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220033 (p : nat) (m : nat) (n : nat) : (term715 p m n) = (term515 p m n).
Proof. exact (@lem7220032 (term515 p m n)). Qed.
Lemma lem7220034 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term515 p m n.
Proof. exact (EQ_MP (@lem7220033 p m n) (@lem7220030 m n f p h1 h2)). Qed.
Lemma lem7220037 (f : nat -> real) (p : nat) (h1 : term606 f p) : term606 f p.
Proof. exact (h1). Qed.
Lemma lem7220038 (f : nat -> real) (p : nat) (h1 : term606 f p) : term716 f p.
Proof. exact (fun h0 : (@I (nat -> real) f p) = term549 => @lem7220037 f p h1). Qed.
Lemma lem7220040 (p : Prop) : (term717 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7220041 (f : nat -> real) (p : nat) : (term716 f p) = (term606 f p).
Proof. exact (@lem7220040 ((@I (nat -> real) f p) = term549)). Qed.
Lemma lem7220042 (f : nat -> real) (p : nat) (h1 : term606 f p) : term606 f p.
Proof. exact (EQ_MP (@lem7220041 f p) (@lem7220038 f p h1)). Qed.
Lemma lem7220048 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220049 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term692 x _96745 _96744 _96746) = (term718 x _96745 _96744 _96746).
Proof. exact (@lem7220048 (term583 x _96744 _96745) (term592 _96745) (term719 _96745 _96744 _96746)). Qed.
Lemma lem7220063 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220064 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term720 _96745 _96744 _96746) = (term721 _96745 _96744 _96746).
Proof. exact (@lem7220063 (term563 _96745 _96744) (term592 _96745) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7220090 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7220091 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term557 _96745 _96744 _96746) = (term722 _96744 _96746 _96745).
Proof. exact (@lem7220090 ((@I (nat -> real) _96744 _96746) = term549) (term554 _96746 _96745)). Qed.
Lemma lem7220099 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7220100 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term723 _96745 _96744 _96746) = (term724 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220099 _96745) (@lem7220091 _96744 _96746 _96745)). Qed.
Lemma lem7220104 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220105 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term724 _96744 _96746 _96745) = (term725 _96744 _96746 _96745).
Proof. exact (@lem7220104 ((@I (nat -> real) _96744 _96746) = term549) (term592 _96745) (term554 _96746 _96745)). Qed.
Lemma lem7220123 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term723 _96745 _96744 _96746) = (term725 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220100 _96744 _96746 _96745) (@lem7220105 _96744 _96746 _96745)). Qed.
Lemma lem7220124 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term726 _96745 _96744) = (term726 _96745 _96744).
Proof. exact (eq_refl (term726 _96745 _96744)). Qed.
Lemma lem7220125 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term721 _96745 _96744 _96746) = (term727 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220124 _96745 _96744) (@lem7220123 _96744 _96746 _96745)). Qed.
Lemma lem7220129 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220130 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term727 _96744 _96746 _96745) = (term728 _96744 _96746 _96745).
Proof. exact (@lem7220129 ((@I (nat -> real) _96744 _96746) = term549) (term563 _96745 _96744) (term729 _96746 _96745)). Qed.
Lemma lem7220160 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term721 _96745 _96744 _96746) = (term728 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220125 _96744 _96746 _96745) (@lem7220130 _96744 _96746 _96745)). Qed.
Lemma lem7220161 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term720 _96745 _96744 _96746) = (term728 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220064 _96745 _96744 _96746) (@lem7220160 _96744 _96746 _96745)). Qed.
Lemma lem7220162 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term730 x _96744 _96745) = (term730 x _96744 _96745).
Proof. exact (eq_refl (term730 x _96744 _96745)). Qed.
Lemma lem7220163 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term731 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220162 x _96744 _96745) (@lem7220161 _96744 _96746 _96745)). Qed.
Lemma lem7220167 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220168 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term731 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745).
Proof. exact (@lem7220167 ((@I (nat -> real) _96744 _96746) = term549) (term583 x _96744 _96745) (term733 _96744 _96746 _96745)). Qed.
Lemma lem7220208 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term732 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220163 x _96744 _96746 _96745) (@lem7220168 x _96744 _96746 _96745)). Qed.
Lemma lem7220209 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term692 x _96745 _96744 _96746) = (term732 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220049 x _96745 _96744 _96746) (@lem7220208 x _96744 _96746 _96745)). Qed.
Lemma lem7220210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7220211 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term734 x _96745 _96744 _96746) = (term735 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220210) (@lem7220209 x _96744 _96746 _96745)). Qed.
Lemma lem7220225 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220226 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term720 _96745 _96744 _96746) = (term721 _96745 _96744 _96746).
Proof. exact (@lem7220225 (term563 _96745 _96744) (term592 _96745) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7220252 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7220253 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term557 _96745 _96744 _96746) = (term722 _96744 _96746 _96745).
Proof. exact (@lem7220252 ((@I (nat -> real) _96744 _96746) = term549) (term554 _96746 _96745)). Qed.
Lemma lem7220261 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7220262 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term723 _96745 _96744 _96746) = (term724 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220261 _96745) (@lem7220253 _96744 _96746 _96745)). Qed.
Lemma lem7220266 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220267 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term724 _96744 _96746 _96745) = (term725 _96744 _96746 _96745).
Proof. exact (@lem7220266 ((@I (nat -> real) _96744 _96746) = term549) (term592 _96745) (term554 _96746 _96745)). Qed.
Lemma lem7220285 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term723 _96745 _96744 _96746) = (term725 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220262 _96744 _96746 _96745) (@lem7220267 _96744 _96746 _96745)). Qed.
Lemma lem7220286 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term726 _96745 _96744) = (term726 _96745 _96744).
Proof. exact (eq_refl (term726 _96745 _96744)). Qed.
Lemma lem7220287 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term721 _96745 _96744 _96746) = (term727 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220286 _96745 _96744) (@lem7220285 _96744 _96746 _96745)). Qed.
Lemma lem7220291 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220292 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term727 _96744 _96746 _96745) = (term728 _96744 _96746 _96745).
Proof. exact (@lem7220291 ((@I (nat -> real) _96744 _96746) = term549) (term563 _96745 _96744) (term729 _96746 _96745)). Qed.
Lemma lem7220322 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term721 _96745 _96744 _96746) = (term728 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220287 _96744 _96746 _96745) (@lem7220292 _96744 _96746 _96745)). Qed.
Lemma lem7220323 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term720 _96745 _96744 _96746) = (term728 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220226 _96745 _96744 _96746) (@lem7220322 _96744 _96746 _96745)). Qed.
Lemma lem7220324 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term730 x _96744 _96745) = (term730 x _96744 _96745).
Proof. exact (eq_refl (term730 x _96744 _96745)). Qed.
Lemma lem7220325 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term731 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7220324 x _96744 _96745) (@lem7220323 _96744 _96746 _96745)). Qed.
Lemma lem7220329 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220330 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term731 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745).
Proof. exact (@lem7220329 ((@I (nat -> real) _96744 _96746) = term549) (term583 x _96744 _96745) (term733 _96744 _96746 _96745)). Qed.
Lemma lem7220370 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term732 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7220325 x _96744 _96746 _96745) (@lem7220330 x _96744 _96746 _96745)). Qed.
Lemma lem7220371 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : ((term692 x _96745 _96744 _96746) = (term718 x _96745 _96744 _96746)) = ((term732 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745)).
Proof. exact (MK_COMB (@lem7220211 x _96744 _96746 _96745) (@lem7220370 x _96744 _96746 _96745)). Qed.
Lemma lem7220373 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7220374 (x : Prop) : (x = x) = True.
Proof. exact (@lem7220373 Prop x). Qed.
Lemma lem7220375 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : ((term732 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745)) = True.
Proof. exact (@lem7220374 (term732 x _96744 _96746 _96745)). Qed.
Lemma lem7220376 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : ((term692 x _96745 _96744 _96746) = (term718 x _96745 _96744 _96746)) = True.
Proof. exact (TRANS (@lem7220371 x _96744 _96746 _96745) (@lem7220375 x _96744 _96746 _96745)). Qed.
Lemma lem7220377 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : True = ((term692 x _96745 _96744 _96746) = (term718 x _96745 _96744 _96746)).
Proof. exact (SYM (@lem7220376 x _96745 _96744 _96746)). Qed.
Lemma lem7220378 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term692 x _96745 _96744 _96746) = (term718 x _96745 _96744 _96746).
Proof. exact (EQ_MP (@lem7220377 x _96745 _96744 _96746) (@lem0)). Qed.
Lemma lem7220379 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term718 x _96745 _96744 _96746.
Proof. exact (EQ_MP (@lem7220378 x _96745 _96744 _96746) (@lem7219577 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7220381 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7220382 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term736 _96746 x _96744 _96745).
Proof. exact (@lem7220381 (term720 _96745 _96744 _96746) (term583 x _96744 _96745)). Qed.
Lemma lem7220384 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220385 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term737 _96745 _96744 _96746) = (term738 _96745 _96744 _96746).
Proof. exact (@lem7220384 (term592 _96745) (term719 _96745 _96744 _96746)). Qed.
Lemma lem7220387 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220388 (_96745 : nat -> Prop) : (term739 _96745) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _96745).
Proof. exact (@lem7220387 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _96745)). Qed.
Lemma lem7220389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220390 (_96745 : nat -> Prop) : (term740 _96745) = (term741 _96745).
Proof. exact (MK_COMB (@lem7220389) (@lem7220388 _96745)). Qed.
Lemma lem7220392 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220393 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term742 _96745 _96744 _96746) = (term743 _96745 _96744 _96746).
Proof. exact (@lem7220392 (term563 _96745 _96744) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7220395 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220396 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term744 _96745 _96744) = ((term560 _96745 _96744) = term549).
Proof. exact (@lem7220395 ((term560 _96745 _96744) = term549)). Qed.
Lemma lem7220397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220398 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term745 _96745 _96744) = (term746 _96745 _96744).
Proof. exact (MK_COMB (@lem7220397) (@lem7220396 _96745 _96744)). Qed.
Lemma lem7220400 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220401 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term747 _96745 _96744 _96746) = (term748 _96745 _96744 _96746).
Proof. exact (@lem7220400 (term554 _96746 _96745) ((@I (nat -> real) _96744 _96746) = term549)). Qed.
Lemma lem7220403 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220404 (_96746 : nat) (_96745 : nat -> Prop) : (term749 _96746 _96745) = (term552 _96746 _96745).
Proof. exact (@lem7220403 (term552 _96746 _96745)). Qed.
Lemma lem7220405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220406 (_96746 : nat) (_96745 : nat -> Prop) : (term750 _96746 _96745) = (term751 _96746 _96745).
Proof. exact (MK_COMB (@lem7220405) (@lem7220404 _96746 _96745)). Qed.
Lemma lem7220407 (_96744 : nat -> real) (_96746 : nat) : (term606 _96744 _96746) = (term606 _96744 _96746).
Proof. exact (eq_refl (term606 _96744 _96746)). Qed.
Lemma lem7220408 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term748 _96745 _96744 _96746) = (term752 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220406 _96746 _96745) (@lem7220407 _96744 _96746)). Qed.
Lemma lem7220409 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term747 _96745 _96744 _96746) = (term752 _96745 _96744 _96746).
Proof. exact (TRANS (@lem7220401 _96745 _96744 _96746) (@lem7220408 _96745 _96744 _96746)). Qed.
Lemma lem7220410 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term743 _96745 _96744 _96746) = (term753 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220398 _96745 _96744) (@lem7220409 _96745 _96744 _96746)). Qed.
Lemma lem7220411 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term742 _96745 _96744 _96746) = (term753 _96745 _96744 _96746).
Proof. exact (TRANS (@lem7220393 _96745 _96744 _96746) (@lem7220410 _96745 _96744 _96746)). Qed.
Lemma lem7220412 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term738 _96745 _96744 _96746) = (term754 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220390 _96745) (@lem7220411 _96745 _96744 _96746)). Qed.
Lemma lem7220413 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term737 _96745 _96744 _96746) = (term754 _96745 _96744 _96746).
Proof. exact (TRANS (@lem7220385 _96745 _96744 _96746) (@lem7220412 _96745 _96744 _96746)). Qed.
Lemma lem7220414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7220415 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term755 _96745 _96744 _96746) = (term756 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220414) (@lem7220413 _96745 _96744 _96746)). Qed.
Lemma lem7220416 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term583 x _96744 _96745) = (term583 x _96744 _96745).
Proof. exact (eq_refl (term583 x _96744 _96745)). Qed.
Lemma lem7220417 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term736 _96746 x _96744 _96745) = (term757 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220415 _96745 _96744 _96746) (@lem7220416 x _96744 _96745)). Qed.
Lemma lem7220418 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term757 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220382 _96746 x _96744 _96745) (@lem7220417 _96746 x _96744 _96745)). Qed.
Lemma lem7220420 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term606 f p) (h3 : term151 m n f p) : term758 m n f p.
Proof. exact (conj (@lem7220034 m n f p h1 h3) (@lem7220042 f p h2)). Qed.
Lemma lem7220421 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term606 f p) (h3 : term151 m n f p) : term759 m n f p.
Proof. exact (conj (@lem7219986 m n f p h3) (@lem7220420 m n f p h1 h2 h3)). Qed.
Lemma lem7220422 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term65) (h3 : term606 f p) (h4 : term151 m n f p) : term760 m n f p.
Proof. exact (conj (@lem7219979 m n h2) (@lem7220421 m n f p h1 h3 h4)). Qed.
Lemma lem7220424 (_96746 : nat) (_96744 : nat -> real) (_96745 : nat -> Prop) (x : type1007) (h1 : term504 x) : term757 _96746 x _96744 _96745.
Proof. exact (EQ_MP (@lem7220418 _96746 x _96744 _96745) (@lem7220379 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7220425 (p : nat) (f : nat -> real) (m : nat) (n : nat) (x : type1007) (h1 : term504 x) : term761 p x f m n.
Proof. exact (@lem7220424 p f (term512 m n) x h1). Qed.
Lemma lem7220428 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term762 x f m n.
Proof. exact (@lem7220425 p f m n x h1 (@lem7220422 m n f p h2 h3 h4 h5)). Qed.
Lemma lem7220429 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term763 x f m n.
Proof. exact (fun h0 : term764 x f m n => @lem7220428 x m n f p h1 h2 h3 h4 h5). Qed.
Lemma lem7220431 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220432 (x : type1007) (f : nat -> real) (m : nat) (n : nat) : (term763 x f m n) = (term762 x f m n).
Proof. exact (@lem7220431 (term762 x f m n)). Qed.
Lemma lem7220433 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term762 x f m n.
Proof. exact (EQ_MP (@lem7220432 x f m n) (@lem7220429 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7220439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7220440 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term687 _96755 _96754 _96756) = (term765 _96756 _96754 _96755).
Proof. exact (@lem7220439 (term508 _96754 _96756) (term517 _96756 _96754 _96755)). Qed.
Lemma lem7220446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7220447 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term766 _96755 _96754 _96756) = (term767 _96756 _96754 _96755).
Proof. exact (MK_COMB (@lem7220446) (@lem7220440 _96756 _96754 _96755)). Qed.
Lemma lem7220453 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term765 _96756 _96754 _96755) = (term765 _96756 _96754 _96755).
Proof. exact (eq_refl (term765 _96756 _96754 _96755)). Qed.
Lemma lem7220454 (_96756 : nat) (_96754 : nat) (_96755 : nat) : ((term687 _96755 _96754 _96756) = (term765 _96756 _96754 _96755)) = ((term765 _96756 _96754 _96755) = (term765 _96756 _96754 _96755)).
Proof. exact (MK_COMB (@lem7220447 _96756 _96754 _96755) (@lem7220453 _96756 _96754 _96755)). Qed.
Lemma lem7220456 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7220457 (x : Prop) : (x = x) = True.
Proof. exact (@lem7220456 Prop x). Qed.
Lemma lem7220458 (_96756 : nat) (_96754 : nat) (_96755 : nat) : ((term765 _96756 _96754 _96755) = (term765 _96756 _96754 _96755)) = True.
Proof. exact (@lem7220457 (term765 _96756 _96754 _96755)). Qed.
Lemma lem7220459 (_96756 : nat) (_96754 : nat) (_96755 : nat) : ((term687 _96755 _96754 _96756) = (term765 _96756 _96754 _96755)) = True.
Proof. exact (TRANS (@lem7220454 _96756 _96754 _96755) (@lem7220458 _96756 _96754 _96755)). Qed.
Lemma lem7220460 (_96756 : nat) (_96754 : nat) (_96755 : nat) : True = ((term687 _96755 _96754 _96756) = (term765 _96756 _96754 _96755)).
Proof. exact (SYM (@lem7220459 _96756 _96754 _96755)). Qed.
Lemma lem7220461 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term687 _96755 _96754 _96756) = (term765 _96756 _96754 _96755).
Proof. exact (EQ_MP (@lem7220460 _96756 _96754 _96755) (@lem0)). Qed.
Lemma lem7220462 (_96756 : nat) (_96754 : nat) (_96755 : nat) (h1 : term73) : term765 _96756 _96754 _96755.
Proof. exact (EQ_MP (@lem7220461 _96756 _96754 _96755) (@lem7219505 _96755 _96754 _96756 h1)). Qed.
Lemma lem7220464 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7220465 (_96755 : nat) (_96754 : nat) (_96756 : nat) : (term765 _96756 _96754 _96755) = (term768 _96755 _96754 _96756).
Proof. exact (@lem7220464 (term517 _96756 _96754 _96755) (term508 _96754 _96756)). Qed.
Lemma lem7220467 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220468 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term769 _96756 _96754 _96755) = (term515 _96756 _96754 _96755).
Proof. exact (@lem7220467 (term515 _96756 _96754 _96755)). Qed.
Lemma lem7220469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7220470 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term770 _96756 _96754 _96755) = (term771 _96756 _96754 _96755).
Proof. exact (MK_COMB (@lem7220469) (@lem7220468 _96756 _96754 _96755)). Qed.
Lemma lem7220471 (_96754 : nat) (_96756 : nat) : (term508 _96754 _96756) = (term508 _96754 _96756).
Proof. exact (eq_refl (term508 _96754 _96756)). Qed.
Lemma lem7220472 (_96755 : nat) (_96754 : nat) (_96756 : nat) : (term768 _96755 _96754 _96756) = (term772 _96755 _96754 _96756).
Proof. exact (MK_COMB (@lem7220470 _96756 _96754 _96755) (@lem7220471 _96754 _96756)). Qed.
Lemma lem7220473 (_96755 : nat) (_96754 : nat) (_96756 : nat) : (term765 _96756 _96754 _96755) = (term772 _96755 _96754 _96756).
Proof. exact (TRANS (@lem7220465 _96755 _96754 _96756) (@lem7220472 _96755 _96754 _96756)). Qed.
Lemma lem7220476 (_96755 : nat) (_96754 : nat) (_96756 : nat) (h1 : term73) : term772 _96755 _96754 _96756.
Proof. exact (EQ_MP (@lem7220473 _96755 _96754 _96756) (@lem7220462 _96756 _96754 _96755 h1)). Qed.
Lemma lem7220477 (x : type1007) (f : nat -> real) (m : nat) (n : nat) (h1 : term73) : term773 x f m n.
Proof. exact (@lem7220476 n m (term774 x f m n) h1). Qed.
Lemma lem7220480 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term775 x f m n.
Proof. exact (@lem7220477 x f m n h2 (@lem7220433 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7220481 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term776 x f m n.
Proof. exact (fun h0 : term777 x f m n => @lem7220480 x m n f p h1 h2 h3 h4 h5). Qed.
Lemma lem7220483 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220484 (x : type1007) (f : nat -> real) (m : nat) (n : nat) : (term776 x f m n) = (term775 x f m n).
Proof. exact (@lem7220483 (term775 x f m n)). Qed.
Lemma lem7220485 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term775 x f m n.
Proof. exact (EQ_MP (@lem7220484 x f m n) (@lem7220481 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7220487 (_96742 : nat) (_96743 : nat) (h1 : term65) : term543 _96742 _96743.
Proof. exact (EQ_MP (@lem7219421 _96742 _96743) (@lem7219420 _96742 _96743 h1)). Qed.
Lemma lem7220488 (m : nat) (n : nat) (h1 : term65) : term543 m n.
Proof. exact (@lem7220487 m n h1). Qed.
Lemma lem7220489 (m : nat) (n : nat) (h1 : term65) : term697 m n.
Proof. exact (fun h0 : term698 m n => @lem7220488 m n h1). Qed.
Lemma lem7220491 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220492 (m : nat) (n : nat) : (term697 m n) = (term543 m n).
Proof. exact (@lem7220491 (term543 m n)). Qed.
Lemma lem7220493 (m : nat) (n : nat) (h1 : term65) : term543 m n.
Proof. exact (EQ_MP (@lem7220492 m n) (@lem7220489 m n h1)). Qed.
Lemma lem7220495 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : (term615 m n f) = term549.
Proof. exact (proj2 (@lem7219141 m n f p h1)). Qed.
Lemma lem7220496 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term700 m n f.
Proof. exact (fun h0 : term701 m n f => @lem7220495 m n f p h1). Qed.
Lemma lem7220498 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220499 (m : nat) (n : nat) (f : nat -> real) : (term700 m n f) = ((term615 m n f) = term549).
Proof. exact (@lem7220498 ((term615 m n f) = term549)). Qed.
Lemma lem7220500 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : (term615 m n f) = term549.
Proof. exact (EQ_MP (@lem7220499 m n f) (@lem7220496 m n f p h1)). Qed.
Lemma lem7220502 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 m p.
Proof. exact (proj1 (@lem7219143 m n f p h1)). Qed.
Lemma lem7220503 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term702 m p.
Proof. exact (fun h0 : term528 m p => @lem7220502 m n f p h1). Qed.
Lemma lem7220505 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220506 (m : nat) (p : nat) : (term702 m p) = (term508 m p).
Proof. exact (@lem7220505 (term508 m p)). Qed.
Lemma lem7220507 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 m p.
Proof. exact (EQ_MP (@lem7220506 m p) (@lem7220503 m n f p h1)). Qed.
Lemma lem7220509 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 p n.
Proof. exact (proj2 (@lem7219143 m n f p h1)). Qed.
Lemma lem7220510 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term702 p n.
Proof. exact (fun h0 : term528 p n => @lem7220509 m n f p h1). Qed.
Lemma lem7220512 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220513 (p : nat) (n : nat) : (term702 p n) = (term508 p n).
Proof. exact (@lem7220512 (term508 p n)). Qed.
Lemma lem7220514 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 p n.
Proof. exact (EQ_MP (@lem7220513 p n) (@lem7220510 m n f p h1)). Qed.
Lemma lem7220515 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term511 m p n.
Proof. exact (conj (@lem7220507 m n f p h1) (@lem7220514 m n f p h1)). Qed.
Lemma lem7220517 (_96753 : nat) (_96751 : nat) (_96752 : nat) (h1 : term73) : term714 _96753 _96751 _96752.
Proof. exact (EQ_MP (@lem7220021 _96753 _96751 _96752) (@lem7219499 _96751 _96753 _96752 h1)). Qed.
Lemma lem7220518 (p : nat) (m : nat) (n : nat) (h1 : term73) : term714 p m n.
Proof. exact (@lem7220517 p m n h1). Qed.
Lemma lem7220521 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term515 p m n.
Proof. exact (@lem7220518 p m n h1 (@lem7220515 m n f p h2)). Qed.
Lemma lem7220522 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term715 p m n.
Proof. exact (fun h0 : term517 p m n => @lem7220521 m n f p h1 h2). Qed.
Lemma lem7220524 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7220525 (p : nat) (m : nat) (n : nat) : (term715 p m n) = (term515 p m n).
Proof. exact (@lem7220524 (term515 p m n)). Qed.
Lemma lem7220526 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term515 p m n.
Proof. exact (EQ_MP (@lem7220525 p m n) (@lem7220522 m n f p h1 h2)). Qed.
Lemma lem7220529 (f : nat -> real) (p : nat) (h1 : term606 f p) : term606 f p.
Proof. exact (h1). Qed.
Lemma lem7220530 (f : nat -> real) (p : nat) (h1 : term606 f p) : term716 f p.
Proof. exact (fun h0 : (@I (nat -> real) f p) = term549 => @lem7220529 f p h1). Qed.
Lemma lem7220532 (p : Prop) : (term717 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7220533 (f : nat -> real) (p : nat) : (term716 f p) = (term606 f p).
Proof. exact (@lem7220532 ((@I (nat -> real) f p) = term549)). Qed.
Lemma lem7220534 (f : nat -> real) (p : nat) (h1 : term606 f p) : term606 f p.
Proof. exact (EQ_MP (@lem7220533 f p) (@lem7220530 f p h1)). Qed.
Lemma lem7220550 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220551 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term695 x _96745 _96744 _96746) = (term778 x _96745 _96744 _96746).
Proof. exact (@lem7220550 (term563 _96745 _96744) (term576 x _96744 _96745) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7220567 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220568 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term779 x _96745 _96744 _96746) = (term780 x _96745 _96744 _96746).
Proof. exact (@lem7220567 (term554 _96746 _96745) (term576 x _96744 _96745) ((@I (nat -> real) _96744 _96746) = term549)). Qed.
Lemma lem7220582 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7220583 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term781 x _96745 _96744 _96746) = (term782 _96746 x _96744 _96745).
Proof. exact (@lem7220582 ((@I (nat -> real) _96744 _96746) = term549) (term576 x _96744 _96745)). Qed.
Lemma lem7220591 (_96746 : nat) (_96745 : nat -> Prop) : (term556 _96746 _96745) = (term556 _96746 _96745).
Proof. exact (eq_refl (term556 _96746 _96745)). Qed.
Lemma lem7220592 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term780 x _96745 _96744 _96746) = (term783 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220591 _96746 _96745) (@lem7220583 _96746 x _96744 _96745)). Qed.
Lemma lem7220596 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220597 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term783 _96746 x _96744 _96745) = (term784 _96746 x _96744 _96745).
Proof. exact (@lem7220596 ((@I (nat -> real) _96744 _96746) = term549) (term554 _96746 _96745) (term576 x _96744 _96745)). Qed.
Lemma lem7220615 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term780 x _96745 _96744 _96746) = (term784 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220592 _96746 x _96744 _96745) (@lem7220597 _96746 x _96744 _96745)). Qed.
Lemma lem7220616 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term779 x _96745 _96744 _96746) = (term784 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220568 x _96745 _96744 _96746) (@lem7220615 _96746 x _96744 _96745)). Qed.
Lemma lem7220617 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term726 _96745 _96744) = (term726 _96745 _96744).
Proof. exact (eq_refl (term726 _96745 _96744)). Qed.
Lemma lem7220618 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term778 x _96745 _96744 _96746) = (term785 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220617 _96745 _96744) (@lem7220616 _96746 x _96744 _96745)). Qed.
Lemma lem7220622 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220623 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term785 _96746 x _96744 _96745) = (term786 _96746 x _96744 _96745).
Proof. exact (@lem7220622 ((@I (nat -> real) _96744 _96746) = term549) (term563 _96745 _96744) (term787 _96746 x _96744 _96745)). Qed.
Lemma lem7220653 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term778 x _96745 _96744 _96746) = (term786 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220618 _96746 x _96744 _96745) (@lem7220623 _96746 x _96744 _96745)). Qed.
Lemma lem7220654 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term695 x _96745 _96744 _96746) = (term786 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220551 x _96745 _96744 _96746) (@lem7220653 _96746 x _96744 _96745)). Qed.
Lemma lem7220655 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7220656 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term696 x _96745 _96744 _96746) = (term788 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220655 _96745) (@lem7220654 _96746 x _96744 _96745)). Qed.
Lemma lem7220660 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220661 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term788 _96746 x _96744 _96745) = (term789 _96746 x _96744 _96745).
Proof. exact (@lem7220660 ((@I (nat -> real) _96744 _96746) = term549) (term592 _96745) (term790 _96746 x _96744 _96745)). Qed.
Lemma lem7220677 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220678 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term791 _96746 x _96744 _96745) = (term792 _96746 x _96744 _96745).
Proof. exact (@lem7220677 (term563 _96745 _96744) (term592 _96745) (term787 _96746 x _96744 _96745)). Qed.
Lemma lem7220706 (_96744 : nat -> real) (_96746 : nat) : (term793 _96744 _96746) = (term793 _96744 _96746).
Proof. exact (eq_refl (term793 _96744 _96746)). Qed.
Lemma lem7220707 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term789 _96746 x _96744 _96745) = (term794 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220706 _96744 _96746) (@lem7220678 _96746 x _96744 _96745)). Qed.
Lemma lem7220718 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term788 _96746 x _96744 _96745) = (term794 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220661 _96746 x _96744 _96745) (@lem7220707 _96746 x _96744 _96745)). Qed.
Lemma lem7220719 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term696 x _96745 _96744 _96746) = (term794 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220656 _96746 x _96744 _96745) (@lem7220718 _96746 x _96744 _96745)). Qed.
Lemma lem7220720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7220721 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term795 x _96745 _96744 _96746) = (term796 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220720) (@lem7220719 _96746 x _96744 _96745)). Qed.
Lemma lem7220725 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220726 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term797 x _96745 _96744 _96746) = (term696 x _96745 _96744 _96746).
Proof. exact (@lem7220725 (term592 _96745) (term576 x _96744 _96745) (term719 _96745 _96744 _96746)). Qed.
Lemma lem7220740 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220741 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term695 x _96745 _96744 _96746) = (term778 x _96745 _96744 _96746).
Proof. exact (@lem7220740 (term563 _96745 _96744) (term576 x _96744 _96745) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7220757 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220758 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term779 x _96745 _96744 _96746) = (term780 x _96745 _96744 _96746).
Proof. exact (@lem7220757 (term554 _96746 _96745) (term576 x _96744 _96745) ((@I (nat -> real) _96744 _96746) = term549)). Qed.
Lemma lem7220772 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7220773 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term781 x _96745 _96744 _96746) = (term782 _96746 x _96744 _96745).
Proof. exact (@lem7220772 ((@I (nat -> real) _96744 _96746) = term549) (term576 x _96744 _96745)). Qed.
Lemma lem7220781 (_96746 : nat) (_96745 : nat -> Prop) : (term556 _96746 _96745) = (term556 _96746 _96745).
Proof. exact (eq_refl (term556 _96746 _96745)). Qed.
Lemma lem7220782 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term780 x _96745 _96744 _96746) = (term783 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220781 _96746 _96745) (@lem7220773 _96746 x _96744 _96745)). Qed.
Lemma lem7220786 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220787 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term783 _96746 x _96744 _96745) = (term784 _96746 x _96744 _96745).
Proof. exact (@lem7220786 ((@I (nat -> real) _96744 _96746) = term549) (term554 _96746 _96745) (term576 x _96744 _96745)). Qed.
Lemma lem7220805 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term780 x _96745 _96744 _96746) = (term784 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220782 _96746 x _96744 _96745) (@lem7220787 _96746 x _96744 _96745)). Qed.
Lemma lem7220806 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term779 x _96745 _96744 _96746) = (term784 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220758 x _96745 _96744 _96746) (@lem7220805 _96746 x _96744 _96745)). Qed.
Lemma lem7220807 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term726 _96745 _96744) = (term726 _96745 _96744).
Proof. exact (eq_refl (term726 _96745 _96744)). Qed.
Lemma lem7220808 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term778 x _96745 _96744 _96746) = (term785 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220807 _96745 _96744) (@lem7220806 _96746 x _96744 _96745)). Qed.
Lemma lem7220812 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220813 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term785 _96746 x _96744 _96745) = (term786 _96746 x _96744 _96745).
Proof. exact (@lem7220812 ((@I (nat -> real) _96744 _96746) = term549) (term563 _96745 _96744) (term787 _96746 x _96744 _96745)). Qed.
Lemma lem7220843 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term778 x _96745 _96744 _96746) = (term786 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220808 _96746 x _96744 _96745) (@lem7220813 _96746 x _96744 _96745)). Qed.
Lemma lem7220844 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term695 x _96745 _96744 _96746) = (term786 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220741 x _96745 _96744 _96746) (@lem7220843 _96746 x _96744 _96745)). Qed.
Lemma lem7220845 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7220846 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term696 x _96745 _96744 _96746) = (term788 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220845 _96745) (@lem7220844 _96746 x _96744 _96745)). Qed.
Lemma lem7220850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220851 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term788 _96746 x _96744 _96745) = (term789 _96746 x _96744 _96745).
Proof. exact (@lem7220850 ((@I (nat -> real) _96744 _96746) = term549) (term592 _96745) (term790 _96746 x _96744 _96745)). Qed.
Lemma lem7220867 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220868 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term791 _96746 x _96744 _96745) = (term792 _96746 x _96744 _96745).
Proof. exact (@lem7220867 (term563 _96745 _96744) (term592 _96745) (term787 _96746 x _96744 _96745)). Qed.
Lemma lem7220896 (_96744 : nat -> real) (_96746 : nat) : (term793 _96744 _96746) = (term793 _96744 _96746).
Proof. exact (eq_refl (term793 _96744 _96746)). Qed.
Lemma lem7220897 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term789 _96746 x _96744 _96745) = (term794 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220896 _96744 _96746) (@lem7220868 _96746 x _96744 _96745)). Qed.
Lemma lem7220908 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term788 _96746 x _96744 _96745) = (term794 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220851 _96746 x _96744 _96745) (@lem7220897 _96746 x _96744 _96745)). Qed.
Lemma lem7220909 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term696 x _96745 _96744 _96746) = (term794 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220846 _96746 x _96744 _96745) (@lem7220908 _96746 x _96744 _96745)). Qed.
Lemma lem7220910 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term797 x _96745 _96744 _96746) = (term794 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220726 x _96745 _96744 _96746) (@lem7220909 _96746 x _96744 _96745)). Qed.
Lemma lem7220911 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : ((term696 x _96745 _96744 _96746) = (term797 x _96745 _96744 _96746)) = ((term794 _96746 x _96744 _96745) = (term794 _96746 x _96744 _96745)).
Proof. exact (MK_COMB (@lem7220721 _96746 x _96744 _96745) (@lem7220910 _96746 x _96744 _96745)). Qed.
Lemma lem7220913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7220914 (x : Prop) : (x = x) = True.
Proof. exact (@lem7220913 Prop x). Qed.
Lemma lem7220915 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : ((term794 _96746 x _96744 _96745) = (term794 _96746 x _96744 _96745)) = True.
Proof. exact (@lem7220914 (term794 _96746 x _96744 _96745)). Qed.
Lemma lem7220916 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : ((term696 x _96745 _96744 _96746) = (term797 x _96745 _96744 _96746)) = True.
Proof. exact (TRANS (@lem7220911 _96746 x _96744 _96745) (@lem7220915 _96746 x _96744 _96745)). Qed.
Lemma lem7220917 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : True = ((term696 x _96745 _96744 _96746) = (term797 x _96745 _96744 _96746)).
Proof. exact (SYM (@lem7220916 x _96745 _96744 _96746)). Qed.
Lemma lem7220918 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term696 x _96745 _96744 _96746) = (term797 x _96745 _96744 _96746).
Proof. exact (EQ_MP (@lem7220917 x _96745 _96744 _96746) (@lem0)). Qed.
Lemma lem7220919 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term797 x _96745 _96744 _96746.
Proof. exact (EQ_MP (@lem7220918 x _96745 _96744 _96746) (@lem7219599 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7220921 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7220922 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term797 x _96745 _96744 _96746) = (term798 _96746 x _96744 _96745).
Proof. exact (@lem7220921 (term720 _96745 _96744 _96746) (term576 x _96744 _96745)). Qed.
Lemma lem7220924 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220925 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term737 _96745 _96744 _96746) = (term738 _96745 _96744 _96746).
Proof. exact (@lem7220924 (term592 _96745) (term719 _96745 _96744 _96746)). Qed.
Lemma lem7220927 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220928 (_96745 : nat -> Prop) : (term739 _96745) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _96745).
Proof. exact (@lem7220927 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _96745)). Qed.
Lemma lem7220929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220930 (_96745 : nat -> Prop) : (term740 _96745) = (term741 _96745).
Proof. exact (MK_COMB (@lem7220929) (@lem7220928 _96745)). Qed.
Lemma lem7220932 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220933 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term742 _96745 _96744 _96746) = (term743 _96745 _96744 _96746).
Proof. exact (@lem7220932 (term563 _96745 _96744) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7220935 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220936 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term744 _96745 _96744) = ((term560 _96745 _96744) = term549).
Proof. exact (@lem7220935 ((term560 _96745 _96744) = term549)). Qed.
Lemma lem7220937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220938 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term745 _96745 _96744) = (term746 _96745 _96744).
Proof. exact (MK_COMB (@lem7220937) (@lem7220936 _96745 _96744)). Qed.
Lemma lem7220940 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7220941 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term747 _96745 _96744 _96746) = (term748 _96745 _96744 _96746).
Proof. exact (@lem7220940 (term554 _96746 _96745) ((@I (nat -> real) _96744 _96746) = term549)). Qed.
Lemma lem7220943 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7220944 (_96746 : nat) (_96745 : nat -> Prop) : (term749 _96746 _96745) = (term552 _96746 _96745).
Proof. exact (@lem7220943 (term552 _96746 _96745)). Qed.
Lemma lem7220945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7220946 (_96746 : nat) (_96745 : nat -> Prop) : (term750 _96746 _96745) = (term751 _96746 _96745).
Proof. exact (MK_COMB (@lem7220945) (@lem7220944 _96746 _96745)). Qed.
Lemma lem7220947 (_96744 : nat -> real) (_96746 : nat) : (term606 _96744 _96746) = (term606 _96744 _96746).
Proof. exact (eq_refl (term606 _96744 _96746)). Qed.
Lemma lem7220948 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term748 _96745 _96744 _96746) = (term752 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220946 _96746 _96745) (@lem7220947 _96744 _96746)). Qed.
Lemma lem7220949 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term747 _96745 _96744 _96746) = (term752 _96745 _96744 _96746).
Proof. exact (TRANS (@lem7220941 _96745 _96744 _96746) (@lem7220948 _96745 _96744 _96746)). Qed.
Lemma lem7220950 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term743 _96745 _96744 _96746) = (term753 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220938 _96745 _96744) (@lem7220949 _96745 _96744 _96746)). Qed.
Lemma lem7220951 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term742 _96745 _96744 _96746) = (term753 _96745 _96744 _96746).
Proof. exact (TRANS (@lem7220933 _96745 _96744 _96746) (@lem7220950 _96745 _96744 _96746)). Qed.
Lemma lem7220952 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term738 _96745 _96744 _96746) = (term754 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220930 _96745) (@lem7220951 _96745 _96744 _96746)). Qed.
Lemma lem7220953 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term737 _96745 _96744 _96746) = (term754 _96745 _96744 _96746).
Proof. exact (TRANS (@lem7220925 _96745 _96744 _96746) (@lem7220952 _96745 _96744 _96746)). Qed.
Lemma lem7220954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7220955 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term755 _96745 _96744 _96746) = (term756 _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7220954) (@lem7220953 _96745 _96744 _96746)). Qed.
Lemma lem7220956 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term576 x _96744 _96745) = (term576 x _96744 _96745).
Proof. exact (eq_refl (term576 x _96744 _96745)). Qed.
Lemma lem7220957 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term798 _96746 x _96744 _96745) = (term799 _96746 x _96744 _96745).
Proof. exact (MK_COMB (@lem7220955 _96745 _96744 _96746) (@lem7220956 x _96744 _96745)). Qed.
Lemma lem7220958 (_96746 : nat) (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term797 x _96745 _96744 _96746) = (term799 _96746 x _96744 _96745).
Proof. exact (TRANS (@lem7220922 _96746 x _96744 _96745) (@lem7220957 _96746 x _96744 _96745)). Qed.
Lemma lem7220960 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term606 f p) (h3 : term151 m n f p) : term758 m n f p.
Proof. exact (conj (@lem7220526 m n f p h1 h3) (@lem7220534 f p h2)). Qed.
Lemma lem7220961 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term606 f p) (h3 : term151 m n f p) : term759 m n f p.
Proof. exact (conj (@lem7220500 m n f p h3) (@lem7220960 m n f p h1 h2 h3)). Qed.
Lemma lem7220962 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term65) (h3 : term606 f p) (h4 : term151 m n f p) : term760 m n f p.
Proof. exact (conj (@lem7220493 m n h2) (@lem7220961 m n f p h1 h3 h4)). Qed.
Lemma lem7220964 (_96746 : nat) (_96744 : nat -> real) (_96745 : nat -> Prop) (x : type1007) (h1 : term504 x) : term799 _96746 x _96744 _96745.
Proof. exact (EQ_MP (@lem7220958 _96746 x _96744 _96745) (@lem7220919 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7220965 (p : nat) (f : nat -> real) (m : nat) (n : nat) (x : type1007) (h1 : term504 x) : term800 p x f m n.
Proof. exact (@lem7220964 p f (term512 m n) x h1). Qed.
Lemma lem7220968 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term801 x f m n.
Proof. exact (@lem7220965 p f m n x h1 (@lem7220962 m n f p h2 h3 h4 h5)). Qed.
Lemma lem7220969 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term802 x f m n.
Proof. exact (fun h0 : term803 x f m n => @lem7220968 x m n f p h1 h2 h3 h4 h5). Qed.
Lemma lem7220971 (p : Prop) : (term717 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7220972 (x : type1007) (f : nat -> real) (m : nat) (n : nat) : (term802 x f m n) = (term801 x f m n).
Proof. exact (@lem7220971 (term803 x f m n)). Qed.
Lemma lem7220973 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term801 x f m n.
Proof. exact (EQ_MP (@lem7220972 x f m n) (@lem7220969 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7220979 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7220980 (n : nat) (m : nat) (f : nat -> real) (_96750 : nat) : (term686 m n f _96750) = (term804 n m f _96750).
Proof. exact (@lem7220979 (term528 _96750 n) (term528 m _96750) (term620 f _96750)). Qed.
Lemma lem7220994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7220995 (f : nat -> real) (m : nat) (_96750 : nat) : (term805 m f _96750) = (term806 f m _96750).
Proof. exact (@lem7220994 (term620 f _96750) (term528 m _96750)). Qed.
Lemma lem7221001 (_96750 : nat) (n : nat) : (term530 _96750 n) = (term530 _96750 n).
Proof. exact (eq_refl (term530 _96750 n)). Qed.
Lemma lem7221002 (n : nat) (f : nat -> real) (m : nat) (_96750 : nat) : (term804 n m f _96750) = (term807 n f m _96750).
Proof. exact (MK_COMB (@lem7221001 _96750 n) (@lem7220995 f m _96750)). Qed.
Lemma lem7221006 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221007 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : (term807 n f m _96750) = (term808 f n m _96750).
Proof. exact (@lem7221006 (term620 f _96750) (term528 _96750 n) (term528 m _96750)). Qed.
Lemma lem7221023 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : (term804 n m f _96750) = (term808 f n m _96750).
Proof. exact (TRANS (@lem7221002 n f m _96750) (@lem7221007 f n m _96750)). Qed.
Lemma lem7221024 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : (term686 m n f _96750) = (term808 f n m _96750).
Proof. exact (TRANS (@lem7220980 n m f _96750) (@lem7221023 f n m _96750)). Qed.
Lemma lem7221025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7221026 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : (term809 m n f _96750) = (term810 f n m _96750).
Proof. exact (MK_COMB (@lem7221025) (@lem7221024 f n m _96750)). Qed.
Lemma lem7221040 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7221041 (f : nat -> real) (m : nat) (_96750 : nat) : (term805 m f _96750) = (term806 f m _96750).
Proof. exact (@lem7221040 (term620 f _96750) (term528 m _96750)). Qed.
Lemma lem7221047 (_96750 : nat) (n : nat) : (term530 _96750 n) = (term530 _96750 n).
Proof. exact (eq_refl (term530 _96750 n)). Qed.
Lemma lem7221048 (n : nat) (f : nat -> real) (m : nat) (_96750 : nat) : (term804 n m f _96750) = (term807 n f m _96750).
Proof. exact (MK_COMB (@lem7221047 _96750 n) (@lem7221041 f m _96750)). Qed.
Lemma lem7221052 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221053 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : (term807 n f m _96750) = (term808 f n m _96750).
Proof. exact (@lem7221052 (term620 f _96750) (term528 _96750 n) (term528 m _96750)). Qed.
Lemma lem7221069 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : (term804 n m f _96750) = (term808 f n m _96750).
Proof. exact (TRANS (@lem7221048 n f m _96750) (@lem7221053 f n m _96750)). Qed.
Lemma lem7221070 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : ((term686 m n f _96750) = (term804 n m f _96750)) = ((term808 f n m _96750) = (term808 f n m _96750)).
Proof. exact (MK_COMB (@lem7221026 f n m _96750) (@lem7221069 f n m _96750)). Qed.
Lemma lem7221072 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7221073 (x : Prop) : (x = x) = True.
Proof. exact (@lem7221072 Prop x). Qed.
Lemma lem7221074 (f : nat -> real) (n : nat) (m : nat) (_96750 : nat) : ((term808 f n m _96750) = (term808 f n m _96750)) = True.
Proof. exact (@lem7221073 (term808 f n m _96750)). Qed.
Lemma lem7221075 (n : nat) (m : nat) (f : nat -> real) (_96750 : nat) : ((term686 m n f _96750) = (term804 n m f _96750)) = True.
Proof. exact (TRANS (@lem7221070 f n m _96750) (@lem7221074 f n m _96750)). Qed.
Lemma lem7221076 (n : nat) (m : nat) (f : nat -> real) (_96750 : nat) : True = ((term686 m n f _96750) = (term804 n m f _96750)).
Proof. exact (SYM (@lem7221075 n m f _96750)). Qed.
Lemma lem7221077 (n : nat) (m : nat) (f : nat -> real) (_96750 : nat) : (term686 m n f _96750) = (term804 n m f _96750).
Proof. exact (EQ_MP (@lem7221076 n m f _96750) (@lem0)). Qed.
Lemma lem7221078 (_96750 : nat) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term804 n m f _96750.
Proof. exact (EQ_MP (@lem7221077 n m f _96750) (@lem7219487 _96750 m n f p h1)). Qed.
Lemma lem7221080 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7221081 (m : nat) (f : nat -> real) (_96750 : nat) (n : nat) : (term804 n m f _96750) = (term811 m f _96750 n).
Proof. exact (@lem7221080 (term805 m f _96750) (term528 _96750 n)). Qed.
Lemma lem7221083 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7221084 (m : nat) (f : nat -> real) (_96750 : nat) : (term812 m f _96750) = (term813 m f _96750).
Proof. exact (@lem7221083 (term528 m _96750) (term620 f _96750)). Qed.
Lemma lem7221086 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7221087 (m : nat) (_96750 : nat) : (term710 m _96750) = (term508 m _96750).
Proof. exact (@lem7221086 (term508 m _96750)). Qed.
Lemma lem7221088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221089 (m : nat) (_96750 : nat) : (term711 m _96750) = (term510 m _96750).
Proof. exact (MK_COMB (@lem7221088) (@lem7221087 m _96750)). Qed.
Lemma lem7221090 (f : nat -> real) (_96750 : nat) : (term814 f _96750) = (term814 f _96750).
Proof. exact (eq_refl (term814 f _96750)). Qed.
Lemma lem7221091 (m : nat) (f : nat -> real) (_96750 : nat) : (term813 m f _96750) = (term815 m f _96750).
Proof. exact (MK_COMB (@lem7221089 m _96750) (@lem7221090 f _96750)). Qed.
Lemma lem7221092 (m : nat) (f : nat -> real) (_96750 : nat) : (term812 m f _96750) = (term815 m f _96750).
Proof. exact (TRANS (@lem7221084 m f _96750) (@lem7221091 m f _96750)). Qed.
Lemma lem7221093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7221094 (m : nat) (f : nat -> real) (_96750 : nat) : (term816 m f _96750) = (term817 m f _96750).
Proof. exact (MK_COMB (@lem7221093) (@lem7221092 m f _96750)). Qed.
Lemma lem7221095 (_96750 : nat) (n : nat) : (term528 _96750 n) = (term528 _96750 n).
Proof. exact (eq_refl (term528 _96750 n)). Qed.
Lemma lem7221096 (m : nat) (f : nat -> real) (_96750 : nat) (n : nat) : (term811 m f _96750 n) = (term818 m f _96750 n).
Proof. exact (MK_COMB (@lem7221094 m f _96750) (@lem7221095 _96750 n)). Qed.
Lemma lem7221097 (m : nat) (f : nat -> real) (_96750 : nat) (n : nat) : (term804 n m f _96750) = (term818 m f _96750 n).
Proof. exact (TRANS (@lem7221081 m f _96750 n) (@lem7221096 m f _96750 n)). Qed.
Lemma lem7221099 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term819 x f m n.
Proof. exact (conj (@lem7220485 x m n f p h1 h2 h3 h4 h5) (@lem7220973 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221101 (_96750 : nat) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term818 m f _96750 n.
Proof. exact (EQ_MP (@lem7221097 m f _96750 n) (@lem7221078 _96750 m n f p h1)). Qed.
Lemma lem7221102 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term820 x f m n.
Proof. exact (@lem7221101 (term774 x f m n) m n f p h1). Qed.
Lemma lem7221105 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term821 x f m n.
Proof. exact (@lem7221102 x m n f p h5 (@lem7221099 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221106 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term822 x f m n.
Proof. exact (fun h0 : term823 x f m n => @lem7221105 x m n f p h1 h2 h3 h4 h5). Qed.
Lemma lem7221108 (p : Prop) : (term717 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7221109 (x : type1007) (f : nat -> real) (m : nat) (n : nat) : (term822 x f m n) = (term821 x f m n).
Proof. exact (@lem7221108 (term823 x f m n)). Qed.
Lemma lem7221110 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term821 x f m n.
Proof. exact (EQ_MP (@lem7221109 x f m n) (@lem7221106 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221112 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7221115 (_96756 : nat) (_96754 : nat) (_96755 : nat) : (term688 _96754 _96756 _96755) = (term824 _96756 _96754 _96755).
Proof. exact (@lem7221112 (term508 _96756 _96755) (term517 _96756 _96754 _96755)). Qed.
Lemma lem7221118 (_96756 : nat) (_96754 : nat) (_96755 : nat) (h1 : term73) : term824 _96756 _96754 _96755.
Proof. exact (EQ_MP (@lem7221115 _96756 _96754 _96755) (@lem7219511 _96754 _96756 _96755 h1)). Qed.
Lemma lem7221119 (x : type1007) (f : nat -> real) (m : nat) (_96754 : nat) (n : nat) (h1 : term73) : term825 x f m _96754 n.
Proof. exact (@lem7221118 (term774 x f m n) _96754 n h1). Qed.
Lemma lem7221122 (_96754 : nat) (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term826 x f m _96754 n.
Proof. exact (@lem7221119 x f m _96754 n h2 (@lem7221110 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221123 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term764 x f m n.
Proof. exact (@lem7221122 m x m n f p h1 h2 h3 h4 h5). Qed.
Lemma lem7221124 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term827 x f m n.
Proof. exact (fun h0 : term762 x f m n => @lem7221123 x m n f p h1 h2 h3 h4 h5). Qed.
Lemma lem7221126 (p : Prop) : (term717 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7221127 (x : type1007) (f : nat -> real) (m : nat) (n : nat) : (term827 x f m n) = (term764 x f m n).
Proof. exact (@lem7221126 (term762 x f m n)). Qed.
Lemma lem7221128 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term764 x f m n.
Proof. exact (EQ_MP (@lem7221127 x f m n) (@lem7221124 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221130 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : (term615 m n f) = term549.
Proof. exact (proj2 (@lem7219141 m n f p h1)). Qed.
Lemma lem7221131 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term700 m n f.
Proof. exact (fun h0 : term701 m n f => @lem7221130 m n f p h1). Qed.
Lemma lem7221133 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7221134 (m : nat) (n : nat) (f : nat -> real) : (term700 m n f) = ((term615 m n f) = term549).
Proof. exact (@lem7221133 ((term615 m n f) = term549)). Qed.
Lemma lem7221135 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : (term615 m n f) = term549.
Proof. exact (EQ_MP (@lem7221134 m n f) (@lem7221131 m n f p h1)). Qed.
Lemma lem7221137 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 m p.
Proof. exact (proj1 (@lem7219143 m n f p h1)). Qed.
Lemma lem7221138 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term702 m p.
Proof. exact (fun h0 : term528 m p => @lem7221137 m n f p h1). Qed.
Lemma lem7221140 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7221141 (m : nat) (p : nat) : (term702 m p) = (term508 m p).
Proof. exact (@lem7221140 (term508 m p)). Qed.
Lemma lem7221142 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 m p.
Proof. exact (EQ_MP (@lem7221141 m p) (@lem7221138 m n f p h1)). Qed.
Lemma lem7221144 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 p n.
Proof. exact (proj2 (@lem7219143 m n f p h1)). Qed.
Lemma lem7221145 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term702 p n.
Proof. exact (fun h0 : term528 p n => @lem7221144 m n f p h1). Qed.
Lemma lem7221147 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7221148 (p : nat) (n : nat) : (term702 p n) = (term508 p n).
Proof. exact (@lem7221147 (term508 p n)). Qed.
Lemma lem7221149 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term508 p n.
Proof. exact (EQ_MP (@lem7221148 p n) (@lem7221145 m n f p h1)). Qed.
Lemma lem7221150 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term511 m p n.
Proof. exact (conj (@lem7221142 m n f p h1) (@lem7221149 m n f p h1)). Qed.
Lemma lem7221152 (_96753 : nat) (_96751 : nat) (_96752 : nat) (h1 : term73) : term714 _96753 _96751 _96752.
Proof. exact (EQ_MP (@lem7220021 _96753 _96751 _96752) (@lem7219499 _96751 _96753 _96752 h1)). Qed.
Lemma lem7221153 (p : nat) (m : nat) (n : nat) (h1 : term73) : term714 p m n.
Proof. exact (@lem7221152 p m n h1). Qed.
Lemma lem7221156 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term515 p m n.
Proof. exact (@lem7221153 p m n h1 (@lem7221150 m n f p h2)). Qed.
Lemma lem7221157 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term715 p m n.
Proof. exact (fun h0 : term517 p m n => @lem7221156 m n f p h1 h2). Qed.
Lemma lem7221159 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7221160 (p : nat) (m : nat) (n : nat) : (term715 p m n) = (term515 p m n).
Proof. exact (@lem7221159 (term515 p m n)). Qed.
Lemma lem7221161 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term515 p m n.
Proof. exact (EQ_MP (@lem7221160 p m n) (@lem7221157 m n f p h1 h2)). Qed.
Lemma lem7221167 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221168 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term692 x _96745 _96744 _96746) = (term718 x _96745 _96744 _96746).
Proof. exact (@lem7221167 (term583 x _96744 _96745) (term592 _96745) (term719 _96745 _96744 _96746)). Qed.
Lemma lem7221182 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221183 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term720 _96745 _96744 _96746) = (term721 _96745 _96744 _96746).
Proof. exact (@lem7221182 (term563 _96745 _96744) (term592 _96745) (term557 _96745 _96744 _96746)). Qed.
Lemma lem7221209 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7221210 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term557 _96745 _96744 _96746) = (term722 _96744 _96746 _96745).
Proof. exact (@lem7221209 ((@I (nat -> real) _96744 _96746) = term549) (term554 _96746 _96745)). Qed.
Lemma lem7221218 (_96745 : nat -> Prop) : (term593 _96745) = (term593 _96745).
Proof. exact (eq_refl (term593 _96745)). Qed.
Lemma lem7221219 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term723 _96745 _96744 _96746) = (term724 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221218 _96745) (@lem7221210 _96744 _96746 _96745)). Qed.
Lemma lem7221223 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221224 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term724 _96744 _96746 _96745) = (term725 _96744 _96746 _96745).
Proof. exact (@lem7221223 ((@I (nat -> real) _96744 _96746) = term549) (term592 _96745) (term554 _96746 _96745)). Qed.
Lemma lem7221242 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term723 _96745 _96744 _96746) = (term725 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221219 _96744 _96746 _96745) (@lem7221224 _96744 _96746 _96745)). Qed.
Lemma lem7221243 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term726 _96745 _96744) = (term726 _96745 _96744).
Proof. exact (eq_refl (term726 _96745 _96744)). Qed.
Lemma lem7221244 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term721 _96745 _96744 _96746) = (term727 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221243 _96745 _96744) (@lem7221242 _96744 _96746 _96745)). Qed.
Lemma lem7221248 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221249 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term727 _96744 _96746 _96745) = (term728 _96744 _96746 _96745).
Proof. exact (@lem7221248 ((@I (nat -> real) _96744 _96746) = term549) (term563 _96745 _96744) (term729 _96746 _96745)). Qed.
Lemma lem7221279 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term721 _96745 _96744 _96746) = (term728 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221244 _96744 _96746 _96745) (@lem7221249 _96744 _96746 _96745)). Qed.
Lemma lem7221280 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term720 _96745 _96744 _96746) = (term728 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221183 _96745 _96744 _96746) (@lem7221279 _96744 _96746 _96745)). Qed.
Lemma lem7221281 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term730 x _96744 _96745) = (term730 x _96744 _96745).
Proof. exact (eq_refl (term730 x _96744 _96745)). Qed.
Lemma lem7221282 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term731 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221281 x _96744 _96745) (@lem7221280 _96744 _96746 _96745)). Qed.
Lemma lem7221286 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221287 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term731 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745).
Proof. exact (@lem7221286 ((@I (nat -> real) _96744 _96746) = term549) (term583 x _96744 _96745) (term733 _96744 _96746 _96745)). Qed.
Lemma lem7221327 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term718 x _96745 _96744 _96746) = (term732 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221282 x _96744 _96746 _96745) (@lem7221287 x _96744 _96746 _96745)). Qed.
Lemma lem7221328 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term692 x _96745 _96744 _96746) = (term732 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221168 x _96745 _96744 _96746) (@lem7221327 x _96744 _96746 _96745)). Qed.
Lemma lem7221329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7221330 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term734 x _96745 _96744 _96746) = (term735 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221329) (@lem7221328 x _96744 _96746 _96745)). Qed.
Lemma lem7221346 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221347 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term828 x _96744 _96746 _96745) = (term829 x _96744 _96746 _96745).
Proof. exact (@lem7221346 (term583 x _96744 _96745) (term592 _96745) (term830 _96744 _96746 _96745)). Qed.
Lemma lem7221361 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7221362 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term831 _96744 _96746 _96745) = (term733 _96744 _96746 _96745).
Proof. exact (@lem7221361 (term563 _96745 _96744) (term592 _96745) (term554 _96746 _96745)). Qed.
Lemma lem7221380 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term730 x _96744 _96745) = (term730 x _96744 _96745).
Proof. exact (eq_refl (term730 x _96744 _96745)). Qed.
Lemma lem7221381 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term829 x _96744 _96746 _96745) = (term832 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221380 x _96744 _96745) (@lem7221362 _96744 _96746 _96745)). Qed.
Lemma lem7221392 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term828 x _96744 _96746 _96745) = (term832 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221347 x _96744 _96746 _96745) (@lem7221381 x _96744 _96746 _96745)). Qed.
Lemma lem7221393 (_96744 : nat -> real) (_96746 : nat) : (term793 _96744 _96746) = (term793 _96744 _96746).
Proof. exact (eq_refl (term793 _96744 _96746)). Qed.
Lemma lem7221394 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term833 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221393 _96744 _96746) (@lem7221392 x _96744 _96746 _96745)). Qed.
Lemma lem7221405 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : ((term692 x _96745 _96744 _96746) = (term833 x _96744 _96746 _96745)) = ((term732 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745)).
Proof. exact (MK_COMB (@lem7221330 x _96744 _96746 _96745) (@lem7221394 x _96744 _96746 _96745)). Qed.
Lemma lem7221407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7221408 (x : Prop) : (x = x) = True.
Proof. exact (@lem7221407 Prop x). Qed.
Lemma lem7221409 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : ((term732 x _96744 _96746 _96745) = (term732 x _96744 _96746 _96745)) = True.
Proof. exact (@lem7221408 (term732 x _96744 _96746 _96745)). Qed.
Lemma lem7221410 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : ((term692 x _96745 _96744 _96746) = (term833 x _96744 _96746 _96745)) = True.
Proof. exact (TRANS (@lem7221405 x _96744 _96746 _96745) (@lem7221409 x _96744 _96746 _96745)). Qed.
Lemma lem7221411 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : True = ((term692 x _96745 _96744 _96746) = (term833 x _96744 _96746 _96745)).
Proof. exact (SYM (@lem7221410 x _96744 _96746 _96745)). Qed.
Lemma lem7221412 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term692 x _96745 _96744 _96746) = (term833 x _96744 _96746 _96745).
Proof. exact (EQ_MP (@lem7221411 x _96744 _96746 _96745) (@lem0)). Qed.
Lemma lem7221413 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) (x : type1007) (h1 : term504 x) : term833 x _96744 _96746 _96745.
Proof. exact (EQ_MP (@lem7221412 x _96744 _96746 _96745) (@lem7219577 _96745 _96744 _96746 x h1)). Qed.
Lemma lem7221415 (b : Prop) (a : Prop) : (a \/ b) = (term703 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7221416 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term833 x _96744 _96746 _96745) = (term834 x _96745 _96744 _96746).
Proof. exact (@lem7221415 (term828 x _96744 _96746 _96745) ((@I (nat -> real) _96744 _96746) = term549)). Qed.
Lemma lem7221418 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7221419 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term835 x _96744 _96746 _96745) = (term836 x _96744 _96746 _96745).
Proof. exact (@lem7221418 (term592 _96745) (term837 x _96744 _96746 _96745)). Qed.
Lemma lem7221421 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7221422 (_96745 : nat -> Prop) : (term739 _96745) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _96745).
Proof. exact (@lem7221421 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _96745)). Qed.
Lemma lem7221423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221424 (_96745 : nat -> Prop) : (term740 _96745) = (term741 _96745).
Proof. exact (MK_COMB (@lem7221423) (@lem7221422 _96745)). Qed.
Lemma lem7221426 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7221427 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term838 x _96744 _96746 _96745) = (term839 x _96744 _96746 _96745).
Proof. exact (@lem7221426 (term583 x _96744 _96745) (term830 _96744 _96746 _96745)). Qed.
Lemma lem7221429 (a : Prop) (b : Prop) : (term705 a b) = (term706 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7221430 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term840 _96744 _96746 _96745) = (term841 _96744 _96746 _96745).
Proof. exact (@lem7221429 (term563 _96745 _96744) (term554 _96746 _96745)). Qed.
Lemma lem7221432 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7221433 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term744 _96745 _96744) = ((term560 _96745 _96744) = term549).
Proof. exact (@lem7221432 ((term560 _96745 _96744) = term549)). Qed.
Lemma lem7221434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221435 (_96745 : nat -> Prop) (_96744 : nat -> real) : (term745 _96745 _96744) = (term746 _96745 _96744).
Proof. exact (MK_COMB (@lem7221434) (@lem7221433 _96745 _96744)). Qed.
Lemma lem7221437 (a : Prop) : (term709 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7221438 (_96746 : nat) (_96745 : nat -> Prop) : (term749 _96746 _96745) = (term552 _96746 _96745).
Proof. exact (@lem7221437 (term552 _96746 _96745)). Qed.
Lemma lem7221439 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term841 _96744 _96746 _96745) = (term842 _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221435 _96745 _96744) (@lem7221438 _96746 _96745)). Qed.
Lemma lem7221440 (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term840 _96744 _96746 _96745) = (term842 _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221430 _96744 _96746 _96745) (@lem7221439 _96744 _96746 _96745)). Qed.
Lemma lem7221441 (x : type1007) (_96744 : nat -> real) (_96745 : nat -> Prop) : (term843 x _96744 _96745) = (term843 x _96744 _96745).
Proof. exact (eq_refl (term843 x _96744 _96745)). Qed.
Lemma lem7221442 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term839 x _96744 _96746 _96745) = (term844 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221441 x _96744 _96745) (@lem7221440 _96744 _96746 _96745)). Qed.
Lemma lem7221443 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term838 x _96744 _96746 _96745) = (term844 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221427 x _96744 _96746 _96745) (@lem7221442 x _96744 _96746 _96745)). Qed.
Lemma lem7221444 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term836 x _96744 _96746 _96745) = (term845 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221424 _96745) (@lem7221443 x _96744 _96746 _96745)). Qed.
Lemma lem7221445 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term835 x _96744 _96746 _96745) = (term845 x _96744 _96746 _96745).
Proof. exact (TRANS (@lem7221419 x _96744 _96746 _96745) (@lem7221444 x _96744 _96746 _96745)). Qed.
Lemma lem7221446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7221447 (x : type1007) (_96744 : nat -> real) (_96746 : nat) (_96745 : nat -> Prop) : (term846 x _96744 _96746 _96745) = (term847 x _96744 _96746 _96745).
Proof. exact (MK_COMB (@lem7221446) (@lem7221445 x _96744 _96746 _96745)). Qed.
Lemma lem7221448 (_96744 : nat -> real) (_96746 : nat) : ((@I (nat -> real) _96744 _96746) = term549) = ((@I (nat -> real) _96744 _96746) = term549).
Proof. exact (eq_refl ((@I (nat -> real) _96744 _96746) = term549)). Qed.
Lemma lem7221449 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term834 x _96745 _96744 _96746) = (term848 x _96745 _96744 _96746).
Proof. exact (MK_COMB (@lem7221447 x _96744 _96746 _96745) (@lem7221448 _96744 _96746)). Qed.
Lemma lem7221450 (x : type1007) (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) : (term833 x _96744 _96746 _96745) = (term848 x _96745 _96744 _96746).
Proof. exact (TRANS (@lem7221416 x _96745 _96744 _96746) (@lem7221449 x _96745 _96744 _96746)). Qed.
Lemma lem7221452 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term73) (h2 : term151 m n f p) : term849 f p m n.
Proof. exact (conj (@lem7221135 m n f p h2) (@lem7221161 m n f p h1 h2)). Qed.
Lemma lem7221453 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term850 x f p m n.
Proof. exact (conj (@lem7221128 x m n f p h1 h2 h3 h4 h5) (@lem7221452 m n f p h2 h5)). Qed.
Lemma lem7221454 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : term851 x f p m n.
Proof. exact (conj (@lem7219971 m n h3) (@lem7221453 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221456 (_96745 : nat -> Prop) (_96744 : nat -> real) (_96746 : nat) (x : type1007) (h1 : term504 x) : term848 x _96745 _96744 _96746.
Proof. exact (EQ_MP (@lem7221450 x _96745 _96744 _96746) (@lem7221413 _96744 _96746 _96745 x h1)). Qed.
Lemma lem7221457 (m : nat) (n : nat) (f : nat -> real) (p : nat) (x : type1007) (h1 : term504 x) : term852 x m n f p.
Proof. exact (@lem7221456 (term512 m n) f p x h1). Qed.
Lemma lem7221460 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term606 f p) (h5 : term151 m n f p) : (@I (nat -> real) f p) = term549.
Proof. exact (@lem7221457 m n f p x h1 (@lem7221454 x m n f p h1 h2 h3 h4 h5)). Qed.
Lemma lem7221461 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term151 m n f p) : term853 f p.
Proof. exact (fun h0 : term606 f p => @lem7221460 x m n f p h1 h2 h3 h0 h4). Qed.
Lemma lem7221463 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7221464 (f : nat -> real) (p : nat) : (term853 f p) = ((@I (nat -> real) f p) = term549).
Proof. exact (@lem7221463 ((@I (nat -> real) f p) = term549)). Qed.
Lemma lem7221465 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term151 m n f p) : (@I (nat -> real) f p) = term549.
Proof. exact (EQ_MP (@lem7221464 f p) (@lem7221461 x m n f p h1 h2 h3 h4)). Qed.
Lemma lem7221468 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7221470 (f : nat -> real) (p : nat) : (term606 f p) = (term854 f p).
Proof. exact (@lem7221468 ((@I (nat -> real) f p) = term549)). Qed.
Lemma lem7221473 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term151 m n f p) : term854 f p.
Proof. exact (EQ_MP (@lem7221470 f p) (@lem7219471 m n f p h1)). Qed.
Lemma lem7221476 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term151 m n f p) : False.
Proof. exact (@lem7221473 m n f p h4 (@lem7221465 x m n f p h1 h2 h3 h4)). Qed.
Lemma lem7221477 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term151 m n f p) : term855.
Proof. exact (fun h0 : ~ False => @lem7221476 x m n f p h1 h2 h3 h4). Qed.
Lemma lem7221479 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7221480 : term855 = False.
Proof. exact (@lem7221479 False). Qed.
Lemma lem7221481 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term151 m n f p) : False.
Proof. exact (EQ_MP (@lem7221480) (@lem7221477 x m n f p h1 h2 h3 h4)). Qed.
Lemma lem7221482 (x : type1007) (m : nat) (n : nat) (f : nat -> real) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term154 m n f) : False.
Proof. exact (ex_elim (@lem7218312 m n f h4) (fun p : nat => fun h0 : term153 m n f p => @lem7221481 x m n f p h1 h2 h3 h0)). Qed.
Lemma lem7221483 (x : type1007) (m : nat) (f : nat -> real) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term156 m f) : False.
Proof. exact (ex_elim (@lem7218311 m f h4) (fun n : nat => fun h0 : term155 m f n => @lem7221482 x m n f h1 h2 h3 h0)). Qed.
Lemma lem7221484 (x : type1007) (f : nat -> real) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term158 f) : False.
Proof. exact (ex_elim (@lem7218310 f h4) (fun m : nat => fun h0 : term157 f m => @lem7221483 x m f h1 h2 h3 h0)). Qed.
Lemma lem7221485 (x : type1007) (h1 : term504 x) (h2 : term73) (h3 : term65) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7217148 h4) (fun f : nat -> real => fun h0 : term159 f => @lem7221484 x f h1 h2 h3 h0)). Qed.
Lemma lem7221486 {_132718 : Type'} (x : type1007) (h1 : term60 _132718) (h2 : term504 x) (h3 : term73) (h4 : term65) (h5 : term10) : False.
Proof. exact (ex_elim (@lem7217961 _132718 h1) (fun x' : type710 _132718 => fun h0 : term376 _132718 x' => @lem7221485 x h2 h3 h4 h5)). Qed.
Lemma lem7221487 {_132718 : Type'} (h1 : term60 _132718) (h2 : term11) (h3 : term73) (h4 : term65) (h5 : term10) : False.
Proof. exact (ex_elim (@lem7218307 h2) (fun x : type1007 => fun h0 : term506 x => @lem7221486 _132718 x h1 h0 h3 h4 h5)). Qed.
Lemma lem7221488 {_132718 : Type'} (h1 : term60 _132718) (h2 : term11) (h3 : term73) (h4 : term65) (h5 : term10) : term65 = False.
Proof. exact (prop_ext (fun h6 : term65 => @lem7221487 _132718 h1 h2 h3 h4 h5) (fun h6 : False => @lem7217615 h4)). Qed.
Lemma lem7221489 {_132718 : Type'} (h1 : term60 _132718) (h2 : term11) (h3 : term73) (h4 : term65) (h5 : term10) : False.
Proof. exact (EQ_MP (@lem7221488 _132718 h1 h2 h3 h4 h5) (@lem7217615 h4)). Qed.
Lemma lem7221490 {_132718 : Type'} (h1 : term60 _132718) (h2 : term73) (h3 : term65) (h4 : term10) : term16.
Proof. exact (fun h0 : term11 => @lem7221489 _132718 h1 h0 h2 h3 h4). Qed.
Lemma lem7221491 : term16 = term17.
Proof. exact (@lem69 term11). Qed.
Lemma lem7221492 {_132718 : Type'} (h1 : term60 _132718) (h2 : term73) (h3 : term65) (h4 : term10) : term17.
Proof. exact (EQ_MP (@lem7221491) (@lem7221490 _132718 h1 h2 h3 h4)). Qed.
Lemma lem7221493 {_132718 : Type'} (h1 : term73) (h2 : term65) (h3 : term10) : term20 _132718.
Proof. exact (fun h0 : term60 _132718 => @lem7221492 _132718 h0 h1 h2 h3). Qed.
Lemma lem7221494 {_132718 : Type'} (h1 : term73) (h2 : term10) : term23 _132718.
Proof. exact (fun h0 : term65 => @lem7221493 _132718 h1 h0 h2). Qed.
Lemma lem7221495 {_132718 : Type'} (h1 : term10) : term26 _132718.
Proof. exact (fun h0 : term73 => @lem7221494 _132718 h0 h1). Qed.
Lemma lem7221496 {_132718 : Type'} : term28 _132718.
Proof. exact (fun h0 : term10 => @lem7221495 _132718 h0). Qed.
Lemma lem7221497 {_132718 : Type'} : term12 _132718.
Proof. exact (EQ_MP (@lem7216882 _132718) (@lem7221496 _132718)). Qed.
Lemma lem7221499 {_132718 : Type'} : term12 _132718.
Proof. exact (@lem7216444 _132718 (@lem7221497 _132718)). Qed.
Lemma lem7221500 {_132718 : Type'} (h1 : term10) : term25 _132718.
Proof. exact (@lem7221499 _132718 (@lem7216427 h1)). Qed.
Lemma lem7221501 {_132718 : Type'} (h1 : term10) : term22 _132718.
Proof. exact (@lem7221500 _132718 h1 (@lem5371273)). Qed.
Lemma lem7221502 {_132718 : Type'} (h1 : term10) : term19 _132718.
Proof. exact (@lem7221501 _132718 h1 (@lem5329299)). Qed.
Lemma lem7221503 (h1 : term10) : term16.
Proof. exact (@lem7221502 Prop h1 (@lem7114167 Prop)). Qed.
Lemma lem7221504 (h1 : term10) : False.
Proof. exact (@lem7221503 h1 (@lem7216428)). Qed.
Lemma lem7221505 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem7221504 h1) (fun h2 : False => @lem7216427 h1)). Qed.
Lemma lem7221506 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem7221505 h1) (@lem7216427 h1)). Qed.
Lemma lem7221507 : term9.
Proof. exact (fun h0 : term10 => @lem7221506 h0). Qed.
Lemma lem7221508 : term8.
Proof. exact (EQ_MP (@lem7216426) (@lem7221507)). Qed.
