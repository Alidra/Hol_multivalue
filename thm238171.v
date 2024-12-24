Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm238171_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import AND_FORALL_THM_spec.
Require Import DIVMOD_UNIQ_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXP_ADD_spec.
Require Import EXP_LT_0_spec.
Require Import EXP_ONE_spec.
Require Import LT_EXP_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import ONE_spec.
Require Import SUB_ADD_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm80360_spec.
Require Import thm80550_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem235571 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem235572 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem235571 n m h1)). Qed.
Lemma lem235573 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem235574 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem235573 m n h1)). Qed.
Lemma lem235575 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem235572 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem235574 m n h1)). Qed.
Lemma lem235576 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem235575 m n)). Qed.
Lemma lem235577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235578 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem235577) (@lem235576 m)). Qed.
Lemma lem235579 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem235578 m)). Qed.
Lemma lem235580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235581 : term7 = term8.
Proof. exact (MK_COMB (@lem235580) (@lem235579)). Qed.
Lemma lem235582 : term8.
Proof. exact (EQ_MP (@lem235581) (@lem97961)). Qed.
Lemma lem235586 (n : nat) (m : nat) (h1 : (term9 m n) = (Peano.le n m)) : (term9 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem235587 (n : nat) (m : nat) (h1 : (term9 m n) = (Peano.le n m)) : (Peano.le n m) = (term9 m n).
Proof. exact (SYM (@lem235586 n m h1)). Qed.
Lemma lem235588 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term9 m n)) : (Peano.le n m) = (term9 m n).
Proof. exact (h1). Qed.
Lemma lem235589 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term9 m n)) : (term9 m n) = (Peano.le n m).
Proof. exact (SYM (@lem235588 m n h1)). Qed.
Lemma lem235590 (m : nat) (n : nat) : ((term9 m n) = (Peano.le n m)) = ((Peano.le n m) = (term9 m n)).
Proof. exact (prop_ext (fun h1 : (term9 m n) = (Peano.le n m) => @lem235587 n m h1) (fun h1 : (Peano.le n m) = (term9 m n) => @lem235589 m n h1)). Qed.
Lemma lem235591 (m : nat) : (term10 m) = (term11 m).
Proof. exact (fun_ext (fun n : nat => @lem235590 m n)). Qed.
Lemma lem235592 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235593 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem235592) (@lem235591 m)). Qed.
Lemma lem235594 : term14 = term15.
Proof. exact (fun_ext (fun m : nat => @lem235593 m)). Qed.
Lemma lem235595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235596 : term16 = term17.
Proof. exact (MK_COMB (@lem235595) (@lem235594)). Qed.
Lemma lem235597 : term17.
Proof. exact (EQ_MP (@lem235596) (@lem98377)). Qed.
Lemma lem235598 (m : nat) : term18 m.
Proof. exact (@lem235597 m). Qed.
Lemma lem235599 (m : nat) : (term18 m) = (term13 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem235600 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem235599 m) (@lem235598 m)). Qed.
Lemma lem235601 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem235600 m n). Qed.
Lemma lem235602 (m : nat) (n : nat) : (term19 m n) = ((Peano.le n m) = (term9 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem235604 : term20.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem235605 (m : nat) : term21 m.
Proof. exact (@lem235604 m). Qed.
Lemma lem235606 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem235607 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem235606 m) (@lem235605 m)). Qed.
Lemma lem235608 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem235607 m n). Qed.
Lemma lem235609 (m : nat) (n : nat) : (term23 m n) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem235611 : term26.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem235612 (m : nat) : term27 m.
Proof. exact (@lem235611 m). Qed.
Lemma lem235613 (m : nat) : (term27 m) = ((term28 m) = False).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem235615 (m : nat) : term29 m.
Proof. exact (@lem9784 (m = term30)). Qed.
Lemma lem235616 (m : nat) : (term29 m) = (term31 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem235617 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem235616 m) (@lem235615 m)). Qed.
Lemma lem235619 (m : nat) (h1 : term32 m) : term32 m.
Proof. exact (h1). Qed.
Lemma lem235623 (n : nat) (m : nat) (p : nat) (h1 : (term33 m n p) = (term34 n m p)) : (term33 m n p) = (term34 n m p).
Proof. exact (h1). Qed.
Lemma lem235624 (n : nat) (m : nat) (p : nat) (h1 : (term33 m n p) = (term34 n m p)) : (term34 n m p) = (term33 m n p).
Proof. exact (SYM (@lem235623 n m p h1)). Qed.
Lemma lem235625 (m : nat) (n : nat) (p : nat) (h1 : (term34 n m p) = (term33 m n p)) : (term34 n m p) = (term33 m n p).
Proof. exact (h1). Qed.
Lemma lem235626 (m : nat) (n : nat) (p : nat) (h1 : (term34 n m p) = (term33 m n p)) : (term33 m n p) = (term34 n m p).
Proof. exact (SYM (@lem235625 m n p h1)). Qed.
Lemma lem235627 (m : nat) (n : nat) (p : nat) : ((term33 m n p) = (term34 n m p)) = ((term34 n m p) = (term33 m n p)).
Proof. exact (prop_ext (fun h1 : (term33 m n p) = (term34 n m p) => @lem235624 n m p h1) (fun h1 : (term34 n m p) = (term33 m n p) => @lem235626 m n p h1)). Qed.
Lemma lem235628 (m : nat) (n : nat) : (term35 n m) = (term36 m n).
Proof. exact (fun_ext (fun p : nat => @lem235627 m n p)). Qed.
Lemma lem235629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235630 (m : nat) (n : nat) : (term37 n m) = (term38 m n).
Proof. exact (MK_COMB (@lem235629) (@lem235628 m n)). Qed.
Lemma lem235631 (m : nat) : (term39 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem235630 m n)). Qed.
Lemma lem235632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235633 (m : nat) : (term41 m) = (term42 m).
Proof. exact (MK_COMB (@lem235632) (@lem235631 m)). Qed.
Lemma lem235634 : term43 = term44.
Proof. exact (fun_ext (fun m : nat => @lem235633 m)). Qed.
Lemma lem235635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235636 : term45 = term46.
Proof. exact (MK_COMB (@lem235635) (@lem235634)). Qed.
Lemma lem235637 : term46.
Proof. exact (EQ_MP (@lem235636) (@lem87724)). Qed.
Lemma lem235638 (p : nat) (n : nat) : term47 p n.
Proof. exact (@lem9784 (Peano.le p n)). Qed.
Lemma lem235639 (p : nat) (n : nat) : (term47 p n) = (term48 p n).
Proof. exact (eq_refl (term47 p n)). Qed.
Lemma lem235640 (p : nat) (n : nat) : term48 p n.
Proof. exact (EQ_MP (@lem235639 p n) (@lem235638 p n)). Qed.
Lemma lem235641 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem235642 (p : nat) (n : nat) (h1 : term0 p n) : term0 p n.
Proof. exact (h1). Qed.
Lemma lem235643 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem235644 (m : nat) (h1 : term49) : term50 m.
Proof. exact (@lem235643 h1 m). Qed.
Lemma lem235645 (m : nat) : (term50 m) = (term51 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem235646 (m : nat) (h1 : term49) : term51 m.
Proof. exact (EQ_MP (@lem235645 m) (@lem235644 m h1)). Qed.
Lemma lem235647 (m : nat) (n : nat) (h1 : term49) : term52 m n.
Proof. exact (@lem235646 m h1 n). Qed.
Lemma lem235648 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem235649 (m : nat) (n : nat) (h1 : term49) : term53 m n.
Proof. exact (EQ_MP (@lem235648 m n) (@lem235647 m n h1)). Qed.
Lemma lem235650 (m : nat) (n : nat) (q : nat) (h1 : term49) : term54 m n q.
Proof. exact (@lem235649 m n h1 q). Qed.
Lemma lem235651 (q : nat) (m : nat) (n : nat) : (term54 m n q) = (term55 q m n).
Proof. exact (eq_refl (term54 m n q)). Qed.
Lemma lem235652 (q : nat) (m : nat) (n : nat) (h1 : term49) : term55 q m n.
Proof. exact (EQ_MP (@lem235651 q m n) (@lem235650 m n q h1)). Qed.
Lemma lem235653 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term49) : term56 q m n r.
Proof. exact (@lem235652 q m n h1 r). Qed.
Lemma lem235654 (q : nat) (m : nat) (n : nat) (r : nat) : (term56 q m n r) = (term57 q m n r).
Proof. exact (eq_refl (term56 q m n r)). Qed.
Lemma lem235655 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term49) : term57 q m n r.
Proof. exact (EQ_MP (@lem235654 q m n r) (@lem235653 q m n r h1)). Qed.
Lemma lem235656 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term58 m q r n) : term58 m q r n.
Proof. exact (h1). Qed.
Lemma lem235657 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term49) (h2 : term58 m q r n) : term59 q m n r.
Proof. exact (@lem235655 q m n r h1 (@lem235656 m q r n h2)). Qed.
Lemma lem235658 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term58 m q r n) : term60 q m n r.
Proof. exact (fun h0 : term49 => @lem235657 m q r n h0 h1). Qed.
Lemma lem235659 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem235660 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term49) (h2 : term58 m q r n) : term59 q m n r.
Proof. exact (@lem235658 m q r n h2 (@lem235659 h1)). Qed.
Lemma lem235661 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term49) : term57 q m n r.
Proof. exact (fun h0 : term58 m q r n => @lem235660 m q r n h1 h0). Qed.
Lemma lem235662 (q : nat) (m : nat) (n : nat) (h1 : term49) : term55 q m n.
Proof. exact (fun r : nat => @lem235661 q m n r h1). Qed.
Lemma lem235663 (q : nat) (m : nat) (h1 : term49) : term61 q m.
Proof. exact (fun n : nat => @lem235662 q m n h1). Qed.
Lemma lem235664 (q : nat) (h1 : term49) : term62 q.
Proof. exact (fun m : nat => @lem235663 q m h1). Qed.
Lemma lem235665 (h1 : term49) : term63.
Proof. exact (fun q : nat => @lem235664 q h1). Qed.
Lemma lem235666 : term64.
Proof. exact (fun h0 : term49 => @lem235665 h0). Qed.
Lemma lem235667 : term63.
Proof. exact (@lem235666 (@lem169651)). Qed.
Lemma lem235668 (q : nat) : term65 q.
Proof. exact (@lem235667 q). Qed.
Lemma lem235669 (q : nat) : (term65 q) = (term62 q).
Proof. exact (eq_refl (term65 q)). Qed.
Lemma lem235670 (q : nat) : term62 q.
Proof. exact (EQ_MP (@lem235669 q) (@lem235668 q)). Qed.
Lemma lem235671 (q : nat) (m : nat) : term66 q m.
Proof. exact (@lem235670 q m). Qed.
Lemma lem235672 (q : nat) (m : nat) : (term66 q m) = (term61 q m).
Proof. exact (eq_refl (term66 q m)). Qed.
Lemma lem235673 (q : nat) (m : nat) : term61 q m.
Proof. exact (EQ_MP (@lem235672 q m) (@lem235671 q m)). Qed.
Lemma lem235674 (q : nat) (m : nat) (n : nat) : term67 q m n.
Proof. exact (@lem235673 q m n). Qed.
Lemma lem235675 (q : nat) (m : nat) (n : nat) : (term67 q m n) = (term55 q m n).
Proof. exact (eq_refl (term67 q m n)). Qed.
Lemma lem235676 (q : nat) (m : nat) (n : nat) : term55 q m n.
Proof. exact (EQ_MP (@lem235675 q m n) (@lem235674 q m n)). Qed.
Lemma lem235677 (q : nat) (m : nat) (n : nat) (r : nat) : term56 q m n r.
Proof. exact (@lem235676 q m n r). Qed.
Lemma lem235678 (q : nat) (m : nat) (n : nat) (r : nat) : (term56 q m n r) = (term57 q m n r).
Proof. exact (eq_refl (term56 q m n r)). Qed.
Lemma lem235680 (m : nat) : term68 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem235681 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem235682 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem235681 m) (@lem235680 m)). Qed.
Lemma lem235684 (m : nat) (h1 : term70 m) : term70 m.
Proof. exact (h1). Qed.
Lemma lem235685 {A : Type'} (P : A -> Prop) : term71 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem235686 {A : Type'} (P : A -> Prop) : (term71 A P) = (term72 A P).
Proof. exact (eq_refl (term71 A P)). Qed.
Lemma lem235687 {A : Type'} (P : A -> Prop) : term72 A P.
Proof. exact (EQ_MP (@lem235686 A P) (@lem235685 A P)). Qed.
Lemma lem235688 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term73 A P Q.
Proof. exact (@lem235687 A P Q). Qed.
Lemma lem235689 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = ((term74 A P Q) = (term75 A P Q)).
Proof. exact (eq_refl (term73 A P Q)). Qed.
Lemma lem235692 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem235689 A P Q) (@lem235688 A P Q)). Qed.
Lemma lem235693 (P : nat -> Prop) (Q : nat -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem235692 nat P Q). Qed.
Lemma lem235694 : term78 = term79.
Proof. exact (@lem235693 term80 term81). Qed.
Lemma lem235695 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem235696 : term84 = term80.
Proof. exact (fun_ext (fun m : nat => @lem235695 m)). Qed.
Lemma lem235697 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235698 : term85 = term86.
Proof. exact (MK_COMB (@lem235697) (@lem235696)). Qed.
Lemma lem235699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235700 : term87 = term88.
Proof. exact (MK_COMB (@lem235699) (@lem235698)). Qed.
Lemma lem235701 (m : nat) : (term89 m) = (term90 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem235702 : term91 = term81.
Proof. exact (fun_ext (fun m : nat => @lem235701 m)). Qed.
Lemma lem235703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235704 : term92 = term93.
Proof. exact (MK_COMB (@lem235703) (@lem235702)). Qed.
Lemma lem235705 : term78 = term94.
Proof. exact (MK_COMB (@lem235700) (@lem235704)). Qed.
Lemma lem235706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem235707 : term95 = term96.
Proof. exact (MK_COMB (@lem235706) (@lem235705)). Qed.
Lemma lem235708 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem235709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235710 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem235709) (@lem235708 m)). Qed.
Lemma lem235711 (m : nat) : (term89 m) = (term90 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem235712 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem235710 m) (@lem235711 m)). Qed.
Lemma lem235713 : term101 = term102.
Proof. exact (fun_ext (fun m : nat => @lem235712 m)). Qed.
Lemma lem235714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235715 : term79 = term103.
Proof. exact (MK_COMB (@lem235714) (@lem235713)). Qed.
Lemma lem235716 : (term78 = term79) = (term94 = term103).
Proof. exact (MK_COMB (@lem235707) (@lem235715)). Qed.
Lemma lem235717 : term94 = term103.
Proof. exact (EQ_MP (@lem235716) (@lem235694)). Qed.
Lemma lem235723 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem235689 A P Q) (@lem235688 A P Q)). Qed.
Lemma lem235724 (P : nat -> Prop) (Q : nat -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem235723 nat P Q). Qed.
Lemma lem235725 (m : nat) : (term104 m) = (term105 m).
Proof. exact (@lem235724 (term106 m) (term107 m)). Qed.
Lemma lem235726 (n : nat) (m : nat) : (term108 m n) = (term109 n m).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem235727 (m : nat) : (term110 m) = (term106 m).
Proof. exact (fun_ext (fun n : nat => @lem235726 n m)). Qed.
Lemma lem235728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235729 (m : nat) : (term111 m) = (term83 m).
Proof. exact (MK_COMB (@lem235728) (@lem235727 m)). Qed.
Lemma lem235730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235731 (m : nat) : (term112 m) = (term98 m).
Proof. exact (MK_COMB (@lem235730) (@lem235729 m)). Qed.
Lemma lem235732 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (eq_refl (term113 m n)). Qed.
Lemma lem235733 (m : nat) : (term115 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem235732 m n)). Qed.
Lemma lem235734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235735 (m : nat) : (term116 m) = (term90 m).
Proof. exact (MK_COMB (@lem235734) (@lem235733 m)). Qed.
Lemma lem235736 (m : nat) : (term104 m) = (term100 m).
Proof. exact (MK_COMB (@lem235731 m) (@lem235735 m)). Qed.
Lemma lem235737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem235738 (m : nat) : (term117 m) = (term118 m).
Proof. exact (MK_COMB (@lem235737) (@lem235736 m)). Qed.
Lemma lem235739 (n : nat) (m : nat) : (term108 m n) = (term109 n m).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem235740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235741 (n : nat) (m : nat) : (term119 m n) = (term120 n m).
Proof. exact (MK_COMB (@lem235740) (@lem235739 n m)). Qed.
Lemma lem235742 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (eq_refl (term113 m n)). Qed.
Lemma lem235743 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem235741 n m) (@lem235742 m n)). Qed.
Lemma lem235744 (m : nat) : (term123 m) = (term124 m).
Proof. exact (fun_ext (fun n : nat => @lem235743 m n)). Qed.
Lemma lem235745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235746 (m : nat) : (term105 m) = (term125 m).
Proof. exact (MK_COMB (@lem235745) (@lem235744 m)). Qed.
Lemma lem235747 (m : nat) : ((term104 m) = (term105 m)) = ((term100 m) = (term125 m)).
Proof. exact (MK_COMB (@lem235738 m) (@lem235746 m)). Qed.
Lemma lem235748 (m : nat) : (term100 m) = (term125 m).
Proof. exact (EQ_MP (@lem235747 m) (@lem235725 m)). Qed.
Lemma lem235754 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem235689 A P Q) (@lem235688 A P Q)). Qed.
Lemma lem235755 (P : nat -> Prop) (Q : nat -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem235754 nat P Q). Qed.
Lemma lem235756 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (@lem235755 (term128 n m) (term129 m n)). Qed.
Lemma lem235757 (n : nat) (p : nat) (m : nat) : (term130 n m p) = (term131 n p m).
Proof. exact (eq_refl (term130 n m p)). Qed.
Lemma lem235758 (n : nat) (m : nat) : (term132 n m) = (term128 n m).
Proof. exact (fun_ext (fun p : nat => @lem235757 n p m)). Qed.
Lemma lem235759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235760 (n : nat) (m : nat) : (term133 n m) = (term109 n m).
Proof. exact (MK_COMB (@lem235759) (@lem235758 n m)). Qed.
Lemma lem235761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235762 (n : nat) (m : nat) : (term134 n m) = (term120 n m).
Proof. exact (MK_COMB (@lem235761) (@lem235760 n m)). Qed.
Lemma lem235763 (p : nat) (m : nat) (n : nat) : (term135 m n p) = (term136 p m n).
Proof. exact (eq_refl (term135 m n p)). Qed.
Lemma lem235764 (m : nat) (n : nat) : (term137 m n) = (term129 m n).
Proof. exact (fun_ext (fun p : nat => @lem235763 p m n)). Qed.
Lemma lem235765 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235766 (m : nat) (n : nat) : (term138 m n) = (term114 m n).
Proof. exact (MK_COMB (@lem235765) (@lem235764 m n)). Qed.
Lemma lem235767 (m : nat) (n : nat) : (term126 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem235762 n m) (@lem235766 m n)). Qed.
Lemma lem235768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem235769 (m : nat) (n : nat) : (term139 m n) = (term140 m n).
Proof. exact (MK_COMB (@lem235768) (@lem235767 m n)). Qed.
Lemma lem235770 (n : nat) (p : nat) (m : nat) : (term130 n m p) = (term131 n p m).
Proof. exact (eq_refl (term130 n m p)). Qed.
Lemma lem235771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235772 (n : nat) (p : nat) (m : nat) : (term141 n m p) = (term142 n p m).
Proof. exact (MK_COMB (@lem235771) (@lem235770 n p m)). Qed.
Lemma lem235773 (p : nat) (m : nat) (n : nat) : (term135 m n p) = (term136 p m n).
Proof. exact (eq_refl (term135 m n p)). Qed.
Lemma lem235774 (p : nat) (m : nat) (n : nat) : (term143 m n p) = (term144 p m n).
Proof. exact (MK_COMB (@lem235772 n p m) (@lem235773 p m n)). Qed.
Lemma lem235775 (m : nat) (n : nat) : (term145 m n) = (term146 m n).
Proof. exact (fun_ext (fun p : nat => @lem235774 p m n)). Qed.
Lemma lem235776 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235777 (m : nat) (n : nat) : (term127 m n) = (term147 m n).
Proof. exact (MK_COMB (@lem235776) (@lem235775 m n)). Qed.
Lemma lem235778 (m : nat) (n : nat) : ((term126 m n) = (term127 m n)) = ((term122 m n) = (term147 m n)).
Proof. exact (MK_COMB (@lem235769 m n) (@lem235777 m n)). Qed.
Lemma lem235779 (m : nat) (n : nat) : (term122 m n) = (term147 m n).
Proof. exact (EQ_MP (@lem235778 m n) (@lem235756 m n)). Qed.
Lemma lem235806 (m : nat) : (term124 m) = (term148 m).
Proof. exact (fun_ext (fun n : nat => @lem235779 m n)). Qed.
Lemma lem235807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235808 (m : nat) : (term125 m) = (term149 m).
Proof. exact (MK_COMB (@lem235807) (@lem235806 m)). Qed.
Lemma lem235813 (m : nat) : (term100 m) = (term149 m).
Proof. exact (TRANS (@lem235748 m) (@lem235808 m)). Qed.
Lemma lem235814 : term102 = term150.
Proof. exact (fun_ext (fun m : nat => @lem235813 m)). Qed.
Lemma lem235815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235816 : term103 = term151.
Proof. exact (MK_COMB (@lem235815) (@lem235814)). Qed.
Lemma lem235821 : term94 = term151.
Proof. exact (TRANS (@lem235717) (@lem235816)). Qed.
Lemma lem235822 : term151 = term94.
Proof. exact (SYM (@lem235821)). Qed.
Lemma lem235830 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235831 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235832 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term152.
Proof. exact (MK_COMB (@lem235831) (@lem235830 m h1)). Qed.
Lemma lem235833 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem235834 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem235832 m h1) (@lem235833)). Qed.
Lemma lem235836 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem235837 (x : nat) : (x = x) = True.
Proof. exact (@lem235836 nat x). Qed.
Lemma lem235838 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem235837 (NUMERAL 0)). Qed.
Lemma lem235839 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem235834 m h1) (@lem235838)). Qed.
Lemma lem235840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem235841 (m : nat) (h1 : m = (NUMERAL 0)) : (term70 m) = (~ True).
Proof. exact (MK_COMB (@lem235840) (@lem235839 m h1)). Qed.
Lemma lem235843 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem235844 (m : nat) (h1 : m = (NUMERAL 0)) : (term70 m) = False.
Proof. exact (TRANS (@lem235841 m h1) (@lem235843)). Qed.
Lemma lem235845 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem235846 (m : nat) (h1 : m = (NUMERAL 0)) : (term153 m) = (imp False).
Proof. exact (MK_COMB (@lem235845) (@lem235844 m h1)). Qed.
Lemma lem235850 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235851 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem235852 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m) = term154.
Proof. exact (MK_COMB (@lem235851) (@lem235850 m h1)). Qed.
Lemma lem235853 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem235854 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m n) = (term155 n).
Proof. exact (MK_COMB (@lem235852 m h1) (@lem235853 n)). Qed.
Lemma lem235855 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem235856 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term156 m n) = (term157 n).
Proof. exact (MK_COMB (@lem235855) (@lem235854 n m h1)). Qed.
Lemma lem235858 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235859 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem235860 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m) = term154.
Proof. exact (MK_COMB (@lem235859) (@lem235858 m h1)). Qed.
Lemma lem235861 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem235862 (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m p) = (term155 p).
Proof. exact (MK_COMB (@lem235860 m h1) (@lem235861 p)). Qed.
Lemma lem235863 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term158 n m p) = (term159 n p).
Proof. exact (MK_COMB (@lem235856 n m h1) (@lem235862 p m h1)). Qed.
Lemma lem235864 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235865 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term160 n m p) = (term161 n p).
Proof. exact (MK_COMB (@lem235864) (@lem235863 n p m h1)). Qed.
Lemma lem235867 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235868 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem235869 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m) = term154.
Proof. exact (MK_COMB (@lem235868) (@lem235867 m h1)). Qed.
Lemma lem235870 (n : nat) (p : nat) : (Nat.sub n p) = (Nat.sub n p).
Proof. exact (eq_refl (Nat.sub n p)). Qed.
Lemma lem235871 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term162 m n p) = (term163 n p).
Proof. exact (MK_COMB (@lem235869 m h1) (@lem235870 n p)). Qed.
Lemma lem235872 (p : nat) (n : nat) : (term164 p n) = (term164 p n).
Proof. exact (eq_refl (term164 p n)). Qed.
Lemma lem235873 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term165 m n p) = (term166 n p).
Proof. exact (MK_COMB (@lem235872 p n) (@lem235871 n p m h1)). Qed.
Lemma lem235879 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235880 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235881 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term152.
Proof. exact (MK_COMB (@lem235880) (@lem235879 m h1)). Qed.
Lemma lem235882 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem235883 (m : nat) (h1 : m = (NUMERAL 0)) : (m = term30) = ((NUMERAL 0) = term30).
Proof. exact (MK_COMB (@lem235881 m h1) (@lem235882)). Qed.
Lemma lem235886 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem235887 (m : nat) (h1 : m = (NUMERAL 0)) : (term167 m) = term168.
Proof. exact (MK_COMB (@lem235886) (@lem235883 m h1)). Qed.
Lemma lem235888 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem235889 (m : nat) (h1 : m = (NUMERAL 0)) : (term169 m) = term170.
Proof. exact (MK_COMB (@lem235887 m h1) (@lem235888)). Qed.
Lemma lem235890 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem235891 (m : nat) (h1 : m = (NUMERAL 0)) : (term171 m) = term172.
Proof. exact (MK_COMB (@lem235889 m h1) (@lem235890)). Qed.
Lemma lem235894 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term173 n p m) = (term174 n p).
Proof. exact (MK_COMB (@lem235873 n p m h1) (@lem235891 m h1)). Qed.
Lemma lem235895 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term158 n m p) = (term173 n p m)) = ((term159 n p) = (term174 n p)).
Proof. exact (MK_COMB (@lem235865 n p m h1) (@lem235894 n p m h1)). Qed.
Lemma lem235898 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term131 n p m) = (term175 n p).
Proof. exact (MK_COMB (@lem235846 m h1) (@lem235895 n p m h1)). Qed.
Lemma lem235900 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem235901 (n : nat) (p : nat) : (term175 n p) = True.
Proof. exact (@lem235900 ((term159 n p) = (term174 n p))). Qed.
Lemma lem235902 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term131 n p m) = True.
Proof. exact (TRANS (@lem235898 n p m h1) (@lem235901 n p)). Qed.
Lemma lem235903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235904 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term142 n p m) = (and True).
Proof. exact (MK_COMB (@lem235903) (@lem235902 n p m h1)). Qed.
Lemma lem235910 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235911 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235912 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term152.
Proof. exact (MK_COMB (@lem235911) (@lem235910 m h1)). Qed.
Lemma lem235913 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem235914 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem235912 m h1) (@lem235913)). Qed.
Lemma lem235916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem235917 (x : nat) : (x = x) = True.
Proof. exact (@lem235916 nat x). Qed.
Lemma lem235918 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem235917 (NUMERAL 0)). Qed.
Lemma lem235919 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem235914 m h1) (@lem235918)). Qed.
Lemma lem235920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem235921 (m : nat) (h1 : m = (NUMERAL 0)) : (term70 m) = (~ True).
Proof. exact (MK_COMB (@lem235920) (@lem235919 m h1)). Qed.
Lemma lem235923 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem235924 (m : nat) (h1 : m = (NUMERAL 0)) : (term70 m) = False.
Proof. exact (TRANS (@lem235921 m h1) (@lem235923)). Qed.
Lemma lem235925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem235926 (m : nat) (h1 : m = (NUMERAL 0)) : (term153 m) = (imp False).
Proof. exact (MK_COMB (@lem235925) (@lem235924 m h1)). Qed.
Lemma lem235930 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235931 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem235932 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m) = term154.
Proof. exact (MK_COMB (@lem235931) (@lem235930 m h1)). Qed.
Lemma lem235933 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem235934 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m n) = (term155 n).
Proof. exact (MK_COMB (@lem235932 m h1) (@lem235933 n)). Qed.
Lemma lem235935 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem235936 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term176 m n) = (term177 n).
Proof. exact (MK_COMB (@lem235935) (@lem235934 n m h1)). Qed.
Lemma lem235938 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235939 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem235940 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m) = term154.
Proof. exact (MK_COMB (@lem235939) (@lem235938 m h1)). Qed.
Lemma lem235941 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem235942 (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m p) = (term155 p).
Proof. exact (MK_COMB (@lem235940 m h1) (@lem235941 p)). Qed.
Lemma lem235943 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term178 n m p) = (term179 n p).
Proof. exact (MK_COMB (@lem235936 n m h1) (@lem235942 p m h1)). Qed.
Lemma lem235944 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235945 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term180 n m p) = (term181 n p).
Proof. exact (MK_COMB (@lem235944) (@lem235943 n p m h1)). Qed.
Lemma lem235951 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235952 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235953 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term152.
Proof. exact (MK_COMB (@lem235952) (@lem235951 m h1)). Qed.
Lemma lem235954 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem235955 (m : nat) (h1 : m = (NUMERAL 0)) : (m = term30) = ((NUMERAL 0) = term30).
Proof. exact (MK_COMB (@lem235953 m h1) (@lem235954)). Qed.
Lemma lem235958 (p : nat) (n : nat) : (term182 p n) = (term182 p n).
Proof. exact (eq_refl (term182 p n)). Qed.
Lemma lem235959 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term183 p n m) = (term184 p n).
Proof. exact (MK_COMB (@lem235958 p n) (@lem235955 m h1)). Qed.
Lemma lem235962 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem235963 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term185 p n m) = (term186 p n).
Proof. exact (MK_COMB (@lem235962) (@lem235959 p n m h1)). Qed.
Lemma lem235964 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem235965 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term187 p n m) = (term188 p n).
Proof. exact (MK_COMB (@lem235963 p n m h1) (@lem235964)). Qed.
Lemma lem235967 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem235968 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem235969 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m) = term154.
Proof. exact (MK_COMB (@lem235968) (@lem235967 m h1)). Qed.
Lemma lem235970 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem235971 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.pow m n) = (term155 n).
Proof. exact (MK_COMB (@lem235969 m h1) (@lem235970 n)). Qed.
Lemma lem235972 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term189 p m n) = (term190 p n).
Proof. exact (MK_COMB (@lem235965 p n m h1) (@lem235971 n m h1)). Qed.
Lemma lem235973 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term178 n m p) = (term189 p m n)) = ((term179 n p) = (term190 p n)).
Proof. exact (MK_COMB (@lem235945 n p m h1) (@lem235972 p n m h1)). Qed.
Lemma lem235976 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term136 p m n) = (term191 p n).
Proof. exact (MK_COMB (@lem235926 m h1) (@lem235973 p n m h1)). Qed.
Lemma lem235978 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem235979 (p : nat) (n : nat) : (term191 p n) = True.
Proof. exact (@lem235978 ((term179 n p) = (term190 p n))). Qed.
Lemma lem235980 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term136 p m n) = True.
Proof. exact (TRANS (@lem235976 p n m h1) (@lem235979 p n)). Qed.
Lemma lem235981 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term144 p m n) = (True /\ True).
Proof. exact (MK_COMB (@lem235904 n p m h1) (@lem235980 p n m h1)). Qed.
Lemma lem235983 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem235984 : (True /\ True) = True.
Proof. exact (@lem235983 True). Qed.
Lemma lem235985 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term144 p m n) = True.
Proof. exact (TRANS (@lem235981 p n m h1) (@lem235984)). Qed.
Lemma lem235986 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : True = (term144 p m n).
Proof. exact (SYM (@lem235985 p n m h1)). Qed.
Lemma lem235987 (p : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : term144 p m n.
Proof. exact (EQ_MP (@lem235986 p n m h1) (@lem0)). Qed.
Lemma lem235988 (m : nat) : term192 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem236006 (m : nat) (h1 : term70 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem235988 m (@lem235684 m h1)). Qed.
Lemma lem236007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem236008 (m : nat) (h1 : term70 m) : (term70 m) = (~ False).
Proof. exact (MK_COMB (@lem236007) (@lem236006 m h1)). Qed.
Lemma lem236010 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem236011 (m : nat) (h1 : term70 m) : (term70 m) = True.
Proof. exact (TRANS (@lem236008 m h1) (@lem236010)). Qed.
Lemma lem236012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem236013 (m : nat) (h1 : term70 m) : (term153 m) = (imp True).
Proof. exact (MK_COMB (@lem236012) (@lem236011 m h1)). Qed.
Lemma lem236020 (n : nat) (p : nat) (m : nat) : ((term158 n m p) = (term173 n p m)) = ((term158 n m p) = (term173 n p m)).
Proof. exact (eq_refl ((term158 n m p) = (term173 n p m))). Qed.
Lemma lem236021 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term131 n p m) = (term193 n p m).
Proof. exact (MK_COMB (@lem236013 m h1) (@lem236020 n p m)). Qed.
Lemma lem236023 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem236024 (n : nat) (p : nat) (m : nat) : (term193 n p m) = ((term158 n m p) = (term173 n p m)).
Proof. exact (@lem236023 ((term158 n m p) = (term173 n p m))). Qed.
Lemma lem236031 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term131 n p m) = ((term158 n m p) = (term173 n p m)).
Proof. exact (TRANS (@lem236021 n p m h1) (@lem236024 n p m)). Qed.
Lemma lem236032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem236033 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term142 n p m) = (term194 n p m).
Proof. exact (MK_COMB (@lem236032) (@lem236031 n p m h1)). Qed.
Lemma lem236037 (m : nat) (h1 : term70 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem235988 m (@lem235684 m h1)). Qed.
Lemma lem236038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem236039 (m : nat) (h1 : term70 m) : (term70 m) = (~ False).
Proof. exact (MK_COMB (@lem236038) (@lem236037 m h1)). Qed.
Lemma lem236041 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem236042 (m : nat) (h1 : term70 m) : (term70 m) = True.
Proof. exact (TRANS (@lem236039 m h1) (@lem236041)). Qed.
Lemma lem236043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem236044 (m : nat) (h1 : term70 m) : (term153 m) = (imp True).
Proof. exact (MK_COMB (@lem236043) (@lem236042 m h1)). Qed.
Lemma lem236051 (p : nat) (m : nat) (n : nat) : ((term178 n m p) = (term189 p m n)) = ((term178 n m p) = (term189 p m n)).
Proof. exact (eq_refl ((term178 n m p) = (term189 p m n))). Qed.
Lemma lem236052 (p : nat) (n : nat) (m : nat) (h1 : term70 m) : (term136 p m n) = (term195 p m n).
Proof. exact (MK_COMB (@lem236044 m h1) (@lem236051 p m n)). Qed.
Lemma lem236054 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem236055 (p : nat) (m : nat) (n : nat) : (term195 p m n) = ((term178 n m p) = (term189 p m n)).
Proof. exact (@lem236054 ((term178 n m p) = (term189 p m n))). Qed.
Lemma lem236062 (p : nat) (n : nat) (m : nat) (h1 : term70 m) : (term136 p m n) = ((term178 n m p) = (term189 p m n)).
Proof. exact (TRANS (@lem236052 p n m h1) (@lem236055 p m n)). Qed.
Lemma lem236063 (p : nat) (n : nat) (m : nat) (h1 : term70 m) : (term144 p m n) = (term196 p m n).
Proof. exact (MK_COMB (@lem236033 n p m h1) (@lem236062 p n m h1)). Qed.
Lemma lem236066 (p : nat) (n : nat) (m : nat) (h1 : term70 m) : (term196 p m n) = (term144 p m n).
Proof. exact (SYM (@lem236063 p n m h1)). Qed.
Lemma lem236068 (q : nat) (m : nat) (n : nat) (r : nat) : term57 q m n r.
Proof. exact (EQ_MP (@lem235678 q m n r) (@lem235677 q m n r)). Qed.
Lemma lem236069 (p : nat) (m : nat) (n : nat) : term197 p m n.
Proof. exact (@lem236068 (term173 n p m) (Nat.pow m n) (Nat.pow m p) (term189 p m n)). Qed.
Lemma lem236070 : term198.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem236086 : term199.
Proof. exact (proj1 (@lem236070)). Qed.
Lemma lem236087 (m : nat) : term200 m.
Proof. exact (@lem236086 m). Qed.
Lemma lem236088 (m : nat) : (term200 m) = ((term201 m) = m).
Proof. exact (eq_refl (term200 m)). Qed.
Lemma lem236094 (m : nat) : term202 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem236095 (m : nat) : (term202 m) = (term203 m).
Proof. exact (eq_refl (term202 m)). Qed.
Lemma lem236096 (m : nat) : term203 m.
Proof. exact (EQ_MP (@lem236095 m) (@lem236094 m)). Qed.
Lemma lem236097 (m : nat) (n : nat) : term204 m n.
Proof. exact (@lem236096 m n). Qed.
Lemma lem236098 (n : nat) (m : nat) : (term204 m n) = (term205 n m).
Proof. exact (eq_refl (term204 m n)). Qed.
Lemma lem236099 (n : nat) (m : nat) : term205 n m.
Proof. exact (EQ_MP (@lem236098 n m) (@lem236097 m n)). Qed.
Lemma lem236100 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem236101 (n : nat) (m : nat) (h1 : Peano.le n m) : (term206 m n) = m.
Proof. exact (@lem236099 n m (@lem236100 n m h1)). Qed.
Lemma lem236107 (n : nat) : term207 n.
Proof. exact (@lem146697 n). Qed.
Lemma lem236108 (n : nat) : (term207 n) = (term208 n).
Proof. exact (eq_refl (term207 n)). Qed.
Lemma lem236109 (n : nat) : term208 n.
Proof. exact (EQ_MP (@lem236108 n) (@lem236107 n)). Qed.
Lemma lem236110 (n : nat) (x : nat) : term209 n x.
Proof. exact (@lem236109 n x). Qed.
Lemma lem236111 (x : nat) (n : nat) : (term209 n x) = ((term210 x n) = (term211 x n)).
Proof. exact (eq_refl (term209 n x)). Qed.
Lemma lem236113 (m : nat) : term212 m.
Proof. exact (@lem235637 m). Qed.
Lemma lem236114 (m : nat) : (term212 m) = (term42 m).
Proof. exact (eq_refl (term212 m)). Qed.
Lemma lem236115 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem236114 m) (@lem236113 m)). Qed.
Lemma lem236116 (m : nat) (n : nat) : term213 m n.
Proof. exact (@lem236115 m n). Qed.
Lemma lem236117 (m : nat) (n : nat) : (term213 m n) = (term38 m n).
Proof. exact (eq_refl (term213 m n)). Qed.
Lemma lem236118 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem236117 m n) (@lem236116 m n)). Qed.
Lemma lem236119 (m : nat) (n : nat) (p : nat) : term214 m n p.
Proof. exact (@lem236118 m n p). Qed.
Lemma lem236120 (m : nat) (n : nat) (p : nat) : (term214 m n p) = ((term34 n m p) = (term33 m n p)).
Proof. exact (eq_refl (term214 m n p)). Qed.
Lemma lem236122 (m : nat) : term192 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem236135 (p : nat) (n : nat) : (Peano.le p n) = ((Peano.le p n) = True).
Proof. exact (@lem7 (Peano.le p n)). Qed.
Lemma lem236142 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term215 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem236143 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term216 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem236142 _2963 g t e g' t' e'). Qed.
Lemma lem236144 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term217 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem236143 _2963 g t e g' t'). Qed.
Lemma lem236145 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term218 _2963 g t e.
Proof. exact (fun g' : Prop => @lem236144 _2963 g t e g'). Qed.
Lemma lem236146 (g : Prop) (t : nat) (e : nat) : term219 g t e.
Proof. exact (@lem236145 nat g t e). Qed.
Lemma lem236147 (n : nat) (p : nat) (m : nat) : term220 n p m.
Proof. exact (@lem236146 (Peano.le p n) (term162 m n p) (term171 m)). Qed.
Lemma lem236148 (n : nat) (p : nat) (m : nat) (g' : Prop) : term221 n p m g'.
Proof. exact (@lem236147 n p m g'). Qed.
Lemma lem236149 (n : nat) (p : nat) (m : nat) (g' : Prop) : (term221 n p m g') = (term222 n p m g').
Proof. exact (eq_refl (term221 n p m g')). Qed.
Lemma lem236150 (n : nat) (p : nat) (m : nat) (g' : Prop) : term222 n p m g'.
Proof. exact (EQ_MP (@lem236149 n p m g') (@lem236148 n p m g')). Qed.
Lemma lem236151 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) : term223 n p m g' t'.
Proof. exact (@lem236150 n p m g' t'). Qed.
Lemma lem236152 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) : (term223 n p m g' t') = (term224 n p m g' t').
Proof. exact (eq_refl (term223 n p m g' t')). Qed.
Lemma lem236153 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) : term224 n p m g' t'.
Proof. exact (EQ_MP (@lem236152 n p m g' t') (@lem236151 n p m g' t')). Qed.
Lemma lem236154 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) (e' : nat) : term225 n p m g' t' e'.
Proof. exact (@lem236153 n p m g' t' e'). Qed.
Lemma lem236155 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) (e' : nat) : (term225 n p m g' t' e') = (term226 n p m g' t' e').
Proof. exact (eq_refl (term225 n p m g' t' e')). Qed.
Lemma lem236156 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) (e' : nat) : term226 n p m g' t' e'.
Proof. exact (EQ_MP (@lem236155 n p m g' t' e') (@lem236154 n p m g' t' e')). Qed.
Lemma lem236158 (p : nat) (n : nat) (h1 : Peano.le p n) : (Peano.le p n) = True.
Proof. exact (EQ_MP (@lem236135 p n) (@lem235641 p n h1)). Qed.
Lemma lem236159 (n : nat) (p : nat) (m : nat) (t' : nat) (e' : nat) : term227 n p m t' e'.
Proof. exact (@lem236156 n p m True t' e'). Qed.
Lemma lem236160 (m : nat) (t' : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term228 n p m t' e'.
Proof. exact (@lem236159 n p m t' e' (@lem236158 p n h1)). Qed.
Lemma lem236166 (m : nat) (n : nat) (p : nat) : (term162 m n p) = (term162 m n p).
Proof. exact (eq_refl (term162 m n p)). Qed.
Lemma lem236167 (m : nat) (n : nat) (p : nat) : term229 m n p.
Proof. exact (fun h0 : True => @lem236166 m n p). Qed.
Lemma lem236168 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term230 m n p e'.
Proof. exact (@lem236160 m (term162 m n p) e' p n h1). Qed.
Lemma lem236169 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term231 m n p e'.
Proof. exact (@lem236168 m e' p n h1 (@lem236167 m n p)). Qed.
Lemma lem236221 (m : nat) : (term171 m) = (term171 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem236222 (m : nat) : term232 m.
Proof. exact (fun h0 : ~ True => @lem236221 m). Qed.
Lemma lem236223 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term233 n p m.
Proof. exact (@lem236169 m (term171 m) p n h1). Qed.
Lemma lem236224 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term173 n p m) = (term234 n p m).
Proof. exact (@lem236223 m p n h1 (@lem236222 m)). Qed.
Lemma lem236226 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem236227 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem236226 nat t2 t1). Qed.
Lemma lem236228 (m : nat) (n : nat) (p : nat) : (term234 n p m) = (term162 m n p).
Proof. exact (@lem236227 (term171 m) (term162 m n p)). Qed.
Lemma lem236229 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term173 n p m) = (term162 m n p).
Proof. exact (TRANS (@lem236224 m p n h1) (@lem236228 m n p)). Qed.
Lemma lem236230 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem236231 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term235 n p m) = (term236 m n p).
Proof. exact (MK_COMB (@lem236230) (@lem236229 m p n h1)). Qed.
Lemma lem236232 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem236233 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term237 n m p) = (term238 n m p).
Proof. exact (MK_COMB (@lem236231 m p n h1) (@lem236232 m p)). Qed.
Lemma lem236235 (m : nat) (n : nat) (p : nat) : (term34 n m p) = (term33 m n p).
Proof. exact (EQ_MP (@lem236120 m n p) (@lem236119 m n p)). Qed.
Lemma lem236236 (m : nat) (n : nat) (p : nat) : (term238 n m p) = (term239 m n p).
Proof. exact (@lem236235 m (Nat.sub n p) p). Qed.
Lemma lem236238 (n : nat) (m : nat) : term205 n m.
Proof. exact (fun h0 : Peano.le n m => @lem236101 n m h0). Qed.
Lemma lem236239 (p : nat) (n : nat) : term205 p n.
Proof. exact (@lem236238 p n). Qed.
Lemma lem236241 (p : nat) (n : nat) (h1 : Peano.le p n) : (Peano.le p n) = True.
Proof. exact (EQ_MP (@lem236135 p n) (@lem235641 p n h1)). Qed.
Lemma lem236242 (p : nat) (n : nat) (h1 : Peano.le p n) : True = (Peano.le p n).
Proof. exact (SYM (@lem236241 p n h1)). Qed.
Lemma lem236243 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (EQ_MP (@lem236242 p n h1) (@lem0)). Qed.
Lemma lem236244 (p : nat) (n : nat) (h1 : Peano.le p n) : (term206 n p) = n.
Proof. exact (@lem236239 p n (@lem236243 p n h1)). Qed.
Lemma lem236245 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem236246 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term239 m n p) = (Nat.pow m n).
Proof. exact (MK_COMB (@lem236245 m) (@lem236244 p n h1)). Qed.
Lemma lem236247 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term238 n m p) = (Nat.pow m n).
Proof. exact (TRANS (@lem236236 m n p) (@lem236246 m p n h1)). Qed.
Lemma lem236248 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term237 n m p) = (Nat.pow m n).
Proof. exact (TRANS (@lem236233 m p n h1) (@lem236247 m p n h1)). Qed.
Lemma lem236249 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem236250 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term240 n m p) = (term241 m n).
Proof. exact (MK_COMB (@lem236249) (@lem236248 m p n h1)). Qed.
Lemma lem236252 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term215 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem236253 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term216 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem236252 _2963 g t e g' t' e'). Qed.
Lemma lem236254 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term217 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem236253 _2963 g t e g' t'). Qed.
Lemma lem236255 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term218 _2963 g t e.
Proof. exact (fun g' : Prop => @lem236254 _2963 g t e g'). Qed.
Lemma lem236256 (g : Prop) (t : nat) (e : nat) : term219 g t e.
Proof. exact (@lem236255 nat g t e). Qed.
Lemma lem236257 (p : nat) (m : nat) (n : nat) : term242 p m n.
Proof. exact (@lem236256 (term183 p n m) (NUMERAL 0) (Nat.pow m n)). Qed.
Lemma lem236258 (p : nat) (m : nat) (n : nat) (g' : Prop) : term243 p m n g'.
Proof. exact (@lem236257 p m n g'). Qed.
Lemma lem236259 (p : nat) (m : nat) (n : nat) (g' : Prop) : (term243 p m n g') = (term244 p m n g').
Proof. exact (eq_refl (term243 p m n g')). Qed.
Lemma lem236260 (p : nat) (m : nat) (n : nat) (g' : Prop) : term244 p m n g'.
Proof. exact (EQ_MP (@lem236259 p m n g') (@lem236258 p m n g')). Qed.
Lemma lem236261 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term245 p m n g' t'.
Proof. exact (@lem236260 p m n g' t'). Qed.
Lemma lem236262 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : (term245 p m n g' t') = (term246 p m n g' t').
Proof. exact (eq_refl (term245 p m n g' t')). Qed.
Lemma lem236263 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term246 p m n g' t'.
Proof. exact (EQ_MP (@lem236262 p m n g' t') (@lem236261 p m n g' t')). Qed.
Lemma lem236264 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term247 p m n g' t' e'.
Proof. exact (@lem236263 p m n g' t' e'). Qed.
Lemma lem236265 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : (term247 p m n g' t' e') = (term248 p m n g' t' e').
Proof. exact (eq_refl (term247 p m n g' t' e')). Qed.
Lemma lem236266 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term248 p m n g' t' e'.
Proof. exact (EQ_MP (@lem236265 p m n g' t' e') (@lem236264 p m n g' t' e')). Qed.
Lemma lem236270 (p : nat) (n : nat) (h1 : Peano.le p n) : (Peano.le p n) = True.
Proof. exact (EQ_MP (@lem236135 p n) (@lem235641 p n h1)). Qed.
Lemma lem236271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem236272 (p : nat) (n : nat) (h1 : Peano.le p n) : (term182 p n) = (or True).
Proof. exact (MK_COMB (@lem236271) (@lem236270 p n h1)). Qed.
Lemma lem236275 (m : nat) : (m = term30) = (m = term30).
Proof. exact (eq_refl (m = term30)). Qed.
Lemma lem236276 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term183 p n m) = (term249 m).
Proof. exact (MK_COMB (@lem236272 p n h1) (@lem236275 m)). Qed.
Lemma lem236278 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem236279 (m : nat) : (term249 m) = True.
Proof. exact (@lem236278 (m = term30)). Qed.
Lemma lem236280 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term183 p n m) = True.
Proof. exact (TRANS (@lem236276 m p n h1) (@lem236279 m)). Qed.
Lemma lem236281 (p : nat) (m : nat) (n : nat) (t' : nat) (e' : nat) : term250 p m n t' e'.
Proof. exact (@lem236266 p m n True t' e'). Qed.
Lemma lem236282 (m : nat) (t' : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term251 p m n t' e'.
Proof. exact (@lem236281 p m n t' e' (@lem236280 m p n h1)). Qed.
Lemma lem236288 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem236289 : term252.
Proof. exact (fun h0 : True => @lem236288). Qed.
Lemma lem236290 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term253 p m n e'.
Proof. exact (@lem236282 m (NUMERAL 0) e' p n h1). Qed.
Lemma lem236291 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term254 p m n e'.
Proof. exact (@lem236290 m e' p n h1 (@lem236289)). Qed.
Lemma lem236295 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem236296 (m : nat) (n : nat) : term255 m n.
Proof. exact (fun h0 : ~ True => @lem236295 m n). Qed.
Lemma lem236297 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term256 p m n.
Proof. exact (@lem236291 m (Nat.pow m n) p n h1). Qed.
Lemma lem236298 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term189 p m n) = (term257 m n).
Proof. exact (@lem236297 m p n h1 (@lem236296 m n)). Qed.
Lemma lem236300 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem236301 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem236300 nat t2 t1). Qed.
Lemma lem236302 (m : nat) (n : nat) : (term257 m n) = (NUMERAL 0).
Proof. exact (@lem236301 (Nat.pow m n) (NUMERAL 0)). Qed.
Lemma lem236303 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term189 p m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem236298 m p n h1) (@lem236302 m n)). Qed.
Lemma lem236304 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term258 p m n) = (term259 m n).
Proof. exact (MK_COMB (@lem236250 m p n h1) (@lem236303 m p n h1)). Qed.
Lemma lem236306 (m : nat) : (term201 m) = m.
Proof. exact (EQ_MP (@lem236088 m) (@lem236087 m)). Qed.
Lemma lem236307 (m : nat) (n : nat) : (term259 m n) = (Nat.pow m n).
Proof. exact (@lem236306 (Nat.pow m n)). Qed.
Lemma lem236308 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term258 p m n) = (Nat.pow m n).
Proof. exact (TRANS (@lem236304 m p n h1) (@lem236307 m n)). Qed.
Lemma lem236309 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem236310 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : ((Nat.pow m n) = (term258 p m n)) = ((Nat.pow m n) = (Nat.pow m n)).
Proof. exact (MK_COMB (@lem236309 m n) (@lem236308 m p n h1)). Qed.
Lemma lem236312 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem236313 (x : nat) : (x = x) = True.
Proof. exact (@lem236312 nat x). Qed.
Lemma lem236314 (m : nat) (n : nat) : ((Nat.pow m n) = (Nat.pow m n)) = True.
Proof. exact (@lem236313 (Nat.pow m n)). Qed.
Lemma lem236315 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : ((Nat.pow m n) = (term258 p m n)) = True.
Proof. exact (TRANS (@lem236310 m p n h1) (@lem236314 m n)). Qed.
Lemma lem236316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem236317 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term261 p m n) = (and True).
Proof. exact (MK_COMB (@lem236316) (@lem236315 m p n h1)). Qed.
Lemma lem236319 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term215 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem236320 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term216 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem236319 _2963 g t e g' t' e'). Qed.
Lemma lem236321 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term217 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem236320 _2963 g t e g' t'). Qed.
Lemma lem236322 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term218 _2963 g t e.
Proof. exact (fun g' : Prop => @lem236321 _2963 g t e g'). Qed.
Lemma lem236323 (g : Prop) (t : nat) (e : nat) : term219 g t e.
Proof. exact (@lem236322 nat g t e). Qed.
Lemma lem236324 (p : nat) (m : nat) (n : nat) : term242 p m n.
Proof. exact (@lem236323 (term183 p n m) (NUMERAL 0) (Nat.pow m n)). Qed.
Lemma lem236325 (p : nat) (m : nat) (n : nat) (g' : Prop) : term243 p m n g'.
Proof. exact (@lem236324 p m n g'). Qed.
Lemma lem236326 (p : nat) (m : nat) (n : nat) (g' : Prop) : (term243 p m n g') = (term244 p m n g').
Proof. exact (eq_refl (term243 p m n g')). Qed.
Lemma lem236327 (p : nat) (m : nat) (n : nat) (g' : Prop) : term244 p m n g'.
Proof. exact (EQ_MP (@lem236326 p m n g') (@lem236325 p m n g')). Qed.
Lemma lem236328 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term245 p m n g' t'.
Proof. exact (@lem236327 p m n g' t'). Qed.
Lemma lem236329 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : (term245 p m n g' t') = (term246 p m n g' t').
Proof. exact (eq_refl (term245 p m n g' t')). Qed.
Lemma lem236330 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term246 p m n g' t'.
Proof. exact (EQ_MP (@lem236329 p m n g' t') (@lem236328 p m n g' t')). Qed.
Lemma lem236331 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term247 p m n g' t' e'.
Proof. exact (@lem236330 p m n g' t' e'). Qed.
Lemma lem236332 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : (term247 p m n g' t' e') = (term248 p m n g' t' e').
Proof. exact (eq_refl (term247 p m n g' t' e')). Qed.
Lemma lem236333 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term248 p m n g' t' e'.
Proof. exact (EQ_MP (@lem236332 p m n g' t' e') (@lem236331 p m n g' t' e')). Qed.
Lemma lem236337 (p : nat) (n : nat) (h1 : Peano.le p n) : (Peano.le p n) = True.
Proof. exact (EQ_MP (@lem236135 p n) (@lem235641 p n h1)). Qed.
Lemma lem236338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem236339 (p : nat) (n : nat) (h1 : Peano.le p n) : (term182 p n) = (or True).
Proof. exact (MK_COMB (@lem236338) (@lem236337 p n h1)). Qed.
Lemma lem236342 (m : nat) : (m = term30) = (m = term30).
Proof. exact (eq_refl (m = term30)). Qed.
Lemma lem236343 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term183 p n m) = (term249 m).
Proof. exact (MK_COMB (@lem236339 p n h1) (@lem236342 m)). Qed.
Lemma lem236345 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem236346 (m : nat) : (term249 m) = True.
Proof. exact (@lem236345 (m = term30)). Qed.
Lemma lem236347 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term183 p n m) = True.
Proof. exact (TRANS (@lem236343 m p n h1) (@lem236346 m)). Qed.
Lemma lem236348 (p : nat) (m : nat) (n : nat) (t' : nat) (e' : nat) : term250 p m n t' e'.
Proof. exact (@lem236333 p m n True t' e'). Qed.
Lemma lem236349 (m : nat) (t' : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term251 p m n t' e'.
Proof. exact (@lem236348 p m n t' e' (@lem236347 m p n h1)). Qed.
Lemma lem236355 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem236356 : term252.
Proof. exact (fun h0 : True => @lem236355). Qed.
Lemma lem236357 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term253 p m n e'.
Proof. exact (@lem236349 m (NUMERAL 0) e' p n h1). Qed.
Lemma lem236358 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term254 p m n e'.
Proof. exact (@lem236357 m e' p n h1 (@lem236356)). Qed.
Lemma lem236362 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem236363 (m : nat) (n : nat) : term255 m n.
Proof. exact (fun h0 : ~ True => @lem236362 m n). Qed.
Lemma lem236364 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : term256 p m n.
Proof. exact (@lem236358 m (Nat.pow m n) p n h1). Qed.
Lemma lem236365 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term189 p m n) = (term257 m n).
Proof. exact (@lem236364 m p n h1 (@lem236363 m n)). Qed.
Lemma lem236367 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem236368 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem236367 nat t2 t1). Qed.
Lemma lem236369 (m : nat) (n : nat) : (term257 m n) = (NUMERAL 0).
Proof. exact (@lem236368 (Nat.pow m n) (NUMERAL 0)). Qed.
Lemma lem236370 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term189 p m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem236365 m p n h1) (@lem236369 m n)). Qed.
Lemma lem236371 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem236372 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term262 p m n) = term263.
Proof. exact (MK_COMB (@lem236371) (@lem236370 m p n h1)). Qed.
Lemma lem236373 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem236374 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term264 n m p) = (term210 m p).
Proof. exact (MK_COMB (@lem236372 m p n h1) (@lem236373 m p)). Qed.
Lemma lem236376 (x : nat) (n : nat) : (term210 x n) = (term211 x n).
Proof. exact (EQ_MP (@lem236111 x n) (@lem236110 n x)). Qed.
Lemma lem236377 (m : nat) (p : nat) : (term210 m p) = (term211 m p).
Proof. exact (@lem236376 m p). Qed.
Lemma lem236381 (m : nat) (h1 : term70 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem236122 m (@lem235684 m h1)). Qed.
Lemma lem236382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem236383 (m : nat) (h1 : term70 m) : (term70 m) = (~ False).
Proof. exact (MK_COMB (@lem236382) (@lem236381 m h1)). Qed.
Lemma lem236385 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem236386 (m : nat) (h1 : term70 m) : (term70 m) = True.
Proof. exact (TRANS (@lem236383 m h1) (@lem236385)). Qed.
Lemma lem236387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem236388 (m : nat) (h1 : term70 m) : (term265 m) = (or True).
Proof. exact (MK_COMB (@lem236387) (@lem236386 m h1)). Qed.
Lemma lem236391 (p : nat) : (p = (NUMERAL 0)) = (p = (NUMERAL 0)).
Proof. exact (eq_refl (p = (NUMERAL 0))). Qed.
Lemma lem236392 (p : nat) (m : nat) (h1 : term70 m) : (term211 m p) = (term266 p).
Proof. exact (MK_COMB (@lem236388 m h1) (@lem236391 p)). Qed.
Lemma lem236394 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem236395 (p : nat) : (term266 p) = True.
Proof. exact (@lem236394 (p = (NUMERAL 0))). Qed.
Lemma lem236396 (p : nat) (m : nat) (h1 : term70 m) : (term211 m p) = True.
Proof. exact (TRANS (@lem236392 p m h1) (@lem236395 p)). Qed.
Lemma lem236397 (p : nat) (m : nat) (h1 : term70 m) : (term210 m p) = True.
Proof. exact (TRANS (@lem236377 m p) (@lem236396 p m h1)). Qed.
Lemma lem236398 (m : nat) (p : nat) (n : nat) (h1 : term70 m) (h2 : Peano.le p n) : (term264 n m p) = True.
Proof. exact (TRANS (@lem236374 m p n h2) (@lem236397 p m h1)). Qed.
Lemma lem236399 (m : nat) (p : nat) (n : nat) (h1 : term70 m) (h2 : Peano.le p n) : (term267 n m p) = (True /\ True).
Proof. exact (MK_COMB (@lem236317 m p n h2) (@lem236398 m p n h1 h2)). Qed.
Lemma lem236401 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem236402 : (True /\ True) = True.
Proof. exact (@lem236401 True). Qed.
Lemma lem236403 (m : nat) (p : nat) (n : nat) (h1 : term70 m) (h2 : Peano.le p n) : (term267 n m p) = True.
Proof. exact (TRANS (@lem236399 m p n h1 h2) (@lem236402)). Qed.
Lemma lem236404 (m : nat) (p : nat) (n : nat) (h1 : term70 m) (h2 : Peano.le p n) : True = (term267 n m p).
Proof. exact (SYM (@lem236403 m p n h1 h2)). Qed.
Lemma lem236405 (m : nat) (p : nat) (n : nat) (h1 : term70 m) (h2 : Peano.le p n) : term267 n m p.
Proof. exact (EQ_MP (@lem236404 m p n h1 h2) (@lem0)). Qed.
Lemma lem236471 (p : nat) (n : nat) : term268 p n.
Proof. exact (@lem82 (Peano.le p n)). Qed.
Lemma lem236478 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term215 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem236479 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term216 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem236478 _2963 g t e g' t' e'). Qed.
Lemma lem236480 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term217 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem236479 _2963 g t e g' t'). Qed.
Lemma lem236481 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term218 _2963 g t e.
Proof. exact (fun g' : Prop => @lem236480 _2963 g t e g'). Qed.
Lemma lem236482 (g : Prop) (t : nat) (e : nat) : term219 g t e.
Proof. exact (@lem236481 nat g t e). Qed.
Lemma lem236483 (n : nat) (p : nat) (m : nat) : term220 n p m.
Proof. exact (@lem236482 (Peano.le p n) (term162 m n p) (term171 m)). Qed.
Lemma lem236484 (n : nat) (p : nat) (m : nat) (g' : Prop) : term221 n p m g'.
Proof. exact (@lem236483 n p m g'). Qed.
Lemma lem236485 (n : nat) (p : nat) (m : nat) (g' : Prop) : (term221 n p m g') = (term222 n p m g').
Proof. exact (eq_refl (term221 n p m g')). Qed.
Lemma lem236486 (n : nat) (p : nat) (m : nat) (g' : Prop) : term222 n p m g'.
Proof. exact (EQ_MP (@lem236485 n p m g') (@lem236484 n p m g')). Qed.
Lemma lem236487 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) : term223 n p m g' t'.
Proof. exact (@lem236486 n p m g' t'). Qed.
Lemma lem236488 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) : (term223 n p m g' t') = (term224 n p m g' t').
Proof. exact (eq_refl (term223 n p m g' t')). Qed.
Lemma lem236489 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) : term224 n p m g' t'.
Proof. exact (EQ_MP (@lem236488 n p m g' t') (@lem236487 n p m g' t')). Qed.
Lemma lem236490 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) (e' : nat) : term225 n p m g' t' e'.
Proof. exact (@lem236489 n p m g' t' e'). Qed.
Lemma lem236491 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) (e' : nat) : (term225 n p m g' t' e') = (term226 n p m g' t' e').
Proof. exact (eq_refl (term225 n p m g' t' e')). Qed.
Lemma lem236492 (n : nat) (p : nat) (m : nat) (g' : Prop) (t' : nat) (e' : nat) : term226 n p m g' t' e'.
Proof. exact (EQ_MP (@lem236491 n p m g' t' e') (@lem236490 n p m g' t' e')). Qed.
Lemma lem236494 (p : nat) (n : nat) (h1 : term0 p n) : (Peano.le p n) = False.
Proof. exact (@lem236471 p n (@lem235642 p n h1)). Qed.
Lemma lem236495 (n : nat) (p : nat) (m : nat) (t' : nat) (e' : nat) : term269 n p m t' e'.
Proof. exact (@lem236492 n p m False t' e'). Qed.
Lemma lem236496 (m : nat) (t' : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term270 n p m t' e'.
Proof. exact (@lem236495 n p m t' e' (@lem236494 p n h1)). Qed.
Lemma lem236500 (m : nat) (n : nat) (p : nat) : (term162 m n p) = (term162 m n p).
Proof. exact (eq_refl (term162 m n p)). Qed.
Lemma lem236501 (m : nat) (n : nat) (p : nat) : term271 m n p.
Proof. exact (fun h0 : False => @lem236500 m n p). Qed.
Lemma lem236502 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term272 m n p e'.
Proof. exact (@lem236496 m (term162 m n p) e' p n h1). Qed.
Lemma lem236503 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term273 m n p e'.
Proof. exact (@lem236502 m e' p n h1 (@lem236501 m n p)). Qed.
Lemma lem236557 (m : nat) : (term171 m) = (term171 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem236558 (m : nat) : term274 m.
Proof. exact (fun h0 : ~ False => @lem236557 m). Qed.
Lemma lem236559 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : term275 n p m.
Proof. exact (@lem236503 m (term171 m) p n h1). Qed.
Lemma lem236560 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term173 n p m) = (term276 n p m).
Proof. exact (@lem236559 m p n h1 (@lem236558 m)). Qed.
Lemma lem236562 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem236563 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem236562 nat t1 t2). Qed.
Lemma lem236564 (n : nat) (p : nat) (m : nat) : (term276 n p m) = (term171 m).
Proof. exact (@lem236563 (term162 m n p) (term171 m)). Qed.
Lemma lem236613 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term173 n p m) = (term171 m).
Proof. exact (TRANS (@lem236560 m p n h1) (@lem236564 n p m)). Qed.
Lemma lem236614 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem236615 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term235 n p m) = (term277 m).
Proof. exact (MK_COMB (@lem236614) (@lem236613 m p n h1)). Qed.
Lemma lem236664 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem236665 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term237 n m p) = (term278 m p).
Proof. exact (MK_COMB (@lem236615 m p n h1) (@lem236664 m p)). Qed.
Lemma lem236714 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem236715 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term240 n m p) = (term279 m p).
Proof. exact (MK_COMB (@lem236714) (@lem236665 m p n h1)). Qed.
Lemma lem236765 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term215 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem236766 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term216 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem236765 _2963 g t e g' t' e'). Qed.
Lemma lem236767 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term217 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem236766 _2963 g t e g' t'). Qed.
Lemma lem236768 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term218 _2963 g t e.
Proof. exact (fun g' : Prop => @lem236767 _2963 g t e g'). Qed.
Lemma lem236769 (g : Prop) (t : nat) (e : nat) : term219 g t e.
Proof. exact (@lem236768 nat g t e). Qed.
Lemma lem236770 (p : nat) (m : nat) (n : nat) : term242 p m n.
Proof. exact (@lem236769 (term183 p n m) (NUMERAL 0) (Nat.pow m n)). Qed.
Lemma lem236771 (p : nat) (m : nat) (n : nat) (g' : Prop) : term243 p m n g'.
Proof. exact (@lem236770 p m n g'). Qed.
Lemma lem236772 (p : nat) (m : nat) (n : nat) (g' : Prop) : (term243 p m n g') = (term244 p m n g').
Proof. exact (eq_refl (term243 p m n g')). Qed.
Lemma lem236773 (p : nat) (m : nat) (n : nat) (g' : Prop) : term244 p m n g'.
Proof. exact (EQ_MP (@lem236772 p m n g') (@lem236771 p m n g')). Qed.
Lemma lem236774 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term245 p m n g' t'.
Proof. exact (@lem236773 p m n g' t'). Qed.
Lemma lem236775 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : (term245 p m n g' t') = (term246 p m n g' t').
Proof. exact (eq_refl (term245 p m n g' t')). Qed.
Lemma lem236776 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term246 p m n g' t'.
Proof. exact (EQ_MP (@lem236775 p m n g' t') (@lem236774 p m n g' t')). Qed.
Lemma lem236777 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term247 p m n g' t' e'.
Proof. exact (@lem236776 p m n g' t' e'). Qed.
Lemma lem236778 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : (term247 p m n g' t' e') = (term248 p m n g' t' e').
Proof. exact (eq_refl (term247 p m n g' t' e')). Qed.
Lemma lem236779 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term248 p m n g' t' e'.
Proof. exact (EQ_MP (@lem236778 p m n g' t' e') (@lem236777 p m n g' t' e')). Qed.
Lemma lem236783 (p : nat) (n : nat) (h1 : term0 p n) : (Peano.le p n) = False.
Proof. exact (@lem236471 p n (@lem235642 p n h1)). Qed.
Lemma lem236784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem236785 (p : nat) (n : nat) (h1 : term0 p n) : (term182 p n) = (or False).
Proof. exact (MK_COMB (@lem236784) (@lem236783 p n h1)). Qed.
Lemma lem236788 (m : nat) : (m = term30) = (m = term30).
Proof. exact (eq_refl (m = term30)). Qed.
Lemma lem236789 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term183 p n m) = (term280 m).
Proof. exact (MK_COMB (@lem236785 p n h1) (@lem236788 m)). Qed.
Lemma lem236791 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem236792 (m : nat) : (term280 m) = (m = term30).
Proof. exact (@lem236791 (m = term30)). Qed.
Lemma lem236795 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term183 p n m) = (m = term30).
Proof. exact (TRANS (@lem236789 m p n h1) (@lem236792 m)). Qed.
Lemma lem236796 (p : nat) (n : nat) (m : nat) (t' : nat) (e' : nat) : term281 p n m t' e'.
Proof. exact (@lem236779 p m n (m = term30) t' e'). Qed.
Lemma lem236797 (m : nat) (t' : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term282 p n m t' e'.
Proof. exact (@lem236796 p n m t' e' (@lem236795 m p n h1)). Qed.
Lemma lem236799 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem236800 (m : nat) : term283 m.
Proof. exact (fun h0 : m = term30 => @lem236799). Qed.
Lemma lem236801 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term284 p n m e'.
Proof. exact (@lem236797 m (NUMERAL 0) e' p n h1). Qed.
Lemma lem236802 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term285 p n m e'.
Proof. exact (@lem236801 m e' p n h1 (@lem236800 m)). Qed.
Lemma lem236817 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem236818 (m : nat) (n : nat) : term286 m n.
Proof. exact (fun h0 : term32 m => @lem236817 m n). Qed.
Lemma lem236819 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : term287 p m n.
Proof. exact (@lem236802 m (Nat.pow m n) p n h1). Qed.
Lemma lem236820 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term189 p m n) = (term288 m n).
Proof. exact (@lem236819 m p n h1 (@lem236818 m n)). Qed.
Lemma lem236869 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term258 p m n) = (term289 p m n).
Proof. exact (MK_COMB (@lem236715 m p n h1) (@lem236820 m p n h1)). Qed.
Lemma lem236966 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem236967 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : ((Nat.pow m n) = (term258 p m n)) = ((Nat.pow m n) = (term289 p m n)).
Proof. exact (MK_COMB (@lem236966 m n) (@lem236869 m p n h1)). Qed.
Lemma lem237066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem237067 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term261 p m n) = (term290 p m n).
Proof. exact (MK_COMB (@lem237066) (@lem236967 m p n h1)). Qed.
Lemma lem237167 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term215 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem237168 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term216 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem237167 _2963 g t e g' t' e'). Qed.
Lemma lem237169 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term217 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem237168 _2963 g t e g' t'). Qed.
Lemma lem237170 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term218 _2963 g t e.
Proof. exact (fun g' : Prop => @lem237169 _2963 g t e g'). Qed.
Lemma lem237171 (g : Prop) (t : nat) (e : nat) : term219 g t e.
Proof. exact (@lem237170 nat g t e). Qed.
Lemma lem237172 (p : nat) (m : nat) (n : nat) : term242 p m n.
Proof. exact (@lem237171 (term183 p n m) (NUMERAL 0) (Nat.pow m n)). Qed.
Lemma lem237173 (p : nat) (m : nat) (n : nat) (g' : Prop) : term243 p m n g'.
Proof. exact (@lem237172 p m n g'). Qed.
Lemma lem237174 (p : nat) (m : nat) (n : nat) (g' : Prop) : (term243 p m n g') = (term244 p m n g').
Proof. exact (eq_refl (term243 p m n g')). Qed.
Lemma lem237175 (p : nat) (m : nat) (n : nat) (g' : Prop) : term244 p m n g'.
Proof. exact (EQ_MP (@lem237174 p m n g') (@lem237173 p m n g')). Qed.
Lemma lem237176 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term245 p m n g' t'.
Proof. exact (@lem237175 p m n g' t'). Qed.
Lemma lem237177 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : (term245 p m n g' t') = (term246 p m n g' t').
Proof. exact (eq_refl (term245 p m n g' t')). Qed.
Lemma lem237178 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) : term246 p m n g' t'.
Proof. exact (EQ_MP (@lem237177 p m n g' t') (@lem237176 p m n g' t')). Qed.
Lemma lem237179 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term247 p m n g' t' e'.
Proof. exact (@lem237178 p m n g' t' e'). Qed.
Lemma lem237180 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : (term247 p m n g' t' e') = (term248 p m n g' t' e').
Proof. exact (eq_refl (term247 p m n g' t' e')). Qed.
Lemma lem237181 (p : nat) (m : nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term248 p m n g' t' e'.
Proof. exact (EQ_MP (@lem237180 p m n g' t' e') (@lem237179 p m n g' t' e')). Qed.
Lemma lem237185 (p : nat) (n : nat) (h1 : term0 p n) : (Peano.le p n) = False.
Proof. exact (@lem236471 p n (@lem235642 p n h1)). Qed.
Lemma lem237186 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem237187 (p : nat) (n : nat) (h1 : term0 p n) : (term182 p n) = (or False).
Proof. exact (MK_COMB (@lem237186) (@lem237185 p n h1)). Qed.
Lemma lem237190 (m : nat) : (m = term30) = (m = term30).
Proof. exact (eq_refl (m = term30)). Qed.
Lemma lem237191 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term183 p n m) = (term280 m).
Proof. exact (MK_COMB (@lem237187 p n h1) (@lem237190 m)). Qed.
Lemma lem237193 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem237194 (m : nat) : (term280 m) = (m = term30).
Proof. exact (@lem237193 (m = term30)). Qed.
Lemma lem237197 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term183 p n m) = (m = term30).
Proof. exact (TRANS (@lem237191 m p n h1) (@lem237194 m)). Qed.
Lemma lem237198 (p : nat) (n : nat) (m : nat) (t' : nat) (e' : nat) : term281 p n m t' e'.
Proof. exact (@lem237181 p m n (m = term30) t' e'). Qed.
Lemma lem237199 (m : nat) (t' : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term282 p n m t' e'.
Proof. exact (@lem237198 p n m t' e' (@lem237197 m p n h1)). Qed.
Lemma lem237201 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237202 (m : nat) : term283 m.
Proof. exact (fun h0 : m = term30 => @lem237201). Qed.
Lemma lem237203 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term284 p n m e'.
Proof. exact (@lem237199 m (NUMERAL 0) e' p n h1). Qed.
Lemma lem237204 (m : nat) (e' : nat) (p : nat) (n : nat) (h1 : term0 p n) : term285 p n m e'.
Proof. exact (@lem237203 m e' p n h1 (@lem237202 m)). Qed.
Lemma lem237219 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem237220 (m : nat) (n : nat) : term286 m n.
Proof. exact (fun h0 : term32 m => @lem237219 m n). Qed.
Lemma lem237221 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : term287 p m n.
Proof. exact (@lem237204 m (Nat.pow m n) p n h1). Qed.
Lemma lem237222 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term189 p m n) = (term288 m n).
Proof. exact (@lem237221 m p n h1 (@lem237220 m n)). Qed.
Lemma lem237271 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem237272 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term262 p m n) = (term291 m n).
Proof. exact (MK_COMB (@lem237271) (@lem237222 m p n h1)). Qed.
Lemma lem237321 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem237322 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term264 n m p) = (term292 n m p).
Proof. exact (MK_COMB (@lem237272 m p n h1) (@lem237321 m p)). Qed.
Lemma lem237371 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term267 n m p) = (term293 n m p).
Proof. exact (MK_COMB (@lem237067 m p n h1) (@lem237322 m p n h1)). Qed.
Lemma lem237520 (m : nat) (p : nat) (n : nat) (h1 : term0 p n) : (term293 n m p) = (term267 n m p).
Proof. exact (SYM (@lem237371 m p n h1)). Qed.
Lemma lem237530 : term294.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem237531 : term295.
Proof. exact (proj2 (@lem237530)). Qed.
Lemma lem237552 : term296.
Proof. exact (proj1 (@lem237531)). Qed.
Lemma lem237553 (n : nat) : term297 n.
Proof. exact (@lem237552 n). Qed.
Lemma lem237554 (n : nat) : (term297 n) = ((term298 n) = n).
Proof. exact (eq_refl (term297 n)). Qed.
Lemma lem237564 : term198.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem237580 : term199.
Proof. exact (proj1 (@lem237564)). Qed.
Lemma lem237581 (m : nat) : term200 m.
Proof. exact (@lem237580 m). Qed.
Lemma lem237582 (m : nat) : (term200 m) = ((term201 m) = m).
Proof. exact (eq_refl (term200 m)). Qed.
Lemma lem237588 (n : nat) : term299 n.
Proof. exact (@lem87885 n). Qed.
Lemma lem237589 (n : nat) : (term299 n) = ((term300 n) = term30).
Proof. exact (eq_refl (term299 n)). Qed.
Lemma lem237611 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237612 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem237613 (m : nat) (h1 : m = term30) : (Nat.pow m) = term301.
Proof. exact (MK_COMB (@lem237612) (@lem237611 m h1)). Qed.
Lemma lem237614 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem237615 (n : nat) (m : nat) (h1 : m = term30) : (Nat.pow m n) = (term300 n).
Proof. exact (MK_COMB (@lem237613 m h1) (@lem237614 n)). Qed.
Lemma lem237617 (n : nat) : (term300 n) = term30.
Proof. exact (EQ_MP (@lem237589 n) (@lem237588 n)). Qed.
Lemma lem237618 (n : nat) (m : nat) (h1 : m = term30) : (Nat.pow m n) = term30.
Proof. exact (TRANS (@lem237615 n m h1) (@lem237617 n)). Qed.
Lemma lem237619 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem237620 (n : nat) (m : nat) (h1 : m = term30) : (term260 m n) = term302.
Proof. exact (MK_COMB (@lem237619) (@lem237618 n m h1)). Qed.
Lemma lem237626 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237627 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem237628 (m : nat) (h1 : m = term30) : (@eq nat m) = term302.
Proof. exact (MK_COMB (@lem237627) (@lem237626 m h1)). Qed.
Lemma lem237629 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem237630 (m : nat) (h1 : m = term30) : (m = term30) = (term30 = term30).
Proof. exact (MK_COMB (@lem237628 m h1) (@lem237629)). Qed.
Lemma lem237632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem237633 (x : nat) : (x = x) = True.
Proof. exact (@lem237632 nat x). Qed.
Lemma lem237634 : (term30 = term30) = True.
Proof. exact (@lem237633 term30). Qed.
Lemma lem237635 (m : nat) (h1 : m = term30) : (m = term30) = True.
Proof. exact (TRANS (@lem237630 m h1) (@lem237634)). Qed.
Lemma lem237636 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem237637 (m : nat) (h1 : m = term30) : (term167 m) = (@COND nat True).
Proof. exact (MK_COMB (@lem237636) (@lem237635 m h1)). Qed.
Lemma lem237638 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem237639 (m : nat) (h1 : m = term30) : (term169 m) = term303.
Proof. exact (MK_COMB (@lem237637 m h1) (@lem237638)). Qed.
Lemma lem237640 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237641 (m : nat) (h1 : m = term30) : (term171 m) = term304.
Proof. exact (MK_COMB (@lem237639 m h1) (@lem237640)). Qed.
Lemma lem237643 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem237644 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem237643 nat t2 t1). Qed.
Lemma lem237645 : term304 = term30.
Proof. exact (@lem237644 (NUMERAL 0) term30). Qed.
Lemma lem237646 (m : nat) (h1 : m = term30) : (term171 m) = term30.
Proof. exact (TRANS (@lem237641 m h1) (@lem237645)). Qed.
Lemma lem237647 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem237648 (m : nat) (h1 : m = term30) : (term277 m) = term305.
Proof. exact (MK_COMB (@lem237647) (@lem237646 m h1)). Qed.
Lemma lem237650 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237651 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem237652 (m : nat) (h1 : m = term30) : (Nat.pow m) = term301.
Proof. exact (MK_COMB (@lem237651) (@lem237650 m h1)). Qed.
Lemma lem237653 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem237654 (p : nat) (m : nat) (h1 : m = term30) : (Nat.pow m p) = (term300 p).
Proof. exact (MK_COMB (@lem237652 m h1) (@lem237653 p)). Qed.
Lemma lem237656 (n : nat) : (term300 n) = term30.
Proof. exact (EQ_MP (@lem237589 n) (@lem237588 n)). Qed.
Lemma lem237657 (p : nat) : (term300 p) = term30.
Proof. exact (@lem237656 p). Qed.
Lemma lem237658 (p : nat) (m : nat) (h1 : m = term30) : (Nat.pow m p) = term30.
Proof. exact (TRANS (@lem237654 p m h1) (@lem237657 p)). Qed.
Lemma lem237659 (p : nat) (m : nat) (h1 : m = term30) : (term278 m p) = term306.
Proof. exact (MK_COMB (@lem237648 m h1) (@lem237658 p m h1)). Qed.
Lemma lem237661 (n : nat) : (term298 n) = n.
Proof. exact (EQ_MP (@lem237554 n) (@lem237553 n)). Qed.
Lemma lem237662 : term306 = term30.
Proof. exact (@lem237661 term30). Qed.
Lemma lem237663 (p : nat) (m : nat) (h1 : m = term30) : (term278 m p) = term30.
Proof. exact (TRANS (@lem237659 p m h1) (@lem237662)). Qed.
Lemma lem237664 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem237665 (p : nat) (m : nat) (h1 : m = term30) : (term279 m p) = term307.
Proof. exact (MK_COMB (@lem237664) (@lem237663 p m h1)). Qed.
Lemma lem237671 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237672 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem237673 (m : nat) (h1 : m = term30) : (@eq nat m) = term302.
Proof. exact (MK_COMB (@lem237672) (@lem237671 m h1)). Qed.
Lemma lem237674 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem237675 (m : nat) (h1 : m = term30) : (m = term30) = (term30 = term30).
Proof. exact (MK_COMB (@lem237673 m h1) (@lem237674)). Qed.
Lemma lem237677 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem237678 (x : nat) : (x = x) = True.
Proof. exact (@lem237677 nat x). Qed.
Lemma lem237679 : (term30 = term30) = True.
Proof. exact (@lem237678 term30). Qed.
Lemma lem237680 (m : nat) (h1 : m = term30) : (m = term30) = True.
Proof. exact (TRANS (@lem237675 m h1) (@lem237679)). Qed.
Lemma lem237681 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem237682 (m : nat) (h1 : m = term30) : (term167 m) = (@COND nat True).
Proof. exact (MK_COMB (@lem237681) (@lem237680 m h1)). Qed.
Lemma lem237683 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237684 (m : nat) (h1 : m = term30) : (term308 m) = term309.
Proof. exact (MK_COMB (@lem237682 m h1) (@lem237683)). Qed.
Lemma lem237686 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237687 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem237688 (m : nat) (h1 : m = term30) : (Nat.pow m) = term301.
Proof. exact (MK_COMB (@lem237687) (@lem237686 m h1)). Qed.
Lemma lem237689 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem237690 (n : nat) (m : nat) (h1 : m = term30) : (Nat.pow m n) = (term300 n).
Proof. exact (MK_COMB (@lem237688 m h1) (@lem237689 n)). Qed.
Lemma lem237692 (n : nat) : (term300 n) = term30.
Proof. exact (EQ_MP (@lem237589 n) (@lem237588 n)). Qed.
Lemma lem237693 (n : nat) (m : nat) (h1 : m = term30) : (Nat.pow m n) = term30.
Proof. exact (TRANS (@lem237690 n m h1) (@lem237692 n)). Qed.
Lemma lem237694 (n : nat) (m : nat) (h1 : m = term30) : (term288 m n) = term310.
Proof. exact (MK_COMB (@lem237684 m h1) (@lem237693 n m h1)). Qed.
Lemma lem237696 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem237697 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem237696 nat t2 t1). Qed.
Lemma lem237698 : term310 = (NUMERAL 0).
Proof. exact (@lem237697 term30 (NUMERAL 0)). Qed.
Lemma lem237699 (n : nat) (m : nat) (h1 : m = term30) : (term288 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem237694 n m h1) (@lem237698)). Qed.
Lemma lem237700 (p : nat) (n : nat) (m : nat) (h1 : m = term30) : (term289 p m n) = term311.
Proof. exact (MK_COMB (@lem237665 p m h1) (@lem237699 n m h1)). Qed.
Lemma lem237702 (m : nat) : (term201 m) = m.
Proof. exact (EQ_MP (@lem237582 m) (@lem237581 m)). Qed.
Lemma lem237703 : term311 = term30.
Proof. exact (@lem237702 term30). Qed.
Lemma lem237704 (p : nat) (n : nat) (m : nat) (h1 : m = term30) : (term289 p m n) = term30.
Proof. exact (TRANS (@lem237700 p n m h1) (@lem237703)). Qed.
Lemma lem237705 (p : nat) (n : nat) (m : nat) (h1 : m = term30) : ((Nat.pow m n) = (term289 p m n)) = (term30 = term30).
Proof. exact (MK_COMB (@lem237620 n m h1) (@lem237704 p n m h1)). Qed.
Lemma lem237707 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem237708 (x : nat) : (x = x) = True.
Proof. exact (@lem237707 nat x). Qed.
Lemma lem237709 : (term30 = term30) = True.
Proof. exact (@lem237708 term30). Qed.
Lemma lem237710 (p : nat) (n : nat) (m : nat) (h1 : m = term30) : ((Nat.pow m n) = (term289 p m n)) = True.
Proof. exact (TRANS (@lem237705 p n m h1) (@lem237709)). Qed.
Lemma lem237711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem237712 (p : nat) (n : nat) (m : nat) (h1 : m = term30) : (term290 p m n) = (and True).
Proof. exact (MK_COMB (@lem237711) (@lem237710 p n m h1)). Qed.
Lemma lem237718 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237719 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem237720 (m : nat) (h1 : m = term30) : (@eq nat m) = term302.
Proof. exact (MK_COMB (@lem237719) (@lem237718 m h1)). Qed.
Lemma lem237721 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem237722 (m : nat) (h1 : m = term30) : (m = term30) = (term30 = term30).
Proof. exact (MK_COMB (@lem237720 m h1) (@lem237721)). Qed.
Lemma lem237724 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem237725 (x : nat) : (x = x) = True.
Proof. exact (@lem237724 nat x). Qed.
Lemma lem237726 : (term30 = term30) = True.
Proof. exact (@lem237725 term30). Qed.
Lemma lem237727 (m : nat) (h1 : m = term30) : (m = term30) = True.
Proof. exact (TRANS (@lem237722 m h1) (@lem237726)). Qed.
Lemma lem237728 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem237729 (m : nat) (h1 : m = term30) : (term167 m) = (@COND nat True).
Proof. exact (MK_COMB (@lem237728) (@lem237727 m h1)). Qed.
Lemma lem237730 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237731 (m : nat) (h1 : m = term30) : (term308 m) = term309.
Proof. exact (MK_COMB (@lem237729 m h1) (@lem237730)). Qed.
Lemma lem237733 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237734 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem237735 (m : nat) (h1 : m = term30) : (Nat.pow m) = term301.
Proof. exact (MK_COMB (@lem237734) (@lem237733 m h1)). Qed.
Lemma lem237736 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem237737 (n : nat) (m : nat) (h1 : m = term30) : (Nat.pow m n) = (term300 n).
Proof. exact (MK_COMB (@lem237735 m h1) (@lem237736 n)). Qed.
Lemma lem237739 (n : nat) : (term300 n) = term30.
Proof. exact (EQ_MP (@lem237589 n) (@lem237588 n)). Qed.
Lemma lem237740 (n : nat) (m : nat) (h1 : m = term30) : (Nat.pow m n) = term30.
Proof. exact (TRANS (@lem237737 n m h1) (@lem237739 n)). Qed.
Lemma lem237741 (n : nat) (m : nat) (h1 : m = term30) : (term288 m n) = term310.
Proof. exact (MK_COMB (@lem237731 m h1) (@lem237740 n m h1)). Qed.
Lemma lem237743 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem237744 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem237743 nat t2 t1). Qed.
Lemma lem237745 : term310 = (NUMERAL 0).
Proof. exact (@lem237744 term30 (NUMERAL 0)). Qed.
Lemma lem237746 (n : nat) (m : nat) (h1 : m = term30) : (term288 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem237741 n m h1) (@lem237745)). Qed.
Lemma lem237747 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem237748 (n : nat) (m : nat) (h1 : m = term30) : (term291 m n) = term263.
Proof. exact (MK_COMB (@lem237747) (@lem237746 n m h1)). Qed.
Lemma lem237750 (m : nat) (h1 : m = term30) : m = term30.
Proof. exact (h1). Qed.
Lemma lem237751 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem237752 (m : nat) (h1 : m = term30) : (Nat.pow m) = term301.
Proof. exact (MK_COMB (@lem237751) (@lem237750 m h1)). Qed.
Lemma lem237753 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem237754 (p : nat) (m : nat) (h1 : m = term30) : (Nat.pow m p) = (term300 p).
Proof. exact (MK_COMB (@lem237752 m h1) (@lem237753 p)). Qed.
Lemma lem237756 (n : nat) : (term300 n) = term30.
Proof. exact (EQ_MP (@lem237589 n) (@lem237588 n)). Qed.
Lemma lem237757 (p : nat) : (term300 p) = term30.
Proof. exact (@lem237756 p). Qed.
Lemma lem237758 (p : nat) (m : nat) (h1 : m = term30) : (Nat.pow m p) = term30.
Proof. exact (TRANS (@lem237754 p m h1) (@lem237757 p)). Qed.
Lemma lem237759 (n : nat) (p : nat) (m : nat) (h1 : m = term30) : (term292 n m p) = term312.
Proof. exact (MK_COMB (@lem237748 n m h1) (@lem237758 p m h1)). Qed.
Lemma lem237760 (n : nat) (p : nat) (m : nat) (h1 : m = term30) : (term293 n m p) = term313.
Proof. exact (MK_COMB (@lem237712 p n m h1) (@lem237759 n p m h1)). Qed.
Lemma lem237762 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem237763 : term313 = term312.
Proof. exact (@lem237762 term312). Qed.
Lemma lem237764 (n : nat) (p : nat) (m : nat) (h1 : m = term30) : (term293 n m p) = term312.
Proof. exact (TRANS (@lem237760 n p m h1) (@lem237763)). Qed.
Lemma lem237765 (n : nat) (p : nat) (m : nat) (h1 : m = term30) : term312 = (term293 n m p).
Proof. exact (SYM (@lem237764 n p m h1)). Qed.
Lemma lem237766 (x : nat) : term314 x.
Proof. exact (@lem148575 x). Qed.
Lemma lem237767 (x : nat) : (term314 x) = (term315 x).
Proof. exact (eq_refl (term314 x)). Qed.
Lemma lem237768 (x : nat) : term315 x.
Proof. exact (EQ_MP (@lem237767 x) (@lem237766 x)). Qed.
Lemma lem237769 (x : nat) (m : nat) : term316 x m.
Proof. exact (@lem237768 x m). Qed.
Lemma lem237770 (x : nat) (m : nat) : (term316 x m) = (term317 x m).
Proof. exact (eq_refl (term316 x m)). Qed.
Lemma lem237771 (x : nat) (m : nat) : term317 x m.
Proof. exact (EQ_MP (@lem237770 x m) (@lem237769 x m)). Qed.
Lemma lem237772 (x : nat) (m : nat) (n : nat) : term318 x m n.
Proof. exact (@lem237771 x m n). Qed.
Lemma lem237773 (x : nat) (m : nat) (n : nat) : (term318 x m n) = ((term319 m x n) = (term320 x m n)).
Proof. exact (eq_refl (term318 x m n)). Qed.
Lemma lem237805 : term321.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem237806 (n : nat) : term322 n.
Proof. exact (@lem237805 n). Qed.
Lemma lem237807 (n : nat) : (term322 n) = ((term323 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term322 n)). Qed.
Lemma lem237829 : term324.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem237830 (n : nat) : term325 n.
Proof. exact (@lem237829 n). Qed.
Lemma lem237831 (n : nat) : (term325 n) = ((term326 n) = n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem237836 (m : nat) : term192 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem237851 (m : nat) : term327 m.
Proof. exact (@lem82 (m = term30)). Qed.
Lemma lem237871 (m : nat) (h1 : term32 m) : (m = term30) = False.
Proof. exact (@lem237851 m (@lem235619 m h1)). Qed.
Lemma lem237872 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem237873 (m : nat) (h1 : term32 m) : (term167 m) = (@COND nat False).
Proof. exact (MK_COMB (@lem237872) (@lem237871 m h1)). Qed.
Lemma lem237874 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem237875 (m : nat) (h1 : term32 m) : (term169 m) = term328.
Proof. exact (MK_COMB (@lem237873 m h1) (@lem237874)). Qed.
Lemma lem237876 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237877 (m : nat) (h1 : term32 m) : (term171 m) = term329.
Proof. exact (MK_COMB (@lem237875 m h1) (@lem237876)). Qed.
Lemma lem237879 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem237880 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem237879 nat t1 t2). Qed.
Lemma lem237881 : term329 = (NUMERAL 0).
Proof. exact (@lem237880 term30 (NUMERAL 0)). Qed.
Lemma lem237882 (m : nat) (h1 : term32 m) : (term171 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem237877 m h1) (@lem237881)). Qed.
Lemma lem237883 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem237884 (m : nat) (h1 : term32 m) : (term277 m) = term330.
Proof. exact (MK_COMB (@lem237883) (@lem237882 m h1)). Qed.
Lemma lem237885 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem237886 (p : nat) (m : nat) (h1 : term32 m) : (term278 m p) = (term331 m p).
Proof. exact (MK_COMB (@lem237884 m h1) (@lem237885 m p)). Qed.
Lemma lem237888 (n : nat) : (term323 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem237807 n) (@lem237806 n)). Qed.
Lemma lem237889 (m : nat) (p : nat) : (term331 m p) = (NUMERAL 0).
Proof. exact (@lem237888 (Nat.pow m p)). Qed.
Lemma lem237890 (p : nat) (m : nat) (h1 : term32 m) : (term278 m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem237886 p m h1) (@lem237889 m p)). Qed.
Lemma lem237891 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem237892 (p : nat) (m : nat) (h1 : term32 m) : (term279 m p) = term332.
Proof. exact (MK_COMB (@lem237891) (@lem237890 p m h1)). Qed.
Lemma lem237896 (m : nat) (h1 : term32 m) : (m = term30) = False.
Proof. exact (@lem237851 m (@lem235619 m h1)). Qed.
Lemma lem237897 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem237898 (m : nat) (h1 : term32 m) : (term167 m) = (@COND nat False).
Proof. exact (MK_COMB (@lem237897) (@lem237896 m h1)). Qed.
Lemma lem237899 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237900 (m : nat) (h1 : term32 m) : (term308 m) = term333.
Proof. exact (MK_COMB (@lem237898 m h1) (@lem237899)). Qed.
Lemma lem237901 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem237902 (n : nat) (m : nat) (h1 : term32 m) : (term288 m n) = (term334 m n).
Proof. exact (MK_COMB (@lem237900 m h1) (@lem237901 m n)). Qed.
Lemma lem237904 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem237905 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem237904 nat t1 t2). Qed.
Lemma lem237906 (m : nat) (n : nat) : (term334 m n) = (Nat.pow m n).
Proof. exact (@lem237905 (NUMERAL 0) (Nat.pow m n)). Qed.
Lemma lem237907 (n : nat) (m : nat) (h1 : term32 m) : (term288 m n) = (Nat.pow m n).
Proof. exact (TRANS (@lem237902 n m h1) (@lem237906 m n)). Qed.
Lemma lem237908 (p : nat) (n : nat) (m : nat) (h1 : term32 m) : (term289 p m n) = (term335 m n).
Proof. exact (MK_COMB (@lem237892 p m h1) (@lem237907 n m h1)). Qed.
Lemma lem237910 (n : nat) : (term326 n) = n.
Proof. exact (EQ_MP (@lem237831 n) (@lem237830 n)). Qed.
Lemma lem237911 (m : nat) (n : nat) : (term335 m n) = (Nat.pow m n).
Proof. exact (@lem237910 (Nat.pow m n)). Qed.
Lemma lem237912 (p : nat) (n : nat) (m : nat) (h1 : term32 m) : (term289 p m n) = (Nat.pow m n).
Proof. exact (TRANS (@lem237908 p n m h1) (@lem237911 m n)). Qed.
Lemma lem237913 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem237914 (p : nat) (n : nat) (m : nat) (h1 : term32 m) : ((Nat.pow m n) = (term289 p m n)) = ((Nat.pow m n) = (Nat.pow m n)).
Proof. exact (MK_COMB (@lem237913 m n) (@lem237912 p n m h1)). Qed.
Lemma lem237916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem237917 (x : nat) : (x = x) = True.
Proof. exact (@lem237916 nat x). Qed.
Lemma lem237918 (m : nat) (n : nat) : ((Nat.pow m n) = (Nat.pow m n)) = True.
Proof. exact (@lem237917 (Nat.pow m n)). Qed.
Lemma lem237919 (p : nat) (n : nat) (m : nat) (h1 : term32 m) : ((Nat.pow m n) = (term289 p m n)) = True.
Proof. exact (TRANS (@lem237914 p n m h1) (@lem237918 m n)). Qed.
Lemma lem237920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem237921 (p : nat) (n : nat) (m : nat) (h1 : term32 m) : (term290 p m n) = (and True).
Proof. exact (MK_COMB (@lem237920) (@lem237919 p n m h1)). Qed.
Lemma lem237925 (m : nat) (h1 : term32 m) : (m = term30) = False.
Proof. exact (@lem237851 m (@lem235619 m h1)). Qed.
Lemma lem237926 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem237927 (m : nat) (h1 : term32 m) : (term167 m) = (@COND nat False).
Proof. exact (MK_COMB (@lem237926) (@lem237925 m h1)). Qed.
Lemma lem237928 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem237929 (m : nat) (h1 : term32 m) : (term308 m) = term333.
Proof. exact (MK_COMB (@lem237927 m h1) (@lem237928)). Qed.
Lemma lem237930 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem237931 (n : nat) (m : nat) (h1 : term32 m) : (term288 m n) = (term334 m n).
Proof. exact (MK_COMB (@lem237929 m h1) (@lem237930 m n)). Qed.
Lemma lem237933 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem237934 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem237933 nat t1 t2). Qed.
Lemma lem237935 (m : nat) (n : nat) : (term334 m n) = (Nat.pow m n).
Proof. exact (@lem237934 (NUMERAL 0) (Nat.pow m n)). Qed.
Lemma lem237936 (n : nat) (m : nat) (h1 : term32 m) : (term288 m n) = (Nat.pow m n).
Proof. exact (TRANS (@lem237931 n m h1) (@lem237935 m n)). Qed.
Lemma lem237937 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem237938 (n : nat) (m : nat) (h1 : term32 m) : (term291 m n) = (term336 m n).
Proof. exact (MK_COMB (@lem237937) (@lem237936 n m h1)). Qed.
Lemma lem237939 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem237940 (n : nat) (p : nat) (m : nat) (h1 : term32 m) : (term292 n m p) = (term319 n m p).
Proof. exact (MK_COMB (@lem237938 n m h1) (@lem237939 m p)). Qed.
Lemma lem237942 (x : nat) (m : nat) (n : nat) : (term319 m x n) = (term320 x m n).
Proof. exact (EQ_MP (@lem237773 x m n) (@lem237772 x m n)). Qed.
Lemma lem237943 (m : nat) (n : nat) (p : nat) : (term319 n m p) = (term320 m n p).
Proof. exact (@lem237942 m n p). Qed.
Lemma lem237951 (m : nat) (h1 : term70 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem237836 m (@lem235684 m h1)). Qed.
Lemma lem237952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem237953 (m : nat) (h1 : term70 m) : (term337 m) = (and False).
Proof. exact (MK_COMB (@lem237952) (@lem237951 m h1)). Qed.
Lemma lem237960 (n : nat) (p : nat) : (term338 n p) = (term338 n p).
Proof. exact (eq_refl (term338 n p)). Qed.
Lemma lem237961 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term339 m n p) = (term340 n p).
Proof. exact (MK_COMB (@lem237953 m h1) (@lem237960 n p)). Qed.
Lemma lem237963 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem237964 (n : nat) (p : nat) : (term340 n p) = False.
Proof. exact (@lem237963 (term338 n p)). Qed.
Lemma lem237965 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term339 m n p) = False.
Proof. exact (TRANS (@lem237961 n p m h1) (@lem237964 n p)). Qed.
Lemma lem237966 (m : nat) (n : nat) (p : nat) : (term341 m n p) = (term341 m n p).
Proof. exact (eq_refl (term341 m n p)). Qed.
Lemma lem237967 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term320 m n p) = (term342 m n p).
Proof. exact (MK_COMB (@lem237966 m n p) (@lem237965 n p m h1)). Qed.
Lemma lem237969 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem237970 (m : nat) (n : nat) (p : nat) : (term342 m n p) = (term343 m n p).
Proof. exact (@lem237969 (term343 m n p)). Qed.
Lemma lem237973 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term320 m n p) = (term343 m n p).
Proof. exact (TRANS (@lem237967 n p m h1) (@lem237970 m n p)). Qed.
Lemma lem237974 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : (term319 n m p) = (term343 m n p).
Proof. exact (TRANS (@lem237943 m n p) (@lem237973 n p m h1)). Qed.
Lemma lem237975 (n : nat) (p : nat) (m : nat) (h1 : term70 m) (h2 : term32 m) : (term292 n m p) = (term343 m n p).
Proof. exact (TRANS (@lem237940 n p m h2) (@lem237974 n p m h1)). Qed.
Lemma lem237976 (n : nat) (p : nat) (m : nat) (h1 : term70 m) (h2 : term32 m) : (term293 n m p) = (term344 m n p).
Proof. exact (MK_COMB (@lem237921 p n m h2) (@lem237975 n p m h1 h2)). Qed.
Lemma lem237978 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem237979 (m : nat) (n : nat) (p : nat) : (term344 m n p) = (term343 m n p).
Proof. exact (@lem237978 (term343 m n p)). Qed.
Lemma lem237982 (n : nat) (p : nat) (m : nat) (h1 : term70 m) (h2 : term32 m) : (term293 n m p) = (term343 m n p).
Proof. exact (TRANS (@lem237976 n p m h1 h2) (@lem237979 m n p)). Qed.
Lemma lem237983 (n : nat) (p : nat) (m : nat) (h1 : term70 m) (h2 : term32 m) : (term343 m n p) = (term293 n m p).
Proof. exact (SYM (@lem237982 n p m h1 h2)). Qed.
Lemma lem237985 : term30 = term345.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem237986 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem237987 : term312 = term346.
Proof. exact (MK_COMB (@lem237986) (@lem237985)). Qed.
Lemma lem237989 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem235609 m n) (@lem235608 m n)). Qed.
Lemma lem237990 : term346 = term347.
Proof. exact (@lem237989 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem237994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem237995 (x : nat) : (x = x) = True.
Proof. exact (@lem237994 nat x). Qed.
Lemma lem237996 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem237995 (NUMERAL 0)). Qed.
Lemma lem237997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem237998 : term348 = (or True).
Proof. exact (MK_COMB (@lem237997) (@lem237996)). Qed.
Lemma lem238000 (m : nat) : (term28 m) = False.
Proof. exact (EQ_MP (@lem235613 m) (@lem235612 m)). Qed.
Lemma lem238001 : term349 = False.
Proof. exact (@lem238000 (NUMERAL 0)). Qed.
Lemma lem238002 : term347 = (True \/ False).
Proof. exact (MK_COMB (@lem237998) (@lem238001)). Qed.
Lemma lem238004 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem238005 : (True \/ False) = True.
Proof. exact (@lem238004 False). Qed.
Lemma lem238006 : term347 = True.
Proof. exact (TRANS (@lem238002) (@lem238005)). Qed.
Lemma lem238007 : term346 = True.
Proof. exact (TRANS (@lem237990) (@lem238006)). Qed.
Lemma lem238008 : term312 = True.
Proof. exact (TRANS (@lem237987) (@lem238007)). Qed.
Lemma lem238009 : True = term312.
Proof. exact (SYM (@lem238008)). Qed.
Lemma lem238010 : term312.
Proof. exact (EQ_MP (@lem238009) (@lem0)). Qed.
Lemma lem238014 (m : nat) (n : nat) : (Peano.le n m) = (term9 m n).
Proof. exact (EQ_MP (@lem235602 m n) (@lem235601 m n)). Qed.
Lemma lem238015 (m : nat) : (term350 m) = (term351 m).
Proof. exact (@lem238014 m term352). Qed.
Lemma lem238017 : term352 = term353.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem238019 : term30 = term345.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem238020 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem238021 : term353 = term354.
Proof. exact (MK_COMB (@lem238020) (@lem238019)). Qed.
Lemma lem238022 : term352 = term354.
Proof. exact (TRANS (@lem238017) (@lem238021)). Qed.
Lemma lem238023 (m : nat) : (Peano.lt m) = (Peano.lt m).
Proof. exact (eq_refl (Peano.lt m)). Qed.
Lemma lem238024 (m : nat) : (term355 m) = (term356 m).
Proof. exact (MK_COMB (@lem238023 m) (@lem238022)). Qed.
Lemma lem238026 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem235609 m n) (@lem235608 m n)). Qed.
Lemma lem238027 (m : nat) : (term356 m) = (term357 m).
Proof. exact (@lem238026 m term345). Qed.
Lemma lem238033 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem235609 m n) (@lem235608 m n)). Qed.
Lemma lem238034 (m : nat) : (term358 m) = (term359 m).
Proof. exact (@lem238033 m (NUMERAL 0)). Qed.
Lemma lem238040 (m : nat) : (term28 m) = False.
Proof. exact (EQ_MP (@lem235613 m) (@lem235612 m)). Qed.
Lemma lem238041 (m : nat) : (term360 m) = (term360 m).
Proof. exact (eq_refl (term360 m)). Qed.
Lemma lem238042 (m : nat) : (term359 m) = (term361 m).
Proof. exact (MK_COMB (@lem238041 m) (@lem238040 m)). Qed.
Lemma lem238044 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem238045 (m : nat) : (term361 m) = (m = (NUMERAL 0)).
Proof. exact (@lem238044 (m = (NUMERAL 0))). Qed.
Lemma lem238048 (m : nat) : (term359 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem238042 m) (@lem238045 m)). Qed.
Lemma lem238049 (m : nat) : (term358 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem238034 m) (@lem238048 m)). Qed.
Lemma lem238050 (m : nat) : (term362 m) = (term362 m).
Proof. exact (eq_refl (term362 m)). Qed.
Lemma lem238051 (m : nat) : (term357 m) = (term363 m).
Proof. exact (MK_COMB (@lem238050 m) (@lem238049 m)). Qed.
Lemma lem238054 (m : nat) : (term356 m) = (term363 m).
Proof. exact (TRANS (@lem238027 m) (@lem238051 m)). Qed.
Lemma lem238055 (m : nat) : (term355 m) = (term363 m).
Proof. exact (TRANS (@lem238024 m) (@lem238054 m)). Qed.
Lemma lem238056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238057 (m : nat) : (term351 m) = (term364 m).
Proof. exact (MK_COMB (@lem238056) (@lem238055 m)). Qed.
Lemma lem238058 (m : nat) : (term350 m) = (term364 m).
Proof. exact (TRANS (@lem238015 m) (@lem238057 m)). Qed.
Lemma lem238059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem238060 (m : nat) : (term365 m) = (term366 m).
Proof. exact (MK_COMB (@lem238059) (@lem238058 m)). Qed.
Lemma lem238061 (n : nat) (p : nat) : (Peano.lt n p) = (Peano.lt n p).
Proof. exact (eq_refl (Peano.lt n p)). Qed.
Lemma lem238062 (m : nat) (n : nat) (p : nat) : (term343 m n p) = (term367 m n p).
Proof. exact (MK_COMB (@lem238060 m) (@lem238061 n p)). Qed.
Lemma lem238065 (m : nat) (n : nat) (p : nat) : (term367 m n p) = (term343 m n p).
Proof. exact (SYM (@lem238062 m n p)). Qed.
Lemma lem238066 (m : nat) : term368 m.
Proof. exact (@lem235582 m). Qed.
Lemma lem238067 (m : nat) : (term368 m) = (term4 m).
Proof. exact (eq_refl (term368 m)). Qed.
Lemma lem238068 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem238067 m) (@lem238066 m)). Qed.
Lemma lem238069 (m : nat) (n : nat) : term369 m n.
Proof. exact (@lem238068 m n). Qed.
Lemma lem238070 (m : nat) (n : nat) : (term369 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term369 m n)). Qed.
Lemma lem238072 (m : nat) : term192 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem238085 (p : nat) (n : nat) : term268 p n.
Proof. exact (@lem82 (Peano.le p n)). Qed.
Lemma lem238087 (m : nat) : term327 m.
Proof. exact (@lem82 (m = term30)). Qed.
Lemma lem238107 : term345 = term30.
Proof. exact (SYM (@lem80361)). Qed.
Lemma lem238108 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem238109 (m : nat) : (m = term345) = (m = term30).
Proof. exact (MK_COMB (@lem238108 m) (@lem238107)). Qed.
Lemma lem238111 (m : nat) (h1 : term32 m) : (m = term30) = False.
Proof. exact (@lem238087 m (@lem235619 m h1)). Qed.
Lemma lem238112 (m : nat) (h1 : term32 m) : (m = term345) = False.
Proof. exact (TRANS (@lem238109 m) (@lem238111 m h1)). Qed.
Lemma lem238113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem238114 (m : nat) (h1 : term32 m) : (term362 m) = (or False).
Proof. exact (MK_COMB (@lem238113) (@lem238112 m h1)). Qed.
Lemma lem238116 (m : nat) (h1 : term70 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem238072 m (@lem235684 m h1)). Qed.
Lemma lem238117 (m : nat) (h1 : term70 m) (h2 : term32 m) : (term363 m) = (False \/ False).
Proof. exact (MK_COMB (@lem238114 m h2) (@lem238116 m h1)). Qed.
Lemma lem238119 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem238120 : (False \/ False) = False.
Proof. exact (@lem238119 False). Qed.
Lemma lem238121 (m : nat) (h1 : term70 m) (h2 : term32 m) : (term363 m) = False.
Proof. exact (TRANS (@lem238117 m h1 h2) (@lem238120)). Qed.
Lemma lem238122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238123 (m : nat) (h1 : term70 m) (h2 : term32 m) : (term364 m) = (~ False).
Proof. exact (MK_COMB (@lem238122) (@lem238121 m h1 h2)). Qed.
Lemma lem238125 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem238126 (m : nat) (h1 : term70 m) (h2 : term32 m) : (term364 m) = True.
Proof. exact (TRANS (@lem238123 m h1 h2) (@lem238125)). Qed.
Lemma lem238127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem238128 (m : nat) (h1 : term70 m) (h2 : term32 m) : (term366 m) = (and True).
Proof. exact (MK_COMB (@lem238127) (@lem238126 m h1 h2)). Qed.
Lemma lem238130 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem238070 m n) (@lem238069 m n)). Qed.
Lemma lem238131 (p : nat) (n : nat) : (Peano.lt n p) = (term0 p n).
Proof. exact (@lem238130 p n). Qed.
Lemma lem238133 (p : nat) (n : nat) (h1 : term0 p n) : (Peano.le p n) = False.
Proof. exact (@lem238085 p n (@lem235642 p n h1)). Qed.
Lemma lem238134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238135 (p : nat) (n : nat) (h1 : term0 p n) : (term0 p n) = (~ False).
Proof. exact (MK_COMB (@lem238134) (@lem238133 p n h1)). Qed.
Lemma lem238137 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem238138 (p : nat) (n : nat) (h1 : term0 p n) : (term0 p n) = True.
Proof. exact (TRANS (@lem238135 p n h1) (@lem238137)). Qed.
Lemma lem238139 (p : nat) (n : nat) (h1 : term0 p n) : (Peano.lt n p) = True.
Proof. exact (TRANS (@lem238131 p n) (@lem238138 p n h1)). Qed.
Lemma lem238140 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) (h3 : term32 m) : (term367 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem238128 m h2 h3) (@lem238139 p n h1)). Qed.
Lemma lem238142 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem238143 : (True /\ True) = True.
Proof. exact (@lem238142 True). Qed.
Lemma lem238144 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) (h3 : term32 m) : (term367 m n p) = True.
Proof. exact (TRANS (@lem238140 p n m h1 h2 h3) (@lem238143)). Qed.
Lemma lem238145 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) (h3 : term32 m) : True = (term367 m n p).
Proof. exact (SYM (@lem238144 p n m h1 h2 h3)). Qed.
Lemma lem238146 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) (h3 : term32 m) : term367 m n p.
Proof. exact (EQ_MP (@lem238145 p n m h1 h2 h3) (@lem0)). Qed.
Lemma lem238147 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) (h3 : term32 m) : term343 m n p.
Proof. exact (EQ_MP (@lem238065 m n p) (@lem238146 p n m h1 h2 h3)). Qed.
Lemma lem238148 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) (h3 : term32 m) : term293 n m p.
Proof. exact (EQ_MP (@lem237983 n p m h2 h3) (@lem238147 p n m h1 h2 h3)). Qed.
Lemma lem238149 (n : nat) (p : nat) (m : nat) (h1 : m = term30) : term293 n m p.
Proof. exact (EQ_MP (@lem237765 n p m h1) (@lem238010)). Qed.
Lemma lem238150 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) : term293 n m p.
Proof. exact (or_elim (@lem235617 m) (fun h0 : m = term30 => @lem238149 n p m h0) (fun h0 : term32 m => @lem238148 p n m h1 h2 h0)). Qed.
Lemma lem238151 (p : nat) (n : nat) (m : nat) (h1 : term0 p n) (h2 : term70 m) : term267 n m p.
Proof. exact (EQ_MP (@lem237520 m p n h1) (@lem238150 p n m h1 h2)). Qed.
Lemma lem238152 (n : nat) (p : nat) (m : nat) (h1 : term70 m) : term267 n m p.
Proof. exact (or_elim (@lem235640 p n) (fun h0 : Peano.le p n => @lem236405 m p n h1 h0) (fun h0 : term0 p n => @lem238151 p n m h0 h1)). Qed.
Lemma lem238153 (p : nat) (n : nat) (m : nat) (h1 : term70 m) : term196 p m n.
Proof. exact (@lem236069 p m n (@lem238152 n p m h1)). Qed.
Lemma lem238154 (p : nat) (n : nat) (m : nat) (h1 : term70 m) : term144 p m n.
Proof. exact (EQ_MP (@lem236066 p n m h1) (@lem238153 p n m h1)). Qed.
Lemma lem238155 (p : nat) (m : nat) (n : nat) : term144 p m n.
Proof. exact (or_elim (@lem235682 m) (fun h0 : m = (NUMERAL 0) => @lem235987 p n m h0) (fun h0 : term70 m => @lem238154 p n m h0)). Qed.
Lemma lem238160 (m : nat) (n : nat) : term147 m n.
Proof. exact (fun p : nat => @lem238155 p m n). Qed.
Lemma lem238165 (m : nat) : term149 m.
Proof. exact (fun n : nat => @lem238160 m n). Qed.
Lemma lem238170 : term151.
Proof. exact (fun m : nat => @lem238165 m). Qed.
Lemma lem238171 : term94.
Proof. exact (EQ_MP (@lem235822) (@lem238170)). Qed.
