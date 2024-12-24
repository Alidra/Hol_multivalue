Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_CLAUSES_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm89498_spec.
Lemma lem4621520 : term0.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem4621521 (m : nat) : term1 m.
Proof. exact (@lem4621520 m). Qed.
Lemma lem4621522 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem4621523 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem4621522 m) (@lem4621521 m)). Qed.
Lemma lem4621524 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem4621523 m n). Qed.
Lemma lem4621525 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem4621527 : term6.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem4621528 (m : nat) : term7 m.
Proof. exact (@lem4621527 m). Qed.
Lemma lem4621529 (m : nat) : (term7 m) = ((term8 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem4621540 (m : nat) : (term8 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem4621529 m) (@lem4621528 m)). Qed.
Lemma lem4621541 (i : nat) : (term8 i) = (i = (NUMERAL 0)).
Proof. exact (@lem4621540 i). Qed.
Lemma lem4621544 (GEN_PVAR_185 : nat) : (@SETSPEC nat GEN_PVAR_185) = (@SETSPEC nat GEN_PVAR_185).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_185)). Qed.
Lemma lem4621545 (GEN_PVAR_185 : nat) (i : nat) : (term9 GEN_PVAR_185 i) = (term10 GEN_PVAR_185 i).
Proof. exact (MK_COMB (@lem4621544 GEN_PVAR_185) (@lem4621541 i)). Qed.
Lemma lem4621546 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4621547 (GEN_PVAR_185 : nat) (i : nat) : (term11 GEN_PVAR_185 i) = (term12 GEN_PVAR_185 i).
Proof. exact (MK_COMB (@lem4621545 GEN_PVAR_185 i) (@lem4621546 i)). Qed.
Lemma lem4621548 (GEN_PVAR_185 : nat) : (term13 GEN_PVAR_185) = (term14 GEN_PVAR_185).
Proof. exact (fun_ext (fun i : nat => @lem4621547 GEN_PVAR_185 i)). Qed.
Lemma lem4621549 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621550 (GEN_PVAR_185 : nat) : (term15 GEN_PVAR_185) = (term16 GEN_PVAR_185).
Proof. exact (MK_COMB (@lem4621549) (@lem4621548 GEN_PVAR_185)). Qed.
Lemma lem4621555 : term17 = term18.
Proof. exact (fun_ext (fun GEN_PVAR_185 : nat => @lem4621550 GEN_PVAR_185)). Qed.
Lemma lem4621556 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621557 : term19 = term20.
Proof. exact (MK_COMB (@lem4621556) (@lem4621555)). Qed.
Lemma lem4621558 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem4621559 : term21 = term22.
Proof. exact (MK_COMB (@lem4621558) (@lem4621557)). Qed.
Lemma lem4621560 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem4621561 : (term19 = term23) = (term20 = term23).
Proof. exact (MK_COMB (@lem4621559) (@lem4621560)). Qed.
Lemma lem4621564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4621565 : term24 = term25.
Proof. exact (MK_COMB (@lem4621564) (@lem4621561)). Qed.
Lemma lem4621577 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem4621525 m n) (@lem4621524 m n)). Qed.
Lemma lem4621578 (i : nat) (k : nat) : (term4 i k) = (term5 i k).
Proof. exact (@lem4621577 i k). Qed.
Lemma lem4621583 (GEN_PVAR_186 : nat) : (@SETSPEC nat GEN_PVAR_186) = (@SETSPEC nat GEN_PVAR_186).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_186)). Qed.
Lemma lem4621584 (GEN_PVAR_186 : nat) (i : nat) (k : nat) : (term26 GEN_PVAR_186 i k) = (term27 GEN_PVAR_186 i k).
Proof. exact (MK_COMB (@lem4621583 GEN_PVAR_186) (@lem4621578 i k)). Qed.
Lemma lem4621585 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4621586 (GEN_PVAR_186 : nat) (k : nat) (i : nat) : (term28 GEN_PVAR_186 k i) = (term29 GEN_PVAR_186 k i).
Proof. exact (MK_COMB (@lem4621584 GEN_PVAR_186 i k) (@lem4621585 i)). Qed.
Lemma lem4621587 (GEN_PVAR_186 : nat) (k : nat) : (term30 GEN_PVAR_186 k) = (term31 GEN_PVAR_186 k).
Proof. exact (fun_ext (fun i : nat => @lem4621586 GEN_PVAR_186 k i)). Qed.
Lemma lem4621588 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621589 (GEN_PVAR_186 : nat) (k : nat) : (term32 GEN_PVAR_186 k) = (term33 GEN_PVAR_186 k).
Proof. exact (MK_COMB (@lem4621588) (@lem4621587 GEN_PVAR_186 k)). Qed.
Lemma lem4621594 (k : nat) : (term34 k) = (term35 k).
Proof. exact (fun_ext (fun GEN_PVAR_186 : nat => @lem4621589 GEN_PVAR_186 k)). Qed.
Lemma lem4621595 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621596 (k : nat) : (term36 k) = (term37 k).
Proof. exact (MK_COMB (@lem4621595) (@lem4621594 k)). Qed.
Lemma lem4621597 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem4621598 (k : nat) : (term38 k) = (term39 k).
Proof. exact (MK_COMB (@lem4621597) (@lem4621596 k)). Qed.
Lemma lem4621603 (k : nat) : (term40 k) = (term40 k).
Proof. exact (eq_refl (term40 k)). Qed.
Lemma lem4621604 (k : nat) : ((term36 k) = (term40 k)) = ((term37 k) = (term40 k)).
Proof. exact (MK_COMB (@lem4621598 k) (@lem4621603 k)). Qed.
Lemma lem4621607 : term41 = term42.
Proof. exact (fun_ext (fun k : nat => @lem4621604 k)). Qed.
Lemma lem4621608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621609 : term43 = term44.
Proof. exact (MK_COMB (@lem4621608) (@lem4621607)). Qed.
Lemma lem4621614 : term45 = term46.
Proof. exact (MK_COMB (@lem4621565) (@lem4621609)). Qed.
Lemma lem4621617 : term46 = term45.
Proof. exact (SYM (@lem4621614)). Qed.
Lemma lem4621623 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term47 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4621624 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term48 s t).
Proof. exact (@lem4621623 nat s t). Qed.
Lemma lem4621625 : (term20 = term23) = term49.
Proof. exact (@lem4621624 term20 term23). Qed.
Lemma lem4621642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4621643 : term25 = term50.
Proof. exact (MK_COMB (@lem4621642) (@lem4621625)). Qed.
Lemma lem4621651 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term47 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4621652 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term48 s t).
Proof. exact (@lem4621651 nat s t). Qed.
Lemma lem4621653 (k : nat) : ((term37 k) = (term40 k)) = (term51 k).
Proof. exact (@lem4621652 (term37 k) (term40 k)). Qed.
Lemma lem4621676 : term42 = term52.
Proof. exact (fun_ext (fun k : nat => @lem4621653 k)). Qed.
Lemma lem4621677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621678 : term44 = term53.
Proof. exact (MK_COMB (@lem4621677) (@lem4621676)). Qed.
Lemma lem4621683 : term46 = term54.
Proof. exact (MK_COMB (@lem4621643) (@lem4621678)). Qed.
Lemma lem4621686 : term54 = term46.
Proof. exact (SYM (@lem4621683)). Qed.
Lemma lem4621696 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term55 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4621697 (p : nat -> Prop) (x : nat) : (term56 x p) = (p x).
Proof. exact (@lem4621696 nat p x). Qed.
Lemma lem4621698 (x : nat) : (term57 x) = (term58 x).
Proof. exact (@lem4621697 term59 x). Qed.
Lemma lem4621699 (i : nat) : (term58 i) = (i = (NUMERAL 0)).
Proof. exact (eq_refl (term58 i)). Qed.
Lemma lem4621700 (GEN_PVAR_185 : nat) : (@SETSPEC nat GEN_PVAR_185) = (@SETSPEC nat GEN_PVAR_185).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_185)). Qed.
Lemma lem4621701 (GEN_PVAR_185 : nat) (i : nat) : (term60 GEN_PVAR_185 i) = (term10 GEN_PVAR_185 i).
Proof. exact (MK_COMB (@lem4621700 GEN_PVAR_185) (@lem4621699 i)). Qed.
Lemma lem4621702 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4621703 (GEN_PVAR_185 : nat) (i : nat) : (term61 GEN_PVAR_185 i) = (term12 GEN_PVAR_185 i).
Proof. exact (MK_COMB (@lem4621701 GEN_PVAR_185 i) (@lem4621702 i)). Qed.
Lemma lem4621704 (GEN_PVAR_185 : nat) : (term62 GEN_PVAR_185) = (term14 GEN_PVAR_185).
Proof. exact (fun_ext (fun i : nat => @lem4621703 GEN_PVAR_185 i)). Qed.
Lemma lem4621705 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621706 (GEN_PVAR_185 : nat) : (term63 GEN_PVAR_185) = (term16 GEN_PVAR_185).
Proof. exact (MK_COMB (@lem4621705) (@lem4621704 GEN_PVAR_185)). Qed.
Lemma lem4621707 : term64 = term18.
Proof. exact (fun_ext (fun GEN_PVAR_185 : nat => @lem4621706 GEN_PVAR_185)). Qed.
Lemma lem4621708 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621709 : term65 = term20.
Proof. exact (MK_COMB (@lem4621708) (@lem4621707)). Qed.
Lemma lem4621710 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4621711 (x : nat) : (term57 x) = (term66 x).
Proof. exact (MK_COMB (@lem4621710 x) (@lem4621709)). Qed.
Lemma lem4621712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4621713 (x : nat) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem4621712) (@lem4621711 x)). Qed.
Lemma lem4621714 (x : nat) : (term58 x) = (x = (NUMERAL 0)).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem4621715 (x : nat) : ((term57 x) = (term58 x)) = ((term66 x) = (x = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem4621713 x) (@lem4621714 x)). Qed.
Lemma lem4621716 (x : nat) : (term66 x) = (x = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem4621715 x) (@lem4621698 x)). Qed.
Lemma lem4621719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4621720 (x : nat) : (term68 x) = (term69 x).
Proof. exact (MK_COMB (@lem4621719) (@lem4621716 x)). Qed.
Lemma lem4621722 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term70 A x y s) = (term71 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4621723 (y : nat) (x : nat) (s : nat -> Prop) : (term72 x y s) = (term73 y x s).
Proof. exact (@lem4621722 nat y x s). Qed.
Lemma lem4621724 (x : nat) : (term74 x) = (term75 x).
Proof. exact (@lem4621723 (NUMERAL 0) x (@EMPTY nat)). Qed.
Lemma lem4621730 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4621731 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem4621730 nat x). Qed.
Lemma lem4621732 (x : nat) : (term76 x) = (term76 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem4621733 (x : nat) : (term75 x) = (term77 x).
Proof. exact (MK_COMB (@lem4621732 x) (@lem4621731 x)). Qed.
Lemma lem4621735 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4621736 (x : nat) : (term77 x) = (x = (NUMERAL 0)).
Proof. exact (@lem4621735 (x = (NUMERAL 0))). Qed.
Lemma lem4621739 (x : nat) : (term75 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem4621733 x) (@lem4621736 x)). Qed.
Lemma lem4621740 (x : nat) : (term74 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem4621724 x) (@lem4621739 x)). Qed.
Lemma lem4621741 (x : nat) : ((term66 x) = (term74 x)) = ((x = (NUMERAL 0)) = (x = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem4621720 x) (@lem4621740 x)). Qed.
Lemma lem4621743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4621744 (x : Prop) : (x = x) = True.
Proof. exact (@lem4621743 Prop x). Qed.
Lemma lem4621745 (x : nat) : ((x = (NUMERAL 0)) = (x = (NUMERAL 0))) = True.
Proof. exact (@lem4621744 (x = (NUMERAL 0))). Qed.
Lemma lem4621746 (x : nat) : ((term66 x) = (term74 x)) = True.
Proof. exact (TRANS (@lem4621741 x) (@lem4621745 x)). Qed.
Lemma lem4621747 : term78 = term79.
Proof. exact (fun_ext (fun x : nat => @lem4621746 x)). Qed.
Lemma lem4621748 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621749 : term49 = term80.
Proof. exact (MK_COMB (@lem4621748) (@lem4621747)). Qed.
Lemma lem4621751 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621752 (t : Prop) : (term82 t) = t.
Proof. exact (@lem4621751 nat t). Qed.
Lemma lem4621753 : term80 = True.
Proof. exact (@lem4621752 True). Qed.
Lemma lem4621754 : term49 = True.
Proof. exact (TRANS (@lem4621749) (@lem4621753)). Qed.
Lemma lem4621755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4621756 : term50 = (and True).
Proof. exact (MK_COMB (@lem4621755) (@lem4621754)). Qed.
Lemma lem4621768 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term55 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4621769 (p : nat -> Prop) (x : nat) : (term56 x p) = (p x).
Proof. exact (@lem4621768 nat p x). Qed.
Lemma lem4621770 (k : nat) (x : nat) : (term83 x k) = (term84 k x).
Proof. exact (@lem4621769 (term85 k) x). Qed.
Lemma lem4621771 (i : nat) (k : nat) : (term84 k i) = (term5 i k).
Proof. exact (eq_refl (term84 k i)). Qed.
Lemma lem4621772 (GEN_PVAR_186 : nat) : (@SETSPEC nat GEN_PVAR_186) = (@SETSPEC nat GEN_PVAR_186).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_186)). Qed.
Lemma lem4621773 (GEN_PVAR_186 : nat) (i : nat) (k : nat) : (term86 GEN_PVAR_186 k i) = (term27 GEN_PVAR_186 i k).
Proof. exact (MK_COMB (@lem4621772 GEN_PVAR_186) (@lem4621771 i k)). Qed.
Lemma lem4621774 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4621775 (GEN_PVAR_186 : nat) (k : nat) (i : nat) : (term87 GEN_PVAR_186 k i) = (term29 GEN_PVAR_186 k i).
Proof. exact (MK_COMB (@lem4621773 GEN_PVAR_186 i k) (@lem4621774 i)). Qed.
Lemma lem4621776 (GEN_PVAR_186 : nat) (k : nat) : (term88 GEN_PVAR_186 k) = (term31 GEN_PVAR_186 k).
Proof. exact (fun_ext (fun i : nat => @lem4621775 GEN_PVAR_186 k i)). Qed.
Lemma lem4621777 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621778 (GEN_PVAR_186 : nat) (k : nat) : (term89 GEN_PVAR_186 k) = (term33 GEN_PVAR_186 k).
Proof. exact (MK_COMB (@lem4621777) (@lem4621776 GEN_PVAR_186 k)). Qed.
Lemma lem4621779 (k : nat) : (term90 k) = (term35 k).
Proof. exact (fun_ext (fun GEN_PVAR_186 : nat => @lem4621778 GEN_PVAR_186 k)). Qed.
Lemma lem4621780 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621781 (k : nat) : (term91 k) = (term37 k).
Proof. exact (MK_COMB (@lem4621780) (@lem4621779 k)). Qed.
Lemma lem4621782 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4621783 (x : nat) (k : nat) : (term83 x k) = (term92 x k).
Proof. exact (MK_COMB (@lem4621782 x) (@lem4621781 k)). Qed.
Lemma lem4621784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4621785 (x : nat) (k : nat) : (term93 x k) = (term94 x k).
Proof. exact (MK_COMB (@lem4621784) (@lem4621783 x k)). Qed.
Lemma lem4621786 (x : nat) (k : nat) : (term84 k x) = (term5 x k).
Proof. exact (eq_refl (term84 k x)). Qed.
Lemma lem4621787 (x : nat) (k : nat) : ((term83 x k) = (term84 k x)) = ((term92 x k) = (term5 x k)).
Proof. exact (MK_COMB (@lem4621785 x k) (@lem4621786 x k)). Qed.
Lemma lem4621788 (x : nat) (k : nat) : (term92 x k) = (term5 x k).
Proof. exact (EQ_MP (@lem4621787 x k) (@lem4621770 k x)). Qed.
Lemma lem4621793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4621794 (x : nat) (k : nat) : (term94 x k) = (term95 x k).
Proof. exact (MK_COMB (@lem4621793) (@lem4621788 x k)). Qed.
Lemma lem4621796 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term70 A x y s) = (term71 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4621797 (y : nat) (x : nat) (s : nat -> Prop) : (term72 x y s) = (term73 y x s).
Proof. exact (@lem4621796 nat y x s). Qed.
Lemma lem4621798 (x : nat) (k : nat) : (term96 x k) = (term97 x k).
Proof. exact (@lem4621797 (S k) x (term98 k)). Qed.
Lemma lem4621804 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term55 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4621805 (p : nat -> Prop) (x : nat) : (term56 x p) = (p x).
Proof. exact (@lem4621804 nat p x). Qed.
Lemma lem4621806 (k : nat) (x : nat) : (term99 x k) = (term100 k x).
Proof. exact (@lem4621805 (term101 k) x). Qed.
Lemma lem4621807 (i : nat) (k : nat) : (term100 k i) = (Peano.le i k).
Proof. exact (eq_refl (term100 k i)). Qed.
Lemma lem4621808 (GEN_PVAR_187 : nat) : (@SETSPEC nat GEN_PVAR_187) = (@SETSPEC nat GEN_PVAR_187).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_187)). Qed.
Lemma lem4621809 (GEN_PVAR_187 : nat) (i : nat) (k : nat) : (term102 GEN_PVAR_187 k i) = (term103 GEN_PVAR_187 i k).
Proof. exact (MK_COMB (@lem4621808 GEN_PVAR_187) (@lem4621807 i k)). Qed.
Lemma lem4621810 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4621811 (GEN_PVAR_187 : nat) (k : nat) (i : nat) : (term104 GEN_PVAR_187 k i) = (term105 GEN_PVAR_187 k i).
Proof. exact (MK_COMB (@lem4621809 GEN_PVAR_187 i k) (@lem4621810 i)). Qed.
Lemma lem4621812 (GEN_PVAR_187 : nat) (k : nat) : (term106 GEN_PVAR_187 k) = (term107 GEN_PVAR_187 k).
Proof. exact (fun_ext (fun i : nat => @lem4621811 GEN_PVAR_187 k i)). Qed.
Lemma lem4621813 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621814 (GEN_PVAR_187 : nat) (k : nat) : (term108 GEN_PVAR_187 k) = (term109 GEN_PVAR_187 k).
Proof. exact (MK_COMB (@lem4621813) (@lem4621812 GEN_PVAR_187 k)). Qed.
Lemma lem4621815 (k : nat) : (term110 k) = (term111 k).
Proof. exact (fun_ext (fun GEN_PVAR_187 : nat => @lem4621814 GEN_PVAR_187 k)). Qed.
Lemma lem4621816 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621817 (k : nat) : (term112 k) = (term98 k).
Proof. exact (MK_COMB (@lem4621816) (@lem4621815 k)). Qed.
Lemma lem4621818 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4621819 (x : nat) (k : nat) : (term99 x k) = (term113 x k).
Proof. exact (MK_COMB (@lem4621818 x) (@lem4621817 k)). Qed.
Lemma lem4621820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4621821 (x : nat) (k : nat) : (term114 x k) = (term115 x k).
Proof. exact (MK_COMB (@lem4621820) (@lem4621819 x k)). Qed.
Lemma lem4621822 (x : nat) (k : nat) : (term100 k x) = (Peano.le x k).
Proof. exact (eq_refl (term100 k x)). Qed.
Lemma lem4621823 (x : nat) (k : nat) : ((term99 x k) = (term100 k x)) = ((term113 x k) = (Peano.le x k)).
Proof. exact (MK_COMB (@lem4621821 x k) (@lem4621822 x k)). Qed.
Lemma lem4621824 (x : nat) (k : nat) : (term113 x k) = (Peano.le x k).
Proof. exact (EQ_MP (@lem4621823 x k) (@lem4621806 k x)). Qed.
Lemma lem4621825 (x : nat) (k : nat) : (term116 x k) = (term116 x k).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem4621826 (x : nat) (k : nat) : (term97 x k) = (term5 x k).
Proof. exact (MK_COMB (@lem4621825 x k) (@lem4621824 x k)). Qed.
Lemma lem4621829 (x : nat) (k : nat) : (term96 x k) = (term5 x k).
Proof. exact (TRANS (@lem4621798 x k) (@lem4621826 x k)). Qed.
Lemma lem4621830 (x : nat) (k : nat) : ((term92 x k) = (term96 x k)) = ((term5 x k) = (term5 x k)).
Proof. exact (MK_COMB (@lem4621794 x k) (@lem4621829 x k)). Qed.
Lemma lem4621832 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4621833 (x : Prop) : (x = x) = True.
Proof. exact (@lem4621832 Prop x). Qed.
Lemma lem4621834 (x : nat) (k : nat) : ((term5 x k) = (term5 x k)) = True.
Proof. exact (@lem4621833 (term5 x k)). Qed.
Lemma lem4621835 (x : nat) (k : nat) : ((term92 x k) = (term96 x k)) = True.
Proof. exact (TRANS (@lem4621830 x k) (@lem4621834 x k)). Qed.
Lemma lem4621836 (k : nat) : (term117 k) = term79.
Proof. exact (fun_ext (fun x : nat => @lem4621835 x k)). Qed.
Lemma lem4621837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621838 (k : nat) : (term51 k) = term80.
Proof. exact (MK_COMB (@lem4621837) (@lem4621836 k)). Qed.
Lemma lem4621840 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621841 (t : Prop) : (term82 t) = t.
Proof. exact (@lem4621840 nat t). Qed.
Lemma lem4621842 : term80 = True.
Proof. exact (@lem4621841 True). Qed.
Lemma lem4621843 (k : nat) : (term51 k) = True.
Proof. exact (TRANS (@lem4621838 k) (@lem4621842)). Qed.
Lemma lem4621844 : term52 = term79.
Proof. exact (fun_ext (fun k : nat => @lem4621843 k)). Qed.
Lemma lem4621845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621846 : term53 = term80.
Proof. exact (MK_COMB (@lem4621845) (@lem4621844)). Qed.
Lemma lem4621848 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621849 (t : Prop) : (term82 t) = t.
Proof. exact (@lem4621848 nat t). Qed.
Lemma lem4621850 : term80 = True.
Proof. exact (@lem4621849 True). Qed.
Lemma lem4621851 : term53 = True.
Proof. exact (TRANS (@lem4621846) (@lem4621850)). Qed.
Lemma lem4621852 : term54 = (True /\ True).
Proof. exact (MK_COMB (@lem4621756) (@lem4621851)). Qed.
Lemma lem4621854 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4621855 : (True /\ True) = True.
Proof. exact (@lem4621854 True). Qed.
Lemma lem4621856 : term54 = True.
Proof. exact (TRANS (@lem4621852) (@lem4621855)). Qed.
Lemma lem4621857 : True = term54.
Proof. exact (SYM (@lem4621856)). Qed.
Lemma lem4621858 : term54.
Proof. exact (EQ_MP (@lem4621857) (@lem0)). Qed.
Lemma lem4621859 : term46.
Proof. exact (EQ_MP (@lem4621686) (@lem4621858)). Qed.
Lemma lem4621860 : term45.
Proof. exact (EQ_MP (@lem4621617) (@lem4621859)). Qed.
