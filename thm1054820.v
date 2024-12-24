Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1054820_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm1054482_spec.
Require Import thm1054744_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1054745 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem1054746 : term1.
Proof. exact (EQ_MP (@lem1054745) (@lem1054482)). Qed.
Lemma lem1054747 : term2.
Proof. exact (@lem1054746 term3). Qed.
Lemma lem1054748 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem1054749 : term4.
Proof. exact (EQ_MP (@lem1054748) (@lem1054747)). Qed.
Lemma lem1054750 (h1 : NUMLEFT = term5) : NUMLEFT = term5.
Proof. exact (h1). Qed.
Lemma lem1054751 (h1 : NUMLEFT = term5) : term5 = NUMLEFT.
Proof. exact (SYM (@lem1054750 h1)). Qed.
Lemma lem1054752 (h1 : term5 = NUMLEFT) : term5 = NUMLEFT.
Proof. exact (h1). Qed.
Lemma lem1054753 (h1 : term5 = NUMLEFT) : NUMLEFT = term5.
Proof. exact (SYM (@lem1054752 h1)). Qed.
Lemma lem1054754 : (NUMLEFT = term5) = (term5 = NUMLEFT).
Proof. exact (prop_ext (fun h1 : NUMLEFT = term5 => @lem1054751 h1) (fun h1 : term5 = NUMLEFT => @lem1054753 h1)). Qed.
Lemma lem1054757 : term5 = NUMLEFT.
Proof. exact (EQ_MP (@lem1054754) (@lem1054744)). Qed.
Lemma lem1054758 (x : Prop) (y : nat) : (NUMSUM x y) = (NUMSUM x y).
Proof. exact (eq_refl (NUMSUM x y)). Qed.
Lemma lem1054759 (x : Prop) (y : nat) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1054757) (@lem1054758 x y)). Qed.
Lemma lem1054760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1054761 (x : Prop) (y : nat) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1054760) (@lem1054759 x y)). Qed.
Lemma lem1054762 (x : Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1054763 (y : nat) (x : Prop) : ((term6 x y) = x) = ((term7 x y) = x).
Proof. exact (MK_COMB (@lem1054761 x y) (@lem1054762 x)). Qed.
Lemma lem1054764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1054765 (y : nat) (x : Prop) : (term10 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1054764) (@lem1054763 y x)). Qed.
Lemma lem1054766 (Y : nat -> nat) (x : Prop) (y : nat) : ((term12 Y x y) = y) = ((term12 Y x y) = y).
Proof. exact (eq_refl ((term12 Y x y) = y)). Qed.
Lemma lem1054767 (Y : nat -> nat) (x : Prop) (y : nat) : (term13 Y x y) = (term14 Y x y).
Proof. exact (MK_COMB (@lem1054765 y x) (@lem1054766 Y x y)). Qed.
Lemma lem1054768 (Y : nat -> nat) (x : Prop) : (term15 Y x) = (term16 Y x).
Proof. exact (fun_ext (fun y : nat => @lem1054767 Y x y)). Qed.
Lemma lem1054769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1054770 (Y : nat -> nat) (x : Prop) : (term17 Y x) = (term18 Y x).
Proof. exact (MK_COMB (@lem1054769) (@lem1054768 Y x)). Qed.
Lemma lem1054771 (Y : nat -> nat) : (term19 Y) = (term20 Y).
Proof. exact (fun_ext (fun x : Prop => @lem1054770 Y x)). Qed.
Lemma lem1054772 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1054773 (Y : nat -> nat) : (term21 Y) = (term22 Y).
Proof. exact (MK_COMB (@lem1054772) (@lem1054771 Y)). Qed.
Lemma lem1054774 : term23 = term24.
Proof. exact (fun_ext (fun Y : nat -> nat => @lem1054773 Y)). Qed.
Lemma lem1054775 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1054776 : term4 = term25.
Proof. exact (MK_COMB (@lem1054775) (@lem1054774)). Qed.
Lemma lem1054777 : term25.
Proof. exact (EQ_MP (@lem1054776) (@lem1054749)). Qed.
Lemma lem1054778 : term26.
Proof. exact (fun _17373 : type1669 => @lem1054777). Qed.
Lemma lem1054779 {A B : Type'} (P : type1413 A B) : term27 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1054780 {A B : Type'} (P : type1413 A B) : (term27 A B P) = ((term28 A B P) = (term29 A B P)).
Proof. exact (eq_refl (term27 A B P)). Qed.
Lemma lem1054783 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem1054780 A B P) (@lem1054779 A B P)). Qed.
Lemma lem1054784 (P : type1246) : (term30 P) = (term31 P).
Proof. exact (@lem1054783 type1669 (nat -> nat) P). Qed.
Lemma lem1054785 : term32 = term33.
Proof. exact (@lem1054784 term34). Qed.
Lemma lem1054786 (_17373 : type1669) : (term35 _17373) = term24.
Proof. exact (eq_refl (term35 _17373)). Qed.
Lemma lem1054787 (Y : nat -> nat) : Y = Y.
Proof. exact (eq_refl Y). Qed.
Lemma lem1054788 (_17373 : type1669) (Y : nat -> nat) : (term36 _17373 Y) = (term37 Y).
Proof. exact (MK_COMB (@lem1054786 _17373) (@lem1054787 Y)). Qed.
Lemma lem1054789 (Y : nat -> nat) : (term37 Y) = (term22 Y).
Proof. exact (eq_refl (term37 Y)). Qed.
Lemma lem1054790 (_17373 : type1669) (Y : nat -> nat) : (term36 _17373 Y) = (term22 Y).
Proof. exact (TRANS (@lem1054788 _17373 Y) (@lem1054789 Y)). Qed.
Lemma lem1054791 (_17373 : type1669) : (term38 _17373) = term24.
Proof. exact (fun_ext (fun Y : nat -> nat => @lem1054790 _17373 Y)). Qed.
Lemma lem1054792 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1054793 (_17373 : type1669) : (term39 _17373) = term25.
Proof. exact (MK_COMB (@lem1054792) (@lem1054791 _17373)). Qed.
Lemma lem1054794 : term40 = term41.
Proof. exact (fun_ext (fun _17373 : type1669 => @lem1054793 _17373)). Qed.
Lemma lem1054795 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1054796 : term32 = term26.
Proof. exact (MK_COMB (@lem1054795) (@lem1054794)). Qed.
Lemma lem1054797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1054798 : term42 = term43.
Proof. exact (MK_COMB (@lem1054797) (@lem1054796)). Qed.
Lemma lem1054799 (_17373 : type1669) : (term35 _17373) = term24.
Proof. exact (eq_refl (term35 _17373)). Qed.
Lemma lem1054800 (Y : type1249) (_17373 : type1669) : (Y _17373) = (Y _17373).
Proof. exact (eq_refl (Y _17373)). Qed.
Lemma lem1054801 (Y : type1249) (_17373 : type1669) : (term44 Y _17373) = (term45 Y _17373).
Proof. exact (MK_COMB (@lem1054799 _17373) (@lem1054800 Y _17373)). Qed.
Lemma lem1054802 (Y : type1249) (_17373 : type1669) : (term45 Y _17373) = (term46 Y _17373).
Proof. exact (eq_refl (term45 Y _17373)). Qed.
Lemma lem1054803 (Y : type1249) (_17373 : type1669) : (term44 Y _17373) = (term46 Y _17373).
Proof. exact (TRANS (@lem1054801 Y _17373) (@lem1054802 Y _17373)). Qed.
Lemma lem1054804 (Y : type1249) : (term47 Y) = (term48 Y).
Proof. exact (fun_ext (fun _17373 : type1669 => @lem1054803 Y _17373)). Qed.
Lemma lem1054805 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1054806 (Y : type1249) : (term49 Y) = (term50 Y).
Proof. exact (MK_COMB (@lem1054805) (@lem1054804 Y)). Qed.
Lemma lem1054807 : term51 = term52.
Proof. exact (fun_ext (fun Y : type1249 => @lem1054806 Y)). Qed.
Lemma lem1054808 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat))). Qed.
Lemma lem1054809 : term33 = term53.
Proof. exact (MK_COMB (@lem1054808) (@lem1054807)). Qed.
Lemma lem1054810 : (term32 = term33) = (term26 = term53).
Proof. exact (MK_COMB (@lem1054798) (@lem1054809)). Qed.
Lemma lem1054811 : term26 = term53.
Proof. exact (EQ_MP (@lem1054810) (@lem1054785)). Qed.
Lemma lem1054812 : term53.
Proof. exact (EQ_MP (@lem1054811) (@lem1054778)). Qed.
Lemma lem1054814 {A : Type'} : (@ex A) = (term54 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1054815 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat)) = term55.
Proof. exact (@lem1054814 type1249). Qed.
Lemma lem1054816 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1054817 : term53 = term56.
Proof. exact (MK_COMB (@lem1054815) (@lem1054816)). Qed.
Lemma lem1054818 : term56 = term57.
Proof. exact (eq_refl term56). Qed.
Lemma lem1054819 : term53 = term57.
Proof. exact (TRANS (@lem1054817) (@lem1054818)). Qed.
Lemma lem1054820 : term57.
Proof. exact (EQ_MP (@lem1054819) (@lem1054812)). Qed.
