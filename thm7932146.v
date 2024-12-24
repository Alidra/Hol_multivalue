Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932146_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm69_spec.
Require Import thm7931551_spec.
Require Import thm7931564_spec.
Require Import thm7931565_spec.
Require Import thm7931587_spec.
Require Import thm7931588_spec.
Lemma lem7931604 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))).
Proof. exact (h1). Qed.
Lemma lem7931605 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A)).
Proof. exact (SYM (@lem7931604 A h1)). Qed.
Lemma lem7931606 {A : Type'} (h1 : (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A))) : (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A)).
Proof. exact (h1). Qed.
Lemma lem7931607 {A : Type'} (h1 : (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A))) : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))).
Proof. exact (SYM (@lem7931606 A h1)). Qed.
Lemma lem7931608 {A : Type'} : ((@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) = ((@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A))).
Proof. exact (prop_ext (fun h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) => @lem7931605 A h1) (fun h1 : (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A)) => @lem7931607 A h1)). Qed.
Lemma lem7931609 {A : Type'} : ((@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A))) = ((@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))).
Proof. exact (SYM (@lem7931608 A)). Qed.
Lemma lem7931611 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term0 _88266 _88270 f s t.
Proof. exact (EQ_MP (@lem7931588 _88266 _88270 f s t) (@lem7931587 _88266 _88270 f s t)). Qed.
Lemma lem7931612 {A : Type'} (f : type46 A) (s : type48 A) (t : type1345 A) : term1 A f s t.
Proof. exact (@lem7931611 (tybit0 A) (finite_sum A A) f s t). Qed.
Lemma lem7931613 {A : Type'} : term2 A.
Proof. exact (@lem7931612 A (@mktybit0 A) (@UNIV (finite_sum A A)) (@UNIV (tybit0 A))). Qed.
Lemma lem7931623 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7931565 A x) (@lem7931564 A x)). Qed.
Lemma lem7931624 {A : Type'} (x : tybit0 A) : (@IN (tybit0 A) x (@UNIV (tybit0 A))) = True.
Proof. exact (@lem7931623 (tybit0 A) x). Qed.
Lemma lem7931625 {A : Type'} (y : tybit0 A) : (@IN (tybit0 A) y (@UNIV (tybit0 A))) = True.
Proof. exact (@lem7931624 A y). Qed.
Lemma lem7931626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7931627 {A : Type'} (y : tybit0 A) : (term3 A y) = (imp True).
Proof. exact (MK_COMB (@lem7931626) (@lem7931625 A y)). Qed.
Lemma lem7931634 {A : Type'} (y : tybit0 A) : (term4 A y) = (term4 A y).
Proof. exact (eq_refl (term4 A y)). Qed.
Lemma lem7931635 {A : Type'} (y : tybit0 A) : (term5 A y) = (term6 A y).
Proof. exact (MK_COMB (@lem7931627 A y) (@lem7931634 A y)). Qed.
Lemma lem7931637 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7931638 {A : Type'} (y : tybit0 A) : (term6 A y) = (term4 A y).
Proof. exact (@lem7931637 (term4 A y)). Qed.
Lemma lem7931645 {A : Type'} (y : tybit0 A) : (term5 A y) = (term4 A y).
Proof. exact (TRANS (@lem7931635 A y) (@lem7931638 A y)). Qed.
Lemma lem7931646 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun y : tybit0 A => @lem7931645 A y)). Qed.
Lemma lem7931647 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931648 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem7931647 A) (@lem7931646 A)). Qed.
Lemma lem7931653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7931654 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem7931653) (@lem7931648 A)). Qed.
Lemma lem7931662 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7931565 A x) (@lem7931564 A x)). Qed.
Lemma lem7931663 {A : Type'} (x : tybit0 A) : (@IN (tybit0 A) x (@UNIV (tybit0 A))) = True.
Proof. exact (@lem7931662 (tybit0 A) x). Qed.
Lemma lem7931664 {A : Type'} (x : finite_sum A A) : (term13 A x) = True.
Proof. exact (@lem7931663 A (@mktybit0 A x)). Qed.
Lemma lem7931665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7931666 {A : Type'} (x : finite_sum A A) : (term14 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7931665) (@lem7931664 A x)). Qed.
Lemma lem7931668 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7931565 A x) (@lem7931564 A x)). Qed.
Lemma lem7931669 {A : Type'} (x : finite_sum A A) : (@IN (finite_sum A A) x (@UNIV (finite_sum A A))) = True.
Proof. exact (@lem7931668 (finite_sum A A) x). Qed.
Lemma lem7931670 {A : Type'} (x : finite_sum A A) : ((term13 A x) = (@IN (finite_sum A A) x (@UNIV (finite_sum A A)))) = (True = True).
Proof. exact (MK_COMB (@lem7931666 A x) (@lem7931669 A x)). Qed.
Lemma lem7931672 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7931673 : (True = True) = True.
Proof. exact (@lem7931672 True). Qed.
Lemma lem7931674 {A : Type'} (x : finite_sum A A) : ((term13 A x) = (@IN (finite_sum A A) x (@UNIV (finite_sum A A)))) = True.
Proof. exact (TRANS (@lem7931670 A x) (@lem7931673)). Qed.
Lemma lem7931675 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun x : finite_sum A A => @lem7931674 A x)). Qed.
Lemma lem7931676 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7931677 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem7931676 A) (@lem7931675 A)). Qed.
Lemma lem7931679 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7931680 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem7931679 (finite_sum A A) t). Qed.
Lemma lem7931681 {A : Type'} : (term18 A) = True.
Proof. exact (@lem7931680 A True). Qed.
Lemma lem7931682 {A : Type'} : (term17 A) = True.
Proof. exact (TRANS (@lem7931677 A) (@lem7931681 A)). Qed.
Lemma lem7931683 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem7931654 A) (@lem7931682 A)). Qed.
Lemma lem7931685 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7931686 {A : Type'} : (term22 A) = (term10 A).
Proof. exact (@lem7931685 (term10 A)). Qed.
Lemma lem7931697 {A : Type'} : (term21 A) = (term10 A).
Proof. exact (TRANS (@lem7931683 A) (@lem7931686 A)). Qed.
Lemma lem7931698 {A : Type'} : (term10 A) = (term21 A).
Proof. exact (SYM (@lem7931697 A)). Qed.
Lemma lem7931700 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7931701 {A : Type'} : (term10 A) = (term24 A).
Proof. exact (@lem7931700 (term10 A)). Qed.
Lemma lem7931702 {A : Type'} : (term24 A) = (term10 A).
Proof. exact (SYM (@lem7931701 A)). Qed.
Lemma lem7931703 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem7931704 {A : Type'} : term26 A.
Proof. exact (@lem7931551 A). Qed.
Lemma lem7931708 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem7931709 {A : Type'} : term28 A.
Proof. exact (fun h0 : term27 A => @lem7931708 A h0). Qed.
Lemma lem7931710 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem7931711 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem7931712 {A : Type'} (h1 : term27 A) (h2 : term28 A) : term27 A.
Proof. exact (@lem7931710 A h2 (@lem7931711 A h1)). Qed.
Lemma lem7931713 {A : Type'} (h1 : term27 A) : term29 A.
Proof. exact (fun h0 : term28 A => @lem7931712 A h1 h0). Qed.
Lemma lem7931714 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem7931715 {A : Type'} (h1 : term27 A) (h2 : term28 A) : term27 A.
Proof. exact (@lem7931713 A h1 (@lem7931714 A h2)). Qed.
Lemma lem7931716 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (fun h0 : term27 A => @lem7931715 A h0 h1). Qed.
Lemma lem7931717 {A : Type'} : term30 A.
Proof. exact (fun h0 : term28 A => @lem7931716 A h0). Qed.
Lemma lem7931720 {A : Type'} : term28 A.
Proof. exact (@lem7931717 A (@lem7931709 A)). Qed.
Lemma lem7931721 {A : Type'} : term28 A.
Proof. exact (@lem7931720 A). Qed.
Lemma lem7931733 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7931734 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (@lem7931733 (term26 A)). Qed.
Lemma lem7931743 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (eq_refl (term33 A)). Qed.
Lemma lem7931750 {A : Type'} : (term27 A) = (term34 A).
Proof. exact (MK_COMB (@lem7931743 A) (@lem7931734 A)). Qed.
Lemma lem7931751 {A : Type'} (x : tybit0 A) (a : finite_sum A A) : (x = (@mktybit0 A a)) = (x = (@mktybit0 A a)).
Proof. exact (eq_refl (x = (@mktybit0 A a))). Qed.
Lemma lem7931752 {A : Type'} (x : tybit0 A) : (term35 A x) = (term35 A x).
Proof. exact (fun_ext (fun a : finite_sum A A => @lem7931751 A x a)). Qed.
Lemma lem7931753 {A : Type'} : (@ex (finite_sum A A)) = (@ex (finite_sum A A)).
Proof. exact (eq_refl (@ex (finite_sum A A))). Qed.
Lemma lem7931754 {A : Type'} (x : tybit0 A) : (term36 A x) = (term36 A x).
Proof. exact (MK_COMB (@lem7931753 A) (@lem7931752 A x)). Qed.
Lemma lem7931755 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931754 A x)). Qed.
Lemma lem7931756 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931757 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7931756 A) (@lem7931755 A)). Qed.
Lemma lem7931758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7931759 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem7931758) (@lem7931757 A)). Qed.
Lemma lem7931760 {A : Type'} (x : finite_sum A A) (y : tybit0 A) : ((@mktybit0 A x) = y) = ((@mktybit0 A x) = y).
Proof. exact (eq_refl ((@mktybit0 A x) = y)). Qed.
Lemma lem7931761 {A : Type'} (y : tybit0 A) : (term38 A y) = (term38 A y).
Proof. exact (fun_ext (fun x : finite_sum A A => @lem7931760 A x y)). Qed.
Lemma lem7931762 {A : Type'} : (@ex (finite_sum A A)) = (@ex (finite_sum A A)).
Proof. exact (eq_refl (@ex (finite_sum A A))). Qed.
Lemma lem7931763 {A : Type'} (y : tybit0 A) : (term4 A y) = (term4 A y).
Proof. exact (MK_COMB (@lem7931762 A) (@lem7931761 A y)). Qed.
Lemma lem7931764 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (fun_ext (fun y : tybit0 A => @lem7931763 A y)). Qed.
Lemma lem7931765 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931766 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7931765 A) (@lem7931764 A)). Qed.
Lemma lem7931767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7931768 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem7931767) (@lem7931766 A)). Qed.
Lemma lem7931769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7931770 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem7931769) (@lem7931768 A)). Qed.
Lemma lem7931771 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem7931770 A) (@lem7931759 A)). Qed.
Lemma lem7931800 {A : Type'} : (term27 A) = (term34 A).
Proof. exact (TRANS (@lem7931750 A) (@lem7931771 A)). Qed.
Lemma lem7931801 {A : Type'} : (term34 A) = (term27 A).
Proof. exact (SYM (@lem7931800 A)). Qed.
Lemma lem7931802 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem7931803 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem7931805 {A : Type'} (P : type48 A) : (term39 A P) = (term40 A P).
Proof. exact (@lem18394 (finite_sum A A) P). Qed.
Lemma lem7931806 {A : Type'} (y : tybit0 A) : (term41 A y) = (term42 A y).
Proof. exact (@lem7931805 A (term38 A y)). Qed.
Lemma lem7931807 {A : Type'} (x : finite_sum A A) (y : tybit0 A) : (term43 A y x) = ((@mktybit0 A x) = y).
Proof. exact (eq_refl (term43 A y x)). Qed.
Lemma lem7931808 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7931810 {A : Type'} (x : finite_sum A A) (y : tybit0 A) : (term44 A y x) = (term45 A x y).
Proof. exact (MK_COMB (@lem7931808) (@lem7931807 A x y)). Qed.
Lemma lem7931811 {A : Type'} (y : tybit0 A) : (term46 A y) = (term47 A y).
Proof. exact (fun_ext (fun x : finite_sum A A => @lem7931810 A x y)). Qed.
Lemma lem7931812 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7931813 {A : Type'} (y : tybit0 A) : (term42 A y) = (term48 A y).
Proof. exact (MK_COMB (@lem7931812 A) (@lem7931811 A y)). Qed.
Lemma lem7931814 {A : Type'} (y : tybit0 A) : (term41 A y) = (term48 A y).
Proof. exact (TRANS (@lem7931806 A y) (@lem7931813 A y)). Qed.
Lemma lem7931815 {A : Type'} (P : type1345 A) : (term49 A P) = (term50 A P).
Proof. exact (@lem18392 (tybit0 A) P). Qed.
Lemma lem7931816 {A : Type'} : (term25 A) = (term51 A).
Proof. exact (@lem7931815 A (term8 A)). Qed.
Lemma lem7931817 {A : Type'} (y : tybit0 A) : (term52 A y) = (term4 A y).
Proof. exact (eq_refl (term52 A y)). Qed.
Lemma lem7931818 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7931819 {A : Type'} (y : tybit0 A) : (term53 A y) = (term41 A y).
Proof. exact (MK_COMB (@lem7931818) (@lem7931817 A y)). Qed.
Lemma lem7931820 {A : Type'} (y : tybit0 A) : (term53 A y) = (term48 A y).
Proof. exact (TRANS (@lem7931819 A y) (@lem7931814 A y)). Qed.
Lemma lem7931821 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (fun_ext (fun y : tybit0 A => @lem7931820 A y)). Qed.
Lemma lem7931822 {A : Type'} : (@ex (tybit0 A)) = (@ex (tybit0 A)).
Proof. exact (eq_refl (@ex (tybit0 A))). Qed.
Lemma lem7931823 {A : Type'} : (term51 A) = (term56 A).
Proof. exact (MK_COMB (@lem7931822 A) (@lem7931821 A)). Qed.
Lemma lem7931836 {A : Type'} : (term25 A) = (term56 A).
Proof. exact (TRANS (@lem7931816 A) (@lem7931823 A)). Qed.
Lemma lem7931837 {A : Type'} (h1 : term25 A) : term56 A.
Proof. exact (EQ_MP (@lem7931836 A) (@lem7931802 A h1)). Qed.
Lemma lem7931838 {A : Type'} (x : tybit0 A) (a : finite_sum A A) : (x = (@mktybit0 A a)) = (x = (@mktybit0 A a)).
Proof. exact (eq_refl (x = (@mktybit0 A a))). Qed.
Lemma lem7931839 {A : Type'} (x : tybit0 A) : (term35 A x) = (term35 A x).
Proof. exact (fun_ext (fun a : finite_sum A A => @lem7931838 A x a)). Qed.
Lemma lem7931840 {A : Type'} : (@ex (finite_sum A A)) = (@ex (finite_sum A A)).
Proof. exact (eq_refl (@ex (finite_sum A A))). Qed.
Lemma lem7931841 {A : Type'} (x : tybit0 A) : (term36 A x) = (term36 A x).
Proof. exact (MK_COMB (@lem7931840 A) (@lem7931839 A x)). Qed.
Lemma lem7931842 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931841 A x)). Qed.
Lemma lem7931843 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931844 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7931843 A) (@lem7931842 A)). Qed.
Lemma lem7931855 {A B : Type'} (P : type1413 A B) : (term57 A B P) = (term58 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7931856 {A : Type'} (P : type1343 A) : (term59 A P) = (term60 A P).
Proof. exact (@lem7931855 (tybit0 A) (finite_sum A A) P). Qed.
Lemma lem7931857 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (@lem7931856 A (term63 A)). Qed.
Lemma lem7931858 {A : Type'} (x : tybit0 A) : (term64 A x) = (term35 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem7931859 {A : Type'} (a : finite_sum A A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7931860 {A : Type'} (x : tybit0 A) (a : finite_sum A A) : (term65 A x a) = (term66 A x a).
Proof. exact (MK_COMB (@lem7931858 A x) (@lem7931859 A a)). Qed.
Lemma lem7931861 {A : Type'} (x : tybit0 A) (a : finite_sum A A) : (term66 A x a) = (x = (@mktybit0 A a)).
Proof. exact (eq_refl (term66 A x a)). Qed.
Lemma lem7931862 {A : Type'} (x : tybit0 A) (a : finite_sum A A) : (term65 A x a) = (x = (@mktybit0 A a)).
Proof. exact (TRANS (@lem7931860 A x a) (@lem7931861 A x a)). Qed.
Lemma lem7931863 {A : Type'} (x : tybit0 A) : (term67 A x) = (term35 A x).
Proof. exact (fun_ext (fun a : finite_sum A A => @lem7931862 A x a)). Qed.
Lemma lem7931864 {A : Type'} : (@ex (finite_sum A A)) = (@ex (finite_sum A A)).
Proof. exact (eq_refl (@ex (finite_sum A A))). Qed.
Lemma lem7931865 {A : Type'} (x : tybit0 A) : (term68 A x) = (term36 A x).
Proof. exact (MK_COMB (@lem7931864 A) (@lem7931863 A x)). Qed.
Lemma lem7931866 {A : Type'} : (term69 A) = (term37 A).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931865 A x)). Qed.
Lemma lem7931867 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931868 {A : Type'} : (term61 A) = (term26 A).
Proof. exact (MK_COMB (@lem7931867 A) (@lem7931866 A)). Qed.
Lemma lem7931869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7931870 {A : Type'} : (term70 A) = (term71 A).
Proof. exact (MK_COMB (@lem7931869) (@lem7931868 A)). Qed.
Lemma lem7931871 {A : Type'} (x : tybit0 A) : (term64 A x) = (term35 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem7931872 {A : Type'} (a : type1342 A) (x : tybit0 A) : (a x) = (a x).
Proof. exact (eq_refl (a x)). Qed.
Lemma lem7931873 {A : Type'} (a : type1342 A) (x : tybit0 A) : (term72 A a x) = (term73 A a x).
Proof. exact (MK_COMB (@lem7931871 A x) (@lem7931872 A a x)). Qed.
Lemma lem7931874 {A : Type'} (a : type1342 A) (x : tybit0 A) : (term73 A a x) = (x = (term74 A a x)).
Proof. exact (eq_refl (term73 A a x)). Qed.
Lemma lem7931875 {A : Type'} (a : type1342 A) (x : tybit0 A) : (term72 A a x) = (x = (term74 A a x)).
Proof. exact (TRANS (@lem7931873 A a x) (@lem7931874 A a x)). Qed.
Lemma lem7931876 {A : Type'} (a : type1342 A) : (term75 A a) = (term76 A a).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931875 A a x)). Qed.
Lemma lem7931877 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931878 {A : Type'} (a : type1342 A) : (term77 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem7931877 A) (@lem7931876 A a)). Qed.
Lemma lem7931879 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (fun_ext (fun a : type1342 A => @lem7931878 A a)). Qed.
Lemma lem7931880 {A : Type'} : (@ex ((tybit0 A) -> finite_sum A A)) = (@ex ((tybit0 A) -> finite_sum A A)).
Proof. exact (eq_refl (@ex ((tybit0 A) -> finite_sum A A))). Qed.
Lemma lem7931881 {A : Type'} : (term62 A) = (term81 A).
Proof. exact (MK_COMB (@lem7931880 A) (@lem7931879 A)). Qed.
Lemma lem7931882 {A : Type'} : ((term61 A) = (term62 A)) = ((term26 A) = (term81 A)).
Proof. exact (MK_COMB (@lem7931870 A) (@lem7931881 A)). Qed.
Lemma lem7931884 {A : Type'} : (term26 A) = (term81 A).
Proof. exact (EQ_MP (@lem7931882 A) (@lem7931857 A)). Qed.
Lemma lem7931885 {A : Type'} : (term26 A) = (term81 A).
Proof. exact (TRANS (@lem7931844 A) (@lem7931884 A)). Qed.
Lemma lem7931886 {A : Type'} (h1 : term26 A) : term81 A.
Proof. exact (EQ_MP (@lem7931885 A) (@lem7931803 A h1)). Qed.
Lemma lem7931887 {A : Type'} (a : type1342 A) (h1 : term78 A a) : term78 A a.
Proof. exact (h1). Qed.
Lemma lem7931888 {A : Type'} (y : tybit0 A) (h1 : term48 A y) : term48 A y.
Proof. exact (h1). Qed.
Lemma lem7931897 {A : Type'} (a : type1342 A) (x : tybit0 A) : (x = (term74 A a x)) = (x = (term74 A a x)).
Proof. exact (eq_refl (x = (term74 A a x))). Qed.
Lemma lem7931898 {A : Type'} (a : type1342 A) : (term76 A a) = (term76 A a).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931897 A a x)). Qed.
Lemma lem7931899 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931900 {A : Type'} (a : type1342 A) : (term78 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem7931899 A) (@lem7931898 A a)). Qed.
Lemma lem7931901 {A : Type'} (a : type1342 A) (h1 : term78 A a) : term78 A a.
Proof. exact (EQ_MP (@lem7931900 A a) (@lem7931887 A a h1)). Qed.
Lemma lem7931910 {A : Type'} (x : finite_sum A A) (y : tybit0 A) : (term45 A x y) = (term45 A x y).
Proof. exact (eq_refl (term45 A x y)). Qed.
Lemma lem7931911 {A : Type'} (y : tybit0 A) : (term47 A y) = (term47 A y).
Proof. exact (fun_ext (fun x : finite_sum A A => @lem7931910 A x y)). Qed.
Lemma lem7931912 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7931913 {A : Type'} (y : tybit0 A) : (term48 A y) = (term48 A y).
Proof. exact (MK_COMB (@lem7931912 A) (@lem7931911 A y)). Qed.
Lemma lem7931914 {A : Type'} (y : tybit0 A) (h1 : term48 A y) : term48 A y.
Proof. exact (EQ_MP (@lem7931913 A y) (@lem7931888 A y h1)). Qed.
Lemma lem7931916 {A : Type'} (a : type1342 A) (x : tybit0 A) : (x = (term74 A a x)) = (x = (term74 A a x)).
Proof. exact (eq_refl (x = (term74 A a x))). Qed.
Lemma lem7931917 {A : Type'} (a : type1342 A) : (term76 A a) = (term76 A a).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931916 A a x)). Qed.
Lemma lem7931918 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931920 {A : Type'} (a : type1342 A) : (term78 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem7931918 A) (@lem7931917 A a)). Qed.
Lemma lem7931921 {A : Type'} (a : type1342 A) (h1 : term78 A a) : term78 A a.
Proof. exact (EQ_MP (@lem7931920 A a) (@lem7931901 A a h1)). Qed.
Lemma lem7931923 {A : Type'} (x : finite_sum A A) (y : tybit0 A) : (term45 A x y) = (term45 A x y).
Proof. exact (eq_refl (term45 A x y)). Qed.
Lemma lem7931924 {A : Type'} (y : tybit0 A) : (term47 A y) = (term47 A y).
Proof. exact (fun_ext (fun x : finite_sum A A => @lem7931923 A x y)). Qed.
Lemma lem7931925 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7931927 {A : Type'} (y : tybit0 A) : (term48 A y) = (term48 A y).
Proof. exact (MK_COMB (@lem7931925 A) (@lem7931924 A y)). Qed.
Lemma lem7931928 {A : Type'} (y : tybit0 A) (h1 : term48 A y) : term48 A y.
Proof. exact (EQ_MP (@lem7931927 A y) (@lem7931914 A y h1)). Qed.
Lemma lem7931929 {A : Type'} (_103823 : tybit0 A) (a : type1342 A) (h1 : term78 A a) : term82 A a _103823.
Proof. exact (@lem7931921 A a h1 _103823). Qed.
Lemma lem7931930 {A : Type'} (a : type1342 A) (_103823 : tybit0 A) : (term82 A a _103823) = (_103823 = (term74 A a _103823)).
Proof. exact (eq_refl (term82 A a _103823)). Qed.
Lemma lem7931932 {A : Type'} (_103824 : finite_sum A A) (y : tybit0 A) (h1 : term48 A y) : term83 A y _103824.
Proof. exact (@lem7931928 A y h1 _103824). Qed.
Lemma lem7931933 {A : Type'} (_103824 : finite_sum A A) (y : tybit0 A) : (term83 A y _103824) = (term45 A _103824 y).
Proof. exact (eq_refl (term83 A y _103824)). Qed.
Lemma lem7931938 {A : Type'} (_103824 : finite_sum A A) (y : tybit0 A) (h1 : term48 A y) : term45 A _103824 y.
Proof. exact (EQ_MP (@lem7931933 A _103824 y) (@lem7931932 A _103824 y h1)). Qed.
Lemma lem7931956 {A : Type'} (x : tybit0 A) (y : tybit0 A) (z : tybit0 A) : term84 A x y z.
Proof. exact (@lem21385 (tybit0 A) x y z). Qed.
Lemma lem7931960 {A : Type'} (_103823 : tybit0 A) (a : type1342 A) (h1 : term78 A a) : _103823 = (term74 A a _103823).
Proof. exact (EQ_MP (@lem7931930 A a _103823) (@lem7931929 A _103823 a h1)). Qed.
Lemma lem7931961 {A : Type'} (_103823 : tybit0 A) (a : type1342 A) (h1 : term78 A a) : _103823 = (term74 A a _103823).
Proof. exact (@lem7931960 A _103823 a h1). Qed.
Lemma lem7931962 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : y = (term74 A a y).
Proof. exact (@lem7931961 A y a h1). Qed.
Lemma lem7931963 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : term85 A a y.
Proof. exact (fun h0 : term86 A a y => @lem7931962 A y a h1). Qed.
Lemma lem7931965 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7931966 {A : Type'} (a : type1342 A) (y : tybit0 A) : (term85 A a y) = (y = (term74 A a y)).
Proof. exact (@lem7931965 (y = (term74 A a y))). Qed.
Lemma lem7931967 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : y = (term74 A a y).
Proof. exact (EQ_MP (@lem7931966 A a y) (@lem7931963 A y a h1)). Qed.
Lemma lem7931969 {A : Type'} (x : tybit0 A) : x = x.
Proof. exact (@lem21386 (tybit0 A) x). Qed.
Lemma lem7931970 {A : Type'} (x : tybit0 A) : x = x.
Proof. exact (@lem7931969 A x). Qed.
Lemma lem7931971 {A : Type'} (y : tybit0 A) : y = y.
Proof. exact (@lem7931970 A y). Qed.
Lemma lem7931972 {A : Type'} (y : tybit0 A) : term88 A y.
Proof. exact (fun h0 : term89 A y => @lem7931971 A y). Qed.
Lemma lem7931974 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7931975 {A : Type'} (y : tybit0 A) : (term88 A y) = (y = y).
Proof. exact (@lem7931974 (y = y)). Qed.
Lemma lem7931976 {A : Type'} (y : tybit0 A) : y = y.
Proof. exact (EQ_MP (@lem7931975 A y) (@lem7931972 A y)). Qed.
Lemma lem7931994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7931995 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term90 A x y z) = (term91 A y x z).
Proof. exact (@lem7931994 (y = z) (term92 A x z)). Qed.
Lemma lem7932005 {A : Type'} (x : tybit0 A) (y : tybit0 A) : (term93 A x y) = (term93 A x y).
Proof. exact (eq_refl (term93 A x y)). Qed.
Lemma lem7932006 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term84 A x y z) = (term94 A y x z).
Proof. exact (MK_COMB (@lem7932005 A x y) (@lem7931995 A y x z)). Qed.
Lemma lem7932010 (q : Prop) (p : Prop) (r : Prop) : (term95 p q r) = (term95 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7932011 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term94 A y x z) = (term96 A y x z).
Proof. exact (@lem7932010 (y = z) (term92 A x y) (term92 A x z)). Qed.
Lemma lem7932033 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term84 A x y z) = (term96 A y x z).
Proof. exact (TRANS (@lem7932006 A y x z) (@lem7932011 A y x z)). Qed.
Lemma lem7932034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7932035 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term97 A x y z) = (term98 A y x z).
Proof. exact (MK_COMB (@lem7932034) (@lem7932033 A y x z)). Qed.
Lemma lem7932057 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term96 A y x z) = (term96 A y x z).
Proof. exact (eq_refl (term96 A y x z)). Qed.
Lemma lem7932058 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : ((term84 A x y z) = (term96 A y x z)) = ((term96 A y x z) = (term96 A y x z)).
Proof. exact (MK_COMB (@lem7932035 A y x z) (@lem7932057 A y x z)). Qed.
Lemma lem7932060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7932061 (x : Prop) : (x = x) = True.
Proof. exact (@lem7932060 Prop x). Qed.
Lemma lem7932062 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : ((term96 A y x z) = (term96 A y x z)) = True.
Proof. exact (@lem7932061 (term96 A y x z)). Qed.
Lemma lem7932063 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : ((term84 A x y z) = (term96 A y x z)) = True.
Proof. exact (TRANS (@lem7932058 A y x z) (@lem7932062 A y x z)). Qed.
Lemma lem7932064 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : True = ((term84 A x y z) = (term96 A y x z)).
Proof. exact (SYM (@lem7932063 A y x z)). Qed.
Lemma lem7932065 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term84 A x y z) = (term96 A y x z).
Proof. exact (EQ_MP (@lem7932064 A y x z) (@lem0)). Qed.
Lemma lem7932066 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : term96 A y x z.
Proof. exact (EQ_MP (@lem7932065 A y x z) (@lem7931956 A x y z)). Qed.
Lemma lem7932068 (b : Prop) (a : Prop) : (a \/ b) = (term99 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7932069 {A : Type'} (x : tybit0 A) (y : tybit0 A) (z : tybit0 A) : (term96 A y x z) = (term100 A x y z).
Proof. exact (@lem7932068 (term101 A y x z) (y = z)). Qed.
Lemma lem7932071 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7932072 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term104 A y x z) = (term105 A y x z).
Proof. exact (@lem7932071 (term92 A x y) (term92 A x z)). Qed.
Lemma lem7932074 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7932075 {A : Type'} (x : tybit0 A) (y : tybit0 A) : (term107 A x y) = (x = y).
Proof. exact (@lem7932074 (x = y)). Qed.
Lemma lem7932076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932077 {A : Type'} (x : tybit0 A) (y : tybit0 A) : (term108 A x y) = (term109 A x y).
Proof. exact (MK_COMB (@lem7932076) (@lem7932075 A x y)). Qed.
Lemma lem7932079 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7932080 {A : Type'} (x : tybit0 A) (z : tybit0 A) : (term107 A x z) = (x = z).
Proof. exact (@lem7932079 (x = z)). Qed.
Lemma lem7932081 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term105 A y x z) = (term110 A y x z).
Proof. exact (MK_COMB (@lem7932077 A x y) (@lem7932080 A x z)). Qed.
Lemma lem7932082 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term104 A y x z) = (term110 A y x z).
Proof. exact (TRANS (@lem7932072 A y x z) (@lem7932081 A y x z)). Qed.
Lemma lem7932083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932084 {A : Type'} (y : tybit0 A) (x : tybit0 A) (z : tybit0 A) : (term111 A y x z) = (term112 A y x z).
Proof. exact (MK_COMB (@lem7932083) (@lem7932082 A y x z)). Qed.
Lemma lem7932085 {A : Type'} (y : tybit0 A) (z : tybit0 A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7932086 {A : Type'} (x : tybit0 A) (y : tybit0 A) (z : tybit0 A) : (term100 A x y z) = (term113 A x y z).
Proof. exact (MK_COMB (@lem7932084 A y x z) (@lem7932085 A y z)). Qed.
Lemma lem7932087 {A : Type'} (x : tybit0 A) (y : tybit0 A) (z : tybit0 A) : (term96 A y x z) = (term113 A x y z).
Proof. exact (TRANS (@lem7932069 A x y z) (@lem7932086 A x y z)). Qed.
Lemma lem7932089 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : term114 A a y.
Proof. exact (conj (@lem7931967 A y a h1) (@lem7931976 A y)). Qed.
Lemma lem7932091 {A : Type'} (x : tybit0 A) (y : tybit0 A) (z : tybit0 A) : term113 A x y z.
Proof. exact (EQ_MP (@lem7932087 A x y z) (@lem7932066 A y x z)). Qed.
Lemma lem7932092 {A : Type'} (x : tybit0 A) (y : tybit0 A) (z : tybit0 A) : term113 A x y z.
Proof. exact (@lem7932091 A x y z). Qed.
Lemma lem7932093 {A : Type'} (a : type1342 A) (y : tybit0 A) : term115 A a y.
Proof. exact (@lem7932092 A y (term74 A a y) y). Qed.
Lemma lem7932096 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : (term74 A a y) = y.
Proof. exact (@lem7932093 A a y (@lem7932089 A y a h1)). Qed.
Lemma lem7932097 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : (term74 A a y) = y.
Proof. exact (@lem7932096 A y a h1). Qed.
Lemma lem7932098 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : term116 A a y.
Proof. exact (fun h0 : term117 A a y => @lem7932097 A y a h1). Qed.
Lemma lem7932100 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7932101 {A : Type'} (a : type1342 A) (y : tybit0 A) : (term116 A a y) = ((term74 A a y) = y).
Proof. exact (@lem7932100 ((term74 A a y) = y)). Qed.
Lemma lem7932102 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term78 A a) : (term74 A a y) = y.
Proof. exact (EQ_MP (@lem7932101 A a y) (@lem7932098 A y a h1)). Qed.
Lemma lem7932105 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7932107 {A : Type'} (_103824 : finite_sum A A) (y : tybit0 A) : (term45 A _103824 y) = (term118 A _103824 y).
Proof. exact (@lem7932105 ((@mktybit0 A _103824) = y)). Qed.
Lemma lem7932110 {A : Type'} (_103824 : finite_sum A A) (y : tybit0 A) (h1 : term48 A y) : term118 A _103824 y.
Proof. exact (EQ_MP (@lem7932107 A _103824 y) (@lem7931938 A _103824 y h1)). Qed.
Lemma lem7932111 {A : Type'} (_103824 : finite_sum A A) (y : tybit0 A) (h1 : term48 A y) : term118 A _103824 y.
Proof. exact (@lem7932110 A _103824 y h1). Qed.
Lemma lem7932112 {A : Type'} (a : type1342 A) (y : tybit0 A) (h1 : term48 A y) : term119 A a y.
Proof. exact (@lem7932111 A (a y) y h1). Qed.
Lemma lem7932115 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (@lem7932112 A a y h1 (@lem7932102 A y a h2)). Qed.
Lemma lem7932116 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : term120.
Proof. exact (fun h0 : ~ False => @lem7932115 A y a h1 h2). Qed.
Lemma lem7932118 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7932119 : term120 = False.
Proof. exact (@lem7932118 False). Qed.
Lemma lem7932120 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932119) (@lem7932116 A y a h1 h2)). Qed.
Lemma lem7932121 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : (term48 A y) = False.
Proof. exact (prop_ext (fun h3 : term48 A y => @lem7932120 A y a h1 h2) (fun h3 : False => @lem7931928 A y h1)). Qed.
Lemma lem7932122 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932121 A y a h1 h2) (@lem7931928 A y h1)). Qed.
Lemma lem7932123 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : (term78 A a) = False.
Proof. exact (prop_ext (fun h3 : term78 A a => @lem7932122 A y a h1 h2) (fun h3 : False => @lem7931921 A a h2)). Qed.
Lemma lem7932124 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932123 A y a h1 h2) (@lem7931921 A a h2)). Qed.
Lemma lem7932125 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : (term48 A y) = False.
Proof. exact (prop_ext (fun h3 : term48 A y => @lem7932124 A y a h1 h2) (fun h3 : False => @lem7931914 A y h1)). Qed.
Lemma lem7932126 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932125 A y a h1 h2) (@lem7931914 A y h1)). Qed.
Lemma lem7932127 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : (term78 A a) = False.
Proof. exact (prop_ext (fun h3 : term78 A a => @lem7932126 A y a h1 h2) (fun h3 : False => @lem7931901 A a h2)). Qed.
Lemma lem7932128 {A : Type'} (y : tybit0 A) (a : type1342 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932127 A y a h1 h2) (@lem7931901 A a h2)). Qed.
Lemma lem7932129 {A : Type'} (a : type1342 A) (h1 : term78 A a) (h2 : term25 A) : False.
Proof. exact (ex_elim (@lem7931837 A h2) (fun y : tybit0 A => fun h0 : term55 A y => @lem7932128 A y a h0 h1)). Qed.
Lemma lem7932130 {A : Type'} (h1 : term26 A) (h2 : term25 A) : False.
Proof. exact (ex_elim (@lem7931886 A h1) (fun a : type1342 A => fun h0 : term80 A a => @lem7932129 A a h0 h2)). Qed.
Lemma lem7932131 {A : Type'} (h1 : term25 A) : term31 A.
Proof. exact (fun h0 : term26 A => @lem7932130 A h0 h1). Qed.
Lemma lem7932132 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (@lem69 (term26 A)). Qed.
Lemma lem7932133 {A : Type'} (h1 : term25 A) : term32 A.
Proof. exact (EQ_MP (@lem7932132 A) (@lem7932131 A h1)). Qed.
Lemma lem7932134 {A : Type'} : term34 A.
Proof. exact (fun h0 : term25 A => @lem7932133 A h0). Qed.
Lemma lem7932135 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem7931801 A) (@lem7932134 A)). Qed.
Lemma lem7932137 {A : Type'} : term27 A.
Proof. exact (@lem7931721 A (@lem7932135 A)). Qed.
Lemma lem7932138 {A : Type'} (h1 : term25 A) : term31 A.
Proof. exact (@lem7932137 A (@lem7931703 A h1)). Qed.
Lemma lem7932139 {A : Type'} (h1 : term25 A) : False.
Proof. exact (@lem7932138 A h1 (@lem7931704 A)). Qed.
Lemma lem7932140 {A : Type'} (h1 : term25 A) : (term25 A) = False.
Proof. exact (prop_ext (fun h2 : term25 A => @lem7932139 A h1) (fun h2 : False => @lem7931703 A h1)). Qed.
Lemma lem7932141 {A : Type'} (h1 : term25 A) : False.
Proof. exact (EQ_MP (@lem7932140 A h1) (@lem7931703 A h1)). Qed.
Lemma lem7932142 {A : Type'} : term24 A.
Proof. exact (fun h0 : term25 A => @lem7932141 A h0). Qed.
Lemma lem7932143 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem7931702 A) (@lem7932142 A)). Qed.
Lemma lem7932144 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem7931698 A) (@lem7932143 A)). Qed.
Lemma lem7932145 {A : Type'} : (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) = (@UNIV (tybit0 A)).
Proof. exact (@lem7931613 A (@lem7932144 A)). Qed.
Lemma lem7932146 {A : Type'} : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))).
Proof. exact (EQ_MP (@lem7931609 A) (@lem7932145 A)). Qed.
