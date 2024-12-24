Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_DISJOINT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3263572 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3263573 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3263572 A s t). Qed.
Lemma lem3263577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3263578 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3263577 A s t). Qed.
Lemma lem3263579 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@INTER A s t) = (@EMPTY A)) = (term1 A s t).
Proof. exact (@lem3263578 A (@INTER A s t) (@EMPTY A)). Qed.
Lemma lem3263584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = (term1 A s t).
Proof. exact (TRANS (@lem3263573 A s t) (@lem3263579 A s t)). Qed.
Lemma lem3263589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3263590 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3263589) (@lem3263584 A s t)). Qed.
Lemma lem3263597 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term4 A s t).
Proof. exact (eq_refl (term4 A s t)). Qed.
Lemma lem3263598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@DISJOINT A s t) = (term4 A s t)) = ((term1 A s t) = (term4 A s t)).
Proof. exact (MK_COMB (@lem3263590 A s t) (@lem3263597 A s t)). Qed.
Lemma lem3263603 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3263598 A s t)). Qed.
Lemma lem3263604 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3263605 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (MK_COMB (@lem3263604 A) (@lem3263603 A s)). Qed.
Lemma lem3263610 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3263605 A s)). Qed.
Lemma lem3263611 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3263612 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3263611 A) (@lem3263610 A)). Qed.
Lemma lem3263617 {A : Type'} : (term12 A) = (term11 A).
Proof. exact (SYM (@lem3263612 A)). Qed.
Lemma lem3263635 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A x s t) = (term14 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3263636 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A x s t) = (term14 A s x t).
Proof. exact (@lem3263635 A s x t). Qed.
Lemma lem3263640 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3263641 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3263640 A P x). Qed.
Lemma lem3263642 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3263641 A s x). Qed.
Lemma lem3263643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3263644 {A : Type'} (s : A -> Prop) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3263643) (@lem3263642 A s x)). Qed.
Lemma lem3263646 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3263647 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3263646 A P x). Qed.
Lemma lem3263648 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3263647 A t x). Qed.
Lemma lem3263649 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term14 A s x t) = (term17 A s t x).
Proof. exact (MK_COMB (@lem3263644 A s x) (@lem3263648 A t x)). Qed.
Lemma lem3263652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term13 A x s t) = (term17 A s t x).
Proof. exact (TRANS (@lem3263636 A s x t) (@lem3263649 A s t x)). Qed.
Lemma lem3263653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3263654 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term18 A x s t) = (term19 A s t x).
Proof. exact (MK_COMB (@lem3263653) (@lem3263652 A s t x)). Qed.
Lemma lem3263656 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3263657 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3263656 A x). Qed.
Lemma lem3263658 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term13 A x s t) = (@IN A x (@EMPTY A))) = ((term17 A s t x) = False).
Proof. exact (MK_COMB (@lem3263654 A s t x) (@lem3263657 A x)). Qed.
Lemma lem3263660 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3263661 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term17 A s t x) = False) = (term20 A s t x).
Proof. exact (@lem3263660 (term17 A s t x)). Qed.
Lemma lem3263664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term13 A x s t) = (@IN A x (@EMPTY A))) = (term20 A s t x).
Proof. exact (TRANS (@lem3263658 A s t x) (@lem3263661 A s t x)). Qed.
Lemma lem3263665 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = (term22 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263664 A s t x)). Qed.
Lemma lem3263666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3263667 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term23 A s t).
Proof. exact (MK_COMB (@lem3263666 A) (@lem3263665 A s t)). Qed.
Lemma lem3263672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3263673 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term24 A s t).
Proof. exact (MK_COMB (@lem3263672) (@lem3263667 A s t)). Qed.
Lemma lem3263681 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3263682 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3263681 A P x). Qed.
Lemma lem3263683 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3263682 A s x). Qed.
Lemma lem3263684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3263685 {A : Type'} (s : A -> Prop) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3263684) (@lem3263683 A s x)). Qed.
Lemma lem3263687 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3263688 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3263687 A P x). Qed.
Lemma lem3263689 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3263688 A t x). Qed.
Lemma lem3263690 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term14 A s x t) = (term17 A s t x).
Proof. exact (MK_COMB (@lem3263685 A s x) (@lem3263689 A t x)). Qed.
Lemma lem3263693 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263690 A s t x)). Qed.
Lemma lem3263694 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3263695 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3263694 A) (@lem3263693 A s t)). Qed.
Lemma lem3263700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3263701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term29 A s t).
Proof. exact (MK_COMB (@lem3263700) (@lem3263695 A s t)). Qed.
Lemma lem3263702 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term1 A s t) = (term4 A s t)) = ((term23 A s t) = (term29 A s t)).
Proof. exact (MK_COMB (@lem3263673 A s t) (@lem3263701 A s t)). Qed.
Lemma lem3263705 {A : Type'} (s : A -> Prop) : (term6 A s) = (term30 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3263702 A s t)). Qed.
Lemma lem3263706 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3263707 {A : Type'} (s : A -> Prop) : (term8 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3263706 A) (@lem3263705 A s)). Qed.
Lemma lem3263712 {A : Type'} : (term10 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3263707 A s)). Qed.
Lemma lem3263713 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3263714 {A : Type'} : (term12 A) = (term33 A).
Proof. exact (MK_COMB (@lem3263713 A) (@lem3263712 A)). Qed.
Lemma lem3263719 {A : Type'} : (term33 A) = (term12 A).
Proof. exact (SYM (@lem3263714 A)). Qed.
Lemma lem3263721 (p : Prop) : p = (term34 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3263722 {A : Type'} : (term33 A) = (term35 A).
Proof. exact (@lem3263721 (term33 A)). Qed.
Lemma lem3263723 {A : Type'} : (term35 A) = (term33 A).
Proof. exact (SYM (@lem3263722 A)). Qed.
Lemma lem3263724 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3263727 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3263728 {A : Type'} : term37 A.
Proof. exact (fun h0 : term35 A => @lem3263727 A h0). Qed.
Lemma lem3263729 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3263730 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3263731 {A : Type'} (h1 : term35 A) (h2 : term37 A) : term35 A.
Proof. exact (@lem3263729 A h2 (@lem3263730 A h1)). Qed.
Lemma lem3263732 {A : Type'} (h1 : term35 A) : term38 A.
Proof. exact (fun h0 : term37 A => @lem3263731 A h1 h0). Qed.
Lemma lem3263733 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3263734 {A : Type'} (h1 : term35 A) (h2 : term37 A) : term35 A.
Proof. exact (@lem3263732 A h1 (@lem3263733 A h2)). Qed.
Lemma lem3263735 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (fun h0 : term35 A => @lem3263734 A h0 h1). Qed.
Lemma lem3263736 {A : Type'} : term39 A.
Proof. exact (fun h0 : term37 A => @lem3263735 A h0). Qed.
Lemma lem3263739 {A : Type'} : term37 A.
Proof. exact (@lem3263736 A (@lem3263728 A)). Qed.
Lemma lem3263740 {A : Type'} : term37 A.
Proof. exact (@lem3263739 A). Qed.
Lemma lem3263742 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3263743 {A : Type'} : (term35 A) = (term40 A).
Proof. exact (@lem3263742 (term36 A)). Qed.
Lemma lem3263745 (t : Prop) : (term41 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3263746 {A : Type'} : (term40 A) = (term33 A).
Proof. exact (@lem3263745 (term33 A)). Qed.
Lemma lem3263779 {A : Type'} : (term35 A) = (term33 A).
Proof. exact (TRANS (@lem3263743 A) (@lem3263746 A)). Qed.
Lemma lem3263784 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term17 A s t x)). Qed.
Lemma lem3263785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263784 A s t x)). Qed.
Lemma lem3263786 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3263787 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3263786 A) (@lem3263785 A s t)). Qed.
Lemma lem3263788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3263789 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term29 A s t).
Proof. exact (MK_COMB (@lem3263788) (@lem3263787 A s t)). Qed.
Lemma lem3263796 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term20 A s t x) = (term20 A s t x).
Proof. exact (eq_refl (term20 A s t x)). Qed.
Lemma lem3263797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term22 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263796 A s t x)). Qed.
Lemma lem3263798 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3263799 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term23 A s t).
Proof. exact (MK_COMB (@lem3263798 A) (@lem3263797 A s t)). Qed.
Lemma lem3263800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3263801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = (term24 A s t).
Proof. exact (MK_COMB (@lem3263800) (@lem3263799 A s t)). Qed.
Lemma lem3263802 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term23 A s t) = (term29 A s t)) = ((term23 A s t) = (term29 A s t)).
Proof. exact (MK_COMB (@lem3263801 A s t) (@lem3263789 A s t)). Qed.
Lemma lem3263803 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3263802 A s t)). Qed.
Lemma lem3263804 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3263805 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3263804 A) (@lem3263803 A s)). Qed.
Lemma lem3263806 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3263805 A s)). Qed.
Lemma lem3263807 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3263808 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3263807 A) (@lem3263806 A)). Qed.
Lemma lem3263839 {A : Type'} : (term35 A) = (term33 A).
Proof. exact (TRANS (@lem3263779 A) (@lem3263808 A)). Qed.
Lemma lem3263840 {A : Type'} : (term33 A) = (term35 A).
Proof. exact (SYM (@lem3263839 A)). Qed.
Lemma lem3263842 (p : Prop) : p = (term34 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3263843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term23 A s t) = (term29 A s t)) = (term42 A s t).
Proof. exact (@lem3263842 ((term23 A s t) = (term29 A s t))). Qed.
Lemma lem3263844 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = ((term23 A s t) = (term29 A s t)).
Proof. exact (SYM (@lem3263843 A s t)). Qed.
Lemma lem3263845 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term43 A s t) : term43 A s t.
Proof. exact (h1). Qed.
Lemma lem3263854 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term20 A s t x) = (term44 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3263859 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A s t x) = (term17 A s t x).
Proof. exact (@lem16933 (term17 A s t x)). Qed.
Lemma lem3263860 {A : Type'} (P : A -> Prop) : (term46 A P) = (term47 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3263861 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term48 A s t) = (term49 A s t).
Proof. exact (@lem3263860 A (term22 A s t)). Qed.
Lemma lem3263862 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term50 A s t x) = (term20 A s t x).
Proof. exact (eq_refl (term50 A s t x)). Qed.
Lemma lem3263863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3263864 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term51 A s t x) = (term45 A s t x).
Proof. exact (MK_COMB (@lem3263863) (@lem3263862 A s t x)). Qed.
Lemma lem3263865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term51 A s t x) = (term17 A s t x).
Proof. exact (TRANS (@lem3263864 A s t x) (@lem3263859 A s t x)). Qed.
Lemma lem3263866 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term52 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263865 A s t x)). Qed.
Lemma lem3263867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3263868 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3263867 A) (@lem3263866 A s t)). Qed.
Lemma lem3263869 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term48 A s t) = (term28 A s t).
Proof. exact (TRANS (@lem3263861 A s t) (@lem3263868 A s t)). Qed.
Lemma lem3263870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263854 A s t x)). Qed.
Lemma lem3263871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3263872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3263871 A) (@lem3263870 A s t)). Qed.
Lemma lem3263881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term20 A s t x) = (term44 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3263884 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term17 A s t x)). Qed.
Lemma lem3263885 {A : Type'} (P : A -> Prop) : (term55 A P) = (term56 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3263886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term57 A s t).
Proof. exact (@lem3263885 A (term26 A s t)). Qed.
Lemma lem3263887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term58 A s t x)). Qed.
Lemma lem3263888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3263889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term59 A s t x) = (term20 A s t x).
Proof. exact (MK_COMB (@lem3263888) (@lem3263887 A s t x)). Qed.
Lemma lem3263890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term59 A s t x) = (term44 A s t x).
Proof. exact (TRANS (@lem3263889 A s t x) (@lem3263881 A s t x)). Qed.
Lemma lem3263891 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term60 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263890 A s t x)). Qed.
Lemma lem3263892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3263893 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3263892 A) (@lem3263891 A s t)). Qed.
Lemma lem3263894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term54 A s t).
Proof. exact (TRANS (@lem3263886 A s t) (@lem3263893 A s t)). Qed.
Lemma lem3263895 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3263884 A s t x)). Qed.
Lemma lem3263896 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3263897 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3263896 A) (@lem3263895 A s t)). Qed.
Lemma lem3263898 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term28 A s t).
Proof. exact (@lem16933 (term28 A s t)). Qed.
Lemma lem3263899 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term28 A s t).
Proof. exact (TRANS (@lem3263898 A s t) (@lem3263897 A s t)). Qed.
Lemma lem3263900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3263901 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term63 A s t).
Proof. exact (MK_COMB (@lem3263900) (@lem3263869 A s t)). Qed.
Lemma lem3263902 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3263901 A s t) (@lem3263894 A s t)). Qed.
Lemma lem3263903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3263904 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term66 A s t) = (term67 A s t).
Proof. exact (MK_COMB (@lem3263903) (@lem3263872 A s t)). Qed.
Lemma lem3263905 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term68 A s t) = (term69 A s t).
Proof. exact (MK_COMB (@lem3263904 A s t) (@lem3263899 A s t)). Qed.
Lemma lem3263906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3263907 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term70 A s t) = (term71 A s t).
Proof. exact (MK_COMB (@lem3263906) (@lem3263905 A s t)). Qed.
Lemma lem3263908 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term72 A s t) = (term73 A s t).
Proof. exact (MK_COMB (@lem3263907 A s t) (@lem3263902 A s t)). Qed.
Lemma lem3263909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term72 A s t).
Proof. exact (@lem17646 (term23 A s t) (term29 A s t)). Qed.
Lemma lem3263910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term73 A s t).
Proof. exact (TRANS (@lem3263909 A s t) (@lem3263908 A s t)). Qed.
Lemma lem3264033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3264034 {A : Type'} (P : Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (@lem3264033 A P Q). Qed.
Lemma lem3264035 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term77 A s t).
Proof. exact (@lem3264034 A (term54 A s t) (term26 A s t)). Qed.
Lemma lem3264036 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term58 A s t x)). Qed.
Lemma lem3264037 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264036 A s t x)). Qed.
Lemma lem3264038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264039 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3264038 A) (@lem3264037 A s t)). Qed.
Lemma lem3264040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term67 A s t).
Proof. exact (eq_refl (term67 A s t)). Qed.
Lemma lem3264041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term69 A s t).
Proof. exact (MK_COMB (@lem3264040 A s t) (@lem3264039 A s t)). Qed.
Lemma lem3264042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264043 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term81 A s t).
Proof. exact (MK_COMB (@lem3264042) (@lem3264041 A s t)). Qed.
Lemma lem3264044 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term58 A s t x)). Qed.
Lemma lem3264045 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term67 A s t).
Proof. exact (eq_refl (term67 A s t)). Qed.
Lemma lem3264046 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term83 A s t x).
Proof. exact (MK_COMB (@lem3264045 A s t) (@lem3264044 A s t x)). Qed.
Lemma lem3264047 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264046 A s t x)). Qed.
Lemma lem3264048 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264049 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3264048 A) (@lem3264047 A s t)). Qed.
Lemma lem3264050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term76 A s t) = (term77 A s t)) = ((term69 A s t) = (term86 A s t)).
Proof. exact (MK_COMB (@lem3264043 A s t) (@lem3264049 A s t)). Qed.
Lemma lem3264051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term69 A s t) = (term86 A s t).
Proof. exact (EQ_MP (@lem3264050 A s t) (@lem3264035 A s t)). Qed.
Lemma lem3264052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term71 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3264052) (@lem3264051 A s t)). Qed.
Lemma lem3264055 {A : Type'} (P : A -> Prop) (Q : Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3264056 {A : Type'} (P : A -> Prop) (Q : Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem3264055 A P Q). Qed.
Lemma lem3264057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term91 A s t).
Proof. exact (@lem3264056 A (term26 A s t) (term54 A s t)). Qed.
Lemma lem3264058 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term58 A s t x)). Qed.
Lemma lem3264059 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264058 A s t x)). Qed.
Lemma lem3264060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264061 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3264060 A) (@lem3264059 A s t)). Qed.
Lemma lem3264062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264063 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term63 A s t).
Proof. exact (MK_COMB (@lem3264062) (@lem3264061 A s t)). Qed.
Lemma lem3264064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (eq_refl (term54 A s t)). Qed.
Lemma lem3264065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3264063 A s t) (@lem3264064 A s t)). Qed.
Lemma lem3264066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term94 A s t).
Proof. exact (MK_COMB (@lem3264066) (@lem3264065 A s t)). Qed.
Lemma lem3264068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term58 A s t x)). Qed.
Lemma lem3264069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term95 A s t x) = (term96 A s t x).
Proof. exact (MK_COMB (@lem3264069) (@lem3264068 A s t x)). Qed.
Lemma lem3264071 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (eq_refl (term54 A s t)). Qed.
Lemma lem3264072 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term97 A x s t) = (term98 A x s t).
Proof. exact (MK_COMB (@lem3264070 A s t x) (@lem3264071 A s t)). Qed.
Lemma lem3264073 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term100 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264072 A x s t)). Qed.
Lemma lem3264074 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term101 A s t).
Proof. exact (MK_COMB (@lem3264074 A) (@lem3264073 A s t)). Qed.
Lemma lem3264076 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term90 A s t) = (term91 A s t)) = ((term65 A s t) = (term101 A s t)).
Proof. exact (MK_COMB (@lem3264067 A s t) (@lem3264075 A s t)). Qed.
Lemma lem3264077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term101 A s t).
Proof. exact (EQ_MP (@lem3264076 A s t) (@lem3264057 A s t)). Qed.
Lemma lem3264078 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term102 A s t).
Proof. exact (MK_COMB (@lem3264053 A s t) (@lem3264077 A s t)). Qed.
Lemma lem3264080 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3264081 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (@lem3264080 A P Q). Qed.
Lemma lem3264082 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term106 A s t).
Proof. exact (@lem3264081 A (term85 A s t) (term100 A s t)). Qed.
Lemma lem3264083 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term83 A s t x).
Proof. exact (eq_refl (term107 A s t x)). Qed.
Lemma lem3264084 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264083 A s t x)). Qed.
Lemma lem3264085 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264086 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term109 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3264085 A) (@lem3264084 A s t)). Qed.
Lemma lem3264087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264088 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term110 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3264087) (@lem3264086 A s t)). Qed.
Lemma lem3264089 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term111 A s t x) = (term98 A x s t).
Proof. exact (eq_refl (term111 A s t x)). Qed.
Lemma lem3264090 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term100 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264089 A x s t)). Qed.
Lemma lem3264091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264092 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term101 A s t).
Proof. exact (MK_COMB (@lem3264091 A) (@lem3264090 A s t)). Qed.
Lemma lem3264093 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term102 A s t).
Proof. exact (MK_COMB (@lem3264088 A s t) (@lem3264092 A s t)). Qed.
Lemma lem3264094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264095 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term115 A s t).
Proof. exact (MK_COMB (@lem3264094) (@lem3264093 A s t)). Qed.
Lemma lem3264096 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term83 A s t x).
Proof. exact (eq_refl (term107 A s t x)). Qed.
Lemma lem3264097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264098 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term116 A s t x) = (term117 A s t x).
Proof. exact (MK_COMB (@lem3264097) (@lem3264096 A s t x)). Qed.
Lemma lem3264099 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term111 A s t x) = (term98 A x s t).
Proof. exact (eq_refl (term111 A s t x)). Qed.
Lemma lem3264100 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term118 A s t x) = (term119 A x s t).
Proof. exact (MK_COMB (@lem3264098 A s t x) (@lem3264099 A x s t)). Qed.
Lemma lem3264101 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A s t) = (term121 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264100 A x s t)). Qed.
Lemma lem3264102 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264103 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term122 A s t).
Proof. exact (MK_COMB (@lem3264102 A) (@lem3264101 A s t)). Qed.
Lemma lem3264104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term105 A s t) = (term106 A s t)) = ((term102 A s t) = (term122 A s t)).
Proof. exact (MK_COMB (@lem3264095 A s t) (@lem3264103 A s t)). Qed.
Lemma lem3264105 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term122 A s t).
Proof. exact (EQ_MP (@lem3264104 A s t) (@lem3264082 A s t)). Qed.
Lemma lem3264107 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term122 A s t).
Proof. exact (TRANS (@lem3264078 A s t) (@lem3264105 A s t)). Qed.
Lemma lem3264108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term122 A s t).
Proof. exact (TRANS (@lem3263910 A s t) (@lem3264107 A s t)). Qed.
Lemma lem3264109 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term43 A s t) : term122 A s t.
Proof. exact (EQ_MP (@lem3264108 A s t) (@lem3263845 A s t h1)). Qed.
Lemma lem3264110 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : term119 A x s t.
Proof. exact (h1). Qed.
Lemma lem3264123 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term44 A s t x).
Proof. exact (eq_refl (term44 A s t x)). Qed.
Lemma lem3264124 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264123 A s t x)). Qed.
Lemma lem3264125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264126 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3264125 A) (@lem3264124 A s t)). Qed.
Lemma lem3264137 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term96 A s t x) = (term96 A s t x).
Proof. exact (eq_refl (term96 A s t x)). Qed.
Lemma lem3264138 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term98 A x s t).
Proof. exact (MK_COMB (@lem3264137 A s t x) (@lem3264126 A s t)). Qed.
Lemma lem3264147 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s t x) = (term17 A s t x).
Proof. exact (eq_refl (term17 A s t x)). Qed.
Lemma lem3264160 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term44 A s t x).
Proof. exact (eq_refl (term44 A s t x)). Qed.
Lemma lem3264161 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264160 A s t x)). Qed.
Lemma lem3264162 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264163 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3264162 A) (@lem3264161 A s t)). Qed.
Lemma lem3264164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264165 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term67 A s t).
Proof. exact (MK_COMB (@lem3264164) (@lem3264163 A s t)). Qed.
Lemma lem3264166 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term83 A s t x) = (term83 A s t x).
Proof. exact (MK_COMB (@lem3264165 A s t) (@lem3264147 A s t x)). Qed.
Lemma lem3264167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term117 A s t x) = (term117 A s t x).
Proof. exact (MK_COMB (@lem3264167) (@lem3264166 A s t x)). Qed.
Lemma lem3264169 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term119 A x s t) = (term119 A x s t).
Proof. exact (MK_COMB (@lem3264168 A s t x) (@lem3264138 A x s t)). Qed.
Lemma lem3264170 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : term119 A x s t.
Proof. exact (EQ_MP (@lem3264169 A x s t) (@lem3264110 A x s t h1)). Qed.
Lemma lem3264171 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term83 A s t x.
Proof. exact (h1). Qed.
Lemma lem3264172 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term98 A x s t.
Proof. exact (h1). Qed.
Lemma lem3264173 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term17 A s t x.
Proof. exact (proj2 (@lem3264171 A s t x h1)). Qed.
Lemma lem3264174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term54 A s t.
Proof. exact (proj1 (@lem3264171 A s t x h1)). Qed.
Lemma lem3264177 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term54 A s t.
Proof. exact (proj2 (@lem3264172 A x s t h1)). Qed.
Lemma lem3264178 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term17 A s t x.
Proof. exact (proj1 (@lem3264172 A x s t h1)). Qed.
Lemma lem3264188 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term44 A s t x).
Proof. exact (eq_refl (term44 A s t x)). Qed.
Lemma lem3264189 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264188 A s t x)). Qed.
Lemma lem3264190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264192 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3264190 A) (@lem3264189 A s t)). Qed.
Lemma lem3264193 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term54 A s t.
Proof. exact (EQ_MP (@lem3264192 A s t) (@lem3264174 A s t x h1)). Qed.
Lemma lem3264209 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term44 A s t x).
Proof. exact (eq_refl (term44 A s t x)). Qed.
Lemma lem3264210 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264209 A s t x)). Qed.
Lemma lem3264211 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3264211 A) (@lem3264210 A s t)). Qed.
Lemma lem3264214 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term54 A s t.
Proof. exact (EQ_MP (@lem3264213 A s t) (@lem3264177 A x s t h1)). Qed.
Lemma lem3264223 {A : Type'} (_33408 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term123 A s t _33408.
Proof. exact (@lem3264193 A s t x h1 _33408). Qed.
Lemma lem3264224 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33408 : A) : (term123 A s t _33408) = (term44 A s t _33408).
Proof. exact (eq_refl (term123 A s t _33408)). Qed.
Lemma lem3264226 {A : Type'} (_33409 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term123 A s t _33409.
Proof. exact (@lem3264214 A x s t h1 _33409). Qed.
Lemma lem3264227 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33409 : A) : (term123 A s t _33409) = (term44 A s t _33409).
Proof. exact (eq_refl (term123 A s t _33409)). Qed.
Lemma lem3264234 {A : Type'} (_33408 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term44 A s t _33408.
Proof. exact (EQ_MP (@lem3264224 A s t _33408) (@lem3264223 A _33408 s t x h1)). Qed.
Lemma lem3264244 {A : Type'} (_33409 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term44 A s t _33409.
Proof. exact (EQ_MP (@lem3264227 A s t _33409) (@lem3264226 A _33409 x s t h1)). Qed.
Lemma lem3264250 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : s x.
Proof. exact (proj1 (@lem3264173 A s t x h1)). Qed.
Lemma lem3264251 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term124 A s x.
Proof. exact (fun h0 : term125 A s x => @lem3264250 A s t x h1). Qed.
Lemma lem3264253 (p : Prop) : (term126 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3264254 {A : Type'} (s : A -> Prop) (x : A) : (term124 A s x) = (s x).
Proof. exact (@lem3264253 (s x)). Qed.
Lemma lem3264255 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : s x.
Proof. exact (EQ_MP (@lem3264254 A s x) (@lem3264251 A s t x h1)). Qed.
Lemma lem3264257 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : t x.
Proof. exact (proj2 (@lem3264173 A s t x h1)). Qed.
Lemma lem3264258 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term124 A t x.
Proof. exact (fun h0 : term125 A t x => @lem3264257 A s t x h1). Qed.
Lemma lem3264260 (p : Prop) : (term126 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3264261 {A : Type'} (t : A -> Prop) (x : A) : (term124 A t x) = (t x).
Proof. exact (@lem3264260 (t x)). Qed.
Lemma lem3264262 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : t x.
Proof. exact (EQ_MP (@lem3264261 A t x) (@lem3264258 A s t x h1)). Qed.
Lemma lem3264264 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3264265 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33408 : A) : (term44 A s t _33408) = (term20 A s t _33408).
Proof. exact (@lem3264264 (s _33408) (t _33408)). Qed.
Lemma lem3264267 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3264268 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33408 : A) : (term20 A s t _33408) = (term129 A s t _33408).
Proof. exact (@lem3264267 (term17 A s t _33408)). Qed.
Lemma lem3264269 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33408 : A) : (term44 A s t _33408) = (term129 A s t _33408).
Proof. exact (TRANS (@lem3264265 A s t _33408) (@lem3264268 A s t _33408)). Qed.
Lemma lem3264271 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term17 A s t x.
Proof. exact (conj (@lem3264255 A s t x h1) (@lem3264262 A s t x h1)). Qed.
Lemma lem3264273 {A : Type'} (_33408 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term129 A s t _33408.
Proof. exact (EQ_MP (@lem3264269 A s t _33408) (@lem3264234 A _33408 s t x h1)). Qed.
Lemma lem3264274 {A : Type'} (_33408 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term129 A s t _33408.
Proof. exact (@lem3264273 A _33408 s t x h1). Qed.
Lemma lem3264275 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term129 A s t x.
Proof. exact (@lem3264274 A x s t x h1). Qed.
Lemma lem3264278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : False.
Proof. exact (@lem3264275 A s t x h1 (@lem3264271 A s t x h1)). Qed.
Lemma lem3264279 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : term130.
Proof. exact (fun h0 : ~ False => @lem3264278 A s t x h1). Qed.
Lemma lem3264281 (p : Prop) : (term126 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3264282 : term130 = False.
Proof. exact (@lem3264281 False). Qed.
Lemma lem3264283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term83 A s t x) : False.
Proof. exact (EQ_MP (@lem3264282) (@lem3264279 A s t x h1)). Qed.
Lemma lem3264285 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : s x.
Proof. exact (proj1 (@lem3264178 A x s t h1)). Qed.
Lemma lem3264286 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term124 A s x.
Proof. exact (fun h0 : term125 A s x => @lem3264285 A x s t h1). Qed.
Lemma lem3264288 (p : Prop) : (term126 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3264289 {A : Type'} (s : A -> Prop) (x : A) : (term124 A s x) = (s x).
Proof. exact (@lem3264288 (s x)). Qed.
Lemma lem3264290 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : s x.
Proof. exact (EQ_MP (@lem3264289 A s x) (@lem3264286 A x s t h1)). Qed.
Lemma lem3264292 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : t x.
Proof. exact (proj2 (@lem3264178 A x s t h1)). Qed.
Lemma lem3264293 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term124 A t x.
Proof. exact (fun h0 : term125 A t x => @lem3264292 A x s t h1). Qed.
Lemma lem3264295 (p : Prop) : (term126 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3264296 {A : Type'} (t : A -> Prop) (x : A) : (term124 A t x) = (t x).
Proof. exact (@lem3264295 (t x)). Qed.
Lemma lem3264297 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : t x.
Proof. exact (EQ_MP (@lem3264296 A t x) (@lem3264293 A x s t h1)). Qed.
Lemma lem3264299 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3264300 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33409 : A) : (term44 A s t _33409) = (term20 A s t _33409).
Proof. exact (@lem3264299 (s _33409) (t _33409)). Qed.
Lemma lem3264302 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3264303 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33409 : A) : (term20 A s t _33409) = (term129 A s t _33409).
Proof. exact (@lem3264302 (term17 A s t _33409)). Qed.
Lemma lem3264304 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33409 : A) : (term44 A s t _33409) = (term129 A s t _33409).
Proof. exact (TRANS (@lem3264300 A s t _33409) (@lem3264303 A s t _33409)). Qed.
Lemma lem3264306 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term17 A s t x.
Proof. exact (conj (@lem3264290 A x s t h1) (@lem3264297 A x s t h1)). Qed.
Lemma lem3264308 {A : Type'} (_33409 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term129 A s t _33409.
Proof. exact (EQ_MP (@lem3264304 A s t _33409) (@lem3264244 A _33409 x s t h1)). Qed.
Lemma lem3264309 {A : Type'} (_33409 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term129 A s t _33409.
Proof. exact (@lem3264308 A _33409 x s t h1). Qed.
Lemma lem3264310 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term129 A s t x.
Proof. exact (@lem3264309 A x x s t h1). Qed.
Lemma lem3264313 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : False.
Proof. exact (@lem3264310 A x s t h1 (@lem3264306 A x s t h1)). Qed.
Lemma lem3264314 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : term130.
Proof. exact (fun h0 : ~ False => @lem3264313 A x s t h1). Qed.
Lemma lem3264316 (p : Prop) : (term126 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3264317 : term130 = False.
Proof. exact (@lem3264316 False). Qed.
Lemma lem3264318 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term98 A x s t) : False.
Proof. exact (EQ_MP (@lem3264317) (@lem3264314 A x s t h1)). Qed.
Lemma lem3264319 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : False.
Proof. exact (or_elim (@lem3264170 A x s t h1) (fun h0 : term83 A s t x => @lem3264283 A s t x h0) (fun h0 : term98 A x s t => @lem3264318 A x s t h0)). Qed.
Lemma lem3264320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : (term119 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term119 A x s t => @lem3264319 A x s t h1) (fun h2 : False => @lem3264170 A x s t h1)). Qed.
Lemma lem3264321 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : False.
Proof. exact (EQ_MP (@lem3264320 A x s t h1) (@lem3264170 A x s t h1)). Qed.
Lemma lem3264322 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term43 A s t) : False.
Proof. exact (ex_elim (@lem3264109 A s t h1) (fun x : A => fun h0 : term121 A s t x => @lem3264321 A x s t h0)). Qed.
Lemma lem3264323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term43 A s t) : (term43 A s t) = False.
Proof. exact (prop_ext (fun h2 : term43 A s t => @lem3264322 A s t h1) (fun h2 : False => @lem3263845 A s t h1)). Qed.
Lemma lem3264324 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term43 A s t) : False.
Proof. exact (EQ_MP (@lem3264323 A s t h1) (@lem3263845 A s t h1)). Qed.
Lemma lem3264325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term42 A s t.
Proof. exact (fun h0 : term43 A s t => @lem3264324 A s t h0). Qed.
Lemma lem3264326 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term29 A s t).
Proof. exact (EQ_MP (@lem3263844 A s t) (@lem3264325 A s t)). Qed.
Lemma lem3264331 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (fun t : A -> Prop => @lem3264326 A s t). Qed.
Lemma lem3264336 {A : Type'} : term33 A.
Proof. exact (fun s : A -> Prop => @lem3264331 A s). Qed.
Lemma lem3264337 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem3263840 A) (@lem3264336 A)). Qed.
Lemma lem3264339 {A : Type'} : term35 A.
Proof. exact (@lem3263740 A (@lem3264337 A)). Qed.
Lemma lem3264340 {A : Type'} (h1 : term36 A) : False.
Proof. exact (@lem3264339 A (@lem3263724 A h1)). Qed.
Lemma lem3264341 {A : Type'} (h1 : term36 A) : (term36 A) = False.
Proof. exact (prop_ext (fun h2 : term36 A => @lem3264340 A h1) (fun h2 : False => @lem3263724 A h1)). Qed.
Lemma lem3264342 {A : Type'} (h1 : term36 A) : False.
Proof. exact (EQ_MP (@lem3264341 A h1) (@lem3263724 A h1)). Qed.
Lemma lem3264343 {A : Type'} : term35 A.
Proof. exact (fun h0 : term36 A => @lem3264342 A h0). Qed.
Lemma lem3264344 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem3263723 A) (@lem3264343 A)). Qed.
Lemma lem3264345 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem3263719 A) (@lem3264344 A)). Qed.
Lemma lem3264346 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3263617 A) (@lem3264345 A)). Qed.
