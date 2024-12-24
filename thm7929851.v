Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7929851_term_abbrevs.
Require Import thm7928419_spec.
Require Import thm7928420_spec.
Require Import thm7928450_spec.
Require Import thm7928454_spec.
Require Import thm7929765_spec.
Lemma lem7929766 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term1 A _103802' tybit1' P.
Proof. exact (@lem7928420 A tybit1' _103802' h1 (term2 A tybit1' P)). Qed.
Lemma lem7929767 {A : Type'} (_103802' : type39 A) (tybit1' : type1329 A) (P : type1351 A) : (term1 A _103802' tybit1' P) = (term3 A _103802' tybit1' P).
Proof. exact (eq_refl (term1 A _103802' tybit1' P)). Qed.
Lemma lem7929768 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term3 A _103802' tybit1' P.
Proof. exact (EQ_MP (@lem7929767 A _103802' tybit1' P) (@lem7929766 A P tybit1' _103802' h1)). Qed.
Lemma lem7929770 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (_103802' : type39 A) (a : type6 A) : (term4 A tybit1' P _103802' a) = (term5 A tybit1' P _103802' a).
Proof. exact (eq_refl (term4 A tybit1' P _103802' a)). Qed.
Lemma lem7929771 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term6 A tybit1' _103802' a.
Proof. exact (@lem7928419 A tybit1' _103802' h1 a). Qed.
Lemma lem7929772 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (a : type6 A) : (term6 A tybit1' _103802' a) = (term7 A tybit1' _103802' a).
Proof. exact (eq_refl (term6 A tybit1' _103802' a)). Qed.
Lemma lem7929775 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term7 A tybit1' _103802' a.
Proof. exact (EQ_MP (@lem7929772 A tybit1' _103802' a) (@lem7929771 A a tybit1' _103802' h1)). Qed.
Lemma lem7929776 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term7 A tybit1' _103802' a.
Proof. exact (@lem7929775 A a tybit1' _103802' h1). Qed.
Lemma lem7929778 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : (term9 A _103802' a) = (@_103802 A a).
Proof. exact (SYM (@lem7929765 A a _103802' h1)). Qed.
Lemma lem7929779 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : (term9 A _103802' a) = (@_103802 A a).
Proof. exact (@lem7929778 A a _103802' h1). Qed.
Lemma lem7929780 {A : Type'} (P : type1351 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7929781 {A : Type'} (P : type1351 A) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : (term10 A P _103802' a) = (term11 A P a).
Proof. exact (MK_COMB (@lem7929780 A P) (@lem7929779 A a _103802' h1)). Qed.
Lemma lem7929782 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (a : type6 A) : (term12 A tybit1' _103802' a) = (term12 A tybit1' _103802' a).
Proof. exact (eq_refl (term12 A tybit1' _103802' a)). Qed.
Lemma lem7929783 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : (term5 A tybit1' P _103802' a) = (term13 A tybit1' _103802' P a).
Proof. exact (MK_COMB (@lem7929782 A tybit1' _103802' a) (@lem7929781 A P a _103802' h1)). Qed.
Lemma lem7929784 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (_103802' : type39 A) (a : type6 A) : (term14 A tybit1' P _103802' a) = (term14 A tybit1' P _103802' a).
Proof. exact (eq_refl (term14 A tybit1' P _103802' a)). Qed.
Lemma lem7929785 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : ((term4 A tybit1' P _103802' a) = (term5 A tybit1' P _103802' a)) = ((term4 A tybit1' P _103802' a) = (term13 A tybit1' _103802' P a)).
Proof. exact (MK_COMB (@lem7929784 A tybit1' P _103802' a) (@lem7929783 A tybit1' P a _103802' h1)). Qed.
Lemma lem7929786 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : (term4 A tybit1' P _103802' a) = (term13 A tybit1' _103802' P a).
Proof. exact (EQ_MP (@lem7929785 A tybit1' P a _103802' h1) (@lem7929770 A tybit1' P _103802' a)). Qed.
Lemma lem7929787 {A : Type'} (P : type1351 A) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem7929788 {A : Type'} (a : type6 A) (P : type1351 A) (h1 : term15 A P) : term16 A P a.
Proof. exact (@lem7929787 A P h1 a). Qed.
Lemma lem7929789 {A : Type'} (P : type1351 A) (a : type6 A) : (term16 A P a) = (term11 A P a).
Proof. exact (eq_refl (term16 A P a)). Qed.
Lemma lem7929790 {A : Type'} (a : type6 A) (P : type1351 A) (h1 : term15 A P) : term11 A P a.
Proof. exact (EQ_MP (@lem7929789 A P a) (@lem7929788 A a P h1)). Qed.
Lemma lem7929791 {A : Type'} (a : type6 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : tybit1' = (term0 A _103802')) : term13 A tybit1' _103802' P a.
Proof. exact (conj (@lem7929776 A a tybit1' _103802' h2) (@lem7929790 A a P h1)). Qed.
Lemma lem7929792 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : (term13 A tybit1' _103802' P a) = (term4 A tybit1' P _103802' a).
Proof. exact (SYM (@lem7929786 A tybit1' P a _103802' h1)). Qed.
Lemma lem7929793 {A : Type'} (a : type6 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term4 A tybit1' P _103802' a.
Proof. exact (EQ_MP (@lem7929792 A tybit1' P a _103802' h2) (@lem7929791 A a P tybit1' _103802' h1 h3)). Qed.
Lemma lem7929794 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term17 A tybit1' P _103802'.
Proof. exact (fun a : type6 A => @lem7929793 A a P tybit1' _103802' h1 h2 h3). Qed.
Lemma lem7929795 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : term18 A tybit1' P _103802'.
Proof. exact (fun h0 : term15 A P => @lem7929794 A P tybit1' _103802' h0 h1 h2). Qed.
Lemma lem7929796 {A : Type'} (P : type1351 A) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem7929797 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term17 A tybit1' P _103802'.
Proof. exact (@lem7929795 A P tybit1' _103802' h2 h3 (@lem7929796 A P h1)). Qed.
Lemma lem7929798 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term19 A tybit1' P.
Proof. exact (@lem7929768 A P tybit1' _103802' h3 (@lem7929797 A P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929799 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term20 A tybit1' P x.
Proof. exact (@lem7929798 A P tybit1' _103802' h1 h2 h3 (@_dest_tybit1 A x)). Qed.
Lemma lem7929800 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (x : tybit1 A) : (term20 A tybit1' P x) = (term21 A tybit1' P x).
Proof. exact (eq_refl (term20 A tybit1' P x)). Qed.
Lemma lem7929801 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term21 A tybit1' P x.
Proof. exact (EQ_MP (@lem7929800 A tybit1' P x) (@lem7929799 A x P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929803 {A : Type'} (r : type1675 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : (tybit1' r) = ((term22 A r) = r).
Proof. exact (TRANS (@lem7928454 A r tybit1' _103802' h1 h2) (@lem7928450 A r)). Qed.
Lemma lem7929804 {A : Type'} (r : type1675 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : (tybit1' r) = ((term22 A r) = r).
Proof. exact (@lem7929803 A r tybit1' _103802' h1 h2). Qed.
Lemma lem7929805 {A : Type'} (x : tybit1 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : (term23 A tybit1' x) = ((term24 A x) = (@_dest_tybit1 A x)).
Proof. exact (@lem7929804 A (@_dest_tybit1 A x) tybit1' _103802' h1 h2). Qed.
Lemma lem7929806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7929807 {A : Type'} (x : tybit1 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : (term25 A tybit1' x) = (term26 A x).
Proof. exact (MK_COMB (@lem7929806) (@lem7929805 A x tybit1' _103802' h1 h2)). Qed.
Lemma lem7929808 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (x : tybit1 A) : (term27 A tybit1' P x) = (term27 A tybit1' P x).
Proof. exact (eq_refl (term27 A tybit1' P x)). Qed.
Lemma lem7929809 {A : Type'} (P : type1351 A) (x : tybit1 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : (term21 A tybit1' P x) = (term28 A tybit1' P x).
Proof. exact (MK_COMB (@lem7929807 A x tybit1' _103802' h1 h2) (@lem7929808 A tybit1' P x)). Qed.
Lemma lem7929810 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term28 A tybit1' P x.
Proof. exact (EQ_MP (@lem7929809 A P x tybit1' _103802' h2 h3) (@lem7929801 A x P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929812 {A : Type'} (a : tybit1 A) : (term29 A a) = a.
Proof. exact (@axiom_39 A a). Qed.
Lemma lem7929813 {A : Type'} (a : tybit1 A) : (term29 A a) = a.
Proof. exact (@lem7929812 A a). Qed.
Lemma lem7929814 {A : Type'} (x : tybit1 A) : (term29 A x) = x.
Proof. exact (@lem7929813 A x). Qed.
Lemma lem7929815 {A : Type'} : (@_dest_tybit1 A) = (@_dest_tybit1 A).
Proof. exact (eq_refl (@_dest_tybit1 A)). Qed.
Lemma lem7929816 {A : Type'} (x : tybit1 A) : (term24 A x) = (@_dest_tybit1 A x).
Proof. exact (MK_COMB (@lem7929815 A) (@lem7929814 A x)). Qed.
Lemma lem7929817 {A : Type'} : (@eq (recspace (finite_sum (finite_sum A A) unit))) = (@eq (recspace (finite_sum (finite_sum A A) unit))).
Proof. exact (eq_refl (@eq (recspace (finite_sum (finite_sum A A) unit)))). Qed.
Lemma lem7929818 {A : Type'} (x : tybit1 A) : (term30 A x) = (term31 A x).
Proof. exact (MK_COMB (@lem7929817 A) (@lem7929816 A x)). Qed.
Lemma lem7929819 {A : Type'} (x : tybit1 A) : (@_dest_tybit1 A x) = (@_dest_tybit1 A x).
Proof. exact (eq_refl (@_dest_tybit1 A x)). Qed.
Lemma lem7929820 {A : Type'} (x : tybit1 A) : ((term24 A x) = (@_dest_tybit1 A x)) = ((@_dest_tybit1 A x) = (@_dest_tybit1 A x)).
Proof. exact (MK_COMB (@lem7929818 A x) (@lem7929819 A x)). Qed.
Lemma lem7929821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7929822 {A : Type'} (x : tybit1 A) : (term26 A x) = (term32 A x).
Proof. exact (MK_COMB (@lem7929821) (@lem7929820 A x)). Qed.
Lemma lem7929823 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (x : tybit1 A) : (term27 A tybit1' P x) = (term27 A tybit1' P x).
Proof. exact (eq_refl (term27 A tybit1' P x)). Qed.
Lemma lem7929824 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (x : tybit1 A) : (term28 A tybit1' P x) = (term33 A tybit1' P x).
Proof. exact (MK_COMB (@lem7929822 A x) (@lem7929823 A tybit1' P x)). Qed.
Lemma lem7929825 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term33 A tybit1' P x.
Proof. exact (EQ_MP (@lem7929824 A tybit1' P x) (@lem7929810 A x P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929826 {A : Type'} (x : tybit1 A) : (@_dest_tybit1 A x) = (@_dest_tybit1 A x).
Proof. exact (eq_refl (@_dest_tybit1 A x)). Qed.
Lemma lem7929827 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term27 A tybit1' P x.
Proof. exact (@lem7929825 A x P tybit1' _103802' h1 h2 h3 (@lem7929826 A x)). Qed.
Lemma lem7929828 {A : Type'} (tybit1' : type1329 A) (P : type1351 A) (x : tybit1 A) : (term27 A tybit1' P x) = (term34 A tybit1' P x).
Proof. exact (eq_refl (term27 A tybit1' P x)). Qed.
Lemma lem7929829 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term34 A tybit1' P x.
Proof. exact (EQ_MP (@lem7929828 A tybit1' P x) (@lem7929827 A x P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929830 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term35 A P x.
Proof. exact (proj2 (@lem7929829 A x P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929832 {A : Type'} (a : tybit1 A) : (term29 A a) = a.
Proof. exact (@axiom_39 A a). Qed.
Lemma lem7929833 {A : Type'} (a : tybit1 A) : (term29 A a) = a.
Proof. exact (@lem7929832 A a). Qed.
Lemma lem7929834 {A : Type'} (x : tybit1 A) : (term29 A x) = x.
Proof. exact (@lem7929833 A x). Qed.
Lemma lem7929835 {A : Type'} (P : type1351 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7929836 {A : Type'} (P : type1351 A) (x : tybit1 A) : (term35 A P x) = (P x).
Proof. exact (MK_COMB (@lem7929835 A P) (@lem7929834 A x)). Qed.
Lemma lem7929837 {A : Type'} (x : tybit1 A) (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : P x.
Proof. exact (EQ_MP (@lem7929836 A P x) (@lem7929830 A x P tybit1' _103802' h1 h2 h3)). Qed.
Lemma lem7929838 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : term15 A P) (h2 : _103802' = (term8 A)) (h3 : tybit1' = (term0 A _103802')) : term36 A P.
Proof. exact (fun x : tybit1 A => @lem7929837 A x P tybit1' _103802' h1 h2 h3). Qed.
Lemma lem7929839 {A : Type'} (P : type1351 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : term37 A P.
Proof. exact (fun h0 : term15 A P => @lem7929838 A P tybit1' _103802' h0 h1 h2). Qed.
Lemma lem7929840 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) (h2 : tybit1' = (term0 A _103802')) : term38 A.
Proof. exact (fun P : type1351 A => @lem7929839 A P tybit1' _103802' h1 h2). Qed.
Lemma lem7929841 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term8 A)) : term39 A tybit1' _103802'.
Proof. exact (fun h0 : tybit1' = (term0 A _103802') => @lem7929840 A tybit1' _103802' h1 h0). Qed.
Lemma lem7929842 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (eq_refl (term8 A)). Qed.
Lemma lem7929843 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) : term40 A tybit1' _103802'.
Proof. exact (fun h0 : _103802' = (term8 A) => @lem7929841 A tybit1' _103802' h0). Qed.
Lemma lem7929844 {A : Type'} (tybit1' : type1329 A) : term41 A tybit1'.
Proof. exact (@lem7929843 A tybit1' (term8 A)). Qed.
Lemma lem7929845 {A : Type'} (tybit1' : type1329 A) : term42 A tybit1'.
Proof. exact (@lem7929844 A tybit1' (@lem7929842 A)). Qed.
Lemma lem7929846 {A : Type'} (tybit1' : type1329 A) (h1 : tybit1' = (term43 A)) : tybit1' = (term43 A).
Proof. exact (h1). Qed.
Lemma lem7929847 {A : Type'} (tybit1' : type1329 A) (h1 : tybit1' = (term43 A)) : term38 A.
Proof. exact (@lem7929845 A tybit1' (@lem7929846 A tybit1' h1)). Qed.
Lemma lem7929848 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (eq_refl (term43 A)). Qed.
Lemma lem7929849 {A : Type'} (tybit1' : type1329 A) : term42 A tybit1'.
Proof. exact (fun h0 : tybit1' = (term43 A) => @lem7929847 A tybit1' h0). Qed.
Lemma lem7929850 {A : Type'} : term44 A.
Proof. exact (@lem7929849 A (term43 A)). Qed.
Lemma lem7929851 {A : Type'} : term38 A.
Proof. exact (@lem7929850 A (@lem7929848 A)). Qed.
