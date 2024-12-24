Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_TRANS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3216617 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3216618 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3216617 A s t). Qed.
Lemma lem3216625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216626 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3216625) (@lem3216618 A s t)). Qed.
Lemma lem3216628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3216629 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3216628 A s t). Qed.
Lemma lem3216630 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term0 A t u).
Proof. exact (@lem3216629 A t u). Qed.
Lemma lem3216637 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term3 A s t u) = (term4 A s t u).
Proof. exact (MK_COMB (@lem3216626 A s t) (@lem3216630 A t u)). Qed.
Lemma lem3216640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3216641 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term5 A s t u) = (term6 A s t u).
Proof. exact (MK_COMB (@lem3216640) (@lem3216637 A s t u)). Qed.
Lemma lem3216643 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3216644 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3216643 A s t). Qed.
Lemma lem3216645 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term0 A s u).
Proof. exact (@lem3216644 A s u). Qed.
Lemma lem3216652 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term7 A t s u) = (term8 A t s u).
Proof. exact (MK_COMB (@lem3216641 A s t u) (@lem3216645 A s u)). Qed.
Lemma lem3216655 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term9 A t s) = (term10 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3216652 A t s u)). Qed.
Lemma lem3216656 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216657 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term11 A t s) = (term12 A t s).
Proof. exact (MK_COMB (@lem3216656 A) (@lem3216655 A t s)). Qed.
Lemma lem3216662 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3216657 A t s)). Qed.
Lemma lem3216663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216664 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (MK_COMB (@lem3216663 A) (@lem3216662 A s)). Qed.
Lemma lem3216669 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3216664 A s)). Qed.
Lemma lem3216670 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216671 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (MK_COMB (@lem3216670 A) (@lem3216669 A)). Qed.
Lemma lem3216676 {A : Type'} : (term20 A) = (term19 A).
Proof. exact (SYM (@lem3216671 A)). Qed.
Lemma lem3216700 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216701 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216700 A P x). Qed.
Lemma lem3216702 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3216701 A s x). Qed.
Lemma lem3216703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3216704 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3216703) (@lem3216702 A s x)). Qed.
Lemma lem3216706 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216707 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216706 A P x). Qed.
Lemma lem3216708 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3216707 A t x). Qed.
Lemma lem3216709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term23 A s x t) = (term24 A s t x).
Proof. exact (MK_COMB (@lem3216704 A s x) (@lem3216708 A t x)). Qed.
Lemma lem3216712 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3216709 A s t x)). Qed.
Lemma lem3216713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216714 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term27 A s t).
Proof. exact (MK_COMB (@lem3216713 A) (@lem3216712 A s t)). Qed.
Lemma lem3216719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3216719) (@lem3216714 A s t)). Qed.
Lemma lem3216728 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216729 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216728 A P x). Qed.
Lemma lem3216730 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3216729 A t x). Qed.
Lemma lem3216731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3216732 {A : Type'} (t : A -> Prop) (x : A) : (term21 A x t) = (term22 A t x).
Proof. exact (MK_COMB (@lem3216731) (@lem3216730 A t x)). Qed.
Lemma lem3216734 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216735 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216734 A P x). Qed.
Lemma lem3216736 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3216735 A u x). Qed.
Lemma lem3216737 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term23 A t x u) = (term24 A t u x).
Proof. exact (MK_COMB (@lem3216732 A t x) (@lem3216736 A u x)). Qed.
Lemma lem3216740 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term25 A t u) = (term26 A t u).
Proof. exact (fun_ext (fun x : A => @lem3216737 A t u x)). Qed.
Lemma lem3216741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216742 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term0 A t u) = (term27 A t u).
Proof. exact (MK_COMB (@lem3216741 A) (@lem3216740 A t u)). Qed.
Lemma lem3216747 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term4 A s t u) = (term29 A s t u).
Proof. exact (MK_COMB (@lem3216720 A s t) (@lem3216742 A t u)). Qed.
Lemma lem3216750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3216751 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term6 A s t u) = (term30 A s t u).
Proof. exact (MK_COMB (@lem3216750) (@lem3216747 A s t u)). Qed.
Lemma lem3216759 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216759 A P x). Qed.
Lemma lem3216761 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3216760 A s x). Qed.
Lemma lem3216762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3216763 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3216762) (@lem3216761 A s x)). Qed.
Lemma lem3216765 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216766 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216765 A P x). Qed.
Lemma lem3216767 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3216766 A u x). Qed.
Lemma lem3216768 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term23 A s x u) = (term24 A s u x).
Proof. exact (MK_COMB (@lem3216763 A s x) (@lem3216767 A u x)). Qed.
Lemma lem3216771 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term25 A s u) = (term26 A s u).
Proof. exact (fun_ext (fun x : A => @lem3216768 A s u x)). Qed.
Lemma lem3216772 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216773 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term0 A s u) = (term27 A s u).
Proof. exact (MK_COMB (@lem3216772 A) (@lem3216771 A s u)). Qed.
Lemma lem3216778 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term8 A t s u) = (term31 A t s u).
Proof. exact (MK_COMB (@lem3216751 A s t u) (@lem3216773 A s u)). Qed.
Lemma lem3216781 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term10 A t s) = (term32 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3216778 A t s u)). Qed.
Lemma lem3216782 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216783 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term12 A t s) = (term33 A t s).
Proof. exact (MK_COMB (@lem3216782 A) (@lem3216781 A t s)). Qed.
Lemma lem3216788 {A : Type'} (s : A -> Prop) : (term14 A s) = (term34 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3216783 A t s)). Qed.
Lemma lem3216789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216790 {A : Type'} (s : A -> Prop) : (term16 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3216789 A) (@lem3216788 A s)). Qed.
Lemma lem3216795 {A : Type'} : (term18 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3216790 A s)). Qed.
Lemma lem3216796 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216797 {A : Type'} : (term20 A) = (term37 A).
Proof. exact (MK_COMB (@lem3216796 A) (@lem3216795 A)). Qed.
Lemma lem3216802 {A : Type'} : (term37 A) = (term20 A).
Proof. exact (SYM (@lem3216797 A)). Qed.
Lemma lem3216804 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3216805 {A : Type'} : (term37 A) = (term39 A).
Proof. exact (@lem3216804 (term37 A)). Qed.
Lemma lem3216806 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (SYM (@lem3216805 A)). Qed.
Lemma lem3216807 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem3216810 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem3216811 {A : Type'} : term41 A.
Proof. exact (fun h0 : term39 A => @lem3216810 A h0). Qed.
Lemma lem3216812 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3216813 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem3216814 {A : Type'} (h1 : term39 A) (h2 : term41 A) : term39 A.
Proof. exact (@lem3216812 A h2 (@lem3216813 A h1)). Qed.
Lemma lem3216815 {A : Type'} (h1 : term39 A) : term42 A.
Proof. exact (fun h0 : term41 A => @lem3216814 A h1 h0). Qed.
Lemma lem3216816 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3216817 {A : Type'} (h1 : term39 A) (h2 : term41 A) : term39 A.
Proof. exact (@lem3216815 A h1 (@lem3216816 A h2)). Qed.
Lemma lem3216818 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (fun h0 : term39 A => @lem3216817 A h0 h1). Qed.
Lemma lem3216819 {A : Type'} : term43 A.
Proof. exact (fun h0 : term41 A => @lem3216818 A h0). Qed.
Lemma lem3216822 {A : Type'} : term41 A.
Proof. exact (@lem3216819 A (@lem3216811 A)). Qed.
Lemma lem3216823 {A : Type'} : term41 A.
Proof. exact (@lem3216822 A). Qed.
Lemma lem3216825 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3216826 {A : Type'} : (term39 A) = (term44 A).
Proof. exact (@lem3216825 (term40 A)). Qed.
Lemma lem3216828 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3216829 {A : Type'} : (term44 A) = (term37 A).
Proof. exact (@lem3216828 (term37 A)). Qed.
Lemma lem3216868 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (TRANS (@lem3216826 A) (@lem3216829 A)). Qed.
Lemma lem3216873 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term24 A s u x) = (term24 A s u x).
Proof. exact (eq_refl (term24 A s u x)). Qed.
Lemma lem3216874 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term26 A s u) = (term26 A s u).
Proof. exact (fun_ext (fun x : A => @lem3216873 A s u x)). Qed.
Lemma lem3216875 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216876 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term27 A s u) = (term27 A s u).
Proof. exact (MK_COMB (@lem3216875 A) (@lem3216874 A s u)). Qed.
Lemma lem3216881 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term24 A t u x) = (term24 A t u x).
Proof. exact (eq_refl (term24 A t u x)). Qed.
Lemma lem3216882 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term26 A t u) = (term26 A t u).
Proof. exact (fun_ext (fun x : A => @lem3216881 A t u x)). Qed.
Lemma lem3216883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216884 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term27 A t u) = (term27 A t u).
Proof. exact (MK_COMB (@lem3216883 A) (@lem3216882 A t u)). Qed.
Lemma lem3216889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term24 A s t x) = (term24 A s t x).
Proof. exact (eq_refl (term24 A s t x)). Qed.
Lemma lem3216890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3216889 A s t x)). Qed.
Lemma lem3216891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216892 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term27 A s t).
Proof. exact (MK_COMB (@lem3216891 A) (@lem3216890 A s t)). Qed.
Lemma lem3216893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3216893) (@lem3216892 A s t)). Qed.
Lemma lem3216895 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term29 A s t u) = (term29 A s t u).
Proof. exact (MK_COMB (@lem3216894 A s t) (@lem3216884 A t u)). Qed.
Lemma lem3216896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3216897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term30 A s t u) = (term30 A s t u).
Proof. exact (MK_COMB (@lem3216896) (@lem3216895 A s t u)). Qed.
Lemma lem3216898 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term31 A t s u) = (term31 A t s u).
Proof. exact (MK_COMB (@lem3216897 A s t u) (@lem3216876 A s u)). Qed.
Lemma lem3216899 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term32 A t s) = (term32 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3216898 A t s u)). Qed.
Lemma lem3216900 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216901 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term33 A t s).
Proof. exact (MK_COMB (@lem3216900 A) (@lem3216899 A t s)). Qed.
Lemma lem3216902 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3216901 A t s)). Qed.
Lemma lem3216903 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216904 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3216903 A) (@lem3216902 A s)). Qed.
Lemma lem3216905 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3216904 A s)). Qed.
Lemma lem3216906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216907 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (MK_COMB (@lem3216906 A) (@lem3216905 A)). Qed.
Lemma lem3216956 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (TRANS (@lem3216868 A) (@lem3216907 A)). Qed.
Lemma lem3216957 {A : Type'} : (term37 A) = (term39 A).
Proof. exact (SYM (@lem3216956 A)). Qed.
Lemma lem3216958 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term29 A s t u.
Proof. exact (h1). Qed.
Lemma lem3216961 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3216962 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (term46 A u x).
Proof. exact (@lem3216961 (u x)). Qed.
Lemma lem3216963 {A : Type'} (u : A -> Prop) (x : A) : (term46 A u x) = (u x).
Proof. exact (SYM (@lem3216962 A u x)). Qed.
Lemma lem3216964 {A : Type'} (u : A -> Prop) (x : A) (h1 : term47 A u x) : term47 A u x.
Proof. exact (h1). Qed.
Lemma lem3216971 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term24 A s t x) = (term48 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3216972 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3216971 A s t x)). Qed.
Lemma lem3216973 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216974 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3216973 A) (@lem3216972 A s t)). Qed.
Lemma lem3216981 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term24 A t u x) = (term48 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3216982 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term26 A t u) = (term49 A t u).
Proof. exact (fun_ext (fun x : A => @lem3216981 A t u x)). Qed.
Lemma lem3216983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216984 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term27 A t u) = (term50 A t u).
Proof. exact (MK_COMB (@lem3216983 A) (@lem3216982 A t u)). Qed.
Lemma lem3216985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216986 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term51 A s t).
Proof. exact (MK_COMB (@lem3216985) (@lem3216974 A s t)). Qed.
Lemma lem3217055 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term29 A s t u) = (term52 A s t u).
Proof. exact (MK_COMB (@lem3216986 A s t) (@lem3216984 A t u)). Qed.
Lemma lem3217056 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term52 A s t u.
Proof. exact (EQ_MP (@lem3217055 A s t u) (@lem3216958 A s t u h1)). Qed.
Lemma lem3217062 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3217068 {A : Type'} (u : A -> Prop) (x : A) (h1 : term47 A u x) : term47 A u x.
Proof. exact (h1). Qed.
Lemma lem3217079 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term48 A t u x) = (term48 A t u x).
Proof. exact (eq_refl (term48 A t u x)). Qed.
Lemma lem3217080 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term49 A t u) = (term49 A t u).
Proof. exact (fun_ext (fun x : A => @lem3217079 A t u x)). Qed.
Lemma lem3217081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217082 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term50 A t u) = (term50 A t u).
Proof. exact (MK_COMB (@lem3217081 A) (@lem3217080 A t u)). Qed.
Lemma lem3217093 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term48 A s t x) = (term48 A s t x).
Proof. exact (eq_refl (term48 A s t x)). Qed.
Lemma lem3217094 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217093 A s t x)). Qed.
Lemma lem3217095 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217096 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3217095 A) (@lem3217094 A s t)). Qed.
Lemma lem3217097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3217098 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term51 A s t).
Proof. exact (MK_COMB (@lem3217097) (@lem3217096 A s t)). Qed.
Lemma lem3217099 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term52 A s t u) = (term52 A s t u).
Proof. exact (MK_COMB (@lem3217098 A s t) (@lem3217082 A t u)). Qed.
Lemma lem3217100 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term52 A s t u.
Proof. exact (EQ_MP (@lem3217099 A s t u) (@lem3217056 A s t u h1)). Qed.
Lemma lem3217104 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3217110 {A : Type'} (u : A -> Prop) (x : A) (h1 : term47 A u x) : term47 A u x.
Proof. exact (h1). Qed.
Lemma lem3217111 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term50 A t u.
Proof. exact (proj2 (@lem3217100 A s t u h1)). Qed.
Lemma lem3217112 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term50 A s t.
Proof. exact (proj1 (@lem3217100 A s t u h1)). Qed.
Lemma lem3217116 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3217120 {A : Type'} (u : A -> Prop) (x : A) (h1 : term47 A u x) : term47 A u x.
Proof. exact (h1). Qed.
Lemma lem3217128 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term48 A s t x) = (term48 A s t x).
Proof. exact (eq_refl (term48 A s t x)). Qed.
Lemma lem3217129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217128 A s t x)). Qed.
Lemma lem3217130 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3217130 A) (@lem3217129 A s t)). Qed.
Lemma lem3217133 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term50 A s t.
Proof. exact (EQ_MP (@lem3217132 A s t) (@lem3217112 A s t u h1)). Qed.
Lemma lem3217141 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term48 A t u x) = (term48 A t u x).
Proof. exact (eq_refl (term48 A t u x)). Qed.
Lemma lem3217142 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term49 A t u) = (term49 A t u).
Proof. exact (fun_ext (fun x : A => @lem3217141 A t u x)). Qed.
Lemma lem3217143 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217145 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term50 A t u) = (term50 A t u).
Proof. exact (MK_COMB (@lem3217143 A) (@lem3217142 A t u)). Qed.
Lemma lem3217146 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term50 A t u.
Proof. exact (EQ_MP (@lem3217145 A t u) (@lem3217111 A s t u h1)). Qed.
Lemma lem3217147 {A : Type'} (_33100 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term53 A s t _33100.
Proof. exact (@lem3217133 A s t u h1 _33100). Qed.
Lemma lem3217148 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33100 : A) : (term53 A s t _33100) = (term48 A s t _33100).
Proof. exact (eq_refl (term53 A s t _33100)). Qed.
Lemma lem3217150 {A : Type'} (_33101 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term53 A t u _33101.
Proof. exact (@lem3217146 A s t u h1 _33101). Qed.
Lemma lem3217151 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33101 : A) : (term53 A t u _33101) = (term48 A t u _33101).
Proof. exact (eq_refl (term53 A t u _33101)). Qed.
Lemma lem3217154 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3217156 {A : Type'} (u : A -> Prop) (x : A) (h1 : term47 A u x) : term47 A u x.
Proof. exact (h1). Qed.
Lemma lem3217162 {A : Type'} (_33100 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term48 A s t _33100.
Proof. exact (EQ_MP (@lem3217148 A s t _33100) (@lem3217147 A _33100 s t u h1)). Qed.
Lemma lem3217168 {A : Type'} (_33101 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term48 A t u _33101.
Proof. exact (EQ_MP (@lem3217151 A t u _33101) (@lem3217150 A _33101 s t u h1)). Qed.
Lemma lem3217170 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3217171 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term54 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3217170 A s x h1). Qed.
Lemma lem3217173 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3217174 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (s x).
Proof. exact (@lem3217173 (s x)). Qed.
Lemma lem3217175 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3217174 A s x) (@lem3217171 A s x h1)). Qed.
Lemma lem3217181 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3217182 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : (term48 A s t _33100) = (term56 A t s _33100).
Proof. exact (@lem3217181 (t _33100) (term47 A s _33100)). Qed.
Lemma lem3217188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3217189 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : (term57 A s t _33100) = (term58 A t s _33100).
Proof. exact (MK_COMB (@lem3217188) (@lem3217182 A t s _33100)). Qed.
Lemma lem3217195 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : (term56 A t s _33100) = (term56 A t s _33100).
Proof. exact (eq_refl (term56 A t s _33100)). Qed.
Lemma lem3217196 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : ((term48 A s t _33100) = (term56 A t s _33100)) = ((term56 A t s _33100) = (term56 A t s _33100)).
Proof. exact (MK_COMB (@lem3217189 A t s _33100) (@lem3217195 A t s _33100)). Qed.
Lemma lem3217198 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3217199 (x : Prop) : (x = x) = True.
Proof. exact (@lem3217198 Prop x). Qed.
Lemma lem3217200 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : ((term56 A t s _33100) = (term56 A t s _33100)) = True.
Proof. exact (@lem3217199 (term56 A t s _33100)). Qed.
Lemma lem3217201 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : ((term48 A s t _33100) = (term56 A t s _33100)) = True.
Proof. exact (TRANS (@lem3217196 A t s _33100) (@lem3217200 A t s _33100)). Qed.
Lemma lem3217202 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : True = ((term48 A s t _33100) = (term56 A t s _33100)).
Proof. exact (SYM (@lem3217201 A t s _33100)). Qed.
Lemma lem3217203 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33100 : A) : (term48 A s t _33100) = (term56 A t s _33100).
Proof. exact (EQ_MP (@lem3217202 A t s _33100) (@lem0)). Qed.
Lemma lem3217204 {A : Type'} (_33100 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term56 A t s _33100.
Proof. exact (EQ_MP (@lem3217203 A t s _33100) (@lem3217162 A _33100 s t u h1)). Qed.
Lemma lem3217206 (b : Prop) (a : Prop) : (a \/ b) = (term59 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3217207 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33100 : A) : (term56 A t s _33100) = (term60 A s t _33100).
Proof. exact (@lem3217206 (term47 A s _33100) (t _33100)). Qed.
Lemma lem3217209 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3217210 {A : Type'} (s : A -> Prop) (_33100 : A) : (term61 A s _33100) = (s _33100).
Proof. exact (@lem3217209 (s _33100)). Qed.
Lemma lem3217211 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217212 {A : Type'} (s : A -> Prop) (_33100 : A) : (term62 A s _33100) = (term22 A s _33100).
Proof. exact (MK_COMB (@lem3217211) (@lem3217210 A s _33100)). Qed.
Lemma lem3217213 {A : Type'} (t : A -> Prop) (_33100 : A) : (t _33100) = (t _33100).
Proof. exact (eq_refl (t _33100)). Qed.
Lemma lem3217214 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33100 : A) : (term60 A s t _33100) = (term24 A s t _33100).
Proof. exact (MK_COMB (@lem3217212 A s _33100) (@lem3217213 A t _33100)). Qed.
Lemma lem3217215 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33100 : A) : (term56 A t s _33100) = (term24 A s t _33100).
Proof. exact (TRANS (@lem3217207 A s t _33100) (@lem3217214 A s t _33100)). Qed.
Lemma lem3217218 {A : Type'} (_33100 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A s t _33100.
Proof. exact (EQ_MP (@lem3217215 A s t _33100) (@lem3217204 A _33100 s t u h1)). Qed.
Lemma lem3217219 {A : Type'} (_33100 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A s t _33100.
Proof. exact (@lem3217218 A _33100 s t u h1). Qed.
Lemma lem3217220 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A s t x.
Proof. exact (@lem3217219 A x s t u h1). Qed.
Lemma lem3217223 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : t x.
Proof. exact (@lem3217220 A x s t u h2 (@lem3217175 A s x h1)). Qed.
Lemma lem3217224 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : term54 A t x.
Proof. exact (fun h0 : term47 A t x => @lem3217223 A x s t u h1 h2). Qed.
Lemma lem3217226 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3217227 {A : Type'} (t : A -> Prop) (x : A) : (term54 A t x) = (t x).
Proof. exact (@lem3217226 (t x)). Qed.
Lemma lem3217228 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : t x.
Proof. exact (EQ_MP (@lem3217227 A t x) (@lem3217224 A x s t u h1 h2)). Qed.
Lemma lem3217234 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3217235 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : (term48 A t u _33101) = (term56 A u t _33101).
Proof. exact (@lem3217234 (u _33101) (term47 A t _33101)). Qed.
Lemma lem3217241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3217242 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : (term57 A t u _33101) = (term58 A u t _33101).
Proof. exact (MK_COMB (@lem3217241) (@lem3217235 A u t _33101)). Qed.
Lemma lem3217248 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : (term56 A u t _33101) = (term56 A u t _33101).
Proof. exact (eq_refl (term56 A u t _33101)). Qed.
Lemma lem3217249 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : ((term48 A t u _33101) = (term56 A u t _33101)) = ((term56 A u t _33101) = (term56 A u t _33101)).
Proof. exact (MK_COMB (@lem3217242 A u t _33101) (@lem3217248 A u t _33101)). Qed.
Lemma lem3217251 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3217252 (x : Prop) : (x = x) = True.
Proof. exact (@lem3217251 Prop x). Qed.
Lemma lem3217253 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : ((term56 A u t _33101) = (term56 A u t _33101)) = True.
Proof. exact (@lem3217252 (term56 A u t _33101)). Qed.
Lemma lem3217254 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : ((term48 A t u _33101) = (term56 A u t _33101)) = True.
Proof. exact (TRANS (@lem3217249 A u t _33101) (@lem3217253 A u t _33101)). Qed.
Lemma lem3217255 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : True = ((term48 A t u _33101) = (term56 A u t _33101)).
Proof. exact (SYM (@lem3217254 A u t _33101)). Qed.
Lemma lem3217256 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33101 : A) : (term48 A t u _33101) = (term56 A u t _33101).
Proof. exact (EQ_MP (@lem3217255 A u t _33101) (@lem0)). Qed.
Lemma lem3217257 {A : Type'} (_33101 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term56 A u t _33101.
Proof. exact (EQ_MP (@lem3217256 A u t _33101) (@lem3217168 A _33101 s t u h1)). Qed.
Lemma lem3217259 (b : Prop) (a : Prop) : (a \/ b) = (term59 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3217260 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33101 : A) : (term56 A u t _33101) = (term60 A t u _33101).
Proof. exact (@lem3217259 (term47 A t _33101) (u _33101)). Qed.
Lemma lem3217262 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3217263 {A : Type'} (t : A -> Prop) (_33101 : A) : (term61 A t _33101) = (t _33101).
Proof. exact (@lem3217262 (t _33101)). Qed.
Lemma lem3217264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217265 {A : Type'} (t : A -> Prop) (_33101 : A) : (term62 A t _33101) = (term22 A t _33101).
Proof. exact (MK_COMB (@lem3217264) (@lem3217263 A t _33101)). Qed.
Lemma lem3217266 {A : Type'} (u : A -> Prop) (_33101 : A) : (u _33101) = (u _33101).
Proof. exact (eq_refl (u _33101)). Qed.
Lemma lem3217267 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33101 : A) : (term60 A t u _33101) = (term24 A t u _33101).
Proof. exact (MK_COMB (@lem3217265 A t _33101) (@lem3217266 A u _33101)). Qed.
Lemma lem3217268 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33101 : A) : (term56 A u t _33101) = (term24 A t u _33101).
Proof. exact (TRANS (@lem3217260 A t u _33101) (@lem3217267 A t u _33101)). Qed.
Lemma lem3217271 {A : Type'} (_33101 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A t u _33101.
Proof. exact (EQ_MP (@lem3217268 A t u _33101) (@lem3217257 A _33101 s t u h1)). Qed.
Lemma lem3217272 {A : Type'} (_33101 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A t u _33101.
Proof. exact (@lem3217271 A _33101 s t u h1). Qed.
Lemma lem3217273 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A t u x.
Proof. exact (@lem3217272 A x s t u h1). Qed.
Lemma lem3217276 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : u x.
Proof. exact (@lem3217273 A x s t u h2 (@lem3217228 A x s t u h1 h2)). Qed.
Lemma lem3217277 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : term54 A u x.
Proof. exact (fun h0 : term47 A u x => @lem3217276 A x s t u h1 h2). Qed.
Lemma lem3217279 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3217280 {A : Type'} (u : A -> Prop) (x : A) : (term54 A u x) = (u x).
Proof. exact (@lem3217279 (u x)). Qed.
Lemma lem3217281 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : u x.
Proof. exact (EQ_MP (@lem3217280 A u x) (@lem3217277 A x s t u h1 h2)). Qed.
Lemma lem3217284 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3217286 {A : Type'} (u : A -> Prop) (x : A) : (term47 A u x) = (term63 A u x).
Proof. exact (@lem3217284 (u x)). Qed.
Lemma lem3217289 {A : Type'} (u : A -> Prop) (x : A) (h1 : term47 A u x) : term63 A u x.
Proof. exact (EQ_MP (@lem3217286 A u x) (@lem3217156 A u x h1)). Qed.
Lemma lem3217292 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (@lem3217289 A u x h1 (@lem3217281 A x s t u h2 h3)). Qed.
Lemma lem3217293 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : term64.
Proof. exact (fun h0 : ~ False => @lem3217292 A x s t u h1 h2 h3). Qed.
Lemma lem3217295 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3217296 : term64 = False.
Proof. exact (@lem3217295 False). Qed.
Lemma lem3217297 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217296) (@lem3217293 A x s t u h1 h2 h3)). Qed.
Lemma lem3217298 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (term47 A u x) = False.
Proof. exact (prop_ext (fun h4 : term47 A u x => @lem3217297 A x s t u h1 h2 h3) (fun h4 : False => @lem3217156 A u x h1)). Qed.
Lemma lem3217299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217298 A x s t u h1 h2 h3) (@lem3217156 A u x h1)). Qed.
Lemma lem3217300 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3217299 A x s t u h1 h2 h3) (fun h4 : False => @lem3217154 A s x h2)). Qed.
Lemma lem3217301 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217300 A x s t u h1 h2 h3) (@lem3217154 A s x h2)). Qed.
Lemma lem3217302 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (term47 A u x) = False.
Proof. exact (prop_ext (fun h4 : term47 A u x => @lem3217301 A x s t u h1 h2 h3) (fun h4 : False => @lem3217120 A u x h1)). Qed.
Lemma lem3217303 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217302 A x s t u h1 h2 h3) (@lem3217120 A u x h1)). Qed.
Lemma lem3217304 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3217303 A x s t u h1 h2 h3) (fun h4 : False => @lem3217116 A s x h2)). Qed.
Lemma lem3217305 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217304 A x s t u h1 h2 h3) (@lem3217116 A s x h2)). Qed.
Lemma lem3217306 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (term47 A u x) = False.
Proof. exact (prop_ext (fun h4 : term47 A u x => @lem3217305 A x s t u h1 h2 h3) (fun h4 : False => @lem3217120 A u x h1)). Qed.
Lemma lem3217307 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217306 A x s t u h1 h2 h3) (@lem3217120 A u x h1)). Qed.
Lemma lem3217308 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3217307 A x s t u h1 h2 h3) (fun h4 : False => @lem3217116 A s x h2)). Qed.
Lemma lem3217309 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217308 A x s t u h1 h2 h3) (@lem3217116 A s x h2)). Qed.
Lemma lem3217310 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (term47 A u x) = False.
Proof. exact (prop_ext (fun h4 : term47 A u x => @lem3217309 A x s t u h1 h2 h3) (fun h4 : False => @lem3217110 A u x h1)). Qed.
Lemma lem3217311 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217310 A x s t u h1 h2 h3) (@lem3217110 A u x h1)). Qed.
Lemma lem3217312 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3217311 A x s t u h1 h2 h3) (fun h4 : False => @lem3217104 A s x h2)). Qed.
Lemma lem3217313 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217312 A x s t u h1 h2 h3) (@lem3217104 A s x h2)). Qed.
Lemma lem3217314 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (term47 A u x) = False.
Proof. exact (prop_ext (fun h4 : term47 A u x => @lem3217313 A x s t u h1 h2 h3) (fun h4 : False => @lem3217068 A u x h1)). Qed.
Lemma lem3217315 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217314 A x s t u h1 h2 h3) (@lem3217068 A u x h1)). Qed.
Lemma lem3217316 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3217315 A x s t u h1 h2 h3) (fun h4 : False => @lem3217062 A s x h2)). Qed.
Lemma lem3217317 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217316 A x s t u h1 h2 h3) (@lem3217062 A s x h2)). Qed.
Lemma lem3217318 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : (term47 A u x) = False.
Proof. exact (prop_ext (fun h4 : term47 A u x => @lem3217317 A x s t u h1 h2 h3) (fun h4 : False => @lem3216964 A u x h1)). Qed.
Lemma lem3217319 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A u x) (h2 : s x) (h3 : term29 A s t u) : False.
Proof. exact (EQ_MP (@lem3217318 A x s t u h1 h2 h3) (@lem3216964 A u x h1)). Qed.
Lemma lem3217320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : term46 A u x.
Proof. exact (fun h0 : term47 A u x => @lem3217319 A x s t u h0 h1 h2). Qed.
Lemma lem3217321 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term29 A s t u) : u x.
Proof. exact (EQ_MP (@lem3216963 A u x) (@lem3217320 A x s t u h1 h2)). Qed.
Lemma lem3217322 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term24 A s u x.
Proof. exact (fun h0 : s x => @lem3217321 A x s t u h0 h1). Qed.
Lemma lem3217327 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term29 A s t u) : term27 A s u.
Proof. exact (fun x : A => @lem3217322 A x s t u h1). Qed.
Lemma lem3217328 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term31 A t s u.
Proof. exact (fun h0 : term29 A s t u => @lem3217327 A s t u h0). Qed.
Lemma lem3217333 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term33 A t s.
Proof. exact (fun u : A -> Prop => @lem3217328 A t s u). Qed.
Lemma lem3217338 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (fun t : A -> Prop => @lem3217333 A t s). Qed.
Lemma lem3217343 {A : Type'} : term37 A.
Proof. exact (fun s : A -> Prop => @lem3217338 A s). Qed.
Lemma lem3217344 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem3216957 A) (@lem3217343 A)). Qed.
Lemma lem3217346 {A : Type'} : term39 A.
Proof. exact (@lem3216823 A (@lem3217344 A)). Qed.
Lemma lem3217347 {A : Type'} (h1 : term40 A) : False.
Proof. exact (@lem3217346 A (@lem3216807 A h1)). Qed.
Lemma lem3217348 {A : Type'} (h1 : term40 A) : (term40 A) = False.
Proof. exact (prop_ext (fun h2 : term40 A => @lem3217347 A h1) (fun h2 : False => @lem3216807 A h1)). Qed.
Lemma lem3217349 {A : Type'} (h1 : term40 A) : False.
Proof. exact (EQ_MP (@lem3217348 A h1) (@lem3216807 A h1)). Qed.
Lemma lem3217350 {A : Type'} : term39 A.
Proof. exact (fun h0 : term40 A => @lem3217349 A h0). Qed.
Lemma lem3217351 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem3216806 A) (@lem3217350 A)). Qed.
Lemma lem3217352 {A : Type'} : term20 A.
Proof. exact (EQ_MP (@lem3216802 A) (@lem3217351 A)). Qed.
Lemma lem3217353 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem3216676 A) (@lem3217352 A)). Qed.
