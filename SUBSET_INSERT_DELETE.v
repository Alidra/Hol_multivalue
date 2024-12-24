Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_INSERT_DELETE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3310606 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3310607 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3310608 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3310607 t1) (@lem3310606 t1)). Qed.
Lemma lem3310609 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3310608 t1 t2). Qed.
Lemma lem3310610 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3310611 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3310610 t1 t2) (@lem3310609 t1 t2)). Qed.
Lemma lem3310612 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3310611 t1 t2 t3). Qed.
Lemma lem3310613 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3310614 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3310613 t1 t2 t3) (@lem3310612 t1 t2 t3)). Qed.
Lemma lem3310615 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3310614 t1 t2 t3)). Qed.
Lemma lem3310633 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3310634 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3310633 A s t). Qed.
Lemma lem3310635 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A s x t) = (term9 A s x t).
Proof. exact (@lem3310634 A s (@INSERT A x t)). Qed.
Lemma lem3310642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3310643 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A s x t) = (term11 A s x t).
Proof. exact (MK_COMB (@lem3310642) (@lem3310635 A s x t)). Qed.
Lemma lem3310645 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3310646 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3310645 A s t). Qed.
Lemma lem3310647 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s x t) = (term13 A s x t).
Proof. exact (@lem3310646 A (@DELETE A s x) t). Qed.
Lemma lem3310654 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term8 A s x t) = (term12 A s x t)) = ((term9 A s x t) = (term13 A s x t)).
Proof. exact (MK_COMB (@lem3310643 A s x t) (@lem3310647 A s x t)). Qed.
Lemma lem3310659 {A : Type'} (s : A -> Prop) (x : A) : (term14 A s x) = (term15 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3310654 A s x t)). Qed.
Lemma lem3310660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3310661 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term17 A s x).
Proof. exact (MK_COMB (@lem3310660 A) (@lem3310659 A s x)). Qed.
Lemma lem3310666 {A : Type'} (x : A) : (term18 A x) = (term19 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3310661 A s x)). Qed.
Lemma lem3310667 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3310668 {A : Type'} (x : A) : (term20 A x) = (term21 A x).
Proof. exact (MK_COMB (@lem3310667 A) (@lem3310666 A x)). Qed.
Lemma lem3310673 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3310668 A x)). Qed.
Lemma lem3310674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310675 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem3310674 A) (@lem3310673 A)). Qed.
Lemma lem3310680 {A : Type'} : (term25 A) = (term24 A).
Proof. exact (SYM (@lem3310675 A)). Qed.
Lemma lem3310702 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3310703 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3310702 A P x). Qed.
Lemma lem3310704 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3310703 A s x'). Qed.
Lemma lem3310705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3310706 {A : Type'} (s : A -> Prop) (x' : A) : (term26 A x' s) = (term27 A s x').
Proof. exact (MK_COMB (@lem3310705) (@lem3310704 A s x')). Qed.
Lemma lem3310708 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term28 A x y s) = (term29 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3310709 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term28 A x y s) = (term29 A y x s).
Proof. exact (@lem3310708 A y x s). Qed.
Lemma lem3310710 {A : Type'} (x : A) (x' : A) (t : A -> Prop) : (term28 A x' x t) = (term29 A x x' t).
Proof. exact (@lem3310709 A x x' t). Qed.
Lemma lem3310716 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3310717 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3310716 A P x). Qed.
Lemma lem3310718 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3310717 A t x'). Qed.
Lemma lem3310719 {A : Type'} (x' : A) (x : A) : (term30 A x' x) = (term30 A x' x).
Proof. exact (eq_refl (term30 A x' x)). Qed.
Lemma lem3310720 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term29 A x x' t) = (term31 A x t x').
Proof. exact (MK_COMB (@lem3310719 A x' x) (@lem3310718 A t x')). Qed.
Lemma lem3310723 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term28 A x' x t) = (term31 A x t x').
Proof. exact (TRANS (@lem3310710 A x x' t) (@lem3310720 A x t x')). Qed.
Lemma lem3310724 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term32 A s x' x t) = (term33 A s x t x').
Proof. exact (MK_COMB (@lem3310706 A s x') (@lem3310723 A x t x')). Qed.
Lemma lem3310727 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term34 A s x t) = (term35 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3310724 A s x t x')). Qed.
Lemma lem3310728 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310729 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term9 A s x t) = (term36 A s x t).
Proof. exact (MK_COMB (@lem3310728 A) (@lem3310727 A s x t)). Qed.
Lemma lem3310734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3310735 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s x t) = (term37 A s x t).
Proof. exact (MK_COMB (@lem3310734) (@lem3310729 A s x t)). Qed.
Lemma lem3310743 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term38 A x s y) = (term39 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3310744 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term38 A x s y) = (term39 A s x y).
Proof. exact (@lem3310743 A s x y). Qed.
Lemma lem3310745 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term38 A x' s x) = (term39 A s x' x).
Proof. exact (@lem3310744 A s x' x). Qed.
Lemma lem3310749 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3310750 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3310749 A P x). Qed.
Lemma lem3310751 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3310750 A s x'). Qed.
Lemma lem3310752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3310753 {A : Type'} (s : A -> Prop) (x' : A) : (term40 A x' s) = (term41 A s x').
Proof. exact (MK_COMB (@lem3310752) (@lem3310751 A s x')). Qed.
Lemma lem3310756 {A : Type'} (x' : A) (x : A) : (term42 A x' x) = (term42 A x' x).
Proof. exact (eq_refl (term42 A x' x)). Qed.
Lemma lem3310757 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term39 A s x' x) = (term43 A s x' x).
Proof. exact (MK_COMB (@lem3310753 A s x') (@lem3310756 A x' x)). Qed.
Lemma lem3310760 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term38 A x' s x) = (term43 A s x' x).
Proof. exact (TRANS (@lem3310745 A s x' x) (@lem3310757 A s x' x)). Qed.
Lemma lem3310761 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3310762 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term44 A x' s x) = (term45 A s x' x).
Proof. exact (MK_COMB (@lem3310761) (@lem3310760 A s x' x)). Qed.
Lemma lem3310764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3310765 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3310764 A P x). Qed.
Lemma lem3310766 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3310765 A t x'). Qed.
Lemma lem3310767 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term46 A s x x' t) = (term47 A s x t x').
Proof. exact (MK_COMB (@lem3310762 A s x' x) (@lem3310766 A t x')). Qed.
Lemma lem3310770 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term48 A s x t) = (term49 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3310767 A s x t x')). Qed.
Lemma lem3310771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310772 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s x t) = (term50 A s x t).
Proof. exact (MK_COMB (@lem3310771 A) (@lem3310770 A s x t)). Qed.
Lemma lem3310777 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A s x t) = (term13 A s x t)) = ((term36 A s x t) = (term50 A s x t)).
Proof. exact (MK_COMB (@lem3310735 A s x t) (@lem3310772 A s x t)). Qed.
Lemma lem3310780 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = (term51 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3310777 A s x t)). Qed.
Lemma lem3310781 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3310782 {A : Type'} (s : A -> Prop) (x : A) : (term17 A s x) = (term52 A s x).
Proof. exact (MK_COMB (@lem3310781 A) (@lem3310780 A s x)). Qed.
Lemma lem3310787 {A : Type'} (x : A) : (term19 A x) = (term53 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3310782 A s x)). Qed.
Lemma lem3310788 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3310789 {A : Type'} (x : A) : (term21 A x) = (term54 A x).
Proof. exact (MK_COMB (@lem3310788 A) (@lem3310787 A x)). Qed.
Lemma lem3310794 {A : Type'} : (term23 A) = (term55 A).
Proof. exact (fun_ext (fun x : A => @lem3310789 A x)). Qed.
Lemma lem3310795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310796 {A : Type'} : (term25 A) = (term56 A).
Proof. exact (MK_COMB (@lem3310795 A) (@lem3310794 A)). Qed.
Lemma lem3310801 {A : Type'} : (term56 A) = (term25 A).
Proof. exact (SYM (@lem3310796 A)). Qed.
Lemma lem3310803 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3310804 {A : Type'} : (term56 A) = (term58 A).
Proof. exact (@lem3310803 (term56 A)). Qed.
Lemma lem3310805 {A : Type'} : (term58 A) = (term56 A).
Proof. exact (SYM (@lem3310804 A)). Qed.
Lemma lem3310806 {A : Type'} (h1 : term59 A) : term59 A.
Proof. exact (h1). Qed.
Lemma lem3310809 {A : Type'} (h1 : term58 A) : term58 A.
Proof. exact (h1). Qed.
Lemma lem3310810 {A : Type'} : term60 A.
Proof. exact (fun h0 : term58 A => @lem3310809 A h0). Qed.
Lemma lem3310811 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (h1). Qed.
Lemma lem3310812 {A : Type'} (h1 : term58 A) : term58 A.
Proof. exact (h1). Qed.
Lemma lem3310813 {A : Type'} (h1 : term58 A) (h2 : term60 A) : term58 A.
Proof. exact (@lem3310811 A h2 (@lem3310812 A h1)). Qed.
Lemma lem3310814 {A : Type'} (h1 : term58 A) : term61 A.
Proof. exact (fun h0 : term60 A => @lem3310813 A h1 h0). Qed.
Lemma lem3310815 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (h1). Qed.
Lemma lem3310816 {A : Type'} (h1 : term58 A) (h2 : term60 A) : term58 A.
Proof. exact (@lem3310814 A h1 (@lem3310815 A h2)). Qed.
Lemma lem3310817 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (fun h0 : term58 A => @lem3310816 A h0 h1). Qed.
Lemma lem3310818 {A : Type'} : term62 A.
Proof. exact (fun h0 : term60 A => @lem3310817 A h0). Qed.
Lemma lem3310821 {A : Type'} : term60 A.
Proof. exact (@lem3310818 A (@lem3310810 A)). Qed.
Lemma lem3310822 {A : Type'} : term60 A.
Proof. exact (@lem3310821 A). Qed.
Lemma lem3310824 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3310825 {A : Type'} : (term58 A) = (term63 A).
Proof. exact (@lem3310824 (term59 A)). Qed.
Lemma lem3310827 (t : Prop) : (term64 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3310828 {A : Type'} : (term63 A) = (term56 A).
Proof. exact (@lem3310827 (term56 A)). Qed.
Lemma lem3310861 {A : Type'} : (term58 A) = (term56 A).
Proof. exact (TRANS (@lem3310825 A) (@lem3310828 A)). Qed.
Lemma lem3310872 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term47 A s x t x') = (term47 A s x t x').
Proof. exact (eq_refl (term47 A s x t x')). Qed.
Lemma lem3310873 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A s x t) = (term49 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3310872 A s x t x')). Qed.
Lemma lem3310874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310875 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term50 A s x t) = (term50 A s x t).
Proof. exact (MK_COMB (@lem3310874 A) (@lem3310873 A s x t)). Qed.
Lemma lem3310884 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term33 A s x t x') = (term33 A s x t x').
Proof. exact (eq_refl (term33 A s x t x')). Qed.
Lemma lem3310885 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A s x t) = (term35 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3310884 A s x t x')). Qed.
Lemma lem3310886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310887 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A s x t) = (term36 A s x t).
Proof. exact (MK_COMB (@lem3310886 A) (@lem3310885 A s x t)). Qed.
Lemma lem3310888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3310889 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A s x t) = (term37 A s x t).
Proof. exact (MK_COMB (@lem3310888) (@lem3310887 A s x t)). Qed.
Lemma lem3310890 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term36 A s x t) = (term50 A s x t)) = ((term36 A s x t) = (term50 A s x t)).
Proof. exact (MK_COMB (@lem3310889 A s x t) (@lem3310875 A s x t)). Qed.
Lemma lem3310891 {A : Type'} (s : A -> Prop) (x : A) : (term51 A s x) = (term51 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3310890 A s x t)). Qed.
Lemma lem3310892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3310893 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term52 A s x).
Proof. exact (MK_COMB (@lem3310892 A) (@lem3310891 A s x)). Qed.
Lemma lem3310894 {A : Type'} (x : A) : (term53 A x) = (term53 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3310893 A s x)). Qed.
Lemma lem3310895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3310896 {A : Type'} (x : A) : (term54 A x) = (term54 A x).
Proof. exact (MK_COMB (@lem3310895 A) (@lem3310894 A x)). Qed.
Lemma lem3310897 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun x : A => @lem3310896 A x)). Qed.
Lemma lem3310898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310899 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem3310898 A) (@lem3310897 A)). Qed.
Lemma lem3310940 {A : Type'} : (term58 A) = (term56 A).
Proof. exact (TRANS (@lem3310861 A) (@lem3310899 A)). Qed.
Lemma lem3310941 {A : Type'} : (term56 A) = (term58 A).
Proof. exact (SYM (@lem3310940 A)). Qed.
Lemma lem3310943 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3310944 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term36 A s x t) = (term50 A s x t)) = (term65 A s x t).
Proof. exact (@lem3310943 ((term36 A s x t) = (term50 A s x t))). Qed.
Lemma lem3310945 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term65 A s x t) = ((term36 A s x t) = (term50 A s x t)).
Proof. exact (SYM (@lem3310944 A s x t)). Qed.
Lemma lem3310946 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term66 A s x t) : term66 A s x t.
Proof. exact (h1). Qed.
Lemma lem3310957 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term67 A x t x') = (term68 A x t x').
Proof. exact (@lem17160 (x' = x) (t x')). Qed.
Lemma lem3310962 {A : Type'} (s : A -> Prop) (x' : A) : (term41 A s x') = (term41 A s x').
Proof. exact (eq_refl (term41 A s x')). Qed.
Lemma lem3310963 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term69 A s x t x') = (term70 A s x t x').
Proof. exact (MK_COMB (@lem3310962 A s x') (@lem3310957 A x t x')). Qed.
Lemma lem3310964 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term71 A s x t x') = (term69 A s x t x').
Proof. exact (@lem17362 (s x') (term31 A x t x')). Qed.
Lemma lem3310965 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term71 A s x t x') = (term70 A s x t x').
Proof. exact (TRANS (@lem3310964 A s x t x') (@lem3310963 A s x t x')). Qed.
Lemma lem3310970 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term33 A s x t x') = (term72 A s x t x').
Proof. exact (@lem17265 (s x') (term31 A x t x')). Qed.
Lemma lem3310971 {A : Type'} (P : A -> Prop) : (term73 A P) = (term74 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3310972 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A s x t) = (term76 A s x t).
Proof. exact (@lem3310971 A (term35 A s x t)). Qed.
Lemma lem3310973 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term77 A s x t x') = (term33 A s x t x').
Proof. exact (eq_refl (term77 A s x t x')). Qed.
Lemma lem3310974 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3310975 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term78 A s x t x') = (term71 A s x t x').
Proof. exact (MK_COMB (@lem3310974) (@lem3310973 A s x t x')). Qed.
Lemma lem3310976 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term78 A s x t x') = (term70 A s x t x').
Proof. exact (TRANS (@lem3310975 A s x t x') (@lem3310965 A s x t x')). Qed.
Lemma lem3310977 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term79 A s x t) = (term80 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3310976 A s x t x')). Qed.
Lemma lem3310978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3310979 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term76 A s x t) = (term81 A s x t).
Proof. exact (MK_COMB (@lem3310978 A) (@lem3310977 A s x t)). Qed.
Lemma lem3310980 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A s x t) = (term81 A s x t).
Proof. exact (TRANS (@lem3310972 A s x t) (@lem3310979 A s x t)). Qed.
Lemma lem3310981 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A s x t) = (term82 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3310970 A s x t x')). Qed.
Lemma lem3310982 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310983 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A s x t) = (term83 A s x t).
Proof. exact (MK_COMB (@lem3310982 A) (@lem3310981 A s x t)). Qed.
Lemma lem3310989 {A : Type'} (x' : A) (x : A) : (term84 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3310991 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term85 A s x').
Proof. exact (eq_refl (term85 A s x')). Qed.
Lemma lem3310992 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term86 A s x' x) = (term87 A s x' x).
Proof. exact (MK_COMB (@lem3310991 A s x') (@lem3310989 A x' x)). Qed.
Lemma lem3310993 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term88 A s x' x) = (term86 A s x' x).
Proof. exact (@lem17045 (s x') (term42 A x' x)). Qed.
Lemma lem3310994 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term88 A s x' x) = (term87 A s x' x).
Proof. exact (TRANS (@lem3310993 A s x' x) (@lem3310992 A s x' x)). Qed.
Lemma lem3310999 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (t x').
Proof. exact (eq_refl (t x')). Qed.
Lemma lem3311004 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term89 A s x t x') = (term90 A s x t x').
Proof. exact (@lem17362 (term43 A s x' x) (t x')). Qed.
Lemma lem3311005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3311006 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term91 A s x' x) = (term92 A s x' x).
Proof. exact (MK_COMB (@lem3311005) (@lem3310994 A s x' x)). Qed.
Lemma lem3311007 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term93 A s x t x') = (term94 A s x t x').
Proof. exact (MK_COMB (@lem3311006 A s x' x) (@lem3310999 A t x')). Qed.
Lemma lem3311008 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term47 A s x t x') = (term93 A s x t x').
Proof. exact (@lem17265 (term43 A s x' x) (t x')). Qed.
Lemma lem3311009 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term47 A s x t x') = (term94 A s x t x').
Proof. exact (TRANS (@lem3311008 A s x t x') (@lem3311007 A s x t x')). Qed.
Lemma lem3311010 {A : Type'} (P : A -> Prop) : (term73 A P) = (term74 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3311011 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term95 A s x t) = (term96 A s x t).
Proof. exact (@lem3311010 A (term49 A s x t)). Qed.
Lemma lem3311012 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term97 A s x t x') = (term47 A s x t x').
Proof. exact (eq_refl (term97 A s x t x')). Qed.
Lemma lem3311013 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3311014 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term98 A s x t x') = (term89 A s x t x').
Proof. exact (MK_COMB (@lem3311013) (@lem3311012 A s x t x')). Qed.
Lemma lem3311015 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term98 A s x t x') = (term90 A s x t x').
Proof. exact (TRANS (@lem3311014 A s x t x') (@lem3311004 A s x t x')). Qed.
Lemma lem3311016 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term99 A s x t) = (term100 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311015 A s x t x')). Qed.
Lemma lem3311017 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311018 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term96 A s x t) = (term101 A s x t).
Proof. exact (MK_COMB (@lem3311017 A) (@lem3311016 A s x t)). Qed.
Lemma lem3311019 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term95 A s x t) = (term101 A s x t).
Proof. exact (TRANS (@lem3311011 A s x t) (@lem3311018 A s x t)). Qed.
Lemma lem3311020 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A s x t) = (term102 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311009 A s x t x')). Qed.
Lemma lem3311021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3311022 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term50 A s x t) = (term103 A s x t).
Proof. exact (MK_COMB (@lem3311021 A) (@lem3311020 A s x t)). Qed.
Lemma lem3311023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311024 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term104 A s x t) = (term105 A s x t).
Proof. exact (MK_COMB (@lem3311023) (@lem3310980 A s x t)). Qed.
Lemma lem3311025 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term106 A s x t) = (term107 A s x t).
Proof. exact (MK_COMB (@lem3311024 A s x t) (@lem3311022 A s x t)). Qed.
Lemma lem3311026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311027 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term108 A s x t) = (term109 A s x t).
Proof. exact (MK_COMB (@lem3311026) (@lem3310983 A s x t)). Qed.
Lemma lem3311028 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term110 A s x t) = (term111 A s x t).
Proof. exact (MK_COMB (@lem3311027 A s x t) (@lem3311019 A s x t)). Qed.
Lemma lem3311029 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3311030 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A s x t) = (term113 A s x t).
Proof. exact (MK_COMB (@lem3311029) (@lem3311028 A s x t)). Qed.
Lemma lem3311031 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A s x t) = (term115 A s x t).
Proof. exact (MK_COMB (@lem3311030 A s x t) (@lem3311025 A s x t)). Qed.
Lemma lem3311032 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term114 A s x t).
Proof. exact (@lem17646 (term36 A s x t) (term50 A s x t)). Qed.
Lemma lem3311033 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term115 A s x t).
Proof. exact (TRANS (@lem3311032 A s x t) (@lem3311031 A s x t)). Qed.
Lemma lem3311192 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3311193 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (@lem3311192 A P Q). Qed.
Lemma lem3311194 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term118 A s x t) = (term119 A s x t).
Proof. exact (@lem3311193 A (term83 A s x t) (term100 A s x t)). Qed.
Lemma lem3311195 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term120 A s x t x') = (term90 A s x t x').
Proof. exact (eq_refl (term120 A s x t x')). Qed.
Lemma lem3311196 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term121 A s x t) = (term100 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311195 A s x t x')). Qed.
Lemma lem3311197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311198 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term122 A s x t) = (term101 A s x t).
Proof. exact (MK_COMB (@lem3311197 A) (@lem3311196 A s x t)). Qed.
Lemma lem3311199 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term109 A s x t) = (term109 A s x t).
Proof. exact (eq_refl (term109 A s x t)). Qed.
Lemma lem3311200 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term118 A s x t) = (term111 A s x t).
Proof. exact (MK_COMB (@lem3311199 A s x t) (@lem3311198 A s x t)). Qed.
Lemma lem3311201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3311202 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term123 A s x t) = (term124 A s x t).
Proof. exact (MK_COMB (@lem3311201) (@lem3311200 A s x t)). Qed.
Lemma lem3311203 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term120 A s x t x') = (term90 A s x t x').
Proof. exact (eq_refl (term120 A s x t x')). Qed.
Lemma lem3311204 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term109 A s x t) = (term109 A s x t).
Proof. exact (eq_refl (term109 A s x t)). Qed.
Lemma lem3311205 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term125 A s x t x') = (term126 A s x t x').
Proof. exact (MK_COMB (@lem3311204 A s x t) (@lem3311203 A s x t x')). Qed.
Lemma lem3311206 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term127 A s x t) = (term128 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311205 A s x t x')). Qed.
Lemma lem3311207 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311208 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term119 A s x t) = (term129 A s x t).
Proof. exact (MK_COMB (@lem3311207 A) (@lem3311206 A s x t)). Qed.
Lemma lem3311209 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term118 A s x t) = (term119 A s x t)) = ((term111 A s x t) = (term129 A s x t)).
Proof. exact (MK_COMB (@lem3311202 A s x t) (@lem3311208 A s x t)). Qed.
Lemma lem3311210 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term111 A s x t) = (term129 A s x t).
Proof. exact (EQ_MP (@lem3311209 A s x t) (@lem3311194 A s x t)). Qed.
Lemma lem3311211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3311212 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term113 A s x t) = (term130 A s x t).
Proof. exact (MK_COMB (@lem3311211) (@lem3311210 A s x t)). Qed.
Lemma lem3311214 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3311215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (@lem3311214 A P Q). Qed.
Lemma lem3311216 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term133 A s x t) = (term134 A s x t).
Proof. exact (@lem3311215 A (term80 A s x t) (term103 A s x t)). Qed.
Lemma lem3311217 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term135 A s x t x') = (term70 A s x t x').
Proof. exact (eq_refl (term135 A s x t x')). Qed.
Lemma lem3311218 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term136 A s x t) = (term80 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311217 A s x t x')). Qed.
Lemma lem3311219 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311220 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term137 A s x t) = (term81 A s x t).
Proof. exact (MK_COMB (@lem3311219 A) (@lem3311218 A s x t)). Qed.
Lemma lem3311221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311222 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term138 A s x t) = (term105 A s x t).
Proof. exact (MK_COMB (@lem3311221) (@lem3311220 A s x t)). Qed.
Lemma lem3311223 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term103 A s x t) = (term103 A s x t).
Proof. exact (eq_refl (term103 A s x t)). Qed.
Lemma lem3311224 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term133 A s x t) = (term107 A s x t).
Proof. exact (MK_COMB (@lem3311222 A s x t) (@lem3311223 A s x t)). Qed.
Lemma lem3311225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3311226 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term139 A s x t) = (term140 A s x t).
Proof. exact (MK_COMB (@lem3311225) (@lem3311224 A s x t)). Qed.
Lemma lem3311227 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term135 A s x t x') = (term70 A s x t x').
Proof. exact (eq_refl (term135 A s x t x')). Qed.
Lemma lem3311228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311229 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term141 A s x t x') = (term142 A s x t x').
Proof. exact (MK_COMB (@lem3311228) (@lem3311227 A s x t x')). Qed.
Lemma lem3311230 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term103 A s x t) = (term103 A s x t).
Proof. exact (eq_refl (term103 A s x t)). Qed.
Lemma lem3311231 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term143 A x' s x t) = (term144 A x' s x t).
Proof. exact (MK_COMB (@lem3311229 A s x t x') (@lem3311230 A s x t)). Qed.
Lemma lem3311232 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term145 A s x t) = (term146 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311231 A x' s x t)). Qed.
Lemma lem3311233 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311234 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term134 A s x t) = (term147 A s x t).
Proof. exact (MK_COMB (@lem3311233 A) (@lem3311232 A s x t)). Qed.
Lemma lem3311235 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term133 A s x t) = (term134 A s x t)) = ((term107 A s x t) = (term147 A s x t)).
Proof. exact (MK_COMB (@lem3311226 A s x t) (@lem3311234 A s x t)). Qed.
Lemma lem3311236 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term107 A s x t) = (term147 A s x t).
Proof. exact (EQ_MP (@lem3311235 A s x t) (@lem3311216 A s x t)). Qed.
Lemma lem3311237 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term115 A s x t) = (term148 A s x t).
Proof. exact (MK_COMB (@lem3311212 A s x t) (@lem3311236 A s x t)). Qed.
Lemma lem3311239 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3311240 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem3311239 A P Q). Qed.
Lemma lem3311241 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term151 A s x t) = (term152 A s x t).
Proof. exact (@lem3311240 A (term128 A s x t) (term146 A s x t)). Qed.
Lemma lem3311242 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term153 A s x t x') = (term126 A s x t x').
Proof. exact (eq_refl (term153 A s x t x')). Qed.
Lemma lem3311243 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term154 A s x t) = (term128 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311242 A s x t x')). Qed.
Lemma lem3311244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311245 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term155 A s x t) = (term129 A s x t).
Proof. exact (MK_COMB (@lem3311244 A) (@lem3311243 A s x t)). Qed.
Lemma lem3311246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3311247 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term156 A s x t) = (term130 A s x t).
Proof. exact (MK_COMB (@lem3311246) (@lem3311245 A s x t)). Qed.
Lemma lem3311248 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term157 A s x t x') = (term144 A x' s x t).
Proof. exact (eq_refl (term157 A s x t x')). Qed.
Lemma lem3311249 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term158 A s x t) = (term146 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311248 A x' s x t)). Qed.
Lemma lem3311250 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311251 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term159 A s x t) = (term147 A s x t).
Proof. exact (MK_COMB (@lem3311250 A) (@lem3311249 A s x t)). Qed.
Lemma lem3311252 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term151 A s x t) = (term148 A s x t).
Proof. exact (MK_COMB (@lem3311247 A s x t) (@lem3311251 A s x t)). Qed.
Lemma lem3311253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3311254 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term160 A s x t) = (term161 A s x t).
Proof. exact (MK_COMB (@lem3311253) (@lem3311252 A s x t)). Qed.
Lemma lem3311255 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term153 A s x t x') = (term126 A s x t x').
Proof. exact (eq_refl (term153 A s x t x')). Qed.
Lemma lem3311256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3311257 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term162 A s x t x') = (term163 A s x t x').
Proof. exact (MK_COMB (@lem3311256) (@lem3311255 A s x t x')). Qed.
Lemma lem3311258 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term157 A s x t x') = (term144 A x' s x t).
Proof. exact (eq_refl (term157 A s x t x')). Qed.
Lemma lem3311259 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term164 A s x t x') = (term165 A x' s x t).
Proof. exact (MK_COMB (@lem3311257 A s x t x') (@lem3311258 A x' s x t)). Qed.
Lemma lem3311260 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A s x t) = (term167 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311259 A x' s x t)). Qed.
Lemma lem3311261 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3311262 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term152 A s x t) = (term168 A s x t).
Proof. exact (MK_COMB (@lem3311261 A) (@lem3311260 A s x t)). Qed.
Lemma lem3311263 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term151 A s x t) = (term152 A s x t)) = ((term148 A s x t) = (term168 A s x t)).
Proof. exact (MK_COMB (@lem3311254 A s x t) (@lem3311262 A s x t)). Qed.
Lemma lem3311264 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term148 A s x t) = (term168 A s x t).
Proof. exact (EQ_MP (@lem3311263 A s x t) (@lem3311241 A s x t)). Qed.
Lemma lem3311266 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term115 A s x t) = (term168 A s x t).
Proof. exact (TRANS (@lem3311237 A s x t) (@lem3311264 A s x t)). Qed.
Lemma lem3311267 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term168 A s x t).
Proof. exact (TRANS (@lem3311033 A s x t) (@lem3311266 A s x t)). Qed.
Lemma lem3311268 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term66 A s x t) : term168 A s x t.
Proof. exact (EQ_MP (@lem3311267 A s x t) (@lem3310946 A s x t h1)). Qed.
Lemma lem3311269 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term165 A x' s x t) : term165 A x' s x t.
Proof. exact (h1). Qed.
Lemma lem3311288 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term94 A s x t x') = (term94 A s x t x').
Proof. exact (eq_refl (term94 A s x t x')). Qed.
Lemma lem3311289 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term102 A s x t) = (term102 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311288 A s x t x')). Qed.
Lemma lem3311290 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3311291 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term103 A s x t) = (term103 A s x t).
Proof. exact (MK_COMB (@lem3311290 A) (@lem3311289 A s x t)). Qed.
Lemma lem3311314 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term142 A s x t x') = (term142 A s x t x').
Proof. exact (eq_refl (term142 A s x t x')). Qed.
Lemma lem3311315 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term144 A x' s x t) = (term144 A x' s x t).
Proof. exact (MK_COMB (@lem3311314 A s x t x') (@lem3311291 A s x t)). Qed.
Lemma lem3311336 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term90 A s x t x') = (term90 A s x t x').
Proof. exact (eq_refl (term90 A s x t x')). Qed.
Lemma lem3311355 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term72 A s x t x') = (term72 A s x t x').
Proof. exact (eq_refl (term72 A s x t x')). Qed.
Lemma lem3311356 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term82 A s x t) = (term82 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311355 A s x t x')). Qed.
Lemma lem3311357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3311358 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term83 A s x t) = (term83 A s x t).
Proof. exact (MK_COMB (@lem3311357 A) (@lem3311356 A s x t)). Qed.
Lemma lem3311359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311360 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term109 A s x t) = (term109 A s x t).
Proof. exact (MK_COMB (@lem3311359) (@lem3311358 A s x t)). Qed.
Lemma lem3311361 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term126 A s x t x') = (term126 A s x t x').
Proof. exact (MK_COMB (@lem3311360 A s x t) (@lem3311336 A s x t x')). Qed.
Lemma lem3311362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3311363 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term163 A s x t x') = (term163 A s x t x').
Proof. exact (MK_COMB (@lem3311362) (@lem3311361 A s x t x')). Qed.
Lemma lem3311364 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term165 A x' s x t) = (term165 A x' s x t).
Proof. exact (MK_COMB (@lem3311363 A s x t x') (@lem3311315 A x' s x t)). Qed.
Lemma lem3311365 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term165 A x' s x t) : term165 A x' s x t.
Proof. exact (EQ_MP (@lem3311364 A x' s x t) (@lem3311269 A x' s x t h1)). Qed.
Lemma lem3311366 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term126 A s x t x'.
Proof. exact (h1). Qed.
Lemma lem3311367 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term144 A x' s x t.
Proof. exact (h1). Qed.
Lemma lem3311368 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term90 A s x t x'.
Proof. exact (proj2 (@lem3311366 A s x t x' h1)). Qed.
Lemma lem3311369 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term83 A s x t.
Proof. exact (proj1 (@lem3311366 A s x t x' h1)). Qed.
Lemma lem3311371 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term43 A s x' x.
Proof. exact (proj1 (@lem3311368 A s x t x' h1)). Qed.
Lemma lem3311374 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term103 A s x t.
Proof. exact (proj2 (@lem3311367 A x' s x t h1)). Qed.
Lemma lem3311375 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term70 A s x t x'.
Proof. exact (proj1 (@lem3311367 A x' s x t h1)). Qed.
Lemma lem3311376 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term68 A x t x'.
Proof. exact (proj2 (@lem3311375 A x' s x t h1)). Qed.
Lemma lem3311393 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term72 A s x t x') = (term72 A s x t x').
Proof. exact (eq_refl (term72 A s x t x')). Qed.
Lemma lem3311394 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term82 A s x t) = (term82 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311393 A s x t x')). Qed.
Lemma lem3311395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3311397 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term83 A s x t) = (term83 A s x t).
Proof. exact (MK_COMB (@lem3311395 A) (@lem3311394 A s x t)). Qed.
Lemma lem3311398 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term83 A s x t.
Proof. exact (EQ_MP (@lem3311397 A s x t) (@lem3311369 A s x t x' h1)). Qed.
Lemma lem3311424 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term94 A s x t x') = (term94 A s x t x').
Proof. exact (eq_refl (term94 A s x t x')). Qed.
Lemma lem3311425 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term102 A s x t) = (term102 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3311424 A s x t x')). Qed.
Lemma lem3311426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3311428 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term103 A s x t) = (term103 A s x t).
Proof. exact (MK_COMB (@lem3311426 A) (@lem3311425 A s x t)). Qed.
Lemma lem3311429 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term103 A s x t.
Proof. exact (EQ_MP (@lem3311428 A s x t) (@lem3311374 A x' s x t h1)). Qed.
Lemma lem3311442 {A : Type'} (_34134 : A) (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term169 A s x t _34134.
Proof. exact (@lem3311398 A s x t x' h1 _34134). Qed.
Lemma lem3311443 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34134 : A) : (term169 A s x t _34134) = (term72 A s x t _34134).
Proof. exact (eq_refl (term169 A s x t _34134)). Qed.
Lemma lem3311445 {A : Type'} (_34135 : A) (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term170 A s x t _34135.
Proof. exact (@lem3311429 A x' s x t h1 _34135). Qed.
Lemma lem3311446 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34135 : A) : (term170 A s x t _34135) = (term94 A s x t _34135).
Proof. exact (eq_refl (term170 A s x t _34135)). Qed.
Lemma lem3311447 {A : Type'} (_34135 : A) (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term94 A s x t _34135.
Proof. exact (EQ_MP (@lem3311446 A s x t _34135) (@lem3311445 A _34135 x' s x t h1)). Qed.
Lemma lem3311457 {A : Type'} (_34134 : A) (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term72 A s x t _34134.
Proof. exact (EQ_MP (@lem3311443 A s x t _34134) (@lem3311442 A _34134 s x t x' h1)). Qed.
Lemma lem3311463 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term42 A x' x.
Proof. exact (proj2 (@lem3311371 A s x t x' h1)). Qed.
Lemma lem3311474 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34135 : A) : (term94 A s x t _34135) = (term72 A s x t _34135).
Proof. exact (@lem3310615 (term171 A s _34135) (_34135 = x) (t _34135)). Qed.
Lemma lem3311475 {A : Type'} (_34135 : A) (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term72 A s x t _34135.
Proof. exact (EQ_MP (@lem3311474 A s x t _34135) (@lem3311447 A _34135 x' s x t h1)). Qed.
Lemma lem3311481 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term171 A t x'.
Proof. exact (proj2 (@lem3311376 A x' s x t h1)). Qed.
Lemma lem3311509 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : s x'.
Proof. exact (proj1 (@lem3311371 A s x t x' h1)). Qed.
Lemma lem3311510 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term172 A s x'.
Proof. exact (fun h0 : term171 A s x' => @lem3311509 A s x t x' h1). Qed.
Lemma lem3311512 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3311513 {A : Type'} (s : A -> Prop) (x' : A) : (term172 A s x') = (s x').
Proof. exact (@lem3311512 (s x')). Qed.
Lemma lem3311514 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : s x'.
Proof. exact (EQ_MP (@lem3311513 A s x') (@lem3311510 A s x t x' h1)). Qed.
Lemma lem3311516 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term171 A t x'.
Proof. exact (proj2 (@lem3311368 A s x t x' h1)). Qed.
Lemma lem3311517 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term174 A t x'.
Proof. exact (fun h0 : t x' => @lem3311516 A s x t x' h1). Qed.
Lemma lem3311519 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3311520 {A : Type'} (t : A -> Prop) (x' : A) : (term174 A t x') = (term171 A t x').
Proof. exact (@lem3311519 (t x')). Qed.
Lemma lem3311521 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term171 A t x'.
Proof. exact (EQ_MP (@lem3311520 A t x') (@lem3311517 A s x t x' h1)). Qed.
Lemma lem3311527 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3311528 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34134 : A) : (term72 A s x t _34134) = (term176 A x s t _34134).
Proof. exact (@lem3311527 (_34134 = x) (term171 A s _34134) (t _34134)). Qed.
Lemma lem3311544 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3311545 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34134 : A) : (term177 A s t _34134) = (term178 A t s _34134).
Proof. exact (@lem3311544 (t _34134) (term171 A s _34134)). Qed.
Lemma lem3311551 {A : Type'} (_34134 : A) (x : A) : (term30 A _34134 x) = (term30 A _34134 x).
Proof. exact (eq_refl (term30 A _34134 x)). Qed.
Lemma lem3311552 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34134 : A) : (term176 A x s t _34134) = (term179 A x t s _34134).
Proof. exact (MK_COMB (@lem3311551 A _34134 x) (@lem3311545 A t s _34134)). Qed.
Lemma lem3311556 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3311557 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : (term179 A x t s _34134) = (term180 A t x s _34134).
Proof. exact (@lem3311556 (t _34134) (_34134 = x) (term171 A s _34134)). Qed.
Lemma lem3311575 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : (term176 A x s t _34134) = (term180 A t x s _34134).
Proof. exact (TRANS (@lem3311552 A x t s _34134) (@lem3311557 A t x s _34134)). Qed.
Lemma lem3311576 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : (term72 A s x t _34134) = (term180 A t x s _34134).
Proof. exact (TRANS (@lem3311528 A x s t _34134) (@lem3311575 A t x s _34134)). Qed.
Lemma lem3311577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3311578 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : (term181 A s x t _34134) = (term182 A t x s _34134).
Proof. exact (MK_COMB (@lem3311577) (@lem3311576 A t x s _34134)). Qed.
Lemma lem3311594 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3311595 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34134 : A) : (term177 A s t _34134) = (term178 A t s _34134).
Proof. exact (@lem3311594 (t _34134) (term171 A s _34134)). Qed.
Lemma lem3311601 {A : Type'} (_34134 : A) (x : A) : (term30 A _34134 x) = (term30 A _34134 x).
Proof. exact (eq_refl (term30 A _34134 x)). Qed.
Lemma lem3311602 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34134 : A) : (term176 A x s t _34134) = (term179 A x t s _34134).
Proof. exact (MK_COMB (@lem3311601 A _34134 x) (@lem3311595 A t s _34134)). Qed.
Lemma lem3311606 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3311607 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : (term179 A x t s _34134) = (term180 A t x s _34134).
Proof. exact (@lem3311606 (t _34134) (_34134 = x) (term171 A s _34134)). Qed.
Lemma lem3311625 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : (term176 A x s t _34134) = (term180 A t x s _34134).
Proof. exact (TRANS (@lem3311602 A x t s _34134) (@lem3311607 A t x s _34134)). Qed.
Lemma lem3311626 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : ((term72 A s x t _34134) = (term176 A x s t _34134)) = ((term180 A t x s _34134) = (term180 A t x s _34134)).
Proof. exact (MK_COMB (@lem3311578 A t x s _34134) (@lem3311625 A t x s _34134)). Qed.
Lemma lem3311628 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3311629 (x : Prop) : (x = x) = True.
Proof. exact (@lem3311628 Prop x). Qed.
Lemma lem3311630 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34134 : A) : ((term180 A t x s _34134) = (term180 A t x s _34134)) = True.
Proof. exact (@lem3311629 (term180 A t x s _34134)). Qed.
Lemma lem3311631 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34134 : A) : ((term72 A s x t _34134) = (term176 A x s t _34134)) = True.
Proof. exact (TRANS (@lem3311626 A t x s _34134) (@lem3311630 A t x s _34134)). Qed.
Lemma lem3311632 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34134 : A) : True = ((term72 A s x t _34134) = (term176 A x s t _34134)).
Proof. exact (SYM (@lem3311631 A x s t _34134)). Qed.
Lemma lem3311633 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34134 : A) : (term72 A s x t _34134) = (term176 A x s t _34134).
Proof. exact (EQ_MP (@lem3311632 A x s t _34134) (@lem0)). Qed.
Lemma lem3311634 {A : Type'} (_34134 : A) (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term176 A x s t _34134.
Proof. exact (EQ_MP (@lem3311633 A x s t _34134) (@lem3311457 A _34134 s x t x' h1)). Qed.
Lemma lem3311636 (b : Prop) (a : Prop) : (a \/ b) = (term183 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3311637 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) (x : A) : (term176 A x s t _34134) = (term184 A s t _34134 x).
Proof. exact (@lem3311636 (term177 A s t _34134) (_34134 = x)). Qed.
Lemma lem3311639 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3311640 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) : (term187 A s t _34134) = (term188 A s t _34134).
Proof. exact (@lem3311639 (term171 A s _34134) (t _34134)). Qed.
Lemma lem3311642 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3311643 {A : Type'} (s : A -> Prop) (_34134 : A) : (term189 A s _34134) = (s _34134).
Proof. exact (@lem3311642 (s _34134)). Qed.
Lemma lem3311644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311645 {A : Type'} (s : A -> Prop) (_34134 : A) : (term190 A s _34134) = (term41 A s _34134).
Proof. exact (MK_COMB (@lem3311644) (@lem3311643 A s _34134)). Qed.
Lemma lem3311646 {A : Type'} (t : A -> Prop) (_34134 : A) : (term171 A t _34134) = (term171 A t _34134).
Proof. exact (eq_refl (term171 A t _34134)). Qed.
Lemma lem3311647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) : (term188 A s t _34134) = (term191 A s t _34134).
Proof. exact (MK_COMB (@lem3311645 A s _34134) (@lem3311646 A t _34134)). Qed.
Lemma lem3311648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) : (term187 A s t _34134) = (term191 A s t _34134).
Proof. exact (TRANS (@lem3311640 A s t _34134) (@lem3311647 A s t _34134)). Qed.
Lemma lem3311649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3311650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) : (term192 A s t _34134) = (term193 A s t _34134).
Proof. exact (MK_COMB (@lem3311649) (@lem3311648 A s t _34134)). Qed.
Lemma lem3311651 {A : Type'} (_34134 : A) (x : A) : (_34134 = x) = (_34134 = x).
Proof. exact (eq_refl (_34134 = x)). Qed.
Lemma lem3311652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) (x : A) : (term184 A s t _34134 x) = (term194 A s t _34134 x).
Proof. exact (MK_COMB (@lem3311650 A s t _34134) (@lem3311651 A _34134 x)). Qed.
Lemma lem3311653 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34134 : A) (x : A) : (term176 A x s t _34134) = (term194 A s t _34134 x).
Proof. exact (TRANS (@lem3311637 A s t _34134 x) (@lem3311652 A s t _34134 x)). Qed.
Lemma lem3311655 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term191 A s t x'.
Proof. exact (conj (@lem3311514 A s x t x' h1) (@lem3311521 A s x t x' h1)). Qed.
Lemma lem3311657 {A : Type'} (_34134 : A) (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term194 A s t _34134 x.
Proof. exact (EQ_MP (@lem3311653 A s t _34134 x) (@lem3311634 A _34134 s x t x' h1)). Qed.
Lemma lem3311658 {A : Type'} (_34134 : A) (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term194 A s t _34134 x.
Proof. exact (@lem3311657 A _34134 s x t x' h1). Qed.
Lemma lem3311659 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term194 A s t x' x.
Proof. exact (@lem3311658 A x' s x t x' h1). Qed.
Lemma lem3311662 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : x' = x.
Proof. exact (@lem3311659 A s x t x' h1 (@lem3311655 A s x t x' h1)). Qed.
Lemma lem3311663 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term195 A x' x.
Proof. exact (fun h0 : term42 A x' x => @lem3311662 A s x t x' h1). Qed.
Lemma lem3311665 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3311666 {A : Type'} (x' : A) (x : A) : (term195 A x' x) = (x' = x).
Proof. exact (@lem3311665 (x' = x)). Qed.
Lemma lem3311667 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : x' = x.
Proof. exact (EQ_MP (@lem3311666 A x' x) (@lem3311663 A s x t x' h1)). Qed.
Lemma lem3311670 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3311672 {A : Type'} (x' : A) (x : A) : (term42 A x' x) = (term196 A x' x).
Proof. exact (@lem3311670 (x' = x)). Qed.
Lemma lem3311675 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term196 A x' x.
Proof. exact (EQ_MP (@lem3311672 A x' x) (@lem3311463 A s x t x' h1)). Qed.
Lemma lem3311678 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : False.
Proof. exact (@lem3311675 A s x t x' h1 (@lem3311667 A s x t x' h1)). Qed.
Lemma lem3311679 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : term197.
Proof. exact (fun h0 : ~ False => @lem3311678 A s x t x' h1). Qed.
Lemma lem3311681 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3311682 : term197 = False.
Proof. exact (@lem3311681 False). Qed.
Lemma lem3311683 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term126 A s x t x') : False.
Proof. exact (EQ_MP (@lem3311682) (@lem3311679 A s x t x' h1)). Qed.
Lemma lem3311711 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : s x'.
Proof. exact (proj1 (@lem3311375 A x' s x t h1)). Qed.
Lemma lem3311712 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term172 A s x'.
Proof. exact (fun h0 : term171 A s x' => @lem3311711 A x' s x t h1). Qed.
Lemma lem3311714 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3311715 {A : Type'} (s : A -> Prop) (x' : A) : (term172 A s x') = (s x').
Proof. exact (@lem3311714 (s x')). Qed.
Lemma lem3311716 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : s x'.
Proof. exact (EQ_MP (@lem3311715 A s x') (@lem3311712 A x' s x t h1)). Qed.
Lemma lem3311718 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term42 A x' x.
Proof. exact (proj1 (@lem3311376 A x' s x t h1)). Qed.
Lemma lem3311719 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term198 A x' x.
Proof. exact (fun h0 : x' = x => @lem3311718 A x' s x t h1). Qed.
Lemma lem3311721 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3311722 {A : Type'} (x' : A) (x : A) : (term198 A x' x) = (term42 A x' x).
Proof. exact (@lem3311721 (x' = x)). Qed.
Lemma lem3311723 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term42 A x' x.
Proof. exact (EQ_MP (@lem3311722 A x' x) (@lem3311719 A x' s x t h1)). Qed.
Lemma lem3311729 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3311730 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34135 : A) : (term72 A s x t _34135) = (term176 A x s t _34135).
Proof. exact (@lem3311729 (_34135 = x) (term171 A s _34135) (t _34135)). Qed.
Lemma lem3311746 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3311747 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34135 : A) : (term177 A s t _34135) = (term178 A t s _34135).
Proof. exact (@lem3311746 (t _34135) (term171 A s _34135)). Qed.
Lemma lem3311753 {A : Type'} (_34135 : A) (x : A) : (term30 A _34135 x) = (term30 A _34135 x).
Proof. exact (eq_refl (term30 A _34135 x)). Qed.
Lemma lem3311754 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34135 : A) : (term176 A x s t _34135) = (term179 A x t s _34135).
Proof. exact (MK_COMB (@lem3311753 A _34135 x) (@lem3311747 A t s _34135)). Qed.
Lemma lem3311758 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3311759 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : (term179 A x t s _34135) = (term180 A t x s _34135).
Proof. exact (@lem3311758 (t _34135) (_34135 = x) (term171 A s _34135)). Qed.
Lemma lem3311777 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : (term176 A x s t _34135) = (term180 A t x s _34135).
Proof. exact (TRANS (@lem3311754 A x t s _34135) (@lem3311759 A t x s _34135)). Qed.
Lemma lem3311778 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : (term72 A s x t _34135) = (term180 A t x s _34135).
Proof. exact (TRANS (@lem3311730 A x s t _34135) (@lem3311777 A t x s _34135)). Qed.
Lemma lem3311779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3311780 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : (term181 A s x t _34135) = (term182 A t x s _34135).
Proof. exact (MK_COMB (@lem3311779) (@lem3311778 A t x s _34135)). Qed.
Lemma lem3311794 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3311795 {A : Type'} (x : A) (s : A -> Prop) (_34135 : A) : (term87 A s _34135 x) = (term199 A x s _34135).
Proof. exact (@lem3311794 (_34135 = x) (term171 A s _34135)). Qed.
Lemma lem3311803 {A : Type'} (t : A -> Prop) (_34135 : A) : (term200 A t _34135) = (term200 A t _34135).
Proof. exact (eq_refl (term200 A t _34135)). Qed.
Lemma lem3311804 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : (term201 A t s _34135 x) = (term180 A t x s _34135).
Proof. exact (MK_COMB (@lem3311803 A t _34135) (@lem3311795 A x s _34135)). Qed.
Lemma lem3311815 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : ((term72 A s x t _34135) = (term201 A t s _34135 x)) = ((term180 A t x s _34135) = (term180 A t x s _34135)).
Proof. exact (MK_COMB (@lem3311780 A t x s _34135) (@lem3311804 A t x s _34135)). Qed.
Lemma lem3311817 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3311818 (x : Prop) : (x = x) = True.
Proof. exact (@lem3311817 Prop x). Qed.
Lemma lem3311819 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34135 : A) : ((term180 A t x s _34135) = (term180 A t x s _34135)) = True.
Proof. exact (@lem3311818 (term180 A t x s _34135)). Qed.
Lemma lem3311820 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34135 : A) (x : A) : ((term72 A s x t _34135) = (term201 A t s _34135 x)) = True.
Proof. exact (TRANS (@lem3311815 A t x s _34135) (@lem3311819 A t x s _34135)). Qed.
Lemma lem3311821 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34135 : A) (x : A) : True = ((term72 A s x t _34135) = (term201 A t s _34135 x)).
Proof. exact (SYM (@lem3311820 A t s _34135 x)). Qed.
Lemma lem3311822 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34135 : A) (x : A) : (term72 A s x t _34135) = (term201 A t s _34135 x).
Proof. exact (EQ_MP (@lem3311821 A t s _34135 x) (@lem0)). Qed.
Lemma lem3311823 {A : Type'} (_34135 : A) (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term201 A t s _34135 x.
Proof. exact (EQ_MP (@lem3311822 A t s _34135 x) (@lem3311475 A _34135 x' s x t h1)). Qed.
Lemma lem3311825 (b : Prop) (a : Prop) : (a \/ b) = (term183 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3311826 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34135 : A) : (term201 A t s _34135 x) = (term202 A s x t _34135).
Proof. exact (@lem3311825 (term87 A s _34135 x) (t _34135)). Qed.
Lemma lem3311828 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3311829 {A : Type'} (s : A -> Prop) (_34135 : A) (x : A) : (term203 A s _34135 x) = (term204 A s _34135 x).
Proof. exact (@lem3311828 (term171 A s _34135) (_34135 = x)). Qed.
Lemma lem3311831 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3311832 {A : Type'} (s : A -> Prop) (_34135 : A) : (term189 A s _34135) = (s _34135).
Proof. exact (@lem3311831 (s _34135)). Qed.
Lemma lem3311833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311834 {A : Type'} (s : A -> Prop) (_34135 : A) : (term190 A s _34135) = (term41 A s _34135).
Proof. exact (MK_COMB (@lem3311833) (@lem3311832 A s _34135)). Qed.
Lemma lem3311835 {A : Type'} (_34135 : A) (x : A) : (term42 A _34135 x) = (term42 A _34135 x).
Proof. exact (eq_refl (term42 A _34135 x)). Qed.
Lemma lem3311836 {A : Type'} (s : A -> Prop) (_34135 : A) (x : A) : (term204 A s _34135 x) = (term43 A s _34135 x).
Proof. exact (MK_COMB (@lem3311834 A s _34135) (@lem3311835 A _34135 x)). Qed.
Lemma lem3311837 {A : Type'} (s : A -> Prop) (_34135 : A) (x : A) : (term203 A s _34135 x) = (term43 A s _34135 x).
Proof. exact (TRANS (@lem3311829 A s _34135 x) (@lem3311836 A s _34135 x)). Qed.
Lemma lem3311838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3311839 {A : Type'} (s : A -> Prop) (_34135 : A) (x : A) : (term205 A s _34135 x) = (term45 A s _34135 x).
Proof. exact (MK_COMB (@lem3311838) (@lem3311837 A s _34135 x)). Qed.
Lemma lem3311840 {A : Type'} (t : A -> Prop) (_34135 : A) : (t _34135) = (t _34135).
Proof. exact (eq_refl (t _34135)). Qed.
Lemma lem3311841 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34135 : A) : (term202 A s x t _34135) = (term47 A s x t _34135).
Proof. exact (MK_COMB (@lem3311839 A s _34135 x) (@lem3311840 A t _34135)). Qed.
Lemma lem3311842 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34135 : A) : (term201 A t s _34135 x) = (term47 A s x t _34135).
Proof. exact (TRANS (@lem3311826 A s x t _34135) (@lem3311841 A s x t _34135)). Qed.
Lemma lem3311844 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term43 A s x' x.
Proof. exact (conj (@lem3311716 A x' s x t h1) (@lem3311723 A x' s x t h1)). Qed.
Lemma lem3311846 {A : Type'} (_34135 : A) (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term47 A s x t _34135.
Proof. exact (EQ_MP (@lem3311842 A s x t _34135) (@lem3311823 A _34135 x' s x t h1)). Qed.
Lemma lem3311847 {A : Type'} (_34135 : A) (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term47 A s x t _34135.
Proof. exact (@lem3311846 A _34135 x' s x t h1). Qed.
Lemma lem3311848 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term47 A s x t x'.
Proof. exact (@lem3311847 A x' x' s x t h1). Qed.
Lemma lem3311851 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : t x'.
Proof. exact (@lem3311848 A x' s x t h1 (@lem3311844 A x' s x t h1)). Qed.
Lemma lem3311852 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term172 A t x'.
Proof. exact (fun h0 : term171 A t x' => @lem3311851 A x' s x t h1). Qed.
Lemma lem3311854 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3311855 {A : Type'} (t : A -> Prop) (x' : A) : (term172 A t x') = (t x').
Proof. exact (@lem3311854 (t x')). Qed.
Lemma lem3311856 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : t x'.
Proof. exact (EQ_MP (@lem3311855 A t x') (@lem3311852 A x' s x t h1)). Qed.
Lemma lem3311859 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3311861 {A : Type'} (t : A -> Prop) (x' : A) : (term171 A t x') = (term206 A t x').
Proof. exact (@lem3311859 (t x')). Qed.
Lemma lem3311864 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term206 A t x'.
Proof. exact (EQ_MP (@lem3311861 A t x') (@lem3311481 A x' s x t h1)). Qed.
Lemma lem3311867 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : False.
Proof. exact (@lem3311864 A x' s x t h1 (@lem3311856 A x' s x t h1)). Qed.
Lemma lem3311868 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : term197.
Proof. exact (fun h0 : ~ False => @lem3311867 A x' s x t h1). Qed.
Lemma lem3311870 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3311871 : term197 = False.
Proof. exact (@lem3311870 False). Qed.
Lemma lem3311872 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term144 A x' s x t) : False.
Proof. exact (EQ_MP (@lem3311871) (@lem3311868 A x' s x t h1)). Qed.
Lemma lem3311873 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term165 A x' s x t) : False.
Proof. exact (or_elim (@lem3311365 A x' s x t h1) (fun h0 : term126 A s x t x' => @lem3311683 A s x t x' h0) (fun h0 : term144 A x' s x t => @lem3311872 A x' s x t h0)). Qed.
Lemma lem3311874 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term165 A x' s x t) : (term165 A x' s x t) = False.
Proof. exact (prop_ext (fun h2 : term165 A x' s x t => @lem3311873 A x' s x t h1) (fun h2 : False => @lem3311365 A x' s x t h1)). Qed.
Lemma lem3311875 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term165 A x' s x t) : False.
Proof. exact (EQ_MP (@lem3311874 A x' s x t h1) (@lem3311365 A x' s x t h1)). Qed.
Lemma lem3311876 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term66 A s x t) : False.
Proof. exact (ex_elim (@lem3311268 A s x t h1) (fun x' : A => fun h0 : term167 A s x t x' => @lem3311875 A x' s x t h0)). Qed.
Lemma lem3311877 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term66 A s x t) : (term66 A s x t) = False.
Proof. exact (prop_ext (fun h2 : term66 A s x t => @lem3311876 A s x t h1) (fun h2 : False => @lem3310946 A s x t h1)). Qed.
Lemma lem3311878 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term66 A s x t) : False.
Proof. exact (EQ_MP (@lem3311877 A s x t h1) (@lem3310946 A s x t h1)). Qed.
Lemma lem3311879 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term65 A s x t.
Proof. exact (fun h0 : term66 A s x t => @lem3311878 A s x t h0). Qed.
Lemma lem3311880 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A s x t) = (term50 A s x t).
Proof. exact (EQ_MP (@lem3310945 A s x t) (@lem3311879 A s x t)). Qed.
Lemma lem3311885 {A : Type'} (s : A -> Prop) (x : A) : term52 A s x.
Proof. exact (fun t : A -> Prop => @lem3311880 A s x t). Qed.
Lemma lem3311890 {A : Type'} (x : A) : term54 A x.
Proof. exact (fun s : A -> Prop => @lem3311885 A s x). Qed.
Lemma lem3311895 {A : Type'} : term56 A.
Proof. exact (fun x : A => @lem3311890 A x). Qed.
Lemma lem3311896 {A : Type'} : term58 A.
Proof. exact (EQ_MP (@lem3310941 A) (@lem3311895 A)). Qed.
Lemma lem3311898 {A : Type'} : term58 A.
Proof. exact (@lem3310822 A (@lem3311896 A)). Qed.
Lemma lem3311899 {A : Type'} (h1 : term59 A) : False.
Proof. exact (@lem3311898 A (@lem3310806 A h1)). Qed.
Lemma lem3311900 {A : Type'} (h1 : term59 A) : (term59 A) = False.
Proof. exact (prop_ext (fun h2 : term59 A => @lem3311899 A h1) (fun h2 : False => @lem3310806 A h1)). Qed.
Lemma lem3311901 {A : Type'} (h1 : term59 A) : False.
Proof. exact (EQ_MP (@lem3311900 A h1) (@lem3310806 A h1)). Qed.
Lemma lem3311902 {A : Type'} : term58 A.
Proof. exact (fun h0 : term59 A => @lem3311901 A h0). Qed.
Lemma lem3311903 {A : Type'} : term56 A.
Proof. exact (EQ_MP (@lem3310805 A) (@lem3311902 A)). Qed.
Lemma lem3311904 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3310801 A) (@lem3311903 A)). Qed.
Lemma lem3311905 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3310680 A) (@lem3311904 A)). Qed.
