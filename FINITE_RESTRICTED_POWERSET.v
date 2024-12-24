Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RESTRICTED_POWERSET_term_abbrevs.
Require Import CARD_SING_spec.
Require Import CHOOSE_SUBSET_BETWEEN_spec.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_POWERSET_spec.
Require Import FINITE_RESTRICT_spec.
Require Import FINITE_SING_spec.
Require Import FINITE_SUBSET_spec.
Require Import FINITE_UNIONS_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import LE_1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SING_GSPEC_spec.
Require Import SING_SUBSET_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm11004_spec.
Require Import thm11005_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21742_spec.
Require Import thm21760_spec.
Require Import thm21761_spec.
Require Import thm21762_spec.
Require Import thm21763_spec.
Require Import thm21780_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4614688 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4614689 {A : Type'} (n : nat) (h1 : term0 A) : term1 A n.
Proof. exact (@lem4614688 A h1 n). Qed.
Lemma lem4614690 {A : Type'} (n : nat) : (term1 A n) = (term2 A n).
Proof. exact (eq_refl (term1 A n)). Qed.
Lemma lem4614691 {A : Type'} (n : nat) (h1 : term0 A) : term2 A n.
Proof. exact (EQ_MP (@lem4614690 A n) (@lem4614689 A n h1)). Qed.
Lemma lem4614692 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term0 A) : term3 A n s.
Proof. exact (@lem4614691 A n h1 s). Qed.
Lemma lem4614693 {A : Type'} (s : A -> Prop) (n : nat) : (term3 A n s) = (term4 A s n).
Proof. exact (eq_refl (term3 A n s)). Qed.
Lemma lem4614694 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term0 A) : term4 A s n.
Proof. exact (EQ_MP (@lem4614693 A s n) (@lem4614692 A n s h1)). Qed.
Lemma lem4614695 {A : Type'} (s : A -> Prop) (n : nat) (u : A -> Prop) (h1 : term0 A) : term5 A s n u.
Proof. exact (@lem4614694 A s n h1 u). Qed.
Lemma lem4614696 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) : (term5 A s n u) = (term6 A s u n).
Proof. exact (eq_refl (term5 A s n u)). Qed.
Lemma lem4614697 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) (h1 : term0 A) : term6 A s u n.
Proof. exact (EQ_MP (@lem4614696 A s u n) (@lem4614695 A s n u h1)). Qed.
Lemma lem4614698 {A : Type'} (s : A -> Prop) (n : nat) (u : A -> Prop) (h1 : term7 A s n u) : term7 A s n u.
Proof. exact (h1). Qed.
Lemma lem4614699 {A : Type'} (s : A -> Prop) (n : nat) (u : A -> Prop) (h1 : term0 A) (h2 : term7 A s n u) : term8 A s u n.
Proof. exact (@lem4614697 A s u n h1 (@lem4614698 A s n u h2)). Qed.
Lemma lem4614700 {A : Type'} (s : A -> Prop) (n : nat) (u : A -> Prop) (h1 : term7 A s n u) : term9 A s u n.
Proof. exact (fun h0 : term0 A => @lem4614699 A s n u h0 h1). Qed.
Lemma lem4614701 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4614702 {A : Type'} (s : A -> Prop) (n : nat) (u : A -> Prop) (h1 : term0 A) (h2 : term7 A s n u) : term8 A s u n.
Proof. exact (@lem4614700 A s n u h2 (@lem4614701 A h1)). Qed.
Lemma lem4614703 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) (h1 : term0 A) : term6 A s u n.
Proof. exact (fun h0 : term7 A s n u => @lem4614702 A s n u h1 h0). Qed.
Lemma lem4614704 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term0 A) : term10 A s u.
Proof. exact (fun n : nat => @lem4614703 A s u n h1). Qed.
Lemma lem4614705 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term11 A s.
Proof. exact (fun u : A -> Prop => @lem4614704 A s u h1). Qed.
Lemma lem4614706 {A : Type'} (h1 : term0 A) : term12 A.
Proof. exact (fun s : A -> Prop => @lem4614705 A s h1). Qed.
Lemma lem4614707 {A : Type'} : term13 A.
Proof. exact (fun h0 : term0 A => @lem4614706 A h0). Qed.
Lemma lem4614708 {A : Type'} : term12 A.
Proof. exact (@lem4614707 A (@lem4106042 A)). Qed.
Lemma lem4614709 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem4614708 A s). Qed.
Lemma lem4614710 {A : Type'} (s : A -> Prop) : (term14 A s) = (term11 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem4614711 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem4614710 A s) (@lem4614709 A s)). Qed.
Lemma lem4614712 {A : Type'} (s : A -> Prop) (u : A -> Prop) : term15 A s u.
Proof. exact (@lem4614711 A s u). Qed.
Lemma lem4614713 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term15 A s u) = (term10 A s u).
Proof. exact (eq_refl (term15 A s u)). Qed.
Lemma lem4614714 {A : Type'} (s : A -> Prop) (u : A -> Prop) : term10 A s u.
Proof. exact (EQ_MP (@lem4614713 A s u) (@lem4614712 A s u)). Qed.
Lemma lem4614715 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) : term16 A s u n.
Proof. exact (@lem4614714 A s u n). Qed.
Lemma lem4614716 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) : (term16 A s u n) = (term6 A s u n).
Proof. exact (eq_refl (term16 A s u n)). Qed.
Lemma lem4614737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4614738 {_108414 : Type'} (s : _108414 -> Prop) (t : _108414 -> Prop) : (@SUBSET _108414 s t) = (term17 _108414 s t).
Proof. exact (@lem4614737 _108414 s t). Qed.
Lemma lem4614739 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term18 _108414 x t) = (term19 _108414 x t).
Proof. exact (@lem4614738 _108414 (@INSERT _108414 x (@EMPTY _108414)) t). Qed.
Lemma lem4614746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4614747 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term20 _108414 x t) = (term21 _108414 x t).
Proof. exact (MK_COMB (@lem4614746) (@lem4614739 _108414 x t)). Qed.
Lemma lem4614748 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4614749 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term22 _108414 x t P) = (term23 _108414 x t P).
Proof. exact (MK_COMB (@lem4614747 _108414 x t) (@lem4614748 P)). Qed.
Lemma lem4614752 {_108414 : Type'} (P : Prop) (x : _108414) (t : _108414 -> Prop) : (term24 _108414 P x t) = (term24 _108414 P x t).
Proof. exact (eq_refl (term24 _108414 P x t)). Qed.
Lemma lem4614753 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : ((term25 _108414 P x t) = (term22 _108414 x t P)) = ((term25 _108414 P x t) = (term23 _108414 x t P)).
Proof. exact (MK_COMB (@lem4614752 _108414 P x t) (@lem4614749 _108414 x t P)). Qed.
Lemma lem4614758 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : ((term25 _108414 P x t) = (term23 _108414 x t P)) = ((term25 _108414 P x t) = (term22 _108414 x t P)).
Proof. exact (SYM (@lem4614753 _108414 x t P)). Qed.
Lemma lem4614764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4614765 {_108414 : Type'} (P : _108414 -> Prop) (x : _108414) : (@IN _108414 x P) = (P x).
Proof. exact (@lem4614764 _108414 P x). Qed.
Lemma lem4614766 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (@IN _108414 x t) = (t x).
Proof. exact (@lem4614765 _108414 t x). Qed.
Lemma lem4614767 (P : Prop) : (and P) = (and P).
Proof. exact (eq_refl (and P)). Qed.
Lemma lem4614768 {_108414 : Type'} (P : Prop) (t : _108414 -> Prop) (x : _108414) : (term25 _108414 P x t) = (term26 _108414 P t x).
Proof. exact (MK_COMB (@lem4614767 P) (@lem4614766 _108414 t x)). Qed.
Lemma lem4614771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4614772 {_108414 : Type'} (P : Prop) (t : _108414 -> Prop) (x : _108414) : (term24 _108414 P x t) = (term27 _108414 P t x).
Proof. exact (MK_COMB (@lem4614771) (@lem4614768 _108414 P t x)). Qed.
Lemma lem4614782 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term28 A x y s) = (term29 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4614783 {_108414 : Type'} (y : _108414) (x : _108414) (s : _108414 -> Prop) : (term28 _108414 x y s) = (term29 _108414 y x s).
Proof. exact (@lem4614782 _108414 y x s). Qed.
Lemma lem4614784 {_108414 : Type'} (x : _108414) (x' : _108414) : (term30 _108414 x' x) = (term31 _108414 x x').
Proof. exact (@lem4614783 _108414 x x' (@EMPTY _108414)). Qed.
Lemma lem4614790 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4614791 {_108414 : Type'} (x : _108414) : (@IN _108414 x (@EMPTY _108414)) = False.
Proof. exact (@lem4614790 _108414 x). Qed.
Lemma lem4614792 {_108414 : Type'} (x' : _108414) : (@IN _108414 x' (@EMPTY _108414)) = False.
Proof. exact (@lem4614791 _108414 x'). Qed.
Lemma lem4614793 {_108414 : Type'} (x' : _108414) (x : _108414) : (term32 _108414 x' x) = (term32 _108414 x' x).
Proof. exact (eq_refl (term32 _108414 x' x)). Qed.
Lemma lem4614794 {_108414 : Type'} (x' : _108414) (x : _108414) : (term31 _108414 x x') = (term33 _108414 x' x).
Proof. exact (MK_COMB (@lem4614793 _108414 x' x) (@lem4614792 _108414 x')). Qed.
Lemma lem4614796 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4614797 {_108414 : Type'} (x' : _108414) (x : _108414) : (term33 _108414 x' x) = (x' = x).
Proof. exact (@lem4614796 (x' = x)). Qed.
Lemma lem4614800 {_108414 : Type'} (x' : _108414) (x : _108414) : (term31 _108414 x x') = (x' = x).
Proof. exact (TRANS (@lem4614794 _108414 x' x) (@lem4614797 _108414 x' x)). Qed.
Lemma lem4614801 {_108414 : Type'} (x' : _108414) (x : _108414) : (term30 _108414 x' x) = (x' = x).
Proof. exact (TRANS (@lem4614784 _108414 x x') (@lem4614800 _108414 x' x)). Qed.
Lemma lem4614802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4614803 {_108414 : Type'} (x' : _108414) (x : _108414) : (term34 _108414 x' x) = (term35 _108414 x' x).
Proof. exact (MK_COMB (@lem4614802) (@lem4614801 _108414 x' x)). Qed.
Lemma lem4614805 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4614806 {_108414 : Type'} (P : _108414 -> Prop) (x : _108414) : (@IN _108414 x P) = (P x).
Proof. exact (@lem4614805 _108414 P x). Qed.
Lemma lem4614807 {_108414 : Type'} (t : _108414 -> Prop) (x' : _108414) : (@IN _108414 x' t) = (t x').
Proof. exact (@lem4614806 _108414 t x'). Qed.
Lemma lem4614808 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term36 _108414 x x' t) = (term37 _108414 x t x').
Proof. exact (MK_COMB (@lem4614803 _108414 x' x) (@lem4614807 _108414 t x')). Qed.
Lemma lem4614813 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term38 _108414 x t) = (term39 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4614808 _108414 x t x')). Qed.
Lemma lem4614814 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4614815 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term19 _108414 x t) = (term40 _108414 x t).
Proof. exact (MK_COMB (@lem4614814 _108414) (@lem4614813 _108414 x t)). Qed.
Lemma lem4614820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4614821 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term21 _108414 x t) = (term41 _108414 x t).
Proof. exact (MK_COMB (@lem4614820) (@lem4614815 _108414 x t)). Qed.
Lemma lem4614822 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4614823 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term23 _108414 x t P) = (term42 _108414 x t P).
Proof. exact (MK_COMB (@lem4614821 _108414 x t) (@lem4614822 P)). Qed.
Lemma lem4614826 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : ((term25 _108414 P x t) = (term23 _108414 x t P)) = ((term26 _108414 P t x) = (term42 _108414 x t P)).
Proof. exact (MK_COMB (@lem4614772 _108414 P t x) (@lem4614823 _108414 x t P)). Qed.
Lemma lem4614829 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : ((term26 _108414 P t x) = (term42 _108414 x t P)) = ((term25 _108414 P x t) = (term23 _108414 x t P)).
Proof. exact (SYM (@lem4614826 _108414 x t P)). Qed.
Lemma lem4614831 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4614832 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : ((term26 _108414 P t x) = (term42 _108414 x t P)) = (term44 _108414 x t P).
Proof. exact (@lem4614831 ((term26 _108414 P t x) = (term42 _108414 x t P))). Qed.
Lemma lem4614833 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term44 _108414 x t P) = ((term26 _108414 P t x) = (term42 _108414 x t P)).
Proof. exact (SYM (@lem4614832 _108414 x t P)). Qed.
Lemma lem4614834 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term45 _108414 x t P) : term45 _108414 x t P.
Proof. exact (h1). Qed.
Lemma lem4614837 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term44 _108414 x t P) : term44 _108414 x t P.
Proof. exact (h1). Qed.
Lemma lem4614838 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term46 _108414 x t P.
Proof. exact (fun h0 : term44 _108414 x t P => @lem4614837 _108414 x t P h0). Qed.
Lemma lem4614839 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term46 _108414 x t P) : term46 _108414 x t P.
Proof. exact (h1). Qed.
Lemma lem4614840 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term44 _108414 x t P) : term44 _108414 x t P.
Proof. exact (h1). Qed.
Lemma lem4614841 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term44 _108414 x t P) (h2 : term46 _108414 x t P) : term44 _108414 x t P.
Proof. exact (@lem4614839 _108414 x t P h2 (@lem4614840 _108414 x t P h1)). Qed.
Lemma lem4614842 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term44 _108414 x t P) : term47 _108414 x t P.
Proof. exact (fun h0 : term46 _108414 x t P => @lem4614841 _108414 x t P h1 h0). Qed.
Lemma lem4614843 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term46 _108414 x t P) : term46 _108414 x t P.
Proof. exact (h1). Qed.
Lemma lem4614844 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term44 _108414 x t P) (h2 : term46 _108414 x t P) : term44 _108414 x t P.
Proof. exact (@lem4614842 _108414 x t P h1 (@lem4614843 _108414 x t P h2)). Qed.
Lemma lem4614845 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term46 _108414 x t P) : term46 _108414 x t P.
Proof. exact (fun h0 : term44 _108414 x t P => @lem4614844 _108414 x t P h0 h1). Qed.
Lemma lem4614846 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term48 _108414 x t P.
Proof. exact (fun h0 : term46 _108414 x t P => @lem4614845 _108414 x t P h0). Qed.
Lemma lem4614849 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term46 _108414 x t P.
Proof. exact (@lem4614846 _108414 x t P (@lem4614838 _108414 x t P)). Qed.
Lemma lem4614850 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term46 _108414 x t P.
Proof. exact (@lem4614849 _108414 x t P). Qed.
Lemma lem4614864 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4614865 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term44 _108414 x t P) = (term49 _108414 x t P).
Proof. exact (@lem4614864 (term45 _108414 x t P)). Qed.
Lemma lem4614867 (t : Prop) : (term50 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4614868 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term49 _108414 x t P) = ((term26 _108414 P t x) = (term42 _108414 x t P)).
Proof. exact (@lem4614867 ((term26 _108414 P t x) = (term42 _108414 x t P))). Qed.
Lemma lem4614869 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term44 _108414 x t P) = ((term26 _108414 P t x) = (term42 _108414 x t P)).
Proof. exact (TRANS (@lem4614865 _108414 x t P) (@lem4614868 _108414 x t P)). Qed.
Lemma lem4614880 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) : (term51 _108414 t P) = (term52 _108414 t P).
Proof. exact (fun_ext (fun x : _108414 => @lem4614869 _108414 x t P)). Qed.
Lemma lem4614881 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4614882 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) : (term53 _108414 t P) = (term54 _108414 t P).
Proof. exact (MK_COMB (@lem4614881 _108414) (@lem4614880 _108414 t P)). Qed.
Lemma lem4614887 {_108414 : Type'} (P : Prop) : (term55 _108414 P) = (term56 _108414 P).
Proof. exact (fun_ext (fun t : _108414 -> Prop => @lem4614882 _108414 t P)). Qed.
Lemma lem4614888 {_108414 : Type'} : (@all (_108414 -> Prop)) = (@all (_108414 -> Prop)).
Proof. exact (eq_refl (@all (_108414 -> Prop))). Qed.
Lemma lem4614889 {_108414 : Type'} (P : Prop) : (term57 _108414 P) = (term58 _108414 P).
Proof. exact (MK_COMB (@lem4614888 _108414) (@lem4614887 _108414 P)). Qed.
Lemma lem4614894 {_108414 : Type'} : (term59 _108414) = (term60 _108414).
Proof. exact (fun_ext (fun P : Prop => @lem4614889 _108414 P)). Qed.
Lemma lem4614895 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4614904 {_108414 : Type'} : (term61 _108414) = (term62 _108414).
Proof. exact (MK_COMB (@lem4614895) (@lem4614894 _108414)). Qed.
Lemma lem4614905 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4614910 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term37 _108414 x t x') = (term37 _108414 x t x').
Proof. exact (eq_refl (term37 _108414 x t x')). Qed.
Lemma lem4614911 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term39 _108414 x t) = (term39 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4614910 _108414 x t x')). Qed.
Lemma lem4614912 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4614913 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term40 _108414 x t) = (term40 _108414 x t).
Proof. exact (MK_COMB (@lem4614912 _108414) (@lem4614911 _108414 x t)). Qed.
Lemma lem4614914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4614915 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term41 _108414 x t) = (term41 _108414 x t).
Proof. exact (MK_COMB (@lem4614914) (@lem4614913 _108414 x t)). Qed.
Lemma lem4614916 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term42 _108414 x t P) = (term42 _108414 x t P).
Proof. exact (MK_COMB (@lem4614915 _108414 x t) (@lem4614905 P)). Qed.
Lemma lem4614923 {_108414 : Type'} (P : Prop) (t : _108414 -> Prop) (x : _108414) : (term27 _108414 P t x) = (term27 _108414 P t x).
Proof. exact (eq_refl (term27 _108414 P t x)). Qed.
Lemma lem4614924 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : ((term26 _108414 P t x) = (term42 _108414 x t P)) = ((term26 _108414 P t x) = (term42 _108414 x t P)).
Proof. exact (MK_COMB (@lem4614923 _108414 P t x) (@lem4614916 _108414 x t P)). Qed.
Lemma lem4614925 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) : (term52 _108414 t P) = (term52 _108414 t P).
Proof. exact (fun_ext (fun x : _108414 => @lem4614924 _108414 x t P)). Qed.
Lemma lem4614926 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4614927 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) : (term54 _108414 t P) = (term54 _108414 t P).
Proof. exact (MK_COMB (@lem4614926 _108414) (@lem4614925 _108414 t P)). Qed.
Lemma lem4614928 {_108414 : Type'} (P : Prop) : (term56 _108414 P) = (term56 _108414 P).
Proof. exact (fun_ext (fun t : _108414 -> Prop => @lem4614927 _108414 t P)). Qed.
Lemma lem4614929 {_108414 : Type'} : (@all (_108414 -> Prop)) = (@all (_108414 -> Prop)).
Proof. exact (eq_refl (@all (_108414 -> Prop))). Qed.
Lemma lem4614930 {_108414 : Type'} (P : Prop) : (term58 _108414 P) = (term58 _108414 P).
Proof. exact (MK_COMB (@lem4614929 _108414) (@lem4614928 _108414 P)). Qed.
Lemma lem4614931 {_108414 : Type'} : (term60 _108414) = (term60 _108414).
Proof. exact (fun_ext (fun P : Prop => @lem4614930 _108414 P)). Qed.
Lemma lem4614932 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4614933 {_108414 : Type'} : (term62 _108414) = (term62 _108414).
Proof. exact (MK_COMB (@lem4614932) (@lem4614931 _108414)). Qed.
Lemma lem4614934 {_108414 : Type'} : (term61 _108414) = (term62 _108414).
Proof. exact (TRANS (@lem4614904 _108414) (@lem4614933 _108414)). Qed.
Lemma lem4614940 (P : Prop -> Prop) : (term63 P) = (term64 P).
Proof. exact (EQ_MP (@lem11005 P) (@lem11004 P)). Qed.
Lemma lem4614941 {_108414 : Type'} : (term65 _108414) = (term66 _108414).
Proof. exact (@lem4614940 (term60 _108414)). Qed.
Lemma lem4614942 {_108414 : Type'} (P : Prop) : (term67 _108414 P) = (term58 _108414 P).
Proof. exact (eq_refl (term67 _108414 P)). Qed.
Lemma lem4614943 {_108414 : Type'} : (term68 _108414) = (term60 _108414).
Proof. exact (fun_ext (fun P : Prop => @lem4614942 _108414 P)). Qed.
Lemma lem4614944 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4614945 {_108414 : Type'} : (term65 _108414) = (term62 _108414).
Proof. exact (MK_COMB (@lem4614944) (@lem4614943 _108414)). Qed.
Lemma lem4614946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4614947 {_108414 : Type'} : (term69 _108414) = (term70 _108414).
Proof. exact (MK_COMB (@lem4614946) (@lem4614945 _108414)). Qed.
Lemma lem4614948 {_108414 : Type'} : (term71 _108414) = (term72 _108414).
Proof. exact (eq_refl (term71 _108414)). Qed.
Lemma lem4614949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4614950 {_108414 : Type'} : (term73 _108414) = (term74 _108414).
Proof. exact (MK_COMB (@lem4614949) (@lem4614948 _108414)). Qed.
Lemma lem4614951 {_108414 : Type'} : (term75 _108414) = (term76 _108414).
Proof. exact (eq_refl (term75 _108414)). Qed.
Lemma lem4614952 {_108414 : Type'} : (term66 _108414) = (term77 _108414).
Proof. exact (MK_COMB (@lem4614950 _108414) (@lem4614951 _108414)). Qed.
Lemma lem4614953 {_108414 : Type'} : ((term65 _108414) = (term66 _108414)) = ((term62 _108414) = (term77 _108414)).
Proof. exact (MK_COMB (@lem4614947 _108414) (@lem4614952 _108414)). Qed.
Lemma lem4614954 {_108414 : Type'} : (term62 _108414) = (term77 _108414).
Proof. exact (EQ_MP (@lem4614953 _108414) (@lem4614941 _108414)). Qed.
Lemma lem4614970 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem21760 t)). Qed.
Lemma lem4614971 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term78 _108414 t x) = (t x).
Proof. exact (@lem4614970 (t x)). Qed.
Lemma lem4614972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4614973 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term79 _108414 t x) = (term80 _108414 t x).
Proof. exact (MK_COMB (@lem4614972) (@lem4614971 _108414 t x)). Qed.
Lemma lem4614975 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem4614976 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term81 _108414 x t) = (term40 _108414 x t).
Proof. exact (@lem4614975 (term40 _108414 x t)). Qed.
Lemma lem4614985 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : ((term78 _108414 t x) = (term81 _108414 x t)) = ((t x) = (term40 _108414 x t)).
Proof. exact (MK_COMB (@lem4614973 _108414 t x) (@lem4614976 _108414 x t)). Qed.
Lemma lem4614986 {_108414 : Type'} (t : _108414 -> Prop) : (term82 _108414 t) = (term83 _108414 t).
Proof. exact (fun_ext (fun x : _108414 => @lem4614985 _108414 x t)). Qed.
Lemma lem4614987 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4614988 {_108414 : Type'} (t : _108414 -> Prop) : (term84 _108414 t) = (term85 _108414 t).
Proof. exact (MK_COMB (@lem4614987 _108414) (@lem4614986 _108414 t)). Qed.
Lemma lem4614995 {_108414 : Type'} : (term86 _108414) = (term87 _108414).
Proof. exact (fun_ext (fun t : _108414 -> Prop => @lem4614988 _108414 t)). Qed.
Lemma lem4614996 {_108414 : Type'} : (@all (_108414 -> Prop)) = (@all (_108414 -> Prop)).
Proof. exact (eq_refl (@all (_108414 -> Prop))). Qed.
Lemma lem4614997 {_108414 : Type'} : (term72 _108414) = (term88 _108414).
Proof. exact (MK_COMB (@lem4614996 _108414) (@lem4614995 _108414)). Qed.
Lemma lem4615004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4615005 {_108414 : Type'} : (term74 _108414) = (term89 _108414).
Proof. exact (MK_COMB (@lem4615004) (@lem4614997 _108414)). Qed.
Lemma lem4615019 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem21762 t)). Qed.
Lemma lem4615020 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term90 _108414 t x) = False.
Proof. exact (@lem4615019 (t x)). Qed.
Lemma lem4615021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615022 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term91 _108414 t x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4615021) (@lem4615020 _108414 t x)). Qed.
Lemma lem4615024 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem21763 t)). Qed.
Lemma lem4615025 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term92 _108414 x t) = False.
Proof. exact (@lem4615024 (term40 _108414 x t)). Qed.
Lemma lem4615026 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : ((term90 _108414 t x) = (term92 _108414 x t)) = (False = False).
Proof. exact (MK_COMB (@lem4615022 _108414 t x) (@lem4615025 _108414 x t)). Qed.
Lemma lem4615028 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem21742 t)). Qed.
Lemma lem4615029 : (False = False) = (~ False).
Proof. exact (@lem4615028 False). Qed.
Lemma lem4615031 : (~ False) = True.
Proof. exact (proj2 (@lem21780)). Qed.
Lemma lem4615032 : (False = False) = True.
Proof. exact (TRANS (@lem4615029) (@lem4615031)). Qed.
Lemma lem4615033 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : ((term90 _108414 t x) = (term92 _108414 x t)) = True.
Proof. exact (TRANS (@lem4615026 _108414 x t) (@lem4615032)). Qed.
Lemma lem4615034 {_108414 : Type'} (t : _108414 -> Prop) : (term93 _108414 t) = (term94 _108414).
Proof. exact (fun_ext (fun x : _108414 => @lem4615033 _108414 x t)). Qed.
Lemma lem4615035 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4615036 {_108414 : Type'} (t : _108414 -> Prop) : (term95 _108414 t) = (term96 _108414).
Proof. exact (MK_COMB (@lem4615035 _108414) (@lem4615034 _108414 t)). Qed.
Lemma lem4615038 {A : Type'} (t : Prop) : (term97 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem4615039 {_108414 : Type'} (t : Prop) : (term97 _108414 t) = t.
Proof. exact (@lem4615038 _108414 t). Qed.
Lemma lem4615040 {_108414 : Type'} : (term96 _108414) = True.
Proof. exact (@lem4615039 _108414 True). Qed.
Lemma lem4615041 {_108414 : Type'} (t : _108414 -> Prop) : (term95 _108414 t) = True.
Proof. exact (TRANS (@lem4615036 _108414 t) (@lem4615040 _108414)). Qed.
Lemma lem4615042 {_108414 : Type'} : (term98 _108414) = (term99 _108414).
Proof. exact (fun_ext (fun t : _108414 -> Prop => @lem4615041 _108414 t)). Qed.
Lemma lem4615043 {_108414 : Type'} : (@all (_108414 -> Prop)) = (@all (_108414 -> Prop)).
Proof. exact (eq_refl (@all (_108414 -> Prop))). Qed.
Lemma lem4615044 {_108414 : Type'} : (term76 _108414) = (term100 _108414).
Proof. exact (MK_COMB (@lem4615043 _108414) (@lem4615042 _108414)). Qed.
Lemma lem4615046 {A : Type'} (t : Prop) : (term97 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem4615047 {_108414 : Type'} (t : Prop) : (term101 _108414 t) = t.
Proof. exact (@lem4615046 (_108414 -> Prop) t). Qed.
Lemma lem4615048 {_108414 : Type'} : (term100 _108414) = True.
Proof. exact (@lem4615047 _108414 True). Qed.
Lemma lem4615049 {_108414 : Type'} : (term76 _108414) = True.
Proof. exact (TRANS (@lem4615044 _108414) (@lem4615048 _108414)). Qed.
Lemma lem4615050 {_108414 : Type'} : (term77 _108414) = (term102 _108414).
Proof. exact (MK_COMB (@lem4615005 _108414) (@lem4615049 _108414)). Qed.
Lemma lem4615052 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem4615053 {_108414 : Type'} : (term102 _108414) = (term88 _108414).
Proof. exact (@lem4615052 (term88 _108414)). Qed.
Lemma lem4615074 {_108414 : Type'} : (term77 _108414) = (term88 _108414).
Proof. exact (TRANS (@lem4615050 _108414) (@lem4615053 _108414)). Qed.
Lemma lem4615075 {_108414 : Type'} : (term62 _108414) = (term88 _108414).
Proof. exact (TRANS (@lem4614954 _108414) (@lem4615074 _108414)). Qed.
Lemma lem4615076 {_108414 : Type'} : (term61 _108414) = (term88 _108414).
Proof. exact (TRANS (@lem4614934 _108414) (@lem4615075 _108414)). Qed.
Lemma lem4615077 {_108414 : Type'} : (term88 _108414) = (term61 _108414).
Proof. exact (SYM (@lem4615076 _108414)). Qed.
Lemma lem4615079 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4615080 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : ((t x) = (term40 _108414 x t)) = (term103 _108414 x t).
Proof. exact (@lem4615079 ((t x) = (term40 _108414 x t))). Qed.
Lemma lem4615081 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term103 _108414 x t) = ((t x) = (term40 _108414 x t)).
Proof. exact (SYM (@lem4615080 _108414 x t)). Qed.
Lemma lem4615082 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term104 _108414 x t) : term104 _108414 x t.
Proof. exact (h1). Qed.
Lemma lem4615093 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term105 _108414 x t x') = (term106 _108414 x t x').
Proof. exact (@lem17362 (x' = x) (t x')). Qed.
Lemma lem4615098 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term37 _108414 x t x') = (term107 _108414 x t x').
Proof. exact (@lem17265 (x' = x) (t x')). Qed.
Lemma lem4615099 {_108414 : Type'} (P : _108414 -> Prop) : (term108 _108414 P) = (term109 _108414 P).
Proof. exact (@lem18392 _108414 P). Qed.
Lemma lem4615100 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term110 _108414 x t) = (term111 _108414 x t).
Proof. exact (@lem4615099 _108414 (term39 _108414 x t)). Qed.
Lemma lem4615101 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term112 _108414 x t x') = (term37 _108414 x t x').
Proof. exact (eq_refl (term112 _108414 x t x')). Qed.
Lemma lem4615102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4615103 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term113 _108414 x t x') = (term105 _108414 x t x').
Proof. exact (MK_COMB (@lem4615102) (@lem4615101 _108414 x t x')). Qed.
Lemma lem4615104 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term113 _108414 x t x') = (term106 _108414 x t x').
Proof. exact (TRANS (@lem4615103 _108414 x t x') (@lem4615093 _108414 x t x')). Qed.
Lemma lem4615105 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term114 _108414 x t) = (term115 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615104 _108414 x t x')). Qed.
Lemma lem4615106 {_108414 : Type'} : (@ex _108414) = (@ex _108414).
Proof. exact (eq_refl (@ex _108414)). Qed.
Lemma lem4615107 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term111 _108414 x t) = (term116 _108414 x t).
Proof. exact (MK_COMB (@lem4615106 _108414) (@lem4615105 _108414 x t)). Qed.
Lemma lem4615108 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term110 _108414 x t) = (term116 _108414 x t).
Proof. exact (TRANS (@lem4615100 _108414 x t) (@lem4615107 _108414 x t)). Qed.
Lemma lem4615109 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term39 _108414 x t) = (term117 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615098 _108414 x t x')). Qed.
Lemma lem4615110 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4615111 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term40 _108414 x t) = (term118 _108414 x t).
Proof. exact (MK_COMB (@lem4615110 _108414) (@lem4615109 _108414 x t)). Qed.
Lemma lem4615113 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term119 _108414 t x) = (term119 _108414 t x).
Proof. exact (eq_refl (term119 _108414 t x)). Qed.
Lemma lem4615114 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term120 _108414 x t) = (term121 _108414 x t).
Proof. exact (MK_COMB (@lem4615113 _108414 t x) (@lem4615111 _108414 x t)). Qed.
Lemma lem4615116 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term122 _108414 t x) = (term122 _108414 t x).
Proof. exact (eq_refl (term122 _108414 t x)). Qed.
Lemma lem4615117 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term123 _108414 x t) = (term124 _108414 x t).
Proof. exact (MK_COMB (@lem4615116 _108414 t x) (@lem4615108 _108414 x t)). Qed.
Lemma lem4615118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4615119 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term125 _108414 x t) = (term126 _108414 x t).
Proof. exact (MK_COMB (@lem4615118) (@lem4615117 _108414 x t)). Qed.
Lemma lem4615120 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term127 _108414 x t) = (term128 _108414 x t).
Proof. exact (MK_COMB (@lem4615119 _108414 x t) (@lem4615114 _108414 x t)). Qed.
Lemma lem4615121 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term104 _108414 x t) = (term127 _108414 x t).
Proof. exact (@lem17646 (t x) (term40 _108414 x t)). Qed.
Lemma lem4615122 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term104 _108414 x t) = (term128 _108414 x t).
Proof. exact (TRANS (@lem4615121 _108414 x t) (@lem4615120 _108414 x t)). Qed.
Lemma lem4615205 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4615206 {_108414 : Type'} (P : Prop) (Q : _108414 -> Prop) : (term129 _108414 P Q) = (term130 _108414 P Q).
Proof. exact (@lem4615205 _108414 P Q). Qed.
Lemma lem4615207 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term131 _108414 x t) = (term132 _108414 x t).
Proof. exact (@lem4615206 _108414 (t x) (term115 _108414 x t)). Qed.
Lemma lem4615208 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term133 _108414 x t x') = (term106 _108414 x t x').
Proof. exact (eq_refl (term133 _108414 x t x')). Qed.
Lemma lem4615209 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term134 _108414 x t) = (term115 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615208 _108414 x t x')). Qed.
Lemma lem4615210 {_108414 : Type'} : (@ex _108414) = (@ex _108414).
Proof. exact (eq_refl (@ex _108414)). Qed.
Lemma lem4615211 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term135 _108414 x t) = (term116 _108414 x t).
Proof. exact (MK_COMB (@lem4615210 _108414) (@lem4615209 _108414 x t)). Qed.
Lemma lem4615212 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term122 _108414 t x) = (term122 _108414 t x).
Proof. exact (eq_refl (term122 _108414 t x)). Qed.
Lemma lem4615213 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term131 _108414 x t) = (term124 _108414 x t).
Proof. exact (MK_COMB (@lem4615212 _108414 t x) (@lem4615211 _108414 x t)). Qed.
Lemma lem4615214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615215 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term136 _108414 x t) = (term137 _108414 x t).
Proof. exact (MK_COMB (@lem4615214) (@lem4615213 _108414 x t)). Qed.
Lemma lem4615216 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term133 _108414 x t x') = (term106 _108414 x t x').
Proof. exact (eq_refl (term133 _108414 x t x')). Qed.
Lemma lem4615217 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term122 _108414 t x) = (term122 _108414 t x).
Proof. exact (eq_refl (term122 _108414 t x)). Qed.
Lemma lem4615218 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term138 _108414 x t x') = (term139 _108414 x t x').
Proof. exact (MK_COMB (@lem4615217 _108414 t x) (@lem4615216 _108414 x t x')). Qed.
Lemma lem4615219 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term140 _108414 x t) = (term141 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615218 _108414 x t x')). Qed.
Lemma lem4615220 {_108414 : Type'} : (@ex _108414) = (@ex _108414).
Proof. exact (eq_refl (@ex _108414)). Qed.
Lemma lem4615221 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term132 _108414 x t) = (term142 _108414 x t).
Proof. exact (MK_COMB (@lem4615220 _108414) (@lem4615219 _108414 x t)). Qed.
Lemma lem4615222 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : ((term131 _108414 x t) = (term132 _108414 x t)) = ((term124 _108414 x t) = (term142 _108414 x t)).
Proof. exact (MK_COMB (@lem4615215 _108414 x t) (@lem4615221 _108414 x t)). Qed.
Lemma lem4615223 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term124 _108414 x t) = (term142 _108414 x t).
Proof. exact (EQ_MP (@lem4615222 _108414 x t) (@lem4615207 _108414 x t)). Qed.
Lemma lem4615224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4615225 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term126 _108414 x t) = (term143 _108414 x t).
Proof. exact (MK_COMB (@lem4615224) (@lem4615223 _108414 x t)). Qed.
Lemma lem4615226 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term121 _108414 x t) = (term121 _108414 x t).
Proof. exact (eq_refl (term121 _108414 x t)). Qed.
Lemma lem4615227 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term128 _108414 x t) = (term144 _108414 x t).
Proof. exact (MK_COMB (@lem4615225 _108414 x t) (@lem4615226 _108414 x t)). Qed.
Lemma lem4615229 {A : Type'} (P : A -> Prop) (Q : Prop) : (term145 A P Q) = (term146 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4615230 {_108414 : Type'} (P : _108414 -> Prop) (Q : Prop) : (term145 _108414 P Q) = (term146 _108414 P Q).
Proof. exact (@lem4615229 _108414 P Q). Qed.
Lemma lem4615231 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term147 _108414 x t) = (term148 _108414 x t).
Proof. exact (@lem4615230 _108414 (term141 _108414 x t) (term121 _108414 x t)). Qed.
Lemma lem4615232 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term149 _108414 x t x') = (term139 _108414 x t x').
Proof. exact (eq_refl (term149 _108414 x t x')). Qed.
Lemma lem4615233 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term150 _108414 x t) = (term141 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615232 _108414 x t x')). Qed.
Lemma lem4615234 {_108414 : Type'} : (@ex _108414) = (@ex _108414).
Proof. exact (eq_refl (@ex _108414)). Qed.
Lemma lem4615235 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term151 _108414 x t) = (term142 _108414 x t).
Proof. exact (MK_COMB (@lem4615234 _108414) (@lem4615233 _108414 x t)). Qed.
Lemma lem4615236 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4615237 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term152 _108414 x t) = (term143 _108414 x t).
Proof. exact (MK_COMB (@lem4615236) (@lem4615235 _108414 x t)). Qed.
Lemma lem4615238 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term121 _108414 x t) = (term121 _108414 x t).
Proof. exact (eq_refl (term121 _108414 x t)). Qed.
Lemma lem4615239 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term147 _108414 x t) = (term144 _108414 x t).
Proof. exact (MK_COMB (@lem4615237 _108414 x t) (@lem4615238 _108414 x t)). Qed.
Lemma lem4615240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615241 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term153 _108414 x t) = (term154 _108414 x t).
Proof. exact (MK_COMB (@lem4615240) (@lem4615239 _108414 x t)). Qed.
Lemma lem4615242 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term149 _108414 x t x') = (term139 _108414 x t x').
Proof. exact (eq_refl (term149 _108414 x t x')). Qed.
Lemma lem4615243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4615244 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term155 _108414 x t x') = (term156 _108414 x t x').
Proof. exact (MK_COMB (@lem4615243) (@lem4615242 _108414 x t x')). Qed.
Lemma lem4615245 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term121 _108414 x t) = (term121 _108414 x t).
Proof. exact (eq_refl (term121 _108414 x t)). Qed.
Lemma lem4615246 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) : (term157 _108414 x' x t) = (term158 _108414 x' x t).
Proof. exact (MK_COMB (@lem4615244 _108414 x t x') (@lem4615245 _108414 x t)). Qed.
Lemma lem4615247 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term159 _108414 x t) = (term160 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615246 _108414 x' x t)). Qed.
Lemma lem4615248 {_108414 : Type'} : (@ex _108414) = (@ex _108414).
Proof. exact (eq_refl (@ex _108414)). Qed.
Lemma lem4615249 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term148 _108414 x t) = (term161 _108414 x t).
Proof. exact (MK_COMB (@lem4615248 _108414) (@lem4615247 _108414 x t)). Qed.
Lemma lem4615250 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : ((term147 _108414 x t) = (term148 _108414 x t)) = ((term144 _108414 x t) = (term161 _108414 x t)).
Proof. exact (MK_COMB (@lem4615241 _108414 x t) (@lem4615249 _108414 x t)). Qed.
Lemma lem4615251 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term144 _108414 x t) = (term161 _108414 x t).
Proof. exact (EQ_MP (@lem4615250 _108414 x t) (@lem4615231 _108414 x t)). Qed.
Lemma lem4615253 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term128 _108414 x t) = (term161 _108414 x t).
Proof. exact (TRANS (@lem4615227 _108414 x t) (@lem4615251 _108414 x t)). Qed.
Lemma lem4615254 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term104 _108414 x t) = (term161 _108414 x t).
Proof. exact (TRANS (@lem4615122 _108414 x t) (@lem4615253 _108414 x t)). Qed.
Lemma lem4615255 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term104 _108414 x t) : term161 _108414 x t.
Proof. exact (EQ_MP (@lem4615254 _108414 x t) (@lem4615082 _108414 x t h1)). Qed.
Lemma lem4615256 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term158 _108414 x' x t) : term158 _108414 x' x t.
Proof. exact (h1). Qed.
Lemma lem4615269 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term107 _108414 x t x') = (term107 _108414 x t x').
Proof. exact (eq_refl (term107 _108414 x t x')). Qed.
Lemma lem4615270 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term117 _108414 x t) = (term117 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615269 _108414 x t x')). Qed.
Lemma lem4615271 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4615272 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term118 _108414 x t) = (term118 _108414 x t).
Proof. exact (MK_COMB (@lem4615271 _108414) (@lem4615270 _108414 x t)). Qed.
Lemma lem4615279 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term119 _108414 t x) = (term119 _108414 t x).
Proof. exact (eq_refl (term119 _108414 t x)). Qed.
Lemma lem4615280 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term121 _108414 x t) = (term121 _108414 x t).
Proof. exact (MK_COMB (@lem4615279 _108414 t x) (@lem4615272 _108414 x t)). Qed.
Lemma lem4615301 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term156 _108414 x t x') = (term156 _108414 x t x').
Proof. exact (eq_refl (term156 _108414 x t x')). Qed.
Lemma lem4615302 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) : (term158 _108414 x' x t) = (term158 _108414 x' x t).
Proof. exact (MK_COMB (@lem4615301 _108414 x t x') (@lem4615280 _108414 x t)). Qed.
Lemma lem4615303 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term158 _108414 x' x t) : term158 _108414 x' x t.
Proof. exact (EQ_MP (@lem4615302 _108414 x' x t) (@lem4615256 _108414 x' x t h1)). Qed.
Lemma lem4615304 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term139 _108414 x t x'.
Proof. exact (h1). Qed.
Lemma lem4615305 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term121 _108414 x t.
Proof. exact (h1). Qed.
Lemma lem4615306 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term106 _108414 x t x'.
Proof. exact (proj2 (@lem4615304 _108414 x t x' h1)). Qed.
Lemma lem4615310 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term118 _108414 x t.
Proof. exact (proj2 (@lem4615305 _108414 x t h1)). Qed.
Lemma lem4615335 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) : (term107 _108414 x t x') = (term107 _108414 x t x').
Proof. exact (eq_refl (term107 _108414 x t x')). Qed.
Lemma lem4615336 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term117 _108414 x t) = (term117 _108414 x t).
Proof. exact (fun_ext (fun x' : _108414 => @lem4615335 _108414 x t x')). Qed.
Lemma lem4615337 {_108414 : Type'} : (@all _108414) = (@all _108414).
Proof. exact (eq_refl (@all _108414)). Qed.
Lemma lem4615339 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (term118 _108414 x t) = (term118 _108414 x t).
Proof. exact (MK_COMB (@lem4615337 _108414) (@lem4615336 _108414 x t)). Qed.
Lemma lem4615340 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term118 _108414 x t.
Proof. exact (EQ_MP (@lem4615339 _108414 x t) (@lem4615310 _108414 x t h1)). Qed.
Lemma lem4615341 {_108414 : Type'} (_55463 : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term162 _108414 x t _55463.
Proof. exact (@lem4615340 _108414 x t h1 _55463). Qed.
Lemma lem4615342 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (_55463 : _108414) : (term162 _108414 x t _55463) = (term107 _108414 x t _55463).
Proof. exact (eq_refl (term162 _108414 x t _55463)). Qed.
Lemma lem4615347 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : x' = x.
Proof. exact (proj1 (@lem4615306 _108414 x t x' h1)). Qed.
Lemma lem4615349 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term163 _108414 t x'.
Proof. exact (proj2 (@lem4615306 _108414 x t x' h1)). Qed.
Lemma lem4615351 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term163 _108414 t x.
Proof. exact (proj1 (@lem4615305 _108414 x t h1)). Qed.
Lemma lem4615357 {_108414 : Type'} (_55463 : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term107 _108414 x t _55463.
Proof. exact (EQ_MP (@lem4615342 _108414 x t _55463) (@lem4615341 _108414 _55463 x t h1)). Qed.
Lemma lem4615386 {_108414 : Type'} (t : _108414 -> Prop) : (term164 _108414 t) = (term164 _108414 t).
Proof. exact (eq_refl (term164 _108414 t)). Qed.
Lemma lem4615387 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : (term165 _108414 t x') = (term165 _108414 t x).
Proof. exact (MK_COMB (@lem4615386 _108414 t) (@lem4615347 _108414 x t x' h1)). Qed.
Lemma lem4615388 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term165 _108414 t x) = (term163 _108414 t x).
Proof. exact (eq_refl (term165 _108414 t x)). Qed.
Lemma lem4615389 {_108414 : Type'} (t : _108414 -> Prop) (x' : _108414) : (term166 _108414 t x') = (term166 _108414 t x').
Proof. exact (eq_refl (term166 _108414 t x')). Qed.
Lemma lem4615390 {_108414 : Type'} (x' : _108414) (t : _108414 -> Prop) (x : _108414) : ((term165 _108414 t x') = (term165 _108414 t x)) = ((term165 _108414 t x') = (term163 _108414 t x)).
Proof. exact (MK_COMB (@lem4615389 _108414 t x') (@lem4615388 _108414 t x)). Qed.
Lemma lem4615391 {_108414 : Type'} (t : _108414 -> Prop) (x' : _108414) : (term165 _108414 t x') = (term163 _108414 t x').
Proof. exact (eq_refl (term165 _108414 t x')). Qed.
Lemma lem4615392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615393 {_108414 : Type'} (t : _108414 -> Prop) (x' : _108414) : (term166 _108414 t x') = (term167 _108414 t x').
Proof. exact (MK_COMB (@lem4615392) (@lem4615391 _108414 t x')). Qed.
Lemma lem4615394 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term163 _108414 t x) = (term163 _108414 t x).
Proof. exact (eq_refl (term163 _108414 t x)). Qed.
Lemma lem4615395 {_108414 : Type'} (x' : _108414) (t : _108414 -> Prop) (x : _108414) : ((term165 _108414 t x') = (term163 _108414 t x)) = ((term163 _108414 t x') = (term163 _108414 t x)).
Proof. exact (MK_COMB (@lem4615393 _108414 t x') (@lem4615394 _108414 t x)). Qed.
Lemma lem4615396 {_108414 : Type'} (x' : _108414) (t : _108414 -> Prop) (x : _108414) : ((term165 _108414 t x') = (term165 _108414 t x)) = ((term163 _108414 t x') = (term163 _108414 t x)).
Proof. exact (TRANS (@lem4615390 _108414 x' t x) (@lem4615395 _108414 x' t x)). Qed.
Lemma lem4615397 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : (term163 _108414 t x') = (term163 _108414 t x).
Proof. exact (EQ_MP (@lem4615396 _108414 x' t x) (@lem4615387 _108414 x t x' h1)). Qed.
Lemma lem4615398 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term163 _108414 t x.
Proof. exact (EQ_MP (@lem4615397 _108414 x t x' h1) (@lem4615349 _108414 x t x' h1)). Qed.
Lemma lem4615400 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : t x.
Proof. exact (proj1 (@lem4615304 _108414 x t x' h1)). Qed.
Lemma lem4615401 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term168 _108414 t x.
Proof. exact (fun h0 : term163 _108414 t x => @lem4615400 _108414 x t x' h1). Qed.
Lemma lem4615403 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4615404 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term168 _108414 t x) = (t x).
Proof. exact (@lem4615403 (t x)). Qed.
Lemma lem4615405 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : t x.
Proof. exact (EQ_MP (@lem4615404 _108414 t x) (@lem4615401 _108414 x t x' h1)). Qed.
Lemma lem4615408 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4615410 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term163 _108414 t x) = (term170 _108414 t x).
Proof. exact (@lem4615408 (t x)). Qed.
Lemma lem4615413 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term170 _108414 t x.
Proof. exact (EQ_MP (@lem4615410 _108414 t x) (@lem4615398 _108414 x t x' h1)). Qed.
Lemma lem4615416 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : False.
Proof. exact (@lem4615413 _108414 x t x' h1 (@lem4615405 _108414 x t x' h1)). Qed.
Lemma lem4615417 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : term171.
Proof. exact (fun h0 : ~ False => @lem4615416 _108414 x t x' h1). Qed.
Lemma lem4615419 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4615420 : term171 = False.
Proof. exact (@lem4615419 False). Qed.
Lemma lem4615437 {_108414 : Type'} (x : _108414) : x = x.
Proof. exact (@lem21386 _108414 x). Qed.
Lemma lem4615438 {_108414 : Type'} (x : _108414) : x = x.
Proof. exact (@lem4615437 _108414 x). Qed.
Lemma lem4615439 {_108414 : Type'} (x : _108414) : term172 _108414 x.
Proof. exact (fun h0 : term173 _108414 x => @lem4615438 _108414 x). Qed.
Lemma lem4615441 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4615442 {_108414 : Type'} (x : _108414) : (term172 _108414 x) = (x = x).
Proof. exact (@lem4615441 (x = x)). Qed.
Lemma lem4615443 {_108414 : Type'} (x : _108414) : x = x.
Proof. exact (EQ_MP (@lem4615442 _108414 x) (@lem4615439 _108414 x)). Qed.
Lemma lem4615449 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4615450 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : (term107 _108414 x t _55463) = (term174 _108414 t _55463 x).
Proof. exact (@lem4615449 (t _55463) (term175 _108414 _55463 x)). Qed.
Lemma lem4615458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615459 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : (term176 _108414 x t _55463) = (term177 _108414 t _55463 x).
Proof. exact (MK_COMB (@lem4615458) (@lem4615450 _108414 t _55463 x)). Qed.
Lemma lem4615467 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : (term174 _108414 t _55463 x) = (term174 _108414 t _55463 x).
Proof. exact (eq_refl (term174 _108414 t _55463 x)). Qed.
Lemma lem4615468 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : ((term107 _108414 x t _55463) = (term174 _108414 t _55463 x)) = ((term174 _108414 t _55463 x) = (term174 _108414 t _55463 x)).
Proof. exact (MK_COMB (@lem4615459 _108414 t _55463 x) (@lem4615467 _108414 t _55463 x)). Qed.
Lemma lem4615470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4615471 (x : Prop) : (x = x) = True.
Proof. exact (@lem4615470 Prop x). Qed.
Lemma lem4615472 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : ((term174 _108414 t _55463 x) = (term174 _108414 t _55463 x)) = True.
Proof. exact (@lem4615471 (term174 _108414 t _55463 x)). Qed.
Lemma lem4615473 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : ((term107 _108414 x t _55463) = (term174 _108414 t _55463 x)) = True.
Proof. exact (TRANS (@lem4615468 _108414 t _55463 x) (@lem4615472 _108414 t _55463 x)). Qed.
Lemma lem4615474 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : True = ((term107 _108414 x t _55463) = (term174 _108414 t _55463 x)).
Proof. exact (SYM (@lem4615473 _108414 t _55463 x)). Qed.
Lemma lem4615475 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) (x : _108414) : (term107 _108414 x t _55463) = (term174 _108414 t _55463 x).
Proof. exact (EQ_MP (@lem4615474 _108414 t _55463 x) (@lem0)). Qed.
Lemma lem4615476 {_108414 : Type'} (_55463 : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term174 _108414 t _55463 x.
Proof. exact (EQ_MP (@lem4615475 _108414 t _55463 x) (@lem4615357 _108414 _55463 x t h1)). Qed.
Lemma lem4615478 (b : Prop) (a : Prop) : (a \/ b) = (term178 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4615479 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (_55463 : _108414) : (term174 _108414 t _55463 x) = (term179 _108414 x t _55463).
Proof. exact (@lem4615478 (term175 _108414 _55463 x) (t _55463)). Qed.
Lemma lem4615481 (a : Prop) : (term50 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4615482 {_108414 : Type'} (_55463 : _108414) (x : _108414) : (term180 _108414 _55463 x) = (_55463 = x).
Proof. exact (@lem4615481 (_55463 = x)). Qed.
Lemma lem4615483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4615484 {_108414 : Type'} (_55463 : _108414) (x : _108414) : (term181 _108414 _55463 x) = (term35 _108414 _55463 x).
Proof. exact (MK_COMB (@lem4615483) (@lem4615482 _108414 _55463 x)). Qed.
Lemma lem4615485 {_108414 : Type'} (t : _108414 -> Prop) (_55463 : _108414) : (t _55463) = (t _55463).
Proof. exact (eq_refl (t _55463)). Qed.
Lemma lem4615486 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (_55463 : _108414) : (term179 _108414 x t _55463) = (term37 _108414 x t _55463).
Proof. exact (MK_COMB (@lem4615484 _108414 _55463 x) (@lem4615485 _108414 t _55463)). Qed.
Lemma lem4615487 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (_55463 : _108414) : (term174 _108414 t _55463 x) = (term37 _108414 x t _55463).
Proof. exact (TRANS (@lem4615479 _108414 x t _55463) (@lem4615486 _108414 x t _55463)). Qed.
Lemma lem4615490 {_108414 : Type'} (_55463 : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term37 _108414 x t _55463.
Proof. exact (EQ_MP (@lem4615487 _108414 x t _55463) (@lem4615476 _108414 _55463 x t h1)). Qed.
Lemma lem4615491 {_108414 : Type'} (_55463 : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term37 _108414 x t _55463.
Proof. exact (@lem4615490 _108414 _55463 x t h1). Qed.
Lemma lem4615492 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term182 _108414 t x.
Proof. exact (@lem4615491 _108414 x x t h1). Qed.
Lemma lem4615495 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : t x.
Proof. exact (@lem4615492 _108414 x t h1 (@lem4615443 _108414 x)). Qed.
Lemma lem4615496 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term168 _108414 t x.
Proof. exact (fun h0 : term163 _108414 t x => @lem4615495 _108414 x t h1). Qed.
Lemma lem4615498 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4615499 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term168 _108414 t x) = (t x).
Proof. exact (@lem4615498 (t x)). Qed.
Lemma lem4615500 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : t x.
Proof. exact (EQ_MP (@lem4615499 _108414 t x) (@lem4615496 _108414 x t h1)). Qed.
Lemma lem4615503 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4615505 {_108414 : Type'} (t : _108414 -> Prop) (x : _108414) : (term163 _108414 t x) = (term170 _108414 t x).
Proof. exact (@lem4615503 (t x)). Qed.
Lemma lem4615508 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term170 _108414 t x.
Proof. exact (EQ_MP (@lem4615505 _108414 t x) (@lem4615351 _108414 x t h1)). Qed.
Lemma lem4615511 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : False.
Proof. exact (@lem4615508 _108414 x t h1 (@lem4615500 _108414 x t h1)). Qed.
Lemma lem4615512 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : term171.
Proof. exact (fun h0 : ~ False => @lem4615511 _108414 x t h1). Qed.
Lemma lem4615514 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4615515 : term171 = False.
Proof. exact (@lem4615514 False). Qed.
Lemma lem4615516 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term121 _108414 x t) : False.
Proof. exact (EQ_MP (@lem4615515) (@lem4615512 _108414 x t h1)). Qed.
Lemma lem4615517 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (x' : _108414) (h1 : term139 _108414 x t x') : False.
Proof. exact (EQ_MP (@lem4615420) (@lem4615417 _108414 x t x' h1)). Qed.
Lemma lem4615518 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term158 _108414 x' x t) : False.
Proof. exact (or_elim (@lem4615303 _108414 x' x t h1) (fun h0 : term139 _108414 x t x' => @lem4615517 _108414 x t x' h0) (fun h0 : term121 _108414 x t => @lem4615516 _108414 x t h0)). Qed.
Lemma lem4615519 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term158 _108414 x' x t) : (term158 _108414 x' x t) = False.
Proof. exact (prop_ext (fun h2 : term158 _108414 x' x t => @lem4615518 _108414 x' x t h1) (fun h2 : False => @lem4615303 _108414 x' x t h1)). Qed.
Lemma lem4615520 {_108414 : Type'} (x' : _108414) (x : _108414) (t : _108414 -> Prop) (h1 : term158 _108414 x' x t) : False.
Proof. exact (EQ_MP (@lem4615519 _108414 x' x t h1) (@lem4615303 _108414 x' x t h1)). Qed.
Lemma lem4615521 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term104 _108414 x t) : False.
Proof. exact (ex_elim (@lem4615255 _108414 x t h1) (fun x' : _108414 => fun h0 : term160 _108414 x t x' => @lem4615520 _108414 x' x t h0)). Qed.
Lemma lem4615522 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term104 _108414 x t) : (term104 _108414 x t) = False.
Proof. exact (prop_ext (fun h2 : term104 _108414 x t => @lem4615521 _108414 x t h1) (fun h2 : False => @lem4615082 _108414 x t h1)). Qed.
Lemma lem4615523 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (h1 : term104 _108414 x t) : False.
Proof. exact (EQ_MP (@lem4615522 _108414 x t h1) (@lem4615082 _108414 x t h1)). Qed.
Lemma lem4615524 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : term103 _108414 x t.
Proof. exact (fun h0 : term104 _108414 x t => @lem4615523 _108414 x t h0). Qed.
Lemma lem4615525 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) : (t x) = (term40 _108414 x t).
Proof. exact (EQ_MP (@lem4615081 _108414 x t) (@lem4615524 _108414 x t)). Qed.
Lemma lem4615530 {_108414 : Type'} (t : _108414 -> Prop) : term85 _108414 t.
Proof. exact (fun x : _108414 => @lem4615525 _108414 x t). Qed.
Lemma lem4615535 {_108414 : Type'} : term88 _108414.
Proof. exact (fun t : _108414 -> Prop => @lem4615530 _108414 t). Qed.
Lemma lem4615536 {_108414 : Type'} : term61 _108414.
Proof. exact (EQ_MP (@lem4615077 _108414) (@lem4615535 _108414)). Qed.
Lemma lem4615537 {_108414 : Type'} (P : Prop) : term183 _108414 P.
Proof. exact (@lem4615536 _108414 P). Qed.
Lemma lem4615538 {_108414 : Type'} (P : Prop) : (term183 _108414 P) = (term57 _108414 P).
Proof. exact (eq_refl (term183 _108414 P)). Qed.
Lemma lem4615539 {_108414 : Type'} (P : Prop) : term57 _108414 P.
Proof. exact (EQ_MP (@lem4615538 _108414 P) (@lem4615537 _108414 P)). Qed.
Lemma lem4615540 {_108414 : Type'} (P : Prop) (t : _108414 -> Prop) : term184 _108414 P t.
Proof. exact (@lem4615539 _108414 P t). Qed.
Lemma lem4615541 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) : (term184 _108414 P t) = (term53 _108414 t P).
Proof. exact (eq_refl (term184 _108414 P t)). Qed.
Lemma lem4615542 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) : term53 _108414 t P.
Proof. exact (EQ_MP (@lem4615541 _108414 t P) (@lem4615540 _108414 P t)). Qed.
Lemma lem4615543 {_108414 : Type'} (t : _108414 -> Prop) (P : Prop) (x : _108414) : term185 _108414 t P x.
Proof. exact (@lem4615542 _108414 t P x). Qed.
Lemma lem4615544 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term185 _108414 t P x) = (term44 _108414 x t P).
Proof. exact (eq_refl (term185 _108414 t P x)). Qed.
Lemma lem4615545 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term44 _108414 x t P.
Proof. exact (EQ_MP (@lem4615544 _108414 x t P) (@lem4615543 _108414 t P x)). Qed.
Lemma lem4615547 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term44 _108414 x t P.
Proof. exact (@lem4614850 _108414 x t P (@lem4615545 _108414 x t P)). Qed.
Lemma lem4615548 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term45 _108414 x t P) : False.
Proof. exact (@lem4615547 _108414 x t P (@lem4614834 _108414 x t P h1)). Qed.
Lemma lem4615549 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term45 _108414 x t P) : (term45 _108414 x t P) = False.
Proof. exact (prop_ext (fun h2 : term45 _108414 x t P => @lem4615548 _108414 x t P h1) (fun h2 : False => @lem4614834 _108414 x t P h1)). Qed.
Lemma lem4615550 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) (h1 : term45 _108414 x t P) : False.
Proof. exact (EQ_MP (@lem4615549 _108414 x t P h1) (@lem4614834 _108414 x t P h1)). Qed.
Lemma lem4615551 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : term44 _108414 x t P.
Proof. exact (fun h0 : term45 _108414 x t P => @lem4615550 _108414 x t P h0). Qed.
Lemma lem4615552 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term26 _108414 P t x) = (term42 _108414 x t P).
Proof. exact (EQ_MP (@lem4614833 _108414 x t P) (@lem4615551 _108414 x t P)). Qed.
Lemma lem4615553 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term25 _108414 P x t) = (term23 _108414 x t P).
Proof. exact (EQ_MP (@lem4614829 _108414 x t P) (@lem4615552 _108414 x t P)). Qed.
Lemma lem4615579 {_83095 : Type'} : term186 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4615580 {_83095 : Type'} (p : _83095 -> Prop) : term187 _83095 p.
Proof. exact (@lem4615579 _83095 p). Qed.
Lemma lem4615581 {_83095 : Type'} (p : _83095 -> Prop) : (term187 _83095 p) = (term188 _83095 p).
Proof. exact (eq_refl (term187 _83095 p)). Qed.
Lemma lem4615582 {_83095 : Type'} (p : _83095 -> Prop) : term188 _83095 p.
Proof. exact (EQ_MP (@lem4615581 _83095 p) (@lem4615580 _83095 p)). Qed.
Lemma lem4615583 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term189 _83095 p x.
Proof. exact (@lem4615582 _83095 p x). Qed.
Lemma lem4615584 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term189 _83095 p x) = ((term190 _83095 x p) = (p x)).
Proof. exact (eq_refl (term189 _83095 p x)). Qed.
Lemma lem4615608 {_89520 _89534 : Type'} : term191 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem4615609 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term192 _89520 _89534 P.
Proof. exact (@lem4615608 _89520 _89534 P). Qed.
Lemma lem4615610 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term192 _89520 _89534 P) = (term193 _89520 _89534 P).
Proof. exact (eq_refl (term192 _89520 _89534 P)). Qed.
Lemma lem4615611 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term193 _89520 _89534 P.
Proof. exact (EQ_MP (@lem4615610 _89520 _89534 P) (@lem4615609 _89520 _89534 P)). Qed.
Lemma lem4615612 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term194 _89520 _89534 P f.
Proof. exact (@lem4615611 _89520 _89534 P f). Qed.
Lemma lem4615613 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term194 _89520 _89534 P f) = ((term195 _89520 _89534 P f) = (term196 _89520 _89534 P f)).
Proof. exact (eq_refl (term194 _89520 _89534 P f)). Qed.
Lemma lem4615615 {A : Type'} (s : A -> Prop) : term197 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4615616 {A : Type'} (s : A -> Prop) : (term197 A s) = (term198 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem4615617 {A : Type'} (s : A -> Prop) : term198 A s.
Proof. exact (EQ_MP (@lem4615616 A s) (@lem4615615 A s)). Qed.
Lemma lem4615618 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term199 A s t.
Proof. exact (@lem4615617 A s t). Qed.
Lemma lem4615619 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term199 A s t) = ((@SUBSET A s t) = (term17 A s t)).
Proof. exact (eq_refl (term199 A s t)). Qed.
Lemma lem4615621 {_100044 : Type'} (s : _100044 -> Prop) : term200 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4615622 {_100044 : Type'} (s : _100044 -> Prop) : (term200 _100044 s) = (term201 _100044 s).
Proof. exact (eq_refl (term200 _100044 s)). Qed.
Lemma lem4615623 {_100044 : Type'} (s : _100044 -> Prop) : term201 _100044 s.
Proof. exact (EQ_MP (@lem4615622 _100044 s) (@lem4615621 _100044 s)). Qed.
Lemma lem4615624 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term202 _100044 s n.
Proof. exact (@lem4615623 _100044 s n). Qed.
Lemma lem4615625 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term202 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term203 _100044 s n)).
Proof. exact (eq_refl (term202 _100044 s n)). Qed.
Lemma lem4615627 {A : Type'} (h1 : term204 A) : term204 A.
Proof. exact (h1). Qed.
Lemma lem4615628 {A : Type'} (s : A -> Prop) (h1 : term204 A) : term205 A s.
Proof. exact (@lem4615627 A h1 s). Qed.
Lemma lem4615629 {A : Type'} (s : A -> Prop) : (term205 A s) = (term206 A s).
Proof. exact (eq_refl (term205 A s)). Qed.
Lemma lem4615630 {A : Type'} (s : A -> Prop) (h1 : term204 A) : term206 A s.
Proof. exact (EQ_MP (@lem4615629 A s) (@lem4615628 A s h1)). Qed.
Lemma lem4615631 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term204 A) : term207 A s t.
Proof. exact (@lem4615630 A s h1 t). Qed.
Lemma lem4615632 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term207 A s t) = (term208 A t s).
Proof. exact (eq_refl (term207 A s t)). Qed.
Lemma lem4615633 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term204 A) : term208 A t s.
Proof. exact (EQ_MP (@lem4615632 A t s) (@lem4615631 A s t h1)). Qed.
Lemma lem4615634 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term209 A s t) : term209 A s t.
Proof. exact (h1). Qed.
Lemma lem4615635 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term204 A) (h2 : term209 A s t) : @FINITE A s.
Proof. exact (@lem4615633 A t s h1 (@lem4615634 A s t h2)). Qed.
Lemma lem4615636 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term209 A s t) : term210 A s.
Proof. exact (fun h0 : term204 A => @lem4615635 A s t h0 h1). Qed.
Lemma lem4615637 {A : Type'} (s : A -> Prop) (h1 : term211 A s) : term211 A s.
Proof. exact (h1). Qed.
Lemma lem4615638 {A : Type'} (s : A -> Prop) (h1 : term211 A s) : term210 A s.
Proof. exact (ex_elim (@lem4615637 A s h1) (fun t : A -> Prop => fun h0 : term212 A s t => @lem4615636 A s t h0)). Qed.
Lemma lem4615639 {A : Type'} (h1 : term204 A) : term204 A.
Proof. exact (h1). Qed.
Lemma lem4615640 {A : Type'} (s : A -> Prop) (h1 : term204 A) (h2 : term211 A s) : @FINITE A s.
Proof. exact (@lem4615638 A s h2 (@lem4615639 A h1)). Qed.
Lemma lem4615641 {A : Type'} (s : A -> Prop) (h1 : term204 A) : term213 A s.
Proof. exact (fun h0 : term211 A s => @lem4615640 A s h1 h0). Qed.
Lemma lem4615642 {A : Type'} (h1 : term204 A) : term214 A.
Proof. exact (fun s : A -> Prop => @lem4615641 A s h1). Qed.
Lemma lem4615643 {A : Type'} : term215 A.
Proof. exact (fun h0 : term204 A => @lem4615642 A h0). Qed.
Lemma lem4615644 {A : Type'} : term214 A.
Proof. exact (@lem4615643 A (@lem3599924 A)). Qed.
Lemma lem4615645 {A : Type'} (s : A -> Prop) : term216 A s.
Proof. exact (@lem4615644 A s). Qed.
Lemma lem4615646 {A : Type'} (s : A -> Prop) : (term216 A s) = (term213 A s).
Proof. exact (eq_refl (term216 A s)). Qed.
Lemma lem4615661 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term217 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4615662 {_108492 : Type'} (s : _108492 -> Prop) (t : _108492 -> Prop) : (s = t) = (term217 _108492 s t).
Proof. exact (@lem4615661 _108492 s t). Qed.
Lemma lem4615663 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : ((term218 _108492 P Q) = (term219 _108492 P Q)) = (term220 _108492 P Q).
Proof. exact (@lem4615662 _108492 (term218 _108492 P Q) (term219 _108492 P Q)). Qed.
Lemma lem4615688 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term220 _108492 P Q) = ((term218 _108492 P Q) = (term219 _108492 P Q)).
Proof. exact (SYM (@lem4615663 _108492 P Q)). Qed.
Lemma lem4615696 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term190 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4615697 {_108492 : Type'} (p : _108492 -> Prop) (x : _108492) : (term190 _108492 x p) = (p x).
Proof. exact (@lem4615696 _108492 p x). Qed.
Lemma lem4615698 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term221 _108492 x P Q) = (term222 _108492 P Q x).
Proof. exact (@lem4615697 _108492 (term223 _108492 P Q) x). Qed.
Lemma lem4615699 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term222 _108492 P Q x) = (term224 _108492 P Q x).
Proof. exact (eq_refl (term222 _108492 P Q x)). Qed.
Lemma lem4615700 {_108492 : Type'} (GEN_PVAR_171 : _108492) : (@SETSPEC _108492 GEN_PVAR_171) = (@SETSPEC _108492 GEN_PVAR_171).
Proof. exact (eq_refl (@SETSPEC _108492 GEN_PVAR_171)). Qed.
Lemma lem4615701 {_108492 : Type'} (GEN_PVAR_171 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term225 _108492 GEN_PVAR_171 P Q x) = (term226 _108492 GEN_PVAR_171 P Q x).
Proof. exact (MK_COMB (@lem4615700 _108492 GEN_PVAR_171) (@lem4615699 _108492 P Q x)). Qed.
Lemma lem4615702 {_108492 : Type'} (x : _108492) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4615703 {_108492 : Type'} (GEN_PVAR_171 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term227 _108492 GEN_PVAR_171 P Q x) = (term228 _108492 GEN_PVAR_171 P Q x).
Proof. exact (MK_COMB (@lem4615701 _108492 GEN_PVAR_171 P Q x) (@lem4615702 _108492 x)). Qed.
Lemma lem4615704 {_108492 : Type'} (GEN_PVAR_171 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term229 _108492 GEN_PVAR_171 P Q) = (term230 _108492 GEN_PVAR_171 P Q).
Proof. exact (fun_ext (fun x : _108492 => @lem4615703 _108492 GEN_PVAR_171 P Q x)). Qed.
Lemma lem4615705 {_108492 : Type'} : (@ex _108492) = (@ex _108492).
Proof. exact (eq_refl (@ex _108492)). Qed.
Lemma lem4615706 {_108492 : Type'} (GEN_PVAR_171 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term231 _108492 GEN_PVAR_171 P Q) = (term232 _108492 GEN_PVAR_171 P Q).
Proof. exact (MK_COMB (@lem4615705 _108492) (@lem4615704 _108492 GEN_PVAR_171 P Q)). Qed.
Lemma lem4615707 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term233 _108492 P Q) = (term234 _108492 P Q).
Proof. exact (fun_ext (fun GEN_PVAR_171 : _108492 => @lem4615706 _108492 GEN_PVAR_171 P Q)). Qed.
Lemma lem4615708 {_108492 : Type'} : (@GSPEC _108492) = (@GSPEC _108492).
Proof. exact (eq_refl (@GSPEC _108492)). Qed.
Lemma lem4615709 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term235 _108492 P Q) = (term218 _108492 P Q).
Proof. exact (MK_COMB (@lem4615708 _108492) (@lem4615707 _108492 P Q)). Qed.
Lemma lem4615710 {_108492 : Type'} (x : _108492) : (@IN _108492 x) = (@IN _108492 x).
Proof. exact (eq_refl (@IN _108492 x)). Qed.
Lemma lem4615711 {_108492 : Type'} (x : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term221 _108492 x P Q) = (term236 _108492 x P Q).
Proof. exact (MK_COMB (@lem4615710 _108492 x) (@lem4615709 _108492 P Q)). Qed.
Lemma lem4615712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615713 {_108492 : Type'} (x : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term237 _108492 x P Q) = (term238 _108492 x P Q).
Proof. exact (MK_COMB (@lem4615712) (@lem4615711 _108492 x P Q)). Qed.
Lemma lem4615714 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term222 _108492 P Q x) = (term224 _108492 P Q x).
Proof. exact (eq_refl (term222 _108492 P Q x)). Qed.
Lemma lem4615715 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : ((term221 _108492 x P Q) = (term222 _108492 P Q x)) = ((term236 _108492 x P Q) = (term224 _108492 P Q x)).
Proof. exact (MK_COMB (@lem4615713 _108492 x P Q) (@lem4615714 _108492 P Q x)). Qed.
Lemma lem4615716 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term236 _108492 x P Q) = (term224 _108492 P Q x).
Proof. exact (EQ_MP (@lem4615715 _108492 P Q x) (@lem4615698 _108492 P Q x)). Qed.
Lemma lem4615719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615720 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term238 _108492 x P Q) = (term239 _108492 P Q x).
Proof. exact (MK_COMB (@lem4615719) (@lem4615716 _108492 P Q x)). Qed.
Lemma lem4615722 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term190 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4615723 {_108492 : Type'} (p : _108492 -> Prop) (x : _108492) : (term190 _108492 x p) = (p x).
Proof. exact (@lem4615722 _108492 p x). Qed.
Lemma lem4615724 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term240 _108492 x P Q) = (term241 _108492 P Q x).
Proof. exact (@lem4615723 _108492 (term242 _108492 P Q) x). Qed.
Lemma lem4615725 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term241 _108492 P Q x) = (term243 _108492 P Q x).
Proof. exact (eq_refl (term241 _108492 P Q x)). Qed.
Lemma lem4615726 {_108492 : Type'} (GEN_PVAR_173 : _108492) : (@SETSPEC _108492 GEN_PVAR_173) = (@SETSPEC _108492 GEN_PVAR_173).
Proof. exact (eq_refl (@SETSPEC _108492 GEN_PVAR_173)). Qed.
Lemma lem4615727 {_108492 : Type'} (GEN_PVAR_173 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term244 _108492 GEN_PVAR_173 P Q x) = (term245 _108492 GEN_PVAR_173 P Q x).
Proof. exact (MK_COMB (@lem4615726 _108492 GEN_PVAR_173) (@lem4615725 _108492 P Q x)). Qed.
Lemma lem4615728 {_108492 : Type'} (x : _108492) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4615729 {_108492 : Type'} (GEN_PVAR_173 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term246 _108492 GEN_PVAR_173 P Q x) = (term247 _108492 GEN_PVAR_173 P Q x).
Proof. exact (MK_COMB (@lem4615727 _108492 GEN_PVAR_173 P Q x) (@lem4615728 _108492 x)). Qed.
Lemma lem4615730 {_108492 : Type'} (GEN_PVAR_173 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term248 _108492 GEN_PVAR_173 P Q) = (term249 _108492 GEN_PVAR_173 P Q).
Proof. exact (fun_ext (fun x : _108492 => @lem4615729 _108492 GEN_PVAR_173 P Q x)). Qed.
Lemma lem4615731 {_108492 : Type'} : (@ex _108492) = (@ex _108492).
Proof. exact (eq_refl (@ex _108492)). Qed.
Lemma lem4615732 {_108492 : Type'} (GEN_PVAR_173 : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term250 _108492 GEN_PVAR_173 P Q) = (term251 _108492 GEN_PVAR_173 P Q).
Proof. exact (MK_COMB (@lem4615731 _108492) (@lem4615730 _108492 GEN_PVAR_173 P Q)). Qed.
Lemma lem4615733 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term252 _108492 P Q) = (term253 _108492 P Q).
Proof. exact (fun_ext (fun GEN_PVAR_173 : _108492 => @lem4615732 _108492 GEN_PVAR_173 P Q)). Qed.
Lemma lem4615734 {_108492 : Type'} : (@GSPEC _108492) = (@GSPEC _108492).
Proof. exact (eq_refl (@GSPEC _108492)). Qed.
Lemma lem4615735 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term254 _108492 P Q) = (term219 _108492 P Q).
Proof. exact (MK_COMB (@lem4615734 _108492) (@lem4615733 _108492 P Q)). Qed.
Lemma lem4615736 {_108492 : Type'} (x : _108492) : (@IN _108492 x) = (@IN _108492 x).
Proof. exact (eq_refl (@IN _108492 x)). Qed.
Lemma lem4615737 {_108492 : Type'} (x : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term240 _108492 x P Q) = (term255 _108492 x P Q).
Proof. exact (MK_COMB (@lem4615736 _108492 x) (@lem4615735 _108492 P Q)). Qed.
Lemma lem4615738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615739 {_108492 : Type'} (x : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term256 _108492 x P Q) = (term257 _108492 x P Q).
Proof. exact (MK_COMB (@lem4615738) (@lem4615737 _108492 x P Q)). Qed.
Lemma lem4615740 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term241 _108492 P Q x) = (term243 _108492 P Q x).
Proof. exact (eq_refl (term241 _108492 P Q x)). Qed.
Lemma lem4615741 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : ((term240 _108492 x P Q) = (term241 _108492 P Q x)) = ((term255 _108492 x P Q) = (term243 _108492 P Q x)).
Proof. exact (MK_COMB (@lem4615739 _108492 x P Q) (@lem4615740 _108492 P Q x)). Qed.
Lemma lem4615742 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term255 _108492 x P Q) = (term243 _108492 P Q x).
Proof. exact (EQ_MP (@lem4615741 _108492 P Q x) (@lem4615724 _108492 P Q x)). Qed.
Lemma lem4615746 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term190 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4615747 {_108492 : Type'} (p : _108492 -> Prop) (x : _108492) : (term190 _108492 x p) = (p x).
Proof. exact (@lem4615746 _108492 p x). Qed.
Lemma lem4615748 {_108492 : Type'} (P : _108492 -> Prop) (x : _108492) : (term190 _108492 x P) = (P x).
Proof. exact (@lem4615747 _108492 P x). Qed.
Lemma lem4615749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4615750 {_108492 : Type'} (P : _108492 -> Prop) (x : _108492) : (term258 _108492 x P) = (term122 _108492 P x).
Proof. exact (MK_COMB (@lem4615749) (@lem4615748 _108492 P x)). Qed.
Lemma lem4615751 {_108492 : Type'} (Q : _108492 -> Prop) (x : _108492) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem4615752 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term243 _108492 P Q x) = (term224 _108492 P Q x).
Proof. exact (MK_COMB (@lem4615750 _108492 P x) (@lem4615751 _108492 Q x)). Qed.
Lemma lem4615755 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : (term255 _108492 x P Q) = (term224 _108492 P Q x).
Proof. exact (TRANS (@lem4615742 _108492 P Q x) (@lem4615752 _108492 P Q x)). Qed.
Lemma lem4615756 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : ((term236 _108492 x P Q) = (term255 _108492 x P Q)) = ((term224 _108492 P Q x) = (term224 _108492 P Q x)).
Proof. exact (MK_COMB (@lem4615720 _108492 P Q x) (@lem4615755 _108492 P Q x)). Qed.
Lemma lem4615758 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4615759 (x : Prop) : (x = x) = True.
Proof. exact (@lem4615758 Prop x). Qed.
Lemma lem4615760 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) (x : _108492) : ((term224 _108492 P Q x) = (term224 _108492 P Q x)) = True.
Proof. exact (@lem4615759 (term224 _108492 P Q x)). Qed.
Lemma lem4615761 {_108492 : Type'} (x : _108492) (P : _108492 -> Prop) (Q : _108492 -> Prop) : ((term236 _108492 x P Q) = (term255 _108492 x P Q)) = True.
Proof. exact (TRANS (@lem4615756 _108492 P Q x) (@lem4615760 _108492 P Q x)). Qed.
Lemma lem4615762 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term259 _108492 P Q) = (term94 _108492).
Proof. exact (fun_ext (fun x : _108492 => @lem4615761 _108492 x P Q)). Qed.
Lemma lem4615763 {_108492 : Type'} : (@all _108492) = (@all _108492).
Proof. exact (eq_refl (@all _108492)). Qed.
Lemma lem4615764 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term220 _108492 P Q) = (term96 _108492).
Proof. exact (MK_COMB (@lem4615763 _108492) (@lem4615762 _108492 P Q)). Qed.
Lemma lem4615766 {A : Type'} (t : Prop) : (term97 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4615767 {_108492 : Type'} (t : Prop) : (term97 _108492 t) = t.
Proof. exact (@lem4615766 _108492 t). Qed.
Lemma lem4615768 {_108492 : Type'} : (term96 _108492) = True.
Proof. exact (@lem4615767 _108492 True). Qed.
Lemma lem4615769 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term220 _108492 P Q) = True.
Proof. exact (TRANS (@lem4615764 _108492 P Q) (@lem4615768 _108492)). Qed.
Lemma lem4615770 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : True = (term220 _108492 P Q).
Proof. exact (SYM (@lem4615769 _108492 P Q)). Qed.
Lemma lem4615771 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : term220 _108492 P Q.
Proof. exact (EQ_MP (@lem4615770 _108492 P Q) (@lem0)). Qed.
Lemma lem4615773 {A : Type'} (s : A -> Prop) : term260 A s.
Proof. exact (@lem9784 (@FINITE A s)). Qed.
Lemma lem4615774 {A : Type'} (s : A -> Prop) : (term260 A s) = (term261 A s).
Proof. exact (eq_refl (term260 A s)). Qed.
Lemma lem4615775 {A : Type'} (s : A -> Prop) : term261 A s.
Proof. exact (EQ_MP (@lem4615774 A s) (@lem4615773 A s)). Qed.
Lemma lem4615776 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4615777 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : term262 A s.
Proof. exact (h1). Qed.
Lemma lem4615778 {_92373 : Type'} (a : _92373) : term263 _92373 a.
Proof. exact (@lem3608356 _92373 a). Qed.
Lemma lem4615779 {_92373 : Type'} (a : _92373) : (term263 _92373 a) = (term264 _92373 a).
Proof. exact (eq_refl (term263 _92373 a)). Qed.
Lemma lem4615780 {_92373 : Type'} (a : _92373) : term264 _92373 a.
Proof. exact (EQ_MP (@lem4615779 _92373 a) (@lem4615778 _92373 a)). Qed.
Lemma lem4615781 {_92373 : Type'} (a : _92373) : (term264 _92373 a) = ((term264 _92373 a) = True).
Proof. exact (@lem7 (term264 _92373 a)). Qed.
Lemma lem4615787 {_88341 : Type'} : term265 _88341.
Proof. exact (proj1 (@lem3400385 _88341 Prop)). Qed.
Lemma lem4615788 {_88341 : Type'} (a : _88341) : term266 _88341 a.
Proof. exact (@lem4615787 _88341 a). Qed.
Lemma lem4615789 {_88341 : Type'} (a : _88341) : (term266 _88341 a) = ((term267 _88341 a) = (@INSERT _88341 a (@EMPTY _88341))).
Proof. exact (eq_refl (term266 _88341 a)). Qed.
Lemma lem4615808 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4615809 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (@SUBSET _108511 s t) = (term17 _108511 s t).
Proof. exact (@lem4615808 _108511 s t). Qed.
Lemma lem4615810 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (@SUBSET _108511 t s) = (term17 _108511 t s).
Proof. exact (@lem4615809 _108511 t s). Qed.
Lemma lem4615817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4615818 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term268 _108511 t s) = (term269 _108511 t s).
Proof. exact (MK_COMB (@lem4615817) (@lem4615810 _108511 t s)). Qed.
Lemma lem4615822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term217 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4615823 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (s = t) = (term217 _108511 s t).
Proof. exact (@lem4615822 _108511 s t). Qed.
Lemma lem4615824 {_108511 : Type'} (t : _108511 -> Prop) : (t = (@EMPTY _108511)) = (term270 _108511 t).
Proof. exact (@lem4615823 _108511 t (@EMPTY _108511)). Qed.
Lemma lem4615833 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term271 _108511 s t) = (term272 _108511 s t).
Proof. exact (MK_COMB (@lem4615818 _108511 t s) (@lem4615824 _108511 t)). Qed.
Lemma lem4615836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615837 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term273 _108511 s t) = (term274 _108511 s t).
Proof. exact (MK_COMB (@lem4615836) (@lem4615833 _108511 s t)). Qed.
Lemma lem4615841 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term217 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4615842 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (s = t) = (term217 _108511 s t).
Proof. exact (@lem4615841 _108511 s t). Qed.
Lemma lem4615843 {_108511 : Type'} (t : _108511 -> Prop) : (t = (@EMPTY _108511)) = (term270 _108511 t).
Proof. exact (@lem4615842 _108511 t (@EMPTY _108511)). Qed.
Lemma lem4615852 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term271 _108511 s t) = (t = (@EMPTY _108511))) = ((term272 _108511 s t) = (term270 _108511 t)).
Proof. exact (MK_COMB (@lem4615837 _108511 s t) (@lem4615843 _108511 t)). Qed.
Lemma lem4615857 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term272 _108511 s t) = (term270 _108511 t)) = ((term271 _108511 s t) = (t = (@EMPTY _108511))).
Proof. exact (SYM (@lem4615852 _108511 s t)). Qed.
Lemma lem4615869 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4615870 {_108511 : Type'} (P : _108511 -> Prop) (x : _108511) : (@IN _108511 x P) = (P x).
Proof. exact (@lem4615869 _108511 P x). Qed.
Lemma lem4615871 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (@IN _108511 x t) = (t x).
Proof. exact (@lem4615870 _108511 t x). Qed.
Lemma lem4615872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4615873 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term275 _108511 x t) = (term276 _108511 t x).
Proof. exact (MK_COMB (@lem4615872) (@lem4615871 _108511 t x)). Qed.
Lemma lem4615875 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4615876 {_108511 : Type'} (P : _108511 -> Prop) (x : _108511) : (@IN _108511 x P) = (P x).
Proof. exact (@lem4615875 _108511 P x). Qed.
Lemma lem4615877 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) : (@IN _108511 x s) = (s x).
Proof. exact (@lem4615876 _108511 s x). Qed.
Lemma lem4615878 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term277 _108511 t x s) = (term278 _108511 t s x).
Proof. exact (MK_COMB (@lem4615873 _108511 t x) (@lem4615877 _108511 s x)). Qed.
Lemma lem4615881 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term279 _108511 t s) = (term280 _108511 t s).
Proof. exact (fun_ext (fun x : _108511 => @lem4615878 _108511 t s x)). Qed.
Lemma lem4615882 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4615883 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term17 _108511 t s) = (term281 _108511 t s).
Proof. exact (MK_COMB (@lem4615882 _108511) (@lem4615881 _108511 t s)). Qed.
Lemma lem4615888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4615889 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term269 _108511 t s) = (term282 _108511 t s).
Proof. exact (MK_COMB (@lem4615888) (@lem4615883 _108511 t s)). Qed.
Lemma lem4615897 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4615898 {_108511 : Type'} (P : _108511 -> Prop) (x : _108511) : (@IN _108511 x P) = (P x).
Proof. exact (@lem4615897 _108511 P x). Qed.
Lemma lem4615899 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (@IN _108511 x t) = (t x).
Proof. exact (@lem4615898 _108511 t x). Qed.
Lemma lem4615900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615901 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term283 _108511 x t) = (term80 _108511 t x).
Proof. exact (MK_COMB (@lem4615900) (@lem4615899 _108511 t x)). Qed.
Lemma lem4615903 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4615904 {_108511 : Type'} (x : _108511) : (@IN _108511 x (@EMPTY _108511)) = False.
Proof. exact (@lem4615903 _108511 x). Qed.
Lemma lem4615905 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : ((@IN _108511 x t) = (@IN _108511 x (@EMPTY _108511))) = ((t x) = False).
Proof. exact (MK_COMB (@lem4615901 _108511 t x) (@lem4615904 _108511 x)). Qed.
Lemma lem4615907 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4615908 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : ((t x) = False) = (term163 _108511 t x).
Proof. exact (@lem4615907 (t x)). Qed.
Lemma lem4615909 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : ((@IN _108511 x t) = (@IN _108511 x (@EMPTY _108511))) = (term163 _108511 t x).
Proof. exact (TRANS (@lem4615905 _108511 t x) (@lem4615908 _108511 t x)). Qed.
Lemma lem4615910 {_108511 : Type'} (t : _108511 -> Prop) : (term284 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4615909 _108511 t x)). Qed.
Lemma lem4615911 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4615912 {_108511 : Type'} (t : _108511 -> Prop) : (term270 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4615911 _108511) (@lem4615910 _108511 t)). Qed.
Lemma lem4615917 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term272 _108511 s t) = (term286 _108511 s t).
Proof. exact (MK_COMB (@lem4615889 _108511 t s) (@lem4615912 _108511 t)). Qed.
Lemma lem4615920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615921 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term274 _108511 s t) = (term287 _108511 s t).
Proof. exact (MK_COMB (@lem4615920) (@lem4615917 _108511 s t)). Qed.
Lemma lem4615929 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4615930 {_108511 : Type'} (P : _108511 -> Prop) (x : _108511) : (@IN _108511 x P) = (P x).
Proof. exact (@lem4615929 _108511 P x). Qed.
Lemma lem4615931 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (@IN _108511 x t) = (t x).
Proof. exact (@lem4615930 _108511 t x). Qed.
Lemma lem4615932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4615933 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term283 _108511 x t) = (term80 _108511 t x).
Proof. exact (MK_COMB (@lem4615932) (@lem4615931 _108511 t x)). Qed.
Lemma lem4615935 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4615936 {_108511 : Type'} (x : _108511) : (@IN _108511 x (@EMPTY _108511)) = False.
Proof. exact (@lem4615935 _108511 x). Qed.
Lemma lem4615937 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : ((@IN _108511 x t) = (@IN _108511 x (@EMPTY _108511))) = ((t x) = False).
Proof. exact (MK_COMB (@lem4615933 _108511 t x) (@lem4615936 _108511 x)). Qed.
Lemma lem4615939 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4615940 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : ((t x) = False) = (term163 _108511 t x).
Proof. exact (@lem4615939 (t x)). Qed.
Lemma lem4615941 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : ((@IN _108511 x t) = (@IN _108511 x (@EMPTY _108511))) = (term163 _108511 t x).
Proof. exact (TRANS (@lem4615937 _108511 t x) (@lem4615940 _108511 t x)). Qed.
Lemma lem4615942 {_108511 : Type'} (t : _108511 -> Prop) : (term284 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4615941 _108511 t x)). Qed.
Lemma lem4615943 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4615944 {_108511 : Type'} (t : _108511 -> Prop) : (term270 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4615943 _108511) (@lem4615942 _108511 t)). Qed.
Lemma lem4615949 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term272 _108511 s t) = (term270 _108511 t)) = ((term286 _108511 s t) = (term285 _108511 t)).
Proof. exact (MK_COMB (@lem4615921 _108511 s t) (@lem4615944 _108511 t)). Qed.
Lemma lem4615952 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term286 _108511 s t) = (term285 _108511 t)) = ((term272 _108511 s t) = (term270 _108511 t)).
Proof. exact (SYM (@lem4615949 _108511 s t)). Qed.
Lemma lem4615954 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4615955 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term286 _108511 s t) = (term285 _108511 t)) = (term288 _108511 s t).
Proof. exact (@lem4615954 ((term286 _108511 s t) = (term285 _108511 t))). Qed.
Lemma lem4615956 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term288 _108511 s t) = ((term286 _108511 s t) = (term285 _108511 t)).
Proof. exact (SYM (@lem4615955 _108511 s t)). Qed.
Lemma lem4615957 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : term289 _108511 s t.
Proof. exact (h1). Qed.
Lemma lem4615960 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term288 _108511 s t) : term288 _108511 s t.
Proof. exact (h1). Qed.
Lemma lem4615961 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term290 _108511 s t.
Proof. exact (fun h0 : term288 _108511 s t => @lem4615960 _108511 s t h0). Qed.
Lemma lem4615962 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term290 _108511 s t) : term290 _108511 s t.
Proof. exact (h1). Qed.
Lemma lem4615963 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term288 _108511 s t) : term288 _108511 s t.
Proof. exact (h1). Qed.
Lemma lem4615964 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term288 _108511 s t) (h2 : term290 _108511 s t) : term288 _108511 s t.
Proof. exact (@lem4615962 _108511 s t h2 (@lem4615963 _108511 s t h1)). Qed.
Lemma lem4615965 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term288 _108511 s t) : term291 _108511 s t.
Proof. exact (fun h0 : term290 _108511 s t => @lem4615964 _108511 s t h1 h0). Qed.
Lemma lem4615966 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term290 _108511 s t) : term290 _108511 s t.
Proof. exact (h1). Qed.
Lemma lem4615967 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term288 _108511 s t) (h2 : term290 _108511 s t) : term288 _108511 s t.
Proof. exact (@lem4615965 _108511 s t h1 (@lem4615966 _108511 s t h2)). Qed.
Lemma lem4615968 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term290 _108511 s t) : term290 _108511 s t.
Proof. exact (fun h0 : term288 _108511 s t => @lem4615967 _108511 s t h0 h1). Qed.
Lemma lem4615969 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term292 _108511 s t.
Proof. exact (fun h0 : term290 _108511 s t => @lem4615968 _108511 s t h0). Qed.
Lemma lem4615972 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term290 _108511 s t.
Proof. exact (@lem4615969 _108511 s t (@lem4615961 _108511 s t)). Qed.
Lemma lem4615973 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term290 _108511 s t.
Proof. exact (@lem4615972 _108511 s t). Qed.
Lemma lem4615983 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4615984 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term288 _108511 s t) = (term293 _108511 s t).
Proof. exact (@lem4615983 (term289 _108511 s t)). Qed.
Lemma lem4615986 (t : Prop) : (term50 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4615987 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term293 _108511 s t) = ((term286 _108511 s t) = (term285 _108511 t)).
Proof. exact (@lem4615986 ((term286 _108511 s t) = (term285 _108511 t))). Qed.
Lemma lem4615988 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term288 _108511 s t) = ((term286 _108511 s t) = (term285 _108511 t)).
Proof. exact (TRANS (@lem4615984 _108511 s t) (@lem4615987 _108511 s t)). Qed.
Lemma lem4616005 {_108511 : Type'} (t : _108511 -> Prop) : (term294 _108511 t) = (term295 _108511 t).
Proof. exact (fun_ext (fun s : _108511 -> Prop => @lem4615988 _108511 s t)). Qed.
Lemma lem4616006 {_108511 : Type'} : (@all (_108511 -> Prop)) = (@all (_108511 -> Prop)).
Proof. exact (eq_refl (@all (_108511 -> Prop))). Qed.
Lemma lem4616007 {_108511 : Type'} (t : _108511 -> Prop) : (term296 _108511 t) = (term297 _108511 t).
Proof. exact (MK_COMB (@lem4616006 _108511) (@lem4616005 _108511 t)). Qed.
Lemma lem4616012 {_108511 : Type'} : (term298 _108511) = (term299 _108511).
Proof. exact (fun_ext (fun t : _108511 -> Prop => @lem4616007 _108511 t)). Qed.
Lemma lem4616013 {_108511 : Type'} : (@all (_108511 -> Prop)) = (@all (_108511 -> Prop)).
Proof. exact (eq_refl (@all (_108511 -> Prop))). Qed.
Lemma lem4616022 {_108511 : Type'} : (term300 _108511) = (term301 _108511).
Proof. exact (MK_COMB (@lem4616013 _108511) (@lem4616012 _108511)). Qed.
Lemma lem4616025 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616026 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616025 _108511 t x)). Qed.
Lemma lem4616027 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616028 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616027 _108511) (@lem4616026 _108511 t)). Qed.
Lemma lem4616031 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616032 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616031 _108511 t x)). Qed.
Lemma lem4616033 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616034 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616033 _108511) (@lem4616032 _108511 t)). Qed.
Lemma lem4616039 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term278 _108511 t s x) = (term278 _108511 t s x).
Proof. exact (eq_refl (term278 _108511 t s x)). Qed.
Lemma lem4616040 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term280 _108511 t s) = (term280 _108511 t s).
Proof. exact (fun_ext (fun x : _108511 => @lem4616039 _108511 t s x)). Qed.
Lemma lem4616041 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616042 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term281 _108511 t s) = (term281 _108511 t s).
Proof. exact (MK_COMB (@lem4616041 _108511) (@lem4616040 _108511 t s)). Qed.
Lemma lem4616043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616044 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term282 _108511 t s) = (term282 _108511 t s).
Proof. exact (MK_COMB (@lem4616043) (@lem4616042 _108511 t s)). Qed.
Lemma lem4616045 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term286 _108511 s t) = (term286 _108511 s t).
Proof. exact (MK_COMB (@lem4616044 _108511 t s) (@lem4616034 _108511 t)). Qed.
Lemma lem4616046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4616047 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term287 _108511 s t) = (term287 _108511 s t).
Proof. exact (MK_COMB (@lem4616046) (@lem4616045 _108511 s t)). Qed.
Lemma lem4616048 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term286 _108511 s t) = (term285 _108511 t)) = ((term286 _108511 s t) = (term285 _108511 t)).
Proof. exact (MK_COMB (@lem4616047 _108511 s t) (@lem4616028 _108511 t)). Qed.
Lemma lem4616049 {_108511 : Type'} (t : _108511 -> Prop) : (term295 _108511 t) = (term295 _108511 t).
Proof. exact (fun_ext (fun s : _108511 -> Prop => @lem4616048 _108511 s t)). Qed.
Lemma lem4616050 {_108511 : Type'} : (@all (_108511 -> Prop)) = (@all (_108511 -> Prop)).
Proof. exact (eq_refl (@all (_108511 -> Prop))). Qed.
Lemma lem4616051 {_108511 : Type'} (t : _108511 -> Prop) : (term297 _108511 t) = (term297 _108511 t).
Proof. exact (MK_COMB (@lem4616050 _108511) (@lem4616049 _108511 t)). Qed.
Lemma lem4616052 {_108511 : Type'} : (term299 _108511) = (term299 _108511).
Proof. exact (fun_ext (fun t : _108511 -> Prop => @lem4616051 _108511 t)). Qed.
Lemma lem4616053 {_108511 : Type'} : (@all (_108511 -> Prop)) = (@all (_108511 -> Prop)).
Proof. exact (eq_refl (@all (_108511 -> Prop))). Qed.
Lemma lem4616054 {_108511 : Type'} : (term301 _108511) = (term301 _108511).
Proof. exact (MK_COMB (@lem4616053 _108511) (@lem4616052 _108511)). Qed.
Lemma lem4616091 {_108511 : Type'} : (term300 _108511) = (term301 _108511).
Proof. exact (TRANS (@lem4616022 _108511) (@lem4616054 _108511)). Qed.
Lemma lem4616092 {_108511 : Type'} : (term301 _108511) = (term300 _108511).
Proof. exact (SYM (@lem4616091 _108511)). Qed.
Lemma lem4616094 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4616095 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term286 _108511 s t) = (term285 _108511 t)) = (term288 _108511 s t).
Proof. exact (@lem4616094 ((term286 _108511 s t) = (term285 _108511 t))). Qed.
Lemma lem4616096 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term288 _108511 s t) = ((term286 _108511 s t) = (term285 _108511 t)).
Proof. exact (SYM (@lem4616095 _108511 s t)). Qed.
Lemma lem4616097 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : term289 _108511 s t.
Proof. exact (h1). Qed.
Lemma lem4616106 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term302 _108511 t s x) = (term303 _108511 t s x).
Proof. exact (@lem17362 (t x) (s x)). Qed.
Lemma lem4616111 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term278 _108511 t s x) = (term304 _108511 t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4616112 {_108511 : Type'} (P : _108511 -> Prop) : (term108 _108511 P) = (term109 _108511 P).
Proof. exact (@lem18392 _108511 P). Qed.
Lemma lem4616113 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term305 _108511 t s) = (term306 _108511 t s).
Proof. exact (@lem4616112 _108511 (term280 _108511 t s)). Qed.
Lemma lem4616114 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term307 _108511 t s x) = (term278 _108511 t s x).
Proof. exact (eq_refl (term307 _108511 t s x)). Qed.
Lemma lem4616115 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4616116 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term308 _108511 t s x) = (term302 _108511 t s x).
Proof. exact (MK_COMB (@lem4616115) (@lem4616114 _108511 t s x)). Qed.
Lemma lem4616117 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term308 _108511 t s x) = (term303 _108511 t s x).
Proof. exact (TRANS (@lem4616116 _108511 t s x) (@lem4616106 _108511 t s x)). Qed.
Lemma lem4616118 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term309 _108511 t s) = (term310 _108511 t s).
Proof. exact (fun_ext (fun x : _108511 => @lem4616117 _108511 t s x)). Qed.
Lemma lem4616119 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616120 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term306 _108511 t s) = (term311 _108511 t s).
Proof. exact (MK_COMB (@lem4616119 _108511) (@lem4616118 _108511 t s)). Qed.
Lemma lem4616121 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term305 _108511 t s) = (term311 _108511 t s).
Proof. exact (TRANS (@lem4616113 _108511 t s) (@lem4616120 _108511 t s)). Qed.
Lemma lem4616122 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term280 _108511 t s) = (term312 _108511 t s).
Proof. exact (fun_ext (fun x : _108511 => @lem4616111 _108511 t s x)). Qed.
Lemma lem4616123 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616124 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term281 _108511 t s) = (term313 _108511 t s).
Proof. exact (MK_COMB (@lem4616123 _108511) (@lem4616122 _108511 t s)). Qed.
Lemma lem4616125 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616128 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term314 _108511 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4616129 {_108511 : Type'} (P : _108511 -> Prop) : (term108 _108511 P) = (term109 _108511 P).
Proof. exact (@lem18392 _108511 P). Qed.
Lemma lem4616130 {_108511 : Type'} (t : _108511 -> Prop) : (term315 _108511 t) = (term316 _108511 t).
Proof. exact (@lem4616129 _108511 (term164 _108511 t)). Qed.
Lemma lem4616131 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term165 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term165 _108511 t x)). Qed.
Lemma lem4616132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4616133 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term317 _108511 t x) = (term314 _108511 t x).
Proof. exact (MK_COMB (@lem4616132) (@lem4616131 _108511 t x)). Qed.
Lemma lem4616134 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term317 _108511 t x) = (t x).
Proof. exact (TRANS (@lem4616133 _108511 t x) (@lem4616128 _108511 t x)). Qed.
Lemma lem4616135 {_108511 : Type'} (t : _108511 -> Prop) : (term318 _108511 t) = (term319 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616134 _108511 t x)). Qed.
Lemma lem4616136 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616137 {_108511 : Type'} (t : _108511 -> Prop) : (term316 _108511 t) = (term320 _108511 t).
Proof. exact (MK_COMB (@lem4616136 _108511) (@lem4616135 _108511 t)). Qed.
Lemma lem4616138 {_108511 : Type'} (t : _108511 -> Prop) : (term315 _108511 t) = (term320 _108511 t).
Proof. exact (TRANS (@lem4616130 _108511 t) (@lem4616137 _108511 t)). Qed.
Lemma lem4616139 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616125 _108511 t x)). Qed.
Lemma lem4616140 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616141 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616140 _108511) (@lem4616139 _108511 t)). Qed.
Lemma lem4616142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616143 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term321 _108511 t s) = (term322 _108511 t s).
Proof. exact (MK_COMB (@lem4616142) (@lem4616121 _108511 t s)). Qed.
Lemma lem4616144 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term323 _108511 s t) = (term324 _108511 s t).
Proof. exact (MK_COMB (@lem4616143 _108511 t s) (@lem4616138 _108511 t)). Qed.
Lemma lem4616145 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term325 _108511 s t) = (term323 _108511 s t).
Proof. exact (@lem17045 (term281 _108511 t s) (term285 _108511 t)). Qed.
Lemma lem4616146 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term325 _108511 s t) = (term324 _108511 s t).
Proof. exact (TRANS (@lem4616145 _108511 s t) (@lem4616144 _108511 s t)). Qed.
Lemma lem4616147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616148 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term282 _108511 t s) = (term326 _108511 t s).
Proof. exact (MK_COMB (@lem4616147) (@lem4616124 _108511 t s)). Qed.
Lemma lem4616149 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term286 _108511 s t) = (term327 _108511 s t).
Proof. exact (MK_COMB (@lem4616148 _108511 t s) (@lem4616141 _108511 t)). Qed.
Lemma lem4616150 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616153 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term314 _108511 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4616154 {_108511 : Type'} (P : _108511 -> Prop) : (term108 _108511 P) = (term109 _108511 P).
Proof. exact (@lem18392 _108511 P). Qed.
Lemma lem4616155 {_108511 : Type'} (t : _108511 -> Prop) : (term315 _108511 t) = (term316 _108511 t).
Proof. exact (@lem4616154 _108511 (term164 _108511 t)). Qed.
Lemma lem4616156 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term165 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term165 _108511 t x)). Qed.
Lemma lem4616157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4616158 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term317 _108511 t x) = (term314 _108511 t x).
Proof. exact (MK_COMB (@lem4616157) (@lem4616156 _108511 t x)). Qed.
Lemma lem4616159 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term317 _108511 t x) = (t x).
Proof. exact (TRANS (@lem4616158 _108511 t x) (@lem4616153 _108511 t x)). Qed.
Lemma lem4616160 {_108511 : Type'} (t : _108511 -> Prop) : (term318 _108511 t) = (term319 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616159 _108511 t x)). Qed.
Lemma lem4616161 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616162 {_108511 : Type'} (t : _108511 -> Prop) : (term316 _108511 t) = (term320 _108511 t).
Proof. exact (MK_COMB (@lem4616161 _108511) (@lem4616160 _108511 t)). Qed.
Lemma lem4616163 {_108511 : Type'} (t : _108511 -> Prop) : (term315 _108511 t) = (term320 _108511 t).
Proof. exact (TRANS (@lem4616155 _108511 t) (@lem4616162 _108511 t)). Qed.
Lemma lem4616164 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616150 _108511 t x)). Qed.
Lemma lem4616165 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616166 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616165 _108511) (@lem4616164 _108511 t)). Qed.
Lemma lem4616167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616168 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term328 _108511 s t) = (term329 _108511 s t).
Proof. exact (MK_COMB (@lem4616167) (@lem4616146 _108511 s t)). Qed.
Lemma lem4616169 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term330 _108511 s t) = (term331 _108511 s t).
Proof. exact (MK_COMB (@lem4616168 _108511 s t) (@lem4616166 _108511 t)). Qed.
Lemma lem4616170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616171 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term332 _108511 s t) = (term333 _108511 s t).
Proof. exact (MK_COMB (@lem4616170) (@lem4616149 _108511 s t)). Qed.
Lemma lem4616172 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term334 _108511 s t) = (term335 _108511 s t).
Proof. exact (MK_COMB (@lem4616171 _108511 s t) (@lem4616163 _108511 t)). Qed.
Lemma lem4616173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616174 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term336 _108511 s t) = (term337 _108511 s t).
Proof. exact (MK_COMB (@lem4616173) (@lem4616172 _108511 s t)). Qed.
Lemma lem4616175 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term338 _108511 s t) = (term339 _108511 s t).
Proof. exact (MK_COMB (@lem4616174 _108511 s t) (@lem4616169 _108511 s t)). Qed.
Lemma lem4616176 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term289 _108511 s t) = (term338 _108511 s t).
Proof. exact (@lem17646 (term286 _108511 s t) (term285 _108511 t)). Qed.
Lemma lem4616177 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term289 _108511 s t) = (term339 _108511 s t).
Proof. exact (TRANS (@lem4616176 _108511 s t) (@lem4616175 _108511 s t)). Qed.
Lemma lem4616256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4616257 {_108511 : Type'} (P : Prop) (Q : _108511 -> Prop) : (term129 _108511 P Q) = (term130 _108511 P Q).
Proof. exact (@lem4616256 _108511 P Q). Qed.
Lemma lem4616258 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term335 _108511 s t) = (term340 _108511 s t).
Proof. exact (@lem4616257 _108511 (term327 _108511 s t) t). Qed.
Lemma lem4616259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616260 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term337 _108511 s t) = (term341 _108511 s t).
Proof. exact (MK_COMB (@lem4616259) (@lem4616258 _108511 s t)). Qed.
Lemma lem4616262 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4616263 {_108511 : Type'} (P : _108511 -> Prop) (Q : _108511 -> Prop) : (term342 _108511 P Q) = (term343 _108511 P Q).
Proof. exact (@lem4616262 _108511 P Q). Qed.
Lemma lem4616264 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term344 _108511 s t) = (term345 _108511 s t).
Proof. exact (@lem4616263 _108511 (term310 _108511 t s) t). Qed.
Lemma lem4616265 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term346 _108511 t s x) = (term303 _108511 t s x).
Proof. exact (eq_refl (term346 _108511 t s x)). Qed.
Lemma lem4616266 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term347 _108511 t s) = (term310 _108511 t s).
Proof. exact (fun_ext (fun x : _108511 => @lem4616265 _108511 t s x)). Qed.
Lemma lem4616267 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616268 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term348 _108511 t s) = (term311 _108511 t s).
Proof. exact (MK_COMB (@lem4616267 _108511) (@lem4616266 _108511 t s)). Qed.
Lemma lem4616269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616270 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term349 _108511 t s) = (term322 _108511 t s).
Proof. exact (MK_COMB (@lem4616269) (@lem4616268 _108511 t s)). Qed.
Lemma lem4616271 {_108511 : Type'} (t : _108511 -> Prop) : (term320 _108511 t) = (term320 _108511 t).
Proof. exact (eq_refl (term320 _108511 t)). Qed.
Lemma lem4616272 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term344 _108511 s t) = (term324 _108511 s t).
Proof. exact (MK_COMB (@lem4616270 _108511 t s) (@lem4616271 _108511 t)). Qed.
Lemma lem4616273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4616274 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term350 _108511 s t) = (term351 _108511 s t).
Proof. exact (MK_COMB (@lem4616273) (@lem4616272 _108511 s t)). Qed.
Lemma lem4616275 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term346 _108511 t s x) = (term303 _108511 t s x).
Proof. exact (eq_refl (term346 _108511 t s x)). Qed.
Lemma lem4616276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616277 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term352 _108511 t s x) = (term353 _108511 t s x).
Proof. exact (MK_COMB (@lem4616276) (@lem4616275 _108511 t s x)). Qed.
Lemma lem4616278 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4616279 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term354 _108511 s t x) = (term355 _108511 s t x).
Proof. exact (MK_COMB (@lem4616277 _108511 t s x) (@lem4616278 _108511 t x)). Qed.
Lemma lem4616280 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term356 _108511 s t) = (term357 _108511 s t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616279 _108511 s t x)). Qed.
Lemma lem4616281 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616282 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term345 _108511 s t) = (term358 _108511 s t).
Proof. exact (MK_COMB (@lem4616281 _108511) (@lem4616280 _108511 s t)). Qed.
Lemma lem4616283 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term344 _108511 s t) = (term345 _108511 s t)) = ((term324 _108511 s t) = (term358 _108511 s t)).
Proof. exact (MK_COMB (@lem4616274 _108511 s t) (@lem4616282 _108511 s t)). Qed.
Lemma lem4616284 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term324 _108511 s t) = (term358 _108511 s t).
Proof. exact (EQ_MP (@lem4616283 _108511 s t) (@lem4616264 _108511 s t)). Qed.
Lemma lem4616285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616286 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term329 _108511 s t) = (term359 _108511 s t).
Proof. exact (MK_COMB (@lem4616285) (@lem4616284 _108511 s t)). Qed.
Lemma lem4616287 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (eq_refl (term285 _108511 t)). Qed.
Lemma lem4616288 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term331 _108511 s t) = (term360 _108511 s t).
Proof. exact (MK_COMB (@lem4616286 _108511 s t) (@lem4616287 _108511 t)). Qed.
Lemma lem4616290 {A : Type'} (P : A -> Prop) (Q : Prop) : (term361 A P Q) = (term362 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4616291 {_108511 : Type'} (P : _108511 -> Prop) (Q : Prop) : (term361 _108511 P Q) = (term362 _108511 P Q).
Proof. exact (@lem4616290 _108511 P Q). Qed.
Lemma lem4616292 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term363 _108511 s t) = (term364 _108511 s t).
Proof. exact (@lem4616291 _108511 (term357 _108511 s t) (term285 _108511 t)). Qed.
Lemma lem4616293 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term365 _108511 s t x) = (term355 _108511 s t x).
Proof. exact (eq_refl (term365 _108511 s t x)). Qed.
Lemma lem4616294 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term366 _108511 s t) = (term357 _108511 s t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616293 _108511 s t x)). Qed.
Lemma lem4616295 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616296 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term367 _108511 s t) = (term358 _108511 s t).
Proof. exact (MK_COMB (@lem4616295 _108511) (@lem4616294 _108511 s t)). Qed.
Lemma lem4616297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616298 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term368 _108511 s t) = (term359 _108511 s t).
Proof. exact (MK_COMB (@lem4616297) (@lem4616296 _108511 s t)). Qed.
Lemma lem4616299 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (eq_refl (term285 _108511 t)). Qed.
Lemma lem4616300 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term363 _108511 s t) = (term360 _108511 s t).
Proof. exact (MK_COMB (@lem4616298 _108511 s t) (@lem4616299 _108511 t)). Qed.
Lemma lem4616301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4616302 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term369 _108511 s t) = (term370 _108511 s t).
Proof. exact (MK_COMB (@lem4616301) (@lem4616300 _108511 s t)). Qed.
Lemma lem4616303 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term365 _108511 s t x) = (term355 _108511 s t x).
Proof. exact (eq_refl (term365 _108511 s t x)). Qed.
Lemma lem4616304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616305 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term371 _108511 s t x) = (term372 _108511 s t x).
Proof. exact (MK_COMB (@lem4616304) (@lem4616303 _108511 s t x)). Qed.
Lemma lem4616306 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (eq_refl (term285 _108511 t)). Qed.
Lemma lem4616307 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) : (term373 _108511 s x t) = (term374 _108511 s x t).
Proof. exact (MK_COMB (@lem4616305 _108511 s t x) (@lem4616306 _108511 t)). Qed.
Lemma lem4616308 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term375 _108511 s t) = (term376 _108511 s t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616307 _108511 s x t)). Qed.
Lemma lem4616309 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616310 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term364 _108511 s t) = (term377 _108511 s t).
Proof. exact (MK_COMB (@lem4616309 _108511) (@lem4616308 _108511 s t)). Qed.
Lemma lem4616311 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term363 _108511 s t) = (term364 _108511 s t)) = ((term360 _108511 s t) = (term377 _108511 s t)).
Proof. exact (MK_COMB (@lem4616302 _108511 s t) (@lem4616310 _108511 s t)). Qed.
Lemma lem4616312 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term360 _108511 s t) = (term377 _108511 s t).
Proof. exact (EQ_MP (@lem4616311 _108511 s t) (@lem4616292 _108511 s t)). Qed.
Lemma lem4616313 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term331 _108511 s t) = (term377 _108511 s t).
Proof. exact (TRANS (@lem4616288 _108511 s t) (@lem4616312 _108511 s t)). Qed.
Lemma lem4616314 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term339 _108511 s t) = (term378 _108511 s t).
Proof. exact (MK_COMB (@lem4616260 _108511 s t) (@lem4616313 _108511 s t)). Qed.
Lemma lem4616316 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4616317 {_108511 : Type'} (P : _108511 -> Prop) (Q : _108511 -> Prop) : (term342 _108511 P Q) = (term343 _108511 P Q).
Proof. exact (@lem4616316 _108511 P Q). Qed.
Lemma lem4616318 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term379 _108511 s t) = (term380 _108511 s t).
Proof. exact (@lem4616317 _108511 (term381 _108511 s t) (term376 _108511 s t)). Qed.
Lemma lem4616319 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term382 _108511 s t x) = (term383 _108511 s t x).
Proof. exact (eq_refl (term382 _108511 s t x)). Qed.
Lemma lem4616320 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term384 _108511 s t) = (term381 _108511 s t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616319 _108511 s t x)). Qed.
Lemma lem4616321 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616322 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term385 _108511 s t) = (term340 _108511 s t).
Proof. exact (MK_COMB (@lem4616321 _108511) (@lem4616320 _108511 s t)). Qed.
Lemma lem4616323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616324 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term386 _108511 s t) = (term341 _108511 s t).
Proof. exact (MK_COMB (@lem4616323) (@lem4616322 _108511 s t)). Qed.
Lemma lem4616325 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) : (term387 _108511 s t x) = (term374 _108511 s x t).
Proof. exact (eq_refl (term387 _108511 s t x)). Qed.
Lemma lem4616326 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term388 _108511 s t) = (term376 _108511 s t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616325 _108511 s x t)). Qed.
Lemma lem4616327 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616328 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term389 _108511 s t) = (term377 _108511 s t).
Proof. exact (MK_COMB (@lem4616327 _108511) (@lem4616326 _108511 s t)). Qed.
Lemma lem4616329 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term379 _108511 s t) = (term378 _108511 s t).
Proof. exact (MK_COMB (@lem4616324 _108511 s t) (@lem4616328 _108511 s t)). Qed.
Lemma lem4616330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4616331 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term390 _108511 s t) = (term391 _108511 s t).
Proof. exact (MK_COMB (@lem4616330) (@lem4616329 _108511 s t)). Qed.
Lemma lem4616332 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term382 _108511 s t x) = (term383 _108511 s t x).
Proof. exact (eq_refl (term382 _108511 s t x)). Qed.
Lemma lem4616333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616334 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term392 _108511 s t x) = (term393 _108511 s t x).
Proof. exact (MK_COMB (@lem4616333) (@lem4616332 _108511 s t x)). Qed.
Lemma lem4616335 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) : (term387 _108511 s t x) = (term374 _108511 s x t).
Proof. exact (eq_refl (term387 _108511 s t x)). Qed.
Lemma lem4616336 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) : (term394 _108511 s t x) = (term395 _108511 s x t).
Proof. exact (MK_COMB (@lem4616334 _108511 s t x) (@lem4616335 _108511 s x t)). Qed.
Lemma lem4616337 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term396 _108511 s t) = (term397 _108511 s t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616336 _108511 s x t)). Qed.
Lemma lem4616338 {_108511 : Type'} : (@ex _108511) = (@ex _108511).
Proof. exact (eq_refl (@ex _108511)). Qed.
Lemma lem4616339 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term380 _108511 s t) = (term398 _108511 s t).
Proof. exact (MK_COMB (@lem4616338 _108511) (@lem4616337 _108511 s t)). Qed.
Lemma lem4616340 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : ((term379 _108511 s t) = (term380 _108511 s t)) = ((term378 _108511 s t) = (term398 _108511 s t)).
Proof. exact (MK_COMB (@lem4616331 _108511 s t) (@lem4616339 _108511 s t)). Qed.
Lemma lem4616341 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term378 _108511 s t) = (term398 _108511 s t).
Proof. exact (EQ_MP (@lem4616340 _108511 s t) (@lem4616318 _108511 s t)). Qed.
Lemma lem4616343 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term339 _108511 s t) = (term398 _108511 s t).
Proof. exact (TRANS (@lem4616314 _108511 s t) (@lem4616341 _108511 s t)). Qed.
Lemma lem4616344 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term289 _108511 s t) = (term398 _108511 s t).
Proof. exact (TRANS (@lem4616177 _108511 s t) (@lem4616343 _108511 s t)). Qed.
Lemma lem4616345 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : term398 _108511 s t.
Proof. exact (EQ_MP (@lem4616344 _108511 s t) (@lem4616097 _108511 s t h1)). Qed.
Lemma lem4616346 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term395 _108511 s x t) : term395 _108511 s x t.
Proof. exact (h1). Qed.
Lemma lem4616351 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616352 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616351 _108511 t x)). Qed.
Lemma lem4616353 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616354 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616353 _108511) (@lem4616352 _108511 t)). Qed.
Lemma lem4616373 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term372 _108511 s t x) = (term372 _108511 s t x).
Proof. exact (eq_refl (term372 _108511 s t x)). Qed.
Lemma lem4616374 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) : (term374 _108511 s x t) = (term374 _108511 s x t).
Proof. exact (MK_COMB (@lem4616373 _108511 s t x) (@lem4616354 _108511 t)). Qed.
Lemma lem4616377 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4616382 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616383 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616382 _108511 t x)). Qed.
Lemma lem4616384 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616385 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616384 _108511) (@lem4616383 _108511 t)). Qed.
Lemma lem4616396 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) : (term304 _108511 t s x) = (term304 _108511 t s x).
Proof. exact (eq_refl (term304 _108511 t s x)). Qed.
Lemma lem4616397 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term312 _108511 t s) = (term312 _108511 t s).
Proof. exact (fun_ext (fun x : _108511 => @lem4616396 _108511 t s x)). Qed.
Lemma lem4616398 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616399 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term313 _108511 t s) = (term313 _108511 t s).
Proof. exact (MK_COMB (@lem4616398 _108511) (@lem4616397 _108511 t s)). Qed.
Lemma lem4616400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616401 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : (term326 _108511 t s) = (term326 _108511 t s).
Proof. exact (MK_COMB (@lem4616400) (@lem4616399 _108511 t s)). Qed.
Lemma lem4616402 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term327 _108511 s t) = (term327 _108511 s t).
Proof. exact (MK_COMB (@lem4616401 _108511 t s) (@lem4616385 _108511 t)). Qed.
Lemma lem4616403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616404 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term333 _108511 s t) = (term333 _108511 s t).
Proof. exact (MK_COMB (@lem4616403) (@lem4616402 _108511 s t)). Qed.
Lemma lem4616405 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term383 _108511 s t x) = (term383 _108511 s t x).
Proof. exact (MK_COMB (@lem4616404 _108511 s t) (@lem4616377 _108511 t x)). Qed.
Lemma lem4616406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4616407 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) : (term393 _108511 s t x) = (term393 _108511 s t x).
Proof. exact (MK_COMB (@lem4616406) (@lem4616405 _108511 s t x)). Qed.
Lemma lem4616408 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) : (term395 _108511 s x t) = (term395 _108511 s x t).
Proof. exact (MK_COMB (@lem4616407 _108511 s t x) (@lem4616374 _108511 s x t)). Qed.
Lemma lem4616409 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term395 _108511 s x t) : term395 _108511 s x t.
Proof. exact (EQ_MP (@lem4616408 _108511 s x t) (@lem4616346 _108511 s x t h1)). Qed.
Lemma lem4616410 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term383 _108511 s t x.
Proof. exact (h1). Qed.
Lemma lem4616411 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term374 _108511 s x t.
Proof. exact (h1). Qed.
Lemma lem4616413 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term327 _108511 s t.
Proof. exact (proj1 (@lem4616410 _108511 s t x h1)). Qed.
Lemma lem4616414 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term285 _108511 t.
Proof. exact (proj2 (@lem4616413 _108511 s t x h1)). Qed.
Lemma lem4616416 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term285 _108511 t.
Proof. exact (proj2 (@lem4616411 _108511 s x t h1)). Qed.
Lemma lem4616417 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term355 _108511 s t x.
Proof. exact (proj1 (@lem4616411 _108511 s x t h1)). Qed.
Lemma lem4616418 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) (h1 : term303 _108511 t s x) : term303 _108511 t s x.
Proof. exact (h1). Qed.
Lemma lem4616440 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616441 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616440 _108511 t x)). Qed.
Lemma lem4616442 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616444 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616442 _108511) (@lem4616441 _108511 t)). Qed.
Lemma lem4616445 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term285 _108511 t.
Proof. exact (EQ_MP (@lem4616444 _108511 t) (@lem4616414 _108511 s t x h1)). Qed.
Lemma lem4616447 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616448 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616447 _108511 t x)). Qed.
Lemma lem4616449 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616451 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616449 _108511) (@lem4616448 _108511 t)). Qed.
Lemma lem4616452 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term285 _108511 t.
Proof. exact (EQ_MP (@lem4616451 _108511 t) (@lem4616416 _108511 s x t h1)). Qed.
Lemma lem4616462 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term163 _108511 t x) = (term163 _108511 t x).
Proof. exact (eq_refl (term163 _108511 t x)). Qed.
Lemma lem4616463 {_108511 : Type'} (t : _108511 -> Prop) : (term164 _108511 t) = (term164 _108511 t).
Proof. exact (fun_ext (fun x : _108511 => @lem4616462 _108511 t x)). Qed.
Lemma lem4616464 {_108511 : Type'} : (@all _108511) = (@all _108511).
Proof. exact (eq_refl (@all _108511)). Qed.
Lemma lem4616466 {_108511 : Type'} (t : _108511 -> Prop) : (term285 _108511 t) = (term285 _108511 t).
Proof. exact (MK_COMB (@lem4616464 _108511) (@lem4616463 _108511 t)). Qed.
Lemma lem4616467 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term285 _108511 t.
Proof. exact (EQ_MP (@lem4616466 _108511 t) (@lem4616416 _108511 s x t h1)). Qed.
Lemma lem4616471 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4616475 {_108511 : Type'} (_55473 : _108511) (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term165 _108511 t _55473.
Proof. exact (@lem4616445 _108511 s t x h1 _55473). Qed.
Lemma lem4616476 {_108511 : Type'} (t : _108511 -> Prop) (_55473 : _108511) : (term165 _108511 t _55473) = (term163 _108511 t _55473).
Proof. exact (eq_refl (term165 _108511 t _55473)). Qed.
Lemma lem4616478 {_108511 : Type'} (_55474 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term165 _108511 t _55474.
Proof. exact (@lem4616452 _108511 s x t h1 _55474). Qed.
Lemma lem4616479 {_108511 : Type'} (t : _108511 -> Prop) (_55474 : _108511) : (term165 _108511 t _55474) = (term163 _108511 t _55474).
Proof. exact (eq_refl (term165 _108511 t _55474)). Qed.
Lemma lem4616481 {_108511 : Type'} (_55475 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term165 _108511 t _55475.
Proof. exact (@lem4616467 _108511 s x t h1 _55475). Qed.
Lemma lem4616482 {_108511 : Type'} (t : _108511 -> Prop) (_55475 : _108511) : (term165 _108511 t _55475) = (term163 _108511 t _55475).
Proof. exact (eq_refl (term165 _108511 t _55475)). Qed.
Lemma lem4616493 {_108511 : Type'} (_55473 : _108511) (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term163 _108511 t _55473.
Proof. exact (EQ_MP (@lem4616476 _108511 t _55473) (@lem4616475 _108511 _55473 s t x h1)). Qed.
Lemma lem4616495 {_108511 : Type'} (_55474 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term163 _108511 t _55474.
Proof. exact (EQ_MP (@lem4616479 _108511 t _55474) (@lem4616478 _108511 _55474 s x t h1)). Qed.
Lemma lem4616501 {_108511 : Type'} (_55475 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term163 _108511 t _55475.
Proof. exact (EQ_MP (@lem4616482 _108511 t _55475) (@lem4616481 _108511 _55475 s x t h1)). Qed.
Lemma lem4616503 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4616505 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : t x.
Proof. exact (proj2 (@lem4616410 _108511 s t x h1)). Qed.
Lemma lem4616506 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term168 _108511 t x.
Proof. exact (fun h0 : term163 _108511 t x => @lem4616505 _108511 s t x h1). Qed.
Lemma lem4616508 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4616509 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term168 _108511 t x) = (t x).
Proof. exact (@lem4616508 (t x)). Qed.
Lemma lem4616510 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : t x.
Proof. exact (EQ_MP (@lem4616509 _108511 t x) (@lem4616506 _108511 s t x h1)). Qed.
Lemma lem4616513 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4616515 {_108511 : Type'} (t : _108511 -> Prop) (_55473 : _108511) : (term163 _108511 t _55473) = (term170 _108511 t _55473).
Proof. exact (@lem4616513 (t _55473)). Qed.
Lemma lem4616518 {_108511 : Type'} (_55473 : _108511) (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term170 _108511 t _55473.
Proof. exact (EQ_MP (@lem4616515 _108511 t _55473) (@lem4616493 _108511 _55473 s t x h1)). Qed.
Lemma lem4616519 {_108511 : Type'} (_55473 : _108511) (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term170 _108511 t _55473.
Proof. exact (@lem4616518 _108511 _55473 s t x h1). Qed.
Lemma lem4616520 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term170 _108511 t x.
Proof. exact (@lem4616519 _108511 x s t x h1). Qed.
Lemma lem4616523 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : False.
Proof. exact (@lem4616520 _108511 s t x h1 (@lem4616510 _108511 s t x h1)). Qed.
Lemma lem4616524 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : term171.
Proof. exact (fun h0 : ~ False => @lem4616523 _108511 s t x h1). Qed.
Lemma lem4616526 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4616527 : term171 = False.
Proof. exact (@lem4616526 False). Qed.
Lemma lem4616528 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (x : _108511) (h1 : term383 _108511 s t x) : False.
Proof. exact (EQ_MP (@lem4616527) (@lem4616524 _108511 s t x h1)). Qed.
Lemma lem4616530 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) (h1 : term303 _108511 t s x) : t x.
Proof. exact (proj1 (@lem4616418 _108511 t s x h1)). Qed.
Lemma lem4616531 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) (h1 : term303 _108511 t s x) : term168 _108511 t x.
Proof. exact (fun h0 : term163 _108511 t x => @lem4616530 _108511 t s x h1). Qed.
Lemma lem4616533 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4616534 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term168 _108511 t x) = (t x).
Proof. exact (@lem4616533 (t x)). Qed.
Lemma lem4616535 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) (x : _108511) (h1 : term303 _108511 t s x) : t x.
Proof. exact (EQ_MP (@lem4616534 _108511 t x) (@lem4616531 _108511 t s x h1)). Qed.
Lemma lem4616538 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4616540 {_108511 : Type'} (t : _108511 -> Prop) (_55474 : _108511) : (term163 _108511 t _55474) = (term170 _108511 t _55474).
Proof. exact (@lem4616538 (t _55474)). Qed.
Lemma lem4616543 {_108511 : Type'} (_55474 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term170 _108511 t _55474.
Proof. exact (EQ_MP (@lem4616540 _108511 t _55474) (@lem4616495 _108511 _55474 s x t h1)). Qed.
Lemma lem4616544 {_108511 : Type'} (_55474 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term170 _108511 t _55474.
Proof. exact (@lem4616543 _108511 _55474 s x t h1). Qed.
Lemma lem4616545 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term170 _108511 t x.
Proof. exact (@lem4616544 _108511 x s x t h1). Qed.
Lemma lem4616548 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term303 _108511 t s x) (h2 : term374 _108511 s x t) : False.
Proof. exact (@lem4616545 _108511 s x t h2 (@lem4616535 _108511 t s x h1)). Qed.
Lemma lem4616549 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term303 _108511 t s x) (h2 : term374 _108511 s x t) : term171.
Proof. exact (fun h0 : ~ False => @lem4616548 _108511 s x t h1 h2). Qed.
Lemma lem4616551 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4616552 : term171 = False.
Proof. exact (@lem4616551 False). Qed.
Lemma lem4616553 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term303 _108511 t s x) (h2 : term374 _108511 s x t) : False.
Proof. exact (EQ_MP (@lem4616552) (@lem4616549 _108511 s x t h1 h2)). Qed.
Lemma lem4616555 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4616556 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) (h1 : t x) : term168 _108511 t x.
Proof. exact (fun h0 : term163 _108511 t x => @lem4616555 _108511 t x h1). Qed.
Lemma lem4616558 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4616559 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) : (term168 _108511 t x) = (t x).
Proof. exact (@lem4616558 (t x)). Qed.
Lemma lem4616560 {_108511 : Type'} (t : _108511 -> Prop) (x : _108511) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4616559 _108511 t x) (@lem4616556 _108511 t x h1)). Qed.
Lemma lem4616563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4616565 {_108511 : Type'} (t : _108511 -> Prop) (_55475 : _108511) : (term163 _108511 t _55475) = (term170 _108511 t _55475).
Proof. exact (@lem4616563 (t _55475)). Qed.
Lemma lem4616568 {_108511 : Type'} (_55475 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term170 _108511 t _55475.
Proof. exact (EQ_MP (@lem4616565 _108511 t _55475) (@lem4616501 _108511 _55475 s x t h1)). Qed.
Lemma lem4616569 {_108511 : Type'} (_55475 : _108511) (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term170 _108511 t _55475.
Proof. exact (@lem4616568 _108511 _55475 s x t h1). Qed.
Lemma lem4616570 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : term170 _108511 t x.
Proof. exact (@lem4616569 _108511 x s x t h1). Qed.
Lemma lem4616573 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : False.
Proof. exact (@lem4616570 _108511 s x t h2 (@lem4616560 _108511 t x h1)). Qed.
Lemma lem4616574 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : term171.
Proof. exact (fun h0 : ~ False => @lem4616573 _108511 s x t h1 h2). Qed.
Lemma lem4616576 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4616577 : term171 = False.
Proof. exact (@lem4616576 False). Qed.
Lemma lem4616578 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : False.
Proof. exact (EQ_MP (@lem4616577) (@lem4616574 _108511 s x t h1 h2)). Qed.
Lemma lem4616579 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4616578 _108511 s x t h1 h2) (fun h3 : False => @lem4616503 _108511 t x h1)). Qed.
Lemma lem4616580 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : False.
Proof. exact (EQ_MP (@lem4616579 _108511 s x t h1 h2) (@lem4616503 _108511 t x h1)). Qed.
Lemma lem4616581 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4616580 _108511 s x t h1 h2) (fun h3 : False => @lem4616471 _108511 t x h1)). Qed.
Lemma lem4616582 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : False.
Proof. exact (EQ_MP (@lem4616581 _108511 s x t h1 h2) (@lem4616471 _108511 t x h1)). Qed.
Lemma lem4616583 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4616582 _108511 s x t h1 h2) (fun h3 : False => @lem4616471 _108511 t x h1)). Qed.
Lemma lem4616584 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : t x) (h2 : term374 _108511 s x t) : False.
Proof. exact (EQ_MP (@lem4616583 _108511 s x t h1 h2) (@lem4616471 _108511 t x h1)). Qed.
Lemma lem4616585 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term374 _108511 s x t) : False.
Proof. exact (or_elim (@lem4616417 _108511 s x t h1) (fun h0 : term303 _108511 t s x => @lem4616553 _108511 s x t h0 h1) (fun h0 : t x => @lem4616584 _108511 s x t h0 h1)). Qed.
Lemma lem4616586 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term395 _108511 s x t) : False.
Proof. exact (or_elim (@lem4616409 _108511 s x t h1) (fun h0 : term383 _108511 s t x => @lem4616528 _108511 s t x h0) (fun h0 : term374 _108511 s x t => @lem4616585 _108511 s x t h0)). Qed.
Lemma lem4616587 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term395 _108511 s x t) : (term395 _108511 s x t) = False.
Proof. exact (prop_ext (fun h2 : term395 _108511 s x t => @lem4616586 _108511 s x t h1) (fun h2 : False => @lem4616409 _108511 s x t h1)). Qed.
Lemma lem4616588 {_108511 : Type'} (s : _108511 -> Prop) (x : _108511) (t : _108511 -> Prop) (h1 : term395 _108511 s x t) : False.
Proof. exact (EQ_MP (@lem4616587 _108511 s x t h1) (@lem4616409 _108511 s x t h1)). Qed.
Lemma lem4616589 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : False.
Proof. exact (ex_elim (@lem4616345 _108511 s t h1) (fun x : _108511 => fun h0 : term397 _108511 s t x => @lem4616588 _108511 s x t h0)). Qed.
Lemma lem4616590 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : (term289 _108511 s t) = False.
Proof. exact (prop_ext (fun h2 : term289 _108511 s t => @lem4616589 _108511 s t h1) (fun h2 : False => @lem4616097 _108511 s t h1)). Qed.
Lemma lem4616591 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : False.
Proof. exact (EQ_MP (@lem4616590 _108511 s t h1) (@lem4616097 _108511 s t h1)). Qed.
Lemma lem4616592 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term288 _108511 s t.
Proof. exact (fun h0 : term289 _108511 s t => @lem4616591 _108511 s t h0). Qed.
Lemma lem4616593 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term286 _108511 s t) = (term285 _108511 t).
Proof. exact (EQ_MP (@lem4616096 _108511 s t) (@lem4616592 _108511 s t)). Qed.
Lemma lem4616598 {_108511 : Type'} (t : _108511 -> Prop) : term297 _108511 t.
Proof. exact (fun s : _108511 -> Prop => @lem4616593 _108511 s t). Qed.
Lemma lem4616603 {_108511 : Type'} : term301 _108511.
Proof. exact (fun t : _108511 -> Prop => @lem4616598 _108511 t). Qed.
Lemma lem4616604 {_108511 : Type'} : term300 _108511.
Proof. exact (EQ_MP (@lem4616092 _108511) (@lem4616603 _108511)). Qed.
Lemma lem4616605 {_108511 : Type'} (t : _108511 -> Prop) : term399 _108511 t.
Proof. exact (@lem4616604 _108511 t). Qed.
Lemma lem4616606 {_108511 : Type'} (t : _108511 -> Prop) : (term399 _108511 t) = (term296 _108511 t).
Proof. exact (eq_refl (term399 _108511 t)). Qed.
Lemma lem4616607 {_108511 : Type'} (t : _108511 -> Prop) : term296 _108511 t.
Proof. exact (EQ_MP (@lem4616606 _108511 t) (@lem4616605 _108511 t)). Qed.
Lemma lem4616608 {_108511 : Type'} (t : _108511 -> Prop) (s : _108511 -> Prop) : term400 _108511 t s.
Proof. exact (@lem4616607 _108511 t s). Qed.
Lemma lem4616609 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term400 _108511 t s) = (term288 _108511 s t).
Proof. exact (eq_refl (term400 _108511 t s)). Qed.
Lemma lem4616610 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term288 _108511 s t.
Proof. exact (EQ_MP (@lem4616609 _108511 s t) (@lem4616608 _108511 t s)). Qed.
Lemma lem4616612 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term288 _108511 s t.
Proof. exact (@lem4615973 _108511 s t (@lem4616610 _108511 s t)). Qed.
Lemma lem4616613 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : False.
Proof. exact (@lem4616612 _108511 s t (@lem4615957 _108511 s t h1)). Qed.
Lemma lem4616614 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : (term289 _108511 s t) = False.
Proof. exact (prop_ext (fun h2 : term289 _108511 s t => @lem4616613 _108511 s t h1) (fun h2 : False => @lem4615957 _108511 s t h1)). Qed.
Lemma lem4616615 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) (h1 : term289 _108511 s t) : False.
Proof. exact (EQ_MP (@lem4616614 _108511 s t h1) (@lem4615957 _108511 s t h1)). Qed.
Lemma lem4616616 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : term288 _108511 s t.
Proof. exact (fun h0 : term289 _108511 s t => @lem4616615 _108511 s t h0). Qed.
Lemma lem4616617 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term286 _108511 s t) = (term285 _108511 t).
Proof. exact (EQ_MP (@lem4615956 _108511 s t) (@lem4616616 _108511 s t)). Qed.
Lemma lem4616618 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term272 _108511 s t) = (term270 _108511 t).
Proof. exact (EQ_MP (@lem4615952 _108511 s t) (@lem4616617 _108511 s t)). Qed.
Lemma lem4616620 {A : Type'} (s : A -> Prop) : term401 A s.
Proof. exact (@lem3864294 A s). Qed.
Lemma lem4616621 {A : Type'} (s : A -> Prop) : (term401 A s) = ((term402 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl (term401 A s)). Qed.
Lemma lem4616623 (n : nat) : term403 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem4616624 (n : nat) : (term403 n) = (term404 n).
Proof. exact (eq_refl (term403 n)). Qed.
Lemma lem4616625 (n : nat) : term404 n.
Proof. exact (EQ_MP (@lem4616624 n) (@lem4616623 n)). Qed.
Lemma lem4616627 (n : nat) (h1 : term405 n) : term405 n.
Proof. exact (h1). Qed.
Lemma lem4616637 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem4616638 {A : Type'} (t : A -> Prop) : (@HAS_SIZE A t) = (@HAS_SIZE A t).
Proof. exact (eq_refl (@HAS_SIZE A t)). Qed.
Lemma lem4616639 {A : Type'} (t : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (@HAS_SIZE A t n) = (term402 A t).
Proof. exact (MK_COMB (@lem4616638 A t) (@lem4616637 n h1)). Qed.
Lemma lem4616640 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term268 A t s) = (term268 A t s).
Proof. exact (eq_refl (term268 A t s)). Qed.
Lemma lem4616641 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term406 A s t n) = (term407 A s t).
Proof. exact (MK_COMB (@lem4616640 A t s) (@lem4616639 A t n h1)). Qed.
Lemma lem4616644 {A : Type'} (GEN_PVAR_174 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_174) = (@SETSPEC (A -> Prop) GEN_PVAR_174).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_174)). Qed.
Lemma lem4616645 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term408 A GEN_PVAR_174 s t n) = (term409 A GEN_PVAR_174 s t).
Proof. exact (MK_COMB (@lem4616644 A GEN_PVAR_174) (@lem4616641 A s t n h1)). Qed.
Lemma lem4616646 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4616647 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term410 A GEN_PVAR_174 s n t) = (term411 A GEN_PVAR_174 s t).
Proof. exact (MK_COMB (@lem4616645 A GEN_PVAR_174 s t n h1) (@lem4616646 A t)). Qed.
Lemma lem4616648 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term412 A GEN_PVAR_174 s n) = (term413 A GEN_PVAR_174 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4616647 A GEN_PVAR_174 s t n h1)). Qed.
Lemma lem4616649 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4616650 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term414 A GEN_PVAR_174 s n) = (term415 A GEN_PVAR_174 s).
Proof. exact (MK_COMB (@lem4616649 A) (@lem4616648 A GEN_PVAR_174 s n h1)). Qed.
Lemma lem4616655 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term416 A s n) = (term417 A s).
Proof. exact (fun_ext (fun GEN_PVAR_174 : A -> Prop => @lem4616650 A GEN_PVAR_174 s n h1)). Qed.
Lemma lem4616656 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4616657 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term418 A s n) = (term419 A s).
Proof. exact (MK_COMB (@lem4616656 A) (@lem4616655 A s n h1)). Qed.
Lemma lem4616658 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4616659 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term420 A s n) = (term421 A s).
Proof. exact (MK_COMB (@lem4616658 A) (@lem4616657 A s n h1)). Qed.
Lemma lem4616660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4616661 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term422 A s n) = (term423 A s).
Proof. exact (MK_COMB (@lem4616660) (@lem4616659 A s n h1)). Qed.
Lemma lem4616667 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem4616668 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4616669 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term424.
Proof. exact (MK_COMB (@lem4616668) (@lem4616667 n h1)). Qed.
Lemma lem4616670 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem4616671 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4616669 n h1) (@lem4616670)). Qed.
Lemma lem4616673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4616674 (x : nat) : (x = x) = True.
Proof. exact (@lem4616673 nat x). Qed.
Lemma lem4616675 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem4616674 (NUMERAL 0)). Qed.
Lemma lem4616676 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem4616671 n h1) (@lem4616675)). Qed.
Lemma lem4616677 {A : Type'} (s : A -> Prop) : (term425 A s) = (term425 A s).
Proof. exact (eq_refl (term425 A s)). Qed.
Lemma lem4616678 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term426 A s n) = (term427 A s).
Proof. exact (MK_COMB (@lem4616677 A s) (@lem4616676 n h1)). Qed.
Lemma lem4616680 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4616681 {A : Type'} (s : A -> Prop) : (term427 A s) = True.
Proof. exact (@lem4616680 (@FINITE A s)). Qed.
Lemma lem4616682 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term426 A s n) = True.
Proof. exact (TRANS (@lem4616678 A s n h1) (@lem4616681 A s)). Qed.
Lemma lem4616683 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : ((term420 A s n) = (term426 A s n)) = ((term421 A s) = True).
Proof. exact (MK_COMB (@lem4616661 A s n h1) (@lem4616682 A s n h1)). Qed.
Lemma lem4616685 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4616686 {A : Type'} (s : A -> Prop) : ((term421 A s) = True) = (term421 A s).
Proof. exact (@lem4616685 (term421 A s)). Qed.
Lemma lem4616693 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : ((term420 A s n) = (term426 A s n)) = (term421 A s).
Proof. exact (TRANS (@lem4616683 A s n h1) (@lem4616686 A s)). Qed.
Lemma lem4616694 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term421 A s) = ((term420 A s n) = (term426 A s n)).
Proof. exact (SYM (@lem4616693 A s n h1)). Qed.
Lemma lem4616695 (n : nat) : term428 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem4616719 (n : nat) (h1 : term405 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem4616695 n (@lem4616627 n h1)). Qed.
Lemma lem4616720 {A : Type'} (s : A -> Prop) : (term425 A s) = (term425 A s).
Proof. exact (eq_refl (term425 A s)). Qed.
Lemma lem4616721 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term405 n) : (term426 A s n) = (term429 A s).
Proof. exact (MK_COMB (@lem4616720 A s) (@lem4616719 n h1)). Qed.
Lemma lem4616723 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4616724 {A : Type'} (s : A -> Prop) : (term429 A s) = (@FINITE A s).
Proof. exact (@lem4616723 (@FINITE A s)). Qed.
Lemma lem4616725 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term405 n) : (term426 A s n) = (@FINITE A s).
Proof. exact (TRANS (@lem4616721 A s n h1) (@lem4616724 A s)). Qed.
Lemma lem4616726 {A : Type'} (s : A -> Prop) (n : nat) : (term422 A s n) = (term422 A s n).
Proof. exact (eq_refl (term422 A s n)). Qed.
Lemma lem4616727 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term405 n) : ((term420 A s n) = (term426 A s n)) = ((term420 A s n) = (@FINITE A s)).
Proof. exact (MK_COMB (@lem4616726 A s n) (@lem4616725 A s n h1)). Qed.
Lemma lem4616730 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term405 n) : ((term420 A s n) = (@FINITE A s)) = ((term420 A s n) = (term426 A s n)).
Proof. exact (SYM (@lem4616727 A s n h1)). Qed.
Lemma lem4616738 {A : Type'} (s : A -> Prop) : (term402 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4616621 A s) (@lem4616620 A s)). Qed.
Lemma lem4616739 {A : Type'} (s : A -> Prop) : (term402 A s) = (s = (@EMPTY A)).
Proof. exact (@lem4616738 A s). Qed.
Lemma lem4616740 {A : Type'} (t : A -> Prop) : (term402 A t) = (t = (@EMPTY A)).
Proof. exact (@lem4616739 A t). Qed.
Lemma lem4616743 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term268 A t s) = (term268 A t s).
Proof. exact (eq_refl (term268 A t s)). Qed.
Lemma lem4616744 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term407 A s t) = (term271 A s t).
Proof. exact (MK_COMB (@lem4616743 A t s) (@lem4616740 A t)). Qed.
Lemma lem4616746 {_108511 : Type'} (s : _108511 -> Prop) (t : _108511 -> Prop) : (term271 _108511 s t) = (t = (@EMPTY _108511)).
Proof. exact (EQ_MP (@lem4615857 _108511 s t) (@lem4616618 _108511 s t)). Qed.
Lemma lem4616747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term271 A s t) = (t = (@EMPTY A)).
Proof. exact (@lem4616746 A s t). Qed.
Lemma lem4616750 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term407 A s t) = (t = (@EMPTY A)).
Proof. exact (TRANS (@lem4616744 A s t) (@lem4616747 A s t)). Qed.
Lemma lem4616751 {A : Type'} (GEN_PVAR_174 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_174) = (@SETSPEC (A -> Prop) GEN_PVAR_174).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_174)). Qed.
Lemma lem4616752 {A : Type'} (s : A -> Prop) (GEN_PVAR_174 : A -> Prop) (t : A -> Prop) : (term409 A GEN_PVAR_174 s t) = (term430 A GEN_PVAR_174 t).
Proof. exact (MK_COMB (@lem4616751 A GEN_PVAR_174) (@lem4616750 A s t)). Qed.
Lemma lem4616753 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4616754 {A : Type'} (s : A -> Prop) (GEN_PVAR_174 : A -> Prop) (t : A -> Prop) : (term411 A GEN_PVAR_174 s t) = (term431 A GEN_PVAR_174 t).
Proof. exact (MK_COMB (@lem4616752 A s GEN_PVAR_174 t) (@lem4616753 A t)). Qed.
Lemma lem4616755 {A : Type'} (s : A -> Prop) (GEN_PVAR_174 : A -> Prop) : (term413 A GEN_PVAR_174 s) = (term432 A GEN_PVAR_174).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4616754 A s GEN_PVAR_174 t)). Qed.
Lemma lem4616756 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4616757 {A : Type'} (s : A -> Prop) (GEN_PVAR_174 : A -> Prop) : (term415 A GEN_PVAR_174 s) = (term433 A GEN_PVAR_174).
Proof. exact (MK_COMB (@lem4616756 A) (@lem4616755 A s GEN_PVAR_174)). Qed.
Lemma lem4616762 {A : Type'} (s : A -> Prop) : (term417 A s) = (term434 A).
Proof. exact (fun_ext (fun GEN_PVAR_174 : A -> Prop => @lem4616757 A s GEN_PVAR_174)). Qed.
Lemma lem4616763 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4616764 {A : Type'} (s : A -> Prop) : (term419 A s) = (term435 A).
Proof. exact (MK_COMB (@lem4616763 A) (@lem4616762 A s)). Qed.
Lemma lem4616765 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4616766 {A : Type'} (s : A -> Prop) : (term421 A s) = (term436 A).
Proof. exact (MK_COMB (@lem4616765 A) (@lem4616764 A s)). Qed.
Lemma lem4616767 {A : Type'} (s : A -> Prop) : (term436 A) = (term421 A s).
Proof. exact (SYM (@lem4616766 A s)). Qed.
Lemma lem4616771 {_88341 : Type'} (a : _88341) : (term267 _88341 a) = (@INSERT _88341 a (@EMPTY _88341)).
Proof. exact (EQ_MP (@lem4615789 _88341 a) (@lem4615788 _88341 a)). Qed.
Lemma lem4616772 {A : Type'} (a : A -> Prop) : (term437 A a) = (@INSERT (A -> Prop) a (@EMPTY (A -> Prop))).
Proof. exact (@lem4616771 (A -> Prop) a). Qed.
Lemma lem4616773 {A : Type'} : (term435 A) = (@INSERT (A -> Prop) (@EMPTY A) (@EMPTY (A -> Prop))).
Proof. exact (@lem4616772 A (@EMPTY A)). Qed.
Lemma lem4616774 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4616775 {A : Type'} : (term436 A) = (term438 A).
Proof. exact (MK_COMB (@lem4616774 A) (@lem4616773 A)). Qed.
Lemma lem4616777 {_92373 : Type'} (a : _92373) : (term264 _92373 a) = True.
Proof. exact (EQ_MP (@lem4615781 _92373 a) (@lem4615780 _92373 a)). Qed.
Lemma lem4616778 {A : Type'} (a : A -> Prop) : (term439 A a) = True.
Proof. exact (@lem4616777 (A -> Prop) a). Qed.
Lemma lem4616779 {A : Type'} : (term438 A) = True.
Proof. exact (@lem4616778 A (@EMPTY A)). Qed.
Lemma lem4616780 {A : Type'} : (term436 A) = True.
Proof. exact (TRANS (@lem4616775 A) (@lem4616779 A)). Qed.
Lemma lem4616781 {A : Type'} : True = (term436 A).
Proof. exact (SYM (@lem4616780 A)). Qed.
Lemma lem4616782 {A : Type'} : term436 A.
Proof. exact (EQ_MP (@lem4616781 A) (@lem0)). Qed.
Lemma lem4616783 {A : Type'} (s : A -> Prop) : term421 A s.
Proof. exact (EQ_MP (@lem4616767 A s) (@lem4616782 A)). Qed.
Lemma lem4616797 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4616808 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4616797 A s) (@lem4615776 A s h1)). Qed.
Lemma lem4616809 {A : Type'} (s : A -> Prop) (n : nat) : (term422 A s n) = (term422 A s n).
Proof. exact (eq_refl (term422 A s n)). Qed.
Lemma lem4616810 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : ((term420 A s n) = (@FINITE A s)) = ((term420 A s n) = True).
Proof. exact (MK_COMB (@lem4616809 A s n) (@lem4616808 A s h1)). Qed.
Lemma lem4616812 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4616813 {A : Type'} (s : A -> Prop) (n : nat) : ((term420 A s n) = True) = (term420 A s n).
Proof. exact (@lem4616812 (term420 A s n)). Qed.
Lemma lem4616820 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : ((term420 A s n) = (@FINITE A s)) = (term420 A s n).
Proof. exact (TRANS (@lem4616810 A n s h1) (@lem4616813 A s n)). Qed.
Lemma lem4616821 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term420 A s n) = ((term420 A s n) = (@FINITE A s)).
Proof. exact (SYM (@lem4616820 A n s h1)). Qed.
Lemma lem4616835 {A : Type'} (s : A -> Prop) : term440 A s.
Proof. exact (@lem82 (@FINITE A s)). Qed.
Lemma lem4616846 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (@FINITE A s) = False.
Proof. exact (@lem4616835 A s (@lem4615777 A s h1)). Qed.
Lemma lem4616847 {A : Type'} (s : A -> Prop) (n : nat) : (term422 A s n) = (term422 A s n).
Proof. exact (eq_refl (term422 A s n)). Qed.
Lemma lem4616848 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term262 A s) : ((term420 A s n) = (@FINITE A s)) = ((term420 A s n) = False).
Proof. exact (MK_COMB (@lem4616847 A s n) (@lem4616846 A s h1)). Qed.
Lemma lem4616850 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4616851 {A : Type'} (s : A -> Prop) (n : nat) : ((term420 A s n) = False) = (term441 A s n).
Proof. exact (@lem4616850 (term420 A s n)). Qed.
Lemma lem4616858 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term262 A s) : ((term420 A s n) = (@FINITE A s)) = (term441 A s n).
Proof. exact (TRANS (@lem4616848 A n s h1) (@lem4616851 A s n)). Qed.
Lemma lem4616859 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term441 A s n) = ((term420 A s n) = (@FINITE A s)).
Proof. exact (SYM (@lem4616858 A n s h1)). Qed.
Lemma lem4616861 {_108492 : Type'} (P : _108492 -> Prop) (Q : _108492 -> Prop) : (term218 _108492 P Q) = (term219 _108492 P Q).
Proof. exact (EQ_MP (@lem4615688 _108492 P Q) (@lem4615771 _108492 P Q)). Qed.
Lemma lem4616862 {A : Type'} (P : type686 A) (Q : type686 A) : (term442 A P Q) = (term443 A P Q).
Proof. exact (@lem4616861 (A -> Prop) P Q). Qed.
Lemma lem4616863 {A : Type'} (s : A -> Prop) (n : nat) : (term444 A s n) = (term445 A s n).
Proof. exact (@lem4616862 A (term446 A s) (term447 A n)). Qed.
Lemma lem4616864 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term448 A s t) = (@SUBSET A t s).
Proof. exact (eq_refl (term448 A s t)). Qed.
Lemma lem4616865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616866 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term449 A s t) = (term268 A t s).
Proof. exact (MK_COMB (@lem4616865) (@lem4616864 A t s)). Qed.
Lemma lem4616867 {A : Type'} (t : A -> Prop) (n : nat) : (term450 A n t) = (@HAS_SIZE A t n).
Proof. exact (eq_refl (term450 A n t)). Qed.
Lemma lem4616868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term451 A s n t) = (term406 A s t n).
Proof. exact (MK_COMB (@lem4616866 A t s) (@lem4616867 A t n)). Qed.
Lemma lem4616869 {A : Type'} (GEN_PVAR_174 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_174) = (@SETSPEC (A -> Prop) GEN_PVAR_174).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_174)). Qed.
Lemma lem4616870 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) : (term452 A GEN_PVAR_174 s n t) = (term408 A GEN_PVAR_174 s t n).
Proof. exact (MK_COMB (@lem4616869 A GEN_PVAR_174) (@lem4616868 A s t n)). Qed.
Lemma lem4616871 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4616872 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (n : nat) (t : A -> Prop) : (term453 A GEN_PVAR_174 s n t) = (term410 A GEN_PVAR_174 s n t).
Proof. exact (MK_COMB (@lem4616870 A GEN_PVAR_174 s t n) (@lem4616871 A t)). Qed.
Lemma lem4616873 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (n : nat) : (term454 A GEN_PVAR_174 s n) = (term412 A GEN_PVAR_174 s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4616872 A GEN_PVAR_174 s n t)). Qed.
Lemma lem4616874 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4616875 {A : Type'} (GEN_PVAR_174 : A -> Prop) (s : A -> Prop) (n : nat) : (term455 A GEN_PVAR_174 s n) = (term414 A GEN_PVAR_174 s n).
Proof. exact (MK_COMB (@lem4616874 A) (@lem4616873 A GEN_PVAR_174 s n)). Qed.
Lemma lem4616876 {A : Type'} (s : A -> Prop) (n : nat) : (term456 A s n) = (term416 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_174 : A -> Prop => @lem4616875 A GEN_PVAR_174 s n)). Qed.
Lemma lem4616877 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4616878 {A : Type'} (s : A -> Prop) (n : nat) : (term444 A s n) = (term418 A s n).
Proof. exact (MK_COMB (@lem4616877 A) (@lem4616876 A s n)). Qed.
Lemma lem4616879 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4616880 {A : Type'} (s : A -> Prop) (n : nat) : (term457 A s n) = (term458 A s n).
Proof. exact (MK_COMB (@lem4616879 A) (@lem4616878 A s n)). Qed.
Lemma lem4616881 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term448 A s y) = (@SUBSET A y s).
Proof. exact (eq_refl (term448 A s y)). Qed.
Lemma lem4616882 {A : Type'} (GEN_PVAR_172 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_172) = (@SETSPEC (A -> Prop) GEN_PVAR_172).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_172)). Qed.
Lemma lem4616883 {A : Type'} (GEN_PVAR_172 : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term459 A GEN_PVAR_172 s y) = (term460 A GEN_PVAR_172 y s).
Proof. exact (MK_COMB (@lem4616882 A GEN_PVAR_172) (@lem4616881 A y s)). Qed.
Lemma lem4616884 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4616885 {A : Type'} (GEN_PVAR_172 : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term461 A GEN_PVAR_172 s y) = (term462 A GEN_PVAR_172 s y).
Proof. exact (MK_COMB (@lem4616883 A GEN_PVAR_172 y s) (@lem4616884 A y)). Qed.
Lemma lem4616886 {A : Type'} (GEN_PVAR_172 : A -> Prop) (s : A -> Prop) : (term463 A GEN_PVAR_172 s) = (term464 A GEN_PVAR_172 s).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4616885 A GEN_PVAR_172 s y)). Qed.
Lemma lem4616887 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4616888 {A : Type'} (GEN_PVAR_172 : A -> Prop) (s : A -> Prop) : (term465 A GEN_PVAR_172 s) = (term466 A GEN_PVAR_172 s).
Proof. exact (MK_COMB (@lem4616887 A) (@lem4616886 A GEN_PVAR_172 s)). Qed.
Lemma lem4616889 {A : Type'} (s : A -> Prop) : (term467 A s) = (term468 A s).
Proof. exact (fun_ext (fun GEN_PVAR_172 : A -> Prop => @lem4616888 A GEN_PVAR_172 s)). Qed.
Lemma lem4616890 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4616891 {A : Type'} (s : A -> Prop) : (term469 A s) = (term470 A s).
Proof. exact (MK_COMB (@lem4616890 A) (@lem4616889 A s)). Qed.
Lemma lem4616892 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4616893 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term471 A t s) = (term472 A t s).
Proof. exact (MK_COMB (@lem4616892 A t) (@lem4616891 A s)). Qed.
Lemma lem4616894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4616895 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term473 A t s) = (term474 A t s).
Proof. exact (MK_COMB (@lem4616894) (@lem4616893 A t s)). Qed.
Lemma lem4616896 {A : Type'} (t : A -> Prop) (n : nat) : (term450 A n t) = (@HAS_SIZE A t n).
Proof. exact (eq_refl (term450 A n t)). Qed.
Lemma lem4616897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term475 A s n t) = (term476 A s t n).
Proof. exact (MK_COMB (@lem4616895 A t s) (@lem4616896 A t n)). Qed.
Lemma lem4616898 {A : Type'} (GEN_PVAR_173 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_173) = (@SETSPEC (A -> Prop) GEN_PVAR_173).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_173)). Qed.
Lemma lem4616899 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) : (term477 A GEN_PVAR_173 s n t) = (term478 A GEN_PVAR_173 s t n).
Proof. exact (MK_COMB (@lem4616898 A GEN_PVAR_173) (@lem4616897 A s t n)). Qed.
Lemma lem4616900 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4616901 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (n : nat) (t : A -> Prop) : (term479 A GEN_PVAR_173 s n t) = (term480 A GEN_PVAR_173 s n t).
Proof. exact (MK_COMB (@lem4616899 A GEN_PVAR_173 s t n) (@lem4616900 A t)). Qed.
Lemma lem4616902 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (n : nat) : (term481 A GEN_PVAR_173 s n) = (term482 A GEN_PVAR_173 s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4616901 A GEN_PVAR_173 s n t)). Qed.
Lemma lem4616903 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4616904 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (n : nat) : (term483 A GEN_PVAR_173 s n) = (term484 A GEN_PVAR_173 s n).
Proof. exact (MK_COMB (@lem4616903 A) (@lem4616902 A GEN_PVAR_173 s n)). Qed.
Lemma lem4616905 {A : Type'} (s : A -> Prop) (n : nat) : (term485 A s n) = (term486 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_173 : A -> Prop => @lem4616904 A GEN_PVAR_173 s n)). Qed.
Lemma lem4616906 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4616907 {A : Type'} (s : A -> Prop) (n : nat) : (term445 A s n) = (term487 A s n).
Proof. exact (MK_COMB (@lem4616906 A) (@lem4616905 A s n)). Qed.
Lemma lem4616908 {A : Type'} (s : A -> Prop) (n : nat) : ((term444 A s n) = (term445 A s n)) = ((term418 A s n) = (term487 A s n)).
Proof. exact (MK_COMB (@lem4616880 A s n) (@lem4616907 A s n)). Qed.
Lemma lem4616909 {A : Type'} (s : A -> Prop) (n : nat) : (term418 A s n) = (term487 A s n).
Proof. exact (EQ_MP (@lem4616908 A s n) (@lem4616863 A s n)). Qed.
Lemma lem4616910 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4616911 {A : Type'} (s : A -> Prop) (n : nat) : (term420 A s n) = (term488 A s n).
Proof. exact (MK_COMB (@lem4616910 A) (@lem4616909 A s n)). Qed.
Lemma lem4616912 {A : Type'} (s : A -> Prop) (n : nat) : (term488 A s n) = (term420 A s n).
Proof. exact (SYM (@lem4616911 A s n)). Qed.
Lemma lem4616913 {A : Type'} (s : A -> Prop) : term489 A s.
Proof. exact (@lem4603107 A s). Qed.
Lemma lem4616914 {A : Type'} (s : A -> Prop) : (term489 A s) = (term490 A s).
Proof. exact (eq_refl (term489 A s)). Qed.
Lemma lem4616915 {A : Type'} (s : A -> Prop) : term490 A s.
Proof. exact (EQ_MP (@lem4616914 A s) (@lem4616913 A s)). Qed.
Lemma lem4616916 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4616917 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term491 A s.
Proof. exact (@lem4616915 A s (@lem4616916 A s h1)). Qed.
Lemma lem4616918 {A : Type'} (s : A -> Prop) : (term491 A s) = ((term491 A s) = True).
Proof. exact (@lem7 (term491 A s)). Qed.
Lemma lem4616919 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term491 A s) = True.
Proof. exact (EQ_MP (@lem4616918 A s) (@lem4616917 A s h1)). Qed.
Lemma lem4616925 {A : Type'} (s : A -> Prop) : term492 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem4616926 {A : Type'} (s : A -> Prop) : (term492 A s) = (term493 A s).
Proof. exact (eq_refl (term492 A s)). Qed.
Lemma lem4616927 {A : Type'} (s : A -> Prop) : term493 A s.
Proof. exact (EQ_MP (@lem4616926 A s) (@lem4616925 A s)). Qed.
Lemma lem4616928 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term494 A s P.
Proof. exact (@lem4616927 A s P). Qed.
Lemma lem4616929 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term494 A s P) = (term495 A s P).
Proof. exact (eq_refl (term494 A s P)). Qed.
Lemma lem4616930 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term495 A s P.
Proof. exact (EQ_MP (@lem4616929 A s P) (@lem4616928 A s P)). Qed.
Lemma lem4616931 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4616932 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term496 A s P.
Proof. exact (@lem4616930 A s P (@lem4616931 A s h1)). Qed.
Lemma lem4616933 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term496 A s P) = ((term496 A s P) = True).
Proof. exact (@lem7 (term496 A s P)). Qed.
Lemma lem4616934 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term496 A s P) = True.
Proof. exact (EQ_MP (@lem4616933 A s P) (@lem4616932 A P s h1)). Qed.
Lemma lem4616953 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4616956 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term497 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem4616934 A P s h0). Qed.
Lemma lem4616957 {A : Type'} (s : type686 A) (P : type686 A) : term498 A s P.
Proof. exact (@lem4616956 (A -> Prop) s P). Qed.
Lemma lem4616958 {A : Type'} (s : A -> Prop) (n : nat) : term499 A s n.
Proof. exact (@lem4616957 A (term470 A s) (term447 A n)). Qed.
Lemma lem4616959 {A : Type'} (t : A -> Prop) (n : nat) : (term450 A n t) = (@HAS_SIZE A t n).
Proof. exact (eq_refl (term450 A n t)). Qed.
Lemma lem4616960 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term474 A t s) = (term474 A t s).
Proof. exact (eq_refl (term474 A t s)). Qed.
Lemma lem4616961 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term500 A s n t) = (term476 A s t n).
Proof. exact (MK_COMB (@lem4616960 A t s) (@lem4616959 A t n)). Qed.
Lemma lem4616962 {A : Type'} (GEN_PVAR_173 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_173) = (@SETSPEC (A -> Prop) GEN_PVAR_173).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_173)). Qed.
Lemma lem4616963 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) : (term501 A GEN_PVAR_173 s n t) = (term478 A GEN_PVAR_173 s t n).
Proof. exact (MK_COMB (@lem4616962 A GEN_PVAR_173) (@lem4616961 A s t n)). Qed.
Lemma lem4616964 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4616965 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (n : nat) (t : A -> Prop) : (term502 A GEN_PVAR_173 s n t) = (term480 A GEN_PVAR_173 s n t).
Proof. exact (MK_COMB (@lem4616963 A GEN_PVAR_173 s t n) (@lem4616964 A t)). Qed.
Lemma lem4616966 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (n : nat) : (term503 A GEN_PVAR_173 s n) = (term482 A GEN_PVAR_173 s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4616965 A GEN_PVAR_173 s n t)). Qed.
Lemma lem4616967 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4616968 {A : Type'} (GEN_PVAR_173 : A -> Prop) (s : A -> Prop) (n : nat) : (term504 A GEN_PVAR_173 s n) = (term484 A GEN_PVAR_173 s n).
Proof. exact (MK_COMB (@lem4616967 A) (@lem4616966 A GEN_PVAR_173 s n)). Qed.
Lemma lem4616969 {A : Type'} (s : A -> Prop) (n : nat) : (term505 A s n) = (term486 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_173 : A -> Prop => @lem4616968 A GEN_PVAR_173 s n)). Qed.
Lemma lem4616970 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4616971 {A : Type'} (s : A -> Prop) (n : nat) : (term506 A s n) = (term487 A s n).
Proof. exact (MK_COMB (@lem4616970 A) (@lem4616969 A s n)). Qed.
Lemma lem4616972 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4616973 {A : Type'} (s : A -> Prop) (n : nat) : (term507 A s n) = (term488 A s n).
Proof. exact (MK_COMB (@lem4616972 A) (@lem4616971 A s n)). Qed.
Lemma lem4616974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4616975 {A : Type'} (s : A -> Prop) (n : nat) : (term508 A s n) = (term509 A s n).
Proof. exact (MK_COMB (@lem4616974) (@lem4616973 A s n)). Qed.
Lemma lem4616976 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem4616977 {A : Type'} (s : A -> Prop) (n : nat) : ((term507 A s n) = True) = ((term488 A s n) = True).
Proof. exact (MK_COMB (@lem4616975 A s n) (@lem4616976)). Qed.
Lemma lem4616978 {A : Type'} (s : A -> Prop) : (term510 A s) = (term510 A s).
Proof. exact (eq_refl (term510 A s)). Qed.
Lemma lem4616979 {A : Type'} (s : A -> Prop) (n : nat) : (term499 A s n) = (term511 A s n).
Proof. exact (MK_COMB (@lem4616978 A s) (@lem4616977 A s n)). Qed.
Lemma lem4616980 {A : Type'} (s : A -> Prop) (n : nat) : term511 A s n.
Proof. exact (EQ_MP (@lem4616979 A s n) (@lem4616958 A s n)). Qed.
Lemma lem4616982 {A : Type'} (s : A -> Prop) : term512 A s.
Proof. exact (fun h0 : @FINITE A s => @lem4616919 A s h0). Qed.
Lemma lem4616983 {A : Type'} (s : A -> Prop) : term512 A s.
Proof. exact (@lem4616982 A s). Qed.
Lemma lem4616985 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4616953 A s) (@lem4615776 A s h1)). Qed.
Lemma lem4616986 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4616985 A s h1)). Qed.
Lemma lem4616987 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4616986 A s h1) (@lem0)). Qed.
Lemma lem4616988 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term491 A s) = True.
Proof. exact (@lem4616983 A s (@lem4616987 A s h1)). Qed.
Lemma lem4616989 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (term491 A s).
Proof. exact (SYM (@lem4616988 A s h1)). Qed.
Lemma lem4616990 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term491 A s.
Proof. exact (EQ_MP (@lem4616989 A s h1) (@lem0)). Qed.
Lemma lem4616991 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term488 A s n) = True.
Proof. exact (@lem4616980 A s n (@lem4616990 A s h1)). Qed.
Lemma lem4616992 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : True = (term488 A s n).
Proof. exact (SYM (@lem4616991 A n s h1)). Qed.
Lemma lem4616993 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : term488 A s n.
Proof. exact (EQ_MP (@lem4616992 A n s h1) (@lem0)). Qed.
Lemma lem4616994 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : term420 A s n.
Proof. exact (EQ_MP (@lem4616912 A s n) (@lem4616993 A n s h1)). Qed.
Lemma lem4616995 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : term420 A s n.
Proof. exact (h1). Qed.
Lemma lem4616996 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4617010 {A : Type'} (s : A -> Prop) : term440 A s.
Proof. exact (@lem82 (@FINITE A s)). Qed.
Lemma lem4617015 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4617016 {A : Type'} (s : A -> Prop) : (term513 A s) = (term262 A s).
Proof. exact (@lem4617015 (@FINITE A s)). Qed.
Lemma lem4617018 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (@FINITE A s) = False.
Proof. exact (@lem4617010 A s (@lem4615777 A s h1)). Qed.
Lemma lem4617019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4617020 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (term262 A s) = (~ False).
Proof. exact (MK_COMB (@lem4617019) (@lem4617018 A s h1)). Qed.
Lemma lem4617022 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4617023 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (term262 A s) = True.
Proof. exact (TRANS (@lem4617020 A s h1) (@lem4617022)). Qed.
Lemma lem4617024 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (term513 A s) = True.
Proof. exact (TRANS (@lem4617016 A s) (@lem4617023 A s h1)). Qed.
Lemma lem4617025 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : True = (term513 A s).
Proof. exact (SYM (@lem4617024 A s h1)). Qed.
Lemma lem4617026 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : term513 A s.
Proof. exact (EQ_MP (@lem4617025 A s h1) (@lem0)). Qed.
Lemma lem4617028 {A : Type'} (s : A -> Prop) : term213 A s.
Proof. exact (EQ_MP (@lem4615646 A s) (@lem4615645 A s)). Qed.
Lemma lem4617029 {A : Type'} (s : A -> Prop) : term213 A s.
Proof. exact (@lem4617028 A s). Qed.
Lemma lem4617053 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term514 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4617054 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term515 _88905 _89106 Q P.
Proof. exact (@lem4617053 _88905 _89106 Q P). Qed.
Lemma lem4617055 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term515 _88905 _89106 Q P) = (term516 _88905 _89106 P Q).
Proof. exact (eq_refl (term515 _88905 _89106 Q P)). Qed.
Lemma lem4617056 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term516 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem4617055 _88905 _89106 P Q) (@lem4617054 _88905 _89106 Q P)). Qed.
Lemma lem4617057 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term517 _88905 _89106 P Q f.
Proof. exact (@lem4617056 _88905 _89106 P Q f). Qed.
Lemma lem4617058 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term517 _88905 _89106 P Q f) = ((term518 _88905 _89106 P f Q) = (term519 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term517 _88905 _89106 P Q f)). Qed.
Lemma lem4617060 {A : Type'} (s : type686 A) : term520 A s.
Proof. exact (@lem4605902 A s). Qed.
Lemma lem4617061 {A : Type'} (s : type686 A) : (term520 A s) = ((term521 A s) = (term522 A s)).
Proof. exact (eq_refl (term520 A s)). Qed.
Lemma lem4617078 {A : Type'} (s : A -> Prop) (n : nat) : (term420 A s n) = ((term420 A s n) = True).
Proof. exact (@lem7 (term420 A s n)). Qed.
Lemma lem4617081 {A : Type'} (s : type686 A) : (term521 A s) = (term522 A s).
Proof. exact (EQ_MP (@lem4617061 A s) (@lem4617060 A s)). Qed.
Lemma lem4617082 {A : Type'} (s : type686 A) : (term521 A s) = (term522 A s).
Proof. exact (@lem4617081 A s). Qed.
Lemma lem4617083 {A : Type'} (s : A -> Prop) (n : nat) : (term523 A s n) = (term524 A s n).
Proof. exact (@lem4617082 A (term418 A s n)). Qed.
Lemma lem4617087 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term420 A s n) = True.
Proof. exact (EQ_MP (@lem4617078 A s n) (@lem4616995 A s n h1)). Qed.
Lemma lem4617088 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term420 A s n) = True.
Proof. exact (@lem4617087 A s n h1). Qed.
Lemma lem4617089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4617090 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term525 A s n) = (and True).
Proof. exact (MK_COMB (@lem4617089) (@lem4617088 A s n h1)). Qed.
Lemma lem4617092 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term518 _88905 _89106 P f Q) = (term519 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4617058 _88905 _89106 P Q f) (@lem4617057 _88905 _89106 P Q f)). Qed.
Lemma lem4617093 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term526 A P f Q) = (term527 A P Q f).
Proof. exact (@lem4617092 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem4617094 {A : Type'} (s : A -> Prop) (n : nat) : (term528 A s n) = (term529 A s n).
Proof. exact (@lem4617093 A (term530 A s n) (@FINITE A) (term531 A)). Qed.
Lemma lem4617095 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term532 A s n t) = (term406 A s t n).
Proof. exact (eq_refl (term532 A s n t)). Qed.
Lemma lem4617096 {A : Type'} (GEN_PVAR_170 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_170) = (@SETSPEC (A -> Prop) GEN_PVAR_170).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_170)). Qed.
Lemma lem4617097 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) : (term533 A GEN_PVAR_170 s n t) = (term408 A GEN_PVAR_170 s t n).
Proof. exact (MK_COMB (@lem4617096 A GEN_PVAR_170) (@lem4617095 A s t n)). Qed.
Lemma lem4617098 {A : Type'} (t : A -> Prop) : (term534 A t) = t.
Proof. exact (eq_refl (term534 A t)). Qed.
Lemma lem4617099 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (n : nat) (t : A -> Prop) : (term535 A GEN_PVAR_170 s n t) = (term410 A GEN_PVAR_170 s n t).
Proof. exact (MK_COMB (@lem4617097 A GEN_PVAR_170 s t n) (@lem4617098 A t)). Qed.
Lemma lem4617100 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (n : nat) : (term536 A GEN_PVAR_170 s n) = (term412 A GEN_PVAR_170 s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617099 A GEN_PVAR_170 s n t)). Qed.
Lemma lem4617101 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4617102 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (n : nat) : (term537 A GEN_PVAR_170 s n) = (term414 A GEN_PVAR_170 s n).
Proof. exact (MK_COMB (@lem4617101 A) (@lem4617100 A GEN_PVAR_170 s n)). Qed.
Lemma lem4617103 {A : Type'} (s : A -> Prop) (n : nat) : (term538 A s n) = (term416 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_170 : A -> Prop => @lem4617102 A GEN_PVAR_170 s n)). Qed.
Lemma lem4617104 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4617105 {A : Type'} (s : A -> Prop) (n : nat) : (term539 A s n) = (term418 A s n).
Proof. exact (MK_COMB (@lem4617104 A) (@lem4617103 A s n)). Qed.
Lemma lem4617106 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4617107 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term540 A t s n) = (term541 A t s n).
Proof. exact (MK_COMB (@lem4617106 A t) (@lem4617105 A s n)). Qed.
Lemma lem4617108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4617109 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term542 A t s n) = (term543 A t s n).
Proof. exact (MK_COMB (@lem4617108) (@lem4617107 A t s n)). Qed.
Lemma lem4617110 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem4617111 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) : (term544 A s n t) = (term545 A s n t).
Proof. exact (MK_COMB (@lem4617109 A t s n) (@lem4617110 A t)). Qed.
Lemma lem4617112 {A : Type'} (s : A -> Prop) (n : nat) : (term546 A s n) = (term547 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617111 A s n t)). Qed.
Lemma lem4617113 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4617114 {A : Type'} (s : A -> Prop) (n : nat) : (term528 A s n) = (term548 A s n).
Proof. exact (MK_COMB (@lem4617113 A) (@lem4617112 A s n)). Qed.
Lemma lem4617115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4617116 {A : Type'} (s : A -> Prop) (n : nat) : (term549 A s n) = (term550 A s n).
Proof. exact (MK_COMB (@lem4617115) (@lem4617114 A s n)). Qed.
Lemma lem4617117 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term532 A s n t) = (term406 A s t n).
Proof. exact (eq_refl (term532 A s n t)). Qed.
Lemma lem4617118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4617119 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term551 A s n t) = (term552 A s t n).
Proof. exact (MK_COMB (@lem4617118) (@lem4617117 A s t n)). Qed.
Lemma lem4617120 {A : Type'} (t : A -> Prop) : (term534 A t) = t.
Proof. exact (eq_refl (term534 A t)). Qed.
Lemma lem4617121 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4617122 {A : Type'} (t : A -> Prop) : (term553 A t) = (@FINITE A t).
Proof. exact (MK_COMB (@lem4617121 A) (@lem4617120 A t)). Qed.
Lemma lem4617123 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) : (term554 A s n t) = (term555 A s n t).
Proof. exact (MK_COMB (@lem4617119 A s t n) (@lem4617122 A t)). Qed.
Lemma lem4617124 {A : Type'} (s : A -> Prop) (n : nat) : (term556 A s n) = (term557 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617123 A s n t)). Qed.
Lemma lem4617125 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4617126 {A : Type'} (s : A -> Prop) (n : nat) : (term529 A s n) = (term558 A s n).
Proof. exact (MK_COMB (@lem4617125 A) (@lem4617124 A s n)). Qed.
Lemma lem4617127 {A : Type'} (s : A -> Prop) (n : nat) : ((term528 A s n) = (term529 A s n)) = ((term548 A s n) = (term558 A s n)).
Proof. exact (MK_COMB (@lem4617116 A s n) (@lem4617126 A s n)). Qed.
Lemma lem4617128 {A : Type'} (s : A -> Prop) (n : nat) : (term548 A s n) = (term558 A s n).
Proof. exact (EQ_MP (@lem4617127 A s n) (@lem4617094 A s n)). Qed.
Lemma lem4617164 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term524 A s n) = (term559 A s n).
Proof. exact (MK_COMB (@lem4617090 A s n h1) (@lem4617128 A s n)). Qed.
Lemma lem4617166 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4617167 {A : Type'} (s : A -> Prop) (n : nat) : (term559 A s n) = (term558 A s n).
Proof. exact (@lem4617166 (term558 A s n)). Qed.
Lemma lem4617203 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term524 A s n) = (term558 A s n).
Proof. exact (TRANS (@lem4617164 A s n h1) (@lem4617167 A s n)). Qed.
Lemma lem4617204 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term523 A s n) = (term558 A s n).
Proof. exact (TRANS (@lem4617083 A s n) (@lem4617203 A s n h1)). Qed.
Lemma lem4617205 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : (term558 A s n) = (term523 A s n).
Proof. exact (SYM (@lem4617204 A s n h1)). Qed.
Lemma lem4617213 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term560 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4617214 (p : Prop) (q : Prop) (p' : Prop) : term561 p q p'.
Proof. exact (fun q' : Prop => @lem4617213 p q p' q'). Qed.
Lemma lem4617215 (p : Prop) (q : Prop) : term562 p q.
Proof. exact (fun p' : Prop => @lem4617214 p q p'). Qed.
Lemma lem4617216 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) : term563 A s n t.
Proof. exact (@lem4617215 (term406 A s t n) (@FINITE A t)). Qed.
Lemma lem4617217 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) (p' : Prop) : term564 A s n t p'.
Proof. exact (@lem4617216 A s n t p'). Qed.
Lemma lem4617218 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) (p' : Prop) : (term564 A s n t p') = (term565 A s n t p').
Proof. exact (eq_refl (term564 A s n t p')). Qed.
Lemma lem4617219 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) (p' : Prop) : term565 A s n t p'.
Proof. exact (EQ_MP (@lem4617218 A s n t p') (@lem4617217 A s n t p')). Qed.
Lemma lem4617220 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) (p' : Prop) (q' : Prop) : term566 A s n t p' q'.
Proof. exact (@lem4617219 A s n t p' q'). Qed.
Lemma lem4617221 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) (p' : Prop) (q' : Prop) : (term566 A s n t p' q') = (term567 A s n t p' q').
Proof. exact (eq_refl (term566 A s n t p' q')). Qed.
Lemma lem4617222 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) (p' : Prop) (q' : Prop) : term567 A s n t p' q'.
Proof. exact (EQ_MP (@lem4617221 A s n t p' q') (@lem4617220 A s n t p' q')). Qed.
Lemma lem4617226 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term203 _100044 s n).
Proof. exact (EQ_MP (@lem4615625 _100044 s n) (@lem4615624 _100044 s n)). Qed.
Lemma lem4617227 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term203 A s n).
Proof. exact (@lem4617226 A s n). Qed.
Lemma lem4617228 {A : Type'} (t : A -> Prop) (n : nat) : (@HAS_SIZE A t n) = (term203 A t n).
Proof. exact (@lem4617227 A t n). Qed.
Lemma lem4617233 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term268 A t s) = (term268 A t s).
Proof. exact (eq_refl (term268 A t s)). Qed.
Lemma lem4617234 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term406 A s t n) = (term568 A s t n).
Proof. exact (MK_COMB (@lem4617233 A t s) (@lem4617228 A t n)). Qed.
Lemma lem4617241 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (q' : Prop) : term569 A s t n q'.
Proof. exact (@lem4617222 A s n t (term568 A s t n) q'). Qed.
Lemma lem4617242 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (q' : Prop) : term570 A s t n q'.
Proof. exact (@lem4617241 A s t n q' (@lem4617234 A s t n)). Qed.
Lemma lem4617243 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term568 A s t n) : term568 A s t n.
Proof. exact (h1). Qed.
Lemma lem4617244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term568 A s t n) : term203 A t n.
Proof. exact (proj2 (@lem4617243 A s t n h1)). Qed.
Lemma lem4617246 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term568 A s t n) : @FINITE A t.
Proof. exact (proj1 (@lem4617244 A s t n h1)). Qed.
Lemma lem4617247 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem4617253 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term568 A s t n) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem4617247 A t) (@lem4617246 A s t n h1)). Qed.
Lemma lem4617254 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) : term571 A s n t.
Proof. exact (fun h0 : term568 A s t n => @lem4617253 A s t n h0). Qed.
Lemma lem4617255 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : term572 A s t n.
Proof. exact (@lem4617242 A s t n True). Qed.
Lemma lem4617256 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term555 A s n t) = (term573 A s t n).
Proof. exact (@lem4617255 A s t n (@lem4617254 A s n t)). Qed.
Lemma lem4617258 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4617259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term573 A s t n) = True.
Proof. exact (@lem4617258 (term568 A s t n)). Qed.
Lemma lem4617260 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) : (term555 A s n t) = True.
Proof. exact (TRANS (@lem4617256 A s t n) (@lem4617259 A s t n)). Qed.
Lemma lem4617261 {A : Type'} (s : A -> Prop) (n : nat) : (term557 A s n) = (term99 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617260 A s n t)). Qed.
Lemma lem4617262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4617263 {A : Type'} (s : A -> Prop) (n : nat) : (term558 A s n) = (term100 A).
Proof. exact (MK_COMB (@lem4617262 A) (@lem4617261 A s n)). Qed.
Lemma lem4617265 {A : Type'} (t : Prop) : (term97 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4617266 {A : Type'} (t : Prop) : (term101 A t) = t.
Proof. exact (@lem4617265 (A -> Prop) t). Qed.
Lemma lem4617267 {A : Type'} : (term100 A) = True.
Proof. exact (@lem4617266 A True). Qed.
Lemma lem4617268 {A : Type'} (s : A -> Prop) (n : nat) : (term558 A s n) = True.
Proof. exact (TRANS (@lem4617263 A s n) (@lem4617267 A)). Qed.
Lemma lem4617269 {A : Type'} (s : A -> Prop) (n : nat) : True = (term558 A s n).
Proof. exact (SYM (@lem4617268 A s n)). Qed.
Lemma lem4617270 {A : Type'} (s : A -> Prop) (n : nat) : term558 A s n.
Proof. exact (EQ_MP (@lem4617269 A s n) (@lem0)). Qed.
Lemma lem4617271 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) : term523 A s n.
Proof. exact (EQ_MP (@lem4617205 A s n h1) (@lem4617270 A s n)). Qed.
Lemma lem4617273 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (EQ_MP (@lem4615619 A s t) (@lem4615618 A s t)). Qed.
Lemma lem4617274 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (@lem4617273 A s t). Qed.
Lemma lem4617275 {A : Type'} (s : A -> Prop) (n : nat) : (term574 A s n) = (term575 A s n).
Proof. exact (@lem4617274 A s (term576 A s n)). Qed.
Lemma lem4617276 {A : Type'} (s : A -> Prop) (n : nat) : (term575 A s n) = (term574 A s n).
Proof. exact (SYM (@lem4617275 A s n)). Qed.
Lemma lem4617277 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4617279 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term195 _89520 _89534 P f) = (term196 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem4615613 _89520 _89534 P f) (@lem4615612 _89520 _89534 P f)). Qed.
Lemma lem4617280 {A : Type'} (P : type686 A) (f : type672 A) : (term577 A P f) = (term578 A P f).
Proof. exact (@lem4617279 A (A -> Prop) P f). Qed.
Lemma lem4617281 {A : Type'} (s : A -> Prop) (n : nat) : (term579 A s n) = (term580 A s n).
Proof. exact (@lem4617280 A (term530 A s n) (term531 A)). Qed.
Lemma lem4617282 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term532 A s n t) = (term406 A s t n).
Proof. exact (eq_refl (term532 A s n t)). Qed.
Lemma lem4617283 {A : Type'} (GEN_PVAR_170 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_170) = (@SETSPEC (A -> Prop) GEN_PVAR_170).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_170)). Qed.
Lemma lem4617284 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (n : nat) : (term533 A GEN_PVAR_170 s n t) = (term408 A GEN_PVAR_170 s t n).
Proof. exact (MK_COMB (@lem4617283 A GEN_PVAR_170) (@lem4617282 A s t n)). Qed.
Lemma lem4617285 {A : Type'} (t : A -> Prop) : (term534 A t) = t.
Proof. exact (eq_refl (term534 A t)). Qed.
Lemma lem4617286 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (n : nat) (t : A -> Prop) : (term535 A GEN_PVAR_170 s n t) = (term410 A GEN_PVAR_170 s n t).
Proof. exact (MK_COMB (@lem4617284 A GEN_PVAR_170 s t n) (@lem4617285 A t)). Qed.
Lemma lem4617287 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (n : nat) : (term536 A GEN_PVAR_170 s n) = (term412 A GEN_PVAR_170 s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617286 A GEN_PVAR_170 s n t)). Qed.
Lemma lem4617288 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4617289 {A : Type'} (GEN_PVAR_170 : A -> Prop) (s : A -> Prop) (n : nat) : (term537 A GEN_PVAR_170 s n) = (term414 A GEN_PVAR_170 s n).
Proof. exact (MK_COMB (@lem4617288 A) (@lem4617287 A GEN_PVAR_170 s n)). Qed.
Lemma lem4617290 {A : Type'} (s : A -> Prop) (n : nat) : (term538 A s n) = (term416 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_170 : A -> Prop => @lem4617289 A GEN_PVAR_170 s n)). Qed.
Lemma lem4617291 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4617292 {A : Type'} (s : A -> Prop) (n : nat) : (term539 A s n) = (term418 A s n).
Proof. exact (MK_COMB (@lem4617291 A) (@lem4617290 A s n)). Qed.
Lemma lem4617293 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4617294 {A : Type'} (s : A -> Prop) (n : nat) : (term579 A s n) = (term576 A s n).
Proof. exact (MK_COMB (@lem4617293 A) (@lem4617292 A s n)). Qed.
Lemma lem4617295 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4617296 {A : Type'} (s : A -> Prop) (n : nat) : (term581 A s n) = (term582 A s n).
Proof. exact (MK_COMB (@lem4617295 A) (@lem4617294 A s n)). Qed.
Lemma lem4617297 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term532 A s n t) = (term406 A s t n).
Proof. exact (eq_refl (term532 A s n t)). Qed.
Lemma lem4617298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4617299 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term583 A s n t) = (term584 A s t n).
Proof. exact (MK_COMB (@lem4617298) (@lem4617297 A s t n)). Qed.
Lemma lem4617300 {A : Type'} (t : A -> Prop) : (term534 A t) = t.
Proof. exact (eq_refl (term534 A t)). Qed.
Lemma lem4617301 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem4617302 {A : Type'} (a : A) (t : A -> Prop) : (term585 A a t) = (@IN A a t).
Proof. exact (MK_COMB (@lem4617301 A a) (@lem4617300 A t)). Qed.
Lemma lem4617303 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (t : A -> Prop) : (term586 A s n a t) = (term587 A s n a t).
Proof. exact (MK_COMB (@lem4617299 A s t n) (@lem4617302 A a t)). Qed.
Lemma lem4617304 {A : Type'} (s : A -> Prop) (n : nat) (a : A) : (term588 A s n a) = (term589 A s n a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617303 A s n a t)). Qed.
Lemma lem4617305 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4617306 {A : Type'} (s : A -> Prop) (n : nat) (a : A) : (term590 A s n a) = (term591 A s n a).
Proof. exact (MK_COMB (@lem4617305 A) (@lem4617304 A s n a)). Qed.
Lemma lem4617307 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem4617308 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) (a : A) : (term592 A GEN_PVAR_50 s n a) = (term593 A GEN_PVAR_50 s n a).
Proof. exact (MK_COMB (@lem4617307 A GEN_PVAR_50) (@lem4617306 A s n a)). Qed.
Lemma lem4617309 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4617310 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) (a : A) : (term594 A GEN_PVAR_50 s n a) = (term595 A GEN_PVAR_50 s n a).
Proof. exact (MK_COMB (@lem4617308 A GEN_PVAR_50 s n a) (@lem4617309 A a)). Qed.
Lemma lem4617311 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) : (term596 A GEN_PVAR_50 s n) = (term597 A GEN_PVAR_50 s n).
Proof. exact (fun_ext (fun a : A => @lem4617310 A GEN_PVAR_50 s n a)). Qed.
Lemma lem4617312 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4617313 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) : (term598 A GEN_PVAR_50 s n) = (term599 A GEN_PVAR_50 s n).
Proof. exact (MK_COMB (@lem4617312 A) (@lem4617311 A GEN_PVAR_50 s n)). Qed.
Lemma lem4617314 {A : Type'} (s : A -> Prop) (n : nat) : (term600 A s n) = (term601 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem4617313 A GEN_PVAR_50 s n)). Qed.
Lemma lem4617315 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4617316 {A : Type'} (s : A -> Prop) (n : nat) : (term580 A s n) = (term602 A s n).
Proof. exact (MK_COMB (@lem4617315 A) (@lem4617314 A s n)). Qed.
Lemma lem4617317 {A : Type'} (s : A -> Prop) (n : nat) : ((term579 A s n) = (term580 A s n)) = ((term576 A s n) = (term602 A s n)).
Proof. exact (MK_COMB (@lem4617296 A s n) (@lem4617316 A s n)). Qed.
Lemma lem4617318 {A : Type'} (s : A -> Prop) (n : nat) : (term576 A s n) = (term602 A s n).
Proof. exact (EQ_MP (@lem4617317 A s n) (@lem4617281 A s n)). Qed.
Lemma lem4617331 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4617332 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : (term603 A x s n) = (term604 A x s n).
Proof. exact (MK_COMB (@lem4617331 A x) (@lem4617318 A s n)). Qed.
Lemma lem4617334 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term190 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4615584 _83095 p x) (@lem4615583 _83095 p x)). Qed.
Lemma lem4617335 {A : Type'} (p : A -> Prop) (x : A) : (term190 A x p) = (p x).
Proof. exact (@lem4617334 A p x). Qed.
Lemma lem4617336 {A : Type'} (s : A -> Prop) (n : nat) (x : A) : (term605 A x s n) = (term606 A s n x).
Proof. exact (@lem4617335 A (term607 A s n) x). Qed.
Lemma lem4617337 {A : Type'} (s : A -> Prop) (n : nat) (a : A) : (term606 A s n a) = (term591 A s n a).
Proof. exact (eq_refl (term606 A s n a)). Qed.
Lemma lem4617338 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem4617339 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) (a : A) : (term608 A GEN_PVAR_50 s n a) = (term593 A GEN_PVAR_50 s n a).
Proof. exact (MK_COMB (@lem4617338 A GEN_PVAR_50) (@lem4617337 A s n a)). Qed.
Lemma lem4617340 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4617341 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) (a : A) : (term609 A GEN_PVAR_50 s n a) = (term595 A GEN_PVAR_50 s n a).
Proof. exact (MK_COMB (@lem4617339 A GEN_PVAR_50 s n a) (@lem4617340 A a)). Qed.
Lemma lem4617342 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) : (term610 A GEN_PVAR_50 s n) = (term597 A GEN_PVAR_50 s n).
Proof. exact (fun_ext (fun a : A => @lem4617341 A GEN_PVAR_50 s n a)). Qed.
Lemma lem4617343 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4617344 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (n : nat) : (term611 A GEN_PVAR_50 s n) = (term599 A GEN_PVAR_50 s n).
Proof. exact (MK_COMB (@lem4617343 A) (@lem4617342 A GEN_PVAR_50 s n)). Qed.
Lemma lem4617345 {A : Type'} (s : A -> Prop) (n : nat) : (term612 A s n) = (term601 A s n).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem4617344 A GEN_PVAR_50 s n)). Qed.
Lemma lem4617346 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4617347 {A : Type'} (s : A -> Prop) (n : nat) : (term613 A s n) = (term602 A s n).
Proof. exact (MK_COMB (@lem4617346 A) (@lem4617345 A s n)). Qed.
Lemma lem4617348 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4617349 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : (term605 A x s n) = (term604 A x s n).
Proof. exact (MK_COMB (@lem4617348 A x) (@lem4617347 A s n)). Qed.
Lemma lem4617350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4617351 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : (term614 A x s n) = (term615 A x s n).
Proof. exact (MK_COMB (@lem4617350) (@lem4617349 A x s n)). Qed.
Lemma lem4617352 {A : Type'} (s : A -> Prop) (n : nat) (x : A) : (term606 A s n x) = (term591 A s n x).
Proof. exact (eq_refl (term606 A s n x)). Qed.
Lemma lem4617353 {A : Type'} (s : A -> Prop) (n : nat) (x : A) : ((term605 A x s n) = (term606 A s n x)) = ((term604 A x s n) = (term591 A s n x)).
Proof. exact (MK_COMB (@lem4617351 A x s n) (@lem4617352 A s n x)). Qed.
Lemma lem4617354 {A : Type'} (s : A -> Prop) (n : nat) (x : A) : (term604 A x s n) = (term591 A s n x).
Proof. exact (EQ_MP (@lem4617353 A s n x) (@lem4617336 A s n x)). Qed.
Lemma lem4617363 {A : Type'} (s : A -> Prop) (n : nat) (x : A) : (term603 A x s n) = (term591 A s n x).
Proof. exact (TRANS (@lem4617332 A x s n) (@lem4617354 A s n x)). Qed.
Lemma lem4617364 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : (term591 A s n x) = (term603 A x s n).
Proof. exact (SYM (@lem4617363 A s n x)). Qed.
Lemma lem4617370 {_108414 : Type'} (x : _108414) (t : _108414 -> Prop) (P : Prop) : (term25 _108414 P x t) = (term22 _108414 x t P).
Proof. exact (EQ_MP (@lem4614758 _108414 x t P) (@lem4615553 _108414 x t P)). Qed.
Lemma lem4617371 {A : Type'} (x : A) (t : A -> Prop) (P : Prop) : (term25 A P x t) = (term22 A x t P).
Proof. exact (@lem4617370 A x t P). Qed.
Lemma lem4617372 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (n : nat) : (term587 A s n x t) = (term616 A x s t n).
Proof. exact (@lem4617371 A x t (term406 A s t n)). Qed.
Lemma lem4617373 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : (term589 A s n x) = (term617 A x s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4617372 A x s t n)). Qed.
Lemma lem4617374 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4617375 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : (term591 A s n x) = (term618 A x s n).
Proof. exact (MK_COMB (@lem4617374 A) (@lem4617373 A x s n)). Qed.
Lemma lem4617376 {A : Type'} (s : A -> Prop) (n : nat) (x : A) : (term618 A x s n) = (term591 A s n x).
Proof. exact (SYM (@lem4617375 A x s n)). Qed.
Lemma lem4617378 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) : term6 A s u n.
Proof. exact (EQ_MP (@lem4614716 A s u n) (@lem4614715 A s u n)). Qed.
Lemma lem4617379 {A : Type'} (s : A -> Prop) (u : A -> Prop) (n : nat) : term6 A s u n.
Proof. exact (@lem4617378 A s u n). Qed.
Lemma lem4617380 {A : Type'} (x : A) (s : A -> Prop) (n : nat) : term619 A x s n.
Proof. exact (@lem4617379 A (@INSERT A x (@EMPTY A)) s n). Qed.
Lemma lem4617381 {A : Type'} (a : A) : term620 A a.
Proof. exact (@lem3855272 A a). Qed.
Lemma lem4617382 {A : Type'} (a : A) : (term620 A a) = ((term621 A a) = term622).
Proof. exact (eq_refl (term620 A a)). Qed.
Lemma lem4617384 {_92373 : Type'} (a : _92373) : term263 _92373 a.
Proof. exact (@lem3608356 _92373 a). Qed.
Lemma lem4617385 {_92373 : Type'} (a : _92373) : (term263 _92373 a) = (term264 _92373 a).
Proof. exact (eq_refl (term263 _92373 a)). Qed.
Lemma lem4617386 {_92373 : Type'} (a : _92373) : term264 _92373 a.
Proof. exact (EQ_MP (@lem4617385 _92373 a) (@lem4617384 _92373 a)). Qed.
Lemma lem4617387 {_92373 : Type'} (a : _92373) : (term264 _92373 a) = ((term264 _92373 a) = True).
Proof. exact (@lem7 (term264 _92373 a)). Qed.
Lemma lem4617389 {_84443 : Type'} (s : _84443 -> Prop) : term623 _84443 s.
Proof. exact (@lem3221020 _84443 s). Qed.
Lemma lem4617390 {_84443 : Type'} (s : _84443 -> Prop) : (term623 _84443 s) = (term624 _84443 s).
Proof. exact (eq_refl (term623 _84443 s)). Qed.
Lemma lem4617391 {_84443 : Type'} (s : _84443 -> Prop) : term624 _84443 s.
Proof. exact (EQ_MP (@lem4617390 _84443 s) (@lem4617389 _84443 s)). Qed.
Lemma lem4617392 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : term625 _84443 s x.
Proof. exact (@lem4617391 _84443 s x). Qed.
Lemma lem4617393 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term625 _84443 s x) = ((term18 _84443 x s) = (@IN _84443 x s)).
Proof. exact (eq_refl (term625 _84443 s x)). Qed.
Lemma lem4617408 {A : Type'} (s : A -> Prop) : term440 A s.
Proof. exact (@lem82 (@FINITE A s)). Qed.
Lemma lem4617412 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4617417 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term18 _84443 x s) = (@IN _84443 x s).
Proof. exact (EQ_MP (@lem4617393 _84443 x s) (@lem4617392 _84443 s x)). Qed.
Lemma lem4617418 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = (@IN A x s).
Proof. exact (@lem4617417 A x s). Qed.
Lemma lem4617420 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4617412 A x s) (@lem4617277 A x s h1)). Qed.
Lemma lem4617421 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term18 A x s) = True.
Proof. exact (TRANS (@lem4617418 A x s) (@lem4617420 A x s h1)). Qed.
Lemma lem4617422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4617423 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term20 A x s) = (and True).
Proof. exact (MK_COMB (@lem4617422) (@lem4617421 A x s h1)). Qed.
Lemma lem4617427 {_92373 : Type'} (a : _92373) : (term264 _92373 a) = True.
Proof. exact (EQ_MP (@lem4617387 _92373 a) (@lem4617386 _92373 a)). Qed.
Lemma lem4617428 {A : Type'} (a : A) : (term264 A a) = True.
Proof. exact (@lem4617427 A a). Qed.
Lemma lem4617429 {A : Type'} (x : A) : (term264 A x) = True.
Proof. exact (@lem4617428 A x). Qed.
Lemma lem4617430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4617431 {A : Type'} (x : A) : (term626 A x) = (and True).
Proof. exact (MK_COMB (@lem4617430) (@lem4617429 A x)). Qed.
Lemma lem4617435 {A : Type'} (a : A) : (term621 A a) = term622.
Proof. exact (EQ_MP (@lem4617382 A a) (@lem4617381 A a)). Qed.
Lemma lem4617436 {A : Type'} (a : A) : (term621 A a) = term622.
Proof. exact (@lem4617435 A a). Qed.
Lemma lem4617437 {A : Type'} (x : A) : (term621 A x) = term622.
Proof. exact (@lem4617436 A x). Qed.
Lemma lem4617438 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4617439 {A : Type'} (x : A) : (term627 A x) = term628.
Proof. exact (MK_COMB (@lem4617438) (@lem4617437 A x)). Qed.
Lemma lem4617440 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4617441 {A : Type'} (x : A) (n : nat) : (term629 A x n) = (term630 n).
Proof. exact (MK_COMB (@lem4617439 A x) (@lem4617440 n)). Qed.
Lemma lem4617442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4617443 {A : Type'} (x : A) (n : nat) : (term631 A x n) = (term632 n).
Proof. exact (MK_COMB (@lem4617442) (@lem4617441 A x n)). Qed.
Lemma lem4617447 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (@FINITE A s) = False.
Proof. exact (@lem4617408 A s (@lem4615777 A s h1)). Qed.
Lemma lem4617448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4617449 {A : Type'} (s : A -> Prop) (h1 : term262 A s) : (term633 A s) = (imp False).
Proof. exact (MK_COMB (@lem4617448) (@lem4617447 A s h1)). Qed.
Lemma lem4617450 {A : Type'} (n : nat) (s : A -> Prop) : (term634 A n s) = (term634 A n s).
Proof. exact (eq_refl (term634 A n s)). Qed.
Lemma lem4617451 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term635 A n s) = (term636 A n s).
Proof. exact (MK_COMB (@lem4617449 A s h1) (@lem4617450 A n s)). Qed.
Lemma lem4617453 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4617454 {A : Type'} (n : nat) (s : A -> Prop) : (term636 A n s) = True.
Proof. exact (@lem4617453 (term634 A n s)). Qed.
Lemma lem4617455 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term635 A n s) = True.
Proof. exact (TRANS (@lem4617451 A n s h1) (@lem4617454 A n s)). Qed.
Lemma lem4617456 {A : Type'} (x : A) (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term637 A x n s) = (term638 n).
Proof. exact (MK_COMB (@lem4617443 A x n) (@lem4617455 A n s h1)). Qed.
Lemma lem4617458 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4617459 (n : nat) : (term638 n) = (term630 n).
Proof. exact (@lem4617458 (term630 n)). Qed.
Lemma lem4617460 {A : Type'} (x : A) (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term637 A x n s) = (term630 n).
Proof. exact (TRANS (@lem4617456 A x n s h1) (@lem4617459 n)). Qed.
Lemma lem4617461 {A : Type'} (x : A) (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term639 A x n s) = (term640 n).
Proof. exact (MK_COMB (@lem4617431 A x) (@lem4617460 A x n s h1)). Qed.
Lemma lem4617463 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4617464 (n : nat) : (term640 n) = (term630 n).
Proof. exact (@lem4617463 (term630 n)). Qed.
Lemma lem4617465 {A : Type'} (x : A) (n : nat) (s : A -> Prop) (h1 : term262 A s) : (term639 A x n s) = (term630 n).
Proof. exact (TRANS (@lem4617461 A x n s h1) (@lem4617464 n)). Qed.
Lemma lem4617466 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : @IN A x s) : (term641 A x n s) = (term640 n).
Proof. exact (MK_COMB (@lem4617423 A x s h2) (@lem4617465 A x n s h1)). Qed.
Lemma lem4617468 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4617469 (n : nat) : (term640 n) = (term630 n).
Proof. exact (@lem4617468 (term630 n)). Qed.
Lemma lem4617470 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : @IN A x s) : (term641 A x n s) = (term630 n).
Proof. exact (TRANS (@lem4617466 A n x s h1 h2) (@lem4617469 n)). Qed.
Lemma lem4617471 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : @IN A x s) : (term630 n) = (term641 A x n s).
Proof. exact (SYM (@lem4617470 A n x s h1 h2)). Qed.
Lemma lem4617472 : term642.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem4617473 : term643.
Proof. exact (proj2 (@lem4617472)). Qed.
Lemma lem4617474 : term644.
Proof. exact (proj2 (@lem4617473)). Qed.
Lemma lem4617475 : term645.
Proof. exact (proj2 (@lem4617474)). Qed.
Lemma lem4617505 : term646.
Proof. exact (proj1 (@lem4617475)). Qed.
Lemma lem4617506 (n : nat) : term647 n.
Proof. exact (@lem4617505 n). Qed.
Lemma lem4617507 (n : nat) : (term647 n) = (term648 n).
Proof. exact (eq_refl (term647 n)). Qed.
Lemma lem4617508 (n : nat) : term648 n.
Proof. exact (EQ_MP (@lem4617507 n) (@lem4617506 n)). Qed.
Lemma lem4617509 (n : nat) (h1 : term630 n) : term630 n.
Proof. exact (h1). Qed.
Lemma lem4617510 (n : nat) (h1 : term630 n) : term649 n.
Proof. exact (@lem4617508 n (@lem4617509 n h1)). Qed.
Lemma lem4617511 (n : nat) : (term649 n) = ((term649 n) = True).
Proof. exact (@lem7 (term649 n)). Qed.
Lemma lem4617512 (n : nat) (h1 : term630 n) : (term649 n) = True.
Proof. exact (EQ_MP (@lem4617511 n) (@lem4617510 n h1)). Qed.
Lemma lem4617518 : term650.
Proof. exact (proj1 (@lem4617474)). Qed.
Lemma lem4617519 (n : nat) : term651 n.
Proof. exact (@lem4617518 n). Qed.
Lemma lem4617520 (n : nat) : (term651 n) = (term652 n).
Proof. exact (eq_refl (term651 n)). Qed.
Lemma lem4617521 (n : nat) : term652 n.
Proof. exact (EQ_MP (@lem4617520 n) (@lem4617519 n)). Qed.
Lemma lem4617522 (n : nat) (h1 : term649 n) : term649 n.
Proof. exact (h1). Qed.
Lemma lem4617523 (n : nat) (h1 : term649 n) : term630 n.
Proof. exact (@lem4617521 n (@lem4617522 n h1)). Qed.
Lemma lem4617524 (n : nat) : (term630 n) = ((term630 n) = True).
Proof. exact (@lem7 (term630 n)). Qed.
Lemma lem4617525 (n : nat) (h1 : term649 n) : (term630 n) = True.
Proof. exact (EQ_MP (@lem4617524 n) (@lem4617523 n h1)). Qed.
Lemma lem4617560 : term653.
Proof. exact (proj1 (@lem4617472)). Qed.
Lemma lem4617561 (n : nat) : term654 n.
Proof. exact (@lem4617560 n). Qed.
Lemma lem4617562 (n : nat) : (term654 n) = (term655 n).
Proof. exact (eq_refl (term654 n)). Qed.
Lemma lem4617563 (n : nat) : term655 n.
Proof. exact (EQ_MP (@lem4617562 n) (@lem4617561 n)). Qed.
Lemma lem4617564 (n : nat) (h1 : term405 n) : term405 n.
Proof. exact (h1). Qed.
Lemma lem4617565 (n : nat) (h1 : term405 n) : term630 n.
Proof. exact (@lem4617563 n (@lem4617564 n h1)). Qed.
Lemma lem4617566 (n : nat) : (term630 n) = ((term630 n) = True).
Proof. exact (@lem7 (term630 n)). Qed.
Lemma lem4617567 (n : nat) (h1 : term405 n) : (term630 n) = True.
Proof. exact (EQ_MP (@lem4617566 n) (@lem4617565 n h1)). Qed.
Lemma lem4617586 (n : nat) : term428 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem4617606 (n : nat) : term656 n.
Proof. exact (fun h0 : term649 n => @lem4617525 n h0). Qed.
Lemma lem4617608 (n : nat) : term657 n.
Proof. exact (fun h0 : term630 n => @lem4617512 n h0). Qed.
Lemma lem4617618 (n : nat) : term658 n.
Proof. exact (fun h0 : term405 n => @lem4617567 n h0). Qed.
Lemma lem4617620 (n : nat) (h1 : term405 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem4617586 n (@lem4616627 n h1)). Qed.
Lemma lem4617621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4617622 (n : nat) (h1 : term405 n) : (term405 n) = (~ False).
Proof. exact (MK_COMB (@lem4617621) (@lem4617620 n h1)). Qed.
Lemma lem4617624 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4617625 (n : nat) (h1 : term405 n) : (term405 n) = True.
Proof. exact (TRANS (@lem4617622 n h1) (@lem4617624)). Qed.
Lemma lem4617626 (n : nat) (h1 : term405 n) : True = (term405 n).
Proof. exact (SYM (@lem4617625 n h1)). Qed.
Lemma lem4617627 (n : nat) (h1 : term405 n) : term405 n.
Proof. exact (EQ_MP (@lem4617626 n h1) (@lem0)). Qed.
Lemma lem4617628 (n : nat) (h1 : term405 n) : (term630 n) = True.
Proof. exact (@lem4617618 n (@lem4617627 n h1)). Qed.
Lemma lem4617629 (n : nat) (h1 : term405 n) : True = (term630 n).
Proof. exact (SYM (@lem4617628 n h1)). Qed.
Lemma lem4617630 (n : nat) (h1 : term405 n) : term630 n.
Proof. exact (EQ_MP (@lem4617629 n h1) (@lem0)). Qed.
Lemma lem4617631 (n : nat) (h1 : term405 n) : (term649 n) = True.
Proof. exact (@lem4617608 n (@lem4617630 n h1)). Qed.
Lemma lem4617632 (n : nat) (h1 : term405 n) : True = (term649 n).
Proof. exact (SYM (@lem4617631 n h1)). Qed.
Lemma lem4617633 (n : nat) (h1 : term405 n) : term649 n.
Proof. exact (EQ_MP (@lem4617632 n h1) (@lem0)). Qed.
Lemma lem4617634 (n : nat) (h1 : term405 n) : (term630 n) = True.
Proof. exact (@lem4617606 n (@lem4617633 n h1)). Qed.
Lemma lem4617635 (n : nat) (h1 : term405 n) : True = (term630 n).
Proof. exact (SYM (@lem4617634 n h1)). Qed.
Lemma lem4617636 (n : nat) (h1 : term405 n) : term630 n.
Proof. exact (EQ_MP (@lem4617635 n h1) (@lem0)). Qed.
Lemma lem4617637 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : term405 n) (h3 : @IN A x s) : term641 A x n s.
Proof. exact (EQ_MP (@lem4617471 A n x s h1 h3) (@lem4617636 n h2)). Qed.
Lemma lem4617638 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : term405 n) (h3 : @IN A x s) : term618 A x s n.
Proof. exact (@lem4617380 A x s n (@lem4617637 A n x s h1 h2 h3)). Qed.
Lemma lem4617639 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : term405 n) (h3 : @IN A x s) : term591 A s n x.
Proof. exact (EQ_MP (@lem4617376 A s n x) (@lem4617638 A n x s h1 h2 h3)). Qed.
Lemma lem4617640 {A : Type'} (n : nat) (x : A) (s : A -> Prop) (h1 : term262 A s) (h2 : term405 n) (h3 : @IN A x s) : term603 A x s n.
Proof. exact (EQ_MP (@lem4617364 A x s n) (@lem4617639 A n x s h1 h2 h3)). Qed.
Lemma lem4617641 {A : Type'} (x : A) (s : A -> Prop) (n : nat) (h1 : term262 A s) (h2 : term405 n) : term659 A x s n.
Proof. exact (fun h0 : @IN A x s => @lem4617640 A n x s h1 h2 h0). Qed.
Lemma lem4617646 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term262 A s) (h2 : term405 n) : term575 A s n.
Proof. exact (fun x : A => @lem4617641 A x s n h1 h2). Qed.
Lemma lem4617647 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term262 A s) (h2 : term405 n) : term574 A s n.
Proof. exact (EQ_MP (@lem4617276 A s n) (@lem4617646 A s n h1 h2)). Qed.
Lemma lem4617648 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) (h2 : term262 A s) (h3 : term405 n) : term660 A s n.
Proof. exact (conj (@lem4617271 A s n h1) (@lem4617647 A s n h2 h3)). Qed.
Lemma lem4617649 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) (h2 : term262 A s) (h3 : term405 n) : term211 A s.
Proof. exact (ex_intro (term212 A s) (term576 A s n) (@lem4617648 A s n h1 h2 h3)). Qed.
Lemma lem4617650 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) (h2 : term262 A s) (h3 : term405 n) : @FINITE A s.
Proof. exact (@lem4617029 A s (@lem4617649 A s n h1 h2 h3)). Qed.
Lemma lem4617651 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term262 A s) : False.
Proof. exact (@lem4617026 A s h2 (@lem4616996 A s h1)). Qed.
Lemma lem4617652 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) (h2 : term262 A s) (h3 : term405 n) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4617651 A s h4 h2) (fun h4 : False => @lem4617650 A s n h1 h2 h3)). Qed.
Lemma lem4617653 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term420 A s n) (h2 : term262 A s) (h3 : term405 n) : False.
Proof. exact (EQ_MP (@lem4617652 A s n h1 h2 h3) (@lem4617650 A s n h1 h2 h3)). Qed.
Lemma lem4617654 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term262 A s) (h2 : term405 n) : term661 A s n.
Proof. exact (fun h0 : term420 A s n => @lem4617653 A s n h0 h1 h2). Qed.
Lemma lem4617655 {A : Type'} (s : A -> Prop) (n : nat) : (term661 A s n) = (term441 A s n).
Proof. exact (@lem69 (term420 A s n)). Qed.
Lemma lem4617656 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term262 A s) (h2 : term405 n) : term441 A s n.
Proof. exact (EQ_MP (@lem4617655 A s n) (@lem4617654 A s n h1 h2)). Qed.
Lemma lem4617657 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term262 A s) (h2 : term405 n) : (term420 A s n) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4616859 A n s h1) (@lem4617656 A s n h1 h2)). Qed.
Lemma lem4617658 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term420 A s n) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4616821 A n s h1) (@lem4616994 A n s h1)). Qed.
Lemma lem4617659 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term405 n) : (term420 A s n) = (@FINITE A s).
Proof. exact (or_elim (@lem4615775 A s) (fun h0 : @FINITE A s => @lem4617658 A n s h0) (fun h0 : term262 A s => @lem4617657 A s n h0 h1)). Qed.
Lemma lem4617660 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term405 n) : (term420 A s n) = (term426 A s n).
Proof. exact (EQ_MP (@lem4616730 A s n h1) (@lem4617659 A s n h1)). Qed.
Lemma lem4617661 {A : Type'} (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term420 A s n) = (term426 A s n).
Proof. exact (EQ_MP (@lem4616694 A s n h1) (@lem4616783 A s)). Qed.
Lemma lem4617662 {A : Type'} (s : A -> Prop) (n : nat) : (term420 A s n) = (term426 A s n).
Proof. exact (or_elim (@lem4616625 n) (fun h0 : n = (NUMERAL 0) => @lem4617661 A s n h0) (fun h0 : term405 n => @lem4617660 A s n h0)). Qed.
Lemma lem4617667 {A : Type'} (s : A -> Prop) : term662 A s.
Proof. exact (fun n : nat => @lem4617662 A s n). Qed.
Lemma lem4617672 {A : Type'} : term663 A.
Proof. exact (fun s : A -> Prop => @lem4617667 A s). Qed.
