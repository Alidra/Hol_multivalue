Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_FINITE_PROD_term_abbrevs.
Require Import DIMINDEX_HAS_SIZE_FINITE_PROD_spec.
Require Import HAS_SIZE_spec.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7924758 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem7924759 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem7924760 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem7924759 _100044 s) (@lem7924758 _100044 s)). Qed.
Lemma lem7924761 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem7924760 _100044 s n). Qed.
Lemma lem7924762 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem7924765 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem7924762 _100044 s n) (@lem7924761 _100044 s n)). Qed.
Lemma lem7924766 {M N : Type'} (s : type36 M N) (n : nat) : (@HAS_SIZE (finite_prod M N) s n) = (term4 M N s n).
Proof. exact (@lem7924765 (finite_prod M N) s n). Qed.
Lemma lem7924767 {M N : Type'} : (term5 M N) = (term6 M N).
Proof. exact (@lem7924766 M N (@UNIV (finite_prod M N)) (term7 M N)). Qed.
Lemma lem7924772 {M N : Type'} : term6 M N.
Proof. exact (EQ_MP (@lem7924767 M N) (@lem7924757 M N)). Qed.
Lemma lem7924774 {M N : Type'} : @FINITE (finite_prod M N) (@UNIV (finite_prod M N)).
Proof. exact (proj1 (@lem7924772 M N)). Qed.
Lemma lem7924775 {M N : Type'} : (@FINITE (finite_prod M N) (@UNIV (finite_prod M N))) = ((@FINITE (finite_prod M N) (@UNIV (finite_prod M N))) = True).
Proof. exact (@lem7 (@FINITE (finite_prod M N) (@UNIV (finite_prod M N)))). Qed.
Lemma lem7924777 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7924778 {A : Type'} (s : A -> Prop) : (term8 A s) = ((@dimindex A s) = (term9 A)).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem7924781 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term9 A).
Proof. exact (EQ_MP (@lem7924778 A s) (@lem7924777 A s)). Qed.
Lemma lem7924782 {M N : Type'} (s : type36 M N) : (@dimindex (finite_prod M N) s) = (term10 M N).
Proof. exact (@lem7924781 (finite_prod M N) s). Qed.
Lemma lem7924783 {M N : Type'} : (@dimindex (finite_prod M N) (@UNIV (finite_prod M N))) = (term10 M N).
Proof. exact (@lem7924782 M N (@UNIV (finite_prod M N))). Qed.
Lemma lem7924784 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7924785 {M N : Type'} : (term11 M N) = (term12 M N).
Proof. exact (MK_COMB (@lem7924784) (@lem7924783 M N)). Qed.
Lemma lem7924786 {M N : Type'} : (term7 M N) = (term7 M N).
Proof. exact (eq_refl (term7 M N)). Qed.
Lemma lem7924787 {M N : Type'} : ((@dimindex (finite_prod M N) (@UNIV (finite_prod M N))) = (term7 M N)) = ((term10 M N) = (term7 M N)).
Proof. exact (MK_COMB (@lem7924785 M N) (@lem7924786 M N)). Qed.
Lemma lem7924788 {M N : Type'} : ((term10 M N) = (term7 M N)) = ((@dimindex (finite_prod M N) (@UNIV (finite_prod M N))) = (term7 M N)).
Proof. exact (SYM (@lem7924787 M N)). Qed.
Lemma lem7924792 {M N : Type'} : (@FINITE (finite_prod M N) (@UNIV (finite_prod M N))) = True.
Proof. exact (EQ_MP (@lem7924775 M N) (@lem7924774 M N)). Qed.
Lemma lem7924793 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7924794 {M N : Type'} : (term13 M N) = (@COND nat True).
Proof. exact (MK_COMB (@lem7924793) (@lem7924792 M N)). Qed.
Lemma lem7924796 {M N : Type'} : (@CARD (finite_prod M N) (@UNIV (finite_prod M N))) = (term7 M N).
Proof. exact (proj2 (@lem7924772 M N)). Qed.
Lemma lem7924797 {M N : Type'} : (term14 M N) = (term15 M N).
Proof. exact (MK_COMB (@lem7924794 M N) (@lem7924796 M N)). Qed.
Lemma lem7924798 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem7924799 {M N : Type'} : (term10 M N) = (term17 M N).
Proof. exact (MK_COMB (@lem7924797 M N) (@lem7924798)). Qed.
Lemma lem7924801 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7924802 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7924801 nat t2 t1). Qed.
Lemma lem7924803 {M N : Type'} : (term17 M N) = (term7 M N).
Proof. exact (@lem7924802 term16 (term7 M N)). Qed.
Lemma lem7924804 {M N : Type'} : (term10 M N) = (term7 M N).
Proof. exact (TRANS (@lem7924799 M N) (@lem7924803 M N)). Qed.
Lemma lem7924805 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7924806 {M N : Type'} : (term12 M N) = (term18 M N).
Proof. exact (MK_COMB (@lem7924805) (@lem7924804 M N)). Qed.
Lemma lem7924807 {M N : Type'} : (term7 M N) = (term7 M N).
Proof. exact (eq_refl (term7 M N)). Qed.
Lemma lem7924808 {M N : Type'} : ((term10 M N) = (term7 M N)) = ((term7 M N) = (term7 M N)).
Proof. exact (MK_COMB (@lem7924806 M N) (@lem7924807 M N)). Qed.
Lemma lem7924810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7924811 (x : nat) : (x = x) = True.
Proof. exact (@lem7924810 nat x). Qed.
Lemma lem7924812 {M N : Type'} : ((term7 M N) = (term7 M N)) = True.
Proof. exact (@lem7924811 (term7 M N)). Qed.
Lemma lem7924813 {M N : Type'} : ((term10 M N) = (term7 M N)) = True.
Proof. exact (TRANS (@lem7924808 M N) (@lem7924812 M N)). Qed.
Lemma lem7924814 {M N : Type'} : True = ((term10 M N) = (term7 M N)).
Proof. exact (SYM (@lem7924813 M N)). Qed.
Lemma lem7924815 {M N : Type'} : (term10 M N) = (term7 M N).
Proof. exact (EQ_MP (@lem7924814 M N) (@lem0)). Qed.
Lemma lem7924816 {M N : Type'} : (@dimindex (finite_prod M N) (@UNIV (finite_prod M N))) = (term7 M N).
Proof. exact (EQ_MP (@lem7924788 M N) (@lem7924815 M N)). Qed.
