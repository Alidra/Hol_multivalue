Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_CARD_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem3863774 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3863775 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem3863776 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem3863775 _100044 s) (@lem3863774 _100044 s)). Qed.
Lemma lem3863777 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem3863776 _100044 s n). Qed.
Lemma lem3863778 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem3863791 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term4 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3863792 (p : Prop) (q : Prop) (p' : Prop) : term5 p q p'.
Proof. exact (fun q' : Prop => @lem3863791 p q p' q'). Qed.
Lemma lem3863793 (p : Prop) (q : Prop) : term6 p q.
Proof. exact (fun p' : Prop => @lem3863792 p q p'). Qed.
Lemma lem3863794 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : term7 _100063 s n.
Proof. exact (@lem3863793 (@HAS_SIZE _100063 s n) ((@CARD _100063 s) = n)). Qed.
Lemma lem3863795 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (p' : Prop) : term8 _100063 s n p'.
Proof. exact (@lem3863794 _100063 s n p'). Qed.
Lemma lem3863796 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (p' : Prop) : (term8 _100063 s n p') = (term9 _100063 s n p').
Proof. exact (eq_refl (term8 _100063 s n p')). Qed.
Lemma lem3863797 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (p' : Prop) : term9 _100063 s n p'.
Proof. exact (EQ_MP (@lem3863796 _100063 s n p') (@lem3863795 _100063 s n p')). Qed.
Lemma lem3863798 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term10 _100063 s n p' q'.
Proof. exact (@lem3863797 _100063 s n p' q'). Qed.
Lemma lem3863799 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (p' : Prop) (q' : Prop) : (term10 _100063 s n p' q') = (term11 _100063 s n p' q').
Proof. exact (eq_refl (term10 _100063 s n p' q')). Qed.
Lemma lem3863800 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term11 _100063 s n p' q'.
Proof. exact (EQ_MP (@lem3863799 _100063 s n p' q') (@lem3863798 _100063 s n p' q')). Qed.
Lemma lem3863802 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem3863778 _100044 s n) (@lem3863777 _100044 s n)). Qed.
Lemma lem3863803 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : (@HAS_SIZE _100063 s n) = (term3 _100063 s n).
Proof. exact (@lem3863802 _100063 s n). Qed.
Lemma lem3863808 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (q' : Prop) : term12 _100063 s n q'.
Proof. exact (@lem3863800 _100063 s n (term3 _100063 s n) q'). Qed.
Lemma lem3863809 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (q' : Prop) : term13 _100063 s n q'.
Proof. exact (@lem3863808 _100063 s n q' (@lem3863803 _100063 s n)). Qed.
Lemma lem3863810 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (h1 : term3 _100063 s n) : term3 _100063 s n.
Proof. exact (h1). Qed.
Lemma lem3863818 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (h1 : term3 _100063 s n) : (@CARD _100063 s) = n.
Proof. exact (proj2 (@lem3863810 _100063 s n h1)). Qed.
Lemma lem3863819 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3863820 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (h1 : term3 _100063 s n) : (term14 _100063 s) = (@eq nat n).
Proof. exact (MK_COMB (@lem3863819) (@lem3863818 _100063 s n h1)). Qed.
Lemma lem3863821 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3863822 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (h1 : term3 _100063 s n) : ((@CARD _100063 s) = n) = (n = n).
Proof. exact (MK_COMB (@lem3863820 _100063 s n h1) (@lem3863821 n)). Qed.
Lemma lem3863824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3863825 (x : nat) : (x = x) = True.
Proof. exact (@lem3863824 nat x). Qed.
Lemma lem3863826 (n : nat) : (n = n) = True.
Proof. exact (@lem3863825 n). Qed.
Lemma lem3863827 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) (h1 : term3 _100063 s n) : ((@CARD _100063 s) = n) = True.
Proof. exact (TRANS (@lem3863822 _100063 s n h1) (@lem3863826 n)). Qed.
Lemma lem3863828 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : term15 _100063 s n.
Proof. exact (fun h0 : term3 _100063 s n => @lem3863827 _100063 s n h0). Qed.
Lemma lem3863829 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : term16 _100063 s n.
Proof. exact (@lem3863809 _100063 s n True). Qed.
Lemma lem3863830 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : (term17 _100063 s n) = (term18 _100063 s n).
Proof. exact (@lem3863829 _100063 s n (@lem3863828 _100063 s n)). Qed.
Lemma lem3863832 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3863833 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : (term18 _100063 s n) = True.
Proof. exact (@lem3863832 (term3 _100063 s n)). Qed.
Lemma lem3863834 {_100063 : Type'} (s : _100063 -> Prop) (n : nat) : (term17 _100063 s n) = True.
Proof. exact (TRANS (@lem3863830 _100063 s n) (@lem3863833 _100063 s n)). Qed.
Lemma lem3863835 {_100063 : Type'} (s : _100063 -> Prop) : (term19 _100063 s) = term20.
Proof. exact (fun_ext (fun n : nat => @lem3863834 _100063 s n)). Qed.
Lemma lem3863836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3863837 {_100063 : Type'} (s : _100063 -> Prop) : (term21 _100063 s) = term22.
Proof. exact (MK_COMB (@lem3863836) (@lem3863835 _100063 s)). Qed.
Lemma lem3863839 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3863840 (t : Prop) : (term24 t) = t.
Proof. exact (@lem3863839 nat t). Qed.
Lemma lem3863841 : term22 = True.
Proof. exact (@lem3863840 True). Qed.
Lemma lem3863842 {_100063 : Type'} (s : _100063 -> Prop) : (term21 _100063 s) = True.
Proof. exact (TRANS (@lem3863837 _100063 s) (@lem3863841)). Qed.
Lemma lem3863843 {_100063 : Type'} : (term25 _100063) = (term26 _100063).
Proof. exact (fun_ext (fun s : _100063 -> Prop => @lem3863842 _100063 s)). Qed.
Lemma lem3863844 {_100063 : Type'} : (@all (_100063 -> Prop)) = (@all (_100063 -> Prop)).
Proof. exact (eq_refl (@all (_100063 -> Prop))). Qed.
Lemma lem3863845 {_100063 : Type'} : (term27 _100063) = (term28 _100063).
Proof. exact (MK_COMB (@lem3863844 _100063) (@lem3863843 _100063)). Qed.
Lemma lem3863847 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3863848 {_100063 : Type'} (t : Prop) : (term29 _100063 t) = t.
Proof. exact (@lem3863847 (_100063 -> Prop) t). Qed.
Lemma lem3863849 {_100063 : Type'} : (term28 _100063) = True.
Proof. exact (@lem3863848 _100063 True). Qed.
Lemma lem3863850 {_100063 : Type'} : (term27 _100063) = True.
Proof. exact (TRANS (@lem3863845 _100063) (@lem3863849 _100063)). Qed.
Lemma lem3863851 {_100063 : Type'} : True = (term27 _100063).
Proof. exact (SYM (@lem3863850 _100063)). Qed.
Lemma lem3863852 {_100063 : Type'} : term27 _100063.
Proof. exact (EQ_MP (@lem3863851 _100063) (@lem0)). Qed.
