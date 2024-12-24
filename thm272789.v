Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm272789_term_abbrevs.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import EQ_SYM_EQ_spec.
Lemma lem272769 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem272770 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem272771 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem272770 A x) (@lem272769 A x)). Qed.
Lemma lem272772 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem272771 A x y). Qed.
Lemma lem272773 {A : Type'} (y : A) (x : A) : (term2 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem272776 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem272773 A y x) (@lem272772 A x y)). Qed.
Lemma lem272777 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem272776 nat y x). Qed.
Lemma lem272778 (m : nat) (n : nat) : ((Nat.add m n) = m) = (m = (Nat.add m n)).
Proof. exact (@lem272777 m (Nat.add m n)). Qed.
Lemma lem272779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem272780 (m : nat) (n : nat) : (term3 n m) = (term4 m n).
Proof. exact (MK_COMB (@lem272779) (@lem272778 m n)). Qed.
Lemma lem272781 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem272782 (m : nat) (n : nat) : (((Nat.add m n) = m) = (n = (NUMERAL 0))) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem272780 m n) (@lem272781 n)). Qed.
Lemma lem272783 (m : nat) : (term5 m) = (term6 m).
Proof. exact (fun_ext (fun n : nat => @lem272782 m n)). Qed.
Lemma lem272784 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem272785 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem272784) (@lem272783 m)). Qed.
Lemma lem272786 : term9 = term10.
Proof. exact (fun_ext (fun m : nat => @lem272785 m)). Qed.
Lemma lem272787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem272788 : term11 = term12.
Proof. exact (MK_COMB (@lem272787) (@lem272786)). Qed.
Lemma lem272789 : term12.
Proof. exact (EQ_MP (@lem272788) (@lem79890)). Qed.
