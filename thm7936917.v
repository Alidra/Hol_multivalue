Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7936917_term_abbrevs.
Require Import dimindex_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem7936865 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7936866 {A : Type'} (s : A -> Prop) : (term0 A s) = ((@dimindex A s) = (term1 A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7936868 (n : nat) : term2 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem7936869 (n : nat) : (term2 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem7936876 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (EQ_MP (@lem7936866 A s) (@lem7936865 A s)). Qed.
Lemma lem7936877 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (@lem7936876 A s). Qed.
Lemma lem7936878 {A : Type'} : (@dimindex A (@UNIV A)) = (term1 A).
Proof. exact (@lem7936877 A (@UNIV A)). Qed.
Lemma lem7936880 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem7936869 n) (@lem7936868 n)). Qed.
Lemma lem7936881 : term3 = (BIT1 0).
Proof. exact (@lem7936880 (BIT1 0)). Qed.
Lemma lem7936882 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7936883 {A : Type'} : (term1 A) = (term5 A).
Proof. exact (MK_COMB (@lem7936882 A) (@lem7936881)). Qed.
Lemma lem7936884 {A : Type'} : (@dimindex A (@UNIV A)) = (term5 A).
Proof. exact (TRANS (@lem7936878 A) (@lem7936883 A)). Qed.
Lemma lem7936885 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7936886 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem7936885) (@lem7936884 A)). Qed.
Lemma lem7936887 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7936888 {A : Type'} (n : nat) : ((@dimindex A (@UNIV A)) = n) = ((term5 A) = n).
Proof. exact (MK_COMB (@lem7936886 A) (@lem7936887 n)). Qed.
Lemma lem7936891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7936892 {A : Type'} (n : nat) : (term8 A n) = (term9 A n).
Proof. exact (MK_COMB (@lem7936891) (@lem7936888 A n)). Qed.
Lemma lem7936896 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (EQ_MP (@lem7936866 A s) (@lem7936865 A s)). Qed.
Lemma lem7936897 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (@lem7936896 A s). Qed.
Lemma lem7936899 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem7936869 n) (@lem7936868 n)). Qed.
Lemma lem7936900 : term3 = (BIT1 0).
Proof. exact (@lem7936899 (BIT1 0)). Qed.
Lemma lem7936901 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7936902 {A : Type'} : (term1 A) = (term5 A).
Proof. exact (MK_COMB (@lem7936901 A) (@lem7936900)). Qed.
Lemma lem7936903 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term5 A).
Proof. exact (TRANS (@lem7936897 A s) (@lem7936902 A)). Qed.
Lemma lem7936904 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7936905 {A : Type'} (s : A -> Prop) : (term10 A s) = (term7 A).
Proof. exact (MK_COMB (@lem7936904) (@lem7936903 A s)). Qed.
Lemma lem7936907 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem7936869 n) (@lem7936868 n)). Qed.
Lemma lem7936908 {A : Type'} (s : A -> Prop) (n : nat) : ((@dimindex A s) = (NUMERAL n)) = ((term5 A) = n).
Proof. exact (MK_COMB (@lem7936905 A s) (@lem7936907 n)). Qed.
Lemma lem7936911 {A : Type'} (s : A -> Prop) (n : nat) : (((@dimindex A (@UNIV A)) = n) = ((@dimindex A s) = (NUMERAL n))) = (((term5 A) = n) = ((term5 A) = n)).
Proof. exact (MK_COMB (@lem7936892 A n) (@lem7936908 A s n)). Qed.
Lemma lem7936913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7936914 (x : Prop) : (x = x) = True.
Proof. exact (@lem7936913 Prop x). Qed.
Lemma lem7936915 {A : Type'} (n : nat) : (((term5 A) = n) = ((term5 A) = n)) = True.
Proof. exact (@lem7936914 ((term5 A) = n)). Qed.
Lemma lem7936916 {A : Type'} (s : A -> Prop) (n : nat) : (((@dimindex A (@UNIV A)) = n) = ((@dimindex A s) = (NUMERAL n))) = True.
Proof. exact (TRANS (@lem7936911 A s n) (@lem7936915 A n)). Qed.
Lemma lem7936917 {A : Type'} (s : A -> Prop) (n : nat) : True = (((@dimindex A (@UNIV A)) = n) = ((@dimindex A s) = (NUMERAL n))).
Proof. exact (SYM (@lem7936916 A s n)). Qed.
