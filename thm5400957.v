Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400957_term_abbrevs.
Require Import thm1834_spec.
Require Import thm5400767_spec.
Require Import thm5400768_spec.
Require Import thm5400772_spec.
Require Import thm5400773_spec.
Require Import thm5400781_spec.
Require Import thm5400782_spec.
Lemma lem5400921 (m : nat) (p : nat) (n : nat) : (term0 p m n) = (term1 m p n).
Proof. exact (EQ_MP (@lem5400782 m p n) (@lem5400781 m n p)). Qed.
Lemma lem5400922 (m : nat) (x : nat) : (term2 x m) = (term3 m x).
Proof. exact (@lem5400921 m x (NUMERAL 0)). Qed.
Lemma lem5400925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5400926 (m : nat) (x : nat) : (term4 x m) = (term5 m x).
Proof. exact (MK_COMB (@lem5400925) (@lem5400922 m x)). Qed.
Lemma lem5400928 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term6 A x y s) = (term7 A y x s).
Proof. exact (EQ_MP (@lem5400768 A y x s) (@lem5400767 A y x s)). Qed.
Lemma lem5400929 (y : nat) (x : nat) (s : nat -> Prop) : (term8 x y s) = (term9 y x s).
Proof. exact (@lem5400928 nat y x s). Qed.
Lemma lem5400930 (x : nat) : (term10 x) = (term11 x).
Proof. exact (@lem5400929 (NUMERAL 0) x (@EMPTY nat)). Qed.
Lemma lem5400936 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5400773 A x (@lem5400772 A x)). Qed.
Lemma lem5400937 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem5400936 nat x). Qed.
Lemma lem5400938 (x : nat) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem5400939 (x : nat) : (term11 x) = (term13 x).
Proof. exact (MK_COMB (@lem5400938 x) (@lem5400937 x)). Qed.
Lemma lem5400941 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5400942 (x : nat) : (term13 x) = (x = (NUMERAL 0)).
Proof. exact (@lem5400941 (x = (NUMERAL 0))). Qed.
Lemma lem5400945 (x : nat) : (term11 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem5400939 x) (@lem5400942 x)). Qed.
Lemma lem5400946 (x : nat) : (term10 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem5400930 x) (@lem5400945 x)). Qed.
Lemma lem5400947 (m : nat) (x : nat) : ((term2 x m) = (term10 x)) = ((term3 m x) = (x = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem5400926 m x) (@lem5400946 x)). Qed.
Lemma lem5400950 (m : nat) : (term14 m) = (term15 m).
Proof. exact (fun_ext (fun x : nat => @lem5400947 m x)). Qed.
Lemma lem5400951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5400952 (m : nat) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem5400951) (@lem5400950 m)). Qed.
Lemma lem5400957 (m : nat) : (term17 m) = (term16 m).
Proof. exact (SYM (@lem5400952 m)). Qed.
