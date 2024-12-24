Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400988_term_abbrevs.
Require Import thm1857_spec.
Require Import thm5400772_spec.
Require Import thm5400773_spec.
Require Import thm5400781_spec.
Require Import thm5400782_spec.
Lemma lem5400965 (m : nat) (p : nat) (n : nat) : (term0 p m n) = (term1 m p n).
Proof. exact (EQ_MP (@lem5400782 m p n) (@lem5400781 m n p)). Qed.
Lemma lem5400966 (m : nat) (x : nat) : (term2 x m) = (term3 m x).
Proof. exact (@lem5400965 m x (NUMERAL 0)). Qed.
Lemma lem5400969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5400970 (m : nat) (x : nat) : (term4 x m) = (term5 m x).
Proof. exact (MK_COMB (@lem5400969) (@lem5400966 m x)). Qed.
Lemma lem5400972 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5400773 A x (@lem5400772 A x)). Qed.
Lemma lem5400973 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem5400972 nat x). Qed.
Lemma lem5400974 (m : nat) (x : nat) : ((term2 x m) = (@IN nat x (@EMPTY nat))) = ((term3 m x) = False).
Proof. exact (MK_COMB (@lem5400970 m x) (@lem5400973 x)). Qed.
Lemma lem5400976 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5400977 (m : nat) (x : nat) : ((term3 m x) = False) = (term6 m x).
Proof. exact (@lem5400976 (term3 m x)). Qed.
Lemma lem5400980 (m : nat) (x : nat) : ((term2 x m) = (@IN nat x (@EMPTY nat))) = (term6 m x).
Proof. exact (TRANS (@lem5400974 m x) (@lem5400977 m x)). Qed.
Lemma lem5400981 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun x : nat => @lem5400980 m x)). Qed.
Lemma lem5400982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5400983 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem5400982) (@lem5400981 m)). Qed.
Lemma lem5400988 (m : nat) : (term10 m) = (term9 m).
Proof. exact (SYM (@lem5400983 m)). Qed.
