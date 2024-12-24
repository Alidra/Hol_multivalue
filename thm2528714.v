Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2528714_term_abbrevs.
Require Import INT_REM_MOD_SELF_spec.
Lemma lem2528709 (m : int) : term0 m.
Proof. exact (@lem2528702 m). Qed.
Lemma lem2528710 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2528711 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2528710 m) (@lem2528709 m)). Qed.
Lemma lem2528712 (m : int) (n : int) (p : int) : term2 m n p.
Proof. exact (@lem2528711 m (int_mul n p)). Qed.
Lemma lem2528713 (m : int) (n : int) (p : int) : (term2 m n p) = (term3 m n p).
Proof. exact (eq_refl (term2 m n p)). Qed.
Lemma lem2528714 (m : int) (n : int) (p : int) : term3 m n p.
Proof. exact (EQ_MP (@lem2528713 m n p) (@lem2528712 m n p)). Qed.
