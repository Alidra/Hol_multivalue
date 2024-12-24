Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337493_term_abbrevs.
Lemma lem1337485 (r : type1233) : (term0 r) = ((term1 r) = r).
Proof. exact (@axiom_24 r). Qed.
Lemma lem1337488 (r : type1233) : (term0 r) = (term2 r).
Proof. exact (eq_refl (term0 r)). Qed.
Lemma lem1337489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337490 (r : type1233) : (term3 r) = (term4 r).
Proof. exact (MK_COMB (@lem1337489) (@lem1337488 r)). Qed.
Lemma lem1337491 (r : type1233) : ((term1 r) = r) = ((term1 r) = r).
Proof. exact (eq_refl ((term1 r) = r)). Qed.
Lemma lem1337492 (r : type1233) : ((term0 r) = ((term1 r) = r)) = ((term2 r) = ((term1 r) = r)).
Proof. exact (MK_COMB (@lem1337490 r) (@lem1337491 r)). Qed.
Lemma lem1337493 (r : type1233) : (term2 r) = ((term1 r) = r).
Proof. exact (EQ_MP (@lem1337492 r) (@lem1337485 r)). Qed.
