Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261377_term_abbrevs.
Require Import thm7260968_spec.
Require Import thm7261111_spec.
Lemma lem7261377 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term1 _137613 s f) = (@sum _137613 s g).
Proof. exact (@lem7260968 _137613 f s g (@lem7261111 _137613 s f g h1)). Qed.
