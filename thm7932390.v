Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932390_term_abbrevs.
Lemma lem7932390 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term0 _88266 _88270 f s t) = (term1 _88266 _88270 f s t).
Proof. exact (eq_refl (term0 _88266 _88270 f s t)). Qed.
