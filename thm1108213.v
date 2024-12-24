Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108213_term_abbrevs.
Require Import thm1108204_spec.
Lemma lem1108206 {_25645 _25647 _25655 : Type'} : term0 _25645 _25647 _25655.
Proof. exact (proj1 (@lem1108204 _25645 _25647 _25655)). Qed.
Lemma lem1108207 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : term1 _25645 _25647 _25655 f.
Proof. exact (@lem1108206 _25645 _25647 _25655 f). Qed.
Lemma lem1108208 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term1 _25645 _25647 _25655 f) = (term2 _25645 _25647 _25655 f).
Proof. exact (eq_refl (term1 _25645 _25647 _25655 f)). Qed.
Lemma lem1108209 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : term2 _25645 _25647 _25655 f.
Proof. exact (EQ_MP (@lem1108208 _25645 _25647 _25655 f) (@lem1108207 _25645 _25647 _25655 f)). Qed.
Lemma lem1108210 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) : term3 _25645 _25647 _25655 f l2.
Proof. exact (@lem1108209 _25645 _25647 _25655 f l2). Qed.
Lemma lem1108211 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) : (term3 _25645 _25647 _25655 f l2) = (term4 _25645 _25647 _25655 f l2).
Proof. exact (eq_refl (term3 _25645 _25647 _25655 f l2)). Qed.
Lemma lem1108212 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) : term4 _25645 _25647 _25655 f l2.
Proof. exact (EQ_MP (@lem1108211 _25645 _25647 _25655 f l2) (@lem1108210 _25645 _25647 _25655 f l2)). Qed.
Lemma lem1108213 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) (b : _25645) : term5 _25645 _25647 _25655 f l2 b.
Proof. exact (@lem1108212 _25645 _25647 _25655 f l2 b). Qed.
