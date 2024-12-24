Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITLIST2_DEF_term_abbrevs.
Require Import thm1108215_spec.
Require Import thm1108228_spec.
Require Import thm1108229_spec.
Lemma lem1108230 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : (term0 _25645 _25647 _25655 f h1' t1 l2 b) = (term1 _25645 _25647 _25655 h1' f t1 l2 b).
Proof. exact (EQ_MP (@lem1108229 _25645 _25647 _25655 h1' f t1 l2 b) (@lem1108228 _25645 _25647 _25655 h1' f t1 l2 b)). Qed.
Lemma lem1108231 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : term2 _25645 _25647 _25655 h1' f t1 l2 b.
Proof. exact (conj (@lem1108215 _25645 _25647 _25655 f l2 b) (@lem1108230 _25645 _25647 _25655 h1' f t1 l2 b)). Qed.
