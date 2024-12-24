Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108228_term_abbrevs.
Require Import thm1108205_spec.
Lemma lem1108216 {_25645 _25647 _25655 : Type'} (h1' : _25647) : term0 _25645 _25647 _25655 h1'.
Proof. exact (@lem1108205 _25645 _25647 _25655 h1'). Qed.
Lemma lem1108217 {_25645 _25647 _25655 : Type'} (h1' : _25647) : (term0 _25645 _25647 _25655 h1') = (term1 _25645 _25647 _25655 h1').
Proof. exact (eq_refl (term0 _25645 _25647 _25655 h1')). Qed.
Lemma lem1108218 {_25645 _25647 _25655 : Type'} (h1' : _25647) : term1 _25645 _25647 _25655 h1'.
Proof. exact (EQ_MP (@lem1108217 _25645 _25647 _25655 h1') (@lem1108216 _25645 _25647 _25655 h1')). Qed.
Lemma lem1108219 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) : term2 _25645 _25647 _25655 h1' f.
Proof. exact (@lem1108218 _25645 _25647 _25655 h1' f). Qed.
Lemma lem1108220 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) : (term2 _25645 _25647 _25655 h1' f) = (term3 _25645 _25647 _25655 h1' f).
Proof. exact (eq_refl (term2 _25645 _25647 _25655 h1' f)). Qed.
Lemma lem1108221 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) : term3 _25645 _25647 _25655 h1' f.
Proof. exact (EQ_MP (@lem1108220 _25645 _25647 _25655 h1' f) (@lem1108219 _25645 _25647 _25655 h1' f)). Qed.
Lemma lem1108222 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) : term4 _25645 _25647 _25655 h1' f t1.
Proof. exact (@lem1108221 _25645 _25647 _25655 h1' f t1). Qed.
Lemma lem1108223 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) : (term4 _25645 _25647 _25655 h1' f t1) = (term5 _25645 _25647 _25655 h1' f t1).
Proof. exact (eq_refl (term4 _25645 _25647 _25655 h1' f t1)). Qed.
Lemma lem1108224 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) : term5 _25645 _25647 _25655 h1' f t1.
Proof. exact (EQ_MP (@lem1108223 _25645 _25647 _25655 h1' f t1) (@lem1108222 _25645 _25647 _25655 h1' f t1)). Qed.
Lemma lem1108225 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) : term6 _25645 _25647 _25655 h1' f t1 l2.
Proof. exact (@lem1108224 _25645 _25647 _25655 h1' f t1 l2). Qed.
Lemma lem1108226 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) : (term6 _25645 _25647 _25655 h1' f t1 l2) = (term7 _25645 _25647 _25655 h1' f t1 l2).
Proof. exact (eq_refl (term6 _25645 _25647 _25655 h1' f t1 l2)). Qed.
Lemma lem1108227 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) : term7 _25645 _25647 _25655 h1' f t1 l2.
Proof. exact (EQ_MP (@lem1108226 _25645 _25647 _25655 h1' f t1 l2) (@lem1108225 _25645 _25647 _25655 h1' f t1 l2)). Qed.
Lemma lem1108228 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : term8 _25645 _25647 _25655 h1' f t1 l2 b.
Proof. exact (@lem1108227 _25645 _25647 _25655 h1' f t1 l2 b). Qed.
