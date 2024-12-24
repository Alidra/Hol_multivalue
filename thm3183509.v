Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183509_term_abbrevs.
Require Import thm3183065_spec.
Require Import thm3183066_spec.
Lemma lem3183489 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : (@SETSPEC _83031 v P t) = (term0 _83031 P v t).
Proof. exact (EQ_MP (@lem3183066 _83031 P v t) (@lem3183065 _83031 P v t)). Qed.
Lemma lem3183490 {_83095 : Type'} (P : Prop) (v : _83095) (t : _83095) : (@SETSPEC _83095 v P t) = (term0 _83095 P v t).
Proof. exact (@lem3183489 _83095 P v t). Qed.
Lemma lem3183491 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term1 _83095 x p y) = (term2 _83095 p x y).
Proof. exact (@lem3183490 _83095 (p y) x y). Qed.
Lemma lem3183496 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 x p) = (term4 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183491 _83095 p x y)). Qed.
Lemma lem3183497 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183498 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term5 _83095 x p) = (term6 _83095 p x).
Proof. exact (MK_COMB (@lem3183497 _83095) (@lem3183496 _83095 p x)). Qed.
Lemma lem3183503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183504 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 x p) = (term8 _83095 p x).
Proof. exact (MK_COMB (@lem3183503) (@lem3183498 _83095 p x)). Qed.
Lemma lem3183505 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183506 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term5 _83095 x p) = (p x)) = ((term6 _83095 p x) = (p x)).
Proof. exact (MK_COMB (@lem3183504 _83095 p x) (@lem3183505 _83095 p x)). Qed.
Lemma lem3183509 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term6 _83095 p x) = (p x)) = ((term5 _83095 x p) = (p x)).
Proof. exact (SYM (@lem3183506 _83095 p x)). Qed.
