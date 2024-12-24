Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183586_term_abbrevs.
Require Import thm3183065_spec.
Require Import thm3183066_spec.
Lemma lem3183566 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : (@SETSPEC _83031 v P t) = (term0 _83031 P v t).
Proof. exact (EQ_MP (@lem3183066 _83031 P v t) (@lem3183065 _83031 P v t)). Qed.
Lemma lem3183567 {_83152 : Type'} (P : Prop) (v : _83152) (t : _83152) : (@SETSPEC _83152 v P t) = (term0 _83152 P v t).
Proof. exact (@lem3183566 _83152 P v t). Qed.
Lemma lem3183568 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term1 _83152 x p y) = (term2 _83152 p x y).
Proof. exact (@lem3183567 _83152 (p y) x y). Qed.
Lemma lem3183573 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 x p) = (term4 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3183568 _83152 p x y)). Qed.
Lemma lem3183574 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3183575 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term5 _83152 x p) = (term6 _83152 p x).
Proof. exact (MK_COMB (@lem3183574 _83152) (@lem3183573 _83152 p x)). Qed.
Lemma lem3183580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183581 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term7 _83152 x p) = (term8 _83152 p x).
Proof. exact (MK_COMB (@lem3183580) (@lem3183575 _83152 p x)). Qed.
Lemma lem3183582 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183583 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term5 _83152 x p) = (p x)) = ((term6 _83152 p x) = (p x)).
Proof. exact (MK_COMB (@lem3183581 _83152 p x) (@lem3183582 _83152 p x)). Qed.
Lemma lem3183586 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term6 _83152 p x) = (p x)) = ((term5 _83152 x p) = (p x)).
Proof. exact (SYM (@lem3183583 _83152 p x)). Qed.
