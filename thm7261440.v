Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261440_term_abbrevs.
Require Import thm7260962_spec.
Require Import thm7261377_spec.
Lemma lem7261420 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term0 _137613 s f g) = ((term1 _137613 s f) = (@sum _137613 s g)).
Proof. exact (prop_ext (fun h2 : term0 _137613 s f g => @lem7261377 _137613 s f g h1) (fun h2 : (term1 _137613 s f) = (@sum _137613 s g) => @lem7260962 _137613 s f g h1)). Qed.
Lemma lem7261421 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term1 _137613 s f) = (@sum _137613 s g).
Proof. exact (EQ_MP (@lem7261420 _137613 s f g h1) (@lem7260962 _137613 s f g h1)). Qed.
Lemma lem7261422 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real) : term2 _137613 f s g.
Proof. exact (fun h0 : term0 _137613 s f g => @lem7261421 _137613 s f g h0). Qed.
Lemma lem7261427 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) : term3 _137613 f g.
Proof. exact (fun s : _137613 -> Prop => @lem7261422 _137613 f s g). Qed.
Lemma lem7261432 {_137613 : Type'} (f : _137613 -> real) : term4 _137613 f.
Proof. exact (fun g : _137613 -> real => @lem7261427 _137613 f g). Qed.
Lemma lem7261440 {_137613 : Type'} : term5 _137613.
Proof. exact (fun f : _137613 -> real => @lem7261432 _137613 f). Qed.
