Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7260959_term_abbrevs.
Require Import SUM_EQ_spec.
Lemma lem7260932 {_132349 : Type'} (h1 : term0 _132349) : term0 _132349.
Proof. exact (h1). Qed.
Lemma lem7260933 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term1 _132349 f.
Proof. exact (@lem7260932 _132349 h1 f). Qed.
Lemma lem7260934 {_132349 : Type'} (f : _132349 -> real) : (term1 _132349 f) = (term2 _132349 f).
Proof. exact (eq_refl (term1 _132349 f)). Qed.
Lemma lem7260935 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term2 _132349 f.
Proof. exact (EQ_MP (@lem7260934 _132349 f) (@lem7260933 _132349 f h1)). Qed.
Lemma lem7260936 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term0 _132349) : term3 _132349 f g.
Proof. exact (@lem7260935 _132349 f h1 g). Qed.
Lemma lem7260937 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term3 _132349 f g) = (term4 _132349 f g).
Proof. exact (eq_refl (term3 _132349 f g)). Qed.
Lemma lem7260938 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term0 _132349) : term4 _132349 f g.
Proof. exact (EQ_MP (@lem7260937 _132349 f g) (@lem7260936 _132349 f g h1)). Qed.
Lemma lem7260939 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (s : _132349 -> Prop) (h1 : term0 _132349) : term5 _132349 f g s.
Proof. exact (@lem7260938 _132349 f g h1 s). Qed.
Lemma lem7260940 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term5 _132349 f g s) = (term6 _132349 f s g).
Proof. exact (eq_refl (term5 _132349 f g s)). Qed.
Lemma lem7260941 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term0 _132349) : term6 _132349 f s g.
Proof. exact (EQ_MP (@lem7260940 _132349 f s g) (@lem7260939 _132349 f g s h1)). Qed.
Lemma lem7260942 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) : term7 _132349 s f g.
Proof. exact (h1). Qed.
Lemma lem7260943 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) (h2 : term0 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7260941 _132349 f s g h2 (@lem7260942 _132349 s f g h1)). Qed.
Lemma lem7260944 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) : term8 _132349 f s g.
Proof. exact (fun h0 : term0 _132349 => @lem7260943 _132349 s f g h1 h0). Qed.
Lemma lem7260945 {_132349 : Type'} (h1 : term0 _132349) : term0 _132349.
Proof. exact (h1). Qed.
Lemma lem7260946 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) (h2 : term0 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7260944 _132349 s f g h1 (@lem7260945 _132349 h2)). Qed.
Lemma lem7260947 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term0 _132349) : term6 _132349 f s g.
Proof. exact (fun h0 : term7 _132349 s f g => @lem7260946 _132349 s f g h0 h1). Qed.
Lemma lem7260948 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (h1 : term0 _132349) : term9 _132349 f s.
Proof. exact (fun g : _132349 -> real => @lem7260947 _132349 f s g h1). Qed.
Lemma lem7260949 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term10 _132349 f.
Proof. exact (fun s : _132349 -> Prop => @lem7260948 _132349 f s h1). Qed.
Lemma lem7260950 {_132349 : Type'} (h1 : term0 _132349) : term11 _132349.
Proof. exact (fun f : _132349 -> real => @lem7260949 _132349 f h1). Qed.
Lemma lem7260951 {_132349 : Type'} : term12 _132349.
Proof. exact (fun h0 : term0 _132349 => @lem7260950 _132349 h0). Qed.
Lemma lem7260952 {_132349 : Type'} : term11 _132349.
Proof. exact (@lem7260951 _132349 (@lem7081239 _132349)). Qed.
Lemma lem7260953 {_132349 : Type'} (f : _132349 -> real) : term13 _132349 f.
Proof. exact (@lem7260952 _132349 f). Qed.
Lemma lem7260954 {_132349 : Type'} (f : _132349 -> real) : (term13 _132349 f) = (term10 _132349 f).
Proof. exact (eq_refl (term13 _132349 f)). Qed.
Lemma lem7260955 {_132349 : Type'} (f : _132349 -> real) : term10 _132349 f.
Proof. exact (EQ_MP (@lem7260954 _132349 f) (@lem7260953 _132349 f)). Qed.
Lemma lem7260956 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term14 _132349 f s.
Proof. exact (@lem7260955 _132349 f s). Qed.
Lemma lem7260957 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : (term14 _132349 f s) = (term9 _132349 f s).
Proof. exact (eq_refl (term14 _132349 f s)). Qed.
Lemma lem7260958 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term9 _132349 f s.
Proof. exact (EQ_MP (@lem7260957 _132349 f s) (@lem7260956 _132349 f s)). Qed.
Lemma lem7260959 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term15 _132349 f s g.
Proof. exact (@lem7260958 _132349 f s g). Qed.
