Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9261_term_abbrevs.
Require Import EQ_EXT_spec.
Lemma lem9235 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem9236 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem9235 A B h1 f). Qed.
Lemma lem9237 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem9238 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem9237 A B f) (@lem9236 A B f h1)). Qed.
Lemma lem9239 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term0 A B) : term3 A B f g.
Proof. exact (@lem9238 A B f h1 g). Qed.
Lemma lem9240 {A B : Type'} (f : A -> B) (g : A -> B) : (term3 A B f g) = (term4 A B f g).
Proof. exact (eq_refl (term3 A B f g)). Qed.
Lemma lem9241 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term0 A B) : term4 A B f g.
Proof. exact (EQ_MP (@lem9240 A B f g) (@lem9239 A B f g h1)). Qed.
Lemma lem9242 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term5 A B f g) : term5 A B f g.
Proof. exact (h1). Qed.
Lemma lem9243 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term5 A B f g) (h2 : term0 A B) : f = g.
Proof. exact (@lem9241 A B f g h2 (@lem9242 A B f g h1)). Qed.
Lemma lem9244 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term5 A B f g) : term6 A B f g.
Proof. exact (fun h0 : term0 A B => @lem9243 A B f g h1 h0). Qed.
Lemma lem9245 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem9246 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term5 A B f g) (h2 : term0 A B) : f = g.
Proof. exact (@lem9244 A B f g h1 (@lem9245 A B h2)). Qed.
Lemma lem9247 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term0 A B) : term4 A B f g.
Proof. exact (fun h0 : term5 A B f g => @lem9246 A B f g h0 h1). Qed.
Lemma lem9248 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun g : A -> B => @lem9247 A B f g h1). Qed.
Lemma lem9249 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem9248 A B f h1). Qed.
Lemma lem9250 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term0 A B => @lem9249 A B h0). Qed.
Lemma lem9251 {A B : Type'} : term0 A B.
Proof. exact (@lem9250 A B (@lem9176 A B)). Qed.
Lemma lem9252 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem9251 A B f). Qed.
Lemma lem9253 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem9254 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem9253 A B f) (@lem9252 A B f)). Qed.
Lemma lem9255 {A B : Type'} (f : A -> B) (g : A -> B) : term3 A B f g.
Proof. exact (@lem9254 A B f g). Qed.
Lemma lem9256 {A B : Type'} (f : A -> B) (g : A -> B) : (term3 A B f g) = (term4 A B f g).
Proof. exact (eq_refl (term3 A B f g)). Qed.
Lemma lem9259 {A B : Type'} (f : A -> B) (g : A -> B) : term4 A B f g.
Proof. exact (EQ_MP (@lem9256 A B f g) (@lem9255 A B f g)). Qed.
Lemma lem9260 {A : Type'} (f : type686 A) (g : type686 A) : term8 A f g.
Proof. exact (@lem9259 (A -> Prop) Prop f g). Qed.
Lemma lem9261 {A : Type'} : term9 A.
Proof. exact (@lem9260 A (@ex A) (term10 A)). Qed.
