Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FUN_EQ_THM_term_abbrevs.
Require Import EQ_EXT_spec.
Require Import thm32_spec.
Lemma lem9177 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : f = g) : f = g.
Proof. exact (h1). Qed.
Lemma lem9178 {A B : Type'} (g : A -> B) : (term0 A B g) = (term0 A B g).
Proof. exact (eq_refl (term0 A B g)). Qed.
Lemma lem9179 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : f = g) : (term1 A B g f) = (term2 A B g).
Proof. exact (MK_COMB (@lem9178 A B g) (@lem9177 A B f g h1)). Qed.
Lemma lem9180 {A B : Type'} (g : A -> B) : (term2 A B g) = (term3 A B g).
Proof. exact (eq_refl (term2 A B g)). Qed.
Lemma lem9181 {A B : Type'} (g : A -> B) (f : A -> B) : (term4 A B g f) = (term4 A B g f).
Proof. exact (eq_refl (term4 A B g f)). Qed.
Lemma lem9182 {A B : Type'} (f : A -> B) (g : A -> B) : ((term1 A B g f) = (term2 A B g)) = ((term1 A B g f) = (term3 A B g)).
Proof. exact (MK_COMB (@lem9181 A B g f) (@lem9180 A B g)). Qed.
Lemma lem9183 {A B : Type'} (f : A -> B) (g : A -> B) : (term1 A B g f) = (term5 A B f g).
Proof. exact (eq_refl (term1 A B g f)). Qed.
Lemma lem9184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9185 {A B : Type'} (f : A -> B) (g : A -> B) : (term4 A B g f) = (term6 A B f g).
Proof. exact (MK_COMB (@lem9184) (@lem9183 A B f g)). Qed.
Lemma lem9186 {A B : Type'} (g : A -> B) : (term3 A B g) = (term3 A B g).
Proof. exact (eq_refl (term3 A B g)). Qed.
Lemma lem9187 {A B : Type'} (f : A -> B) (g : A -> B) : ((term1 A B g f) = (term3 A B g)) = ((term5 A B f g) = (term3 A B g)).
Proof. exact (MK_COMB (@lem9185 A B f g) (@lem9186 A B g)). Qed.
Lemma lem9188 {A B : Type'} (f : A -> B) (g : A -> B) : ((term1 A B g f) = (term2 A B g)) = ((term5 A B f g) = (term3 A B g)).
Proof. exact (TRANS (@lem9182 A B f g) (@lem9187 A B f g)). Qed.
Lemma lem9189 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : f = g) : (term5 A B f g) = (term3 A B g).
Proof. exact (EQ_MP (@lem9188 A B f g) (@lem9179 A B f g h1)). Qed.
Lemma lem9190 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : f = g) : (term3 A B g) = (term5 A B f g).
Proof. exact (SYM (@lem9189 A B f g h1)). Qed.
Lemma lem9191 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem9196 {A B : Type'} (g : A -> B) : term3 A B g.
Proof. exact (fun x : A => @lem9191 A B g x). Qed.
Lemma lem9197 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : f = g) : term5 A B f g.
Proof. exact (EQ_MP (@lem9190 A B f g h1) (@lem9196 A B g)). Qed.
Lemma lem9198 {A B : Type'} (f : A -> B) (g : A -> B) : term7 A B f g.
Proof. exact (fun h0 : f = g => @lem9197 A B f g h0). Qed.
Lemma lem9199 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (@lem9176 A B f). Qed.
Lemma lem9200 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (eq_refl (term8 A B f)). Qed.
Lemma lem9201 {A B : Type'} (f : A -> B) : term9 A B f.
Proof. exact (EQ_MP (@lem9200 A B f) (@lem9199 A B f)). Qed.
Lemma lem9202 {A B : Type'} (f : A -> B) (g : A -> B) : term10 A B f g.
Proof. exact (@lem9201 A B f g). Qed.
Lemma lem9203 {A B : Type'} (f : A -> B) (g : A -> B) : (term10 A B f g) = (term11 A B f g).
Proof. exact (eq_refl (term10 A B f g)). Qed.
Lemma lem9206 {A B : Type'} (f : A -> B) (g : A -> B) : term11 A B f g.
Proof. exact (EQ_MP (@lem9203 A B f g) (@lem9202 A B f g)). Qed.
Lemma lem9207 {A B : Type'} (f : A -> B) (g : A -> B) : term11 A B f g.
Proof. exact (@lem9206 A B f g). Qed.
Lemma lem9208 {A B : Type'} (f : A -> B) (g : A -> B) : term12 A B f g.
Proof. exact (conj (@lem9198 A B f g) (@lem9207 A B f g)). Qed.
Lemma lem9209 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = ((f = g) = (term5 A B f g)).
Proof. exact (@lem32 (f = g) (term5 A B f g)). Qed.
Lemma lem9210 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term5 A B f g).
Proof. exact (EQ_MP (@lem9209 A B f g) (@lem9208 A B f g)). Qed.
Lemma lem9215 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (fun g : A -> B => @lem9210 A B f g). Qed.
Lemma lem9220 {A B : Type'} : term14 A B.
Proof. exact (fun f : A -> B => @lem9215 A B f). Qed.
