Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637176_term_abbrevs.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Lemma lem7637149 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7637150 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem7637149 A B h1 f). Qed.
Lemma lem7637151 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7637152 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem7637151 A B f) (@lem7637150 A B f h1)). Qed.
Lemma lem7637153 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem7637152 A B f h1 s). Qed.
Lemma lem7637154 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem7637155 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem7637154 A B f s) (@lem7637153 A B f s h1)). Qed.
Lemma lem7637156 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term5 A B f s n.
Proof. exact (@lem7637155 A B f s h1 n). Qed.
Lemma lem7637157 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem7637158 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (EQ_MP (@lem7637157 A B f s n) (@lem7637156 A B f s n h1)). Qed.
Lemma lem7637159 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term7 A B f s n.
Proof. exact (h1). Qed.
Lemma lem7637160 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem7637158 A B f s n h1 (@lem7637159 A B f s n h2)). Qed.
Lemma lem7637161 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term9 A B f s n.
Proof. exact (fun h0 : term0 A B => @lem7637160 A B f s n h0 h1). Qed.
Lemma lem7637162 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7637163 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem7637161 A B f s n h2 (@lem7637162 A B h1)). Qed.
Lemma lem7637164 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (fun h0 : term7 A B f s n => @lem7637163 A B f s n h1 h0). Qed.
Lemma lem7637165 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun n : nat => @lem7637164 A B f s n h1). Qed.
Lemma lem7637166 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem7637165 A B f s h1). Qed.
Lemma lem7637167 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem7637166 A B f h1). Qed.
Lemma lem7637168 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term0 A B => @lem7637167 A B h0). Qed.
Lemma lem7637169 {A B : Type'} : term0 A B.
Proof. exact (@lem7637168 A B (@lem4004559 A B)). Qed.
Lemma lem7637170 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem7637169 A B f). Qed.
Lemma lem7637171 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7637172 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem7637171 A B f) (@lem7637170 A B f)). Qed.
Lemma lem7637173 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem7637172 A B f s). Qed.
Lemma lem7637174 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem7637175 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem7637174 A B f s) (@lem7637173 A B f s)). Qed.
Lemma lem7637176 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term5 A B f s n.
Proof. exact (@lem7637175 A B f s n). Qed.
