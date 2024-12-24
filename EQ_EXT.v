Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_EXT_term_abbrevs.
Require Import ETA_AX_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Lemma lem9128 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem9129 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem9130 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem9129 A B t) (@lem9128 A B t)). Qed.
Lemma lem9131 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term2 A B f g) : term2 A B f g.
Proof. exact (h1). Qed.
Lemma lem9132 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (h1 : term2 A B f g) : term3 A B f g x.
Proof. exact (@lem9131 A B f g h1 x). Qed.
Lemma lem9133 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term3 A B f g x) = ((f x) = (g x)).
Proof. exact (eq_refl (term3 A B f g x)). Qed.
Lemma lem9134 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (h1 : term2 A B f g) : (f x) = (g x).
Proof. exact (EQ_MP (@lem9133 A B f g x) (@lem9132 A B x f g h1)). Qed.
Lemma lem9135 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term2 A B f g) : (term1 A B f) = (term1 A B g).
Proof. exact (fun_ext (fun x : A => @lem9134 A B x f g h1)). Qed.
Lemma lem9142 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (@lem9130 A B t). Qed.
Lemma lem9143 {A B : Type'} (f : A -> B) : (term1 A B f) = f.
Proof. exact (@lem9142 A B f). Qed.
Lemma lem9144 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem9145 {A B : Type'} (f : A -> B) : (term4 A B f) = (@eq (A -> B) f).
Proof. exact (MK_COMB (@lem9144 A B) (@lem9143 A B f)). Qed.
Lemma lem9146 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (@lem9130 A B t). Qed.
Lemma lem9147 {A B : Type'} (g : A -> B) : (term1 A B g) = g.
Proof. exact (@lem9146 A B g). Qed.
Lemma lem9148 {A B : Type'} (f : A -> B) (g : A -> B) : ((term1 A B f) = (term1 A B g)) = (f = g).
Proof. exact (MK_COMB (@lem9145 A B f) (@lem9147 A B g)). Qed.
Lemma lem9151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem9152 {A B : Type'} (f : A -> B) (g : A -> B) : (term5 A B f g) = (term6 A B f g).
Proof. exact (MK_COMB (@lem9151) (@lem9148 A B f g)). Qed.
Lemma lem9155 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem9156 {A B : Type'} (f : A -> B) (g : A -> B) : (term7 A B f g) = (term8 A B f g).
Proof. exact (MK_COMB (@lem9152 A B f g) (@lem9155 A B f g)). Qed.
Lemma lem9160 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem9161 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = True.
Proof. exact (@lem9160 (f = g)). Qed.
Lemma lem9162 {A B : Type'} (f : A -> B) (g : A -> B) : (term7 A B f g) = True.
Proof. exact (TRANS (@lem9156 A B f g) (@lem9161 A B f g)). Qed.
Lemma lem9163 {A B : Type'} (f : A -> B) (g : A -> B) : True = (term7 A B f g).
Proof. exact (SYM (@lem9162 A B f g)). Qed.
Lemma lem9164 {A B : Type'} (f : A -> B) (g : A -> B) : term7 A B f g.
Proof. exact (EQ_MP (@lem9163 A B f g) (@lem0)). Qed.
Lemma lem9165 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term2 A B f g) : f = g.
Proof. exact (@lem9164 A B f g (@lem9135 A B f g h1)). Qed.
Lemma lem9166 {A B : Type'} (f : A -> B) (g : A -> B) : term9 A B f g.
Proof. exact (fun h0 : term2 A B f g => @lem9165 A B f g h0). Qed.
Lemma lem9171 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (fun g : A -> B => @lem9166 A B f g). Qed.
Lemma lem9176 {A B : Type'} : term11 A B.
Proof. exact (fun f : A -> B => @lem9171 A B f). Qed.
