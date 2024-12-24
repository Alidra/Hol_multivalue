Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import one_axiom_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import one_spec.
Lemma lem15882 (v : unit) : term0 v.
Proof. exact (@lem15881 v). Qed.
Lemma lem15883 (v : unit) : (term0 v) = (v = tt).
Proof. exact (eq_refl (term0 v)). Qed.
Lemma lem15885 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem15886 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem15887 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem15886 A B f) (@lem15885 A B f)). Qed.
Lemma lem15888 {A B : Type'} (f : A -> B) (g : A -> B) : term3 A B f g.
Proof. exact (@lem15887 A B f g). Qed.
Lemma lem15889 {A B : Type'} (f : A -> B) (g : A -> B) : (term3 A B f g) = ((f = g) = (term4 A B f g)).
Proof. exact (eq_refl (term3 A B f g)). Qed.
Lemma lem15894 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term4 A B f g).
Proof. exact (EQ_MP (@lem15889 A B f g) (@lem15888 A B f g)). Qed.
Lemma lem15895 {A : Type'} (f : A -> unit) (g : A -> unit) : (f = g) = (term5 A f g).
Proof. exact (@lem15894 A unit f g). Qed.
Lemma lem15896 {A : Type'} (f : A -> unit) (g : A -> unit) : (term5 A f g) = (f = g).
Proof. exact (SYM (@lem15895 A f g)). Qed.
Lemma lem15906 (v : unit) : v = tt.
Proof. exact (EQ_MP (@lem15883 v) (@lem15882 v)). Qed.
Lemma lem15907 {A : Type'} (f : A -> unit) (x : A) : (f x) = tt.
Proof. exact (@lem15906 (f x)). Qed.
Lemma lem15908 : (@eq unit) = (@eq unit).
Proof. exact (eq_refl (@eq unit)). Qed.
Lemma lem15909 {A : Type'} (f : A -> unit) (x : A) : (term6 A f x) = (@eq unit tt).
Proof. exact (MK_COMB (@lem15908) (@lem15907 A f x)). Qed.
Lemma lem15911 (v : unit) : v = tt.
Proof. exact (EQ_MP (@lem15883 v) (@lem15882 v)). Qed.
Lemma lem15912 {A : Type'} (g : A -> unit) (x : A) : (g x) = tt.
Proof. exact (@lem15911 (g x)). Qed.
Lemma lem15913 {A : Type'} (f : A -> unit) (g : A -> unit) (x : A) : ((f x) = (g x)) = (tt = tt).
Proof. exact (MK_COMB (@lem15909 A f x) (@lem15912 A g x)). Qed.
Lemma lem15914 {A : Type'} (f : A -> unit) (g : A -> unit) (x : A) : (tt = tt) = ((f x) = (g x)).
Proof. exact (SYM (@lem15913 A f g x)). Qed.
Lemma lem15915 : tt = tt.
Proof. exact (eq_refl tt). Qed.
Lemma lem15916 {A : Type'} (f : A -> unit) (g : A -> unit) (x : A) : (f x) = (g x).
Proof. exact (EQ_MP (@lem15914 A f g x) (@lem15915)). Qed.
Lemma lem15921 {A : Type'} (f : A -> unit) (g : A -> unit) : term5 A f g.
Proof. exact (fun x : A => @lem15916 A f g x). Qed.
Lemma lem15922 {A : Type'} (f : A -> unit) (g : A -> unit) : f = g.
Proof. exact (EQ_MP (@lem15896 A f g) (@lem15921 A f g)). Qed.
Lemma lem15927 {A : Type'} (f : A -> unit) : term7 A f.
Proof. exact (fun g : A -> unit => @lem15922 A f g). Qed.
Lemma lem15932 {A : Type'} : term8 A.
Proof. exact (fun f : A -> unit => @lem15927 A f). Qed.
