Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183558_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3183065_spec.
Require Import thm3183066_spec.
Lemma lem3183521 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : (@SETSPEC _83031 v P t) = (term0 _83031 P v t).
Proof. exact (EQ_MP (@lem3183066 _83031 P v t) (@lem3183065 _83031 P v t)). Qed.
Lemma lem3183522 {_83123 : Type'} (P : Prop) (v : _83123) (t : _83123) : (@SETSPEC _83123 v P t) = (term0 _83123 P v t).
Proof. exact (@lem3183521 _83123 P v t). Qed.
Lemma lem3183523 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (@SETSPEC _83123 x' x x'') = (term0 _83123 x x' x'').
Proof. exact (@lem3183522 _83123 x x' x''). Qed.
Lemma lem3183528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183529 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term1 _83123 x' x x'') = (term2 _83123 x x' x'').
Proof. exact (MK_COMB (@lem3183528) (@lem3183523 _83123 x x' x'')). Qed.
Lemma lem3183534 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term0 _83123 x x' x'') = (term0 _83123 x x' x'').
Proof. exact (eq_refl (term0 _83123 x x' x'')). Qed.
Lemma lem3183535 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : ((@SETSPEC _83123 x' x x'') = (term0 _83123 x x' x'')) = ((term0 _83123 x x' x'') = (term0 _83123 x x' x'')).
Proof. exact (MK_COMB (@lem3183529 _83123 x x' x'') (@lem3183534 _83123 x x' x'')). Qed.
Lemma lem3183537 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3183538 (x : Prop) : (x = x) = True.
Proof. exact (@lem3183537 Prop x). Qed.
Lemma lem3183539 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : ((term0 _83123 x x' x'') = (term0 _83123 x x' x'')) = True.
Proof. exact (@lem3183538 (term0 _83123 x x' x'')). Qed.
Lemma lem3183540 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : ((@SETSPEC _83123 x' x x'') = (term0 _83123 x x' x'')) = True.
Proof. exact (TRANS (@lem3183535 _83123 x x' x'') (@lem3183539 _83123 x x' x'')). Qed.
Lemma lem3183541 {_83123 : Type'} (x : Prop) (x' : _83123) : (term3 _83123 x x') = (term4 _83123).
Proof. exact (fun_ext (fun x'' : _83123 => @lem3183540 _83123 x x' x'')). Qed.
Lemma lem3183542 {_83123 : Type'} : (@all _83123) = (@all _83123).
Proof. exact (eq_refl (@all _83123)). Qed.
Lemma lem3183543 {_83123 : Type'} (x : Prop) (x' : _83123) : (term5 _83123 x x') = (term6 _83123).
Proof. exact (MK_COMB (@lem3183542 _83123) (@lem3183541 _83123 x x')). Qed.
Lemma lem3183545 {A : Type'} (t : Prop) : (term7 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3183546 {_83123 : Type'} (t : Prop) : (term7 _83123 t) = t.
Proof. exact (@lem3183545 _83123 t). Qed.
Lemma lem3183547 {_83123 : Type'} : (term6 _83123) = True.
Proof. exact (@lem3183546 _83123 True). Qed.
Lemma lem3183548 {_83123 : Type'} (x : Prop) (x' : _83123) : (term5 _83123 x x') = True.
Proof. exact (TRANS (@lem3183543 _83123 x x') (@lem3183547 _83123)). Qed.
Lemma lem3183549 {_83123 : Type'} (x : _83123) : (term8 _83123 x) = term9.
Proof. exact (fun_ext (fun x' : Prop => @lem3183548 _83123 x' x)). Qed.
Lemma lem3183550 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3183551 {_83123 : Type'} (x : _83123) : (term10 _83123 x) = term11.
Proof. exact (MK_COMB (@lem3183550) (@lem3183549 _83123 x)). Qed.
Lemma lem3183553 {A : Type'} (t : Prop) : (term7 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3183554 (t : Prop) : (term12 t) = t.
Proof. exact (@lem3183553 Prop t). Qed.
Lemma lem3183555 : term11 = True.
Proof. exact (@lem3183554 True). Qed.
Lemma lem3183556 {_83123 : Type'} (x : _83123) : (term10 _83123 x) = True.
Proof. exact (TRANS (@lem3183551 _83123 x) (@lem3183555)). Qed.
Lemma lem3183557 {_83123 : Type'} (x : _83123) : True = (term10 _83123 x).
Proof. exact (SYM (@lem3183556 _83123 x)). Qed.
Lemma lem3183558 {_83123 : Type'} (x : _83123) : term10 _83123 x.
Proof. exact (EQ_MP (@lem3183557 _83123 x) (@lem0)). Qed.
