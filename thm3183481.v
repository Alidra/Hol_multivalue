Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183481_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3183065_spec.
Require Import thm3183066_spec.
Lemma lem3183444 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : (@SETSPEC _83031 v P t) = (term0 _83031 P v t).
Proof. exact (EQ_MP (@lem3183066 _83031 P v t) (@lem3183065 _83031 P v t)). Qed.
Lemma lem3183445 {_83064 : Type'} (P : Prop) (v : _83064) (t : _83064) : (@SETSPEC _83064 v P t) = (term0 _83064 P v t).
Proof. exact (@lem3183444 _83064 P v t). Qed.
Lemma lem3183446 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (@SETSPEC _83064 x' x x'') = (term0 _83064 x x' x'').
Proof. exact (@lem3183445 _83064 x x' x''). Qed.
Lemma lem3183451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183452 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term1 _83064 x' x x'') = (term2 _83064 x x' x'').
Proof. exact (MK_COMB (@lem3183451) (@lem3183446 _83064 x x' x'')). Qed.
Lemma lem3183457 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term0 _83064 x x' x'') = (term0 _83064 x x' x'').
Proof. exact (eq_refl (term0 _83064 x x' x'')). Qed.
Lemma lem3183458 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : ((@SETSPEC _83064 x' x x'') = (term0 _83064 x x' x'')) = ((term0 _83064 x x' x'') = (term0 _83064 x x' x'')).
Proof. exact (MK_COMB (@lem3183452 _83064 x x' x'') (@lem3183457 _83064 x x' x'')). Qed.
Lemma lem3183460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3183461 (x : Prop) : (x = x) = True.
Proof. exact (@lem3183460 Prop x). Qed.
Lemma lem3183462 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : ((term0 _83064 x x' x'') = (term0 _83064 x x' x'')) = True.
Proof. exact (@lem3183461 (term0 _83064 x x' x'')). Qed.
Lemma lem3183463 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : ((@SETSPEC _83064 x' x x'') = (term0 _83064 x x' x'')) = True.
Proof. exact (TRANS (@lem3183458 _83064 x x' x'') (@lem3183462 _83064 x x' x'')). Qed.
Lemma lem3183464 {_83064 : Type'} (x : Prop) (x' : _83064) : (term3 _83064 x x') = (term4 _83064).
Proof. exact (fun_ext (fun x'' : _83064 => @lem3183463 _83064 x x' x'')). Qed.
Lemma lem3183465 {_83064 : Type'} : (@all _83064) = (@all _83064).
Proof. exact (eq_refl (@all _83064)). Qed.
Lemma lem3183466 {_83064 : Type'} (x : Prop) (x' : _83064) : (term5 _83064 x x') = (term6 _83064).
Proof. exact (MK_COMB (@lem3183465 _83064) (@lem3183464 _83064 x x')). Qed.
Lemma lem3183468 {A : Type'} (t : Prop) : (term7 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3183469 {_83064 : Type'} (t : Prop) : (term7 _83064 t) = t.
Proof. exact (@lem3183468 _83064 t). Qed.
Lemma lem3183470 {_83064 : Type'} : (term6 _83064) = True.
Proof. exact (@lem3183469 _83064 True). Qed.
Lemma lem3183471 {_83064 : Type'} (x : Prop) (x' : _83064) : (term5 _83064 x x') = True.
Proof. exact (TRANS (@lem3183466 _83064 x x') (@lem3183470 _83064)). Qed.
Lemma lem3183472 {_83064 : Type'} (x : _83064) : (term8 _83064 x) = term9.
Proof. exact (fun_ext (fun x' : Prop => @lem3183471 _83064 x' x)). Qed.
Lemma lem3183473 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3183474 {_83064 : Type'} (x : _83064) : (term10 _83064 x) = term11.
Proof. exact (MK_COMB (@lem3183473) (@lem3183472 _83064 x)). Qed.
Lemma lem3183476 {A : Type'} (t : Prop) : (term7 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3183477 (t : Prop) : (term12 t) = t.
Proof. exact (@lem3183476 Prop t). Qed.
Lemma lem3183478 : term11 = True.
Proof. exact (@lem3183477 True). Qed.
Lemma lem3183479 {_83064 : Type'} (x : _83064) : (term10 _83064 x) = True.
Proof. exact (TRANS (@lem3183474 _83064 x) (@lem3183478)). Qed.
Lemma lem3183480 {_83064 : Type'} (x : _83064) : True = (term10 _83064 x).
Proof. exact (SYM (@lem3183479 _83064 x)). Qed.
Lemma lem3183481 {_83064 : Type'} (x : _83064) : term10 _83064 x.
Proof. exact (EQ_MP (@lem3183480 _83064 x) (@lem0)). Qed.
