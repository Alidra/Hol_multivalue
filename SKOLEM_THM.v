Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SKOLEM_THM_term_abbrevs.
Require Import thm32_spec.
Require Import thm9425_spec.
Lemma lem13490 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term0 A B P.
Proof. exact (h1). Qed.
Lemma lem13491 {A B : Type'} (P : type1413 A B) (h1 : term1 A B P) : term1 A B P.
Proof. exact (h1). Qed.
Lemma lem13492 {A B : Type'} (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term2 A B P y.
Proof. exact (h1). Qed.
Lemma lem13493 {A B : Type'} (P : type1413 A B) (x : A) : (term3 A B P x) = (term4 A B P x).
Proof. exact (eq_refl (term3 A B P x)). Qed.
Lemma lem13494 {A B : Type'} (P : type1413 A B) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem13495 {A B : Type'} (P : type1413 A B) (x : A) : (term5 A B P x) = (term6 A B P x).
Proof. exact (MK_COMB (@lem13494 A B P x) (@lem13493 A B P x)). Qed.
Lemma lem13496 {A B : Type'} (P : type1413 A B) (x : A) : (term6 A B P x) = (term5 A B P x).
Proof. exact (SYM (@lem13495 A B P x)). Qed.
Lemma lem13497 {B : Type'} (P : B -> Prop) : (term7 B P) = (ex P).
Proof. exact (@lem9425 B P). Qed.
Lemma lem13498 {A B : Type'} (P : type1413 A B) (x : A) : (term8 A B P x) = (term9 A B P x).
Proof. exact (@lem13497 B (term10 A B P x)). Qed.
Lemma lem13499 {A B : Type'} (P : type1413 A B) (x : A) : (term8 A B P x) = (term6 A B P x).
Proof. exact (eq_refl (term8 A B P x)). Qed.
Lemma lem13500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13501 {A B : Type'} (P : type1413 A B) (x : A) : (term11 A B P x) = (term12 A B P x).
Proof. exact (MK_COMB (@lem13500) (@lem13499 A B P x)). Qed.
Lemma lem13502 {A B : Type'} (P : type1413 A B) (x : A) : (term9 A B P x) = (term9 A B P x).
Proof. exact (eq_refl (term9 A B P x)). Qed.
Lemma lem13503 {A B : Type'} (P : type1413 A B) (x : A) : ((term8 A B P x) = (term9 A B P x)) = ((term6 A B P x) = (term9 A B P x)).
Proof. exact (MK_COMB (@lem13501 A B P x) (@lem13502 A B P x)). Qed.
Lemma lem13504 {A B : Type'} (P : type1413 A B) (x : A) : (term6 A B P x) = (term9 A B P x).
Proof. exact (EQ_MP (@lem13503 A B P x) (@lem13498 A B P x)). Qed.
Lemma lem13505 {A B : Type'} (P : type1413 A B) (x : A) : (term9 A B P x) = (term6 A B P x).
Proof. exact (SYM (@lem13504 A B P x)). Qed.
Lemma lem13506 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term0 A B P) : term13 A B P x.
Proof. exact (@lem13490 A B P h1 x). Qed.
Lemma lem13507 {A B : Type'} (P : type1413 A B) (x : A) : (term13 A B P x) = (term9 A B P x).
Proof. exact (eq_refl (term13 A B P x)). Qed.
Lemma lem13510 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term0 A B P) : term9 A B P x.
Proof. exact (EQ_MP (@lem13507 A B P x) (@lem13506 A B x P h1)). Qed.
Lemma lem13511 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term0 A B P) : term9 A B P x.
Proof. exact (@lem13510 A B x P h1). Qed.
Lemma lem13512 {A B : Type'} (x : A) (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term14 A B P y x.
Proof. exact (@lem13492 A B P y h1 x). Qed.
Lemma lem13513 {A B : Type'} (P : type1413 A B) (y : A -> B) (x : A) : (term14 A B P y x) = (term15 A B P y x).
Proof. exact (eq_refl (term14 A B P y x)). Qed.
Lemma lem13516 {A B : Type'} (x : A) (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term15 A B P y x.
Proof. exact (EQ_MP (@lem13513 A B P y x) (@lem13512 A B x P y h1)). Qed.
Lemma lem13517 {A B : Type'} (x : A) (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term15 A B P y x.
Proof. exact (@lem13516 A B x P y h1). Qed.
Lemma lem13518 {A B : Type'} (x : A) (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term9 A B P x.
Proof. exact (ex_intro (term10 A B P x) (y x) (@lem13517 A B x P y h1)). Qed.
Lemma lem13519 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term0 A B P) : term6 A B P x.
Proof. exact (EQ_MP (@lem13505 A B P x) (@lem13511 A B x P h1)). Qed.
Lemma lem13520 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term0 A B P) : term5 A B P x.
Proof. exact (EQ_MP (@lem13496 A B P x) (@lem13519 A B x P h1)). Qed.
Lemma lem13525 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term16 A B P.
Proof. exact (fun x : A => @lem13520 A B x P h1). Qed.
Lemma lem13526 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term1 A B P.
Proof. exact (ex_intro (term17 A B P) (term18 A B P) (@lem13525 A B P h1)). Qed.
Lemma lem13531 {A B : Type'} (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term0 A B P.
Proof. exact (fun x : A => @lem13518 A B x P y h1). Qed.
Lemma lem13532 {A B : Type'} (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : (term2 A B P y) = (term0 A B P).
Proof. exact (prop_ext (fun h2 : term2 A B P y => @lem13531 A B P y h1) (fun h2 : term0 A B P => @lem13492 A B P y h1)). Qed.
Lemma lem13533 {A B : Type'} (P : type1413 A B) (y : A -> B) (h1 : term2 A B P y) : term0 A B P.
Proof. exact (EQ_MP (@lem13532 A B P y h1) (@lem13492 A B P y h1)). Qed.
Lemma lem13534 {A B : Type'} (P : type1413 A B) (h1 : term1 A B P) : term0 A B P.
Proof. exact (ex_elim (@lem13491 A B P h1) (fun y : A -> B => fun h0 : term17 A B P y => @lem13533 A B P y h0)). Qed.
Lemma lem13535 {A B : Type'} (P : type1413 A B) : term19 A B P.
Proof. exact (fun h0 : term1 A B P => @lem13534 A B P h0). Qed.
Lemma lem13536 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : (term0 A B P) = (term1 A B P).
Proof. exact (prop_ext (fun h2 : term0 A B P => @lem13526 A B P h1) (fun h2 : term1 A B P => @lem13490 A B P h1)). Qed.
Lemma lem13537 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term1 A B P.
Proof. exact (EQ_MP (@lem13536 A B P h1) (@lem13490 A B P h1)). Qed.
Lemma lem13538 {A B : Type'} (P : type1413 A B) : term20 A B P.
Proof. exact (fun h0 : term0 A B P => @lem13537 A B P h0). Qed.
Lemma lem13539 {A B : Type'} (P : type1413 A B) : term21 A B P.
Proof. exact (conj (@lem13538 A B P) (@lem13535 A B P)). Qed.
Lemma lem13540 {A B : Type'} (P : type1413 A B) : (term21 A B P) = ((term0 A B P) = (term1 A B P)).
Proof. exact (@lem32 (term0 A B P) (term1 A B P)). Qed.
Lemma lem13541 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem13540 A B P) (@lem13539 A B P)). Qed.
Lemma lem13546 {A B : Type'} : term22 A B.
Proof. exact (fun P : type1413 A B => @lem13541 A B P). Qed.
