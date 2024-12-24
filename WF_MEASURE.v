Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_MEASURE_term_abbrevs.
Require Import MEASURE_spec.
Require Import WF_MEASURE_GEN_spec.
Require Import thm0_spec.
Require Import thm365139_spec.
Lemma lem365418 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem365419 {A B : Type'} (lt2 : type1402 B) (h1 : term0 A B) : term1 A B lt2.
Proof. exact (@lem365418 A B h1 lt2). Qed.
Lemma lem365420 {A B : Type'} (lt2 : type1402 B) : (term1 A B lt2) = (term2 A B lt2).
Proof. exact (eq_refl (term1 A B lt2)). Qed.
Lemma lem365421 {A B : Type'} (lt2 : type1402 B) (h1 : term0 A B) : term2 A B lt2.
Proof. exact (EQ_MP (@lem365420 A B lt2) (@lem365419 A B lt2 h1)). Qed.
Lemma lem365422 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (h1 : term0 A B) : term3 A B lt2 m.
Proof. exact (@lem365421 A B lt2 h1 m). Qed.
Lemma lem365423 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term3 A B lt2 m) = (term4 A B lt2 m).
Proof. exact (eq_refl (term3 A B lt2 m)). Qed.
Lemma lem365424 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (h1 : term0 A B) : term4 A B lt2 m.
Proof. exact (EQ_MP (@lem365423 A B lt2 m) (@lem365422 A B lt2 m h1)). Qed.
Lemma lem365425 {B : Type'} (lt2 : type1402 B) (h1 : @WF B lt2) : @WF B lt2.
Proof. exact (h1). Qed.
Lemma lem365426 {A B : Type'} (m : A -> B) (lt2 : type1402 B) (h1 : term0 A B) (h2 : @WF B lt2) : term5 A B lt2 m.
Proof. exact (@lem365424 A B lt2 m h1 (@lem365425 B lt2 h2)). Qed.
Lemma lem365427 {A B : Type'} (m : A -> B) (lt2 : type1402 B) (h1 : @WF B lt2) : term6 A B lt2 m.
Proof. exact (fun h0 : term0 A B => @lem365426 A B m lt2 h0 h1). Qed.
Lemma lem365428 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem365429 {A B : Type'} (m : A -> B) (lt2 : type1402 B) (h1 : term0 A B) (h2 : @WF B lt2) : term5 A B lt2 m.
Proof. exact (@lem365427 A B m lt2 h2 (@lem365428 A B h1)). Qed.
Lemma lem365430 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (h1 : term0 A B) : term4 A B lt2 m.
Proof. exact (fun h0 : @WF B lt2 => @lem365429 A B m lt2 h1 h0). Qed.
Lemma lem365431 {A B : Type'} (lt2 : type1402 B) (h1 : term0 A B) : term2 A B lt2.
Proof. exact (fun m : A -> B => @lem365430 A B lt2 m h1). Qed.
Lemma lem365432 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun lt2 : type1402 B => @lem365431 A B lt2 h1). Qed.
Lemma lem365433 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term0 A B => @lem365432 A B h0). Qed.
Lemma lem365434 {A B : Type'} : term0 A B.
Proof. exact (@lem365433 A B (@lem361737 A B)). Qed.
Lemma lem365435 {A B : Type'} (lt2 : type1402 B) : term1 A B lt2.
Proof. exact (@lem365434 A B lt2). Qed.
Lemma lem365436 {A B : Type'} (lt2 : type1402 B) : (term1 A B lt2) = (term2 A B lt2).
Proof. exact (eq_refl (term1 A B lt2)). Qed.
Lemma lem365437 {A B : Type'} (lt2 : type1402 B) : term2 A B lt2.
Proof. exact (EQ_MP (@lem365436 A B lt2) (@lem365435 A B lt2)). Qed.
Lemma lem365438 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : term3 A B lt2 m.
Proof. exact (@lem365437 A B lt2 m). Qed.
Lemma lem365439 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term3 A B lt2 m) = (term4 A B lt2 m).
Proof. exact (eq_refl (term3 A B lt2 m)). Qed.
Lemma lem365441 {_16406 : Type'} (m : _16406 -> nat) : term8 _16406 m.
Proof. exact (@lem365417 _16406 m). Qed.
Lemma lem365442 {_16406 : Type'} (m : _16406 -> nat) : (term8 _16406 m) = ((@MEASURE _16406 m) = (term9 _16406 m)).
Proof. exact (eq_refl (term8 _16406 m)). Qed.
Lemma lem365445 {_16406 : Type'} (m : _16406 -> nat) : (@MEASURE _16406 m) = (term9 _16406 m).
Proof. exact (EQ_MP (@lem365442 _16406 m) (@lem365441 _16406 m)). Qed.
Lemma lem365446 {A : Type'} (m : A -> nat) : (@MEASURE A m) = (term9 A m).
Proof. exact (@lem365445 A m). Qed.
Lemma lem365447 {A : Type'} : (@WF A) = (@WF A).
Proof. exact (eq_refl (@WF A)). Qed.
Lemma lem365448 {A : Type'} (m : A -> nat) : (term10 A m) = (term11 A m).
Proof. exact (MK_COMB (@lem365447 A) (@lem365446 A m)). Qed.
Lemma lem365449 {A : Type'} (m : A -> nat) : (term11 A m) = (term10 A m).
Proof. exact (SYM (@lem365448 A m)). Qed.
Lemma lem365451 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : term4 A B lt2 m.
Proof. exact (EQ_MP (@lem365439 A B lt2 m) (@lem365438 A B lt2 m)). Qed.
Lemma lem365452 {A : Type'} (lt2 : type1605) (m : A -> nat) : term12 A lt2 m.
Proof. exact (@lem365451 A nat lt2 m). Qed.
Lemma lem365453 {A : Type'} (m : A -> nat) : term13 A m.
Proof. exact (@lem365452 A Peano.lt m). Qed.
Lemma lem365455 : @WF nat Peano.lt.
Proof. exact (EQ_MP (@lem365139) (@lem0)). Qed.
Lemma lem365456 {A : Type'} (m : A -> nat) : term11 A m.
Proof. exact (@lem365453 A m (@lem365455)). Qed.
Lemma lem365457 {A : Type'} (m : A -> nat) : term10 A m.
Proof. exact (EQ_MP (@lem365449 A m) (@lem365456 A m)). Qed.
Lemma lem365462 {A : Type'} : term14 A.
Proof. exact (fun m : A -> nat => @lem365457 A m). Qed.
