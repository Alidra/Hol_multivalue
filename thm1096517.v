Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096517_term_abbrevs.
Require Import thm1096118_spec.
Require Import thm1096470_spec.
Lemma lem1096471 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1096472 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1096471 A) (@lem1096118 A)). Qed.
Lemma lem1096473 {A : Type'} : term2 A.
Proof. exact (@lem1096472 A term3). Qed.
Lemma lem1096474 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1096475 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1096474 A) (@lem1096473 A)). Qed.
Lemma lem1096476 {A : Type'} (h1 : (@List.rev A) = (term5 A)) : (@List.rev A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1096477 {A : Type'} (h1 : (@List.rev A) = (term5 A)) : (term5 A) = (@List.rev A).
Proof. exact (SYM (@lem1096476 A h1)). Qed.
Lemma lem1096478 {A : Type'} (h1 : (term5 A) = (@List.rev A)) : (term5 A) = (@List.rev A).
Proof. exact (h1). Qed.
Lemma lem1096479 {A : Type'} (h1 : (term5 A) = (@List.rev A)) : (@List.rev A) = (term5 A).
Proof. exact (SYM (@lem1096478 A h1)). Qed.
Lemma lem1096480 {A : Type'} : ((@List.rev A) = (term5 A)) = ((term5 A) = (@List.rev A)).
Proof. exact (prop_ext (fun h1 : (@List.rev A) = (term5 A) => @lem1096477 A h1) (fun h1 : (term5 A) = (@List.rev A) => @lem1096479 A h1)). Qed.
Lemma lem1096483 {A : Type'} : (term5 A) = (@List.rev A).
Proof. exact (EQ_MP (@lem1096480 A) (@lem1096470 A)). Qed.
Lemma lem1096484 {A : Type'} : (term5 A) = (@List.rev A).
Proof. exact (@lem1096483 A). Qed.
Lemma lem1096485 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1096486 {A : Type'} : (term6 A) = (@List.rev A (@nil A)).
Proof. exact (MK_COMB (@lem1096484 A) (@lem1096485 A)). Qed.
Lemma lem1096487 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1096488 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem1096487 A) (@lem1096486 A)). Qed.
Lemma lem1096489 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1096490 {A : Type'} : ((term6 A) = (@nil A)) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (MK_COMB (@lem1096488 A) (@lem1096489 A)). Qed.
Lemma lem1096491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1096492 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem1096491) (@lem1096490 A)). Qed.
Lemma lem1096494 {A : Type'} : (term5 A) = (@List.rev A).
Proof. exact (EQ_MP (@lem1096480 A) (@lem1096470 A)). Qed.
Lemma lem1096495 {A : Type'} : (term5 A) = (@List.rev A).
Proof. exact (@lem1096494 A). Qed.
Lemma lem1096496 {A : Type'} (x : A) (l : list A) : (@cons A x l) = (@cons A x l).
Proof. exact (eq_refl (@cons A x l)). Qed.
Lemma lem1096497 {A : Type'} (x : A) (l : list A) : (term11 A x l) = (term12 A x l).
Proof. exact (MK_COMB (@lem1096495 A) (@lem1096496 A x l)). Qed.
Lemma lem1096498 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1096499 {A : Type'} (x : A) (l : list A) : (term13 A x l) = (term14 A x l).
Proof. exact (MK_COMB (@lem1096498 A) (@lem1096497 A x l)). Qed.
Lemma lem1096501 {A : Type'} : (term5 A) = (@List.rev A).
Proof. exact (EQ_MP (@lem1096480 A) (@lem1096470 A)). Qed.
Lemma lem1096502 {A : Type'} : (term5 A) = (@List.rev A).
Proof. exact (@lem1096501 A). Qed.
Lemma lem1096503 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1096504 {A : Type'} (l : list A) : (term15 A l) = (@List.rev A l).
Proof. exact (MK_COMB (@lem1096502 A) (@lem1096503 A l)). Qed.
Lemma lem1096505 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1096506 {A : Type'} (l : list A) : (term16 A l) = (term17 A l).
Proof. exact (MK_COMB (@lem1096505 A) (@lem1096504 A l)). Qed.
Lemma lem1096507 {A : Type'} (x : A) : (@cons A x (@nil A)) = (@cons A x (@nil A)).
Proof. exact (eq_refl (@cons A x (@nil A))). Qed.
Lemma lem1096508 {A : Type'} (l : list A) (x : A) : (term18 A l x) = (term19 A l x).
Proof. exact (MK_COMB (@lem1096506 A l) (@lem1096507 A x)). Qed.
Lemma lem1096509 {A : Type'} (l : list A) (x : A) : ((term11 A x l) = (term18 A l x)) = ((term12 A x l) = (term19 A l x)).
Proof. exact (MK_COMB (@lem1096499 A x l) (@lem1096508 A l x)). Qed.
Lemma lem1096510 {A : Type'} (l : list A) : (term20 A l) = (term21 A l).
Proof. exact (fun_ext (fun x : A => @lem1096509 A l x)). Qed.
Lemma lem1096511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1096512 {A : Type'} (l : list A) : (term22 A l) = (term23 A l).
Proof. exact (MK_COMB (@lem1096511 A) (@lem1096510 A l)). Qed.
Lemma lem1096513 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (fun_ext (fun l : list A => @lem1096512 A l)). Qed.
Lemma lem1096514 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1096515 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem1096514 A) (@lem1096513 A)). Qed.
Lemma lem1096516 {A : Type'} : (term4 A) = (term28 A).
Proof. exact (MK_COMB (@lem1096492 A) (@lem1096515 A)). Qed.
Lemma lem1096517 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem1096516 A) (@lem1096475 A)). Qed.
