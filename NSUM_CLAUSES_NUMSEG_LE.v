Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLAUSES_NUMSEG_LE_term_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_LE_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Lemma lem7047418 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) : term0 _123593 f op.
Proof. exact (@lem6198343 _123593 f op). Qed.
Lemma lem7047419 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term0 _123593 f op) = (term1 _123593 op f).
Proof. exact (eq_refl (term0 _123593 f op)). Qed.
Lemma lem7047422 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : term1 _123593 op f.
Proof. exact (EQ_MP (@lem7047419 _123593 op f) (@lem7047418 _123593 f op)). Qed.
Lemma lem7047423 (op : type1606) (f : nat -> nat) : term2 op f.
Proof. exact (@lem7047422 nat op f). Qed.
Lemma lem7047424 (f : nat -> nat) : term3 f.
Proof. exact (@lem7047423 Nat.add f). Qed.
Lemma lem7047425 (f : nat -> nat) : term4 f.
Proof. exact (@lem7047424 f (@lem6924403)). Qed.
Lemma lem7047455 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047456 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047455 nat). Qed.
Lemma lem7047461 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem7047462 : term6 = term7.
Proof. exact (MK_COMB (@lem7047456) (@lem7047461)). Qed.
Lemma lem7047463 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047464 (f : nat -> nat) : (term8 f) = (term9 f).
Proof. exact (MK_COMB (@lem7047462) (@lem7047463 f)). Qed.
Lemma lem7047465 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047466 (f : nat -> nat) : (term10 f) = (term11 f).
Proof. exact (MK_COMB (@lem7047465) (@lem7047464 f)). Qed.
Lemma lem7047467 (f : nat -> nat) : (term12 f) = (term12 f).
Proof. exact (eq_refl (term12 f)). Qed.
Lemma lem7047468 (f : nat -> nat) : ((term8 f) = (term12 f)) = ((term9 f) = (term12 f)).
Proof. exact (MK_COMB (@lem7047466 f) (@lem7047467 f)). Qed.
Lemma lem7047471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047472 (f : nat -> nat) : (term13 f) = (term14 f).
Proof. exact (MK_COMB (@lem7047471) (@lem7047468 f)). Qed.
Lemma lem7047480 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047481 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047480 nat). Qed.
Lemma lem7047486 (k : nat) : (term15 k) = (term15 k).
Proof. exact (eq_refl (term15 k)). Qed.
Lemma lem7047487 (k : nat) : (term16 k) = (term17 k).
Proof. exact (MK_COMB (@lem7047481) (@lem7047486 k)). Qed.
Lemma lem7047488 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047489 (k : nat) (f : nat -> nat) : (term18 k f) = (term19 k f).
Proof. exact (MK_COMB (@lem7047487 k) (@lem7047488 f)). Qed.
Lemma lem7047490 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047491 (k : nat) (f : nat -> nat) : (term20 k f) = (term21 k f).
Proof. exact (MK_COMB (@lem7047490) (@lem7047489 k f)). Qed.
Lemma lem7047493 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047494 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047493 nat). Qed.
Lemma lem7047499 (k : nat) : (term22 k) = (term22 k).
Proof. exact (eq_refl (term22 k)). Qed.
Lemma lem7047500 (k : nat) : (term23 k) = (term24 k).
Proof. exact (MK_COMB (@lem7047494) (@lem7047499 k)). Qed.
Lemma lem7047501 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047502 (k : nat) (f : nat -> nat) : (term25 k f) = (term26 k f).
Proof. exact (MK_COMB (@lem7047500 k) (@lem7047501 f)). Qed.
Lemma lem7047503 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7047504 (k : nat) (f : nat -> nat) : (term27 k f) = (term28 k f).
Proof. exact (MK_COMB (@lem7047503) (@lem7047502 k f)). Qed.
Lemma lem7047505 (f : nat -> nat) (k : nat) : (term29 f k) = (term29 f k).
Proof. exact (eq_refl (term29 f k)). Qed.
Lemma lem7047506 (f : nat -> nat) (k : nat) : (term30 f k) = (term31 f k).
Proof. exact (MK_COMB (@lem7047504 k f) (@lem7047505 f k)). Qed.
Lemma lem7047507 (f : nat -> nat) (k : nat) : ((term18 k f) = (term30 f k)) = ((term19 k f) = (term31 f k)).
Proof. exact (MK_COMB (@lem7047491 k f) (@lem7047506 f k)). Qed.
Lemma lem7047510 (f : nat -> nat) : (term32 f) = (term33 f).
Proof. exact (fun_ext (fun k : nat => @lem7047507 f k)). Qed.
Lemma lem7047511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047512 (f : nat -> nat) : (term34 f) = (term35 f).
Proof. exact (MK_COMB (@lem7047511) (@lem7047510 f)). Qed.
Lemma lem7047517 (f : nat -> nat) : (term36 f) = (term4 f).
Proof. exact (MK_COMB (@lem7047472 f) (@lem7047512 f)). Qed.
Lemma lem7047520 (f : nat -> nat) : (term37 f) = (term37 f).
Proof. exact (eq_refl (term37 f)). Qed.
Lemma lem7047521 (f : nat -> nat) : (term38 f) = (term39 f).
Proof. exact (MK_COMB (@lem7047520 f) (@lem7047517 f)). Qed.
Lemma lem7047523 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7047524 (f : nat -> nat) : (term39 f) = True.
Proof. exact (@lem7047523 (term4 f)). Qed.
Lemma lem7047527 (f : nat -> nat) : (term40 f) = (term40 f).
Proof. exact (eq_refl (term40 f)). Qed.
Lemma lem7047528 (f : nat -> nat) : (term40 f) = ((term39 f) = True).
Proof. exact (eq_refl (term40 f)). Qed.
Lemma lem7047529 (f : nat -> nat) : (term41 f) = (term41 f).
Proof. exact (eq_refl (term41 f)). Qed.
Lemma lem7047530 (f : nat -> nat) : ((term40 f) = (term40 f)) = ((term40 f) = ((term39 f) = True)).
Proof. exact (MK_COMB (@lem7047529 f) (@lem7047528 f)). Qed.
Lemma lem7047531 (f : nat -> nat) : (term40 f) = ((term39 f) = True).
Proof. exact (eq_refl (term40 f)). Qed.
Lemma lem7047532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7047533 (f : nat -> nat) : (term41 f) = (term42 f).
Proof. exact (MK_COMB (@lem7047532) (@lem7047531 f)). Qed.
Lemma lem7047534 (f : nat -> nat) : ((term39 f) = True) = ((term39 f) = True).
Proof. exact (eq_refl ((term39 f) = True)). Qed.
Lemma lem7047535 (f : nat -> nat) : ((term40 f) = ((term39 f) = True)) = (((term39 f) = True) = ((term39 f) = True)).
Proof. exact (MK_COMB (@lem7047533 f) (@lem7047534 f)). Qed.
Lemma lem7047536 (f : nat -> nat) : ((term40 f) = (term40 f)) = (((term39 f) = True) = ((term39 f) = True)).
Proof. exact (TRANS (@lem7047530 f) (@lem7047535 f)). Qed.
Lemma lem7047537 (f : nat -> nat) : ((term39 f) = True) = ((term39 f) = True).
Proof. exact (EQ_MP (@lem7047536 f) (@lem7047527 f)). Qed.
Lemma lem7047538 (f : nat -> nat) : (term39 f) = True.
Proof. exact (EQ_MP (@lem7047537 f) (@lem7047524 f)). Qed.
Lemma lem7047539 (f : nat -> nat) : (term38 f) = True.
Proof. exact (TRANS (@lem7047521 f) (@lem7047538 f)). Qed.
Lemma lem7047540 (f : nat -> nat) : True = (term38 f).
Proof. exact (SYM (@lem7047539 f)). Qed.
Lemma lem7047541 (f : nat -> nat) : term38 f.
Proof. exact (EQ_MP (@lem7047540 f) (@lem0)). Qed.
Lemma lem7047542 (f : nat -> nat) : term36 f.
Proof. exact (@lem7047541 f (@lem7047425 f)). Qed.
