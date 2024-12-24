Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNION_NONZERO_term_abbrevs.
Require Import ITERATE_UNION_NONZERO_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7018471 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7018473 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7018474 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7018473 A B h1 op). Qed.
Lemma lem7018475 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7018476 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7018475 A B op) (@lem7018474 A B op h1)). Qed.
Lemma lem7018477 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7018478 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7018476 A B op h1 (@lem7018477 B op h2)). Qed.
Lemma lem7018479 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7018478 A B op h0 h1). Qed.
Lemma lem7018480 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7018481 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7018479 A B op h2 (@lem7018480 A B h1)). Qed.
Lemma lem7018482 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7018481 A B op h1 h0). Qed.
Lemma lem7018483 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7018482 A B op h1). Qed.
Lemma lem7018484 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7018483 A B h0). Qed.
Lemma lem7018485 {A B : Type'} : term0 A B.
Proof. exact (@lem7018484 A B (@lem6007453 A B)). Qed.
Lemma lem7018486 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7018485 A B op). Qed.
Lemma lem7018487 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7018489 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7018490 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem7018489 h1)). Qed.
Lemma lem7018491 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem7018492 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem7018491 h1)). Qed.
Lemma lem7018493 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem7018490 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem7018492 h1)). Qed.
Lemma lem7018522 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem7018493) (@lem6921993)). Qed.
Lemma lem7018523 {_129614 : Type'} (f : _129614 -> nat) (x : _129614) : (term6 _129614 f x) = (term6 _129614 f x).
Proof. exact (eq_refl (term6 _129614 f x)). Qed.
Lemma lem7018524 {_129614 : Type'} (f : _129614 -> nat) (x : _129614) : ((f x) = (NUMERAL 0)) = ((f x) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem7018523 _129614 f x) (@lem7018522)). Qed.
Lemma lem7018527 {_129614 : Type'} (x : _129614) (s : _129614 -> Prop) (t : _129614 -> Prop) : (term7 _129614 x s t) = (term7 _129614 x s t).
Proof. exact (eq_refl (term7 _129614 x s t)). Qed.
Lemma lem7018528 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (x : _129614) : (term8 _129614 s t f x) = (term9 _129614 s t f x).
Proof. exact (MK_COMB (@lem7018527 _129614 x s t) (@lem7018524 _129614 f x)). Qed.
Lemma lem7018531 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term10 _129614 s t f) = (term11 _129614 s t f).
Proof. exact (fun_ext (fun x : _129614 => @lem7018528 _129614 s t f x)). Qed.
Lemma lem7018532 {_129614 : Type'} : (@all _129614) = (@all _129614).
Proof. exact (eq_refl (@all _129614)). Qed.
Lemma lem7018533 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term12 _129614 s t f) = (term13 _129614 s t f).
Proof. exact (MK_COMB (@lem7018532 _129614) (@lem7018531 _129614 s t f)). Qed.
Lemma lem7018538 {_129614 : Type'} (t : _129614 -> Prop) : (term14 _129614 t) = (term14 _129614 t).
Proof. exact (eq_refl (term14 _129614 t)). Qed.
Lemma lem7018539 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term15 _129614 s t f) = (term16 _129614 s t f).
Proof. exact (MK_COMB (@lem7018538 _129614 t) (@lem7018533 _129614 s t f)). Qed.
Lemma lem7018542 {_129614 : Type'} (s : _129614 -> Prop) : (term14 _129614 s) = (term14 _129614 s).
Proof. exact (eq_refl (term14 _129614 s)). Qed.
Lemma lem7018543 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term17 _129614 s t f) = (term18 _129614 s t f).
Proof. exact (MK_COMB (@lem7018542 _129614 s) (@lem7018539 _129614 s t f)). Qed.
Lemma lem7018546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7018547 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term19 _129614 s t f) = (term20 _129614 s t f).
Proof. exact (MK_COMB (@lem7018546) (@lem7018543 _129614 s t f)). Qed.
Lemma lem7018551 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018552 {_129614 : Type'} : (@nsum _129614) = (@iterate nat _129614 Nat.add).
Proof. exact (@lem7018551 _129614). Qed.
Lemma lem7018553 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) : (@UNION _129614 s t) = (@UNION _129614 s t).
Proof. exact (eq_refl (@UNION _129614 s t)). Qed.
Lemma lem7018554 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) : (term21 _129614 s t) = (term22 _129614 s t).
Proof. exact (MK_COMB (@lem7018552 _129614) (@lem7018553 _129614 s t)). Qed.
Lemma lem7018555 {_129614 : Type'} (f : _129614 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018556 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term23 _129614 s t f) = (term24 _129614 s t f).
Proof. exact (MK_COMB (@lem7018554 _129614 s t) (@lem7018555 _129614 f)). Qed.
Lemma lem7018557 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7018558 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term25 _129614 s t f) = (term26 _129614 s t f).
Proof. exact (MK_COMB (@lem7018557) (@lem7018556 _129614 s t f)). Qed.
Lemma lem7018560 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018561 {_129614 : Type'} : (@nsum _129614) = (@iterate nat _129614 Nat.add).
Proof. exact (@lem7018560 _129614). Qed.
Lemma lem7018562 {_129614 : Type'} (s : _129614 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7018563 {_129614 : Type'} (s : _129614 -> Prop) : (@nsum _129614 s) = (@iterate nat _129614 Nat.add s).
Proof. exact (MK_COMB (@lem7018561 _129614) (@lem7018562 _129614 s)). Qed.
Lemma lem7018564 {_129614 : Type'} (f : _129614 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018565 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) : (@nsum _129614 s f) = (@iterate nat _129614 Nat.add s f).
Proof. exact (MK_COMB (@lem7018563 _129614 s) (@lem7018564 _129614 f)). Qed.
Lemma lem7018566 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7018567 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) : (term27 _129614 s f) = (term28 _129614 s f).
Proof. exact (MK_COMB (@lem7018566) (@lem7018565 _129614 s f)). Qed.
Lemma lem7018569 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018570 {_129614 : Type'} : (@nsum _129614) = (@iterate nat _129614 Nat.add).
Proof. exact (@lem7018569 _129614). Qed.
Lemma lem7018571 {_129614 : Type'} (t : _129614 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7018572 {_129614 : Type'} (t : _129614 -> Prop) : (@nsum _129614 t) = (@iterate nat _129614 Nat.add t).
Proof. exact (MK_COMB (@lem7018570 _129614) (@lem7018571 _129614 t)). Qed.
Lemma lem7018573 {_129614 : Type'} (f : _129614 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018574 {_129614 : Type'} (t : _129614 -> Prop) (f : _129614 -> nat) : (@nsum _129614 t f) = (@iterate nat _129614 Nat.add t f).
Proof. exact (MK_COMB (@lem7018572 _129614 t) (@lem7018573 _129614 f)). Qed.
Lemma lem7018575 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term29 _129614 s t f) = (term30 _129614 s t f).
Proof. exact (MK_COMB (@lem7018567 _129614 s f) (@lem7018574 _129614 t f)). Qed.
Lemma lem7018576 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : ((term23 _129614 s t f) = (term29 _129614 s t f)) = ((term24 _129614 s t f) = (term30 _129614 s t f)).
Proof. exact (MK_COMB (@lem7018558 _129614 s t f) (@lem7018575 _129614 s t f)). Qed.
Lemma lem7018579 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term31 _129614 s t f) = (term32 _129614 s t f).
Proof. exact (MK_COMB (@lem7018547 _129614 s t f) (@lem7018576 _129614 s t f)). Qed.
Lemma lem7018582 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) : (term33 _129614 s f) = (term34 _129614 s f).
Proof. exact (fun_ext (fun t : _129614 -> Prop => @lem7018579 _129614 s t f)). Qed.
Lemma lem7018583 {_129614 : Type'} : (@all (_129614 -> Prop)) = (@all (_129614 -> Prop)).
Proof. exact (eq_refl (@all (_129614 -> Prop))). Qed.
Lemma lem7018584 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) : (term35 _129614 s f) = (term36 _129614 s f).
Proof. exact (MK_COMB (@lem7018583 _129614) (@lem7018582 _129614 s f)). Qed.
Lemma lem7018589 {_129614 : Type'} (f : _129614 -> nat) : (term37 _129614 f) = (term38 _129614 f).
Proof. exact (fun_ext (fun s : _129614 -> Prop => @lem7018584 _129614 s f)). Qed.
Lemma lem7018590 {_129614 : Type'} : (@all (_129614 -> Prop)) = (@all (_129614 -> Prop)).
Proof. exact (eq_refl (@all (_129614 -> Prop))). Qed.
Lemma lem7018591 {_129614 : Type'} (f : _129614 -> nat) : (term39 _129614 f) = (term40 _129614 f).
Proof. exact (MK_COMB (@lem7018590 _129614) (@lem7018589 _129614 f)). Qed.
Lemma lem7018596 {_129614 : Type'} : (term41 _129614) = (term42 _129614).
Proof. exact (fun_ext (fun f : _129614 -> nat => @lem7018591 _129614 f)). Qed.
Lemma lem7018597 {_129614 : Type'} : (@all (_129614 -> nat)) = (@all (_129614 -> nat)).
Proof. exact (eq_refl (@all (_129614 -> nat))). Qed.
Lemma lem7018598 {_129614 : Type'} : (term43 _129614) = (term44 _129614).
Proof. exact (MK_COMB (@lem7018597 _129614) (@lem7018596 _129614)). Qed.
Lemma lem7018603 {_129614 : Type'} : (term44 _129614) = (term43 _129614).
Proof. exact (SYM (@lem7018598 _129614)). Qed.
Lemma lem7018605 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7018487 A B op) (@lem7018486 A B op)). Qed.
Lemma lem7018606 {_129614 : Type'} (op : type1606) : term45 _129614 op.
Proof. exact (@lem7018605 _129614 nat op). Qed.
Lemma lem7018607 {_129614 : Type'} : term46 _129614.
Proof. exact (@lem7018606 _129614 Nat.add). Qed.
Lemma lem7018609 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7018471) (@lem6924403)). Qed.
Lemma lem7018610 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7018609)). Qed.
Lemma lem7018611 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7018610) (@lem0)). Qed.
Lemma lem7018612 {_129614 : Type'} : term44 _129614.
Proof. exact (@lem7018607 _129614 (@lem7018611)). Qed.
Lemma lem7018613 {_129614 : Type'} : term43 _129614.
Proof. exact (EQ_MP (@lem7018603 _129614) (@lem7018612 _129614)). Qed.
