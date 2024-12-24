Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUPPORT_term_abbrevs.
Require Import SUPPORT_SUPPORT_spec.
Require Import iterate_spec.
Require Import thm0_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7068427 {_119851 _119862 : Type'} (op : type1400 _119851) : term0 _119851 _119862 op.
Proof. exact (@lem5718586 _119851 _119862 op). Qed.
Lemma lem7068428 {_119851 _119862 : Type'} (op : type1400 _119851) : (term0 _119851 _119862 op) = (term1 _119851 _119862 op).
Proof. exact (eq_refl (term0 _119851 _119862 op)). Qed.
Lemma lem7068429 {_119851 _119862 : Type'} (op : type1400 _119851) : term1 _119851 _119862 op.
Proof. exact (EQ_MP (@lem7068428 _119851 _119862 op) (@lem7068427 _119851 _119862 op)). Qed.
Lemma lem7068430 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term2 _119851 _119862 op f.
Proof. exact (@lem7068429 _119851 _119862 op f). Qed.
Lemma lem7068431 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : (term2 _119851 _119862 op f) = (term3 _119851 _119862 op f).
Proof. exact (eq_refl (term2 _119851 _119862 op f)). Qed.
Lemma lem7068432 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term3 _119851 _119862 op f.
Proof. exact (EQ_MP (@lem7068431 _119851 _119862 op f) (@lem7068430 _119851 _119862 op f)). Qed.
Lemma lem7068433 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : term4 _119851 _119862 op f s.
Proof. exact (@lem7068432 _119851 _119862 op f s). Qed.
Lemma lem7068434 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term4 _119851 _119862 op f s) = ((term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s)).
Proof. exact (eq_refl (term4 _119851 _119862 op f s)). Qed.
Lemma lem7068436 {_119779 A : Type'} (f : A -> _119779) : term6 _119779 A f.
Proof. exact (@lem5718049 _119779 A f). Qed.
Lemma lem7068437 {_119779 A : Type'} (f : A -> _119779) : (term6 _119779 A f) = (term7 _119779 A f).
Proof. exact (eq_refl (term6 _119779 A f)). Qed.
Lemma lem7068438 {_119779 A : Type'} (f : A -> _119779) : term7 _119779 A f.
Proof. exact (EQ_MP (@lem7068437 _119779 A f) (@lem7068436 _119779 A f)). Qed.
Lemma lem7068439 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term8 _119779 A f s.
Proof. exact (@lem7068438 _119779 A f s). Qed.
Lemma lem7068440 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : (term8 _119779 A f s) = (term9 _119779 A f s).
Proof. exact (eq_refl (term8 _119779 A f s)). Qed.
Lemma lem7068441 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term9 _119779 A f s.
Proof. exact (EQ_MP (@lem7068440 _119779 A f s) (@lem7068439 _119779 A f s)). Qed.
Lemma lem7068442 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : term10 _119779 A f s op.
Proof. exact (@lem7068441 _119779 A f s op). Qed.
Lemma lem7068443 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (term10 _119779 A f s op) = ((@iterate _119779 A op s f) = (term11 _119779 A f s op)).
Proof. exact (eq_refl (term10 _119779 A f s op)). Qed.
Lemma lem7068456 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068457 {_131679 : Type'} : (@sum _131679) = (@iterate real _131679 real_add).
Proof. exact (@lem7068456 _131679). Qed.
Lemma lem7068458 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (@support _131679 real real_add f s) = (@support _131679 real real_add f s).
Proof. exact (eq_refl (@support _131679 real real_add f s)). Qed.
Lemma lem7068459 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term12 _131679 f s) = (term13 _131679 f s).
Proof. exact (MK_COMB (@lem7068457 _131679) (@lem7068458 _131679 f s)). Qed.
Lemma lem7068460 {_131679 : Type'} (f : _131679 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068461 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : (term14 _131679 s f) = (term15 _131679 s f).
Proof. exact (MK_COMB (@lem7068459 _131679 f s) (@lem7068460 _131679 f)). Qed.
Lemma lem7068463 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem7068443 _119779 A f s op) (@lem7068442 _119779 A f s op)). Qed.
Lemma lem7068464 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (op : type1627) : (@iterate real _131679 op s f) = (term16 _131679 f s op).
Proof. exact (@lem7068463 real _131679 f s op). Qed.
Lemma lem7068465 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term15 _131679 s f) = (term17 _131679 f s).
Proof. exact (@lem7068464 _131679 f (@support _131679 real real_add f s) real_add). Qed.
Lemma lem7068467 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term18 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7068468 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term19 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7068467 _2963 g t e g' t' e'). Qed.
Lemma lem7068469 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term20 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7068468 _2963 g t e g' t'). Qed.
Lemma lem7068470 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term21 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7068469 _2963 g t e g'). Qed.
Lemma lem7068471 (g : Prop) (t : real) (e : real) : term22 g t e.
Proof. exact (@lem7068470 real g t e). Qed.
Lemma lem7068472 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : term23 _131679 f s.
Proof. exact (@lem7068471 (term24 _131679 f s) (term25 _131679 f s) (@neutral real real_add)). Qed.
Lemma lem7068473 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) : term26 _131679 f s g'.
Proof. exact (@lem7068472 _131679 f s g'). Qed.
Lemma lem7068474 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) : (term26 _131679 f s g') = (term27 _131679 f s g').
Proof. exact (eq_refl (term26 _131679 f s g')). Qed.
Lemma lem7068475 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) : term27 _131679 f s g'.
Proof. exact (EQ_MP (@lem7068474 _131679 f s g') (@lem7068473 _131679 f s g')). Qed.
Lemma lem7068476 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) (t' : real) : term28 _131679 f s g' t'.
Proof. exact (@lem7068475 _131679 f s g' t'). Qed.
Lemma lem7068477 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) (t' : real) : (term28 _131679 f s g' t') = (term29 _131679 f s g' t').
Proof. exact (eq_refl (term28 _131679 f s g' t')). Qed.
Lemma lem7068478 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) (t' : real) : term29 _131679 f s g' t'.
Proof. exact (EQ_MP (@lem7068477 _131679 f s g' t') (@lem7068476 _131679 f s g' t')). Qed.
Lemma lem7068479 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) (t' : real) (e' : real) : term30 _131679 f s g' t' e'.
Proof. exact (@lem7068478 _131679 f s g' t' e'). Qed.
Lemma lem7068480 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) (t' : real) (e' : real) : (term30 _131679 f s g' t' e') = (term31 _131679 f s g' t' e').
Proof. exact (eq_refl (term30 _131679 f s g' t' e')). Qed.
Lemma lem7068481 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (g' : Prop) (t' : real) (e' : real) : term31 _131679 f s g' t' e'.
Proof. exact (EQ_MP (@lem7068480 _131679 f s g' t' e') (@lem7068479 _131679 f s g' t' e')). Qed.
Lemma lem7068483 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem7068434 _119851 _119862 op f s) (@lem7068433 _119851 _119862 op f s)). Qed.
Lemma lem7068484 {_131679 : Type'} (op : type1627) (f : _131679 -> real) (s : _131679 -> Prop) : (term32 _131679 op f s) = (@support _131679 real op f s).
Proof. exact (@lem7068483 real _131679 op f s). Qed.
Lemma lem7068485 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term33 _131679 f s) = (@support _131679 real real_add f s).
Proof. exact (@lem7068484 _131679 real_add f s). Qed.
Lemma lem7068486 {_131679 : Type'} : (@FINITE _131679) = (@FINITE _131679).
Proof. exact (eq_refl (@FINITE _131679)). Qed.
Lemma lem7068487 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term24 _131679 f s) = (term34 _131679 f s).
Proof. exact (MK_COMB (@lem7068486 _131679) (@lem7068485 _131679 f s)). Qed.
Lemma lem7068488 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (t' : real) (e' : real) : term35 _131679 f s t' e'.
Proof. exact (@lem7068481 _131679 f s (term34 _131679 f s) t' e'). Qed.
Lemma lem7068489 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (t' : real) (e' : real) : term36 _131679 f s t' e'.
Proof. exact (@lem7068488 _131679 f s t' e' (@lem7068487 _131679 f s)). Qed.
Lemma lem7068494 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem7068434 _119851 _119862 op f s) (@lem7068433 _119851 _119862 op f s)). Qed.
Lemma lem7068495 {_131679 : Type'} (op : type1627) (f : _131679 -> real) (s : _131679 -> Prop) : (term32 _131679 op f s) = (@support _131679 real op f s).
Proof. exact (@lem7068494 real _131679 op f s). Qed.
Lemma lem7068496 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term33 _131679 f s) = (@support _131679 real real_add f s).
Proof. exact (@lem7068495 _131679 real_add f s). Qed.
Lemma lem7068497 {_131679 : Type'} (f : _131679 -> real) : (term37 _131679 f) = (term37 _131679 f).
Proof. exact (eq_refl (term37 _131679 f)). Qed.
Lemma lem7068498 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term38 _131679 f s) = (term39 _131679 f s).
Proof. exact (MK_COMB (@lem7068497 _131679 f) (@lem7068496 _131679 f s)). Qed.
Lemma lem7068499 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7068500 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term25 _131679 f s) = (term40 _131679 f s).
Proof. exact (MK_COMB (@lem7068498 _131679 f s) (@lem7068499)). Qed.
Lemma lem7068501 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : term41 _131679 f s.
Proof. exact (fun h0 : term34 _131679 f s => @lem7068500 _131679 f s). Qed.
Lemma lem7068502 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (e' : real) : term42 _131679 f s e'.
Proof. exact (@lem7068489 _131679 f s (term40 _131679 f s) e'). Qed.
Lemma lem7068503 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (e' : real) : term43 _131679 f s e'.
Proof. exact (@lem7068502 _131679 f s e' (@lem7068501 _131679 f s)). Qed.
Lemma lem7068507 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7068508 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : term44 _131679 f s.
Proof. exact (fun h0 : term45 _131679 f s => @lem7068507). Qed.
Lemma lem7068509 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : term46 _131679 f s.
Proof. exact (@lem7068503 _131679 f s (@neutral real real_add)). Qed.
Lemma lem7068510 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term17 _131679 f s) = (term47 _131679 f s).
Proof. exact (@lem7068509 _131679 f s (@lem7068508 _131679 f s)). Qed.
Lemma lem7068544 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term15 _131679 s f) = (term47 _131679 f s).
Proof. exact (TRANS (@lem7068465 _131679 f s) (@lem7068510 _131679 f s)). Qed.
Lemma lem7068545 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term14 _131679 s f) = (term47 _131679 f s).
Proof. exact (TRANS (@lem7068461 _131679 s f) (@lem7068544 _131679 f s)). Qed.
Lemma lem7068546 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7068547 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (term48 _131679 s f) = (term49 _131679 f s).
Proof. exact (MK_COMB (@lem7068546) (@lem7068545 _131679 f s)). Qed.
Lemma lem7068582 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068583 {_131679 : Type'} : (@sum _131679) = (@iterate real _131679 real_add).
Proof. exact (@lem7068582 _131679). Qed.
Lemma lem7068584 {_131679 : Type'} (s : _131679 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068585 {_131679 : Type'} (s : _131679 -> Prop) : (@sum _131679 s) = (@iterate real _131679 real_add s).
Proof. exact (MK_COMB (@lem7068583 _131679) (@lem7068584 _131679 s)). Qed.
Lemma lem7068586 {_131679 : Type'} (f : _131679 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068587 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : (@sum _131679 s f) = (@iterate real _131679 real_add s f).
Proof. exact (MK_COMB (@lem7068585 _131679 s) (@lem7068586 _131679 f)). Qed.
Lemma lem7068589 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem7068443 _119779 A f s op) (@lem7068442 _119779 A f s op)). Qed.
Lemma lem7068590 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) (op : type1627) : (@iterate real _131679 op s f) = (term16 _131679 f s op).
Proof. exact (@lem7068589 real _131679 f s op). Qed.
Lemma lem7068591 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (@iterate real _131679 real_add s f) = (term47 _131679 f s).
Proof. exact (@lem7068590 _131679 f s real_add). Qed.
Lemma lem7068625 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : (@sum _131679 s f) = (term47 _131679 f s).
Proof. exact (TRANS (@lem7068587 _131679 s f) (@lem7068591 _131679 f s)). Qed.
Lemma lem7068626 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : ((term14 _131679 s f) = (@sum _131679 s f)) = ((term47 _131679 f s) = (term47 _131679 f s)).
Proof. exact (MK_COMB (@lem7068547 _131679 f s) (@lem7068625 _131679 f s)). Qed.
Lemma lem7068628 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7068629 (x : real) : (x = x) = True.
Proof. exact (@lem7068628 real x). Qed.
Lemma lem7068630 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : ((term47 _131679 f s) = (term47 _131679 f s)) = True.
Proof. exact (@lem7068629 (term47 _131679 f s)). Qed.
Lemma lem7068631 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : ((term14 _131679 s f) = (@sum _131679 s f)) = True.
Proof. exact (TRANS (@lem7068626 _131679 f s) (@lem7068630 _131679 f s)). Qed.
Lemma lem7068632 {_131679 : Type'} (f : _131679 -> real) : (term50 _131679 f) = (term51 _131679).
Proof. exact (fun_ext (fun s : _131679 -> Prop => @lem7068631 _131679 s f)). Qed.
Lemma lem7068633 {_131679 : Type'} : (@all (_131679 -> Prop)) = (@all (_131679 -> Prop)).
Proof. exact (eq_refl (@all (_131679 -> Prop))). Qed.
Lemma lem7068634 {_131679 : Type'} (f : _131679 -> real) : (term52 _131679 f) = (term53 _131679).
Proof. exact (MK_COMB (@lem7068633 _131679) (@lem7068632 _131679 f)). Qed.
Lemma lem7068636 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068637 {_131679 : Type'} (t : Prop) : (term55 _131679 t) = t.
Proof. exact (@lem7068636 (_131679 -> Prop) t). Qed.
Lemma lem7068638 {_131679 : Type'} : (term53 _131679) = True.
Proof. exact (@lem7068637 _131679 True). Qed.
Lemma lem7068639 {_131679 : Type'} (f : _131679 -> real) : (term52 _131679 f) = True.
Proof. exact (TRANS (@lem7068634 _131679 f) (@lem7068638 _131679)). Qed.
Lemma lem7068640 {_131679 : Type'} : (term56 _131679) = (term57 _131679).
Proof. exact (fun_ext (fun f : _131679 -> real => @lem7068639 _131679 f)). Qed.
Lemma lem7068641 {_131679 : Type'} : (@all (_131679 -> real)) = (@all (_131679 -> real)).
Proof. exact (eq_refl (@all (_131679 -> real))). Qed.
Lemma lem7068642 {_131679 : Type'} : (term58 _131679) = (term59 _131679).
Proof. exact (MK_COMB (@lem7068641 _131679) (@lem7068640 _131679)). Qed.
Lemma lem7068644 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068645 {_131679 : Type'} (t : Prop) : (term60 _131679 t) = t.
Proof. exact (@lem7068644 (_131679 -> real) t). Qed.
Lemma lem7068646 {_131679 : Type'} : (term59 _131679) = True.
Proof. exact (@lem7068645 _131679 True). Qed.
Lemma lem7068647 {_131679 : Type'} : (term58 _131679) = True.
Proof. exact (TRANS (@lem7068642 _131679) (@lem7068646 _131679)). Qed.
Lemma lem7068648 {_131679 : Type'} : True = (term58 _131679).
Proof. exact (SYM (@lem7068647 _131679)). Qed.
Lemma lem7068649 {_131679 : Type'} : term58 _131679.
Proof. exact (EQ_MP (@lem7068648 _131679) (@lem0)). Qed.
