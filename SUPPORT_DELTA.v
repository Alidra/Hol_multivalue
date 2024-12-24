Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPPORT_DELTA_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_SING_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5736506 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem5736507 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5736508 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5736507 A x) (@lem5736506 A x)). Qed.
Lemma lem5736509 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem5736508 A x y). Qed.
Lemma lem5736510 {A : Type'} (x : A) (y : A) : (term2 A x y) = ((term3 A x y) = (x = y)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem5736536 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5736537 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem5736536 _83095 p). Qed.
Lemma lem5736538 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem5736539 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem5736538 _83095 p) (@lem5736537 _83095 p)). Qed.
Lemma lem5736540 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem5736539 _83095 p x). Qed.
Lemma lem5736541 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem5736550 {A B : Type'} (s : A -> Prop) : term9 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem5736551 {A B : Type'} (s : A -> Prop) : (term9 A B s) = (term10 A B s).
Proof. exact (eq_refl (term9 A B s)). Qed.
Lemma lem5736552 {A B : Type'} (s : A -> Prop) : term10 A B s.
Proof. exact (EQ_MP (@lem5736551 A B s) (@lem5736550 A B s)). Qed.
Lemma lem5736553 {A B : Type'} (s : A -> Prop) (f : A -> B) : term11 A B s f.
Proof. exact (@lem5736552 A B s f). Qed.
Lemma lem5736554 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term12 A B s f).
Proof. exact (eq_refl (term11 A B s f)). Qed.
Lemma lem5736555 {A B : Type'} (s : A -> Prop) (f : A -> B) : term12 A B s f.
Proof. exact (EQ_MP (@lem5736554 A B s f) (@lem5736553 A B s f)). Qed.
Lemma lem5736556 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term13 A B s f op.
Proof. exact (@lem5736555 A B s f op). Qed.
Lemma lem5736557 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term13 A B s f op) = ((@support A B op f s) = (term14 A B s f op)).
Proof. exact (eq_refl (term13 A B s f op)). Qed.
Lemma lem5736559 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5736560 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem5736561 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem5736560 A s) (@lem5736559 A s)). Qed.
Lemma lem5736562 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (@lem5736561 A s t). Qed.
Lemma lem5736563 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = ((s = t) = (term18 A s t)).
Proof. exact (eq_refl (term17 A s t)). Qed.
Lemma lem5736584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem5736563 A s t) (@lem5736562 A s t)). Qed.
Lemma lem5736585 {_120250 : Type'} (s : _120250 -> Prop) (t : _120250 -> Prop) : (s = t) = (term18 _120250 s t).
Proof. exact (@lem5736584 _120250 s t). Qed.
Lemma lem5736586 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : ((term19 _120222 _120250 a f op s) = (term20 _120222 _120250 s op f a)) = (term21 _120222 _120250 s op f a).
Proof. exact (@lem5736585 _120250 (term19 _120222 _120250 a f op s) (term20 _120222 _120250 s op f a)). Qed.
Lemma lem5736596 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term14 A B s f op).
Proof. exact (EQ_MP (@lem5736557 A B s f op) (@lem5736556 A B s f op)). Qed.
Lemma lem5736597 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) : (@support _120250 _120222 op f s) = (term22 _120222 _120250 s f op).
Proof. exact (@lem5736596 _120250 _120222 s f op). Qed.
Lemma lem5736598 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term19 _120222 _120250 a f op s) = (term23 _120222 _120250 s a f op).
Proof. exact (@lem5736597 _120222 _120250 s (term24 _120222 _120250 a f op) op). Qed.
Lemma lem5736610 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5736611 {_120222 _120250 : Type'} (f : _120250 -> _120222) (y : _120250) : (term26 _120222 _120250 f y) = (f y).
Proof. exact (@lem5736610 _120250 _120222 f y). Qed.
Lemma lem5736612 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term27 _120222 _120250 a f op x) = (term28 _120222 _120250 a f op x).
Proof. exact (@lem5736611 _120222 _120250 (term24 _120222 _120250 a f op) x). Qed.
Lemma lem5736613 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term28 _120222 _120250 a f op x) = (term29 _120222 _120250 a f x op).
Proof. exact (eq_refl (term28 _120222 _120250 a f op x)). Qed.
Lemma lem5736614 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term30 _120222 _120250 a f op) = (term24 _120222 _120250 a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5736613 _120222 _120250 a f x op)). Qed.
Lemma lem5736615 {_120250 : Type'} (x : _120250) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5736616 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term27 _120222 _120250 a f op x) = (term28 _120222 _120250 a f op x).
Proof. exact (MK_COMB (@lem5736614 _120222 _120250 a f op) (@lem5736615 _120250 x)). Qed.
Lemma lem5736617 {_120222 : Type'} : (@eq _120222) = (@eq _120222).
Proof. exact (eq_refl (@eq _120222)). Qed.
Lemma lem5736618 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term31 _120222 _120250 a f op x) = (term32 _120222 _120250 a f op x).
Proof. exact (MK_COMB (@lem5736617 _120222) (@lem5736616 _120222 _120250 a f op x)). Qed.
Lemma lem5736619 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term28 _120222 _120250 a f op x) = (term29 _120222 _120250 a f x op).
Proof. exact (eq_refl (term28 _120222 _120250 a f op x)). Qed.
Lemma lem5736620 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : ((term27 _120222 _120250 a f op x) = (term28 _120222 _120250 a f op x)) = ((term28 _120222 _120250 a f op x) = (term29 _120222 _120250 a f x op)).
Proof. exact (MK_COMB (@lem5736618 _120222 _120250 a f op x) (@lem5736619 _120222 _120250 a f x op)). Qed.
Lemma lem5736621 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term28 _120222 _120250 a f op x) = (term29 _120222 _120250 a f x op).
Proof. exact (EQ_MP (@lem5736620 _120222 _120250 a f x op) (@lem5736612 _120222 _120250 a f op x)). Qed.
Lemma lem5736628 {_120222 : Type'} : (@eq _120222) = (@eq _120222).
Proof. exact (eq_refl (@eq _120222)). Qed.
Lemma lem5736629 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term32 _120222 _120250 a f op x) = (term33 _120222 _120250 a f x op).
Proof. exact (MK_COMB (@lem5736628 _120222) (@lem5736621 _120222 _120250 a f x op)). Qed.
Lemma lem5736630 {_120222 : Type'} (op : type1400 _120222) : (@neutral _120222 op) = (@neutral _120222 op).
Proof. exact (eq_refl (@neutral _120222 op)). Qed.
Lemma lem5736631 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : ((term28 _120222 _120250 a f op x) = (@neutral _120222 op)) = ((term29 _120222 _120250 a f x op) = (@neutral _120222 op)).
Proof. exact (MK_COMB (@lem5736629 _120222 _120250 a f x op) (@lem5736630 _120222 op)). Qed.
Lemma lem5736636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5736637 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term34 _120222 _120250 a f x op) = (term35 _120222 _120250 a f x op).
Proof. exact (MK_COMB (@lem5736636) (@lem5736631 _120222 _120250 a f x op)). Qed.
Lemma lem5736638 {_120250 : Type'} (x : _120250) (s : _120250 -> Prop) : (term36 _120250 x s) = (term36 _120250 x s).
Proof. exact (eq_refl (term36 _120250 x s)). Qed.
Lemma lem5736639 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term37 _120222 _120250 s a f x op) = (term38 _120222 _120250 s a f x op).
Proof. exact (MK_COMB (@lem5736638 _120250 x s) (@lem5736637 _120222 _120250 a f x op)). Qed.
Lemma lem5736642 {_120250 : Type'} (GEN_PVAR_237 : _120250) : (@SETSPEC _120250 GEN_PVAR_237) = (@SETSPEC _120250 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120250 GEN_PVAR_237)). Qed.
Lemma lem5736643 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term39 _120222 _120250 GEN_PVAR_237 s a f x op) = (term40 _120222 _120250 GEN_PVAR_237 s a f x op).
Proof. exact (MK_COMB (@lem5736642 _120250 GEN_PVAR_237) (@lem5736639 _120222 _120250 s a f x op)). Qed.
Lemma lem5736644 {_120250 : Type'} (x : _120250) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5736645 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term41 _120222 _120250 GEN_PVAR_237 s a f op x) = (term42 _120222 _120250 GEN_PVAR_237 s a f op x).
Proof. exact (MK_COMB (@lem5736643 _120222 _120250 GEN_PVAR_237 s a f x op) (@lem5736644 _120250 x)). Qed.
Lemma lem5736646 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term43 _120222 _120250 GEN_PVAR_237 s a f op) = (term44 _120222 _120250 GEN_PVAR_237 s a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5736645 _120222 _120250 GEN_PVAR_237 s a f op x)). Qed.
Lemma lem5736647 {_120250 : Type'} : (@ex _120250) = (@ex _120250).
Proof. exact (eq_refl (@ex _120250)). Qed.
Lemma lem5736648 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term45 _120222 _120250 GEN_PVAR_237 s a f op) = (term46 _120222 _120250 GEN_PVAR_237 s a f op).
Proof. exact (MK_COMB (@lem5736647 _120250) (@lem5736646 _120222 _120250 GEN_PVAR_237 s a f op)). Qed.
Lemma lem5736653 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term47 _120222 _120250 s a f op) = (term48 _120222 _120250 s a f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120250 => @lem5736648 _120222 _120250 GEN_PVAR_237 s a f op)). Qed.
Lemma lem5736654 {_120250 : Type'} : (@GSPEC _120250) = (@GSPEC _120250).
Proof. exact (eq_refl (@GSPEC _120250)). Qed.
Lemma lem5736655 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term23 _120222 _120250 s a f op) = (term49 _120222 _120250 s a f op).
Proof. exact (MK_COMB (@lem5736654 _120250) (@lem5736653 _120222 _120250 s a f op)). Qed.
Lemma lem5736656 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term19 _120222 _120250 a f op s) = (term49 _120222 _120250 s a f op).
Proof. exact (TRANS (@lem5736598 _120222 _120250 s a f op) (@lem5736655 _120222 _120250 s a f op)). Qed.
Lemma lem5736657 {_120250 : Type'} (x : _120250) : (@IN _120250 x) = (@IN _120250 x).
Proof. exact (eq_refl (@IN _120250 x)). Qed.
Lemma lem5736658 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term50 _120222 _120250 x a f op s) = (term51 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736657 _120250 x) (@lem5736656 _120222 _120250 s a f op)). Qed.
Lemma lem5736660 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5736541 _83095 p x) (@lem5736540 _83095 p x)). Qed.
Lemma lem5736661 {_120250 : Type'} (p : _120250 -> Prop) (x : _120250) : (term8 _120250 x p) = (p x).
Proof. exact (@lem5736660 _120250 p x). Qed.
Lemma lem5736662 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term52 _120222 _120250 x s a f op) = (term53 _120222 _120250 s a f op x).
Proof. exact (@lem5736661 _120250 (term54 _120222 _120250 s a f op) x). Qed.
Lemma lem5736663 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term53 _120222 _120250 s a f op x) = (term38 _120222 _120250 s a f x op).
Proof. exact (eq_refl (term53 _120222 _120250 s a f op x)). Qed.
Lemma lem5736664 {_120250 : Type'} (GEN_PVAR_237 : _120250) : (@SETSPEC _120250 GEN_PVAR_237) = (@SETSPEC _120250 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120250 GEN_PVAR_237)). Qed.
Lemma lem5736665 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term55 _120222 _120250 GEN_PVAR_237 s a f op x) = (term40 _120222 _120250 GEN_PVAR_237 s a f x op).
Proof. exact (MK_COMB (@lem5736664 _120250 GEN_PVAR_237) (@lem5736663 _120222 _120250 s a f x op)). Qed.
Lemma lem5736666 {_120250 : Type'} (x : _120250) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5736667 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term56 _120222 _120250 GEN_PVAR_237 s a f op x) = (term42 _120222 _120250 GEN_PVAR_237 s a f op x).
Proof. exact (MK_COMB (@lem5736665 _120222 _120250 GEN_PVAR_237 s a f x op) (@lem5736666 _120250 x)). Qed.
Lemma lem5736668 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term57 _120222 _120250 GEN_PVAR_237 s a f op) = (term44 _120222 _120250 GEN_PVAR_237 s a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5736667 _120222 _120250 GEN_PVAR_237 s a f op x)). Qed.
Lemma lem5736669 {_120250 : Type'} : (@ex _120250) = (@ex _120250).
Proof. exact (eq_refl (@ex _120250)). Qed.
Lemma lem5736670 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term58 _120222 _120250 GEN_PVAR_237 s a f op) = (term46 _120222 _120250 GEN_PVAR_237 s a f op).
Proof. exact (MK_COMB (@lem5736669 _120250) (@lem5736668 _120222 _120250 GEN_PVAR_237 s a f op)). Qed.
Lemma lem5736671 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term59 _120222 _120250 s a f op) = (term48 _120222 _120250 s a f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120250 => @lem5736670 _120222 _120250 GEN_PVAR_237 s a f op)). Qed.
Lemma lem5736672 {_120250 : Type'} : (@GSPEC _120250) = (@GSPEC _120250).
Proof. exact (eq_refl (@GSPEC _120250)). Qed.
Lemma lem5736673 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term60 _120222 _120250 s a f op) = (term49 _120222 _120250 s a f op).
Proof. exact (MK_COMB (@lem5736672 _120250) (@lem5736671 _120222 _120250 s a f op)). Qed.
Lemma lem5736674 {_120250 : Type'} (x : _120250) : (@IN _120250 x) = (@IN _120250 x).
Proof. exact (eq_refl (@IN _120250 x)). Qed.
Lemma lem5736675 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term52 _120222 _120250 x s a f op) = (term51 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736674 _120250 x) (@lem5736673 _120222 _120250 s a f op)). Qed.
Lemma lem5736676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5736677 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term61 _120222 _120250 x s a f op) = (term62 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736676) (@lem5736675 _120222 _120250 x s a f op)). Qed.
Lemma lem5736678 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term53 _120222 _120250 s a f op x) = (term38 _120222 _120250 s a f x op).
Proof. exact (eq_refl (term53 _120222 _120250 s a f op x)). Qed.
Lemma lem5736679 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : ((term52 _120222 _120250 x s a f op) = (term53 _120222 _120250 s a f op x)) = ((term51 _120222 _120250 x s a f op) = (term38 _120222 _120250 s a f x op)).
Proof. exact (MK_COMB (@lem5736677 _120222 _120250 x s a f op) (@lem5736678 _120222 _120250 s a f x op)). Qed.
Lemma lem5736680 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term51 _120222 _120250 x s a f op) = (term38 _120222 _120250 s a f x op).
Proof. exact (EQ_MP (@lem5736679 _120222 _120250 s a f x op) (@lem5736662 _120222 _120250 s a f op x)). Qed.
Lemma lem5736693 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term50 _120222 _120250 x a f op s) = (term38 _120222 _120250 s a f x op).
Proof. exact (TRANS (@lem5736658 _120222 _120250 x s a f op) (@lem5736680 _120222 _120250 s a f x op)). Qed.
Lemma lem5736694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5736695 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term63 _120222 _120250 x a f op s) = (term64 _120222 _120250 s a f x op).
Proof. exact (MK_COMB (@lem5736694) (@lem5736693 _120222 _120250 s a f x op)). Qed.
Lemma lem5736697 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term14 A B s f op).
Proof. exact (EQ_MP (@lem5736557 A B s f op) (@lem5736556 A B s f op)). Qed.
Lemma lem5736698 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) : (@support _120250 _120222 op f s) = (term22 _120222 _120250 s f op).
Proof. exact (@lem5736697 _120250 _120222 s f op). Qed.
Lemma lem5736699 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term65 _120222 _120250 op f a) = (term66 _120222 _120250 a f op).
Proof. exact (@lem5736698 _120222 _120250 (@INSERT _120250 a (@EMPTY _120250)) f op). Qed.
Lemma lem5736707 {A : Type'} (x : A) (y : A) : (term3 A x y) = (x = y).
Proof. exact (EQ_MP (@lem5736510 A x y) (@lem5736509 A x y)). Qed.
Lemma lem5736708 {_120250 : Type'} (x : _120250) (y : _120250) : (term3 _120250 x y) = (x = y).
Proof. exact (@lem5736707 _120250 x y). Qed.
Lemma lem5736709 {_120250 : Type'} (x : _120250) (a : _120250) : (term3 _120250 x a) = (x = a).
Proof. exact (@lem5736708 _120250 x a). Qed.
Lemma lem5736714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5736715 {_120250 : Type'} (x : _120250) (a : _120250) : (term67 _120250 x a) = (term68 _120250 x a).
Proof. exact (MK_COMB (@lem5736714) (@lem5736709 _120250 x a)). Qed.
Lemma lem5736720 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term69 _120222 _120250 f x op) = (term69 _120222 _120250 f x op).
Proof. exact (eq_refl (term69 _120222 _120250 f x op)). Qed.
Lemma lem5736721 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term70 _120222 _120250 a f x op) = (term71 _120222 _120250 a f x op).
Proof. exact (MK_COMB (@lem5736715 _120250 x a) (@lem5736720 _120222 _120250 f x op)). Qed.
Lemma lem5736724 {_120250 : Type'} (GEN_PVAR_237 : _120250) : (@SETSPEC _120250 GEN_PVAR_237) = (@SETSPEC _120250 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120250 GEN_PVAR_237)). Qed.
Lemma lem5736725 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term72 _120222 _120250 GEN_PVAR_237 a f x op) = (term73 _120222 _120250 GEN_PVAR_237 a f x op).
Proof. exact (MK_COMB (@lem5736724 _120250 GEN_PVAR_237) (@lem5736721 _120222 _120250 a f x op)). Qed.
Lemma lem5736726 {_120250 : Type'} (x : _120250) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5736727 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term74 _120222 _120250 GEN_PVAR_237 a f op x) = (term75 _120222 _120250 GEN_PVAR_237 a f op x).
Proof. exact (MK_COMB (@lem5736725 _120222 _120250 GEN_PVAR_237 a f x op) (@lem5736726 _120250 x)). Qed.
Lemma lem5736728 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term76 _120222 _120250 GEN_PVAR_237 a f op) = (term77 _120222 _120250 GEN_PVAR_237 a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5736727 _120222 _120250 GEN_PVAR_237 a f op x)). Qed.
Lemma lem5736729 {_120250 : Type'} : (@ex _120250) = (@ex _120250).
Proof. exact (eq_refl (@ex _120250)). Qed.
Lemma lem5736730 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term78 _120222 _120250 GEN_PVAR_237 a f op) = (term79 _120222 _120250 GEN_PVAR_237 a f op).
Proof. exact (MK_COMB (@lem5736729 _120250) (@lem5736728 _120222 _120250 GEN_PVAR_237 a f op)). Qed.
Lemma lem5736735 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term80 _120222 _120250 a f op) = (term81 _120222 _120250 a f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120250 => @lem5736730 _120222 _120250 GEN_PVAR_237 a f op)). Qed.
Lemma lem5736736 {_120250 : Type'} : (@GSPEC _120250) = (@GSPEC _120250).
Proof. exact (eq_refl (@GSPEC _120250)). Qed.
Lemma lem5736737 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term66 _120222 _120250 a f op) = (term82 _120222 _120250 a f op).
Proof. exact (MK_COMB (@lem5736736 _120250) (@lem5736735 _120222 _120250 a f op)). Qed.
Lemma lem5736738 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term65 _120222 _120250 op f a) = (term82 _120222 _120250 a f op).
Proof. exact (TRANS (@lem5736699 _120222 _120250 a f op) (@lem5736737 _120222 _120250 a f op)). Qed.
Lemma lem5736739 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : (term83 _120250 a s) = (term83 _120250 a s).
Proof. exact (eq_refl (term83 _120250 a s)). Qed.
Lemma lem5736740 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term84 _120222 _120250 s op f a) = (term85 _120222 _120250 s a f op).
Proof. exact (MK_COMB (@lem5736739 _120250 a s) (@lem5736738 _120222 _120250 a f op)). Qed.
Lemma lem5736741 {_120250 : Type'} : (@EMPTY _120250) = (@EMPTY _120250).
Proof. exact (eq_refl (@EMPTY _120250)). Qed.
Lemma lem5736742 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term20 _120222 _120250 s op f a) = (term86 _120222 _120250 s a f op).
Proof. exact (MK_COMB (@lem5736740 _120222 _120250 s a f op) (@lem5736741 _120250)). Qed.
Lemma lem5736743 {_120250 : Type'} (x : _120250) : (@IN _120250 x) = (@IN _120250 x).
Proof. exact (eq_refl (@IN _120250 x)). Qed.
Lemma lem5736744 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term87 _120222 _120250 x s op f a) = (term88 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736743 _120250 x) (@lem5736742 _120222 _120250 s a f op)). Qed.
Lemma lem5736745 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : ((term50 _120222 _120250 x a f op s) = (term87 _120222 _120250 x s op f a)) = ((term38 _120222 _120250 s a f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (MK_COMB (@lem5736695 _120222 _120250 s a f x op) (@lem5736744 _120222 _120250 x s a f op)). Qed.
Lemma lem5736750 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term89 _120222 _120250 s op f a) = (term90 _120222 _120250 s a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5736745 _120222 _120250 x s a f op)). Qed.
Lemma lem5736751 {_120250 : Type'} : (@all _120250) = (@all _120250).
Proof. exact (eq_refl (@all _120250)). Qed.
Lemma lem5736752 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term21 _120222 _120250 s op f a) = (term91 _120222 _120250 s a f op).
Proof. exact (MK_COMB (@lem5736751 _120250) (@lem5736750 _120222 _120250 s a f op)). Qed.
Lemma lem5736757 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : ((term19 _120222 _120250 a f op s) = (term20 _120222 _120250 s op f a)) = (term91 _120222 _120250 s a f op).
Proof. exact (TRANS (@lem5736586 _120222 _120250 s op f a) (@lem5736752 _120222 _120250 s a f op)). Qed.
Lemma lem5736758 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) : (term92 _120222 _120250 s op f) = (term93 _120222 _120250 s f op).
Proof. exact (fun_ext (fun a : _120250 => @lem5736757 _120222 _120250 s a f op)). Qed.
Lemma lem5736759 {_120250 : Type'} : (@all _120250) = (@all _120250).
Proof. exact (eq_refl (@all _120250)). Qed.
Lemma lem5736760 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) : (term94 _120222 _120250 s op f) = (term95 _120222 _120250 s f op).
Proof. exact (MK_COMB (@lem5736759 _120250) (@lem5736758 _120222 _120250 s f op)). Qed.
Lemma lem5736765 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : (term96 _120222 _120250 s op) = (term97 _120222 _120250 s op).
Proof. exact (fun_ext (fun f : _120250 -> _120222 => @lem5736760 _120222 _120250 s f op)). Qed.
Lemma lem5736766 {_120222 _120250 : Type'} : (@all (_120250 -> _120222)) = (@all (_120250 -> _120222)).
Proof. exact (eq_refl (@all (_120250 -> _120222))). Qed.
Lemma lem5736767 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : (term98 _120222 _120250 s op) = (term99 _120222 _120250 s op).
Proof. exact (MK_COMB (@lem5736766 _120222 _120250) (@lem5736765 _120222 _120250 s op)). Qed.
Lemma lem5736772 {_120222 _120250 : Type'} (op : type1400 _120222) : (term100 _120222 _120250 op) = (term101 _120222 _120250 op).
Proof. exact (fun_ext (fun s : _120250 -> Prop => @lem5736767 _120222 _120250 s op)). Qed.
Lemma lem5736773 {_120250 : Type'} : (@all (_120250 -> Prop)) = (@all (_120250 -> Prop)).
Proof. exact (eq_refl (@all (_120250 -> Prop))). Qed.
Lemma lem5736774 {_120222 _120250 : Type'} (op : type1400 _120222) : (term102 _120222 _120250 op) = (term103 _120222 _120250 op).
Proof. exact (MK_COMB (@lem5736773 _120250) (@lem5736772 _120222 _120250 op)). Qed.
Lemma lem5736779 {_120222 _120250 : Type'} : (term104 _120222 _120250) = (term105 _120222 _120250).
Proof. exact (fun_ext (fun op : type1400 _120222 => @lem5736774 _120222 _120250 op)). Qed.
Lemma lem5736780 {_120222 : Type'} : (@all (_120222 -> _120222 -> _120222)) = (@all (_120222 -> _120222 -> _120222)).
Proof. exact (eq_refl (@all (_120222 -> _120222 -> _120222))). Qed.
Lemma lem5736781 {_120222 _120250 : Type'} : (term106 _120222 _120250) = (term107 _120222 _120250).
Proof. exact (MK_COMB (@lem5736780 _120222) (@lem5736779 _120222 _120250)). Qed.
Lemma lem5736786 {_120222 _120250 : Type'} : (term107 _120222 _120250) = (term106 _120222 _120250).
Proof. exact (SYM (@lem5736781 _120222 _120250)). Qed.
Lemma lem5736787 {_120222 : Type'} (_474 : _120222) (_475 : Prop) (_476 : _120222 -> Prop) (_477 : _120222) : (term108 _120222 _476 _475 _474 _477) = (term109 _120222 _474 _475 _476 _477).
Proof. exact (@lem13473 _120222 _474 _475 _476 _477). Qed.
Lemma lem5736788 {_120222 _120250 : Type'} (_474 : _120222) (_475 : Prop) (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (_477 : _120222) : (term110 _120222 _120250 x s a f op _475 _474 _477) = (term111 _120222 _120250 _474 _475 x s a f op _477).
Proof. exact (@lem5736787 _120222 _474 _475 (term112 _120222 _120250 x s a f op) _477). Qed.
Lemma lem5736789 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term113 _120222 _120250 s a f x op) = (term114 _120222 _120250 x s a f op).
Proof. exact (@lem5736788 _120222 _120250 (f x) (x = a) x s a f op (@neutral _120222 op)). Qed.
Lemma lem5736790 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term115 _120222 _120250 x s a f op) = ((term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (eq_refl (term115 _120222 _120250 x s a f op)). Qed.
Lemma lem5736791 {_120250 : Type'} (x : _120250) (a : _120250) : (term117 _120250 x a) = (term117 _120250 x a).
Proof. exact (eq_refl (term117 _120250 x a)). Qed.
Lemma lem5736792 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term118 _120222 _120250 x s a f op) = (term119 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736791 _120250 x a) (@lem5736790 _120222 _120250 x s a f op)). Qed.
Lemma lem5736793 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term120 _120222 _120250 s a op f x) = ((term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (eq_refl (term120 _120222 _120250 s a op f x)). Qed.
Lemma lem5736794 {_120250 : Type'} (x : _120250) (a : _120250) : (term122 _120250 x a) = (term122 _120250 x a).
Proof. exact (eq_refl (term122 _120250 x a)). Qed.
Lemma lem5736795 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term123 _120222 _120250 s a op f x) = (term124 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736794 _120250 x a) (@lem5736793 _120222 _120250 x s a f op)). Qed.
Lemma lem5736796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5736797 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term125 _120222 _120250 s a op f x) = (term126 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736796) (@lem5736795 _120222 _120250 x s a f op)). Qed.
Lemma lem5736798 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term114 _120222 _120250 x s a f op) = (term127 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736797 _120222 _120250 x s a f op) (@lem5736792 _120222 _120250 x s a f op)). Qed.
Lemma lem5736799 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term113 _120222 _120250 s a f x op) = ((term38 _120222 _120250 s a f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (eq_refl (term113 _120222 _120250 s a f x op)). Qed.
Lemma lem5736800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5736801 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term128 _120222 _120250 s a f x op) = (term129 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736800) (@lem5736799 _120222 _120250 x s a f op)). Qed.
Lemma lem5736802 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : ((term113 _120222 _120250 s a f x op) = (term114 _120222 _120250 x s a f op)) = (((term38 _120222 _120250 s a f x op) = (term88 _120222 _120250 x s a f op)) = (term127 _120222 _120250 x s a f op)).
Proof. exact (MK_COMB (@lem5736801 _120222 _120250 x s a f op) (@lem5736798 _120222 _120250 x s a f op)). Qed.
Lemma lem5736803 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : ((term38 _120222 _120250 s a f x op) = (term88 _120222 _120250 x s a f op)) = (term127 _120222 _120250 x s a f op).
Proof. exact (EQ_MP (@lem5736802 _120222 _120250 x s a f op) (@lem5736789 _120222 _120250 x s a f op)). Qed.
Lemma lem5736804 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term127 _120222 _120250 x s a f op) = ((term38 _120222 _120250 s a f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (SYM (@lem5736803 _120222 _120250 x s a f op)). Qed.
Lemma lem5736805 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5736822 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : term130 _120250 x a.
Proof. exact (h1). Qed.
Lemma lem5736839 {_120250 : Type'} (_474 : _120250 -> Prop) (_475 : Prop) (_476 : type686 _120250) (_477 : _120250 -> Prop) : (term131 _120250 _476 _475 _474 _477) = (term132 _120250 _474 _475 _476 _477).
Proof. exact (@lem13473 (_120250 -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5736840 {_120222 _120250 : Type'} (_474 : _120250 -> Prop) (_475 : Prop) (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (_477 : _120250 -> Prop) : (term133 _120222 _120250 s f op x _475 _474 _477) = (term134 _120222 _120250 _474 _475 s f op x _477).
Proof. exact (@lem5736839 _120250 _474 _475 (term135 _120222 _120250 s f op x) _477). Qed.
Lemma lem5736841 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term136 _120222 _120250 x s a f op) = (term137 _120222 _120250 a s f op x).
Proof. exact (@lem5736840 _120222 _120250 (term82 _120222 _120250 a f op) (@IN _120250 a s) s f op x (@EMPTY _120250)). Qed.
Lemma lem5736842 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term138 _120222 _120250 s f op x) = ((term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250))).
Proof. exact (eq_refl (term138 _120222 _120250 s f op x)). Qed.
Lemma lem5736843 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : (term139 _120250 a s) = (term139 _120250 a s).
Proof. exact (eq_refl (term139 _120250 a s)). Qed.
Lemma lem5736844 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term140 _120222 _120250 a s f op x) = (term141 _120222 _120250 a s f op x).
Proof. exact (MK_COMB (@lem5736843 _120250 a s) (@lem5736842 _120222 _120250 s f op x)). Qed.
Lemma lem5736845 {_120222 _120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term142 _120222 _120250 s x a f op) = ((term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op)).
Proof. exact (eq_refl (term142 _120222 _120250 s x a f op)). Qed.
Lemma lem5736846 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : (term144 _120250 a s) = (term144 _120250 a s).
Proof. exact (eq_refl (term144 _120250 a s)). Qed.
Lemma lem5736847 {_120222 _120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term145 _120222 _120250 s x a f op) = (term146 _120222 _120250 s x a f op).
Proof. exact (MK_COMB (@lem5736846 _120250 a s) (@lem5736845 _120222 _120250 s x a f op)). Qed.
Lemma lem5736848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5736849 {_120222 _120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term147 _120222 _120250 s x a f op) = (term148 _120222 _120250 s x a f op).
Proof. exact (MK_COMB (@lem5736848) (@lem5736847 _120222 _120250 s x a f op)). Qed.
Lemma lem5736850 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term137 _120222 _120250 a s f op x) = (term149 _120222 _120250 a s f op x).
Proof. exact (MK_COMB (@lem5736849 _120222 _120250 s x a f op) (@lem5736844 _120222 _120250 a s f op x)). Qed.
Lemma lem5736851 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term136 _120222 _120250 x s a f op) = ((term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (eq_refl (term136 _120222 _120250 x s a f op)). Qed.
Lemma lem5736852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5736853 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term150 _120222 _120250 x s a f op) = (term151 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736852) (@lem5736851 _120222 _120250 x s a f op)). Qed.
Lemma lem5736854 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : ((term136 _120222 _120250 x s a f op) = (term137 _120222 _120250 a s f op x)) = (((term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op)) = (term149 _120222 _120250 a s f op x)).
Proof. exact (MK_COMB (@lem5736853 _120222 _120250 x s a f op) (@lem5736850 _120222 _120250 a s f op x)). Qed.
Lemma lem5736855 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : ((term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op)) = (term149 _120222 _120250 a s f op x).
Proof. exact (EQ_MP (@lem5736854 _120222 _120250 a s f op x) (@lem5736841 _120222 _120250 a s f op x)). Qed.
Lemma lem5736856 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term149 _120222 _120250 a s f op x) = ((term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (SYM (@lem5736855 _120222 _120250 a s f op x)). Qed.
Lemma lem5736857 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) (h1 : @IN _120250 a s) : @IN _120250 a s.
Proof. exact (h1). Qed.
Lemma lem5736874 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) (h1 : term152 _120250 a s) : term152 _120250 a s.
Proof. exact (h1). Qed.
Lemma lem5736891 {_120250 : Type'} (_474 : _120250 -> Prop) (_475 : Prop) (_476 : type686 _120250) (_477 : _120250 -> Prop) : (term131 _120250 _476 _475 _474 _477) = (term132 _120250 _474 _475 _476 _477).
Proof. exact (@lem13473 (_120250 -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5736892 {_120222 _120250 : Type'} (_474 : _120250 -> Prop) (_475 : Prop) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) (_477 : _120250 -> Prop) : (term153 _120222 _120250 s op x _475 _474 _477) = (term154 _120222 _120250 _474 _475 s op x _477).
Proof. exact (@lem5736891 _120250 _474 _475 (term155 _120222 _120250 s op x) _477). Qed.
Lemma lem5736893 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : (term156 _120222 _120250 x s a f op) = (term157 _120222 _120250 f a s op x).
Proof. exact (@lem5736892 _120222 _120250 (term82 _120222 _120250 a f op) (@IN _120250 a s) s op x (@EMPTY _120250)). Qed.
Lemma lem5736894 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : (term158 _120222 _120250 s op x) = ((term116 _120222 _120250 x s op) = (@IN _120250 x (@EMPTY _120250))).
Proof. exact (eq_refl (term158 _120222 _120250 s op x)). Qed.
Lemma lem5736895 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : (term139 _120250 a s) = (term139 _120250 a s).
Proof. exact (eq_refl (term139 _120250 a s)). Qed.
Lemma lem5736896 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : (term159 _120222 _120250 a s op x) = (term160 _120222 _120250 a s op x).
Proof. exact (MK_COMB (@lem5736895 _120250 a s) (@lem5736894 _120222 _120250 s op x)). Qed.
Lemma lem5736897 {_120222 _120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term161 _120222 _120250 s x a f op) = ((term116 _120222 _120250 x s op) = (term143 _120222 _120250 x a f op)).
Proof. exact (eq_refl (term161 _120222 _120250 s x a f op)). Qed.
Lemma lem5736898 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : (term144 _120250 a s) = (term144 _120250 a s).
Proof. exact (eq_refl (term144 _120250 a s)). Qed.
Lemma lem5736899 {_120222 _120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term162 _120222 _120250 s x a f op) = (term163 _120222 _120250 s x a f op).
Proof. exact (MK_COMB (@lem5736898 _120250 a s) (@lem5736897 _120222 _120250 s x a f op)). Qed.
Lemma lem5736900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5736901 {_120222 _120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term164 _120222 _120250 s x a f op) = (term165 _120222 _120250 s x a f op).
Proof. exact (MK_COMB (@lem5736900) (@lem5736899 _120222 _120250 s x a f op)). Qed.
Lemma lem5736902 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : (term157 _120222 _120250 f a s op x) = (term166 _120222 _120250 f a s op x).
Proof. exact (MK_COMB (@lem5736901 _120222 _120250 s x a f op) (@lem5736896 _120222 _120250 a s op x)). Qed.
Lemma lem5736903 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term156 _120222 _120250 x s a f op) = ((term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (eq_refl (term156 _120222 _120250 x s a f op)). Qed.
Lemma lem5736904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5736905 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term167 _120222 _120250 x s a f op) = (term168 _120222 _120250 x s a f op).
Proof. exact (MK_COMB (@lem5736904) (@lem5736903 _120222 _120250 x s a f op)). Qed.
Lemma lem5736906 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : ((term156 _120222 _120250 x s a f op) = (term157 _120222 _120250 f a s op x)) = (((term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op)) = (term166 _120222 _120250 f a s op x)).
Proof. exact (MK_COMB (@lem5736905 _120222 _120250 x s a f op) (@lem5736902 _120222 _120250 f a s op x)). Qed.
Lemma lem5736907 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : ((term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op)) = (term166 _120222 _120250 f a s op x).
Proof. exact (EQ_MP (@lem5736906 _120222 _120250 f a s op x) (@lem5736893 _120222 _120250 f a s op x)). Qed.
Lemma lem5736908 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term166 _120222 _120250 f a s op x) = ((term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (SYM (@lem5736907 _120222 _120250 f a s op x)). Qed.
Lemma lem5736972 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5736973 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem5736972 _83095 p). Qed.
Lemma lem5736974 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem5736975 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem5736974 _83095 p) (@lem5736973 _83095 p)). Qed.
Lemma lem5736976 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem5736975 _83095 p x). Qed.
Lemma lem5736977 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem5736986 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : (@IN _120250 a s) = ((@IN _120250 a s) = True).
Proof. exact (@lem7 (@IN _120250 a s)). Qed.
Lemma lem5736993 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5736994 {_120250 : Type'} : (@IN _120250) = (@IN _120250).
Proof. exact (eq_refl (@IN _120250)). Qed.
Lemma lem5736995 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : (@IN _120250 x) = (@IN _120250 a).
Proof. exact (MK_COMB (@lem5736994 _120250) (@lem5736993 _120250 x a h1)). Qed.
Lemma lem5736996 {_120250 : Type'} (s : _120250 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5736997 {_120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : x = a) : (@IN _120250 x s) = (@IN _120250 a s).
Proof. exact (MK_COMB (@lem5736995 _120250 x a h1) (@lem5736996 _120250 s)). Qed.
Lemma lem5736999 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) (h1 : @IN _120250 a s) : (@IN _120250 a s) = True.
Proof. exact (EQ_MP (@lem5736986 _120250 a s) (@lem5736857 _120250 a s h1)). Qed.
Lemma lem5737000 {_120250 : Type'} (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (@IN _120250 x s) = True.
Proof. exact (TRANS (@lem5736997 _120250 s x a h1) (@lem5736999 _120250 a s h2)). Qed.
Lemma lem5737001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5737002 {_120250 : Type'} (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (term36 _120250 x s) = (and True).
Proof. exact (MK_COMB (@lem5737001) (@lem5737000 _120250 x a s h1 h2)). Qed.
Lemma lem5737006 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5737007 {_120222 _120250 : Type'} (f : _120250 -> _120222) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5737008 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (a : _120250) (h1 : x = a) : (f x) = (f a).
Proof. exact (MK_COMB (@lem5737007 _120222 _120250 f) (@lem5737006 _120250 x a h1)). Qed.
Lemma lem5737009 {_120222 : Type'} : (@eq _120222) = (@eq _120222).
Proof. exact (eq_refl (@eq _120222)). Qed.
Lemma lem5737010 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term169 _120222 _120250 f x) = (term169 _120222 _120250 f a).
Proof. exact (MK_COMB (@lem5737009 _120222) (@lem5737008 _120222 _120250 f x a h1)). Qed.
Lemma lem5737011 {_120222 : Type'} (op : type1400 _120222) : (@neutral _120222 op) = (@neutral _120222 op).
Proof. exact (eq_refl (@neutral _120222 op)). Qed.
Lemma lem5737012 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : ((f x) = (@neutral _120222 op)) = ((f a) = (@neutral _120222 op)).
Proof. exact (MK_COMB (@lem5737010 _120222 _120250 f x a h1) (@lem5737011 _120222 op)). Qed.
Lemma lem5737015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5737016 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term69 _120222 _120250 f x op) = (term69 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737015) (@lem5737012 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737017 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (term121 _120222 _120250 s f x op) = (term170 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737002 _120250 x a s h1 h2) (@lem5737016 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737019 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5737020 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (op : type1400 _120222) : (term170 _120222 _120250 f a op) = (term69 _120222 _120250 f a op).
Proof. exact (@lem5737019 (term69 _120222 _120250 f a op)). Qed.
Lemma lem5737023 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (term121 _120222 _120250 s f x op) = (term69 _120222 _120250 f a op).
Proof. exact (TRANS (@lem5737017 _120222 _120250 f op x a s h1 h2) (@lem5737020 _120222 _120250 f a op)). Qed.
Lemma lem5737024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737025 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (term171 _120222 _120250 s f x op) = (term172 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737024) (@lem5737023 _120222 _120250 f op x a s h1 h2)). Qed.
Lemma lem5737027 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5736977 _83095 p x) (@lem5736976 _83095 p x)). Qed.
Lemma lem5737028 {_120250 : Type'} (p : _120250 -> Prop) (x : _120250) : (term8 _120250 x p) = (p x).
Proof. exact (@lem5737027 _120250 p x). Qed.
Lemma lem5737029 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term173 _120222 _120250 x a f op) = (term174 _120222 _120250 a f op x).
Proof. exact (@lem5737028 _120250 (term175 _120222 _120250 a f op) x). Qed.
Lemma lem5737030 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term174 _120222 _120250 a f op x) = (term71 _120222 _120250 a f x op).
Proof. exact (eq_refl (term174 _120222 _120250 a f op x)). Qed.
Lemma lem5737031 {_120250 : Type'} (GEN_PVAR_237 : _120250) : (@SETSPEC _120250 GEN_PVAR_237) = (@SETSPEC _120250 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120250 GEN_PVAR_237)). Qed.
Lemma lem5737032 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term176 _120222 _120250 GEN_PVAR_237 a f op x) = (term73 _120222 _120250 GEN_PVAR_237 a f x op).
Proof. exact (MK_COMB (@lem5737031 _120250 GEN_PVAR_237) (@lem5737030 _120222 _120250 a f x op)). Qed.
Lemma lem5737033 {_120250 : Type'} (x : _120250) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5737034 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term177 _120222 _120250 GEN_PVAR_237 a f op x) = (term75 _120222 _120250 GEN_PVAR_237 a f op x).
Proof. exact (MK_COMB (@lem5737032 _120222 _120250 GEN_PVAR_237 a f x op) (@lem5737033 _120250 x)). Qed.
Lemma lem5737035 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term178 _120222 _120250 GEN_PVAR_237 a f op) = (term77 _120222 _120250 GEN_PVAR_237 a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5737034 _120222 _120250 GEN_PVAR_237 a f op x)). Qed.
Lemma lem5737036 {_120250 : Type'} : (@ex _120250) = (@ex _120250).
Proof. exact (eq_refl (@ex _120250)). Qed.
Lemma lem5737037 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term179 _120222 _120250 GEN_PVAR_237 a f op) = (term79 _120222 _120250 GEN_PVAR_237 a f op).
Proof. exact (MK_COMB (@lem5737036 _120250) (@lem5737035 _120222 _120250 GEN_PVAR_237 a f op)). Qed.
Lemma lem5737038 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term180 _120222 _120250 a f op) = (term81 _120222 _120250 a f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120250 => @lem5737037 _120222 _120250 GEN_PVAR_237 a f op)). Qed.
Lemma lem5737039 {_120250 : Type'} : (@GSPEC _120250) = (@GSPEC _120250).
Proof. exact (eq_refl (@GSPEC _120250)). Qed.
Lemma lem5737040 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term181 _120222 _120250 a f op) = (term82 _120222 _120250 a f op).
Proof. exact (MK_COMB (@lem5737039 _120250) (@lem5737038 _120222 _120250 a f op)). Qed.
Lemma lem5737041 {_120250 : Type'} (x : _120250) : (@IN _120250 x) = (@IN _120250 x).
Proof. exact (eq_refl (@IN _120250 x)). Qed.
Lemma lem5737042 {_120222 _120250 : Type'} (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term173 _120222 _120250 x a f op) = (term143 _120222 _120250 x a f op).
Proof. exact (MK_COMB (@lem5737041 _120250 x) (@lem5737040 _120222 _120250 a f op)). Qed.
Lemma lem5737043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737044 {_120222 _120250 : Type'} (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term182 _120222 _120250 x a f op) = (term183 _120222 _120250 x a f op).
Proof. exact (MK_COMB (@lem5737043) (@lem5737042 _120222 _120250 x a f op)). Qed.
Lemma lem5737045 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term174 _120222 _120250 a f op x) = (term71 _120222 _120250 a f x op).
Proof. exact (eq_refl (term174 _120222 _120250 a f op x)). Qed.
Lemma lem5737046 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : ((term173 _120222 _120250 x a f op) = (term174 _120222 _120250 a f op x)) = ((term143 _120222 _120250 x a f op) = (term71 _120222 _120250 a f x op)).
Proof. exact (MK_COMB (@lem5737044 _120222 _120250 x a f op) (@lem5737045 _120222 _120250 a f x op)). Qed.
Lemma lem5737047 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term143 _120222 _120250 x a f op) = (term71 _120222 _120250 a f x op).
Proof. exact (EQ_MP (@lem5737046 _120222 _120250 a f x op) (@lem5737029 _120222 _120250 a f op x)). Qed.
Lemma lem5737053 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5737054 {_120250 : Type'} : (@eq _120250) = (@eq _120250).
Proof. exact (eq_refl (@eq _120250)). Qed.
Lemma lem5737055 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : (@eq _120250 x) = (@eq _120250 a).
Proof. exact (MK_COMB (@lem5737054 _120250) (@lem5737053 _120250 x a h1)). Qed.
Lemma lem5737056 {_120250 : Type'} (a : _120250) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5737057 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : (x = a) = (a = a).
Proof. exact (MK_COMB (@lem5737055 _120250 x a h1) (@lem5737056 _120250 a)). Qed.
Lemma lem5737059 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5737060 {_120250 : Type'} (x : _120250) : (x = x) = True.
Proof. exact (@lem5737059 _120250 x). Qed.
Lemma lem5737061 {_120250 : Type'} (a : _120250) : (a = a) = True.
Proof. exact (@lem5737060 _120250 a). Qed.
Lemma lem5737062 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : (x = a) = True.
Proof. exact (TRANS (@lem5737057 _120250 x a h1) (@lem5737061 _120250 a)). Qed.
Lemma lem5737063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5737064 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : (term68 _120250 x a) = (and True).
Proof. exact (MK_COMB (@lem5737063) (@lem5737062 _120250 x a h1)). Qed.
Lemma lem5737068 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5737069 {_120222 _120250 : Type'} (f : _120250 -> _120222) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5737070 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (a : _120250) (h1 : x = a) : (f x) = (f a).
Proof. exact (MK_COMB (@lem5737069 _120222 _120250 f) (@lem5737068 _120250 x a h1)). Qed.
Lemma lem5737071 {_120222 : Type'} : (@eq _120222) = (@eq _120222).
Proof. exact (eq_refl (@eq _120222)). Qed.
Lemma lem5737072 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term169 _120222 _120250 f x) = (term169 _120222 _120250 f a).
Proof. exact (MK_COMB (@lem5737071 _120222) (@lem5737070 _120222 _120250 f x a h1)). Qed.
Lemma lem5737073 {_120222 : Type'} (op : type1400 _120222) : (@neutral _120222 op) = (@neutral _120222 op).
Proof. exact (eq_refl (@neutral _120222 op)). Qed.
Lemma lem5737074 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : ((f x) = (@neutral _120222 op)) = ((f a) = (@neutral _120222 op)).
Proof. exact (MK_COMB (@lem5737072 _120222 _120250 f x a h1) (@lem5737073 _120222 op)). Qed.
Lemma lem5737077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5737078 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term69 _120222 _120250 f x op) = (term69 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737077) (@lem5737074 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737079 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term71 _120222 _120250 a f x op) = (term170 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737064 _120250 x a h1) (@lem5737078 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737081 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5737082 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (op : type1400 _120222) : (term170 _120222 _120250 f a op) = (term69 _120222 _120250 f a op).
Proof. exact (@lem5737081 (term69 _120222 _120250 f a op)). Qed.
Lemma lem5737085 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term71 _120222 _120250 a f x op) = (term69 _120222 _120250 f a op).
Proof. exact (TRANS (@lem5737079 _120222 _120250 f op x a h1) (@lem5737082 _120222 _120250 f a op)). Qed.
Lemma lem5737086 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term143 _120222 _120250 x a f op) = (term69 _120222 _120250 f a op).
Proof. exact (TRANS (@lem5737047 _120222 _120250 a f x op) (@lem5737085 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737087 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : ((term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op)) = ((term69 _120222 _120250 f a op) = (term69 _120222 _120250 f a op)).
Proof. exact (MK_COMB (@lem5737025 _120222 _120250 f op x a s h1 h2) (@lem5737086 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737089 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5737090 (x : Prop) : (x = x) = True.
Proof. exact (@lem5737089 Prop x). Qed.
Lemma lem5737091 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (op : type1400 _120222) : ((term69 _120222 _120250 f a op) = (term69 _120222 _120250 f a op)) = True.
Proof. exact (@lem5737090 (term69 _120222 _120250 f a op)). Qed.
Lemma lem5737092 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : ((term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op)) = True.
Proof. exact (TRANS (@lem5737087 _120222 _120250 f op x a s h1 h2) (@lem5737091 _120222 _120250 f a op)). Qed.
Lemma lem5737093 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : True = ((term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op)).
Proof. exact (SYM (@lem5737092 _120222 _120250 f op x a s h1 h2)). Qed.
Lemma lem5737095 {A : Type'} (x : A) : term184 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5737096 {A : Type'} (x : A) : (term184 A x) = (term185 A x).
Proof. exact (eq_refl (term184 A x)). Qed.
Lemma lem5737097 {A : Type'} (x : A) : term185 A x.
Proof. exact (EQ_MP (@lem5737096 A x) (@lem5737095 A x)). Qed.
Lemma lem5737098 {A : Type'} (x : A) : term186 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5737138 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) : term187 _120250 a s.
Proof. exact (@lem82 (@IN _120250 a s)). Qed.
Lemma lem5737145 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5737146 {_120250 : Type'} : (@IN _120250) = (@IN _120250).
Proof. exact (eq_refl (@IN _120250)). Qed.
Lemma lem5737147 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : (@IN _120250 x) = (@IN _120250 a).
Proof. exact (MK_COMB (@lem5737146 _120250) (@lem5737145 _120250 x a h1)). Qed.
Lemma lem5737148 {_120250 : Type'} (s : _120250 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5737149 {_120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : x = a) : (@IN _120250 x s) = (@IN _120250 a s).
Proof. exact (MK_COMB (@lem5737147 _120250 x a h1) (@lem5737148 _120250 s)). Qed.
Lemma lem5737151 {_120250 : Type'} (a : _120250) (s : _120250 -> Prop) (h1 : term152 _120250 a s) : (@IN _120250 a s) = False.
Proof. exact (@lem5737138 _120250 a s (@lem5736874 _120250 a s h1)). Qed.
Lemma lem5737152 {_120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (@IN _120250 x s) = False.
Proof. exact (TRANS (@lem5737149 _120250 s x a h2) (@lem5737151 _120250 a s h1)). Qed.
Lemma lem5737153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5737154 {_120250 : Type'} (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term36 _120250 x s) = (and False).
Proof. exact (MK_COMB (@lem5737153) (@lem5737152 _120250 s x a h1 h2)). Qed.
Lemma lem5737158 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5737159 {_120222 _120250 : Type'} (f : _120250 -> _120222) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5737160 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (a : _120250) (h1 : x = a) : (f x) = (f a).
Proof. exact (MK_COMB (@lem5737159 _120222 _120250 f) (@lem5737158 _120250 x a h1)). Qed.
Lemma lem5737161 {_120222 : Type'} : (@eq _120222) = (@eq _120222).
Proof. exact (eq_refl (@eq _120222)). Qed.
Lemma lem5737162 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term169 _120222 _120250 f x) = (term169 _120222 _120250 f a).
Proof. exact (MK_COMB (@lem5737161 _120222) (@lem5737160 _120222 _120250 f x a h1)). Qed.
Lemma lem5737163 {_120222 : Type'} (op : type1400 _120222) : (@neutral _120222 op) = (@neutral _120222 op).
Proof. exact (eq_refl (@neutral _120222 op)). Qed.
Lemma lem5737164 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : ((f x) = (@neutral _120222 op)) = ((f a) = (@neutral _120222 op)).
Proof. exact (MK_COMB (@lem5737162 _120222 _120250 f x a h1) (@lem5737163 _120222 op)). Qed.
Lemma lem5737167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5737168 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term69 _120222 _120250 f x op) = (term69 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737167) (@lem5737164 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737169 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term121 _120222 _120250 s f x op) = (term188 _120222 _120250 f a op).
Proof. exact (MK_COMB (@lem5737154 _120250 s x a h1 h2) (@lem5737168 _120222 _120250 f op x a h2)). Qed.
Lemma lem5737171 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5737172 {_120222 _120250 : Type'} (f : _120250 -> _120222) (a : _120250) (op : type1400 _120222) : (term188 _120222 _120250 f a op) = False.
Proof. exact (@lem5737171 (term69 _120222 _120250 f a op)). Qed.
Lemma lem5737173 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term121 _120222 _120250 s f x op) = False.
Proof. exact (TRANS (@lem5737169 _120222 _120250 f op s x a h1 h2) (@lem5737172 _120222 _120250 f a op)). Qed.
Lemma lem5737174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737175 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term171 _120222 _120250 s f x op) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5737174) (@lem5737173 _120222 _120250 f op s x a h1 h2)). Qed.
Lemma lem5737177 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5737098 A x (@lem5737097 A x)). Qed.
Lemma lem5737178 {_120250 : Type'} (x : _120250) : (@IN _120250 x (@EMPTY _120250)) = False.
Proof. exact (@lem5737177 _120250 x). Qed.
Lemma lem5737179 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : ((term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250))) = (False = False).
Proof. exact (MK_COMB (@lem5737175 _120222 _120250 f op s x a h1 h2) (@lem5737178 _120250 x)). Qed.
Lemma lem5737181 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5737182 : (False = False) = (~ False).
Proof. exact (@lem5737181 False). Qed.
Lemma lem5737184 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5737185 : (False = False) = True.
Proof. exact (TRANS (@lem5737182) (@lem5737184)). Qed.
Lemma lem5737186 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : ((term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250))) = True.
Proof. exact (TRANS (@lem5737179 _120222 _120250 f op s x a h1 h2) (@lem5737185)). Qed.
Lemma lem5737187 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : True = ((term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250))).
Proof. exact (SYM (@lem5737186 _120222 _120250 f op s x a h1 h2)). Qed.
Lemma lem5737218 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5737219 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem5737218 _83095 p). Qed.
Lemma lem5737220 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem5737221 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem5737220 _83095 p) (@lem5737219 _83095 p)). Qed.
Lemma lem5737222 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem5737221 _83095 p x). Qed.
Lemma lem5737223 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem5737232 {_120250 : Type'} (x : _120250) (a : _120250) : term189 _120250 x a.
Proof. exact (@lem82 (x = a)). Qed.
Lemma lem5737252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5737253 {_120222 : Type'} (x : _120222) : (x = x) = True.
Proof. exact (@lem5737252 _120222 x). Qed.
Lemma lem5737254 {_120222 : Type'} (op : type1400 _120222) : ((@neutral _120222 op) = (@neutral _120222 op)) = True.
Proof. exact (@lem5737253 _120222 (@neutral _120222 op)). Qed.
Lemma lem5737255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5737256 {_120222 : Type'} (op : type1400 _120222) : (term190 _120222 op) = (~ True).
Proof. exact (MK_COMB (@lem5737255) (@lem5737254 _120222 op)). Qed.
Lemma lem5737258 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5737259 {_120222 : Type'} (op : type1400 _120222) : (term190 _120222 op) = False.
Proof. exact (TRANS (@lem5737256 _120222 op) (@lem5737258)). Qed.
Lemma lem5737260 {_120250 : Type'} (x : _120250) (s : _120250 -> Prop) : (term36 _120250 x s) = (term36 _120250 x s).
Proof. exact (eq_refl (term36 _120250 x s)). Qed.
Lemma lem5737261 {_120222 _120250 : Type'} (op : type1400 _120222) (x : _120250) (s : _120250 -> Prop) : (term116 _120222 _120250 x s op) = (term191 _120250 x s).
Proof. exact (MK_COMB (@lem5737260 _120250 x s) (@lem5737259 _120222 op)). Qed.
Lemma lem5737263 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5737264 {_120250 : Type'} (x : _120250) (s : _120250 -> Prop) : (term191 _120250 x s) = False.
Proof. exact (@lem5737263 (@IN _120250 x s)). Qed.
Lemma lem5737265 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (op : type1400 _120222) : (term116 _120222 _120250 x s op) = False.
Proof. exact (TRANS (@lem5737261 _120222 _120250 op x s) (@lem5737264 _120250 x s)). Qed.
Lemma lem5737266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737267 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (op : type1400 _120222) : (term192 _120222 _120250 x s op) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5737266) (@lem5737265 _120222 _120250 x s op)). Qed.
Lemma lem5737269 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5737223 _83095 p x) (@lem5737222 _83095 p x)). Qed.
Lemma lem5737270 {_120250 : Type'} (p : _120250 -> Prop) (x : _120250) : (term8 _120250 x p) = (p x).
Proof. exact (@lem5737269 _120250 p x). Qed.
Lemma lem5737271 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term173 _120222 _120250 x a f op) = (term174 _120222 _120250 a f op x).
Proof. exact (@lem5737270 _120250 (term175 _120222 _120250 a f op) x). Qed.
Lemma lem5737272 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term174 _120222 _120250 a f op x) = (term71 _120222 _120250 a f x op).
Proof. exact (eq_refl (term174 _120222 _120250 a f op x)). Qed.
Lemma lem5737273 {_120250 : Type'} (GEN_PVAR_237 : _120250) : (@SETSPEC _120250 GEN_PVAR_237) = (@SETSPEC _120250 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120250 GEN_PVAR_237)). Qed.
Lemma lem5737274 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term176 _120222 _120250 GEN_PVAR_237 a f op x) = (term73 _120222 _120250 GEN_PVAR_237 a f x op).
Proof. exact (MK_COMB (@lem5737273 _120250 GEN_PVAR_237) (@lem5737272 _120222 _120250 a f x op)). Qed.
Lemma lem5737275 {_120250 : Type'} (x : _120250) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5737276 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) : (term177 _120222 _120250 GEN_PVAR_237 a f op x) = (term75 _120222 _120250 GEN_PVAR_237 a f op x).
Proof. exact (MK_COMB (@lem5737274 _120222 _120250 GEN_PVAR_237 a f x op) (@lem5737275 _120250 x)). Qed.
Lemma lem5737277 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term178 _120222 _120250 GEN_PVAR_237 a f op) = (term77 _120222 _120250 GEN_PVAR_237 a f op).
Proof. exact (fun_ext (fun x : _120250 => @lem5737276 _120222 _120250 GEN_PVAR_237 a f op x)). Qed.
Lemma lem5737278 {_120250 : Type'} : (@ex _120250) = (@ex _120250).
Proof. exact (eq_refl (@ex _120250)). Qed.
Lemma lem5737279 {_120222 _120250 : Type'} (GEN_PVAR_237 : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term179 _120222 _120250 GEN_PVAR_237 a f op) = (term79 _120222 _120250 GEN_PVAR_237 a f op).
Proof. exact (MK_COMB (@lem5737278 _120250) (@lem5737277 _120222 _120250 GEN_PVAR_237 a f op)). Qed.
Lemma lem5737280 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term180 _120222 _120250 a f op) = (term81 _120222 _120250 a f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120250 => @lem5737279 _120222 _120250 GEN_PVAR_237 a f op)). Qed.
Lemma lem5737281 {_120250 : Type'} : (@GSPEC _120250) = (@GSPEC _120250).
Proof. exact (eq_refl (@GSPEC _120250)). Qed.
Lemma lem5737282 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term181 _120222 _120250 a f op) = (term82 _120222 _120250 a f op).
Proof. exact (MK_COMB (@lem5737281 _120250) (@lem5737280 _120222 _120250 a f op)). Qed.
Lemma lem5737283 {_120250 : Type'} (x : _120250) : (@IN _120250 x) = (@IN _120250 x).
Proof. exact (eq_refl (@IN _120250 x)). Qed.
Lemma lem5737284 {_120222 _120250 : Type'} (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term173 _120222 _120250 x a f op) = (term143 _120222 _120250 x a f op).
Proof. exact (MK_COMB (@lem5737283 _120250 x) (@lem5737282 _120222 _120250 a f op)). Qed.
Lemma lem5737285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737286 {_120222 _120250 : Type'} (x : _120250) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term182 _120222 _120250 x a f op) = (term183 _120222 _120250 x a f op).
Proof. exact (MK_COMB (@lem5737285) (@lem5737284 _120222 _120250 x a f op)). Qed.
Lemma lem5737287 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term174 _120222 _120250 a f op x) = (term71 _120222 _120250 a f x op).
Proof. exact (eq_refl (term174 _120222 _120250 a f op x)). Qed.
Lemma lem5737288 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : ((term173 _120222 _120250 x a f op) = (term174 _120222 _120250 a f op x)) = ((term143 _120222 _120250 x a f op) = (term71 _120222 _120250 a f x op)).
Proof. exact (MK_COMB (@lem5737286 _120222 _120250 x a f op) (@lem5737287 _120222 _120250 a f x op)). Qed.
Lemma lem5737289 {_120222 _120250 : Type'} (a : _120250) (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term143 _120222 _120250 x a f op) = (term71 _120222 _120250 a f x op).
Proof. exact (EQ_MP (@lem5737288 _120222 _120250 a f x op) (@lem5737271 _120222 _120250 a f op x)). Qed.
Lemma lem5737293 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (x = a) = False.
Proof. exact (@lem5737232 _120250 x a (@lem5736822 _120250 x a h1)). Qed.
Lemma lem5737294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5737295 {_120250 : Type'} (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term68 _120250 x a) = (and False).
Proof. exact (MK_COMB (@lem5737294) (@lem5737293 _120250 x a h1)). Qed.
Lemma lem5737298 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term69 _120222 _120250 f x op) = (term69 _120222 _120250 f x op).
Proof. exact (eq_refl (term69 _120222 _120250 f x op)). Qed.
Lemma lem5737299 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term71 _120222 _120250 a f x op) = (term188 _120222 _120250 f x op).
Proof. exact (MK_COMB (@lem5737295 _120250 x a h1) (@lem5737298 _120222 _120250 f x op)). Qed.
Lemma lem5737301 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5737302 {_120222 _120250 : Type'} (f : _120250 -> _120222) (x : _120250) (op : type1400 _120222) : (term188 _120222 _120250 f x op) = False.
Proof. exact (@lem5737301 (term69 _120222 _120250 f x op)). Qed.
Lemma lem5737303 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term71 _120222 _120250 a f x op) = False.
Proof. exact (TRANS (@lem5737299 _120222 _120250 f op x a h1) (@lem5737302 _120222 _120250 f x op)). Qed.
Lemma lem5737304 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term143 _120222 _120250 x a f op) = False.
Proof. exact (TRANS (@lem5737289 _120222 _120250 a f x op) (@lem5737303 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737305 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : ((term116 _120222 _120250 x s op) = (term143 _120222 _120250 x a f op)) = (False = False).
Proof. exact (MK_COMB (@lem5737267 _120222 _120250 x s op) (@lem5737304 _120222 _120250 f op x a h1)). Qed.
Lemma lem5737307 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5737308 : (False = False) = (~ False).
Proof. exact (@lem5737307 False). Qed.
Lemma lem5737310 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5737311 : (False = False) = True.
Proof. exact (TRANS (@lem5737308) (@lem5737310)). Qed.
Lemma lem5737312 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : ((term116 _120222 _120250 x s op) = (term143 _120222 _120250 x a f op)) = True.
Proof. exact (TRANS (@lem5737305 _120222 _120250 s f op x a h1) (@lem5737311)). Qed.
Lemma lem5737313 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : True = ((term116 _120222 _120250 x s op) = (term143 _120222 _120250 x a f op)).
Proof. exact (SYM (@lem5737312 _120222 _120250 s f op x a h1)). Qed.
Lemma lem5737315 {A : Type'} (x : A) : term184 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5737316 {A : Type'} (x : A) : (term184 A x) = (term185 A x).
Proof. exact (eq_refl (term184 A x)). Qed.
Lemma lem5737317 {A : Type'} (x : A) : term185 A x.
Proof. exact (EQ_MP (@lem5737316 A x) (@lem5737315 A x)). Qed.
Lemma lem5737318 {A : Type'} (x : A) : term186 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5737378 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5737379 {_120222 : Type'} (x : _120222) : (x = x) = True.
Proof. exact (@lem5737378 _120222 x). Qed.
Lemma lem5737380 {_120222 : Type'} (op : type1400 _120222) : ((@neutral _120222 op) = (@neutral _120222 op)) = True.
Proof. exact (@lem5737379 _120222 (@neutral _120222 op)). Qed.
Lemma lem5737381 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5737382 {_120222 : Type'} (op : type1400 _120222) : (term190 _120222 op) = (~ True).
Proof. exact (MK_COMB (@lem5737381) (@lem5737380 _120222 op)). Qed.
Lemma lem5737384 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5737385 {_120222 : Type'} (op : type1400 _120222) : (term190 _120222 op) = False.
Proof. exact (TRANS (@lem5737382 _120222 op) (@lem5737384)). Qed.
Lemma lem5737386 {_120250 : Type'} (x : _120250) (s : _120250 -> Prop) : (term36 _120250 x s) = (term36 _120250 x s).
Proof. exact (eq_refl (term36 _120250 x s)). Qed.
Lemma lem5737387 {_120222 _120250 : Type'} (op : type1400 _120222) (x : _120250) (s : _120250 -> Prop) : (term116 _120222 _120250 x s op) = (term191 _120250 x s).
Proof. exact (MK_COMB (@lem5737386 _120250 x s) (@lem5737385 _120222 op)). Qed.
Lemma lem5737389 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5737390 {_120250 : Type'} (x : _120250) (s : _120250 -> Prop) : (term191 _120250 x s) = False.
Proof. exact (@lem5737389 (@IN _120250 x s)). Qed.
Lemma lem5737391 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (op : type1400 _120222) : (term116 _120222 _120250 x s op) = False.
Proof. exact (TRANS (@lem5737387 _120222 _120250 op x s) (@lem5737390 _120250 x s)). Qed.
Lemma lem5737392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737393 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (op : type1400 _120222) : (term192 _120222 _120250 x s op) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5737392) (@lem5737391 _120222 _120250 x s op)). Qed.
Lemma lem5737395 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5737318 A x (@lem5737317 A x)). Qed.
Lemma lem5737396 {_120250 : Type'} (x : _120250) : (@IN _120250 x (@EMPTY _120250)) = False.
Proof. exact (@lem5737395 _120250 x). Qed.
Lemma lem5737397 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : ((term116 _120222 _120250 x s op) = (@IN _120250 x (@EMPTY _120250))) = (False = False).
Proof. exact (MK_COMB (@lem5737393 _120222 _120250 x s op) (@lem5737396 _120250 x)). Qed.
Lemma lem5737399 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5737400 : (False = False) = (~ False).
Proof. exact (@lem5737399 False). Qed.
Lemma lem5737402 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5737403 : (False = False) = True.
Proof. exact (TRANS (@lem5737400) (@lem5737402)). Qed.
Lemma lem5737404 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : ((term116 _120222 _120250 x s op) = (@IN _120250 x (@EMPTY _120250))) = True.
Proof. exact (TRANS (@lem5737397 _120222 _120250 s op x) (@lem5737403)). Qed.
Lemma lem5737405 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : True = ((term116 _120222 _120250 x s op) = (@IN _120250 x (@EMPTY _120250))).
Proof. exact (SYM (@lem5737404 _120222 _120250 s op x)). Qed.
Lemma lem5737407 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : (term116 _120222 _120250 x s op) = (@IN _120250 x (@EMPTY _120250)).
Proof. exact (EQ_MP (@lem5737405 _120222 _120250 s op x) (@lem0)). Qed.
Lemma lem5737408 {_120222 _120250 : Type'} (a : _120250) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) : term160 _120222 _120250 a s op x.
Proof. exact (fun h0 : term152 _120250 a s => @lem5737407 _120222 _120250 s op x). Qed.
Lemma lem5737409 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term116 _120222 _120250 x s op) = (term143 _120222 _120250 x a f op).
Proof. exact (EQ_MP (@lem5737313 _120222 _120250 s f op x a h1) (@lem0)). Qed.
Lemma lem5737410 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : term163 _120222 _120250 s x a f op.
Proof. exact (fun h0 : @IN _120250 a s => @lem5737409 _120222 _120250 s f op x a h1). Qed.
Lemma lem5737411 {_120222 _120250 : Type'} (f : _120250 -> _120222) (s : _120250 -> Prop) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : term166 _120222 _120250 f a s op x.
Proof. exact (conj (@lem5737410 _120222 _120250 s f op x a h1) (@lem5737408 _120222 _120250 a s op x)). Qed.
Lemma lem5737413 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250)).
Proof. exact (EQ_MP (@lem5737187 _120222 _120250 f op s x a h1 h2) (@lem0)). Qed.
Lemma lem5737414 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term152 _120250 a s) = ((term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250))).
Proof. exact (prop_ext (fun h3 : term152 _120250 a s => @lem5737413 _120222 _120250 f op s x a h1 h2) (fun h3 : (term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250)) => @lem5736874 _120250 a s h1)). Qed.
Lemma lem5737415 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (s : _120250 -> Prop) (x : _120250) (a : _120250) (h1 : term152 _120250 a s) (h2 : x = a) : (term121 _120222 _120250 s f x op) = (@IN _120250 x (@EMPTY _120250)).
Proof. exact (EQ_MP (@lem5737414 _120222 _120250 f op s x a h1 h2) (@lem5736874 _120250 a s h1)). Qed.
Lemma lem5737416 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : term141 _120222 _120250 a s f op x.
Proof. exact (fun h0 : term152 _120250 a s => @lem5737415 _120222 _120250 f op s x a h0 h1). Qed.
Lemma lem5737417 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op).
Proof. exact (EQ_MP (@lem5737093 _120222 _120250 f op x a s h1 h2) (@lem0)). Qed.
Lemma lem5737418 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (@IN _120250 a s) = ((term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op)).
Proof. exact (prop_ext (fun h3 : @IN _120250 a s => @lem5737417 _120222 _120250 f op x a s h1 h2) (fun h3 : (term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op) => @lem5736857 _120250 a s h2)). Qed.
Lemma lem5737419 {_120222 _120250 : Type'} (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (s : _120250 -> Prop) (h1 : x = a) (h2 : @IN _120250 a s) : (term121 _120222 _120250 s f x op) = (term143 _120222 _120250 x a f op).
Proof. exact (EQ_MP (@lem5737418 _120222 _120250 f op x a s h1 h2) (@lem5736857 _120250 a s h2)). Qed.
Lemma lem5737420 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : term146 _120222 _120250 s x a f op.
Proof. exact (fun h0 : @IN _120250 a s => @lem5737419 _120222 _120250 f op x a s h1 h0). Qed.
Lemma lem5737421 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : term149 _120222 _120250 a s f op x.
Proof. exact (conj (@lem5737420 _120222 _120250 s f op x a h1) (@lem5737416 _120222 _120250 s f op x a h1)). Qed.
Lemma lem5737423 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op).
Proof. exact (EQ_MP (@lem5736908 _120222 _120250 x s a f op) (@lem5737411 _120222 _120250 f s op x a h1)). Qed.
Lemma lem5737424 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term130 _120250 x a) = ((term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (prop_ext (fun h2 : term130 _120250 x a => @lem5737423 _120222 _120250 s f op x a h1) (fun h2 : (term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op) => @lem5736822 _120250 x a h1)). Qed.
Lemma lem5737425 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : term130 _120250 x a) : (term116 _120222 _120250 x s op) = (term88 _120222 _120250 x s a f op).
Proof. exact (EQ_MP (@lem5737424 _120222 _120250 s f op x a h1) (@lem5736822 _120250 x a h1)). Qed.
Lemma lem5737426 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : term119 _120222 _120250 x s a f op.
Proof. exact (fun h0 : term130 _120250 x a => @lem5737425 _120222 _120250 s f op x a h0). Qed.
Lemma lem5737427 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op).
Proof. exact (EQ_MP (@lem5736856 _120222 _120250 x s a f op) (@lem5737421 _120222 _120250 s f op x a h1)). Qed.
Lemma lem5737428 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (x = a) = ((term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op)).
Proof. exact (prop_ext (fun h2 : x = a => @lem5737427 _120222 _120250 s f op x a h1) (fun h2 : (term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op) => @lem5736805 _120250 x a h1)). Qed.
Lemma lem5737429 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) (x : _120250) (a : _120250) (h1 : x = a) : (term121 _120222 _120250 s f x op) = (term88 _120222 _120250 x s a f op).
Proof. exact (EQ_MP (@lem5737428 _120222 _120250 s f op x a h1) (@lem5736805 _120250 x a h1)). Qed.
Lemma lem5737430 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : term124 _120222 _120250 x s a f op.
Proof. exact (fun h0 : x = a => @lem5737429 _120222 _120250 s f op x a h0). Qed.
Lemma lem5737431 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : term127 _120222 _120250 x s a f op.
Proof. exact (conj (@lem5737430 _120222 _120250 x s a f op) (@lem5737426 _120222 _120250 x s a f op)). Qed.
Lemma lem5737432 {_120222 _120250 : Type'} (x : _120250) (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : (term38 _120222 _120250 s a f x op) = (term88 _120222 _120250 x s a f op).
Proof. exact (EQ_MP (@lem5736804 _120222 _120250 x s a f op) (@lem5737431 _120222 _120250 x s a f op)). Qed.
Lemma lem5737437 {_120222 _120250 : Type'} (s : _120250 -> Prop) (a : _120250) (f : _120250 -> _120222) (op : type1400 _120222) : term91 _120222 _120250 s a f op.
Proof. exact (fun x : _120250 => @lem5737432 _120222 _120250 x s a f op). Qed.
Lemma lem5737442 {_120222 _120250 : Type'} (s : _120250 -> Prop) (f : _120250 -> _120222) (op : type1400 _120222) : term95 _120222 _120250 s f op.
Proof. exact (fun a : _120250 => @lem5737437 _120222 _120250 s a f op). Qed.
Lemma lem5737447 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : term99 _120222 _120250 s op.
Proof. exact (fun f : _120250 -> _120222 => @lem5737442 _120222 _120250 s f op). Qed.
Lemma lem5737452 {_120222 _120250 : Type'} (op : type1400 _120222) : term103 _120222 _120250 op.
Proof. exact (fun s : _120250 -> Prop => @lem5737447 _120222 _120250 s op). Qed.
Lemma lem5737457 {_120222 _120250 : Type'} : term107 _120222 _120250.
Proof. exact (fun op : type1400 _120222 => @lem5737452 _120222 _120250 op). Qed.
Lemma lem5737458 {_120222 _120250 : Type'} : term106 _120222 _120250.
Proof. exact (EQ_MP (@lem5736786 _120222 _120250) (@lem5737457 _120222 _120250)). Qed.
