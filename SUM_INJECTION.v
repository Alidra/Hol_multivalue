Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_INJECTION_term_abbrevs.
Require Import ITERATE_INJECTION_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7178549 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7178551 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7178552 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7178551 A B h1 op). Qed.
Lemma lem7178553 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7178554 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7178553 A B op) (@lem7178552 A B op h1)). Qed.
Lemma lem7178555 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7178556 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7178554 A B op h1 (@lem7178555 B op h2)). Qed.
Lemma lem7178557 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7178556 A B op h0 h1). Qed.
Lemma lem7178558 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7178559 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7178557 A B op h2 (@lem7178558 A B h1)). Qed.
Lemma lem7178560 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7178559 A B op h1 h0). Qed.
Lemma lem7178561 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7178560 A B op h1). Qed.
Lemma lem7178562 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7178561 A B h0). Qed.
Lemma lem7178563 {A B : Type'} : term0 A B.
Proof. exact (@lem7178562 A B (@lem6003902 A B)). Qed.
Lemma lem7178564 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7178563 A B op). Qed.
Lemma lem7178565 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7178612 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178613 {_135209 : Type'} : (@sum _135209) = (@iterate real _135209 real_add).
Proof. exact (@lem7178612 _135209). Qed.
Lemma lem7178614 {_135209 : Type'} (s : _135209 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178615 {_135209 : Type'} (s : _135209 -> Prop) : (@sum _135209 s) = (@iterate real _135209 real_add s).
Proof. exact (MK_COMB (@lem7178613 _135209) (@lem7178614 _135209 s)). Qed.
Lemma lem7178616 {_135209 : Type'} (f : _135209 -> real) (p : _135209 -> _135209) : (@o _135209 _135209 real f p) = (@o _135209 _135209 real f p).
Proof. exact (eq_refl (@o _135209 _135209 real f p)). Qed.
Lemma lem7178617 {_135209 : Type'} (s : _135209 -> Prop) (f : _135209 -> real) (p : _135209 -> _135209) : (term6 _135209 s f p) = (term7 _135209 s f p).
Proof. exact (MK_COMB (@lem7178615 _135209 s) (@lem7178616 _135209 f p)). Qed.
Lemma lem7178618 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178619 {_135209 : Type'} (s : _135209 -> Prop) (f : _135209 -> real) (p : _135209 -> _135209) : (term8 _135209 s f p) = (term9 _135209 s f p).
Proof. exact (MK_COMB (@lem7178618) (@lem7178617 _135209 s f p)). Qed.
Lemma lem7178621 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178622 {_135209 : Type'} : (@sum _135209) = (@iterate real _135209 real_add).
Proof. exact (@lem7178621 _135209). Qed.
Lemma lem7178623 {_135209 : Type'} (s : _135209 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178624 {_135209 : Type'} (s : _135209 -> Prop) : (@sum _135209 s) = (@iterate real _135209 real_add s).
Proof. exact (MK_COMB (@lem7178622 _135209) (@lem7178623 _135209 s)). Qed.
Lemma lem7178625 {_135209 : Type'} (f : _135209 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178626 {_135209 : Type'} (s : _135209 -> Prop) (f : _135209 -> real) : (@sum _135209 s f) = (@iterate real _135209 real_add s f).
Proof. exact (MK_COMB (@lem7178624 _135209 s) (@lem7178625 _135209 f)). Qed.
Lemma lem7178627 {_135209 : Type'} (p : _135209 -> _135209) (s : _135209 -> Prop) (f : _135209 -> real) : ((term6 _135209 s f p) = (@sum _135209 s f)) = ((term7 _135209 s f p) = (@iterate real _135209 real_add s f)).
Proof. exact (MK_COMB (@lem7178619 _135209 s f p) (@lem7178626 _135209 s f)). Qed.
Lemma lem7178630 {_135209 : Type'} (s : _135209 -> Prop) (p : _135209 -> _135209) : (term10 _135209 s p) = (term10 _135209 s p).
Proof. exact (eq_refl (term10 _135209 s p)). Qed.
Lemma lem7178631 {_135209 : Type'} (p : _135209 -> _135209) (s : _135209 -> Prop) (f : _135209 -> real) : (term11 _135209 p s f) = (term12 _135209 p s f).
Proof. exact (MK_COMB (@lem7178630 _135209 s p) (@lem7178627 _135209 p s f)). Qed.
Lemma lem7178634 {_135209 : Type'} (p : _135209 -> _135209) (f : _135209 -> real) : (term13 _135209 p f) = (term14 _135209 p f).
Proof. exact (fun_ext (fun s : _135209 -> Prop => @lem7178631 _135209 p s f)). Qed.
Lemma lem7178635 {_135209 : Type'} : (@all (_135209 -> Prop)) = (@all (_135209 -> Prop)).
Proof. exact (eq_refl (@all (_135209 -> Prop))). Qed.
Lemma lem7178636 {_135209 : Type'} (p : _135209 -> _135209) (f : _135209 -> real) : (term15 _135209 p f) = (term16 _135209 p f).
Proof. exact (MK_COMB (@lem7178635 _135209) (@lem7178634 _135209 p f)). Qed.
Lemma lem7178641 {_135209 : Type'} (f : _135209 -> real) : (term17 _135209 f) = (term18 _135209 f).
Proof. exact (fun_ext (fun p : _135209 -> _135209 => @lem7178636 _135209 p f)). Qed.
Lemma lem7178642 {_135209 : Type'} : (@all (_135209 -> _135209)) = (@all (_135209 -> _135209)).
Proof. exact (eq_refl (@all (_135209 -> _135209))). Qed.
Lemma lem7178643 {_135209 : Type'} (f : _135209 -> real) : (term19 _135209 f) = (term20 _135209 f).
Proof. exact (MK_COMB (@lem7178642 _135209) (@lem7178641 _135209 f)). Qed.
Lemma lem7178648 {_135209 : Type'} : (term21 _135209) = (term22 _135209).
Proof. exact (fun_ext (fun f : _135209 -> real => @lem7178643 _135209 f)). Qed.
Lemma lem7178649 {_135209 : Type'} : (@all (_135209 -> real)) = (@all (_135209 -> real)).
Proof. exact (eq_refl (@all (_135209 -> real))). Qed.
Lemma lem7178650 {_135209 : Type'} : (term23 _135209) = (term24 _135209).
Proof. exact (MK_COMB (@lem7178649 _135209) (@lem7178648 _135209)). Qed.
Lemma lem7178655 {_135209 : Type'} : (term24 _135209) = (term23 _135209).
Proof. exact (SYM (@lem7178650 _135209)). Qed.
Lemma lem7178657 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7178565 A B op) (@lem7178564 A B op)). Qed.
Lemma lem7178658 {_135209 : Type'} (op : type1627) : term25 _135209 op.
Proof. exact (@lem7178657 _135209 real op). Qed.
Lemma lem7178659 {_135209 : Type'} : term26 _135209.
Proof. exact (@lem7178658 _135209 real_add). Qed.
Lemma lem7178661 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7178549) (@lem7067132)). Qed.
Lemma lem7178662 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178661)). Qed.
Lemma lem7178663 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178662) (@lem0)). Qed.
Lemma lem7178664 {_135209 : Type'} : term24 _135209.
Proof. exact (@lem7178659 _135209 (@lem7178663)). Qed.
Lemma lem7178665 {_135209 : Type'} : term23 _135209.
Proof. exact (EQ_MP (@lem7178655 _135209) (@lem7178664 _135209)). Qed.
