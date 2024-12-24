Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_COMBINE_R_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FINITE_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import IN_INTER_spec.
Require Import IN_NUMSEG_spec.
Require Import IN_UNION_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUM_UNION_EQ_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7235571 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7235572 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7235573 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7235572 m) (@lem7235571 m)). Qed.
Lemma lem7235574 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7235573 m n). Qed.
Lemma lem7235575 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7235576 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7235575 m n) (@lem7235574 m n)). Qed.
Lemma lem7235577 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7235576 m n p). Qed.
Lemma lem7235578 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7235580 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem7235581 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem7235582 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem7235581 A x) (@lem7235580 A x)). Qed.
Lemma lem7235583 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem7235585 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem7235586 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem7235587 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem7235586 A s) (@lem7235585 A s)). Qed.
Lemma lem7235588 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (@lem7235587 A s t). Qed.
Lemma lem7235589 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = (term13 A s t).
Proof. exact (eq_refl (term12 A s t)). Qed.
Lemma lem7235590 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (EQ_MP (@lem7235589 A s t) (@lem7235588 A s t)). Qed.
Lemma lem7235591 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term14 A s t x.
Proof. exact (@lem7235590 A s t x). Qed.
Lemma lem7235592 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A s t x) = ((term15 A x s t) = (term16 A s x t)).
Proof. exact (eq_refl (term14 A s t x)). Qed.
Lemma lem7235594 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem7235595 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem7235596 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem7235595 A s) (@lem7235594 A s)). Qed.
Lemma lem7235597 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem7235596 A s t). Qed.
Lemma lem7235598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term20 A s t).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem7235599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term20 A s t.
Proof. exact (EQ_MP (@lem7235598 A s t) (@lem7235597 A s t)). Qed.
Lemma lem7235600 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term21 A s t x.
Proof. exact (@lem7235599 A s t x). Qed.
Lemma lem7235601 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A s t x) = ((term22 A x s t) = (term23 A s x t)).
Proof. exact (eq_refl (term21 A s t x)). Qed.
Lemma lem7235603 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7235604 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem7235605 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem7235604 A s) (@lem7235603 A s)). Qed.
Lemma lem7235606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem7235605 A s t). Qed.
Lemma lem7235607 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem7235609 (m : nat) : term28 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7235610 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem7235611 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem7235610 m) (@lem7235609 m)). Qed.
Lemma lem7235612 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem7235611 m n). Qed.
Lemma lem7235613 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem7235614 (m : nat) (n : nat) : term31 m n.
Proof. exact (EQ_MP (@lem7235613 m n) (@lem7235612 m n)). Qed.
Lemma lem7235615 (m : nat) (n : nat) : (term31 m n) = ((term31 m n) = True).
Proof. exact (@lem7 (term31 m n)). Qed.
Lemma lem7235617 {_133751 : Type'} (f : _133751 -> real) (h1 : term32 _133751 f) : term32 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7235618 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term33 _133751 f s.
Proof. exact (@lem7235617 _133751 f h1 s). Qed.
Lemma lem7235619 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term33 _133751 f s) = (term34 _133751 s f).
Proof. exact (eq_refl (term33 _133751 f s)). Qed.
Lemma lem7235620 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term34 _133751 s f.
Proof. exact (EQ_MP (@lem7235619 _133751 s f) (@lem7235618 _133751 s f h1)). Qed.
Lemma lem7235621 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term35 _133751 s f t.
Proof. exact (@lem7235620 _133751 s f h1 t). Qed.
Lemma lem7235622 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term35 _133751 s f t) = (term36 _133751 s t f).
Proof. exact (eq_refl (term35 _133751 s f t)). Qed.
Lemma lem7235623 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term36 _133751 s t f.
Proof. exact (EQ_MP (@lem7235622 _133751 s t f) (@lem7235621 _133751 s t f h1)). Qed.
Lemma lem7235624 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term37 _133751 s t f u.
Proof. exact (@lem7235623 _133751 s t f h1 u). Qed.
Lemma lem7235625 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term37 _133751 s t f u) = (term38 _133751 s t u f).
Proof. exact (eq_refl (term37 _133751 s t f u)). Qed.
Lemma lem7235626 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term38 _133751 s t u f.
Proof. exact (EQ_MP (@lem7235625 _133751 s t u f) (@lem7235624 _133751 s t u f h1)). Qed.
Lemma lem7235627 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (h1 : term39 _133751 s t u) : term39 _133751 s t u.
Proof. exact (h1). Qed.
Lemma lem7235628 {_133751 : Type'} (f : _133751 -> real) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (h1 : term32 _133751 f) (h2 : term39 _133751 s t u) : (term40 _133751 s t f) = (@sum _133751 u f).
Proof. exact (@lem7235626 _133751 s t u f h1 (@lem7235627 _133751 s t u h2)). Qed.
Lemma lem7235629 {_133751 : Type'} (f : _133751 -> real) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (h1 : term39 _133751 s t u) : term41 _133751 s t u f.
Proof. exact (fun h0 : term32 _133751 f => @lem7235628 _133751 f s t u h0 h1). Qed.
Lemma lem7235630 {_133751 : Type'} (f : _133751 -> real) (h1 : term32 _133751 f) : term32 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7235631 {_133751 : Type'} (f : _133751 -> real) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (h1 : term32 _133751 f) (h2 : term39 _133751 s t u) : (term40 _133751 s t f) = (@sum _133751 u f).
Proof. exact (@lem7235629 _133751 f s t u h2 (@lem7235630 _133751 f h1)). Qed.
Lemma lem7235632 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term38 _133751 s t u f.
Proof. exact (fun h0 : term39 _133751 s t u => @lem7235631 _133751 f s t u h1 h0). Qed.
Lemma lem7235633 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term36 _133751 s t f.
Proof. exact (fun u : _133751 -> Prop => @lem7235632 _133751 s t u f h1). Qed.
Lemma lem7235634 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) (h1 : term32 _133751 f) : term34 _133751 s f.
Proof. exact (fun t : _133751 -> Prop => @lem7235633 _133751 s t f h1). Qed.
Lemma lem7235635 {_133751 : Type'} (f : _133751 -> real) (h1 : term32 _133751 f) : term32 _133751 f.
Proof. exact (fun s : _133751 -> Prop => @lem7235634 _133751 s f h1). Qed.
Lemma lem7235636 {_133751 : Type'} (f : _133751 -> real) : term42 _133751 f.
Proof. exact (fun h0 : term32 _133751 f => @lem7235635 _133751 f h0). Qed.
Lemma lem7235637 {_133751 : Type'} (f : _133751 -> real) : term32 _133751 f.
Proof. exact (@lem7235636 _133751 f (@lem7153073 _133751 f)). Qed.
Lemma lem7235638 {_133751 : Type'} (f : _133751 -> real) (s : _133751 -> Prop) : term33 _133751 f s.
Proof. exact (@lem7235637 _133751 f s). Qed.
Lemma lem7235639 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term33 _133751 f s) = (term34 _133751 s f).
Proof. exact (eq_refl (term33 _133751 f s)). Qed.
Lemma lem7235640 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : term34 _133751 s f.
Proof. exact (EQ_MP (@lem7235639 _133751 s f) (@lem7235638 _133751 f s)). Qed.
Lemma lem7235641 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) (t : _133751 -> Prop) : term35 _133751 s f t.
Proof. exact (@lem7235640 _133751 s f t). Qed.
Lemma lem7235642 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term35 _133751 s f t) = (term36 _133751 s t f).
Proof. exact (eq_refl (term35 _133751 s f t)). Qed.
Lemma lem7235643 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : term36 _133751 s t f.
Proof. exact (EQ_MP (@lem7235642 _133751 s t f) (@lem7235641 _133751 s f t)). Qed.
Lemma lem7235644 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (u : _133751 -> Prop) : term37 _133751 s t f u.
Proof. exact (@lem7235643 _133751 s t f u). Qed.
Lemma lem7235645 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term37 _133751 s t f u) = (term38 _133751 s t u f).
Proof. exact (eq_refl (term37 _133751 s t f u)). Qed.
Lemma lem7235647 (m : nat) (n : nat) (p : nat) (h1 : term43 m n p) : term43 m n p.
Proof. exact (h1). Qed.
Lemma lem7235648 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem7235649 (m : nat) (n : nat) (h1 : term44 m n) : term44 m n.
Proof. exact (h1). Qed.
Lemma lem7235651 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : term38 _133751 s t u f.
Proof. exact (EQ_MP (@lem7235645 _133751 s t u f) (@lem7235644 _133751 s t f u)). Qed.
Lemma lem7235652 (s : nat -> Prop) (t : nat -> Prop) (u : nat -> Prop) (f : nat -> real) : term45 s t u f.
Proof. exact (@lem7235651 nat s t u f). Qed.
Lemma lem7235653 (n : nat) (m : nat) (p : nat) (f : nat -> real) : term46 n m p f.
Proof. exact (@lem7235652 (dotdot m n) (term47 n p) (dotdot m p) f). Qed.
Lemma lem7235657 (m : nat) (n : nat) : (term31 m n) = True.
Proof. exact (EQ_MP (@lem7235615 m n) (@lem7235614 m n)). Qed.
Lemma lem7235658 (m : nat) (p : nat) : (term31 m p) = True.
Proof. exact (@lem7235657 m p). Qed.
Lemma lem7235659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235660 (m : nat) (p : nat) : (term48 m p) = (and True).
Proof. exact (MK_COMB (@lem7235659) (@lem7235658 m p)). Qed.
Lemma lem7235666 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem7235607 A s t) (@lem7235606 A s t)). Qed.
Lemma lem7235667 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term49 s t).
Proof. exact (@lem7235666 nat s t). Qed.
Lemma lem7235668 (m : nat) (n : nat) (p : nat) : ((term50 m n p) = (@EMPTY nat)) = (term51 m n p).
Proof. exact (@lem7235667 (term50 m n p) (@EMPTY nat)). Qed.
Lemma lem7235678 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem7235601 A s x t) (@lem7235600 A s t x)). Qed.
Lemma lem7235679 (s : nat -> Prop) (x : nat) (t : nat -> Prop) : (term52 x s t) = (term53 s x t).
Proof. exact (@lem7235678 nat s x t). Qed.
Lemma lem7235680 (m : nat) (x : nat) (n : nat) (p : nat) : (term54 x m n p) = (term55 m x n p).
Proof. exact (@lem7235679 (dotdot m n) x (term47 n p)). Qed.
Lemma lem7235684 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7235578 m p n) (@lem7235577 m n p)). Qed.
Lemma lem7235685 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7235684 m x n). Qed.
Lemma lem7235688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235689 (m : nat) (x : nat) (n : nat) : (term56 x m n) = (term57 m x n).
Proof. exact (MK_COMB (@lem7235688) (@lem7235685 m x n)). Qed.
Lemma lem7235691 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7235578 m p n) (@lem7235577 m n p)). Qed.
Lemma lem7235692 (n : nat) (x : nat) (p : nat) : (term58 x n p) = (term59 n x p).
Proof. exact (@lem7235691 (term60 n) x p). Qed.
Lemma lem7235695 (m : nat) (n : nat) (x : nat) (p : nat) : (term55 m x n p) = (term61 m n x p).
Proof. exact (MK_COMB (@lem7235689 m x n) (@lem7235692 n x p)). Qed.
Lemma lem7235698 (m : nat) (n : nat) (x : nat) (p : nat) : (term54 x m n p) = (term61 m n x p).
Proof. exact (TRANS (@lem7235680 m x n p) (@lem7235695 m n x p)). Qed.
Lemma lem7235699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7235700 (m : nat) (n : nat) (x : nat) (p : nat) : (term62 x m n p) = (term63 m n x p).
Proof. exact (MK_COMB (@lem7235699) (@lem7235698 m n x p)). Qed.
Lemma lem7235702 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7235583 A x (@lem7235582 A x)). Qed.
Lemma lem7235703 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem7235702 nat x). Qed.
Lemma lem7235704 (m : nat) (n : nat) (x : nat) (p : nat) : ((term54 x m n p) = (@IN nat x (@EMPTY nat))) = ((term61 m n x p) = False).
Proof. exact (MK_COMB (@lem7235700 m n x p) (@lem7235703 x)). Qed.
Lemma lem7235706 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7235707 (m : nat) (n : nat) (x : nat) (p : nat) : ((term61 m n x p) = False) = (term64 m n x p).
Proof. exact (@lem7235706 (term61 m n x p)). Qed.
Lemma lem7235714 (m : nat) (n : nat) (x : nat) (p : nat) : ((term54 x m n p) = (@IN nat x (@EMPTY nat))) = (term64 m n x p).
Proof. exact (TRANS (@lem7235704 m n x p) (@lem7235707 m n x p)). Qed.
Lemma lem7235715 (m : nat) (n : nat) (p : nat) : (term65 m n p) = (term66 m n p).
Proof. exact (fun_ext (fun x : nat => @lem7235714 m n x p)). Qed.
Lemma lem7235716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7235717 (m : nat) (n : nat) (p : nat) : (term51 m n p) = (term67 m n p).
Proof. exact (MK_COMB (@lem7235716) (@lem7235715 m n p)). Qed.
Lemma lem7235722 (m : nat) (n : nat) (p : nat) : ((term50 m n p) = (@EMPTY nat)) = (term67 m n p).
Proof. exact (TRANS (@lem7235668 m n p) (@lem7235717 m n p)). Qed.
Lemma lem7235723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235724 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem7235723) (@lem7235722 m n p)). Qed.
Lemma lem7235728 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem7235607 A s t) (@lem7235606 A s t)). Qed.
Lemma lem7235729 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term49 s t).
Proof. exact (@lem7235728 nat s t). Qed.
Lemma lem7235730 (n : nat) (m : nat) (p : nat) : ((term70 m n p) = (dotdot m p)) = (term71 n m p).
Proof. exact (@lem7235729 (term70 m n p) (dotdot m p)). Qed.
Lemma lem7235740 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem7235592 A s x t) (@lem7235591 A s t x)). Qed.
Lemma lem7235741 (s : nat -> Prop) (x : nat) (t : nat -> Prop) : (term72 x s t) = (term73 s x t).
Proof. exact (@lem7235740 nat s x t). Qed.
Lemma lem7235742 (m : nat) (x : nat) (n : nat) (p : nat) : (term74 x m n p) = (term75 m x n p).
Proof. exact (@lem7235741 (dotdot m n) x (term47 n p)). Qed.
Lemma lem7235746 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7235578 m p n) (@lem7235577 m n p)). Qed.
Lemma lem7235747 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7235746 m x n). Qed.
Lemma lem7235750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7235751 (m : nat) (x : nat) (n : nat) : (term76 x m n) = (term77 m x n).
Proof. exact (MK_COMB (@lem7235750) (@lem7235747 m x n)). Qed.
Lemma lem7235753 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7235578 m p n) (@lem7235577 m n p)). Qed.
Lemma lem7235754 (n : nat) (x : nat) (p : nat) : (term58 x n p) = (term59 n x p).
Proof. exact (@lem7235753 (term60 n) x p). Qed.
Lemma lem7235757 (m : nat) (n : nat) (x : nat) (p : nat) : (term75 m x n p) = (term78 m n x p).
Proof. exact (MK_COMB (@lem7235751 m x n) (@lem7235754 n x p)). Qed.
Lemma lem7235760 (m : nat) (n : nat) (x : nat) (p : nat) : (term74 x m n p) = (term78 m n x p).
Proof. exact (TRANS (@lem7235742 m x n p) (@lem7235757 m n x p)). Qed.
Lemma lem7235761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7235762 (m : nat) (n : nat) (x : nat) (p : nat) : (term79 x m n p) = (term80 m n x p).
Proof. exact (MK_COMB (@lem7235761) (@lem7235760 m n x p)). Qed.
Lemma lem7235764 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7235578 m p n) (@lem7235577 m n p)). Qed.
Lemma lem7235765 (m : nat) (x : nat) (p : nat) : (term5 x m p) = (term6 m x p).
Proof. exact (@lem7235764 m x p). Qed.
Lemma lem7235768 (n : nat) (m : nat) (x : nat) (p : nat) : ((term74 x m n p) = (term5 x m p)) = ((term78 m n x p) = (term6 m x p)).
Proof. exact (MK_COMB (@lem7235762 m n x p) (@lem7235765 m x p)). Qed.
Lemma lem7235773 (n : nat) (m : nat) (p : nat) : (term81 n m p) = (term82 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7235768 n m x p)). Qed.
Lemma lem7235774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7235775 (n : nat) (m : nat) (p : nat) : (term71 n m p) = (term83 n m p).
Proof. exact (MK_COMB (@lem7235774) (@lem7235773 n m p)). Qed.
Lemma lem7235780 (n : nat) (m : nat) (p : nat) : ((term70 m n p) = (dotdot m p)) = (term83 n m p).
Proof. exact (TRANS (@lem7235730 n m p) (@lem7235775 n m p)). Qed.
Lemma lem7235781 (n : nat) (m : nat) (p : nat) : (term84 n m p) = (term85 n m p).
Proof. exact (MK_COMB (@lem7235724 m n p) (@lem7235780 n m p)). Qed.
Lemma lem7235784 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term87 n m p).
Proof. exact (MK_COMB (@lem7235660 m p) (@lem7235781 n m p)). Qed.
Lemma lem7235786 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7235787 (n : nat) (m : nat) (p : nat) : (term87 n m p) = (term85 n m p).
Proof. exact (@lem7235786 (term85 n m p)). Qed.
Lemma lem7235816 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term85 n m p).
Proof. exact (TRANS (@lem7235784 n m p) (@lem7235787 n m p)). Qed.
Lemma lem7235817 (n : nat) (m : nat) (p : nat) : (term85 n m p) = (term86 n m p).
Proof. exact (SYM (@lem7235816 n m p)). Qed.
Lemma lem7235869 (n : nat) (m : nat) (x : nat) (p : nat) : ((term78 m n x p) = (term6 m x p)) = ((term78 m n x p) = (term6 m x p)).
Proof. exact (eq_refl ((term78 m n x p) = (term6 m x p))). Qed.
Lemma lem7235870 (n : nat) (m : nat) (p : nat) : (term82 n m p) = (term82 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7235869 n m x p)). Qed.
Lemma lem7235871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7235872 (n : nat) (m : nat) (p : nat) : (term83 n m p) = (term83 n m p).
Proof. exact (MK_COMB (@lem7235871) (@lem7235870 n m p)). Qed.
Lemma lem7235887 (m : nat) (n : nat) (x : nat) (p : nat) : (term64 m n x p) = (term64 m n x p).
Proof. exact (eq_refl (term64 m n x p)). Qed.
Lemma lem7235888 (m : nat) (n : nat) (p : nat) : (term66 m n p) = (term66 m n p).
Proof. exact (fun_ext (fun x : nat => @lem7235887 m n x p)). Qed.
Lemma lem7235889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7235890 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term67 m n p).
Proof. exact (MK_COMB (@lem7235889) (@lem7235888 m n p)). Qed.
Lemma lem7235891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235892 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem7235891) (@lem7235890 m n p)). Qed.
Lemma lem7235893 (n : nat) (m : nat) (p : nat) : (term85 n m p) = (term85 n m p).
Proof. exact (MK_COMB (@lem7235892 m n p) (@lem7235872 n m p)). Qed.
Lemma lem7235896 (n : nat) (p : nat) : (term88 n p) = (term88 n p).
Proof. exact (eq_refl (term88 n p)). Qed.
Lemma lem7235897 (n : nat) (m : nat) (p : nat) : (term89 n m p) = (term89 n m p).
Proof. exact (MK_COMB (@lem7235896 n p) (@lem7235893 n m p)). Qed.
Lemma lem7235900 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem7235902 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term91 n m p).
Proof. exact (MK_COMB (@lem7235900 m n) (@lem7235897 n m p)). Qed.
Lemma lem7235911 (m : nat) (x : nat) (n : nat) : (term92 m x n) = (term93 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem7235918 (n : nat) (x : nat) (p : nat) : (term94 n x p) = (term95 n x p).
Proof. exact (@lem17045 (term96 n x) (Peano.le x p)). Qed.
Lemma lem7235919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7235920 (m : nat) (x : nat) (n : nat) : (term97 m x n) = (term98 m x n).
Proof. exact (MK_COMB (@lem7235919) (@lem7235911 m x n)). Qed.
Lemma lem7235921 (m : nat) (n : nat) (x : nat) (p : nat) : (term99 m n x p) = (term100 m n x p).
Proof. exact (MK_COMB (@lem7235920 m x n) (@lem7235918 n x p)). Qed.
Lemma lem7235922 (m : nat) (n : nat) (x : nat) (p : nat) : (term64 m n x p) = (term99 m n x p).
Proof. exact (@lem17045 (term6 m x n) (term59 n x p)). Qed.
Lemma lem7235923 (m : nat) (n : nat) (x : nat) (p : nat) : (term64 m n x p) = (term100 m n x p).
Proof. exact (TRANS (@lem7235922 m n x p) (@lem7235921 m n x p)). Qed.
Lemma lem7235924 (m : nat) (n : nat) (p : nat) : (term66 m n p) = (term101 m n p).
Proof. exact (fun_ext (fun x : nat => @lem7235923 m n x p)). Qed.
Lemma lem7235925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7235926 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term102 m n p).
Proof. exact (MK_COMB (@lem7235925) (@lem7235924 m n p)). Qed.
Lemma lem7235935 (m : nat) (x : nat) (n : nat) : (term92 m x n) = (term93 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem7235947 (n : nat) (x : nat) (p : nat) : (term94 n x p) = (term95 n x p).
Proof. exact (@lem17045 (term96 n x) (Peano.le x p)). Qed.
Lemma lem7235951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235952 (m : nat) (x : nat) (n : nat) : (term103 m x n) = (term104 m x n).
Proof. exact (MK_COMB (@lem7235951) (@lem7235935 m x n)). Qed.
Lemma lem7235953 (m : nat) (n : nat) (x : nat) (p : nat) : (term105 m n x p) = (term106 m n x p).
Proof. exact (MK_COMB (@lem7235952 m x n) (@lem7235947 n x p)). Qed.
Lemma lem7235954 (m : nat) (n : nat) (x : nat) (p : nat) : (term107 m n x p) = (term105 m n x p).
Proof. exact (@lem17160 (term6 m x n) (term59 n x p)). Qed.
Lemma lem7235955 (m : nat) (n : nat) (x : nat) (p : nat) : (term107 m n x p) = (term106 m n x p).
Proof. exact (TRANS (@lem7235954 m n x p) (@lem7235953 m n x p)). Qed.
Lemma lem7235967 (m : nat) (x : nat) (p : nat) : (term92 m x p) = (term93 m x p).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x p)). Qed.
Lemma lem7235970 (m : nat) (x : nat) (p : nat) : (term6 m x p) = (term6 m x p).
Proof. exact (eq_refl (term6 m x p)). Qed.
Lemma lem7235971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7235972 (m : nat) (n : nat) (x : nat) (p : nat) : (term108 m n x p) = (term109 m n x p).
Proof. exact (MK_COMB (@lem7235971) (@lem7235955 m n x p)). Qed.
Lemma lem7235973 (n : nat) (m : nat) (x : nat) (p : nat) : (term110 n m x p) = (term111 n m x p).
Proof. exact (MK_COMB (@lem7235972 m n x p) (@lem7235970 m x p)). Qed.
Lemma lem7235975 (m : nat) (n : nat) (x : nat) (p : nat) : (term112 m n x p) = (term112 m n x p).
Proof. exact (eq_refl (term112 m n x p)). Qed.
Lemma lem7235976 (n : nat) (m : nat) (x : nat) (p : nat) : (term113 n m x p) = (term114 n m x p).
Proof. exact (MK_COMB (@lem7235975 m n x p) (@lem7235967 m x p)). Qed.
Lemma lem7235977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235978 (n : nat) (m : nat) (x : nat) (p : nat) : (term115 n m x p) = (term116 n m x p).
Proof. exact (MK_COMB (@lem7235977) (@lem7235976 n m x p)). Qed.
Lemma lem7235979 (n : nat) (m : nat) (x : nat) (p : nat) : (term117 n m x p) = (term118 n m x p).
Proof. exact (MK_COMB (@lem7235978 n m x p) (@lem7235973 n m x p)). Qed.
Lemma lem7235980 (n : nat) (m : nat) (x : nat) (p : nat) : ((term78 m n x p) = (term6 m x p)) = (term117 n m x p).
Proof. exact (@lem17784 (term78 m n x p) (term6 m x p)). Qed.
Lemma lem7235981 (n : nat) (m : nat) (x : nat) (p : nat) : ((term78 m n x p) = (term6 m x p)) = (term118 n m x p).
Proof. exact (TRANS (@lem7235980 n m x p) (@lem7235979 n m x p)). Qed.
Lemma lem7235982 (n : nat) (m : nat) (p : nat) : (term82 n m p) = (term119 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7235981 n m x p)). Qed.
Lemma lem7235983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7235984 (n : nat) (m : nat) (p : nat) : (term83 n m p) = (term120 n m p).
Proof. exact (MK_COMB (@lem7235983) (@lem7235982 n m p)). Qed.
Lemma lem7235985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235986 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term121 m n p).
Proof. exact (MK_COMB (@lem7235985) (@lem7235926 m n p)). Qed.
Lemma lem7235987 (n : nat) (m : nat) (p : nat) : (term85 n m p) = (term122 n m p).
Proof. exact (MK_COMB (@lem7235986 m n p) (@lem7235984 n m p)). Qed.
Lemma lem7235989 (n : nat) (p : nat) : (term123 n p) = (term123 n p).
Proof. exact (eq_refl (term123 n p)). Qed.
Lemma lem7235990 (n : nat) (m : nat) (p : nat) : (term124 n m p) = (term125 n m p).
Proof. exact (MK_COMB (@lem7235989 n p) (@lem7235987 n m p)). Qed.
Lemma lem7235991 (n : nat) (m : nat) (p : nat) : (term89 n m p) = (term124 n m p).
Proof. exact (@lem17265 (Peano.le n p) (term85 n m p)). Qed.
Lemma lem7235992 (n : nat) (m : nat) (p : nat) : (term89 n m p) = (term125 n m p).
Proof. exact (TRANS (@lem7235991 n m p) (@lem7235990 n m p)). Qed.
Lemma lem7235994 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem7235995 (n : nat) (m : nat) (p : nat) : (term127 n m p) = (term128 n m p).
Proof. exact (MK_COMB (@lem7235994 m n) (@lem7235992 n m p)). Qed.
Lemma lem7235996 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term127 n m p).
Proof. exact (@lem17265 (term44 m n) (term89 n m p)). Qed.
Lemma lem7235997 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term128 n m p).
Proof. exact (TRANS (@lem7235996 n m p) (@lem7235995 n m p)). Qed.
Lemma lem7235998 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term128 n m p).
Proof. exact (TRANS (@lem7235902 n m p) (@lem7235997 n m p)). Qed.
Lemma lem7235999 (n : nat) (m : nat) (x : nat) (p : nat) : (term118 n m x p) = (term118 n m x p).
Proof. exact (eq_refl (term118 n m x p)). Qed.
Lemma lem7236000 (n : nat) (m : nat) (p : nat) : (term119 n m p) = (term119 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7235999 n m x p)). Qed.
Lemma lem7236001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236002 (n : nat) (m : nat) (p : nat) : (term120 n m p) = (term120 n m p).
Proof. exact (MK_COMB (@lem7236001) (@lem7236000 n m p)). Qed.
Lemma lem7236003 (m : nat) (n : nat) (x : nat) (p : nat) : (term100 m n x p) = (term100 m n x p).
Proof. exact (eq_refl (term100 m n x p)). Qed.
Lemma lem7236004 (m : nat) (n : nat) (p : nat) : (term101 m n p) = (term101 m n p).
Proof. exact (fun_ext (fun x : nat => @lem7236003 m n x p)). Qed.
Lemma lem7236005 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236006 (m : nat) (n : nat) (p : nat) : (term102 m n p) = (term102 m n p).
Proof. exact (MK_COMB (@lem7236005) (@lem7236004 m n p)). Qed.
Lemma lem7236007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236008 (m : nat) (n : nat) (p : nat) : (term121 m n p) = (term121 m n p).
Proof. exact (MK_COMB (@lem7236007) (@lem7236006 m n p)). Qed.
Lemma lem7236009 (n : nat) (m : nat) (p : nat) : (term122 n m p) = (term122 n m p).
Proof. exact (MK_COMB (@lem7236008 m n p) (@lem7236002 n m p)). Qed.
Lemma lem7236012 (n : nat) (p : nat) : (term123 n p) = (term123 n p).
Proof. exact (eq_refl (term123 n p)). Qed.
Lemma lem7236013 (n : nat) (m : nat) (p : nat) : (term125 n m p) = (term125 n m p).
Proof. exact (MK_COMB (@lem7236012 n p) (@lem7236009 n m p)). Qed.
Lemma lem7236016 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem7236017 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term128 n m p).
Proof. exact (MK_COMB (@lem7236016 m n) (@lem7236013 n m p)). Qed.
Lemma lem7236066 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term128 n m p).
Proof. exact (TRANS (@lem7235998 n m p) (@lem7236017 n m p)). Qed.
Lemma lem7236183 (n : nat) (m : nat) (x : nat) (p : nat) : (term118 n m x p) = (term118 n m x p).
Proof. exact (eq_refl (term118 n m x p)). Qed.
Lemma lem7236184 (n : nat) (m : nat) (p : nat) : (term119 n m p) = (term119 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236183 n m x p)). Qed.
Lemma lem7236185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236186 (n : nat) (m : nat) (p : nat) : (term120 n m p) = (term120 n m p).
Proof. exact (MK_COMB (@lem7236185) (@lem7236184 n m p)). Qed.
Lemma lem7236229 (m : nat) (n : nat) (x : nat) (p : nat) : (term100 m n x p) = (term100 m n x p).
Proof. exact (eq_refl (term100 m n x p)). Qed.
Lemma lem7236230 (m : nat) (n : nat) (p : nat) : (term101 m n p) = (term101 m n p).
Proof. exact (fun_ext (fun x : nat => @lem7236229 m n x p)). Qed.
Lemma lem7236231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236232 (m : nat) (n : nat) (p : nat) : (term102 m n p) = (term102 m n p).
Proof. exact (MK_COMB (@lem7236231) (@lem7236230 m n p)). Qed.
Lemma lem7236233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236234 (m : nat) (n : nat) (p : nat) : (term121 m n p) = (term121 m n p).
Proof. exact (MK_COMB (@lem7236233) (@lem7236232 m n p)). Qed.
Lemma lem7236235 (n : nat) (m : nat) (p : nat) : (term122 n m p) = (term122 n m p).
Proof. exact (MK_COMB (@lem7236234 m n p) (@lem7236186 n m p)). Qed.
Lemma lem7236244 (n : nat) (p : nat) : (term123 n p) = (term123 n p).
Proof. exact (eq_refl (term123 n p)). Qed.
Lemma lem7236245 (n : nat) (m : nat) (p : nat) : (term125 n m p) = (term125 n m p).
Proof. exact (MK_COMB (@lem7236244 n p) (@lem7236235 n m p)). Qed.
Lemma lem7236260 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem7236261 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term128 n m p).
Proof. exact (MK_COMB (@lem7236260 m n) (@lem7236245 n m p)). Qed.
Lemma lem7236262 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term128 n m p).
Proof. exact (TRANS (@lem7236066 n m p) (@lem7236261 n m p)). Qed.
Lemma lem7236264 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem7236265 (P : nat -> Prop) (Q : nat -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem7236264 nat P Q). Qed.
Lemma lem7236266 (n : nat) (m : nat) (p : nat) : (term133 n m p) = (term134 n m p).
Proof. exact (@lem7236265 (term101 m n p) (term119 n m p)). Qed.
Lemma lem7236267 (m : nat) (n : nat) (x : nat) (p : nat) : (term135 m n p x) = (term100 m n x p).
Proof. exact (eq_refl (term135 m n p x)). Qed.
Lemma lem7236268 (m : nat) (n : nat) (p : nat) : (term136 m n p) = (term101 m n p).
Proof. exact (fun_ext (fun x : nat => @lem7236267 m n x p)). Qed.
Lemma lem7236269 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236270 (m : nat) (n : nat) (p : nat) : (term137 m n p) = (term102 m n p).
Proof. exact (MK_COMB (@lem7236269) (@lem7236268 m n p)). Qed.
Lemma lem7236271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236272 (m : nat) (n : nat) (p : nat) : (term138 m n p) = (term121 m n p).
Proof. exact (MK_COMB (@lem7236271) (@lem7236270 m n p)). Qed.
Lemma lem7236273 (n : nat) (m : nat) (x : nat) (p : nat) : (term139 n m p x) = (term118 n m x p).
Proof. exact (eq_refl (term139 n m p x)). Qed.
Lemma lem7236274 (n : nat) (m : nat) (p : nat) : (term140 n m p) = (term119 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236273 n m x p)). Qed.
Lemma lem7236275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236276 (n : nat) (m : nat) (p : nat) : (term141 n m p) = (term120 n m p).
Proof. exact (MK_COMB (@lem7236275) (@lem7236274 n m p)). Qed.
Lemma lem7236277 (n : nat) (m : nat) (p : nat) : (term133 n m p) = (term122 n m p).
Proof. exact (MK_COMB (@lem7236272 m n p) (@lem7236276 n m p)). Qed.
Lemma lem7236278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7236279 (n : nat) (m : nat) (p : nat) : (term142 n m p) = (term143 n m p).
Proof. exact (MK_COMB (@lem7236278) (@lem7236277 n m p)). Qed.
Lemma lem7236280 (m : nat) (n : nat) (x : nat) (p : nat) : (term135 m n p x) = (term100 m n x p).
Proof. exact (eq_refl (term135 m n p x)). Qed.
Lemma lem7236281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236282 (m : nat) (n : nat) (x : nat) (p : nat) : (term144 m n p x) = (term145 m n x p).
Proof. exact (MK_COMB (@lem7236281) (@lem7236280 m n x p)). Qed.
Lemma lem7236283 (n : nat) (m : nat) (x : nat) (p : nat) : (term139 n m p x) = (term118 n m x p).
Proof. exact (eq_refl (term139 n m p x)). Qed.
Lemma lem7236284 (n : nat) (m : nat) (x : nat) (p : nat) : (term146 n m p x) = (term147 n m x p).
Proof. exact (MK_COMB (@lem7236282 m n x p) (@lem7236283 n m x p)). Qed.
Lemma lem7236285 (n : nat) (m : nat) (p : nat) : (term148 n m p) = (term149 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236284 n m x p)). Qed.
Lemma lem7236286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236287 (n : nat) (m : nat) (p : nat) : (term134 n m p) = (term150 n m p).
Proof. exact (MK_COMB (@lem7236286) (@lem7236285 n m p)). Qed.
Lemma lem7236288 (n : nat) (m : nat) (p : nat) : ((term133 n m p) = (term134 n m p)) = ((term122 n m p) = (term150 n m p)).
Proof. exact (MK_COMB (@lem7236279 n m p) (@lem7236287 n m p)). Qed.
Lemma lem7236289 (n : nat) (m : nat) (p : nat) : (term122 n m p) = (term150 n m p).
Proof. exact (EQ_MP (@lem7236288 n m p) (@lem7236266 n m p)). Qed.
Lemma lem7236290 (n : nat) (p : nat) : (term123 n p) = (term123 n p).
Proof. exact (eq_refl (term123 n p)). Qed.
Lemma lem7236291 (n : nat) (m : nat) (p : nat) : (term125 n m p) = (term151 n m p).
Proof. exact (MK_COMB (@lem7236290 n p) (@lem7236289 n m p)). Qed.
Lemma lem7236293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7236294 (P : Prop) (Q : nat -> Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem7236293 nat P Q). Qed.
Lemma lem7236295 (n : nat) (m : nat) (p : nat) : (term156 n m p) = (term157 n m p).
Proof. exact (@lem7236294 (term158 n p) (term149 n m p)). Qed.
Lemma lem7236296 (n : nat) (m : nat) (x : nat) (p : nat) : (term159 n m p x) = (term147 n m x p).
Proof. exact (eq_refl (term159 n m p x)). Qed.
Lemma lem7236297 (n : nat) (m : nat) (p : nat) : (term160 n m p) = (term149 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236296 n m x p)). Qed.
Lemma lem7236298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236299 (n : nat) (m : nat) (p : nat) : (term161 n m p) = (term150 n m p).
Proof. exact (MK_COMB (@lem7236298) (@lem7236297 n m p)). Qed.
Lemma lem7236300 (n : nat) (p : nat) : (term123 n p) = (term123 n p).
Proof. exact (eq_refl (term123 n p)). Qed.
Lemma lem7236301 (n : nat) (m : nat) (p : nat) : (term156 n m p) = (term151 n m p).
Proof. exact (MK_COMB (@lem7236300 n p) (@lem7236299 n m p)). Qed.
Lemma lem7236302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7236303 (n : nat) (m : nat) (p : nat) : (term162 n m p) = (term163 n m p).
Proof. exact (MK_COMB (@lem7236302) (@lem7236301 n m p)). Qed.
Lemma lem7236304 (n : nat) (m : nat) (x : nat) (p : nat) : (term159 n m p x) = (term147 n m x p).
Proof. exact (eq_refl (term159 n m p x)). Qed.
Lemma lem7236305 (n : nat) (p : nat) : (term123 n p) = (term123 n p).
Proof. exact (eq_refl (term123 n p)). Qed.
Lemma lem7236306 (n : nat) (m : nat) (x : nat) (p : nat) : (term164 n m p x) = (term165 n m x p).
Proof. exact (MK_COMB (@lem7236305 n p) (@lem7236304 n m x p)). Qed.
Lemma lem7236307 (n : nat) (m : nat) (p : nat) : (term166 n m p) = (term167 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236306 n m x p)). Qed.
Lemma lem7236308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236309 (n : nat) (m : nat) (p : nat) : (term157 n m p) = (term168 n m p).
Proof. exact (MK_COMB (@lem7236308) (@lem7236307 n m p)). Qed.
Lemma lem7236310 (n : nat) (m : nat) (p : nat) : ((term156 n m p) = (term157 n m p)) = ((term151 n m p) = (term168 n m p)).
Proof. exact (MK_COMB (@lem7236303 n m p) (@lem7236309 n m p)). Qed.
Lemma lem7236311 (n : nat) (m : nat) (p : nat) : (term151 n m p) = (term168 n m p).
Proof. exact (EQ_MP (@lem7236310 n m p) (@lem7236295 n m p)). Qed.
Lemma lem7236312 (n : nat) (m : nat) (p : nat) : (term125 n m p) = (term168 n m p).
Proof. exact (TRANS (@lem7236291 n m p) (@lem7236311 n m p)). Qed.
Lemma lem7236313 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem7236314 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term169 n m p).
Proof. exact (MK_COMB (@lem7236313 m n) (@lem7236312 n m p)). Qed.
Lemma lem7236316 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7236317 (P : Prop) (Q : nat -> Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem7236316 nat P Q). Qed.
Lemma lem7236318 (n : nat) (m : nat) (p : nat) : (term170 n m p) = (term171 n m p).
Proof. exact (@lem7236317 (term172 m n) (term167 n m p)). Qed.
Lemma lem7236319 (n : nat) (m : nat) (x : nat) (p : nat) : (term173 n m p x) = (term165 n m x p).
Proof. exact (eq_refl (term173 n m p x)). Qed.
Lemma lem7236320 (n : nat) (m : nat) (p : nat) : (term174 n m p) = (term167 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236319 n m x p)). Qed.
Lemma lem7236321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236322 (n : nat) (m : nat) (p : nat) : (term175 n m p) = (term168 n m p).
Proof. exact (MK_COMB (@lem7236321) (@lem7236320 n m p)). Qed.
Lemma lem7236323 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem7236324 (n : nat) (m : nat) (p : nat) : (term170 n m p) = (term169 n m p).
Proof. exact (MK_COMB (@lem7236323 m n) (@lem7236322 n m p)). Qed.
Lemma lem7236325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7236326 (n : nat) (m : nat) (p : nat) : (term176 n m p) = (term177 n m p).
Proof. exact (MK_COMB (@lem7236325) (@lem7236324 n m p)). Qed.
Lemma lem7236327 (n : nat) (m : nat) (x : nat) (p : nat) : (term173 n m p x) = (term165 n m x p).
Proof. exact (eq_refl (term173 n m p x)). Qed.
Lemma lem7236328 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem7236329 (n : nat) (m : nat) (x : nat) (p : nat) : (term178 n m p x) = (term179 n m x p).
Proof. exact (MK_COMB (@lem7236328 m n) (@lem7236327 n m x p)). Qed.
Lemma lem7236330 (n : nat) (m : nat) (p : nat) : (term180 n m p) = (term181 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236329 n m x p)). Qed.
Lemma lem7236331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236332 (n : nat) (m : nat) (p : nat) : (term171 n m p) = (term182 n m p).
Proof. exact (MK_COMB (@lem7236331) (@lem7236330 n m p)). Qed.
Lemma lem7236333 (n : nat) (m : nat) (p : nat) : ((term170 n m p) = (term171 n m p)) = ((term169 n m p) = (term182 n m p)).
Proof. exact (MK_COMB (@lem7236326 n m p) (@lem7236332 n m p)). Qed.
Lemma lem7236334 (n : nat) (m : nat) (p : nat) : (term169 n m p) = (term182 n m p).
Proof. exact (EQ_MP (@lem7236333 n m p) (@lem7236318 n m p)). Qed.
Lemma lem7236335 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term182 n m p).
Proof. exact (TRANS (@lem7236314 n m p) (@lem7236334 n m p)). Qed.
Lemma lem7236336 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term182 n m p).
Proof. exact (TRANS (@lem7236262 n m p) (@lem7236335 n m p)). Qed.
Lemma lem7236338 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236339 (m : nat) (n : nat) : (term44 m n) = (term184 m n).
Proof. exact (@lem7236338 m (term60 n)). Qed.
Lemma lem7236341 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7236342 (n : nat) : (term187 n) = (term188 n).
Proof. exact (@lem7236341 n term189). Qed.
Lemma lem7236343 (m : nat) : (term190 m) = (term190 m).
Proof. exact (eq_refl (term190 m)). Qed.
Lemma lem7236344 (m : nat) (n : nat) : (term184 m n) = (term191 m n).
Proof. exact (MK_COMB (@lem7236343 m) (@lem7236342 n)). Qed.
Lemma lem7236345 (m : nat) (n : nat) : (term44 m n) = (term191 m n).
Proof. exact (TRANS (@lem7236339 m n) (@lem7236344 m n)). Qed.
Lemma lem7236346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236347 (m : nat) (n : nat) : (term172 m n) = (term192 m n).
Proof. exact (MK_COMB (@lem7236346) (@lem7236345 m n)). Qed.
Lemma lem7236348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236349 (m : nat) (n : nat) : (term126 m n) = (term193 m n).
Proof. exact (MK_COMB (@lem7236348) (@lem7236347 m n)). Qed.
Lemma lem7236351 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236352 (n : nat) (p : nat) : (Peano.le n p) = (term183 n p).
Proof. exact (@lem7236351 n p). Qed.
Lemma lem7236353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236354 (n : nat) (p : nat) : (term158 n p) = (term194 n p).
Proof. exact (MK_COMB (@lem7236353) (@lem7236352 n p)). Qed.
Lemma lem7236355 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236356 (n : nat) (p : nat) : (term123 n p) = (term195 n p).
Proof. exact (MK_COMB (@lem7236355) (@lem7236354 n p)). Qed.
Lemma lem7236358 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236359 (m : nat) (x : nat) : (Peano.le m x) = (term183 m x).
Proof. exact (@lem7236358 m x). Qed.
Lemma lem7236360 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236361 (m : nat) (x : nat) : (term158 m x) = (term194 m x).
Proof. exact (MK_COMB (@lem7236360) (@lem7236359 m x)). Qed.
Lemma lem7236362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236363 (m : nat) (x : nat) : (term123 m x) = (term195 m x).
Proof. exact (MK_COMB (@lem7236362) (@lem7236361 m x)). Qed.
Lemma lem7236365 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236366 (x : nat) (n : nat) : (Peano.le x n) = (term183 x n).
Proof. exact (@lem7236365 x n). Qed.
Lemma lem7236367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236368 (x : nat) (n : nat) : (term158 x n) = (term194 x n).
Proof. exact (MK_COMB (@lem7236367) (@lem7236366 x n)). Qed.
Lemma lem7236369 (m : nat) (x : nat) (n : nat) : (term93 m x n) = (term196 m x n).
Proof. exact (MK_COMB (@lem7236363 m x) (@lem7236368 x n)). Qed.
Lemma lem7236370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236371 (m : nat) (x : nat) (n : nat) : (term98 m x n) = (term197 m x n).
Proof. exact (MK_COMB (@lem7236370) (@lem7236369 m x n)). Qed.
Lemma lem7236373 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236374 (n : nat) (x : nat) : (term96 n x) = (term198 n x).
Proof. exact (@lem7236373 (term60 n) x). Qed.
Lemma lem7236376 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7236377 (n : nat) : (term187 n) = (term188 n).
Proof. exact (@lem7236376 n term189). Qed.
Lemma lem7236378 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7236379 (n : nat) : (term199 n) = (term200 n).
Proof. exact (MK_COMB (@lem7236378) (@lem7236377 n)). Qed.
Lemma lem7236380 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem7236381 (n : nat) (x : nat) : (term198 n x) = (term201 n x).
Proof. exact (MK_COMB (@lem7236379 n) (@lem7236380 x)). Qed.
Lemma lem7236382 (n : nat) (x : nat) : (term96 n x) = (term201 n x).
Proof. exact (TRANS (@lem7236374 n x) (@lem7236381 n x)). Qed.
Lemma lem7236383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236384 (n : nat) (x : nat) : (term202 n x) = (term203 n x).
Proof. exact (MK_COMB (@lem7236383) (@lem7236382 n x)). Qed.
Lemma lem7236385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236386 (n : nat) (x : nat) : (term204 n x) = (term205 n x).
Proof. exact (MK_COMB (@lem7236385) (@lem7236384 n x)). Qed.
Lemma lem7236388 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236389 (x : nat) (p : nat) : (Peano.le x p) = (term183 x p).
Proof. exact (@lem7236388 x p). Qed.
Lemma lem7236390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236391 (x : nat) (p : nat) : (term158 x p) = (term194 x p).
Proof. exact (MK_COMB (@lem7236390) (@lem7236389 x p)). Qed.
Lemma lem7236392 (n : nat) (x : nat) (p : nat) : (term95 n x p) = (term206 n x p).
Proof. exact (MK_COMB (@lem7236386 n x) (@lem7236391 x p)). Qed.
Lemma lem7236393 (m : nat) (n : nat) (x : nat) (p : nat) : (term100 m n x p) = (term207 m n x p).
Proof. exact (MK_COMB (@lem7236371 m x n) (@lem7236392 n x p)). Qed.
Lemma lem7236394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236395 (m : nat) (n : nat) (x : nat) (p : nat) : (term145 m n x p) = (term208 m n x p).
Proof. exact (MK_COMB (@lem7236394) (@lem7236393 m n x p)). Qed.
Lemma lem7236397 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236398 (m : nat) (x : nat) : (Peano.le m x) = (term183 m x).
Proof. exact (@lem7236397 m x). Qed.
Lemma lem7236399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236400 (m : nat) (x : nat) : (term209 m x) = (term210 m x).
Proof. exact (MK_COMB (@lem7236399) (@lem7236398 m x)). Qed.
Lemma lem7236402 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236403 (x : nat) (n : nat) : (Peano.le x n) = (term183 x n).
Proof. exact (@lem7236402 x n). Qed.
Lemma lem7236404 (m : nat) (x : nat) (n : nat) : (term6 m x n) = (term211 m x n).
Proof. exact (MK_COMB (@lem7236400 m x) (@lem7236403 x n)). Qed.
Lemma lem7236405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236406 (m : nat) (x : nat) (n : nat) : (term77 m x n) = (term212 m x n).
Proof. exact (MK_COMB (@lem7236405) (@lem7236404 m x n)). Qed.
Lemma lem7236408 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236409 (n : nat) (x : nat) : (term96 n x) = (term198 n x).
Proof. exact (@lem7236408 (term60 n) x). Qed.
Lemma lem7236411 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7236412 (n : nat) : (term187 n) = (term188 n).
Proof. exact (@lem7236411 n term189). Qed.
Lemma lem7236413 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7236414 (n : nat) : (term199 n) = (term200 n).
Proof. exact (MK_COMB (@lem7236413) (@lem7236412 n)). Qed.
Lemma lem7236415 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem7236416 (n : nat) (x : nat) : (term198 n x) = (term201 n x).
Proof. exact (MK_COMB (@lem7236414 n) (@lem7236415 x)). Qed.
Lemma lem7236417 (n : nat) (x : nat) : (term96 n x) = (term201 n x).
Proof. exact (TRANS (@lem7236409 n x) (@lem7236416 n x)). Qed.
Lemma lem7236418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236419 (n : nat) (x : nat) : (term213 n x) = (term214 n x).
Proof. exact (MK_COMB (@lem7236418) (@lem7236417 n x)). Qed.
Lemma lem7236421 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236422 (x : nat) (p : nat) : (Peano.le x p) = (term183 x p).
Proof. exact (@lem7236421 x p). Qed.
Lemma lem7236423 (n : nat) (x : nat) (p : nat) : (term59 n x p) = (term215 n x p).
Proof. exact (MK_COMB (@lem7236419 n x) (@lem7236422 x p)). Qed.
Lemma lem7236424 (m : nat) (n : nat) (x : nat) (p : nat) : (term78 m n x p) = (term216 m n x p).
Proof. exact (MK_COMB (@lem7236406 m x n) (@lem7236423 n x p)). Qed.
Lemma lem7236425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236426 (m : nat) (n : nat) (x : nat) (p : nat) : (term112 m n x p) = (term217 m n x p).
Proof. exact (MK_COMB (@lem7236425) (@lem7236424 m n x p)). Qed.
Lemma lem7236428 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236429 (m : nat) (x : nat) : (Peano.le m x) = (term183 m x).
Proof. exact (@lem7236428 m x). Qed.
Lemma lem7236430 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236431 (m : nat) (x : nat) : (term158 m x) = (term194 m x).
Proof. exact (MK_COMB (@lem7236430) (@lem7236429 m x)). Qed.
Lemma lem7236432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236433 (m : nat) (x : nat) : (term123 m x) = (term195 m x).
Proof. exact (MK_COMB (@lem7236432) (@lem7236431 m x)). Qed.
Lemma lem7236435 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236436 (x : nat) (p : nat) : (Peano.le x p) = (term183 x p).
Proof. exact (@lem7236435 x p). Qed.
Lemma lem7236437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236438 (x : nat) (p : nat) : (term158 x p) = (term194 x p).
Proof. exact (MK_COMB (@lem7236437) (@lem7236436 x p)). Qed.
Lemma lem7236439 (m : nat) (x : nat) (p : nat) : (term93 m x p) = (term196 m x p).
Proof. exact (MK_COMB (@lem7236433 m x) (@lem7236438 x p)). Qed.
Lemma lem7236440 (n : nat) (m : nat) (x : nat) (p : nat) : (term114 n m x p) = (term218 n m x p).
Proof. exact (MK_COMB (@lem7236426 m n x p) (@lem7236439 m x p)). Qed.
Lemma lem7236441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236442 (n : nat) (m : nat) (x : nat) (p : nat) : (term116 n m x p) = (term219 n m x p).
Proof. exact (MK_COMB (@lem7236441) (@lem7236440 n m x p)). Qed.
Lemma lem7236444 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236445 (m : nat) (x : nat) : (Peano.le m x) = (term183 m x).
Proof. exact (@lem7236444 m x). Qed.
Lemma lem7236446 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236447 (m : nat) (x : nat) : (term158 m x) = (term194 m x).
Proof. exact (MK_COMB (@lem7236446) (@lem7236445 m x)). Qed.
Lemma lem7236448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236449 (m : nat) (x : nat) : (term123 m x) = (term195 m x).
Proof. exact (MK_COMB (@lem7236448) (@lem7236447 m x)). Qed.
Lemma lem7236451 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236452 (x : nat) (n : nat) : (Peano.le x n) = (term183 x n).
Proof. exact (@lem7236451 x n). Qed.
Lemma lem7236453 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236454 (x : nat) (n : nat) : (term158 x n) = (term194 x n).
Proof. exact (MK_COMB (@lem7236453) (@lem7236452 x n)). Qed.
Lemma lem7236455 (m : nat) (x : nat) (n : nat) : (term93 m x n) = (term196 m x n).
Proof. exact (MK_COMB (@lem7236449 m x) (@lem7236454 x n)). Qed.
Lemma lem7236456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236457 (m : nat) (x : nat) (n : nat) : (term104 m x n) = (term220 m x n).
Proof. exact (MK_COMB (@lem7236456) (@lem7236455 m x n)). Qed.
Lemma lem7236459 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236460 (n : nat) (x : nat) : (term96 n x) = (term198 n x).
Proof. exact (@lem7236459 (term60 n) x). Qed.
Lemma lem7236462 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7236463 (n : nat) : (term187 n) = (term188 n).
Proof. exact (@lem7236462 n term189). Qed.
Lemma lem7236464 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7236465 (n : nat) : (term199 n) = (term200 n).
Proof. exact (MK_COMB (@lem7236464) (@lem7236463 n)). Qed.
Lemma lem7236466 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem7236467 (n : nat) (x : nat) : (term198 n x) = (term201 n x).
Proof. exact (MK_COMB (@lem7236465 n) (@lem7236466 x)). Qed.
Lemma lem7236468 (n : nat) (x : nat) : (term96 n x) = (term201 n x).
Proof. exact (TRANS (@lem7236460 n x) (@lem7236467 n x)). Qed.
Lemma lem7236469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236470 (n : nat) (x : nat) : (term202 n x) = (term203 n x).
Proof. exact (MK_COMB (@lem7236469) (@lem7236468 n x)). Qed.
Lemma lem7236471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236472 (n : nat) (x : nat) : (term204 n x) = (term205 n x).
Proof. exact (MK_COMB (@lem7236471) (@lem7236470 n x)). Qed.
Lemma lem7236474 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236475 (x : nat) (p : nat) : (Peano.le x p) = (term183 x p).
Proof. exact (@lem7236474 x p). Qed.
Lemma lem7236476 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7236477 (x : nat) (p : nat) : (term158 x p) = (term194 x p).
Proof. exact (MK_COMB (@lem7236476) (@lem7236475 x p)). Qed.
Lemma lem7236478 (n : nat) (x : nat) (p : nat) : (term95 n x p) = (term206 n x p).
Proof. exact (MK_COMB (@lem7236472 n x) (@lem7236477 x p)). Qed.
Lemma lem7236479 (m : nat) (n : nat) (x : nat) (p : nat) : (term106 m n x p) = (term221 m n x p).
Proof. exact (MK_COMB (@lem7236457 m x n) (@lem7236478 n x p)). Qed.
Lemma lem7236480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236481 (m : nat) (n : nat) (x : nat) (p : nat) : (term109 m n x p) = (term222 m n x p).
Proof. exact (MK_COMB (@lem7236480) (@lem7236479 m n x p)). Qed.
Lemma lem7236483 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236484 (m : nat) (x : nat) : (Peano.le m x) = (term183 m x).
Proof. exact (@lem7236483 m x). Qed.
Lemma lem7236485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236486 (m : nat) (x : nat) : (term209 m x) = (term210 m x).
Proof. exact (MK_COMB (@lem7236485) (@lem7236484 m x)). Qed.
Lemma lem7236488 (m : nat) (n : nat) : (Peano.le m n) = (term183 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7236489 (x : nat) (p : nat) : (Peano.le x p) = (term183 x p).
Proof. exact (@lem7236488 x p). Qed.
Lemma lem7236490 (m : nat) (x : nat) (p : nat) : (term6 m x p) = (term211 m x p).
Proof. exact (MK_COMB (@lem7236486 m x) (@lem7236489 x p)). Qed.
Lemma lem7236491 (n : nat) (m : nat) (x : nat) (p : nat) : (term111 n m x p) = (term223 n m x p).
Proof. exact (MK_COMB (@lem7236481 m n x p) (@lem7236490 m x p)). Qed.
Lemma lem7236492 (n : nat) (m : nat) (x : nat) (p : nat) : (term118 n m x p) = (term224 n m x p).
Proof. exact (MK_COMB (@lem7236442 n m x p) (@lem7236491 n m x p)). Qed.
Lemma lem7236493 (n : nat) (m : nat) (x : nat) (p : nat) : (term147 n m x p) = (term225 n m x p).
Proof. exact (MK_COMB (@lem7236395 m n x p) (@lem7236492 n m x p)). Qed.
Lemma lem7236494 (n : nat) (m : nat) (x : nat) (p : nat) : (term165 n m x p) = (term226 n m x p).
Proof. exact (MK_COMB (@lem7236356 n p) (@lem7236493 n m x p)). Qed.
Lemma lem7236495 (n : nat) (m : nat) (x : nat) (p : nat) : (term179 n m x p) = (term227 n m x p).
Proof. exact (MK_COMB (@lem7236349 m n) (@lem7236494 n m x p)). Qed.
Lemma lem7236496 (n : nat) (m : nat) (p : nat) : (term181 n m p) = (term228 n m p).
Proof. exact (fun_ext (fun x : nat => @lem7236495 n m x p)). Qed.
Lemma lem7236497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7236498 (n : nat) (m : nat) (p : nat) : (term182 n m p) = (term229 n m p).
Proof. exact (MK_COMB (@lem7236497) (@lem7236496 n m p)). Qed.
Lemma lem7236499 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term229 n m p).
Proof. exact (TRANS (@lem7236336 n m p) (@lem7236498 n m p)). Qed.
Lemma lem7236500 (m : nat) : term230 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem7236501 (m : nat) : (term230 m) = (term231 m).
Proof. exact (eq_refl (term230 m)). Qed.
Lemma lem7236502 (m : nat) : term231 m.
Proof. exact (EQ_MP (@lem7236501 m) (@lem7236500 m)). Qed.
Lemma lem7236503 (n : nat) : term230 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem7236504 (n : nat) : (term230 n) = (term231 n).
Proof. exact (eq_refl (term230 n)). Qed.
Lemma lem7236505 (n : nat) : term231 n.
Proof. exact (EQ_MP (@lem7236504 n) (@lem7236503 n)). Qed.
Lemma lem7236506 (p : nat) : term230 p.
Proof. exact (@lem2307535 p). Qed.
Lemma lem7236507 (p : nat) : (term230 p) = (term231 p).
Proof. exact (eq_refl (term230 p)). Qed.
Lemma lem7236508 (p : nat) : term231 p.
Proof. exact (EQ_MP (@lem7236507 p) (@lem7236506 p)). Qed.
Lemma lem7236509 (x : nat) : term230 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem7236510 (x : nat) : (term230 x) = (term231 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem7236511 (x : nat) : term231 x.
Proof. exact (EQ_MP (@lem7236510 x) (@lem7236509 x)). Qed.
Lemma lem7236512 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term232 _96884 _96883 _96886 _96885) = (term233 _96884 _96883 _96886 _96885).
Proof. exact (@lem2318604 (term233 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236566 (_96883 : int) (_96884 : int) : (term234 _96883 _96884) = (term235 _96883 _96884).
Proof. exact (@lem16933 (term235 _96883 _96884)). Qed.
Lemma lem7236569 (_96884 : int) (_96885 : int) : (term236 _96884 _96885) = (int_le _96884 _96885).
Proof. exact (@lem16933 (int_le _96884 _96885)). Qed.
Lemma lem7236572 (_96883 : int) (_96886 : int) : (term236 _96883 _96886) = (int_le _96883 _96886).
Proof. exact (@lem16933 (int_le _96883 _96886)). Qed.
Lemma lem7236575 (_96886 : int) (_96884 : int) : (term236 _96886 _96884) = (int_le _96886 _96884).
Proof. exact (@lem16933 (int_le _96886 _96884)). Qed.
Lemma lem7236576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236577 (_96883 : int) (_96886 : int) : (term237 _96883 _96886) = (term238 _96883 _96886).
Proof. exact (MK_COMB (@lem7236576) (@lem7236572 _96883 _96886)). Qed.
Lemma lem7236578 (_96883 : int) (_96886 : int) (_96884 : int) : (term239 _96883 _96886 _96884) = (term240 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236577 _96883 _96886) (@lem7236575 _96886 _96884)). Qed.
Lemma lem7236579 (_96883 : int) (_96886 : int) (_96884 : int) : (term241 _96883 _96886 _96884) = (term239 _96883 _96886 _96884).
Proof. exact (@lem17160 (term242 _96883 _96886) (term242 _96886 _96884)). Qed.
Lemma lem7236580 (_96883 : int) (_96886 : int) (_96884 : int) : (term241 _96883 _96886 _96884) = (term240 _96883 _96886 _96884).
Proof. exact (TRANS (@lem7236579 _96883 _96886 _96884) (@lem7236578 _96883 _96886 _96884)). Qed.
Lemma lem7236583 (_96884 : int) (_96886 : int) : (term243 _96884 _96886) = (term244 _96884 _96886).
Proof. exact (@lem16933 (term244 _96884 _96886)). Qed.
Lemma lem7236586 (_96886 : int) (_96885 : int) : (term236 _96886 _96885) = (int_le _96886 _96885).
Proof. exact (@lem16933 (int_le _96886 _96885)). Qed.
Lemma lem7236587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236588 (_96884 : int) (_96886 : int) : (term245 _96884 _96886) = (term246 _96884 _96886).
Proof. exact (MK_COMB (@lem7236587) (@lem7236583 _96884 _96886)). Qed.
Lemma lem7236589 (_96884 : int) (_96886 : int) (_96885 : int) : (term247 _96884 _96886 _96885) = (term248 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236588 _96884 _96886) (@lem7236586 _96886 _96885)). Qed.
Lemma lem7236590 (_96884 : int) (_96886 : int) (_96885 : int) : (term249 _96884 _96886 _96885) = (term247 _96884 _96886 _96885).
Proof. exact (@lem17160 (term250 _96884 _96886) (term242 _96886 _96885)). Qed.
Lemma lem7236591 (_96884 : int) (_96886 : int) (_96885 : int) : (term249 _96884 _96886 _96885) = (term248 _96884 _96886 _96885).
Proof. exact (TRANS (@lem7236590 _96884 _96886 _96885) (@lem7236589 _96884 _96886 _96885)). Qed.
Lemma lem7236592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236593 (_96883 : int) (_96886 : int) (_96884 : int) : (term251 _96883 _96886 _96884) = (term252 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236592) (@lem7236580 _96883 _96886 _96884)). Qed.
Lemma lem7236594 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term253 _96883 _96884 _96886 _96885) = (term254 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236593 _96883 _96886 _96884) (@lem7236591 _96884 _96886 _96885)). Qed.
Lemma lem7236595 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term255 _96883 _96884 _96886 _96885) = (term253 _96883 _96884 _96886 _96885).
Proof. exact (@lem17160 (term256 _96883 _96886 _96884) (term257 _96884 _96886 _96885)). Qed.
Lemma lem7236596 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term255 _96883 _96884 _96886 _96885) = (term254 _96883 _96884 _96886 _96885).
Proof. exact (TRANS (@lem7236595 _96883 _96884 _96886 _96885) (@lem7236594 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7236603 (_96883 : int) (_96886 : int) (_96884 : int) : (term258 _96883 _96886 _96884) = (term256 _96883 _96886 _96884).
Proof. exact (@lem17045 (int_le _96883 _96886) (int_le _96886 _96884)). Qed.
Lemma lem7236610 (_96884 : int) (_96886 : int) (_96885 : int) : (term259 _96884 _96886 _96885) = (term257 _96884 _96886 _96885).
Proof. exact (@lem17045 (term244 _96884 _96886) (int_le _96886 _96885)). Qed.
Lemma lem7236611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236612 (_96883 : int) (_96886 : int) (_96884 : int) : (term260 _96883 _96886 _96884) = (term261 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236611) (@lem7236603 _96883 _96886 _96884)). Qed.
Lemma lem7236613 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term262 _96883 _96884 _96886 _96885) = (term263 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236612 _96883 _96886 _96884) (@lem7236610 _96884 _96886 _96885)). Qed.
Lemma lem7236614 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term264 _96883 _96884 _96886 _96885) = (term262 _96883 _96884 _96886 _96885).
Proof. exact (@lem17160 (term240 _96883 _96886 _96884) (term248 _96884 _96886 _96885)). Qed.
Lemma lem7236615 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term264 _96883 _96884 _96886 _96885) = (term263 _96883 _96884 _96886 _96885).
Proof. exact (TRANS (@lem7236614 _96883 _96884 _96886 _96885) (@lem7236613 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7236618 (_96883 : int) (_96886 : int) : (term236 _96883 _96886) = (int_le _96883 _96886).
Proof. exact (@lem16933 (int_le _96883 _96886)). Qed.
Lemma lem7236621 (_96886 : int) (_96885 : int) : (term236 _96886 _96885) = (int_le _96886 _96885).
Proof. exact (@lem16933 (int_le _96886 _96885)). Qed.
Lemma lem7236622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236623 (_96883 : int) (_96886 : int) : (term237 _96883 _96886) = (term238 _96883 _96886).
Proof. exact (MK_COMB (@lem7236622) (@lem7236618 _96883 _96886)). Qed.
Lemma lem7236624 (_96883 : int) (_96886 : int) (_96885 : int) : (term239 _96883 _96886 _96885) = (term240 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236623 _96883 _96886) (@lem7236621 _96886 _96885)). Qed.
Lemma lem7236625 (_96883 : int) (_96886 : int) (_96885 : int) : (term241 _96883 _96886 _96885) = (term239 _96883 _96886 _96885).
Proof. exact (@lem17160 (term242 _96883 _96886) (term242 _96886 _96885)). Qed.
Lemma lem7236626 (_96883 : int) (_96886 : int) (_96885 : int) : (term241 _96883 _96886 _96885) = (term240 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236625 _96883 _96886 _96885) (@lem7236624 _96883 _96886 _96885)). Qed.
Lemma lem7236627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236628 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term265 _96883 _96884 _96886 _96885) = (term266 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236627) (@lem7236615 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7236629 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term267 _96884 _96883 _96886 _96885) = (term268 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236628 _96883 _96884 _96886 _96885) (@lem7236626 _96883 _96886 _96885)). Qed.
Lemma lem7236630 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term269 _96884 _96883 _96886 _96885) = (term267 _96884 _96883 _96886 _96885).
Proof. exact (@lem17160 (term270 _96883 _96884 _96886 _96885) (term256 _96883 _96886 _96885)). Qed.
Lemma lem7236631 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term269 _96884 _96883 _96886 _96885) = (term268 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236630 _96884 _96883 _96886 _96885) (@lem7236629 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236634 (_96883 : int) (_96886 : int) : (term236 _96883 _96886) = (int_le _96883 _96886).
Proof. exact (@lem16933 (int_le _96883 _96886)). Qed.
Lemma lem7236637 (_96886 : int) (_96884 : int) : (term236 _96886 _96884) = (int_le _96886 _96884).
Proof. exact (@lem16933 (int_le _96886 _96884)). Qed.
Lemma lem7236638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236639 (_96883 : int) (_96886 : int) : (term237 _96883 _96886) = (term238 _96883 _96886).
Proof. exact (MK_COMB (@lem7236638) (@lem7236634 _96883 _96886)). Qed.
Lemma lem7236640 (_96883 : int) (_96886 : int) (_96884 : int) : (term239 _96883 _96886 _96884) = (term240 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236639 _96883 _96886) (@lem7236637 _96886 _96884)). Qed.
Lemma lem7236641 (_96883 : int) (_96886 : int) (_96884 : int) : (term241 _96883 _96886 _96884) = (term239 _96883 _96886 _96884).
Proof. exact (@lem17160 (term242 _96883 _96886) (term242 _96886 _96884)). Qed.
Lemma lem7236642 (_96883 : int) (_96886 : int) (_96884 : int) : (term241 _96883 _96886 _96884) = (term240 _96883 _96886 _96884).
Proof. exact (TRANS (@lem7236641 _96883 _96886 _96884) (@lem7236640 _96883 _96886 _96884)). Qed.
Lemma lem7236645 (_96884 : int) (_96886 : int) : (term243 _96884 _96886) = (term244 _96884 _96886).
Proof. exact (@lem16933 (term244 _96884 _96886)). Qed.
Lemma lem7236648 (_96886 : int) (_96885 : int) : (term236 _96886 _96885) = (int_le _96886 _96885).
Proof. exact (@lem16933 (int_le _96886 _96885)). Qed.
Lemma lem7236649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236650 (_96884 : int) (_96886 : int) : (term245 _96884 _96886) = (term246 _96884 _96886).
Proof. exact (MK_COMB (@lem7236649) (@lem7236645 _96884 _96886)). Qed.
Lemma lem7236651 (_96884 : int) (_96886 : int) (_96885 : int) : (term247 _96884 _96886 _96885) = (term248 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236650 _96884 _96886) (@lem7236648 _96886 _96885)). Qed.
Lemma lem7236652 (_96884 : int) (_96886 : int) (_96885 : int) : (term249 _96884 _96886 _96885) = (term247 _96884 _96886 _96885).
Proof. exact (@lem17160 (term250 _96884 _96886) (term242 _96886 _96885)). Qed.
Lemma lem7236653 (_96884 : int) (_96886 : int) (_96885 : int) : (term249 _96884 _96886 _96885) = (term248 _96884 _96886 _96885).
Proof. exact (TRANS (@lem7236652 _96884 _96886 _96885) (@lem7236651 _96884 _96886 _96885)). Qed.
Lemma lem7236654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236655 (_96883 : int) (_96886 : int) (_96884 : int) : (term271 _96883 _96886 _96884) = (term272 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236654) (@lem7236642 _96883 _96886 _96884)). Qed.
Lemma lem7236656 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term273 _96883 _96884 _96886 _96885) = (term270 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236655 _96883 _96886 _96884) (@lem7236653 _96884 _96886 _96885)). Qed.
Lemma lem7236657 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term274 _96883 _96884 _96886 _96885) = (term273 _96883 _96884 _96886 _96885).
Proof. exact (@lem17045 (term256 _96883 _96886 _96884) (term257 _96884 _96886 _96885)). Qed.
Lemma lem7236658 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term274 _96883 _96884 _96886 _96885) = (term270 _96883 _96884 _96886 _96885).
Proof. exact (TRANS (@lem7236657 _96883 _96884 _96886 _96885) (@lem7236656 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7236665 (_96883 : int) (_96886 : int) (_96885 : int) : (term258 _96883 _96886 _96885) = (term256 _96883 _96886 _96885).
Proof. exact (@lem17045 (int_le _96883 _96886) (int_le _96886 _96885)). Qed.
Lemma lem7236666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236667 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term275 _96883 _96884 _96886 _96885) = (term276 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236666) (@lem7236658 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7236668 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term277 _96884 _96883 _96886 _96885) = (term278 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236667 _96883 _96884 _96886 _96885) (@lem7236665 _96883 _96886 _96885)). Qed.
Lemma lem7236669 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term279 _96884 _96883 _96886 _96885) = (term277 _96884 _96883 _96886 _96885).
Proof. exact (@lem17160 (term263 _96883 _96884 _96886 _96885) (term240 _96883 _96886 _96885)). Qed.
Lemma lem7236670 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term279 _96884 _96883 _96886 _96885) = (term278 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236669 _96884 _96883 _96886 _96885) (@lem7236668 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236672 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term280 _96884 _96883 _96886 _96885) = (term281 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236671) (@lem7236631 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236673 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term282 _96884 _96883 _96886 _96885) = (term283 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236672 _96884 _96883 _96886 _96885) (@lem7236670 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236674 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term284 _96884 _96883 _96886 _96885) = (term282 _96884 _96883 _96886 _96885).
Proof. exact (@lem17045 (term285 _96884 _96883 _96886 _96885) (term286 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236675 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term284 _96884 _96883 _96886 _96885) = (term283 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236674 _96884 _96883 _96886 _96885) (@lem7236673 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236677 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term287 _96883 _96884 _96886 _96885) = (term288 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236676) (@lem7236596 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7236678 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term289 _96884 _96883 _96886 _96885) = (term290 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236677 _96883 _96884 _96886 _96885) (@lem7236675 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236679 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term291 _96884 _96883 _96886 _96885) = (term289 _96884 _96883 _96886 _96885).
Proof. exact (@lem17045 (term292 _96883 _96884 _96886 _96885) (term293 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236680 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term291 _96884 _96883 _96886 _96885) = (term290 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236679 _96884 _96883 _96886 _96885) (@lem7236678 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236682 (_96884 : int) (_96885 : int) : (term237 _96884 _96885) = (term238 _96884 _96885).
Proof. exact (MK_COMB (@lem7236681) (@lem7236569 _96884 _96885)). Qed.
Lemma lem7236683 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term294 _96884 _96883 _96886 _96885) = (term295 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236682 _96884 _96885) (@lem7236680 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236684 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term296 _96884 _96883 _96886 _96885) = (term294 _96884 _96883 _96886 _96885).
Proof. exact (@lem17160 (term242 _96884 _96885) (term297 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236685 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term296 _96884 _96883 _96886 _96885) = (term295 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236684 _96884 _96883 _96886 _96885) (@lem7236683 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236687 (_96883 : int) (_96884 : int) : (term298 _96883 _96884) = (term299 _96883 _96884).
Proof. exact (MK_COMB (@lem7236686) (@lem7236566 _96883 _96884)). Qed.
Lemma lem7236688 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term300 _96884 _96883 _96886 _96885) = (term301 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236687 _96883 _96884) (@lem7236685 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236689 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term302 _96884 _96883 _96886 _96885) = (term300 _96884 _96883 _96886 _96885).
Proof. exact (@lem17160 (term303 _96883 _96884) (term304 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236690 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term302 _96884 _96883 _96886 _96885) = (term301 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236689 _96884 _96883 _96886 _96885) (@lem7236688 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236692 (_96886 : int) : (term305 _96886) = (term305 _96886).
Proof. exact (eq_refl (term305 _96886)). Qed.
Lemma lem7236693 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term306 _96884 _96883 _96886 _96885) = (term307 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236692 _96886) (@lem7236690 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236694 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term308 _96884 _96883 _96886 _96885) = (term306 _96884 _96883 _96886 _96885).
Proof. exact (@lem17362 (term309 _96886) (term310 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236695 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term308 _96884 _96883 _96886 _96885) = (term307 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236694 _96884 _96883 _96886 _96885) (@lem7236693 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236697 (_96885 : int) : (term305 _96885) = (term305 _96885).
Proof. exact (eq_refl (term305 _96885)). Qed.
Lemma lem7236698 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term311 _96884 _96883 _96886 _96885) = (term312 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236697 _96885) (@lem7236695 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236699 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term313 _96884 _96883 _96886 _96885) = (term311 _96884 _96883 _96886 _96885).
Proof. exact (@lem17362 (term309 _96885) (term314 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236700 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term313 _96884 _96883 _96886 _96885) = (term312 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236699 _96884 _96883 _96886 _96885) (@lem7236698 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236702 (_96884 : int) : (term305 _96884) = (term305 _96884).
Proof. exact (eq_refl (term305 _96884)). Qed.
Lemma lem7236703 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term315 _96884 _96883 _96886 _96885) = (term316 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236702 _96884) (@lem7236700 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236704 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term317 _96884 _96883 _96886 _96885) = (term315 _96884 _96883 _96886 _96885).
Proof. exact (@lem17362 (term309 _96884) (term318 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236705 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term317 _96884 _96883 _96886 _96885) = (term316 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236704 _96884 _96883 _96886 _96885) (@lem7236703 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236707 (_96883 : int) : (term305 _96883) = (term305 _96883).
Proof. exact (eq_refl (term305 _96883)). Qed.
Lemma lem7236708 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term319 _96884 _96883 _96886 _96885) = (term320 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7236707 _96883) (@lem7236705 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236709 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term321 _96884 _96883 _96886 _96885) = (term319 _96884 _96883 _96886 _96885).
Proof. exact (@lem17362 (term309 _96883) (term322 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236809 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term321 _96884 _96883 _96886 _96885) = (term320 _96884 _96883 _96886 _96885).
Proof. exact (TRANS (@lem7236709 _96884 _96883 _96886 _96885) (@lem7236708 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7236812 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236813 (_96883 : int) : (term309 _96883) = (term324 _96883).
Proof. exact (@lem7236812 term325 _96883). Qed.
Lemma lem7236815 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236816 : term327 = term328.
Proof. exact (@lem7236815 (NUMERAL 0)). Qed.
Lemma lem7236817 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236818 : term329 = term330.
Proof. exact (MK_COMB (@lem7236817) (@lem7236816)). Qed.
Lemma lem7236819 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7236820 (_96883 : int) : (term324 _96883) = (term331 _96883).
Proof. exact (MK_COMB (@lem7236818) (@lem7236819 _96883)). Qed.
Lemma lem7236822 (_96883 : int) : (term309 _96883) = (term331 _96883).
Proof. exact (TRANS (@lem7236813 _96883) (@lem7236820 _96883)). Qed.
Lemma lem7236825 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236826 (_96884 : int) : (term309 _96884) = (term324 _96884).
Proof. exact (@lem7236825 term325 _96884). Qed.
Lemma lem7236828 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236829 : term327 = term328.
Proof. exact (@lem7236828 (NUMERAL 0)). Qed.
Lemma lem7236830 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236831 : term329 = term330.
Proof. exact (MK_COMB (@lem7236830) (@lem7236829)). Qed.
Lemma lem7236832 (_96884 : int) : (real_of_int _96884) = (real_of_int _96884).
Proof. exact (eq_refl (real_of_int _96884)). Qed.
Lemma lem7236833 (_96884 : int) : (term324 _96884) = (term331 _96884).
Proof. exact (MK_COMB (@lem7236831) (@lem7236832 _96884)). Qed.
Lemma lem7236835 (_96884 : int) : (term309 _96884) = (term331 _96884).
Proof. exact (TRANS (@lem7236826 _96884) (@lem7236833 _96884)). Qed.
Lemma lem7236838 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236839 (_96885 : int) : (term309 _96885) = (term324 _96885).
Proof. exact (@lem7236838 term325 _96885). Qed.
Lemma lem7236841 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236842 : term327 = term328.
Proof. exact (@lem7236841 (NUMERAL 0)). Qed.
Lemma lem7236843 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236844 : term329 = term330.
Proof. exact (MK_COMB (@lem7236843) (@lem7236842)). Qed.
Lemma lem7236845 (_96885 : int) : (real_of_int _96885) = (real_of_int _96885).
Proof. exact (eq_refl (real_of_int _96885)). Qed.
Lemma lem7236846 (_96885 : int) : (term324 _96885) = (term331 _96885).
Proof. exact (MK_COMB (@lem7236844) (@lem7236845 _96885)). Qed.
Lemma lem7236848 (_96885 : int) : (term309 _96885) = (term331 _96885).
Proof. exact (TRANS (@lem7236839 _96885) (@lem7236846 _96885)). Qed.
Lemma lem7236851 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236852 (_96886 : int) : (term309 _96886) = (term324 _96886).
Proof. exact (@lem7236851 term325 _96886). Qed.
Lemma lem7236854 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236855 : term327 = term328.
Proof. exact (@lem7236854 (NUMERAL 0)). Qed.
Lemma lem7236856 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236857 : term329 = term330.
Proof. exact (MK_COMB (@lem7236856) (@lem7236855)). Qed.
Lemma lem7236858 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7236859 (_96886 : int) : (term324 _96886) = (term331 _96886).
Proof. exact (MK_COMB (@lem7236857) (@lem7236858 _96886)). Qed.
Lemma lem7236861 (_96886 : int) : (term309 _96886) = (term331 _96886).
Proof. exact (TRANS (@lem7236852 _96886) (@lem7236859 _96886)). Qed.
Lemma lem7236864 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236865 (_96883 : int) (_96884 : int) : (term235 _96883 _96884) = (term332 _96883 _96884).
Proof. exact (@lem7236864 _96883 (term333 _96884)). Qed.
Lemma lem7236867 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7236868 (_96884 : int) : (term336 _96884) = (term337 _96884).
Proof. exact (@lem7236867 _96884 term338). Qed.
Lemma lem7236870 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236871 : term339 = term340.
Proof. exact (@lem7236870 term189). Qed.
Lemma lem7236872 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7236873 (_96884 : int) : (term337 _96884) = (term342 _96884).
Proof. exact (MK_COMB (@lem7236872 _96884) (@lem7236871)). Qed.
Lemma lem7236874 (_96884 : int) : (term336 _96884) = (term342 _96884).
Proof. exact (TRANS (@lem7236868 _96884) (@lem7236873 _96884)). Qed.
Lemma lem7236875 (_96883 : int) : (term343 _96883) = (term343 _96883).
Proof. exact (eq_refl (term343 _96883)). Qed.
Lemma lem7236876 (_96883 : int) (_96884 : int) : (term332 _96883 _96884) = (term344 _96883 _96884).
Proof. exact (MK_COMB (@lem7236875 _96883) (@lem7236874 _96884)). Qed.
Lemma lem7236878 (_96883 : int) (_96884 : int) : (term235 _96883 _96884) = (term344 _96883 _96884).
Proof. exact (TRANS (@lem7236865 _96883 _96884) (@lem7236876 _96883 _96884)). Qed.
Lemma lem7236881 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236883 (_96884 : int) (_96885 : int) : (int_le _96884 _96885) = (term323 _96884 _96885).
Proof. exact (@lem7236881 _96884 _96885). Qed.
Lemma lem7236886 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236888 (_96883 : int) (_96886 : int) : (int_le _96883 _96886) = (term323 _96883 _96886).
Proof. exact (@lem7236886 _96883 _96886). Qed.
Lemma lem7236891 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236893 (_96886 : int) (_96884 : int) : (int_le _96886 _96884) = (term323 _96886 _96884).
Proof. exact (@lem7236891 _96886 _96884). Qed.
Lemma lem7236894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236895 (_96883 : int) (_96886 : int) : (term238 _96883 _96886) = (term345 _96883 _96886).
Proof. exact (MK_COMB (@lem7236894) (@lem7236888 _96883 _96886)). Qed.
Lemma lem7236896 (_96883 : int) (_96886 : int) (_96884 : int) : (term240 _96883 _96886 _96884) = (term346 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236895 _96883 _96886) (@lem7236893 _96886 _96884)). Qed.
Lemma lem7236899 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236900 (_96884 : int) (_96886 : int) : (term244 _96884 _96886) = (term347 _96884 _96886).
Proof. exact (@lem7236899 (term333 _96884) _96886). Qed.
Lemma lem7236902 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7236903 (_96884 : int) : (term336 _96884) = (term337 _96884).
Proof. exact (@lem7236902 _96884 term338). Qed.
Lemma lem7236905 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236906 : term339 = term340.
Proof. exact (@lem7236905 term189). Qed.
Lemma lem7236907 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7236908 (_96884 : int) : (term337 _96884) = (term342 _96884).
Proof. exact (MK_COMB (@lem7236907 _96884) (@lem7236906)). Qed.
Lemma lem7236909 (_96884 : int) : (term336 _96884) = (term342 _96884).
Proof. exact (TRANS (@lem7236903 _96884) (@lem7236908 _96884)). Qed.
Lemma lem7236910 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236911 (_96884 : int) : (term348 _96884) = (term349 _96884).
Proof. exact (MK_COMB (@lem7236910) (@lem7236909 _96884)). Qed.
Lemma lem7236912 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7236913 (_96884 : int) (_96886 : int) : (term347 _96884 _96886) = (term350 _96884 _96886).
Proof. exact (MK_COMB (@lem7236911 _96884) (@lem7236912 _96886)). Qed.
Lemma lem7236915 (_96884 : int) (_96886 : int) : (term244 _96884 _96886) = (term350 _96884 _96886).
Proof. exact (TRANS (@lem7236900 _96884 _96886) (@lem7236913 _96884 _96886)). Qed.
Lemma lem7236918 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236920 (_96886 : int) (_96885 : int) : (int_le _96886 _96885) = (term323 _96886 _96885).
Proof. exact (@lem7236918 _96886 _96885). Qed.
Lemma lem7236921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236922 (_96884 : int) (_96886 : int) : (term246 _96884 _96886) = (term351 _96884 _96886).
Proof. exact (MK_COMB (@lem7236921) (@lem7236915 _96884 _96886)). Qed.
Lemma lem7236923 (_96884 : int) (_96886 : int) (_96885 : int) : (term248 _96884 _96886 _96885) = (term352 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236922 _96884 _96886) (@lem7236920 _96886 _96885)). Qed.
Lemma lem7236924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7236925 (_96883 : int) (_96886 : int) (_96884 : int) : (term252 _96883 _96886 _96884) = (term353 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7236924) (@lem7236896 _96883 _96886 _96884)). Qed.
Lemma lem7236926 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term254 _96883 _96884 _96886 _96885) = (term354 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7236925 _96883 _96886 _96884) (@lem7236923 _96884 _96886 _96885)). Qed.
Lemma lem7236928 (y : int) (x : int) : (term242 x y) = (term244 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7236929 (_96886 : int) (_96883 : int) : (term242 _96883 _96886) = (term244 _96886 _96883).
Proof. exact (@lem7236928 _96886 _96883). Qed.
Lemma lem7236931 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236932 (_96886 : int) (_96883 : int) : (term244 _96886 _96883) = (term347 _96886 _96883).
Proof. exact (@lem7236931 (term333 _96886) _96883). Qed.
Lemma lem7236934 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7236935 (_96886 : int) : (term336 _96886) = (term337 _96886).
Proof. exact (@lem7236934 _96886 term338). Qed.
Lemma lem7236937 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236938 : term339 = term340.
Proof. exact (@lem7236937 term189). Qed.
Lemma lem7236939 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7236940 (_96886 : int) : (term337 _96886) = (term342 _96886).
Proof. exact (MK_COMB (@lem7236939 _96886) (@lem7236938)). Qed.
Lemma lem7236941 (_96886 : int) : (term336 _96886) = (term342 _96886).
Proof. exact (TRANS (@lem7236935 _96886) (@lem7236940 _96886)). Qed.
Lemma lem7236942 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236943 (_96886 : int) : (term348 _96886) = (term349 _96886).
Proof. exact (MK_COMB (@lem7236942) (@lem7236941 _96886)). Qed.
Lemma lem7236944 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7236945 (_96886 : int) (_96883 : int) : (term347 _96886 _96883) = (term350 _96886 _96883).
Proof. exact (MK_COMB (@lem7236943 _96886) (@lem7236944 _96883)). Qed.
Lemma lem7236946 (_96886 : int) (_96883 : int) : (term244 _96886 _96883) = (term350 _96886 _96883).
Proof. exact (TRANS (@lem7236932 _96886 _96883) (@lem7236945 _96886 _96883)). Qed.
Lemma lem7236947 (_96886 : int) (_96883 : int) : (term242 _96883 _96886) = (term350 _96886 _96883).
Proof. exact (TRANS (@lem7236929 _96886 _96883) (@lem7236946 _96886 _96883)). Qed.
Lemma lem7236949 (y : int) (x : int) : (term242 x y) = (term244 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7236950 (_96884 : int) (_96886 : int) : (term242 _96886 _96884) = (term244 _96884 _96886).
Proof. exact (@lem7236949 _96884 _96886). Qed.
Lemma lem7236952 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236953 (_96884 : int) (_96886 : int) : (term244 _96884 _96886) = (term347 _96884 _96886).
Proof. exact (@lem7236952 (term333 _96884) _96886). Qed.
Lemma lem7236955 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7236956 (_96884 : int) : (term336 _96884) = (term337 _96884).
Proof. exact (@lem7236955 _96884 term338). Qed.
Lemma lem7236958 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236959 : term339 = term340.
Proof. exact (@lem7236958 term189). Qed.
Lemma lem7236960 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7236961 (_96884 : int) : (term337 _96884) = (term342 _96884).
Proof. exact (MK_COMB (@lem7236960 _96884) (@lem7236959)). Qed.
Lemma lem7236962 (_96884 : int) : (term336 _96884) = (term342 _96884).
Proof. exact (TRANS (@lem7236956 _96884) (@lem7236961 _96884)). Qed.
Lemma lem7236963 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236964 (_96884 : int) : (term348 _96884) = (term349 _96884).
Proof. exact (MK_COMB (@lem7236963) (@lem7236962 _96884)). Qed.
Lemma lem7236965 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7236966 (_96884 : int) (_96886 : int) : (term347 _96884 _96886) = (term350 _96884 _96886).
Proof. exact (MK_COMB (@lem7236964 _96884) (@lem7236965 _96886)). Qed.
Lemma lem7236967 (_96884 : int) (_96886 : int) : (term244 _96884 _96886) = (term350 _96884 _96886).
Proof. exact (TRANS (@lem7236953 _96884 _96886) (@lem7236966 _96884 _96886)). Qed.
Lemma lem7236968 (_96884 : int) (_96886 : int) : (term242 _96886 _96884) = (term350 _96884 _96886).
Proof. exact (TRANS (@lem7236950 _96884 _96886) (@lem7236967 _96884 _96886)). Qed.
Lemma lem7236969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7236970 (_96886 : int) (_96883 : int) : (term355 _96883 _96886) = (term356 _96886 _96883).
Proof. exact (MK_COMB (@lem7236969) (@lem7236947 _96886 _96883)). Qed.
Lemma lem7236971 (_96883 : int) (_96884 : int) (_96886 : int) : (term256 _96883 _96886 _96884) = (term357 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7236970 _96886 _96883) (@lem7236968 _96884 _96886)). Qed.
Lemma lem7236973 (y : int) (x : int) : (term242 x y) = (term244 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7236974 (_96886 : int) (_96884 : int) : (term250 _96884 _96886) = (term358 _96886 _96884).
Proof. exact (@lem7236973 _96886 (term333 _96884)). Qed.
Lemma lem7236976 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7236977 (_96886 : int) (_96884 : int) : (term358 _96886 _96884) = (term359 _96886 _96884).
Proof. exact (@lem7236976 (term333 _96886) (term333 _96884)). Qed.
Lemma lem7236979 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7236980 (_96886 : int) : (term336 _96886) = (term337 _96886).
Proof. exact (@lem7236979 _96886 term338). Qed.
Lemma lem7236982 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236983 : term339 = term340.
Proof. exact (@lem7236982 term189). Qed.
Lemma lem7236984 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7236985 (_96886 : int) : (term337 _96886) = (term342 _96886).
Proof. exact (MK_COMB (@lem7236984 _96886) (@lem7236983)). Qed.
Lemma lem7236986 (_96886 : int) : (term336 _96886) = (term342 _96886).
Proof. exact (TRANS (@lem7236980 _96886) (@lem7236985 _96886)). Qed.
Lemma lem7236987 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7236988 (_96886 : int) : (term348 _96886) = (term349 _96886).
Proof. exact (MK_COMB (@lem7236987) (@lem7236986 _96886)). Qed.
Lemma lem7236990 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7236991 (_96884 : int) : (term336 _96884) = (term337 _96884).
Proof. exact (@lem7236990 _96884 term338). Qed.
Lemma lem7236993 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7236994 : term339 = term340.
Proof. exact (@lem7236993 term189). Qed.
Lemma lem7236995 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7236996 (_96884 : int) : (term337 _96884) = (term342 _96884).
Proof. exact (MK_COMB (@lem7236995 _96884) (@lem7236994)). Qed.
Lemma lem7236997 (_96884 : int) : (term336 _96884) = (term342 _96884).
Proof. exact (TRANS (@lem7236991 _96884) (@lem7236996 _96884)). Qed.
Lemma lem7236998 (_96886 : int) (_96884 : int) : (term359 _96886 _96884) = (term360 _96886 _96884).
Proof. exact (MK_COMB (@lem7236988 _96886) (@lem7236997 _96884)). Qed.
Lemma lem7236999 (_96886 : int) (_96884 : int) : (term358 _96886 _96884) = (term360 _96886 _96884).
Proof. exact (TRANS (@lem7236977 _96886 _96884) (@lem7236998 _96886 _96884)). Qed.
Lemma lem7237000 (_96886 : int) (_96884 : int) : (term250 _96884 _96886) = (term360 _96886 _96884).
Proof. exact (TRANS (@lem7236974 _96886 _96884) (@lem7236999 _96886 _96884)). Qed.
Lemma lem7237002 (y : int) (x : int) : (term242 x y) = (term244 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7237003 (_96885 : int) (_96886 : int) : (term242 _96886 _96885) = (term244 _96885 _96886).
Proof. exact (@lem7237002 _96885 _96886). Qed.
Lemma lem7237005 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237006 (_96885 : int) (_96886 : int) : (term244 _96885 _96886) = (term347 _96885 _96886).
Proof. exact (@lem7237005 (term333 _96885) _96886). Qed.
Lemma lem7237008 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7237009 (_96885 : int) : (term336 _96885) = (term337 _96885).
Proof. exact (@lem7237008 _96885 term338). Qed.
Lemma lem7237011 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7237012 : term339 = term340.
Proof. exact (@lem7237011 term189). Qed.
Lemma lem7237013 (_96885 : int) : (term341 _96885) = (term341 _96885).
Proof. exact (eq_refl (term341 _96885)). Qed.
Lemma lem7237014 (_96885 : int) : (term337 _96885) = (term342 _96885).
Proof. exact (MK_COMB (@lem7237013 _96885) (@lem7237012)). Qed.
Lemma lem7237015 (_96885 : int) : (term336 _96885) = (term342 _96885).
Proof. exact (TRANS (@lem7237009 _96885) (@lem7237014 _96885)). Qed.
Lemma lem7237016 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7237017 (_96885 : int) : (term348 _96885) = (term349 _96885).
Proof. exact (MK_COMB (@lem7237016) (@lem7237015 _96885)). Qed.
Lemma lem7237018 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7237019 (_96885 : int) (_96886 : int) : (term347 _96885 _96886) = (term350 _96885 _96886).
Proof. exact (MK_COMB (@lem7237017 _96885) (@lem7237018 _96886)). Qed.
Lemma lem7237020 (_96885 : int) (_96886 : int) : (term244 _96885 _96886) = (term350 _96885 _96886).
Proof. exact (TRANS (@lem7237006 _96885 _96886) (@lem7237019 _96885 _96886)). Qed.
Lemma lem7237021 (_96885 : int) (_96886 : int) : (term242 _96886 _96885) = (term350 _96885 _96886).
Proof. exact (TRANS (@lem7237003 _96885 _96886) (@lem7237020 _96885 _96886)). Qed.
Lemma lem7237022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7237023 (_96886 : int) (_96884 : int) : (term361 _96884 _96886) = (term362 _96886 _96884).
Proof. exact (MK_COMB (@lem7237022) (@lem7237000 _96886 _96884)). Qed.
Lemma lem7237024 (_96884 : int) (_96885 : int) (_96886 : int) : (term257 _96884 _96886 _96885) = (term363 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7237023 _96886 _96884) (@lem7237021 _96885 _96886)). Qed.
Lemma lem7237025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237026 (_96883 : int) (_96884 : int) (_96886 : int) : (term261 _96883 _96886 _96884) = (term364 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7237025) (@lem7236971 _96883 _96884 _96886)). Qed.
Lemma lem7237027 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term263 _96883 _96884 _96886 _96885) = (term365 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7237026 _96883 _96884 _96886) (@lem7237024 _96884 _96885 _96886)). Qed.
Lemma lem7237030 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237032 (_96883 : int) (_96886 : int) : (int_le _96883 _96886) = (term323 _96883 _96886).
Proof. exact (@lem7237030 _96883 _96886). Qed.
Lemma lem7237035 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237037 (_96886 : int) (_96885 : int) : (int_le _96886 _96885) = (term323 _96886 _96885).
Proof. exact (@lem7237035 _96886 _96885). Qed.
Lemma lem7237038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237039 (_96883 : int) (_96886 : int) : (term238 _96883 _96886) = (term345 _96883 _96886).
Proof. exact (MK_COMB (@lem7237038) (@lem7237032 _96883 _96886)). Qed.
Lemma lem7237040 (_96883 : int) (_96886 : int) (_96885 : int) : (term240 _96883 _96886 _96885) = (term346 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7237039 _96883 _96886) (@lem7237037 _96886 _96885)). Qed.
Lemma lem7237041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237042 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term266 _96883 _96884 _96886 _96885) = (term366 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7237041) (@lem7237027 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7237043 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term268 _96884 _96883 _96886 _96885) = (term367 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7237042 _96883 _96884 _96885 _96886) (@lem7237040 _96883 _96886 _96885)). Qed.
Lemma lem7237046 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237048 (_96883 : int) (_96886 : int) : (int_le _96883 _96886) = (term323 _96883 _96886).
Proof. exact (@lem7237046 _96883 _96886). Qed.
Lemma lem7237051 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237053 (_96886 : int) (_96884 : int) : (int_le _96886 _96884) = (term323 _96886 _96884).
Proof. exact (@lem7237051 _96886 _96884). Qed.
Lemma lem7237054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237055 (_96883 : int) (_96886 : int) : (term238 _96883 _96886) = (term345 _96883 _96886).
Proof. exact (MK_COMB (@lem7237054) (@lem7237048 _96883 _96886)). Qed.
Lemma lem7237056 (_96883 : int) (_96886 : int) (_96884 : int) : (term240 _96883 _96886 _96884) = (term346 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7237055 _96883 _96886) (@lem7237053 _96886 _96884)). Qed.
Lemma lem7237059 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237060 (_96884 : int) (_96886 : int) : (term244 _96884 _96886) = (term347 _96884 _96886).
Proof. exact (@lem7237059 (term333 _96884) _96886). Qed.
Lemma lem7237062 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7237063 (_96884 : int) : (term336 _96884) = (term337 _96884).
Proof. exact (@lem7237062 _96884 term338). Qed.
Lemma lem7237065 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7237066 : term339 = term340.
Proof. exact (@lem7237065 term189). Qed.
Lemma lem7237067 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7237068 (_96884 : int) : (term337 _96884) = (term342 _96884).
Proof. exact (MK_COMB (@lem7237067 _96884) (@lem7237066)). Qed.
Lemma lem7237069 (_96884 : int) : (term336 _96884) = (term342 _96884).
Proof. exact (TRANS (@lem7237063 _96884) (@lem7237068 _96884)). Qed.
Lemma lem7237070 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7237071 (_96884 : int) : (term348 _96884) = (term349 _96884).
Proof. exact (MK_COMB (@lem7237070) (@lem7237069 _96884)). Qed.
Lemma lem7237072 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7237073 (_96884 : int) (_96886 : int) : (term347 _96884 _96886) = (term350 _96884 _96886).
Proof. exact (MK_COMB (@lem7237071 _96884) (@lem7237072 _96886)). Qed.
Lemma lem7237075 (_96884 : int) (_96886 : int) : (term244 _96884 _96886) = (term350 _96884 _96886).
Proof. exact (TRANS (@lem7237060 _96884 _96886) (@lem7237073 _96884 _96886)). Qed.
Lemma lem7237078 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237080 (_96886 : int) (_96885 : int) : (int_le _96886 _96885) = (term323 _96886 _96885).
Proof. exact (@lem7237078 _96886 _96885). Qed.
Lemma lem7237081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237082 (_96884 : int) (_96886 : int) : (term246 _96884 _96886) = (term351 _96884 _96886).
Proof. exact (MK_COMB (@lem7237081) (@lem7237075 _96884 _96886)). Qed.
Lemma lem7237083 (_96884 : int) (_96886 : int) (_96885 : int) : (term248 _96884 _96886 _96885) = (term352 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7237082 _96884 _96886) (@lem7237080 _96886 _96885)). Qed.
Lemma lem7237084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7237085 (_96883 : int) (_96886 : int) (_96884 : int) : (term272 _96883 _96886 _96884) = (term368 _96883 _96886 _96884).
Proof. exact (MK_COMB (@lem7237084) (@lem7237056 _96883 _96886 _96884)). Qed.
Lemma lem7237086 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term270 _96883 _96884 _96886 _96885) = (term369 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7237085 _96883 _96886 _96884) (@lem7237083 _96884 _96886 _96885)). Qed.
Lemma lem7237088 (y : int) (x : int) : (term242 x y) = (term244 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7237089 (_96886 : int) (_96883 : int) : (term242 _96883 _96886) = (term244 _96886 _96883).
Proof. exact (@lem7237088 _96886 _96883). Qed.
Lemma lem7237091 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237092 (_96886 : int) (_96883 : int) : (term244 _96886 _96883) = (term347 _96886 _96883).
Proof. exact (@lem7237091 (term333 _96886) _96883). Qed.
Lemma lem7237094 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7237095 (_96886 : int) : (term336 _96886) = (term337 _96886).
Proof. exact (@lem7237094 _96886 term338). Qed.
Lemma lem7237097 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7237098 : term339 = term340.
Proof. exact (@lem7237097 term189). Qed.
Lemma lem7237099 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7237100 (_96886 : int) : (term337 _96886) = (term342 _96886).
Proof. exact (MK_COMB (@lem7237099 _96886) (@lem7237098)). Qed.
Lemma lem7237101 (_96886 : int) : (term336 _96886) = (term342 _96886).
Proof. exact (TRANS (@lem7237095 _96886) (@lem7237100 _96886)). Qed.
Lemma lem7237102 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7237103 (_96886 : int) : (term348 _96886) = (term349 _96886).
Proof. exact (MK_COMB (@lem7237102) (@lem7237101 _96886)). Qed.
Lemma lem7237104 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7237105 (_96886 : int) (_96883 : int) : (term347 _96886 _96883) = (term350 _96886 _96883).
Proof. exact (MK_COMB (@lem7237103 _96886) (@lem7237104 _96883)). Qed.
Lemma lem7237106 (_96886 : int) (_96883 : int) : (term244 _96886 _96883) = (term350 _96886 _96883).
Proof. exact (TRANS (@lem7237092 _96886 _96883) (@lem7237105 _96886 _96883)). Qed.
Lemma lem7237107 (_96886 : int) (_96883 : int) : (term242 _96883 _96886) = (term350 _96886 _96883).
Proof. exact (TRANS (@lem7237089 _96886 _96883) (@lem7237106 _96886 _96883)). Qed.
Lemma lem7237109 (y : int) (x : int) : (term242 x y) = (term244 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7237110 (_96885 : int) (_96886 : int) : (term242 _96886 _96885) = (term244 _96885 _96886).
Proof. exact (@lem7237109 _96885 _96886). Qed.
Lemma lem7237112 (x : int) (y : int) : (int_le x y) = (term323 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7237113 (_96885 : int) (_96886 : int) : (term244 _96885 _96886) = (term347 _96885 _96886).
Proof. exact (@lem7237112 (term333 _96885) _96886). Qed.
Lemma lem7237115 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7237116 (_96885 : int) : (term336 _96885) = (term337 _96885).
Proof. exact (@lem7237115 _96885 term338). Qed.
Lemma lem7237118 (n : nat) : (term326 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7237119 : term339 = term340.
Proof. exact (@lem7237118 term189). Qed.
Lemma lem7237120 (_96885 : int) : (term341 _96885) = (term341 _96885).
Proof. exact (eq_refl (term341 _96885)). Qed.
Lemma lem7237121 (_96885 : int) : (term337 _96885) = (term342 _96885).
Proof. exact (MK_COMB (@lem7237120 _96885) (@lem7237119)). Qed.
Lemma lem7237122 (_96885 : int) : (term336 _96885) = (term342 _96885).
Proof. exact (TRANS (@lem7237116 _96885) (@lem7237121 _96885)). Qed.
Lemma lem7237123 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7237124 (_96885 : int) : (term348 _96885) = (term349 _96885).
Proof. exact (MK_COMB (@lem7237123) (@lem7237122 _96885)). Qed.
Lemma lem7237125 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7237126 (_96885 : int) (_96886 : int) : (term347 _96885 _96886) = (term350 _96885 _96886).
Proof. exact (MK_COMB (@lem7237124 _96885) (@lem7237125 _96886)). Qed.
Lemma lem7237127 (_96885 : int) (_96886 : int) : (term244 _96885 _96886) = (term350 _96885 _96886).
Proof. exact (TRANS (@lem7237113 _96885 _96886) (@lem7237126 _96885 _96886)). Qed.
Lemma lem7237128 (_96885 : int) (_96886 : int) : (term242 _96886 _96885) = (term350 _96885 _96886).
Proof. exact (TRANS (@lem7237110 _96885 _96886) (@lem7237127 _96885 _96886)). Qed.
Lemma lem7237129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7237130 (_96886 : int) (_96883 : int) : (term355 _96883 _96886) = (term356 _96886 _96883).
Proof. exact (MK_COMB (@lem7237129) (@lem7237107 _96886 _96883)). Qed.
Lemma lem7237131 (_96883 : int) (_96885 : int) (_96886 : int) : (term256 _96883 _96886 _96885) = (term357 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237130 _96886 _96883) (@lem7237128 _96885 _96886)). Qed.
Lemma lem7237132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237133 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term276 _96883 _96884 _96886 _96885) = (term370 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7237132) (@lem7237086 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7237134 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term278 _96884 _96883 _96886 _96885) = (term371 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237133 _96883 _96884 _96886 _96885) (@lem7237131 _96883 _96885 _96886)). Qed.
Lemma lem7237135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7237136 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term281 _96884 _96883 _96886 _96885) = (term372 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7237135) (@lem7237043 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7237137 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term283 _96884 _96883 _96886 _96885) = (term373 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237136 _96884 _96883 _96886 _96885) (@lem7237134 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7237139 (_96883 : int) (_96884 : int) (_96886 : int) (_96885 : int) : (term288 _96883 _96884 _96886 _96885) = (term374 _96883 _96884 _96886 _96885).
Proof. exact (MK_COMB (@lem7237138) (@lem7236926 _96883 _96884 _96886 _96885)). Qed.
Lemma lem7237140 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term290 _96884 _96883 _96886 _96885) = (term375 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237139 _96883 _96884 _96886 _96885) (@lem7237137 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237142 (_96884 : int) (_96885 : int) : (term238 _96884 _96885) = (term345 _96884 _96885).
Proof. exact (MK_COMB (@lem7237141) (@lem7236883 _96884 _96885)). Qed.
Lemma lem7237143 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term295 _96884 _96883 _96886 _96885) = (term376 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237142 _96884 _96885) (@lem7237140 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237145 (_96883 : int) (_96884 : int) : (term299 _96883 _96884) = (term377 _96883 _96884).
Proof. exact (MK_COMB (@lem7237144) (@lem7236878 _96883 _96884)). Qed.
Lemma lem7237146 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term301 _96884 _96883 _96886 _96885) = (term378 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237145 _96883 _96884) (@lem7237143 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237148 (_96886 : int) : (term305 _96886) = (term379 _96886).
Proof. exact (MK_COMB (@lem7237147) (@lem7236861 _96886)). Qed.
Lemma lem7237149 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term307 _96884 _96883 _96886 _96885) = (term380 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237148 _96886) (@lem7237146 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237151 (_96885 : int) : (term305 _96885) = (term379 _96885).
Proof. exact (MK_COMB (@lem7237150) (@lem7236848 _96885)). Qed.
Lemma lem7237152 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term312 _96884 _96883 _96886 _96885) = (term381 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237151 _96885) (@lem7237149 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237154 (_96884 : int) : (term305 _96884) = (term379 _96884).
Proof. exact (MK_COMB (@lem7237153) (@lem7236835 _96884)). Qed.
Lemma lem7237155 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term316 _96884 _96883 _96886 _96885) = (term382 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237154 _96884) (@lem7237152 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237157 (_96883 : int) : (term305 _96883) = (term379 _96883).
Proof. exact (MK_COMB (@lem7237156) (@lem7236822 _96883)). Qed.
Lemma lem7237158 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term320 _96884 _96883 _96886 _96885) = (term383 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7237157 _96883) (@lem7237155 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237159 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term321 _96884 _96883 _96886 _96885) = (term383 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7236809 _96884 _96883 _96886 _96885) (@lem7237158 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237163 (t : Prop) : (term384 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7237379 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term385 _96884 _96883 _96885 _96886) = (term383 _96884 _96883 _96885 _96886).
Proof. exact (@lem7237163 (term383 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7237380 (_96883 : int) : (term331 _96883) = (term386 _96883).
Proof. exact (@lem1988287 (real_of_int _96883) term328). Qed.
Lemma lem7237386 (_96883 : int) : (term387 _96883) = (term388 _96883).
Proof. exact (@lem1982792 (real_of_int _96883) term328). Qed.
Lemma lem7237388 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237389 : term328 = term390.
Proof. exact (@lem7237388 (NUMERAL 0)). Qed.
Lemma lem7237391 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237392 : term393 = term394.
Proof. exact (@lem7237391 term189). Qed.
Lemma lem7237393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237394 : term395 = term396.
Proof. exact (MK_COMB (@lem7237393) (@lem7237392)). Qed.
Lemma lem7237395 : term397 = term398.
Proof. exact (MK_COMB (@lem7237394) (@lem7237389)). Qed.
Lemma lem7237396 : term398 = term399.
Proof. exact (@lem1981613 term393 term328 term340 term340). Qed.
Lemma lem7237398 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237399 : term402 = term403.
Proof. exact (@lem7237398 term189 term189). Qed.
Lemma lem7237400 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237401 : term405 = term189.
Proof. exact (EQ_MP (@lem7237400) (@lem940073)). Qed.
Lemma lem7237402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237403 : term403 = term340.
Proof. exact (MK_COMB (@lem7237402) (@lem7237401)). Qed.
Lemma lem7237404 : term402 = term340.
Proof. exact (TRANS (@lem7237399) (@lem7237403)). Qed.
Lemma lem7237406 (x : nat) : (term406 x) = term328.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7237407 : term397 = term328.
Proof. exact (@lem7237406 term189). Qed.
Lemma lem7237408 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237409 : term407 = term408.
Proof. exact (MK_COMB (@lem7237408) (@lem7237407)). Qed.
Lemma lem7237410 : term399 = term390.
Proof. exact (MK_COMB (@lem7237409) (@lem7237404)). Qed.
Lemma lem7237411 : term398 = term390.
Proof. exact (TRANS (@lem7237396) (@lem7237410)). Qed.
Lemma lem7237412 : term397 = term390.
Proof. exact (TRANS (@lem7237395) (@lem7237411)). Qed.
Lemma lem7237414 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237415 : term390 = term328.
Proof. exact (@lem7237414 term328). Qed.
Lemma lem7237416 : term397 = term328.
Proof. exact (TRANS (@lem7237412) (@lem7237415)). Qed.
Lemma lem7237417 (_96883 : int) : (term341 _96883) = (term341 _96883).
Proof. exact (eq_refl (term341 _96883)). Qed.
Lemma lem7237418 (_96883 : int) : (term388 _96883) = (term410 _96883).
Proof. exact (MK_COMB (@lem7237417 _96883) (@lem7237416)). Qed.
Lemma lem7237419 (_96883 : int) : (term410 _96883) = (real_of_int _96883).
Proof. exact (@lem1982723 (real_of_int _96883)). Qed.
Lemma lem7237420 (_96883 : int) : (term388 _96883) = (real_of_int _96883).
Proof. exact (TRANS (@lem7237418 _96883) (@lem7237419 _96883)). Qed.
Lemma lem7237422 (_96883 : int) : (term387 _96883) = (real_of_int _96883).
Proof. exact (TRANS (@lem7237386 _96883) (@lem7237420 _96883)). Qed.
Lemma lem7237423 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237424 (_96883 : int) : (term411 _96883) = (term412 _96883).
Proof. exact (MK_COMB (@lem7237423) (@lem7237422 _96883)). Qed.
Lemma lem7237425 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237426 (_96883 : int) : (term386 _96883) = (term413 _96883).
Proof. exact (MK_COMB (@lem7237424 _96883) (@lem7237425)). Qed.
Lemma lem7237427 (_96883 : int) : (term331 _96883) = (term413 _96883).
Proof. exact (TRANS (@lem7237380 _96883) (@lem7237426 _96883)). Qed.
Lemma lem7237428 (_96884 : int) : (term331 _96884) = (term386 _96884).
Proof. exact (@lem1988287 (real_of_int _96884) term328). Qed.
Lemma lem7237434 (_96884 : int) : (term387 _96884) = (term388 _96884).
Proof. exact (@lem1982792 (real_of_int _96884) term328). Qed.
Lemma lem7237436 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237437 : term328 = term390.
Proof. exact (@lem7237436 (NUMERAL 0)). Qed.
Lemma lem7237439 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237440 : term393 = term394.
Proof. exact (@lem7237439 term189). Qed.
Lemma lem7237441 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237442 : term395 = term396.
Proof. exact (MK_COMB (@lem7237441) (@lem7237440)). Qed.
Lemma lem7237443 : term397 = term398.
Proof. exact (MK_COMB (@lem7237442) (@lem7237437)). Qed.
Lemma lem7237444 : term398 = term399.
Proof. exact (@lem1981613 term393 term328 term340 term340). Qed.
Lemma lem7237446 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237447 : term402 = term403.
Proof. exact (@lem7237446 term189 term189). Qed.
Lemma lem7237448 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237449 : term405 = term189.
Proof. exact (EQ_MP (@lem7237448) (@lem940073)). Qed.
Lemma lem7237450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237451 : term403 = term340.
Proof. exact (MK_COMB (@lem7237450) (@lem7237449)). Qed.
Lemma lem7237452 : term402 = term340.
Proof. exact (TRANS (@lem7237447) (@lem7237451)). Qed.
Lemma lem7237454 (x : nat) : (term406 x) = term328.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7237455 : term397 = term328.
Proof. exact (@lem7237454 term189). Qed.
Lemma lem7237456 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237457 : term407 = term408.
Proof. exact (MK_COMB (@lem7237456) (@lem7237455)). Qed.
Lemma lem7237458 : term399 = term390.
Proof. exact (MK_COMB (@lem7237457) (@lem7237452)). Qed.
Lemma lem7237459 : term398 = term390.
Proof. exact (TRANS (@lem7237444) (@lem7237458)). Qed.
Lemma lem7237460 : term397 = term390.
Proof. exact (TRANS (@lem7237443) (@lem7237459)). Qed.
Lemma lem7237462 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237463 : term390 = term328.
Proof. exact (@lem7237462 term328). Qed.
Lemma lem7237464 : term397 = term328.
Proof. exact (TRANS (@lem7237460) (@lem7237463)). Qed.
Lemma lem7237465 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7237466 (_96884 : int) : (term388 _96884) = (term410 _96884).
Proof. exact (MK_COMB (@lem7237465 _96884) (@lem7237464)). Qed.
Lemma lem7237467 (_96884 : int) : (term410 _96884) = (real_of_int _96884).
Proof. exact (@lem1982723 (real_of_int _96884)). Qed.
Lemma lem7237468 (_96884 : int) : (term388 _96884) = (real_of_int _96884).
Proof. exact (TRANS (@lem7237466 _96884) (@lem7237467 _96884)). Qed.
Lemma lem7237470 (_96884 : int) : (term387 _96884) = (real_of_int _96884).
Proof. exact (TRANS (@lem7237434 _96884) (@lem7237468 _96884)). Qed.
Lemma lem7237471 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237472 (_96884 : int) : (term411 _96884) = (term412 _96884).
Proof. exact (MK_COMB (@lem7237471) (@lem7237470 _96884)). Qed.
Lemma lem7237473 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237474 (_96884 : int) : (term386 _96884) = (term413 _96884).
Proof. exact (MK_COMB (@lem7237472 _96884) (@lem7237473)). Qed.
Lemma lem7237475 (_96884 : int) : (term331 _96884) = (term413 _96884).
Proof. exact (TRANS (@lem7237428 _96884) (@lem7237474 _96884)). Qed.
Lemma lem7237476 (_96885 : int) : (term331 _96885) = (term386 _96885).
Proof. exact (@lem1988287 (real_of_int _96885) term328). Qed.
Lemma lem7237482 (_96885 : int) : (term387 _96885) = (term388 _96885).
Proof. exact (@lem1982792 (real_of_int _96885) term328). Qed.
Lemma lem7237484 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237485 : term328 = term390.
Proof. exact (@lem7237484 (NUMERAL 0)). Qed.
Lemma lem7237487 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237488 : term393 = term394.
Proof. exact (@lem7237487 term189). Qed.
Lemma lem7237489 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237490 : term395 = term396.
Proof. exact (MK_COMB (@lem7237489) (@lem7237488)). Qed.
Lemma lem7237491 : term397 = term398.
Proof. exact (MK_COMB (@lem7237490) (@lem7237485)). Qed.
Lemma lem7237492 : term398 = term399.
Proof. exact (@lem1981613 term393 term328 term340 term340). Qed.
Lemma lem7237494 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237495 : term402 = term403.
Proof. exact (@lem7237494 term189 term189). Qed.
Lemma lem7237496 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237497 : term405 = term189.
Proof. exact (EQ_MP (@lem7237496) (@lem940073)). Qed.
Lemma lem7237498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237499 : term403 = term340.
Proof. exact (MK_COMB (@lem7237498) (@lem7237497)). Qed.
Lemma lem7237500 : term402 = term340.
Proof. exact (TRANS (@lem7237495) (@lem7237499)). Qed.
Lemma lem7237502 (x : nat) : (term406 x) = term328.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7237503 : term397 = term328.
Proof. exact (@lem7237502 term189). Qed.
Lemma lem7237504 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237505 : term407 = term408.
Proof. exact (MK_COMB (@lem7237504) (@lem7237503)). Qed.
Lemma lem7237506 : term399 = term390.
Proof. exact (MK_COMB (@lem7237505) (@lem7237500)). Qed.
Lemma lem7237507 : term398 = term390.
Proof. exact (TRANS (@lem7237492) (@lem7237506)). Qed.
Lemma lem7237508 : term397 = term390.
Proof. exact (TRANS (@lem7237491) (@lem7237507)). Qed.
Lemma lem7237510 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237511 : term390 = term328.
Proof. exact (@lem7237510 term328). Qed.
Lemma lem7237512 : term397 = term328.
Proof. exact (TRANS (@lem7237508) (@lem7237511)). Qed.
Lemma lem7237513 (_96885 : int) : (term341 _96885) = (term341 _96885).
Proof. exact (eq_refl (term341 _96885)). Qed.
Lemma lem7237514 (_96885 : int) : (term388 _96885) = (term410 _96885).
Proof. exact (MK_COMB (@lem7237513 _96885) (@lem7237512)). Qed.
Lemma lem7237515 (_96885 : int) : (term410 _96885) = (real_of_int _96885).
Proof. exact (@lem1982723 (real_of_int _96885)). Qed.
Lemma lem7237516 (_96885 : int) : (term388 _96885) = (real_of_int _96885).
Proof. exact (TRANS (@lem7237514 _96885) (@lem7237515 _96885)). Qed.
Lemma lem7237518 (_96885 : int) : (term387 _96885) = (real_of_int _96885).
Proof. exact (TRANS (@lem7237482 _96885) (@lem7237516 _96885)). Qed.
Lemma lem7237519 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237520 (_96885 : int) : (term411 _96885) = (term412 _96885).
Proof. exact (MK_COMB (@lem7237519) (@lem7237518 _96885)). Qed.
Lemma lem7237521 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237522 (_96885 : int) : (term386 _96885) = (term413 _96885).
Proof. exact (MK_COMB (@lem7237520 _96885) (@lem7237521)). Qed.
Lemma lem7237523 (_96885 : int) : (term331 _96885) = (term413 _96885).
Proof. exact (TRANS (@lem7237476 _96885) (@lem7237522 _96885)). Qed.
Lemma lem7237524 (_96886 : int) : (term331 _96886) = (term386 _96886).
Proof. exact (@lem1988287 (real_of_int _96886) term328). Qed.
Lemma lem7237530 (_96886 : int) : (term387 _96886) = (term388 _96886).
Proof. exact (@lem1982792 (real_of_int _96886) term328). Qed.
Lemma lem7237532 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237533 : term328 = term390.
Proof. exact (@lem7237532 (NUMERAL 0)). Qed.
Lemma lem7237535 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237536 : term393 = term394.
Proof. exact (@lem7237535 term189). Qed.
Lemma lem7237537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237538 : term395 = term396.
Proof. exact (MK_COMB (@lem7237537) (@lem7237536)). Qed.
Lemma lem7237539 : term397 = term398.
Proof. exact (MK_COMB (@lem7237538) (@lem7237533)). Qed.
Lemma lem7237540 : term398 = term399.
Proof. exact (@lem1981613 term393 term328 term340 term340). Qed.
Lemma lem7237542 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237543 : term402 = term403.
Proof. exact (@lem7237542 term189 term189). Qed.
Lemma lem7237544 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237545 : term405 = term189.
Proof. exact (EQ_MP (@lem7237544) (@lem940073)). Qed.
Lemma lem7237546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237547 : term403 = term340.
Proof. exact (MK_COMB (@lem7237546) (@lem7237545)). Qed.
Lemma lem7237548 : term402 = term340.
Proof. exact (TRANS (@lem7237543) (@lem7237547)). Qed.
Lemma lem7237550 (x : nat) : (term406 x) = term328.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7237551 : term397 = term328.
Proof. exact (@lem7237550 term189). Qed.
Lemma lem7237552 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237553 : term407 = term408.
Proof. exact (MK_COMB (@lem7237552) (@lem7237551)). Qed.
Lemma lem7237554 : term399 = term390.
Proof. exact (MK_COMB (@lem7237553) (@lem7237548)). Qed.
Lemma lem7237555 : term398 = term390.
Proof. exact (TRANS (@lem7237540) (@lem7237554)). Qed.
Lemma lem7237556 : term397 = term390.
Proof. exact (TRANS (@lem7237539) (@lem7237555)). Qed.
Lemma lem7237558 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237559 : term390 = term328.
Proof. exact (@lem7237558 term328). Qed.
Lemma lem7237560 : term397 = term328.
Proof. exact (TRANS (@lem7237556) (@lem7237559)). Qed.
Lemma lem7237561 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7237562 (_96886 : int) : (term388 _96886) = (term410 _96886).
Proof. exact (MK_COMB (@lem7237561 _96886) (@lem7237560)). Qed.
Lemma lem7237563 (_96886 : int) : (term410 _96886) = (real_of_int _96886).
Proof. exact (@lem1982723 (real_of_int _96886)). Qed.
Lemma lem7237564 (_96886 : int) : (term388 _96886) = (real_of_int _96886).
Proof. exact (TRANS (@lem7237562 _96886) (@lem7237563 _96886)). Qed.
Lemma lem7237566 (_96886 : int) : (term387 _96886) = (real_of_int _96886).
Proof. exact (TRANS (@lem7237530 _96886) (@lem7237564 _96886)). Qed.
Lemma lem7237567 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237568 (_96886 : int) : (term411 _96886) = (term412 _96886).
Proof. exact (MK_COMB (@lem7237567) (@lem7237566 _96886)). Qed.
Lemma lem7237569 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237570 (_96886 : int) : (term386 _96886) = (term413 _96886).
Proof. exact (MK_COMB (@lem7237568 _96886) (@lem7237569)). Qed.
Lemma lem7237571 (_96886 : int) : (term331 _96886) = (term413 _96886).
Proof. exact (TRANS (@lem7237524 _96886) (@lem7237570 _96886)). Qed.
Lemma lem7237572 (_96884 : int) (_96883 : int) : (term344 _96883 _96884) = (term414 _96884 _96883).
Proof. exact (@lem1988287 (term342 _96884) (real_of_int _96883)). Qed.
Lemma lem7237584 (_96884 : int) (_96883 : int) : (term415 _96884 _96883) = (term416 _96884 _96883).
Proof. exact (@lem1982792 (term342 _96884) (real_of_int _96883)). Qed.
Lemma lem7237589 (_96883 : int) (_96884 : int) : (term416 _96884 _96883) = (term417 _96883 _96884).
Proof. exact (@lem1982761 (term418 _96883) (term342 _96884)). Qed.
Lemma lem7237591 (_96883 : int) (_96884 : int) : (term415 _96884 _96883) = (term417 _96883 _96884).
Proof. exact (TRANS (@lem7237584 _96884 _96883) (@lem7237589 _96883 _96884)). Qed.
Lemma lem7237592 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237593 (_96883 : int) (_96884 : int) : (term419 _96884 _96883) = (term420 _96883 _96884).
Proof. exact (MK_COMB (@lem7237592) (@lem7237591 _96883 _96884)). Qed.
Lemma lem7237594 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237595 (_96883 : int) (_96884 : int) : (term414 _96884 _96883) = (term421 _96883 _96884).
Proof. exact (MK_COMB (@lem7237593 _96883 _96884) (@lem7237594)). Qed.
Lemma lem7237596 (_96883 : int) (_96884 : int) : (term344 _96883 _96884) = (term421 _96883 _96884).
Proof. exact (TRANS (@lem7237572 _96884 _96883) (@lem7237595 _96883 _96884)). Qed.
Lemma lem7237597 (_96885 : int) (_96884 : int) : (term323 _96884 _96885) = (term422 _96885 _96884).
Proof. exact (@lem1988287 (real_of_int _96885) (real_of_int _96884)). Qed.
Lemma lem7237603 (_96885 : int) (_96884 : int) : (term423 _96885 _96884) = (term424 _96885 _96884).
Proof. exact (@lem1982792 (real_of_int _96885) (real_of_int _96884)). Qed.
Lemma lem7237608 (_96884 : int) (_96885 : int) : (term424 _96885 _96884) = (term425 _96884 _96885).
Proof. exact (@lem1982761 (term418 _96884) (real_of_int _96885)). Qed.
Lemma lem7237610 (_96884 : int) (_96885 : int) : (term423 _96885 _96884) = (term425 _96884 _96885).
Proof. exact (TRANS (@lem7237603 _96885 _96884) (@lem7237608 _96884 _96885)). Qed.
Lemma lem7237611 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237612 (_96884 : int) (_96885 : int) : (term426 _96885 _96884) = (term427 _96884 _96885).
Proof. exact (MK_COMB (@lem7237611) (@lem7237610 _96884 _96885)). Qed.
Lemma lem7237613 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237614 (_96884 : int) (_96885 : int) : (term422 _96885 _96884) = (term428 _96884 _96885).
Proof. exact (MK_COMB (@lem7237612 _96884 _96885) (@lem7237613)). Qed.
Lemma lem7237615 (_96884 : int) (_96885 : int) : (term323 _96884 _96885) = (term428 _96884 _96885).
Proof. exact (TRANS (@lem7237597 _96885 _96884) (@lem7237614 _96884 _96885)). Qed.
Lemma lem7237616 (_96886 : int) (_96883 : int) : (term323 _96883 _96886) = (term422 _96886 _96883).
Proof. exact (@lem1988287 (real_of_int _96886) (real_of_int _96883)). Qed.
Lemma lem7237622 (_96886 : int) (_96883 : int) : (term423 _96886 _96883) = (term424 _96886 _96883).
Proof. exact (@lem1982792 (real_of_int _96886) (real_of_int _96883)). Qed.
Lemma lem7237627 (_96883 : int) (_96886 : int) : (term424 _96886 _96883) = (term425 _96883 _96886).
Proof. exact (@lem1982761 (term418 _96883) (real_of_int _96886)). Qed.
Lemma lem7237629 (_96883 : int) (_96886 : int) : (term423 _96886 _96883) = (term425 _96883 _96886).
Proof. exact (TRANS (@lem7237622 _96886 _96883) (@lem7237627 _96883 _96886)). Qed.
Lemma lem7237630 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237631 (_96883 : int) (_96886 : int) : (term426 _96886 _96883) = (term427 _96883 _96886).
Proof. exact (MK_COMB (@lem7237630) (@lem7237629 _96883 _96886)). Qed.
Lemma lem7237632 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237633 (_96883 : int) (_96886 : int) : (term422 _96886 _96883) = (term428 _96883 _96886).
Proof. exact (MK_COMB (@lem7237631 _96883 _96886) (@lem7237632)). Qed.
Lemma lem7237634 (_96883 : int) (_96886 : int) : (term323 _96883 _96886) = (term428 _96883 _96886).
Proof. exact (TRANS (@lem7237616 _96886 _96883) (@lem7237633 _96883 _96886)). Qed.
Lemma lem7237635 (_96884 : int) (_96886 : int) : (term323 _96886 _96884) = (term422 _96884 _96886).
Proof. exact (@lem1988287 (real_of_int _96884) (real_of_int _96886)). Qed.
Lemma lem7237648 (_96884 : int) (_96886 : int) : (term423 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982792 (real_of_int _96884) (real_of_int _96886)). Qed.
Lemma lem7237649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237650 (_96884 : int) (_96886 : int) : (term426 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7237649) (@lem7237648 _96884 _96886)). Qed.
Lemma lem7237651 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237652 (_96884 : int) (_96886 : int) : (term422 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7237650 _96884 _96886) (@lem7237651)). Qed.
Lemma lem7237653 (_96884 : int) (_96886 : int) : (term323 _96886 _96884) = (term430 _96884 _96886).
Proof. exact (TRANS (@lem7237635 _96884 _96886) (@lem7237652 _96884 _96886)). Qed.
Lemma lem7237654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237655 (_96883 : int) (_96886 : int) : (term345 _96883 _96886) = (term431 _96883 _96886).
Proof. exact (MK_COMB (@lem7237654) (@lem7237634 _96883 _96886)). Qed.
Lemma lem7237656 (_96883 : int) (_96884 : int) (_96886 : int) : (term346 _96883 _96886 _96884) = (term432 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7237655 _96883 _96886) (@lem7237653 _96884 _96886)). Qed.
Lemma lem7237657 (_96886 : int) (_96884 : int) : (term350 _96884 _96886) = (term433 _96886 _96884).
Proof. exact (@lem1988287 (real_of_int _96886) (term342 _96884)). Qed.
Lemma lem7237669 (_96886 : int) (_96884 : int) : (term434 _96886 _96884) = (term435 _96886 _96884).
Proof. exact (@lem1982792 (real_of_int _96886) (term342 _96884)). Qed.
Lemma lem7237670 (_96884 : int) : (term436 _96884) = (term437 _96884).
Proof. exact (@lem1982781 (real_of_int _96884) term393 term340). Qed.
Lemma lem7237672 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237673 : term340 = term438.
Proof. exact (@lem7237672 term189). Qed.
Lemma lem7237675 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237676 : term393 = term394.
Proof. exact (@lem7237675 term189). Qed.
Lemma lem7237677 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237678 : term395 = term396.
Proof. exact (MK_COMB (@lem7237677) (@lem7237676)). Qed.
Lemma lem7237679 : term439 = term440.
Proof. exact (MK_COMB (@lem7237678) (@lem7237673)). Qed.
Lemma lem7237680 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7237682 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237683 : term402 = term403.
Proof. exact (@lem7237682 term189 term189). Qed.
Lemma lem7237684 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237685 : term405 = term189.
Proof. exact (EQ_MP (@lem7237684) (@lem940073)). Qed.
Lemma lem7237686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237687 : term403 = term340.
Proof. exact (MK_COMB (@lem7237686) (@lem7237685)). Qed.
Lemma lem7237688 : term402 = term340.
Proof. exact (TRANS (@lem7237683) (@lem7237687)). Qed.
Lemma lem7237690 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7237691 : term439 = term444.
Proof. exact (@lem7237690 term189 term189). Qed.
Lemma lem7237692 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237693 : term405 = term189.
Proof. exact (EQ_MP (@lem7237692) (@lem940073)). Qed.
Lemma lem7237694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237695 : term403 = term340.
Proof. exact (MK_COMB (@lem7237694) (@lem7237693)). Qed.
Lemma lem7237696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7237697 : term444 = term393.
Proof. exact (MK_COMB (@lem7237696) (@lem7237695)). Qed.
Lemma lem7237698 : term439 = term393.
Proof. exact (TRANS (@lem7237691) (@lem7237697)). Qed.
Lemma lem7237699 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237700 : term445 = term446.
Proof. exact (MK_COMB (@lem7237699) (@lem7237698)). Qed.
Lemma lem7237701 : term441 = term394.
Proof. exact (MK_COMB (@lem7237700) (@lem7237688)). Qed.
Lemma lem7237702 : term440 = term394.
Proof. exact (TRANS (@lem7237680) (@lem7237701)). Qed.
Lemma lem7237703 : term439 = term394.
Proof. exact (TRANS (@lem7237679) (@lem7237702)). Qed.
Lemma lem7237705 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237706 : term394 = term393.
Proof. exact (@lem7237705 term393). Qed.
Lemma lem7237707 : term439 = term393.
Proof. exact (TRANS (@lem7237703) (@lem7237706)). Qed.
Lemma lem7237710 (_96884 : int) : (term447 _96884) = (term447 _96884).
Proof. exact (eq_refl (term447 _96884)). Qed.
Lemma lem7237711 (_96884 : int) : (term437 _96884) = (term448 _96884).
Proof. exact (MK_COMB (@lem7237710 _96884) (@lem7237707)). Qed.
Lemma lem7237712 (_96884 : int) : (term436 _96884) = (term448 _96884).
Proof. exact (TRANS (@lem7237670 _96884) (@lem7237711 _96884)). Qed.
Lemma lem7237713 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7237714 (_96886 : int) (_96884 : int) : (term435 _96886 _96884) = (term449 _96886 _96884).
Proof. exact (MK_COMB (@lem7237713 _96886) (@lem7237712 _96884)). Qed.
Lemma lem7237719 (_96884 : int) (_96886 : int) : (term449 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (@lem1982757 (term418 _96884) (real_of_int _96886) term393). Qed.
Lemma lem7237720 (_96884 : int) (_96886 : int) : (term435 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7237714 _96886 _96884) (@lem7237719 _96884 _96886)). Qed.
Lemma lem7237722 (_96884 : int) (_96886 : int) : (term434 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7237669 _96886 _96884) (@lem7237720 _96884 _96886)). Qed.
Lemma lem7237723 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237724 (_96884 : int) (_96886 : int) : (term451 _96886 _96884) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7237723) (@lem7237722 _96884 _96886)). Qed.
Lemma lem7237725 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237726 (_96884 : int) (_96886 : int) : (term433 _96886 _96884) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7237724 _96884 _96886) (@lem7237725)). Qed.
Lemma lem7237727 (_96884 : int) (_96886 : int) : (term350 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (TRANS (@lem7237657 _96886 _96884) (@lem7237726 _96884 _96886)). Qed.
Lemma lem7237728 (_96885 : int) (_96886 : int) : (term323 _96886 _96885) = (term422 _96885 _96886).
Proof. exact (@lem1988287 (real_of_int _96885) (real_of_int _96886)). Qed.
Lemma lem7237741 (_96885 : int) (_96886 : int) : (term423 _96885 _96886) = (term424 _96885 _96886).
Proof. exact (@lem1982792 (real_of_int _96885) (real_of_int _96886)). Qed.
Lemma lem7237742 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237743 (_96885 : int) (_96886 : int) : (term426 _96885 _96886) = (term429 _96885 _96886).
Proof. exact (MK_COMB (@lem7237742) (@lem7237741 _96885 _96886)). Qed.
Lemma lem7237744 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237745 (_96885 : int) (_96886 : int) : (term422 _96885 _96886) = (term430 _96885 _96886).
Proof. exact (MK_COMB (@lem7237743 _96885 _96886) (@lem7237744)). Qed.
Lemma lem7237746 (_96885 : int) (_96886 : int) : (term323 _96886 _96885) = (term430 _96885 _96886).
Proof. exact (TRANS (@lem7237728 _96885 _96886) (@lem7237745 _96885 _96886)). Qed.
Lemma lem7237747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237748 (_96884 : int) (_96886 : int) : (term351 _96884 _96886) = (term454 _96884 _96886).
Proof. exact (MK_COMB (@lem7237747) (@lem7237727 _96884 _96886)). Qed.
Lemma lem7237749 (_96884 : int) (_96885 : int) (_96886 : int) : (term352 _96884 _96886 _96885) = (term455 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7237748 _96884 _96886) (@lem7237746 _96885 _96886)). Qed.
Lemma lem7237750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7237751 (_96883 : int) (_96884 : int) (_96886 : int) : (term353 _96883 _96886 _96884) = (term456 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7237750) (@lem7237656 _96883 _96884 _96886)). Qed.
Lemma lem7237752 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term354 _96883 _96884 _96886 _96885) = (term457 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7237751 _96883 _96884 _96886) (@lem7237749 _96884 _96885 _96886)). Qed.
Lemma lem7237753 (_96883 : int) (_96886 : int) : (term350 _96886 _96883) = (term433 _96883 _96886).
Proof. exact (@lem1988287 (real_of_int _96883) (term342 _96886)). Qed.
Lemma lem7237765 (_96883 : int) (_96886 : int) : (term434 _96883 _96886) = (term435 _96883 _96886).
Proof. exact (@lem1982792 (real_of_int _96883) (term342 _96886)). Qed.
Lemma lem7237766 (_96886 : int) : (term436 _96886) = (term437 _96886).
Proof. exact (@lem1982781 (real_of_int _96886) term393 term340). Qed.
Lemma lem7237768 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237769 : term340 = term438.
Proof. exact (@lem7237768 term189). Qed.
Lemma lem7237771 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237772 : term393 = term394.
Proof. exact (@lem7237771 term189). Qed.
Lemma lem7237773 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237774 : term395 = term396.
Proof. exact (MK_COMB (@lem7237773) (@lem7237772)). Qed.
Lemma lem7237775 : term439 = term440.
Proof. exact (MK_COMB (@lem7237774) (@lem7237769)). Qed.
Lemma lem7237776 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7237778 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237779 : term402 = term403.
Proof. exact (@lem7237778 term189 term189). Qed.
Lemma lem7237780 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237781 : term405 = term189.
Proof. exact (EQ_MP (@lem7237780) (@lem940073)). Qed.
Lemma lem7237782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237783 : term403 = term340.
Proof. exact (MK_COMB (@lem7237782) (@lem7237781)). Qed.
Lemma lem7237784 : term402 = term340.
Proof. exact (TRANS (@lem7237779) (@lem7237783)). Qed.
Lemma lem7237786 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7237787 : term439 = term444.
Proof. exact (@lem7237786 term189 term189). Qed.
Lemma lem7237788 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237789 : term405 = term189.
Proof. exact (EQ_MP (@lem7237788) (@lem940073)). Qed.
Lemma lem7237790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237791 : term403 = term340.
Proof. exact (MK_COMB (@lem7237790) (@lem7237789)). Qed.
Lemma lem7237792 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7237793 : term444 = term393.
Proof. exact (MK_COMB (@lem7237792) (@lem7237791)). Qed.
Lemma lem7237794 : term439 = term393.
Proof. exact (TRANS (@lem7237787) (@lem7237793)). Qed.
Lemma lem7237795 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237796 : term445 = term446.
Proof. exact (MK_COMB (@lem7237795) (@lem7237794)). Qed.
Lemma lem7237797 : term441 = term394.
Proof. exact (MK_COMB (@lem7237796) (@lem7237784)). Qed.
Lemma lem7237798 : term440 = term394.
Proof. exact (TRANS (@lem7237776) (@lem7237797)). Qed.
Lemma lem7237799 : term439 = term394.
Proof. exact (TRANS (@lem7237775) (@lem7237798)). Qed.
Lemma lem7237801 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237802 : term394 = term393.
Proof. exact (@lem7237801 term393). Qed.
Lemma lem7237803 : term439 = term393.
Proof. exact (TRANS (@lem7237799) (@lem7237802)). Qed.
Lemma lem7237806 (_96886 : int) : (term447 _96886) = (term447 _96886).
Proof. exact (eq_refl (term447 _96886)). Qed.
Lemma lem7237807 (_96886 : int) : (term437 _96886) = (term448 _96886).
Proof. exact (MK_COMB (@lem7237806 _96886) (@lem7237803)). Qed.
Lemma lem7237808 (_96886 : int) : (term436 _96886) = (term448 _96886).
Proof. exact (TRANS (@lem7237766 _96886) (@lem7237807 _96886)). Qed.
Lemma lem7237809 (_96883 : int) : (term341 _96883) = (term341 _96883).
Proof. exact (eq_refl (term341 _96883)). Qed.
Lemma lem7237812 (_96883 : int) (_96886 : int) : (term435 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (MK_COMB (@lem7237809 _96883) (@lem7237808 _96886)). Qed.
Lemma lem7237814 (_96883 : int) (_96886 : int) : (term434 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (TRANS (@lem7237765 _96883 _96886) (@lem7237812 _96883 _96886)). Qed.
Lemma lem7237815 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237816 (_96883 : int) (_96886 : int) : (term451 _96883 _96886) = (term458 _96883 _96886).
Proof. exact (MK_COMB (@lem7237815) (@lem7237814 _96883 _96886)). Qed.
Lemma lem7237817 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237818 (_96883 : int) (_96886 : int) : (term433 _96883 _96886) = (term459 _96883 _96886).
Proof. exact (MK_COMB (@lem7237816 _96883 _96886) (@lem7237817)). Qed.
Lemma lem7237819 (_96883 : int) (_96886 : int) : (term350 _96886 _96883) = (term459 _96883 _96886).
Proof. exact (TRANS (@lem7237753 _96883 _96886) (@lem7237818 _96883 _96886)). Qed.
Lemma lem7237820 (_96886 : int) (_96884 : int) : (term350 _96884 _96886) = (term433 _96886 _96884).
Proof. exact (@lem1988287 (real_of_int _96886) (term342 _96884)). Qed.
Lemma lem7237832 (_96886 : int) (_96884 : int) : (term434 _96886 _96884) = (term435 _96886 _96884).
Proof. exact (@lem1982792 (real_of_int _96886) (term342 _96884)). Qed.
Lemma lem7237833 (_96884 : int) : (term436 _96884) = (term437 _96884).
Proof. exact (@lem1982781 (real_of_int _96884) term393 term340). Qed.
Lemma lem7237835 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237836 : term340 = term438.
Proof. exact (@lem7237835 term189). Qed.
Lemma lem7237838 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237839 : term393 = term394.
Proof. exact (@lem7237838 term189). Qed.
Lemma lem7237840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237841 : term395 = term396.
Proof. exact (MK_COMB (@lem7237840) (@lem7237839)). Qed.
Lemma lem7237842 : term439 = term440.
Proof. exact (MK_COMB (@lem7237841) (@lem7237836)). Qed.
Lemma lem7237843 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7237845 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237846 : term402 = term403.
Proof. exact (@lem7237845 term189 term189). Qed.
Lemma lem7237847 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237848 : term405 = term189.
Proof. exact (EQ_MP (@lem7237847) (@lem940073)). Qed.
Lemma lem7237849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237850 : term403 = term340.
Proof. exact (MK_COMB (@lem7237849) (@lem7237848)). Qed.
Lemma lem7237851 : term402 = term340.
Proof. exact (TRANS (@lem7237846) (@lem7237850)). Qed.
Lemma lem7237853 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7237854 : term439 = term444.
Proof. exact (@lem7237853 term189 term189). Qed.
Lemma lem7237855 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237856 : term405 = term189.
Proof. exact (EQ_MP (@lem7237855) (@lem940073)). Qed.
Lemma lem7237857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237858 : term403 = term340.
Proof. exact (MK_COMB (@lem7237857) (@lem7237856)). Qed.
Lemma lem7237859 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7237860 : term444 = term393.
Proof. exact (MK_COMB (@lem7237859) (@lem7237858)). Qed.
Lemma lem7237861 : term439 = term393.
Proof. exact (TRANS (@lem7237854) (@lem7237860)). Qed.
Lemma lem7237862 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237863 : term445 = term446.
Proof. exact (MK_COMB (@lem7237862) (@lem7237861)). Qed.
Lemma lem7237864 : term441 = term394.
Proof. exact (MK_COMB (@lem7237863) (@lem7237851)). Qed.
Lemma lem7237865 : term440 = term394.
Proof. exact (TRANS (@lem7237843) (@lem7237864)). Qed.
Lemma lem7237866 : term439 = term394.
Proof. exact (TRANS (@lem7237842) (@lem7237865)). Qed.
Lemma lem7237868 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237869 : term394 = term393.
Proof. exact (@lem7237868 term393). Qed.
Lemma lem7237870 : term439 = term393.
Proof. exact (TRANS (@lem7237866) (@lem7237869)). Qed.
Lemma lem7237873 (_96884 : int) : (term447 _96884) = (term447 _96884).
Proof. exact (eq_refl (term447 _96884)). Qed.
Lemma lem7237874 (_96884 : int) : (term437 _96884) = (term448 _96884).
Proof. exact (MK_COMB (@lem7237873 _96884) (@lem7237870)). Qed.
Lemma lem7237875 (_96884 : int) : (term436 _96884) = (term448 _96884).
Proof. exact (TRANS (@lem7237833 _96884) (@lem7237874 _96884)). Qed.
Lemma lem7237876 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7237877 (_96886 : int) (_96884 : int) : (term435 _96886 _96884) = (term449 _96886 _96884).
Proof. exact (MK_COMB (@lem7237876 _96886) (@lem7237875 _96884)). Qed.
Lemma lem7237882 (_96884 : int) (_96886 : int) : (term449 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (@lem1982757 (term418 _96884) (real_of_int _96886) term393). Qed.
Lemma lem7237883 (_96884 : int) (_96886 : int) : (term435 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7237877 _96886 _96884) (@lem7237882 _96884 _96886)). Qed.
Lemma lem7237885 (_96884 : int) (_96886 : int) : (term434 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7237832 _96886 _96884) (@lem7237883 _96884 _96886)). Qed.
Lemma lem7237886 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7237887 (_96884 : int) (_96886 : int) : (term451 _96886 _96884) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7237886) (@lem7237885 _96884 _96886)). Qed.
Lemma lem7237888 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7237889 (_96884 : int) (_96886 : int) : (term433 _96886 _96884) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7237887 _96884 _96886) (@lem7237888)). Qed.
Lemma lem7237890 (_96884 : int) (_96886 : int) : (term350 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (TRANS (@lem7237820 _96886 _96884) (@lem7237889 _96884 _96886)). Qed.
Lemma lem7237891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7237892 (_96883 : int) (_96886 : int) : (term356 _96886 _96883) = (term460 _96883 _96886).
Proof. exact (MK_COMB (@lem7237891) (@lem7237819 _96883 _96886)). Qed.
Lemma lem7237893 (_96883 : int) (_96884 : int) (_96886 : int) : (term357 _96883 _96884 _96886) = (term461 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7237892 _96883 _96886) (@lem7237890 _96884 _96886)). Qed.
Lemma lem7237894 (_96884 : int) (_96886 : int) : (term360 _96886 _96884) = (term462 _96884 _96886).
Proof. exact (@lem1988287 (term342 _96884) (term342 _96886)). Qed.
Lemma lem7237912 (_96884 : int) (_96886 : int) : (term463 _96884 _96886) = (term464 _96884 _96886).
Proof. exact (@lem1982792 (term342 _96884) (term342 _96886)). Qed.
Lemma lem7237913 (_96886 : int) : (term436 _96886) = (term437 _96886).
Proof. exact (@lem1982781 (real_of_int _96886) term393 term340). Qed.
Lemma lem7237915 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237916 : term340 = term438.
Proof. exact (@lem7237915 term189). Qed.
Lemma lem7237918 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237919 : term393 = term394.
Proof. exact (@lem7237918 term189). Qed.
Lemma lem7237920 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7237921 : term395 = term396.
Proof. exact (MK_COMB (@lem7237920) (@lem7237919)). Qed.
Lemma lem7237922 : term439 = term440.
Proof. exact (MK_COMB (@lem7237921) (@lem7237916)). Qed.
Lemma lem7237923 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7237925 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7237926 : term402 = term403.
Proof. exact (@lem7237925 term189 term189). Qed.
Lemma lem7237927 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237928 : term405 = term189.
Proof. exact (EQ_MP (@lem7237927) (@lem940073)). Qed.
Lemma lem7237929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237930 : term403 = term340.
Proof. exact (MK_COMB (@lem7237929) (@lem7237928)). Qed.
Lemma lem7237931 : term402 = term340.
Proof. exact (TRANS (@lem7237926) (@lem7237930)). Qed.
Lemma lem7237933 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7237934 : term439 = term444.
Proof. exact (@lem7237933 term189 term189). Qed.
Lemma lem7237935 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7237936 : term405 = term189.
Proof. exact (EQ_MP (@lem7237935) (@lem940073)). Qed.
Lemma lem7237937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7237938 : term403 = term340.
Proof. exact (MK_COMB (@lem7237937) (@lem7237936)). Qed.
Lemma lem7237939 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7237940 : term444 = term393.
Proof. exact (MK_COMB (@lem7237939) (@lem7237938)). Qed.
Lemma lem7237941 : term439 = term393.
Proof. exact (TRANS (@lem7237934) (@lem7237940)). Qed.
Lemma lem7237942 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7237943 : term445 = term446.
Proof. exact (MK_COMB (@lem7237942) (@lem7237941)). Qed.
Lemma lem7237944 : term441 = term394.
Proof. exact (MK_COMB (@lem7237943) (@lem7237931)). Qed.
Lemma lem7237945 : term440 = term394.
Proof. exact (TRANS (@lem7237923) (@lem7237944)). Qed.
Lemma lem7237946 : term439 = term394.
Proof. exact (TRANS (@lem7237922) (@lem7237945)). Qed.
Lemma lem7237948 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7237949 : term394 = term393.
Proof. exact (@lem7237948 term393). Qed.
Lemma lem7237950 : term439 = term393.
Proof. exact (TRANS (@lem7237946) (@lem7237949)). Qed.
Lemma lem7237953 (_96886 : int) : (term447 _96886) = (term447 _96886).
Proof. exact (eq_refl (term447 _96886)). Qed.
Lemma lem7237954 (_96886 : int) : (term437 _96886) = (term448 _96886).
Proof. exact (MK_COMB (@lem7237953 _96886) (@lem7237950)). Qed.
Lemma lem7237955 (_96886 : int) : (term436 _96886) = (term448 _96886).
Proof. exact (TRANS (@lem7237913 _96886) (@lem7237954 _96886)). Qed.
Lemma lem7237956 (_96884 : int) : (term465 _96884) = (term465 _96884).
Proof. exact (eq_refl (term465 _96884)). Qed.
Lemma lem7237957 (_96884 : int) (_96886 : int) : (term464 _96884 _96886) = (term466 _96884 _96886).
Proof. exact (MK_COMB (@lem7237956 _96884) (@lem7237955 _96886)). Qed.
Lemma lem7237958 (_96884 : int) (_96886 : int) : (term466 _96884 _96886) = (term467 _96884 _96886).
Proof. exact (@lem1982755 (real_of_int _96884) term340 (term448 _96886)). Qed.
Lemma lem7237959 (_96886 : int) : (term468 _96886) = (term469 _96886).
Proof. exact (@lem1982757 (term418 _96886) term340 term393). Qed.
Lemma lem7237961 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7237962 : term393 = term394.
Proof. exact (@lem7237961 term189). Qed.
Lemma lem7237964 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7237965 : term340 = term438.
Proof. exact (@lem7237964 term189). Qed.
Lemma lem7237966 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7237967 : term470 = term471.
Proof. exact (MK_COMB (@lem7237966) (@lem7237965)). Qed.
Lemma lem7237968 : term472 = term473.
Proof. exact (MK_COMB (@lem7237967) (@lem7237962)). Qed.
Lemma lem7237969 : term474.
Proof. exact (@lem1981473 term340 term340 term393 term340 term328 term340). Qed.
Lemma lem7237971 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7237972 : term476 = term477.
Proof. exact (@lem7237971 (NUMERAL 0) term189). Qed.
Lemma lem7237973 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7237974 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7237975 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7237974 h1) (fun h1 : term477 = True => @lem7237973)). Qed.
Lemma lem7237976 : term477 = True.
Proof. exact (EQ_MP (@lem7237975) (@lem7237973)). Qed.
Lemma lem7237977 : term476 = True.
Proof. exact (TRANS (@lem7237972) (@lem7237976)). Qed.
Lemma lem7237978 : True = term476.
Proof. exact (SYM (@lem7237977)). Qed.
Lemma lem7237979 : term476.
Proof. exact (EQ_MP (@lem7237978) (@lem0)). Qed.
Lemma lem7237980 : term479.
Proof. exact (@lem7237969 (@lem7237979)). Qed.
Lemma lem7237982 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7237983 : term476 = term477.
Proof. exact (@lem7237982 (NUMERAL 0) term189). Qed.
Lemma lem7237984 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7237985 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7237986 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7237985 h1) (fun h1 : term477 = True => @lem7237984)). Qed.
Lemma lem7237987 : term477 = True.
Proof. exact (EQ_MP (@lem7237986) (@lem7237984)). Qed.
Lemma lem7237988 : term476 = True.
Proof. exact (TRANS (@lem7237983) (@lem7237987)). Qed.
Lemma lem7237989 : True = term476.
Proof. exact (SYM (@lem7237988)). Qed.
Lemma lem7237990 : term476.
Proof. exact (EQ_MP (@lem7237989) (@lem0)). Qed.
Lemma lem7237991 : term480.
Proof. exact (@lem7237980 (@lem7237990)). Qed.
Lemma lem7237993 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7237994 : term476 = term477.
Proof. exact (@lem7237993 (NUMERAL 0) term189). Qed.
Lemma lem7237995 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7237996 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7237997 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7237996 h1) (fun h1 : term477 = True => @lem7237995)). Qed.
Lemma lem7237998 : term477 = True.
Proof. exact (EQ_MP (@lem7237997) (@lem7237995)). Qed.
Lemma lem7237999 : term476 = True.
Proof. exact (TRANS (@lem7237994) (@lem7237998)). Qed.
Lemma lem7238000 : True = term476.
Proof. exact (SYM (@lem7237999)). Qed.
Lemma lem7238001 : term476.
Proof. exact (EQ_MP (@lem7238000) (@lem0)). Qed.
Lemma lem7238002 : term481.
Proof. exact (@lem7237991 (@lem7238001)). Qed.
Lemma lem7238004 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7238005 : term439 = term444.
Proof. exact (@lem7238004 term189 term189). Qed.
Lemma lem7238006 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238007 : term405 = term189.
Proof. exact (EQ_MP (@lem7238006) (@lem940073)). Qed.
Lemma lem7238008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238009 : term403 = term340.
Proof. exact (MK_COMB (@lem7238008) (@lem7238007)). Qed.
Lemma lem7238010 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7238011 : term444 = term393.
Proof. exact (MK_COMB (@lem7238010) (@lem7238009)). Qed.
Lemma lem7238012 : term439 = term393.
Proof. exact (TRANS (@lem7238005) (@lem7238011)). Qed.
Lemma lem7238014 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7238015 : term402 = term403.
Proof. exact (@lem7238014 term189 term189). Qed.
Lemma lem7238016 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238017 : term405 = term189.
Proof. exact (EQ_MP (@lem7238016) (@lem940073)). Qed.
Lemma lem7238018 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238019 : term403 = term340.
Proof. exact (MK_COMB (@lem7238018) (@lem7238017)). Qed.
Lemma lem7238020 : term402 = term340.
Proof. exact (TRANS (@lem7238015) (@lem7238019)). Qed.
Lemma lem7238021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7238022 : term482 = term470.
Proof. exact (MK_COMB (@lem7238021) (@lem7238020)). Qed.
Lemma lem7238023 : term483 = term472.
Proof. exact (MK_COMB (@lem7238022) (@lem7238012)). Qed.
Lemma lem7238025 (m : nat) : (term484 m) = term328.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7238026 : term472 = term328.
Proof. exact (@lem7238025 term189). Qed.
Lemma lem7238027 : term483 = term328.
Proof. exact (TRANS (@lem7238023) (@lem7238026)). Qed.
Lemma lem7238028 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7238029 : term485 = term486.
Proof. exact (MK_COMB (@lem7238028) (@lem7238027)). Qed.
Lemma lem7238030 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7238031 : term487 = term488.
Proof. exact (MK_COMB (@lem7238029) (@lem7238030)). Qed.
Lemma lem7238033 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7238034 : term488 = term328.
Proof. exact (@lem7238033 term189). Qed.
Lemma lem7238035 : term487 = term328.
Proof. exact (TRANS (@lem7238031) (@lem7238034)). Qed.
Lemma lem7238037 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7238038 : term402 = term403.
Proof. exact (@lem7238037 term189 term189). Qed.
Lemma lem7238039 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238040 : term405 = term189.
Proof. exact (EQ_MP (@lem7238039) (@lem940073)). Qed.
Lemma lem7238041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238042 : term403 = term340.
Proof. exact (MK_COMB (@lem7238041) (@lem7238040)). Qed.
Lemma lem7238043 : term402 = term340.
Proof. exact (TRANS (@lem7238038) (@lem7238042)). Qed.
Lemma lem7238044 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7238045 : term490 = term488.
Proof. exact (MK_COMB (@lem7238044) (@lem7238043)). Qed.
Lemma lem7238047 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7238048 : term488 = term328.
Proof. exact (@lem7238047 term189). Qed.
Lemma lem7238049 : term490 = term328.
Proof. exact (TRANS (@lem7238045) (@lem7238048)). Qed.
Lemma lem7238050 : term328 = term490.
Proof. exact (SYM (@lem7238049)). Qed.
Lemma lem7238051 : term487 = term490.
Proof. exact (TRANS (@lem7238035) (@lem7238050)). Qed.
Lemma lem7238052 : term473 = term390.
Proof. exact (@lem7238002 (@lem7238051)). Qed.
Lemma lem7238053 : term472 = term390.
Proof. exact (TRANS (@lem7237968) (@lem7238052)). Qed.
Lemma lem7238055 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7238056 : term390 = term328.
Proof. exact (@lem7238055 term328). Qed.
Lemma lem7238057 : term472 = term328.
Proof. exact (TRANS (@lem7238053) (@lem7238056)). Qed.
Lemma lem7238058 (_96886 : int) : (term447 _96886) = (term447 _96886).
Proof. exact (eq_refl (term447 _96886)). Qed.
Lemma lem7238059 (_96886 : int) : (term469 _96886) = (term491 _96886).
Proof. exact (MK_COMB (@lem7238058 _96886) (@lem7238057)). Qed.
Lemma lem7238060 (_96886 : int) : (term468 _96886) = (term491 _96886).
Proof. exact (TRANS (@lem7237959 _96886) (@lem7238059 _96886)). Qed.
Lemma lem7238061 (_96886 : int) : (term491 _96886) = (term418 _96886).
Proof. exact (@lem1982723 (term418 _96886)). Qed.
Lemma lem7238062 (_96886 : int) : (term468 _96886) = (term418 _96886).
Proof. exact (TRANS (@lem7238060 _96886) (@lem7238061 _96886)). Qed.
Lemma lem7238063 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7238064 (_96884 : int) (_96886 : int) : (term467 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (MK_COMB (@lem7238063 _96884) (@lem7238062 _96886)). Qed.
Lemma lem7238065 (_96884 : int) (_96886 : int) : (term466 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (TRANS (@lem7237958 _96884 _96886) (@lem7238064 _96884 _96886)). Qed.
Lemma lem7238066 (_96884 : int) (_96886 : int) : (term464 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (TRANS (@lem7237957 _96884 _96886) (@lem7238065 _96884 _96886)). Qed.
Lemma lem7238068 (_96884 : int) (_96886 : int) : (term463 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (TRANS (@lem7237912 _96884 _96886) (@lem7238066 _96884 _96886)). Qed.
Lemma lem7238069 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238070 (_96884 : int) (_96886 : int) : (term492 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7238069) (@lem7238068 _96884 _96886)). Qed.
Lemma lem7238071 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238072 (_96884 : int) (_96886 : int) : (term462 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7238070 _96884 _96886) (@lem7238071)). Qed.
Lemma lem7238073 (_96884 : int) (_96886 : int) : (term360 _96886 _96884) = (term430 _96884 _96886).
Proof. exact (TRANS (@lem7237894 _96884 _96886) (@lem7238072 _96884 _96886)). Qed.
Lemma lem7238074 (_96886 : int) (_96885 : int) : (term350 _96885 _96886) = (term433 _96886 _96885).
Proof. exact (@lem1988287 (real_of_int _96886) (term342 _96885)). Qed.
Lemma lem7238086 (_96886 : int) (_96885 : int) : (term434 _96886 _96885) = (term435 _96886 _96885).
Proof. exact (@lem1982792 (real_of_int _96886) (term342 _96885)). Qed.
Lemma lem7238087 (_96885 : int) : (term436 _96885) = (term437 _96885).
Proof. exact (@lem1982781 (real_of_int _96885) term393 term340). Qed.
Lemma lem7238089 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7238090 : term340 = term438.
Proof. exact (@lem7238089 term189). Qed.
Lemma lem7238092 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7238093 : term393 = term394.
Proof. exact (@lem7238092 term189). Qed.
Lemma lem7238094 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7238095 : term395 = term396.
Proof. exact (MK_COMB (@lem7238094) (@lem7238093)). Qed.
Lemma lem7238096 : term439 = term440.
Proof. exact (MK_COMB (@lem7238095) (@lem7238090)). Qed.
Lemma lem7238097 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7238099 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7238100 : term402 = term403.
Proof. exact (@lem7238099 term189 term189). Qed.
Lemma lem7238101 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238102 : term405 = term189.
Proof. exact (EQ_MP (@lem7238101) (@lem940073)). Qed.
Lemma lem7238103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238104 : term403 = term340.
Proof. exact (MK_COMB (@lem7238103) (@lem7238102)). Qed.
Lemma lem7238105 : term402 = term340.
Proof. exact (TRANS (@lem7238100) (@lem7238104)). Qed.
Lemma lem7238107 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7238108 : term439 = term444.
Proof. exact (@lem7238107 term189 term189). Qed.
Lemma lem7238109 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238110 : term405 = term189.
Proof. exact (EQ_MP (@lem7238109) (@lem940073)). Qed.
Lemma lem7238111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238112 : term403 = term340.
Proof. exact (MK_COMB (@lem7238111) (@lem7238110)). Qed.
Lemma lem7238113 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7238114 : term444 = term393.
Proof. exact (MK_COMB (@lem7238113) (@lem7238112)). Qed.
Lemma lem7238115 : term439 = term393.
Proof. exact (TRANS (@lem7238108) (@lem7238114)). Qed.
Lemma lem7238116 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7238117 : term445 = term446.
Proof. exact (MK_COMB (@lem7238116) (@lem7238115)). Qed.
Lemma lem7238118 : term441 = term394.
Proof. exact (MK_COMB (@lem7238117) (@lem7238105)). Qed.
Lemma lem7238119 : term440 = term394.
Proof. exact (TRANS (@lem7238097) (@lem7238118)). Qed.
Lemma lem7238120 : term439 = term394.
Proof. exact (TRANS (@lem7238096) (@lem7238119)). Qed.
Lemma lem7238122 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7238123 : term394 = term393.
Proof. exact (@lem7238122 term393). Qed.
Lemma lem7238124 : term439 = term393.
Proof. exact (TRANS (@lem7238120) (@lem7238123)). Qed.
Lemma lem7238127 (_96885 : int) : (term447 _96885) = (term447 _96885).
Proof. exact (eq_refl (term447 _96885)). Qed.
Lemma lem7238128 (_96885 : int) : (term437 _96885) = (term448 _96885).
Proof. exact (MK_COMB (@lem7238127 _96885) (@lem7238124)). Qed.
Lemma lem7238129 (_96885 : int) : (term436 _96885) = (term448 _96885).
Proof. exact (TRANS (@lem7238087 _96885) (@lem7238128 _96885)). Qed.
Lemma lem7238130 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7238131 (_96886 : int) (_96885 : int) : (term435 _96886 _96885) = (term449 _96886 _96885).
Proof. exact (MK_COMB (@lem7238130 _96886) (@lem7238129 _96885)). Qed.
Lemma lem7238136 (_96885 : int) (_96886 : int) : (term449 _96886 _96885) = (term450 _96885 _96886).
Proof. exact (@lem1982757 (term418 _96885) (real_of_int _96886) term393). Qed.
Lemma lem7238137 (_96885 : int) (_96886 : int) : (term435 _96886 _96885) = (term450 _96885 _96886).
Proof. exact (TRANS (@lem7238131 _96886 _96885) (@lem7238136 _96885 _96886)). Qed.
Lemma lem7238139 (_96885 : int) (_96886 : int) : (term434 _96886 _96885) = (term450 _96885 _96886).
Proof. exact (TRANS (@lem7238086 _96886 _96885) (@lem7238137 _96885 _96886)). Qed.
Lemma lem7238140 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238141 (_96885 : int) (_96886 : int) : (term451 _96886 _96885) = (term452 _96885 _96886).
Proof. exact (MK_COMB (@lem7238140) (@lem7238139 _96885 _96886)). Qed.
Lemma lem7238142 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238143 (_96885 : int) (_96886 : int) : (term433 _96886 _96885) = (term453 _96885 _96886).
Proof. exact (MK_COMB (@lem7238141 _96885 _96886) (@lem7238142)). Qed.
Lemma lem7238144 (_96885 : int) (_96886 : int) : (term350 _96885 _96886) = (term453 _96885 _96886).
Proof. exact (TRANS (@lem7238074 _96886 _96885) (@lem7238143 _96885 _96886)). Qed.
Lemma lem7238145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238146 (_96884 : int) (_96886 : int) : (term362 _96886 _96884) = (term493 _96884 _96886).
Proof. exact (MK_COMB (@lem7238145) (@lem7238073 _96884 _96886)). Qed.
Lemma lem7238147 (_96884 : int) (_96885 : int) (_96886 : int) : (term363 _96884 _96885 _96886) = (term494 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238146 _96884 _96886) (@lem7238144 _96885 _96886)). Qed.
Lemma lem7238148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238149 (_96883 : int) (_96884 : int) (_96886 : int) : (term364 _96883 _96884 _96886) = (term495 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7238148) (@lem7237893 _96883 _96884 _96886)). Qed.
Lemma lem7238150 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term365 _96883 _96884 _96885 _96886) = (term496 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238149 _96883 _96884 _96886) (@lem7238147 _96884 _96885 _96886)). Qed.
Lemma lem7238151 (_96886 : int) (_96883 : int) : (term323 _96883 _96886) = (term422 _96886 _96883).
Proof. exact (@lem1988287 (real_of_int _96886) (real_of_int _96883)). Qed.
Lemma lem7238157 (_96886 : int) (_96883 : int) : (term423 _96886 _96883) = (term424 _96886 _96883).
Proof. exact (@lem1982792 (real_of_int _96886) (real_of_int _96883)). Qed.
Lemma lem7238162 (_96883 : int) (_96886 : int) : (term424 _96886 _96883) = (term425 _96883 _96886).
Proof. exact (@lem1982761 (term418 _96883) (real_of_int _96886)). Qed.
Lemma lem7238164 (_96883 : int) (_96886 : int) : (term423 _96886 _96883) = (term425 _96883 _96886).
Proof. exact (TRANS (@lem7238157 _96886 _96883) (@lem7238162 _96883 _96886)). Qed.
Lemma lem7238165 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238166 (_96883 : int) (_96886 : int) : (term426 _96886 _96883) = (term427 _96883 _96886).
Proof. exact (MK_COMB (@lem7238165) (@lem7238164 _96883 _96886)). Qed.
Lemma lem7238167 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238168 (_96883 : int) (_96886 : int) : (term422 _96886 _96883) = (term428 _96883 _96886).
Proof. exact (MK_COMB (@lem7238166 _96883 _96886) (@lem7238167)). Qed.
Lemma lem7238169 (_96883 : int) (_96886 : int) : (term323 _96883 _96886) = (term428 _96883 _96886).
Proof. exact (TRANS (@lem7238151 _96886 _96883) (@lem7238168 _96883 _96886)). Qed.
Lemma lem7238170 (_96885 : int) (_96886 : int) : (term323 _96886 _96885) = (term422 _96885 _96886).
Proof. exact (@lem1988287 (real_of_int _96885) (real_of_int _96886)). Qed.
Lemma lem7238183 (_96885 : int) (_96886 : int) : (term423 _96885 _96886) = (term424 _96885 _96886).
Proof. exact (@lem1982792 (real_of_int _96885) (real_of_int _96886)). Qed.
Lemma lem7238184 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238185 (_96885 : int) (_96886 : int) : (term426 _96885 _96886) = (term429 _96885 _96886).
Proof. exact (MK_COMB (@lem7238184) (@lem7238183 _96885 _96886)). Qed.
Lemma lem7238186 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238187 (_96885 : int) (_96886 : int) : (term422 _96885 _96886) = (term430 _96885 _96886).
Proof. exact (MK_COMB (@lem7238185 _96885 _96886) (@lem7238186)). Qed.
Lemma lem7238188 (_96885 : int) (_96886 : int) : (term323 _96886 _96885) = (term430 _96885 _96886).
Proof. exact (TRANS (@lem7238170 _96885 _96886) (@lem7238187 _96885 _96886)). Qed.
Lemma lem7238189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238190 (_96883 : int) (_96886 : int) : (term345 _96883 _96886) = (term431 _96883 _96886).
Proof. exact (MK_COMB (@lem7238189) (@lem7238169 _96883 _96886)). Qed.
Lemma lem7238191 (_96883 : int) (_96885 : int) (_96886 : int) : (term346 _96883 _96886 _96885) = (term432 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238190 _96883 _96886) (@lem7238188 _96885 _96886)). Qed.
Lemma lem7238192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238193 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term366 _96883 _96884 _96885 _96886) = (term497 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238192) (@lem7238150 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238194 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term367 _96884 _96883 _96886 _96885) = (term498 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238193 _96883 _96884 _96885 _96886) (@lem7238191 _96883 _96885 _96886)). Qed.
Lemma lem7238195 (_96886 : int) (_96883 : int) : (term323 _96883 _96886) = (term422 _96886 _96883).
Proof. exact (@lem1988287 (real_of_int _96886) (real_of_int _96883)). Qed.
Lemma lem7238201 (_96886 : int) (_96883 : int) : (term423 _96886 _96883) = (term424 _96886 _96883).
Proof. exact (@lem1982792 (real_of_int _96886) (real_of_int _96883)). Qed.
Lemma lem7238206 (_96883 : int) (_96886 : int) : (term424 _96886 _96883) = (term425 _96883 _96886).
Proof. exact (@lem1982761 (term418 _96883) (real_of_int _96886)). Qed.
Lemma lem7238208 (_96883 : int) (_96886 : int) : (term423 _96886 _96883) = (term425 _96883 _96886).
Proof. exact (TRANS (@lem7238201 _96886 _96883) (@lem7238206 _96883 _96886)). Qed.
Lemma lem7238209 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238210 (_96883 : int) (_96886 : int) : (term426 _96886 _96883) = (term427 _96883 _96886).
Proof. exact (MK_COMB (@lem7238209) (@lem7238208 _96883 _96886)). Qed.
Lemma lem7238211 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238212 (_96883 : int) (_96886 : int) : (term422 _96886 _96883) = (term428 _96883 _96886).
Proof. exact (MK_COMB (@lem7238210 _96883 _96886) (@lem7238211)). Qed.
Lemma lem7238213 (_96883 : int) (_96886 : int) : (term323 _96883 _96886) = (term428 _96883 _96886).
Proof. exact (TRANS (@lem7238195 _96886 _96883) (@lem7238212 _96883 _96886)). Qed.
Lemma lem7238214 (_96884 : int) (_96886 : int) : (term323 _96886 _96884) = (term422 _96884 _96886).
Proof. exact (@lem1988287 (real_of_int _96884) (real_of_int _96886)). Qed.
Lemma lem7238227 (_96884 : int) (_96886 : int) : (term423 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982792 (real_of_int _96884) (real_of_int _96886)). Qed.
Lemma lem7238228 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238229 (_96884 : int) (_96886 : int) : (term426 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7238228) (@lem7238227 _96884 _96886)). Qed.
Lemma lem7238230 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238231 (_96884 : int) (_96886 : int) : (term422 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7238229 _96884 _96886) (@lem7238230)). Qed.
Lemma lem7238232 (_96884 : int) (_96886 : int) : (term323 _96886 _96884) = (term430 _96884 _96886).
Proof. exact (TRANS (@lem7238214 _96884 _96886) (@lem7238231 _96884 _96886)). Qed.
Lemma lem7238233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238234 (_96883 : int) (_96886 : int) : (term345 _96883 _96886) = (term431 _96883 _96886).
Proof. exact (MK_COMB (@lem7238233) (@lem7238213 _96883 _96886)). Qed.
Lemma lem7238235 (_96883 : int) (_96884 : int) (_96886 : int) : (term346 _96883 _96886 _96884) = (term432 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7238234 _96883 _96886) (@lem7238232 _96884 _96886)). Qed.
Lemma lem7238236 (_96886 : int) (_96884 : int) : (term350 _96884 _96886) = (term433 _96886 _96884).
Proof. exact (@lem1988287 (real_of_int _96886) (term342 _96884)). Qed.
Lemma lem7238248 (_96886 : int) (_96884 : int) : (term434 _96886 _96884) = (term435 _96886 _96884).
Proof. exact (@lem1982792 (real_of_int _96886) (term342 _96884)). Qed.
Lemma lem7238249 (_96884 : int) : (term436 _96884) = (term437 _96884).
Proof. exact (@lem1982781 (real_of_int _96884) term393 term340). Qed.
Lemma lem7238251 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7238252 : term340 = term438.
Proof. exact (@lem7238251 term189). Qed.
Lemma lem7238254 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7238255 : term393 = term394.
Proof. exact (@lem7238254 term189). Qed.
Lemma lem7238256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7238257 : term395 = term396.
Proof. exact (MK_COMB (@lem7238256) (@lem7238255)). Qed.
Lemma lem7238258 : term439 = term440.
Proof. exact (MK_COMB (@lem7238257) (@lem7238252)). Qed.
Lemma lem7238259 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7238261 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7238262 : term402 = term403.
Proof. exact (@lem7238261 term189 term189). Qed.
Lemma lem7238263 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238264 : term405 = term189.
Proof. exact (EQ_MP (@lem7238263) (@lem940073)). Qed.
Lemma lem7238265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238266 : term403 = term340.
Proof. exact (MK_COMB (@lem7238265) (@lem7238264)). Qed.
Lemma lem7238267 : term402 = term340.
Proof. exact (TRANS (@lem7238262) (@lem7238266)). Qed.
Lemma lem7238269 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7238270 : term439 = term444.
Proof. exact (@lem7238269 term189 term189). Qed.
Lemma lem7238271 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238272 : term405 = term189.
Proof. exact (EQ_MP (@lem7238271) (@lem940073)). Qed.
Lemma lem7238273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238274 : term403 = term340.
Proof. exact (MK_COMB (@lem7238273) (@lem7238272)). Qed.
Lemma lem7238275 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7238276 : term444 = term393.
Proof. exact (MK_COMB (@lem7238275) (@lem7238274)). Qed.
Lemma lem7238277 : term439 = term393.
Proof. exact (TRANS (@lem7238270) (@lem7238276)). Qed.
Lemma lem7238278 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7238279 : term445 = term446.
Proof. exact (MK_COMB (@lem7238278) (@lem7238277)). Qed.
Lemma lem7238280 : term441 = term394.
Proof. exact (MK_COMB (@lem7238279) (@lem7238267)). Qed.
Lemma lem7238281 : term440 = term394.
Proof. exact (TRANS (@lem7238259) (@lem7238280)). Qed.
Lemma lem7238282 : term439 = term394.
Proof. exact (TRANS (@lem7238258) (@lem7238281)). Qed.
Lemma lem7238284 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7238285 : term394 = term393.
Proof. exact (@lem7238284 term393). Qed.
Lemma lem7238286 : term439 = term393.
Proof. exact (TRANS (@lem7238282) (@lem7238285)). Qed.
Lemma lem7238289 (_96884 : int) : (term447 _96884) = (term447 _96884).
Proof. exact (eq_refl (term447 _96884)). Qed.
Lemma lem7238290 (_96884 : int) : (term437 _96884) = (term448 _96884).
Proof. exact (MK_COMB (@lem7238289 _96884) (@lem7238286)). Qed.
Lemma lem7238291 (_96884 : int) : (term436 _96884) = (term448 _96884).
Proof. exact (TRANS (@lem7238249 _96884) (@lem7238290 _96884)). Qed.
Lemma lem7238292 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7238293 (_96886 : int) (_96884 : int) : (term435 _96886 _96884) = (term449 _96886 _96884).
Proof. exact (MK_COMB (@lem7238292 _96886) (@lem7238291 _96884)). Qed.
Lemma lem7238298 (_96884 : int) (_96886 : int) : (term449 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (@lem1982757 (term418 _96884) (real_of_int _96886) term393). Qed.
Lemma lem7238299 (_96884 : int) (_96886 : int) : (term435 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7238293 _96886 _96884) (@lem7238298 _96884 _96886)). Qed.
Lemma lem7238301 (_96884 : int) (_96886 : int) : (term434 _96886 _96884) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7238248 _96886 _96884) (@lem7238299 _96884 _96886)). Qed.
Lemma lem7238302 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238303 (_96884 : int) (_96886 : int) : (term451 _96886 _96884) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7238302) (@lem7238301 _96884 _96886)). Qed.
Lemma lem7238304 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238305 (_96884 : int) (_96886 : int) : (term433 _96886 _96884) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7238303 _96884 _96886) (@lem7238304)). Qed.
Lemma lem7238306 (_96884 : int) (_96886 : int) : (term350 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (TRANS (@lem7238236 _96886 _96884) (@lem7238305 _96884 _96886)). Qed.
Lemma lem7238307 (_96885 : int) (_96886 : int) : (term323 _96886 _96885) = (term422 _96885 _96886).
Proof. exact (@lem1988287 (real_of_int _96885) (real_of_int _96886)). Qed.
Lemma lem7238320 (_96885 : int) (_96886 : int) : (term423 _96885 _96886) = (term424 _96885 _96886).
Proof. exact (@lem1982792 (real_of_int _96885) (real_of_int _96886)). Qed.
Lemma lem7238321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238322 (_96885 : int) (_96886 : int) : (term426 _96885 _96886) = (term429 _96885 _96886).
Proof. exact (MK_COMB (@lem7238321) (@lem7238320 _96885 _96886)). Qed.
Lemma lem7238323 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238324 (_96885 : int) (_96886 : int) : (term422 _96885 _96886) = (term430 _96885 _96886).
Proof. exact (MK_COMB (@lem7238322 _96885 _96886) (@lem7238323)). Qed.
Lemma lem7238325 (_96885 : int) (_96886 : int) : (term323 _96886 _96885) = (term430 _96885 _96886).
Proof. exact (TRANS (@lem7238307 _96885 _96886) (@lem7238324 _96885 _96886)). Qed.
Lemma lem7238326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238327 (_96884 : int) (_96886 : int) : (term351 _96884 _96886) = (term454 _96884 _96886).
Proof. exact (MK_COMB (@lem7238326) (@lem7238306 _96884 _96886)). Qed.
Lemma lem7238328 (_96884 : int) (_96885 : int) (_96886 : int) : (term352 _96884 _96886 _96885) = (term455 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238327 _96884 _96886) (@lem7238325 _96885 _96886)). Qed.
Lemma lem7238329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238330 (_96883 : int) (_96884 : int) (_96886 : int) : (term368 _96883 _96886 _96884) = (term499 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7238329) (@lem7238235 _96883 _96884 _96886)). Qed.
Lemma lem7238331 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term369 _96883 _96884 _96886 _96885) = (term500 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238330 _96883 _96884 _96886) (@lem7238328 _96884 _96885 _96886)). Qed.
Lemma lem7238332 (_96883 : int) (_96886 : int) : (term350 _96886 _96883) = (term433 _96883 _96886).
Proof. exact (@lem1988287 (real_of_int _96883) (term342 _96886)). Qed.
Lemma lem7238344 (_96883 : int) (_96886 : int) : (term434 _96883 _96886) = (term435 _96883 _96886).
Proof. exact (@lem1982792 (real_of_int _96883) (term342 _96886)). Qed.
Lemma lem7238345 (_96886 : int) : (term436 _96886) = (term437 _96886).
Proof. exact (@lem1982781 (real_of_int _96886) term393 term340). Qed.
Lemma lem7238347 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7238348 : term340 = term438.
Proof. exact (@lem7238347 term189). Qed.
Lemma lem7238350 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7238351 : term393 = term394.
Proof. exact (@lem7238350 term189). Qed.
Lemma lem7238352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7238353 : term395 = term396.
Proof. exact (MK_COMB (@lem7238352) (@lem7238351)). Qed.
Lemma lem7238354 : term439 = term440.
Proof. exact (MK_COMB (@lem7238353) (@lem7238348)). Qed.
Lemma lem7238355 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7238357 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7238358 : term402 = term403.
Proof. exact (@lem7238357 term189 term189). Qed.
Lemma lem7238359 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238360 : term405 = term189.
Proof. exact (EQ_MP (@lem7238359) (@lem940073)). Qed.
Lemma lem7238361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238362 : term403 = term340.
Proof. exact (MK_COMB (@lem7238361) (@lem7238360)). Qed.
Lemma lem7238363 : term402 = term340.
Proof. exact (TRANS (@lem7238358) (@lem7238362)). Qed.
Lemma lem7238365 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7238366 : term439 = term444.
Proof. exact (@lem7238365 term189 term189). Qed.
Lemma lem7238367 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238368 : term405 = term189.
Proof. exact (EQ_MP (@lem7238367) (@lem940073)). Qed.
Lemma lem7238369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238370 : term403 = term340.
Proof. exact (MK_COMB (@lem7238369) (@lem7238368)). Qed.
Lemma lem7238371 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7238372 : term444 = term393.
Proof. exact (MK_COMB (@lem7238371) (@lem7238370)). Qed.
Lemma lem7238373 : term439 = term393.
Proof. exact (TRANS (@lem7238366) (@lem7238372)). Qed.
Lemma lem7238374 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7238375 : term445 = term446.
Proof. exact (MK_COMB (@lem7238374) (@lem7238373)). Qed.
Lemma lem7238376 : term441 = term394.
Proof. exact (MK_COMB (@lem7238375) (@lem7238363)). Qed.
Lemma lem7238377 : term440 = term394.
Proof. exact (TRANS (@lem7238355) (@lem7238376)). Qed.
Lemma lem7238378 : term439 = term394.
Proof. exact (TRANS (@lem7238354) (@lem7238377)). Qed.
Lemma lem7238380 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7238381 : term394 = term393.
Proof. exact (@lem7238380 term393). Qed.
Lemma lem7238382 : term439 = term393.
Proof. exact (TRANS (@lem7238378) (@lem7238381)). Qed.
Lemma lem7238385 (_96886 : int) : (term447 _96886) = (term447 _96886).
Proof. exact (eq_refl (term447 _96886)). Qed.
Lemma lem7238386 (_96886 : int) : (term437 _96886) = (term448 _96886).
Proof. exact (MK_COMB (@lem7238385 _96886) (@lem7238382)). Qed.
Lemma lem7238387 (_96886 : int) : (term436 _96886) = (term448 _96886).
Proof. exact (TRANS (@lem7238345 _96886) (@lem7238386 _96886)). Qed.
Lemma lem7238388 (_96883 : int) : (term341 _96883) = (term341 _96883).
Proof. exact (eq_refl (term341 _96883)). Qed.
Lemma lem7238391 (_96883 : int) (_96886 : int) : (term435 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (MK_COMB (@lem7238388 _96883) (@lem7238387 _96886)). Qed.
Lemma lem7238393 (_96883 : int) (_96886 : int) : (term434 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (TRANS (@lem7238344 _96883 _96886) (@lem7238391 _96883 _96886)). Qed.
Lemma lem7238394 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238395 (_96883 : int) (_96886 : int) : (term451 _96883 _96886) = (term458 _96883 _96886).
Proof. exact (MK_COMB (@lem7238394) (@lem7238393 _96883 _96886)). Qed.
Lemma lem7238396 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238397 (_96883 : int) (_96886 : int) : (term433 _96883 _96886) = (term459 _96883 _96886).
Proof. exact (MK_COMB (@lem7238395 _96883 _96886) (@lem7238396)). Qed.
Lemma lem7238398 (_96883 : int) (_96886 : int) : (term350 _96886 _96883) = (term459 _96883 _96886).
Proof. exact (TRANS (@lem7238332 _96883 _96886) (@lem7238397 _96883 _96886)). Qed.
Lemma lem7238399 (_96886 : int) (_96885 : int) : (term350 _96885 _96886) = (term433 _96886 _96885).
Proof. exact (@lem1988287 (real_of_int _96886) (term342 _96885)). Qed.
Lemma lem7238411 (_96886 : int) (_96885 : int) : (term434 _96886 _96885) = (term435 _96886 _96885).
Proof. exact (@lem1982792 (real_of_int _96886) (term342 _96885)). Qed.
Lemma lem7238412 (_96885 : int) : (term436 _96885) = (term437 _96885).
Proof. exact (@lem1982781 (real_of_int _96885) term393 term340). Qed.
Lemma lem7238414 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7238415 : term340 = term438.
Proof. exact (@lem7238414 term189). Qed.
Lemma lem7238417 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7238418 : term393 = term394.
Proof. exact (@lem7238417 term189). Qed.
Lemma lem7238419 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7238420 : term395 = term396.
Proof. exact (MK_COMB (@lem7238419) (@lem7238418)). Qed.
Lemma lem7238421 : term439 = term440.
Proof. exact (MK_COMB (@lem7238420) (@lem7238415)). Qed.
Lemma lem7238422 : term440 = term441.
Proof. exact (@lem1981613 term393 term340 term340 term340). Qed.
Lemma lem7238424 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7238425 : term402 = term403.
Proof. exact (@lem7238424 term189 term189). Qed.
Lemma lem7238426 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238427 : term405 = term189.
Proof. exact (EQ_MP (@lem7238426) (@lem940073)). Qed.
Lemma lem7238428 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238429 : term403 = term340.
Proof. exact (MK_COMB (@lem7238428) (@lem7238427)). Qed.
Lemma lem7238430 : term402 = term340.
Proof. exact (TRANS (@lem7238425) (@lem7238429)). Qed.
Lemma lem7238432 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7238433 : term439 = term444.
Proof. exact (@lem7238432 term189 term189). Qed.
Lemma lem7238434 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7238435 : term405 = term189.
Proof. exact (EQ_MP (@lem7238434) (@lem940073)). Qed.
Lemma lem7238436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7238437 : term403 = term340.
Proof. exact (MK_COMB (@lem7238436) (@lem7238435)). Qed.
Lemma lem7238438 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7238439 : term444 = term393.
Proof. exact (MK_COMB (@lem7238438) (@lem7238437)). Qed.
Lemma lem7238440 : term439 = term393.
Proof. exact (TRANS (@lem7238433) (@lem7238439)). Qed.
Lemma lem7238441 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7238442 : term445 = term446.
Proof. exact (MK_COMB (@lem7238441) (@lem7238440)). Qed.
Lemma lem7238443 : term441 = term394.
Proof. exact (MK_COMB (@lem7238442) (@lem7238430)). Qed.
Lemma lem7238444 : term440 = term394.
Proof. exact (TRANS (@lem7238422) (@lem7238443)). Qed.
Lemma lem7238445 : term439 = term394.
Proof. exact (TRANS (@lem7238421) (@lem7238444)). Qed.
Lemma lem7238447 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7238448 : term394 = term393.
Proof. exact (@lem7238447 term393). Qed.
Lemma lem7238449 : term439 = term393.
Proof. exact (TRANS (@lem7238445) (@lem7238448)). Qed.
Lemma lem7238452 (_96885 : int) : (term447 _96885) = (term447 _96885).
Proof. exact (eq_refl (term447 _96885)). Qed.
Lemma lem7238453 (_96885 : int) : (term437 _96885) = (term448 _96885).
Proof. exact (MK_COMB (@lem7238452 _96885) (@lem7238449)). Qed.
Lemma lem7238454 (_96885 : int) : (term436 _96885) = (term448 _96885).
Proof. exact (TRANS (@lem7238412 _96885) (@lem7238453 _96885)). Qed.
Lemma lem7238455 (_96886 : int) : (term341 _96886) = (term341 _96886).
Proof. exact (eq_refl (term341 _96886)). Qed.
Lemma lem7238456 (_96886 : int) (_96885 : int) : (term435 _96886 _96885) = (term449 _96886 _96885).
Proof. exact (MK_COMB (@lem7238455 _96886) (@lem7238454 _96885)). Qed.
Lemma lem7238461 (_96885 : int) (_96886 : int) : (term449 _96886 _96885) = (term450 _96885 _96886).
Proof. exact (@lem1982757 (term418 _96885) (real_of_int _96886) term393). Qed.
Lemma lem7238462 (_96885 : int) (_96886 : int) : (term435 _96886 _96885) = (term450 _96885 _96886).
Proof. exact (TRANS (@lem7238456 _96886 _96885) (@lem7238461 _96885 _96886)). Qed.
Lemma lem7238464 (_96885 : int) (_96886 : int) : (term434 _96886 _96885) = (term450 _96885 _96886).
Proof. exact (TRANS (@lem7238411 _96886 _96885) (@lem7238462 _96885 _96886)). Qed.
Lemma lem7238465 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7238466 (_96885 : int) (_96886 : int) : (term451 _96886 _96885) = (term452 _96885 _96886).
Proof. exact (MK_COMB (@lem7238465) (@lem7238464 _96885 _96886)). Qed.
Lemma lem7238467 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7238468 (_96885 : int) (_96886 : int) : (term433 _96886 _96885) = (term453 _96885 _96886).
Proof. exact (MK_COMB (@lem7238466 _96885 _96886) (@lem7238467)). Qed.
Lemma lem7238469 (_96885 : int) (_96886 : int) : (term350 _96885 _96886) = (term453 _96885 _96886).
Proof. exact (TRANS (@lem7238399 _96886 _96885) (@lem7238468 _96885 _96886)). Qed.
Lemma lem7238470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238471 (_96883 : int) (_96886 : int) : (term356 _96886 _96883) = (term460 _96883 _96886).
Proof. exact (MK_COMB (@lem7238470) (@lem7238398 _96883 _96886)). Qed.
Lemma lem7238472 (_96883 : int) (_96885 : int) (_96886 : int) : (term357 _96883 _96885 _96886) = (term461 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238471 _96883 _96886) (@lem7238469 _96885 _96886)). Qed.
Lemma lem7238473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238474 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term370 _96883 _96884 _96886 _96885) = (term501 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238473) (@lem7238331 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238475 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term371 _96884 _96883 _96885 _96886) = (term502 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238474 _96883 _96884 _96885 _96886) (@lem7238472 _96883 _96885 _96886)). Qed.
Lemma lem7238476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238477 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term372 _96884 _96883 _96886 _96885) = (term503 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238476) (@lem7238194 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238478 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term373 _96884 _96883 _96885 _96886) = (term504 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238477 _96884 _96883 _96885 _96886) (@lem7238475 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238479 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238480 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term374 _96883 _96884 _96886 _96885) = (term505 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238479) (@lem7237752 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238481 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term375 _96884 _96883 _96885 _96886) = (term506 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238480 _96883 _96884 _96885 _96886) (@lem7238478 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238483 (_96884 : int) (_96885 : int) : (term345 _96884 _96885) = (term431 _96884 _96885).
Proof. exact (MK_COMB (@lem7238482) (@lem7237615 _96884 _96885)). Qed.
Lemma lem7238484 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term376 _96884 _96883 _96885 _96886) = (term507 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238483 _96884 _96885) (@lem7238481 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238486 (_96883 : int) (_96884 : int) : (term377 _96883 _96884) = (term508 _96883 _96884).
Proof. exact (MK_COMB (@lem7238485) (@lem7237596 _96883 _96884)). Qed.
Lemma lem7238487 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term378 _96884 _96883 _96885 _96886) = (term509 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238486 _96883 _96884) (@lem7238484 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238489 (_96886 : int) : (term379 _96886) = (term510 _96886).
Proof. exact (MK_COMB (@lem7238488) (@lem7237571 _96886)). Qed.
Lemma lem7238490 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term380 _96884 _96883 _96885 _96886) = (term511 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238489 _96886) (@lem7238487 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238492 (_96885 : int) : (term379 _96885) = (term510 _96885).
Proof. exact (MK_COMB (@lem7238491) (@lem7237523 _96885)). Qed.
Lemma lem7238493 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term381 _96884 _96883 _96885 _96886) = (term512 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238492 _96885) (@lem7238490 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238495 (_96884 : int) : (term379 _96884) = (term510 _96884).
Proof. exact (MK_COMB (@lem7238494) (@lem7237475 _96884)). Qed.
Lemma lem7238496 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term382 _96884 _96883 _96885 _96886) = (term513 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238495 _96884) (@lem7238493 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238498 (_96883 : int) : (term379 _96883) = (term510 _96883).
Proof. exact (MK_COMB (@lem7238497) (@lem7237427 _96883)). Qed.
Lemma lem7238499 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term383 _96884 _96883 _96885 _96886) = (term514 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238498 _96883) (@lem7238496 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238506 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term385 _96884 _96883 _96885 _96886) = (term514 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7237379 _96884 _96883 _96885 _96886) (@lem7238499 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238532 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term502 _96884 _96883 _96885 _96886) = (term515 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term459 _96883 _96886) (term500 _96883 _96884 _96885 _96886) (term453 _96885 _96886)). Qed.
Lemma lem7238539 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term516 _96883 _96884 _96885 _96886) = (term517 _96883 _96884 _96885 _96886).
Proof. exact (@lem19367 (term432 _96883 _96884 _96886) (term455 _96884 _96885 _96886) (term453 _96885 _96886)). Qed.
Lemma lem7238546 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term518 _96884 _96885 _96883 _96886) = (term519 _96884 _96885 _96883 _96886).
Proof. exact (@lem19367 (term432 _96883 _96884 _96886) (term455 _96884 _96885 _96886) (term459 _96883 _96886)). Qed.
Lemma lem7238547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238548 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term520 _96884 _96885 _96883 _96886) = (term521 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238547) (@lem7238546 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238549 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term515 _96883 _96884 _96885 _96886) = (term522 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238548 _96884 _96885 _96883 _96886) (@lem7238539 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238551 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term502 _96884 _96883 _96885 _96886) = (term522 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238532 _96883 _96884 _96885 _96886) (@lem7238549 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238558 (_96883 : int) (_96885 : int) (_96886 : int) : (term432 _96883 _96885 _96886) = (term432 _96883 _96885 _96886).
Proof. exact (eq_refl (term432 _96883 _96885 _96886)). Qed.
Lemma lem7238572 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term496 _96883 _96884 _96885 _96886) = (term523 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term430 _96884 _96886) (term461 _96883 _96884 _96886) (term453 _96885 _96886)). Qed.
Lemma lem7238579 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term524 _96883 _96884 _96885 _96886) = (term525 _96883 _96884 _96885 _96886).
Proof. exact (@lem19367 (term459 _96883 _96886) (term453 _96884 _96886) (term453 _96885 _96886)). Qed.
Lemma lem7238586 (_96883 : int) (_96884 : int) (_96886 : int) : (term526 _96883 _96884 _96886) = (term527 _96883 _96884 _96886).
Proof. exact (@lem19367 (term459 _96883 _96886) (term453 _96884 _96886) (term430 _96884 _96886)). Qed.
Lemma lem7238587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238588 (_96883 : int) (_96884 : int) (_96886 : int) : (term528 _96883 _96884 _96886) = (term529 _96883 _96884 _96886).
Proof. exact (MK_COMB (@lem7238587) (@lem7238586 _96883 _96884 _96886)). Qed.
Lemma lem7238589 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term523 _96883 _96884 _96885 _96886) = (term530 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238588 _96883 _96884 _96886) (@lem7238579 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238591 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term496 _96883 _96884 _96885 _96886) = (term530 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238572 _96883 _96884 _96885 _96886) (@lem7238589 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7238593 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term497 _96883 _96884 _96885 _96886) = (term531 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238592) (@lem7238591 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238594 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term498 _96884 _96883 _96885 _96886) = (term532 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238593 _96883 _96884 _96885 _96886) (@lem7238558 _96883 _96885 _96886)). Qed.
Lemma lem7238595 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term532 _96884 _96883 _96885 _96886) = (term533 _96884 _96883 _96885 _96886).
Proof. exact (@lem19367 (term527 _96883 _96884 _96886) (term525 _96883 _96884 _96885 _96886) (term432 _96883 _96885 _96886)). Qed.
Lemma lem7238602 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term534 _96884 _96883 _96885 _96886) = (term535 _96884 _96883 _96885 _96886).
Proof. exact (@lem19367 (term536 _96883 _96885 _96886) (term537 _96884 _96885 _96886) (term432 _96883 _96885 _96886)). Qed.
Lemma lem7238609 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term538 _96884 _96883 _96885 _96886) = (term539 _96884 _96883 _96885 _96886).
Proof. exact (@lem19367 (term540 _96883 _96884 _96886) (term541 _96884 _96886) (term432 _96883 _96885 _96886)). Qed.
Lemma lem7238610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238611 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term542 _96884 _96883 _96885 _96886) = (term543 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238610) (@lem7238609 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238612 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term533 _96884 _96883 _96885 _96886) = (term544 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238611 _96884 _96883 _96885 _96886) (@lem7238602 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238613 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term532 _96884 _96883 _96885 _96886) = (term544 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238595 _96884 _96883 _96885 _96886) (@lem7238612 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238614 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term498 _96884 _96883 _96885 _96886) = (term544 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238594 _96884 _96883 _96885 _96886) (@lem7238613 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238616 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term503 _96884 _96883 _96885 _96886) = (term545 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238615) (@lem7238614 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238617 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term504 _96884 _96883 _96885 _96886) = (term546 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238616 _96884 _96883 _96885 _96886) (@lem7238551 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238638 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term505 _96883 _96884 _96885 _96886) = (term505 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term505 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238639 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term506 _96884 _96883 _96885 _96886) = (term547 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238638 _96883 _96884 _96885 _96886) (@lem7238617 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238642 (_96884 : int) (_96885 : int) : (term431 _96884 _96885) = (term431 _96884 _96885).
Proof. exact (eq_refl (term431 _96884 _96885)). Qed.
Lemma lem7238643 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term507 _96884 _96883 _96885 _96886) = (term548 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238642 _96884 _96885) (@lem7238639 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238644 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term548 _96883 _96884 _96885 _96886) = (term549 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term457 _96883 _96884 _96885 _96886) (term428 _96884 _96885) (term546 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238645 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term550 _96883 _96884 _96885 _96886) = (term551 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term544 _96884 _96883 _96885 _96886) (term428 _96884 _96885) (term522 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238646 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term552 _96883 _96884 _96885 _96886) = (term553 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term519 _96884 _96885 _96883 _96886) (term428 _96884 _96885) (term517 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238653 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term554 _96883 _96884 _96885 _96886) = (term555 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term556 _96883 _96884 _96885 _96886) (term428 _96884 _96885) (term557 _96884 _96885 _96886)). Qed.
Lemma lem7238660 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term558 _96884 _96885 _96883 _96886) = (term559 _96884 _96885 _96883 _96886).
Proof. exact (@lem19158 (term560 _96884 _96883 _96886) (term428 _96884 _96885) (term561 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238662 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term562 _96884 _96885 _96883 _96886) = (term563 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238661) (@lem7238660 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238663 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term553 _96883 _96884 _96885 _96886) = (term564 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238662 _96884 _96885 _96883 _96886) (@lem7238653 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238664 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term552 _96883 _96884 _96885 _96886) = (term564 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238646 _96883 _96884 _96885 _96886) (@lem7238663 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238665 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term565 _96884 _96883 _96885 _96886) = (term566 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term539 _96884 _96883 _96885 _96886) (term428 _96884 _96885) (term535 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238672 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term567 _96884 _96883 _96885 _96886) = (term568 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term569 _96883 _96885 _96886) (term428 _96884 _96885) (term570 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238679 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term571 _96884 _96883 _96885 _96886) = (term572 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term573 _96884 _96883 _96885 _96886) (term428 _96884 _96885) (term574 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238681 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term575 _96884 _96883 _96885 _96886) = (term576 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238680) (@lem7238679 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238682 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term566 _96884 _96883 _96885 _96886) = (term577 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238681 _96884 _96883 _96885 _96886) (@lem7238672 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238683 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term565 _96884 _96883 _96885 _96886) = (term577 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238665 _96884 _96883 _96885 _96886) (@lem7238682 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238685 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term578 _96884 _96883 _96885 _96886) = (term579 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238684) (@lem7238683 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238686 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term551 _96883 _96884 _96885 _96886) = (term580 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238685 _96884 _96883 _96885 _96886) (@lem7238664 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238687 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term550 _96883 _96884 _96885 _96886) = (term580 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238645 _96883 _96884 _96885 _96886) (@lem7238686 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238690 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term581 _96883 _96884 _96885 _96886) = (term581 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term581 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238691 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term549 _96883 _96884 _96885 _96886) = (term582 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238690 _96883 _96884 _96885 _96886) (@lem7238687 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238692 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term548 _96883 _96884 _96885 _96886) = (term582 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238644 _96883 _96884 _96885 _96886) (@lem7238691 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238693 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term507 _96884 _96883 _96885 _96886) = (term582 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238643 _96883 _96884 _96885 _96886) (@lem7238692 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238696 (_96883 : int) (_96884 : int) : (term508 _96883 _96884) = (term508 _96883 _96884).
Proof. exact (eq_refl (term508 _96883 _96884)). Qed.
Lemma lem7238697 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term509 _96884 _96883 _96885 _96886) = (term583 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238696 _96883 _96884) (@lem7238693 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238698 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term583 _96883 _96884 _96885 _96886) = (term584 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term585 _96883 _96884 _96885 _96886) (term421 _96883 _96884) (term580 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238699 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term586 _96883 _96884 _96885 _96886) = (term587 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term577 _96884 _96883 _96885 _96886) (term421 _96883 _96884) (term564 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238700 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term588 _96883 _96884 _96885 _96886) = (term589 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term559 _96884 _96885 _96883 _96886) (term421 _96883 _96884) (term555 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238707 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term590 _96883 _96884 _96885 _96886) = (term591 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term592 _96883 _96884 _96885 _96886) (term421 _96883 _96884) (term593 _96884 _96885 _96886)). Qed.
Lemma lem7238714 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term594 _96884 _96885 _96883 _96886) = (term595 _96884 _96885 _96883 _96886).
Proof. exact (@lem19158 (term596 _96885 _96884 _96883 _96886) (term421 _96883 _96884) (term597 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238716 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term598 _96884 _96885 _96883 _96886) = (term599 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238715) (@lem7238714 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238717 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term589 _96883 _96884 _96885 _96886) = (term600 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238716 _96884 _96885 _96883 _96886) (@lem7238707 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238718 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term588 _96883 _96884 _96885 _96886) = (term600 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238700 _96883 _96884 _96885 _96886) (@lem7238717 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238719 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term601 _96884 _96883 _96885 _96886) = (term602 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term572 _96884 _96883 _96885 _96886) (term421 _96883 _96884) (term568 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238726 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term603 _96884 _96883 _96885 _96886) = (term604 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term605 _96884 _96883 _96885 _96886) (term421 _96883 _96884) (term606 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238733 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term607 _96884 _96883 _96885 _96886) = (term608 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term609 _96884 _96883 _96885 _96886) (term421 _96883 _96884) (term610 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238735 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term611 _96884 _96883 _96885 _96886) = (term612 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238734) (@lem7238733 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238736 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term602 _96884 _96883 _96885 _96886) = (term613 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238735 _96884 _96883 _96885 _96886) (@lem7238726 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238737 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term601 _96884 _96883 _96885 _96886) = (term613 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238719 _96884 _96883 _96885 _96886) (@lem7238736 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238739 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term614 _96884 _96883 _96885 _96886) = (term615 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238738) (@lem7238737 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238740 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term587 _96883 _96884 _96885 _96886) = (term616 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238739 _96884 _96883 _96885 _96886) (@lem7238718 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238741 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term586 _96883 _96884 _96885 _96886) = (term616 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238699 _96883 _96884 _96885 _96886) (@lem7238740 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238744 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term617 _96883 _96884 _96885 _96886) = (term617 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term617 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238745 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term584 _96883 _96884 _96885 _96886) = (term618 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238744 _96883 _96884 _96885 _96886) (@lem7238741 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238746 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term583 _96883 _96884 _96885 _96886) = (term618 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238698 _96883 _96884 _96885 _96886) (@lem7238745 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238747 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term509 _96884 _96883 _96885 _96886) = (term618 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238697 _96883 _96884 _96885 _96886) (@lem7238746 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238750 (_96886 : int) : (term510 _96886) = (term510 _96886).
Proof. exact (eq_refl (term510 _96886)). Qed.
Lemma lem7238751 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term511 _96884 _96883 _96885 _96886) = (term619 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238750 _96886) (@lem7238747 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238752 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term619 _96883 _96884 _96885 _96886) = (term620 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term621 _96883 _96884 _96885 _96886) (term413 _96886) (term616 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238753 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term622 _96883 _96884 _96885 _96886) = (term623 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term613 _96884 _96883 _96885 _96886) (term413 _96886) (term600 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238754 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term624 _96883 _96884 _96885 _96886) = (term625 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term595 _96884 _96885 _96883 _96886) (term413 _96886) (term591 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238761 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term626 _96883 _96884 _96885 _96886) = (term627 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term628 _96883 _96884 _96885 _96886) (term413 _96886) (term629 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238768 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term630 _96884 _96885 _96883 _96886) = (term631 _96884 _96885 _96883 _96886).
Proof. exact (@lem19158 (term632 _96885 _96884 _96883 _96886) (term413 _96886) (term633 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238770 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term634 _96884 _96885 _96883 _96886) = (term635 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238769) (@lem7238768 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238771 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term625 _96883 _96884 _96885 _96886) = (term636 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238770 _96884 _96885 _96883 _96886) (@lem7238761 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238772 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term624 _96883 _96884 _96885 _96886) = (term636 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238754 _96883 _96884 _96885 _96886) (@lem7238771 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238773 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term637 _96884 _96883 _96885 _96886) = (term638 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term608 _96884 _96883 _96885 _96886) (term413 _96886) (term604 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238780 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term639 _96884 _96883 _96885 _96886) = (term640 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term641 _96884 _96883 _96885 _96886) (term413 _96886) (term642 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238787 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term643 _96884 _96883 _96885 _96886) = (term644 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term645 _96884 _96883 _96885 _96886) (term413 _96886) (term646 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238789 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term647 _96884 _96883 _96885 _96886) = (term648 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238788) (@lem7238787 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238790 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term638 _96884 _96883 _96885 _96886) = (term649 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238789 _96884 _96883 _96885 _96886) (@lem7238780 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238791 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term637 _96884 _96883 _96885 _96886) = (term649 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238773 _96884 _96883 _96885 _96886) (@lem7238790 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238793 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term650 _96884 _96883 _96885 _96886) = (term651 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238792) (@lem7238791 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238794 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term623 _96883 _96884 _96885 _96886) = (term652 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238793 _96884 _96883 _96885 _96886) (@lem7238772 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238795 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term622 _96883 _96884 _96885 _96886) = (term652 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238753 _96883 _96884 _96885 _96886) (@lem7238794 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238798 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term653 _96883 _96884 _96885 _96886) = (term653 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term653 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238799 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term620 _96883 _96884 _96885 _96886) = (term654 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238798 _96883 _96884 _96885 _96886) (@lem7238795 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238800 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term619 _96883 _96884 _96885 _96886) = (term654 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238752 _96883 _96884 _96885 _96886) (@lem7238799 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238801 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term511 _96884 _96883 _96885 _96886) = (term654 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238751 _96883 _96884 _96885 _96886) (@lem7238800 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238804 (_96885 : int) : (term510 _96885) = (term510 _96885).
Proof. exact (eq_refl (term510 _96885)). Qed.
Lemma lem7238805 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term512 _96884 _96883 _96885 _96886) = (term655 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238804 _96885) (@lem7238801 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238806 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term655 _96883 _96884 _96885 _96886) = (term656 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term657 _96883 _96884 _96885 _96886) (term413 _96885) (term652 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238807 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term658 _96883 _96884 _96885 _96886) = (term659 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term649 _96884 _96883 _96885 _96886) (term413 _96885) (term636 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238808 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term660 _96883 _96884 _96885 _96886) = (term661 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term631 _96884 _96885 _96883 _96886) (term413 _96885) (term627 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238815 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term662 _96883 _96884 _96885 _96886) = (term663 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term664 _96883 _96884 _96885 _96886) (term413 _96885) (term665 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238822 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term666 _96884 _96885 _96883 _96886) = (term667 _96884 _96885 _96883 _96886).
Proof. exact (@lem19158 (term668 _96885 _96884 _96883 _96886) (term413 _96885) (term669 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238824 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term670 _96884 _96885 _96883 _96886) = (term671 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238823) (@lem7238822 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238825 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term661 _96883 _96884 _96885 _96886) = (term672 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238824 _96884 _96885 _96883 _96886) (@lem7238815 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238826 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term660 _96883 _96884 _96885 _96886) = (term672 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238808 _96883 _96884 _96885 _96886) (@lem7238825 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238827 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term673 _96884 _96883 _96885 _96886) = (term674 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term644 _96884 _96883 _96885 _96886) (term413 _96885) (term640 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238834 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term675 _96884 _96883 _96885 _96886) = (term676 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term677 _96884 _96883 _96885 _96886) (term413 _96885) (term678 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238841 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term679 _96884 _96883 _96885 _96886) = (term680 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term681 _96884 _96883 _96885 _96886) (term413 _96885) (term682 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238843 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term683 _96884 _96883 _96885 _96886) = (term684 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238842) (@lem7238841 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238844 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term674 _96884 _96883 _96885 _96886) = (term685 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238843 _96884 _96883 _96885 _96886) (@lem7238834 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238845 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term673 _96884 _96883 _96885 _96886) = (term685 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238827 _96884 _96883 _96885 _96886) (@lem7238844 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238847 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term686 _96884 _96883 _96885 _96886) = (term687 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238846) (@lem7238845 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238848 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term659 _96883 _96884 _96885 _96886) = (term688 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238847 _96884 _96883 _96885 _96886) (@lem7238826 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238849 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term658 _96883 _96884 _96885 _96886) = (term688 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238807 _96883 _96884 _96885 _96886) (@lem7238848 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238852 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term689 _96883 _96884 _96885 _96886) = (term689 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term689 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238853 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term656 _96883 _96884 _96885 _96886) = (term690 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238852 _96883 _96884 _96885 _96886) (@lem7238849 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238854 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term655 _96883 _96884 _96885 _96886) = (term690 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238806 _96883 _96884 _96885 _96886) (@lem7238853 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238855 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term512 _96884 _96883 _96885 _96886) = (term690 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238805 _96883 _96884 _96885 _96886) (@lem7238854 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238858 (_96884 : int) : (term510 _96884) = (term510 _96884).
Proof. exact (eq_refl (term510 _96884)). Qed.
Lemma lem7238859 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term513 _96884 _96883 _96885 _96886) = (term691 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238858 _96884) (@lem7238855 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238860 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term691 _96883 _96884 _96885 _96886) = (term692 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term693 _96883 _96884 _96885 _96886) (term413 _96884) (term688 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238861 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term694 _96883 _96884 _96885 _96886) = (term695 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term685 _96884 _96883 _96885 _96886) (term413 _96884) (term672 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238862 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term696 _96883 _96884 _96885 _96886) = (term697 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term667 _96884 _96885 _96883 _96886) (term413 _96884) (term663 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238869 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term698 _96883 _96884 _96885 _96886) = (term699 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term700 _96883 _96884 _96885 _96886) (term413 _96884) (term701 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238876 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term702 _96884 _96885 _96883 _96886) = (term703 _96884 _96885 _96883 _96886).
Proof. exact (@lem19158 (term704 _96885 _96884 _96883 _96886) (term413 _96884) (term705 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238877 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238878 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term706 _96884 _96885 _96883 _96886) = (term707 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238877) (@lem7238876 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238879 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term697 _96883 _96884 _96885 _96886) = (term708 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238878 _96884 _96885 _96883 _96886) (@lem7238869 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238880 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term696 _96883 _96884 _96885 _96886) = (term708 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238862 _96883 _96884 _96885 _96886) (@lem7238879 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238881 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term709 _96884 _96883 _96885 _96886) = (term710 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term680 _96884 _96883 _96885 _96886) (term413 _96884) (term676 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238888 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term711 _96884 _96883 _96885 _96886) = (term712 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term713 _96884 _96883 _96885 _96886) (term413 _96884) (term714 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238895 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term715 _96884 _96883 _96885 _96886) = (term716 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term717 _96884 _96883 _96885 _96886) (term413 _96884) (term718 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238897 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term719 _96884 _96883 _96885 _96886) = (term720 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238896) (@lem7238895 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238898 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term710 _96884 _96883 _96885 _96886) = (term721 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238897 _96884 _96883 _96885 _96886) (@lem7238888 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238899 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term709 _96884 _96883 _96885 _96886) = (term721 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238881 _96884 _96883 _96885 _96886) (@lem7238898 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238901 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term722 _96884 _96883 _96885 _96886) = (term723 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238900) (@lem7238899 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238902 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term695 _96883 _96884 _96885 _96886) = (term724 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238901 _96884 _96883 _96885 _96886) (@lem7238880 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238903 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term694 _96883 _96884 _96885 _96886) = (term724 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238861 _96883 _96884 _96885 _96886) (@lem7238902 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238906 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term725 _96883 _96884 _96885 _96886) = (term725 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term725 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238907 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term692 _96883 _96884 _96885 _96886) = (term726 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238906 _96883 _96884 _96885 _96886) (@lem7238903 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238908 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term691 _96883 _96884 _96885 _96886) = (term726 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238860 _96883 _96884 _96885 _96886) (@lem7238907 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238909 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term513 _96884 _96883 _96885 _96886) = (term726 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238859 _96883 _96884 _96885 _96886) (@lem7238908 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238912 (_96883 : int) : (term510 _96883) = (term510 _96883).
Proof. exact (eq_refl (term510 _96883)). Qed.
Lemma lem7238913 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term514 _96884 _96883 _96885 _96886) = (term727 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238912 _96883) (@lem7238909 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238914 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term727 _96883 _96884 _96885 _96886) = (term728 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term729 _96883 _96884 _96885 _96886) (term413 _96883) (term724 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238915 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term730 _96883 _96884 _96885 _96886) = (term731 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term721 _96884 _96883 _96885 _96886) (term413 _96883) (term708 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238916 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term732 _96883 _96884 _96885 _96886) = (term733 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term703 _96884 _96885 _96883 _96886) (term413 _96883) (term699 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238923 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term734 _96883 _96884 _96885 _96886) = (term735 _96883 _96884 _96885 _96886).
Proof. exact (@lem19158 (term736 _96883 _96884 _96885 _96886) (term413 _96883) (term737 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238930 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term738 _96884 _96885 _96883 _96886) = (term739 _96884 _96885 _96883 _96886).
Proof. exact (@lem19158 (term740 _96885 _96884 _96883 _96886) (term413 _96883) (term741 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238932 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) : (term742 _96884 _96885 _96883 _96886) = (term743 _96884 _96885 _96883 _96886).
Proof. exact (MK_COMB (@lem7238931) (@lem7238930 _96884 _96885 _96883 _96886)). Qed.
Lemma lem7238933 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term733 _96883 _96884 _96885 _96886) = (term744 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238932 _96884 _96885 _96883 _96886) (@lem7238923 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238934 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term732 _96883 _96884 _96885 _96886) = (term744 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238916 _96883 _96884 _96885 _96886) (@lem7238933 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238935 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term745 _96884 _96883 _96885 _96886) = (term746 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term716 _96884 _96883 _96885 _96886) (term413 _96883) (term712 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238942 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term747 _96884 _96883 _96885 _96886) = (term748 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term749 _96884 _96883 _96885 _96886) (term413 _96883) (term750 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238949 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term751 _96884 _96883 _96885 _96886) = (term752 _96884 _96883 _96885 _96886).
Proof. exact (@lem19158 (term753 _96884 _96883 _96885 _96886) (term413 _96883) (term754 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238951 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term755 _96884 _96883 _96885 _96886) = (term756 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238950) (@lem7238949 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238952 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term746 _96884 _96883 _96885 _96886) = (term757 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238951 _96884 _96883 _96885 _96886) (@lem7238942 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238953 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term745 _96884 _96883 _96885 _96886) = (term757 _96884 _96883 _96885 _96886).
Proof. exact (TRANS (@lem7238935 _96884 _96883 _96885 _96886) (@lem7238952 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7238955 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : (term758 _96884 _96883 _96885 _96886) = (term759 _96884 _96883 _96885 _96886).
Proof. exact (MK_COMB (@lem7238954) (@lem7238953 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7238956 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term731 _96883 _96884 _96885 _96886) = (term760 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238955 _96884 _96883 _96885 _96886) (@lem7238934 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238957 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term730 _96883 _96884 _96885 _96886) = (term760 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238915 _96883 _96884 _96885 _96886) (@lem7238956 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238960 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term761 _96883 _96884 _96885 _96886) = (term761 _96883 _96884 _96885 _96886).
Proof. exact (eq_refl (term761 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238961 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term728 _96883 _96884 _96885 _96886) = (term762 _96883 _96884 _96885 _96886).
Proof. exact (MK_COMB (@lem7238960 _96883 _96884 _96885 _96886) (@lem7238957 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238962 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term727 _96883 _96884 _96885 _96886) = (term762 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238914 _96883 _96884 _96885 _96886) (@lem7238961 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238963 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term514 _96884 _96883 _96885 _96886) = (term762 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238913 _96883 _96884 _96885 _96886) (@lem7238962 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7238964 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) : (term385 _96884 _96883 _96885 _96886) = (term762 _96883 _96884 _96885 _96886).
Proof. exact (TRANS (@lem7238506 _96884 _96883 _96885 _96886) (@lem7238963 _96883 _96884 _96885 _96886)). Qed.
Lemma lem7239016 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term762 _96883 _96884 _96885 _96886) : term762 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239017 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term763 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239018 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term729 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239017 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239020 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term693 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239018 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239022 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term657 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239020 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239024 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term621 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239022 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239026 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term585 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239024 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239028 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term457 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239026 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239030 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term455 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7239028 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239031 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term432 _96883 _96884 _96886.
Proof. exact (proj1 (@lem7239028 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239032 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term430 _96884 _96886.
Proof. exact (proj2 (@lem7239031 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239035 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term453 _96884 _96886.
Proof. exact (proj1 (@lem7239030 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239037 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7239038 : term764 = term476.
Proof. exact (@lem7239037 term328 term340). Qed.
Lemma lem7239040 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239041 : term340 = term438.
Proof. exact (@lem7239040 term189). Qed.
Lemma lem7239043 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239044 : term328 = term390.
Proof. exact (@lem7239043 (NUMERAL 0)). Qed.
Lemma lem7239045 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239046 : term765 = term766.
Proof. exact (MK_COMB (@lem7239045) (@lem7239044)). Qed.
Lemma lem7239047 : term476 = term767.
Proof. exact (MK_COMB (@lem7239046) (@lem7239041)). Qed.
Lemma lem7239048 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7239050 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239051 : term476 = term477.
Proof. exact (@lem7239050 (NUMERAL 0) term189). Qed.
Lemma lem7239052 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239053 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239054 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239053 h1) (fun h1 : term477 = True => @lem7239052)). Qed.
Lemma lem7239055 : term477 = True.
Proof. exact (EQ_MP (@lem7239054) (@lem7239052)). Qed.
Lemma lem7239056 : term476 = True.
Proof. exact (TRANS (@lem7239051) (@lem7239055)). Qed.
Lemma lem7239057 : True = term476.
Proof. exact (SYM (@lem7239056)). Qed.
Lemma lem7239058 : term476.
Proof. exact (EQ_MP (@lem7239057) (@lem0)). Qed.
Lemma lem7239059 : term769.
Proof. exact (@lem7239048 (@lem7239058)). Qed.
Lemma lem7239061 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239062 : term476 = term477.
Proof. exact (@lem7239061 (NUMERAL 0) term189). Qed.
Lemma lem7239063 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239064 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239065 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239064 h1) (fun h1 : term477 = True => @lem7239063)). Qed.
Lemma lem7239066 : term477 = True.
Proof. exact (EQ_MP (@lem7239065) (@lem7239063)). Qed.
Lemma lem7239067 : term476 = True.
Proof. exact (TRANS (@lem7239062) (@lem7239066)). Qed.
Lemma lem7239068 : True = term476.
Proof. exact (SYM (@lem7239067)). Qed.
Lemma lem7239069 : term476.
Proof. exact (EQ_MP (@lem7239068) (@lem0)). Qed.
Lemma lem7239070 : term767 = term770.
Proof. exact (@lem7239059 (@lem7239069)). Qed.
Lemma lem7239072 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239073 : term402 = term403.
Proof. exact (@lem7239072 term189 term189). Qed.
Lemma lem7239074 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239075 : term405 = term189.
Proof. exact (EQ_MP (@lem7239074) (@lem940073)). Qed.
Lemma lem7239076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239077 : term403 = term340.
Proof. exact (MK_COMB (@lem7239076) (@lem7239075)). Qed.
Lemma lem7239078 : term402 = term340.
Proof. exact (TRANS (@lem7239073) (@lem7239077)). Qed.
Lemma lem7239080 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239081 : term488 = term328.
Proof. exact (@lem7239080 term189). Qed.
Lemma lem7239082 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239083 : term771 = term765.
Proof. exact (MK_COMB (@lem7239082) (@lem7239081)). Qed.
Lemma lem7239084 : term770 = term476.
Proof. exact (MK_COMB (@lem7239083) (@lem7239078)). Qed.
Lemma lem7239086 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239087 : term476 = term477.
Proof. exact (@lem7239086 (NUMERAL 0) term189). Qed.
Lemma lem7239088 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239089 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239090 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239089 h1) (fun h1 : term477 = True => @lem7239088)). Qed.
Lemma lem7239091 : term477 = True.
Proof. exact (EQ_MP (@lem7239090) (@lem7239088)). Qed.
Lemma lem7239092 : term476 = True.
Proof. exact (TRANS (@lem7239087) (@lem7239091)). Qed.
Lemma lem7239093 : term770 = True.
Proof. exact (TRANS (@lem7239084) (@lem7239092)). Qed.
Lemma lem7239094 : term767 = True.
Proof. exact (TRANS (@lem7239070) (@lem7239093)). Qed.
Lemma lem7239095 : term476 = True.
Proof. exact (TRANS (@lem7239047) (@lem7239094)). Qed.
Lemma lem7239096 : term764 = True.
Proof. exact (TRANS (@lem7239038) (@lem7239095)). Qed.
Lemma lem7239097 : True = term764.
Proof. exact (SYM (@lem7239096)). Qed.
Lemma lem7239098 : term764.
Proof. exact (EQ_MP (@lem7239097) (@lem0)). Qed.
Lemma lem7239099 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term772 _96884 _96886.
Proof. exact (conj (@lem7239098) (@lem7239032 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239101 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7239102 (_96884 : int) (_96886 : int) : term774 _96884 _96886.
Proof. exact (@lem7239101 term340 (term424 _96884 _96886)). Qed.
Lemma lem7239103 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term775 _96884 _96886.
Proof. exact (@lem7239102 _96884 _96886 (@lem7239099 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239104 (_96884 : int) (_96886 : int) : (term776 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982733 (term424 _96884 _96886)). Qed.
Lemma lem7239105 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7239106 (_96884 : int) (_96886 : int) : (term777 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7239105) (@lem7239104 _96884 _96886)). Qed.
Lemma lem7239107 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7239108 (_96884 : int) (_96886 : int) : (term775 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7239106 _96884 _96886) (@lem7239107)). Qed.
Lemma lem7239109 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term430 _96884 _96886.
Proof. exact (EQ_MP (@lem7239108 _96884 _96886) (@lem7239103 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239111 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7239112 : term764 = term476.
Proof. exact (@lem7239111 term328 term340). Qed.
Lemma lem7239114 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239115 : term340 = term438.
Proof. exact (@lem7239114 term189). Qed.
Lemma lem7239117 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239118 : term328 = term390.
Proof. exact (@lem7239117 (NUMERAL 0)). Qed.
Lemma lem7239119 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239120 : term765 = term766.
Proof. exact (MK_COMB (@lem7239119) (@lem7239118)). Qed.
Lemma lem7239121 : term476 = term767.
Proof. exact (MK_COMB (@lem7239120) (@lem7239115)). Qed.
Lemma lem7239122 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7239124 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239125 : term476 = term477.
Proof. exact (@lem7239124 (NUMERAL 0) term189). Qed.
Lemma lem7239126 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239127 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239128 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239127 h1) (fun h1 : term477 = True => @lem7239126)). Qed.
Lemma lem7239129 : term477 = True.
Proof. exact (EQ_MP (@lem7239128) (@lem7239126)). Qed.
Lemma lem7239130 : term476 = True.
Proof. exact (TRANS (@lem7239125) (@lem7239129)). Qed.
Lemma lem7239131 : True = term476.
Proof. exact (SYM (@lem7239130)). Qed.
Lemma lem7239132 : term476.
Proof. exact (EQ_MP (@lem7239131) (@lem0)). Qed.
Lemma lem7239133 : term769.
Proof. exact (@lem7239122 (@lem7239132)). Qed.
Lemma lem7239135 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239136 : term476 = term477.
Proof. exact (@lem7239135 (NUMERAL 0) term189). Qed.
Lemma lem7239137 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239138 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239139 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239138 h1) (fun h1 : term477 = True => @lem7239137)). Qed.
Lemma lem7239140 : term477 = True.
Proof. exact (EQ_MP (@lem7239139) (@lem7239137)). Qed.
Lemma lem7239141 : term476 = True.
Proof. exact (TRANS (@lem7239136) (@lem7239140)). Qed.
Lemma lem7239142 : True = term476.
Proof. exact (SYM (@lem7239141)). Qed.
Lemma lem7239143 : term476.
Proof. exact (EQ_MP (@lem7239142) (@lem0)). Qed.
Lemma lem7239144 : term767 = term770.
Proof. exact (@lem7239133 (@lem7239143)). Qed.
Lemma lem7239146 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239147 : term402 = term403.
Proof. exact (@lem7239146 term189 term189). Qed.
Lemma lem7239148 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239149 : term405 = term189.
Proof. exact (EQ_MP (@lem7239148) (@lem940073)). Qed.
Lemma lem7239150 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239151 : term403 = term340.
Proof. exact (MK_COMB (@lem7239150) (@lem7239149)). Qed.
Lemma lem7239152 : term402 = term340.
Proof. exact (TRANS (@lem7239147) (@lem7239151)). Qed.
Lemma lem7239154 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239155 : term488 = term328.
Proof. exact (@lem7239154 term189). Qed.
Lemma lem7239156 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239157 : term771 = term765.
Proof. exact (MK_COMB (@lem7239156) (@lem7239155)). Qed.
Lemma lem7239158 : term770 = term476.
Proof. exact (MK_COMB (@lem7239157) (@lem7239152)). Qed.
Lemma lem7239160 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239161 : term476 = term477.
Proof. exact (@lem7239160 (NUMERAL 0) term189). Qed.
Lemma lem7239162 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239163 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239164 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239163 h1) (fun h1 : term477 = True => @lem7239162)). Qed.
Lemma lem7239165 : term477 = True.
Proof. exact (EQ_MP (@lem7239164) (@lem7239162)). Qed.
Lemma lem7239166 : term476 = True.
Proof. exact (TRANS (@lem7239161) (@lem7239165)). Qed.
Lemma lem7239167 : term770 = True.
Proof. exact (TRANS (@lem7239158) (@lem7239166)). Qed.
Lemma lem7239168 : term767 = True.
Proof. exact (TRANS (@lem7239144) (@lem7239167)). Qed.
Lemma lem7239169 : term476 = True.
Proof. exact (TRANS (@lem7239121) (@lem7239168)). Qed.
Lemma lem7239170 : term764 = True.
Proof. exact (TRANS (@lem7239112) (@lem7239169)). Qed.
Lemma lem7239171 : True = term764.
Proof. exact (SYM (@lem7239170)). Qed.
Lemma lem7239172 : term764.
Proof. exact (EQ_MP (@lem7239171) (@lem0)). Qed.
Lemma lem7239173 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term778 _96884 _96886.
Proof. exact (conj (@lem7239172) (@lem7239035 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239175 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7239176 (_96884 : int) (_96886 : int) : term779 _96884 _96886.
Proof. exact (@lem7239175 term340 (term450 _96884 _96886)). Qed.
Lemma lem7239177 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term780 _96884 _96886.
Proof. exact (@lem7239176 _96884 _96886 (@lem7239173 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239178 (_96884 : int) (_96886 : int) : (term781 _96884 _96886) = (term450 _96884 _96886).
Proof. exact (@lem1982733 (term450 _96884 _96886)). Qed.
Lemma lem7239179 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7239180 (_96884 : int) (_96886 : int) : (term782 _96884 _96886) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7239179) (@lem7239178 _96884 _96886)). Qed.
Lemma lem7239181 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7239182 (_96884 : int) (_96886 : int) : (term780 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7239180 _96884 _96886) (@lem7239181)). Qed.
Lemma lem7239183 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term453 _96884 _96886.
Proof. exact (EQ_MP (@lem7239182 _96884 _96886) (@lem7239177 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239184 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term541 _96884 _96886.
Proof. exact (conj (@lem7239183 _96883 _96884 _96885 _96886 h1) (@lem7239109 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239186 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7239187 (_96884 : int) (_96886 : int) : term784 _96884 _96886.
Proof. exact (@lem7239186 (term450 _96884 _96886) (term424 _96884 _96886)). Qed.
Lemma lem7239188 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term785 _96884 _96886.
Proof. exact (@lem7239187 _96884 _96886 (@lem7239184 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239189 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = (term787 _96884 _96886).
Proof. exact (@lem1982753 (term418 _96884) (real_of_int _96884) (term788 _96886) (term418 _96886)). Qed.
Lemma lem7239190 (_96884 : int) : (term789 _96884) = (term790 _96884).
Proof. exact (@lem1982713 term393 (real_of_int _96884)). Qed.
Lemma lem7239192 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239193 : term340 = term438.
Proof. exact (@lem7239192 term189). Qed.
Lemma lem7239195 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7239196 : term393 = term394.
Proof. exact (@lem7239195 term189). Qed.
Lemma lem7239197 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239198 : term791 = term792.
Proof. exact (MK_COMB (@lem7239197) (@lem7239196)). Qed.
Lemma lem7239199 : term793 = term794.
Proof. exact (MK_COMB (@lem7239198) (@lem7239193)). Qed.
Lemma lem7239200 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7239202 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239203 : term476 = term477.
Proof. exact (@lem7239202 (NUMERAL 0) term189). Qed.
Lemma lem7239204 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239205 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239206 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239205 h1) (fun h1 : term477 = True => @lem7239204)). Qed.
Lemma lem7239207 : term477 = True.
Proof. exact (EQ_MP (@lem7239206) (@lem7239204)). Qed.
Lemma lem7239208 : term476 = True.
Proof. exact (TRANS (@lem7239203) (@lem7239207)). Qed.
Lemma lem7239209 : True = term476.
Proof. exact (SYM (@lem7239208)). Qed.
Lemma lem7239210 : term476.
Proof. exact (EQ_MP (@lem7239209) (@lem0)). Qed.
Lemma lem7239211 : term796.
Proof. exact (@lem7239200 (@lem7239210)). Qed.
Lemma lem7239213 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239214 : term476 = term477.
Proof. exact (@lem7239213 (NUMERAL 0) term189). Qed.
Lemma lem7239215 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239216 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239217 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239216 h1) (fun h1 : term477 = True => @lem7239215)). Qed.
Lemma lem7239218 : term477 = True.
Proof. exact (EQ_MP (@lem7239217) (@lem7239215)). Qed.
Lemma lem7239219 : term476 = True.
Proof. exact (TRANS (@lem7239214) (@lem7239218)). Qed.
Lemma lem7239220 : True = term476.
Proof. exact (SYM (@lem7239219)). Qed.
Lemma lem7239221 : term476.
Proof. exact (EQ_MP (@lem7239220) (@lem0)). Qed.
Lemma lem7239222 : term797.
Proof. exact (@lem7239211 (@lem7239221)). Qed.
Lemma lem7239224 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239225 : term476 = term477.
Proof. exact (@lem7239224 (NUMERAL 0) term189). Qed.
Lemma lem7239226 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239227 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239228 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239227 h1) (fun h1 : term477 = True => @lem7239226)). Qed.
Lemma lem7239229 : term477 = True.
Proof. exact (EQ_MP (@lem7239228) (@lem7239226)). Qed.
Lemma lem7239230 : term476 = True.
Proof. exact (TRANS (@lem7239225) (@lem7239229)). Qed.
Lemma lem7239231 : True = term476.
Proof. exact (SYM (@lem7239230)). Qed.
Lemma lem7239232 : term476.
Proof. exact (EQ_MP (@lem7239231) (@lem0)). Qed.
Lemma lem7239233 : term798.
Proof. exact (@lem7239222 (@lem7239232)). Qed.
Lemma lem7239235 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239236 : term402 = term403.
Proof. exact (@lem7239235 term189 term189). Qed.
Lemma lem7239237 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239238 : term405 = term189.
Proof. exact (EQ_MP (@lem7239237) (@lem940073)). Qed.
Lemma lem7239239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239240 : term403 = term340.
Proof. exact (MK_COMB (@lem7239239) (@lem7239238)). Qed.
Lemma lem7239241 : term402 = term340.
Proof. exact (TRANS (@lem7239236) (@lem7239240)). Qed.
Lemma lem7239243 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7239244 : term439 = term444.
Proof. exact (@lem7239243 term189 term189). Qed.
Lemma lem7239245 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239246 : term405 = term189.
Proof. exact (EQ_MP (@lem7239245) (@lem940073)). Qed.
Lemma lem7239247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239248 : term403 = term340.
Proof. exact (MK_COMB (@lem7239247) (@lem7239246)). Qed.
Lemma lem7239249 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7239250 : term444 = term393.
Proof. exact (MK_COMB (@lem7239249) (@lem7239248)). Qed.
Lemma lem7239251 : term439 = term393.
Proof. exact (TRANS (@lem7239244) (@lem7239250)). Qed.
Lemma lem7239252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239253 : term799 = term791.
Proof. exact (MK_COMB (@lem7239252) (@lem7239251)). Qed.
Lemma lem7239254 : term800 = term793.
Proof. exact (MK_COMB (@lem7239253) (@lem7239241)). Qed.
Lemma lem7239256 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7239257 : term793 = term328.
Proof. exact (@lem7239256 term189). Qed.
Lemma lem7239258 : term800 = term328.
Proof. exact (TRANS (@lem7239254) (@lem7239257)). Qed.
Lemma lem7239259 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239260 : term802 = term486.
Proof. exact (MK_COMB (@lem7239259) (@lem7239258)). Qed.
Lemma lem7239261 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7239262 : term803 = term488.
Proof. exact (MK_COMB (@lem7239260) (@lem7239261)). Qed.
Lemma lem7239264 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239265 : term488 = term328.
Proof. exact (@lem7239264 term189). Qed.
Lemma lem7239266 : term803 = term328.
Proof. exact (TRANS (@lem7239262) (@lem7239265)). Qed.
Lemma lem7239268 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239269 : term402 = term403.
Proof. exact (@lem7239268 term189 term189). Qed.
Lemma lem7239270 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239271 : term405 = term189.
Proof. exact (EQ_MP (@lem7239270) (@lem940073)). Qed.
Lemma lem7239272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239273 : term403 = term340.
Proof. exact (MK_COMB (@lem7239272) (@lem7239271)). Qed.
Lemma lem7239274 : term402 = term340.
Proof. exact (TRANS (@lem7239269) (@lem7239273)). Qed.
Lemma lem7239275 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7239276 : term490 = term488.
Proof. exact (MK_COMB (@lem7239275) (@lem7239274)). Qed.
Lemma lem7239278 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239279 : term488 = term328.
Proof. exact (@lem7239278 term189). Qed.
Lemma lem7239280 : term490 = term328.
Proof. exact (TRANS (@lem7239276) (@lem7239279)). Qed.
Lemma lem7239281 : term328 = term490.
Proof. exact (SYM (@lem7239280)). Qed.
Lemma lem7239282 : term803 = term490.
Proof. exact (TRANS (@lem7239266) (@lem7239281)). Qed.
Lemma lem7239283 : term794 = term390.
Proof. exact (@lem7239233 (@lem7239282)). Qed.
Lemma lem7239284 : term793 = term390.
Proof. exact (TRANS (@lem7239199) (@lem7239283)). Qed.
Lemma lem7239286 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7239287 : term390 = term328.
Proof. exact (@lem7239286 term328). Qed.
Lemma lem7239288 : term793 = term328.
Proof. exact (TRANS (@lem7239284) (@lem7239287)). Qed.
Lemma lem7239289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239290 : term804 = term486.
Proof. exact (MK_COMB (@lem7239289) (@lem7239288)). Qed.
Lemma lem7239291 (_96884 : int) : (real_of_int _96884) = (real_of_int _96884).
Proof. exact (eq_refl (real_of_int _96884)). Qed.
Lemma lem7239292 (_96884 : int) : (term790 _96884) = (term805 _96884).
Proof. exact (MK_COMB (@lem7239290) (@lem7239291 _96884)). Qed.
Lemma lem7239293 (_96884 : int) : (term789 _96884) = (term805 _96884).
Proof. exact (TRANS (@lem7239190 _96884) (@lem7239292 _96884)). Qed.
Lemma lem7239294 (_96884 : int) : (term805 _96884) = term328.
Proof. exact (@lem1982719 (real_of_int _96884)). Qed.
Lemma lem7239295 (_96884 : int) : (term789 _96884) = term328.
Proof. exact (TRANS (@lem7239293 _96884) (@lem7239294 _96884)). Qed.
Lemma lem7239296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239297 (_96884 : int) : (term806 _96884) = term807.
Proof. exact (MK_COMB (@lem7239296) (@lem7239295 _96884)). Qed.
Lemma lem7239298 (_96886 : int) : (term808 _96886) = (term809 _96886).
Proof. exact (@lem1982759 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7239299 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7239301 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239302 : term340 = term438.
Proof. exact (@lem7239301 term189). Qed.
Lemma lem7239304 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7239305 : term393 = term394.
Proof. exact (@lem7239304 term189). Qed.
Lemma lem7239306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239307 : term791 = term792.
Proof. exact (MK_COMB (@lem7239306) (@lem7239305)). Qed.
Lemma lem7239308 : term793 = term794.
Proof. exact (MK_COMB (@lem7239307) (@lem7239302)). Qed.
Lemma lem7239309 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7239311 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239312 : term476 = term477.
Proof. exact (@lem7239311 (NUMERAL 0) term189). Qed.
Lemma lem7239313 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239314 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239315 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239314 h1) (fun h1 : term477 = True => @lem7239313)). Qed.
Lemma lem7239316 : term477 = True.
Proof. exact (EQ_MP (@lem7239315) (@lem7239313)). Qed.
Lemma lem7239317 : term476 = True.
Proof. exact (TRANS (@lem7239312) (@lem7239316)). Qed.
Lemma lem7239318 : True = term476.
Proof. exact (SYM (@lem7239317)). Qed.
Lemma lem7239319 : term476.
Proof. exact (EQ_MP (@lem7239318) (@lem0)). Qed.
Lemma lem7239320 : term796.
Proof. exact (@lem7239309 (@lem7239319)). Qed.
Lemma lem7239322 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239323 : term476 = term477.
Proof. exact (@lem7239322 (NUMERAL 0) term189). Qed.
Lemma lem7239324 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239325 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239326 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239325 h1) (fun h1 : term477 = True => @lem7239324)). Qed.
Lemma lem7239327 : term477 = True.
Proof. exact (EQ_MP (@lem7239326) (@lem7239324)). Qed.
Lemma lem7239328 : term476 = True.
Proof. exact (TRANS (@lem7239323) (@lem7239327)). Qed.
Lemma lem7239329 : True = term476.
Proof. exact (SYM (@lem7239328)). Qed.
Lemma lem7239330 : term476.
Proof. exact (EQ_MP (@lem7239329) (@lem0)). Qed.
Lemma lem7239331 : term797.
Proof. exact (@lem7239320 (@lem7239330)). Qed.
Lemma lem7239333 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239334 : term476 = term477.
Proof. exact (@lem7239333 (NUMERAL 0) term189). Qed.
Lemma lem7239335 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239336 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239337 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239336 h1) (fun h1 : term477 = True => @lem7239335)). Qed.
Lemma lem7239338 : term477 = True.
Proof. exact (EQ_MP (@lem7239337) (@lem7239335)). Qed.
Lemma lem7239339 : term476 = True.
Proof. exact (TRANS (@lem7239334) (@lem7239338)). Qed.
Lemma lem7239340 : True = term476.
Proof. exact (SYM (@lem7239339)). Qed.
Lemma lem7239341 : term476.
Proof. exact (EQ_MP (@lem7239340) (@lem0)). Qed.
Lemma lem7239342 : term798.
Proof. exact (@lem7239331 (@lem7239341)). Qed.
Lemma lem7239344 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239345 : term402 = term403.
Proof. exact (@lem7239344 term189 term189). Qed.
Lemma lem7239346 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239347 : term405 = term189.
Proof. exact (EQ_MP (@lem7239346) (@lem940073)). Qed.
Lemma lem7239348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239349 : term403 = term340.
Proof. exact (MK_COMB (@lem7239348) (@lem7239347)). Qed.
Lemma lem7239350 : term402 = term340.
Proof. exact (TRANS (@lem7239345) (@lem7239349)). Qed.
Lemma lem7239352 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7239353 : term439 = term444.
Proof. exact (@lem7239352 term189 term189). Qed.
Lemma lem7239354 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239355 : term405 = term189.
Proof. exact (EQ_MP (@lem7239354) (@lem940073)). Qed.
Lemma lem7239356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239357 : term403 = term340.
Proof. exact (MK_COMB (@lem7239356) (@lem7239355)). Qed.
Lemma lem7239358 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7239359 : term444 = term393.
Proof. exact (MK_COMB (@lem7239358) (@lem7239357)). Qed.
Lemma lem7239360 : term439 = term393.
Proof. exact (TRANS (@lem7239353) (@lem7239359)). Qed.
Lemma lem7239361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239362 : term799 = term791.
Proof. exact (MK_COMB (@lem7239361) (@lem7239360)). Qed.
Lemma lem7239363 : term800 = term793.
Proof. exact (MK_COMB (@lem7239362) (@lem7239350)). Qed.
Lemma lem7239365 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7239366 : term793 = term328.
Proof. exact (@lem7239365 term189). Qed.
Lemma lem7239367 : term800 = term328.
Proof. exact (TRANS (@lem7239363) (@lem7239366)). Qed.
Lemma lem7239368 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239369 : term802 = term486.
Proof. exact (MK_COMB (@lem7239368) (@lem7239367)). Qed.
Lemma lem7239370 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7239371 : term803 = term488.
Proof. exact (MK_COMB (@lem7239369) (@lem7239370)). Qed.
Lemma lem7239373 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239374 : term488 = term328.
Proof. exact (@lem7239373 term189). Qed.
Lemma lem7239375 : term803 = term328.
Proof. exact (TRANS (@lem7239371) (@lem7239374)). Qed.
Lemma lem7239377 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239378 : term402 = term403.
Proof. exact (@lem7239377 term189 term189). Qed.
Lemma lem7239379 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239380 : term405 = term189.
Proof. exact (EQ_MP (@lem7239379) (@lem940073)). Qed.
Lemma lem7239381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239382 : term403 = term340.
Proof. exact (MK_COMB (@lem7239381) (@lem7239380)). Qed.
Lemma lem7239383 : term402 = term340.
Proof. exact (TRANS (@lem7239378) (@lem7239382)). Qed.
Lemma lem7239384 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7239385 : term490 = term488.
Proof. exact (MK_COMB (@lem7239384) (@lem7239383)). Qed.
Lemma lem7239387 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239388 : term488 = term328.
Proof. exact (@lem7239387 term189). Qed.
Lemma lem7239389 : term490 = term328.
Proof. exact (TRANS (@lem7239385) (@lem7239388)). Qed.
Lemma lem7239390 : term328 = term490.
Proof. exact (SYM (@lem7239389)). Qed.
Lemma lem7239391 : term803 = term490.
Proof. exact (TRANS (@lem7239375) (@lem7239390)). Qed.
Lemma lem7239392 : term794 = term390.
Proof. exact (@lem7239342 (@lem7239391)). Qed.
Lemma lem7239393 : term793 = term390.
Proof. exact (TRANS (@lem7239308) (@lem7239392)). Qed.
Lemma lem7239395 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7239396 : term390 = term328.
Proof. exact (@lem7239395 term328). Qed.
Lemma lem7239397 : term793 = term328.
Proof. exact (TRANS (@lem7239393) (@lem7239396)). Qed.
Lemma lem7239398 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239399 : term804 = term486.
Proof. exact (MK_COMB (@lem7239398) (@lem7239397)). Qed.
Lemma lem7239400 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7239401 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7239399) (@lem7239400 _96886)). Qed.
Lemma lem7239402 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7239299 _96886) (@lem7239401 _96886)). Qed.
Lemma lem7239403 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7239404 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7239402 _96886) (@lem7239403 _96886)). Qed.
Lemma lem7239405 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239406 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7239405) (@lem7239404 _96886)). Qed.
Lemma lem7239407 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7239408 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7239406 _96886) (@lem7239407)). Qed.
Lemma lem7239409 (_96886 : int) : (term808 _96886) = term812.
Proof. exact (TRANS (@lem7239298 _96886) (@lem7239408 _96886)). Qed.
Lemma lem7239410 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7239411 (_96886 : int) : (term808 _96886) = term393.
Proof. exact (TRANS (@lem7239409 _96886) (@lem7239410)). Qed.
Lemma lem7239412 (_96884 : int) (_96886 : int) : (term787 _96884 _96886) = term812.
Proof. exact (MK_COMB (@lem7239297 _96884) (@lem7239411 _96886)). Qed.
Lemma lem7239413 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = term812.
Proof. exact (TRANS (@lem7239189 _96884 _96886) (@lem7239412 _96884 _96886)). Qed.
Lemma lem7239414 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7239415 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = term393.
Proof. exact (TRANS (@lem7239413 _96884 _96886) (@lem7239414)). Qed.
Lemma lem7239416 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7239417 (_96884 : int) (_96886 : int) : (term813 _96884 _96886) = term814.
Proof. exact (MK_COMB (@lem7239416) (@lem7239415 _96884 _96886)). Qed.
Lemma lem7239418 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7239419 (_96884 : int) (_96886 : int) : (term785 _96884 _96886) = term815.
Proof. exact (MK_COMB (@lem7239417 _96884 _96886) (@lem7239418)). Qed.
Lemma lem7239420 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7239419 _96884 _96886) (@lem7239188 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239422 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7239423 : term815 = term816.
Proof. exact (@lem7239422 term328 term393). Qed.
Lemma lem7239425 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7239426 : term393 = term394.
Proof. exact (@lem7239425 term189). Qed.
Lemma lem7239428 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239429 : term328 = term390.
Proof. exact (@lem7239428 (NUMERAL 0)). Qed.
Lemma lem7239430 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7239431 : term330 = term817.
Proof. exact (MK_COMB (@lem7239430) (@lem7239429)). Qed.
Lemma lem7239432 : term816 = term818.
Proof. exact (MK_COMB (@lem7239431) (@lem7239426)). Qed.
Lemma lem7239433 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7239435 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239436 : term476 = term477.
Proof. exact (@lem7239435 (NUMERAL 0) term189). Qed.
Lemma lem7239437 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239438 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239439 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239438 h1) (fun h1 : term477 = True => @lem7239437)). Qed.
Lemma lem7239440 : term477 = True.
Proof. exact (EQ_MP (@lem7239439) (@lem7239437)). Qed.
Lemma lem7239441 : term476 = True.
Proof. exact (TRANS (@lem7239436) (@lem7239440)). Qed.
Lemma lem7239442 : True = term476.
Proof. exact (SYM (@lem7239441)). Qed.
Lemma lem7239443 : term476.
Proof. exact (EQ_MP (@lem7239442) (@lem0)). Qed.
Lemma lem7239444 : term820.
Proof. exact (@lem7239433 (@lem7239443)). Qed.
Lemma lem7239446 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239447 : term476 = term477.
Proof. exact (@lem7239446 (NUMERAL 0) term189). Qed.
Lemma lem7239448 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239449 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239450 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239449 h1) (fun h1 : term477 = True => @lem7239448)). Qed.
Lemma lem7239451 : term477 = True.
Proof. exact (EQ_MP (@lem7239450) (@lem7239448)). Qed.
Lemma lem7239452 : term476 = True.
Proof. exact (TRANS (@lem7239447) (@lem7239451)). Qed.
Lemma lem7239453 : True = term476.
Proof. exact (SYM (@lem7239452)). Qed.
Lemma lem7239454 : term476.
Proof. exact (EQ_MP (@lem7239453) (@lem0)). Qed.
Lemma lem7239455 : term818 = term821.
Proof. exact (@lem7239444 (@lem7239454)). Qed.
Lemma lem7239457 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7239458 : term439 = term444.
Proof. exact (@lem7239457 term189 term189). Qed.
Lemma lem7239459 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239460 : term405 = term189.
Proof. exact (EQ_MP (@lem7239459) (@lem940073)). Qed.
Lemma lem7239461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239462 : term403 = term340.
Proof. exact (MK_COMB (@lem7239461) (@lem7239460)). Qed.
Lemma lem7239463 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7239464 : term444 = term393.
Proof. exact (MK_COMB (@lem7239463) (@lem7239462)). Qed.
Lemma lem7239465 : term439 = term393.
Proof. exact (TRANS (@lem7239458) (@lem7239464)). Qed.
Lemma lem7239467 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239468 : term488 = term328.
Proof. exact (@lem7239467 term189). Qed.
Lemma lem7239469 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7239470 : term822 = term330.
Proof. exact (MK_COMB (@lem7239469) (@lem7239468)). Qed.
Lemma lem7239471 : term821 = term816.
Proof. exact (MK_COMB (@lem7239470) (@lem7239465)). Qed.
Lemma lem7239473 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7239474 : term816 = term825.
Proof. exact (@lem7239473 (NUMERAL 0) term189). Qed.
Lemma lem7239475 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239476 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7239477 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239476 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7239475)). Qed.
Lemma lem7239478 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7239477) (@lem7239475)). Qed.
Lemma lem7239479 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7239480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7239481 : term826 = (and True).
Proof. exact (MK_COMB (@lem7239480) (@lem7239479)). Qed.
Lemma lem7239482 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7239481) (@lem7239478)). Qed.
Lemma lem7239484 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7239485 : term825 = False.
Proof. exact (TRANS (@lem7239482) (@lem7239484)). Qed.
Lemma lem7239486 : term816 = False.
Proof. exact (TRANS (@lem7239474) (@lem7239485)). Qed.
Lemma lem7239487 : term821 = False.
Proof. exact (TRANS (@lem7239471) (@lem7239486)). Qed.
Lemma lem7239488 : term818 = False.
Proof. exact (TRANS (@lem7239455) (@lem7239487)). Qed.
Lemma lem7239489 : term816 = False.
Proof. exact (TRANS (@lem7239432) (@lem7239488)). Qed.
Lemma lem7239490 : term815 = False.
Proof. exact (TRANS (@lem7239423) (@lem7239489)). Qed.
Lemma lem7239491 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term763 _96883 _96884 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7239490) (@lem7239420 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7239492 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term760 _96883 _96884 _96885 _96886) : term760 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239493 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term757 _96884 _96883 _96885 _96886) : term757 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239494 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term752 _96884 _96883 _96885 _96886) : term752 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239495 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term827 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239496 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term753 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239495 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239498 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term717 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239496 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239500 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term681 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239498 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239502 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term645 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239500 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239504 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term609 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239502 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239506 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term573 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239504 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239508 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term432 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239506 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239509 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term540 _96883 _96884 _96886.
Proof. exact (proj1 (@lem7239506 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239511 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term459 _96883 _96886.
Proof. exact (proj1 (@lem7239509 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239513 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term428 _96883 _96886.
Proof. exact (proj1 (@lem7239508 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239515 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7239516 : term764 = term476.
Proof. exact (@lem7239515 term328 term340). Qed.
Lemma lem7239518 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239519 : term340 = term438.
Proof. exact (@lem7239518 term189). Qed.
Lemma lem7239521 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239522 : term328 = term390.
Proof. exact (@lem7239521 (NUMERAL 0)). Qed.
Lemma lem7239523 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239524 : term765 = term766.
Proof. exact (MK_COMB (@lem7239523) (@lem7239522)). Qed.
Lemma lem7239525 : term476 = term767.
Proof. exact (MK_COMB (@lem7239524) (@lem7239519)). Qed.
Lemma lem7239526 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7239528 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239529 : term476 = term477.
Proof. exact (@lem7239528 (NUMERAL 0) term189). Qed.
Lemma lem7239530 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239531 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239532 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239531 h1) (fun h1 : term477 = True => @lem7239530)). Qed.
Lemma lem7239533 : term477 = True.
Proof. exact (EQ_MP (@lem7239532) (@lem7239530)). Qed.
Lemma lem7239534 : term476 = True.
Proof. exact (TRANS (@lem7239529) (@lem7239533)). Qed.
Lemma lem7239535 : True = term476.
Proof. exact (SYM (@lem7239534)). Qed.
Lemma lem7239536 : term476.
Proof. exact (EQ_MP (@lem7239535) (@lem0)). Qed.
Lemma lem7239537 : term769.
Proof. exact (@lem7239526 (@lem7239536)). Qed.
Lemma lem7239539 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239540 : term476 = term477.
Proof. exact (@lem7239539 (NUMERAL 0) term189). Qed.
Lemma lem7239541 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239542 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239543 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239542 h1) (fun h1 : term477 = True => @lem7239541)). Qed.
Lemma lem7239544 : term477 = True.
Proof. exact (EQ_MP (@lem7239543) (@lem7239541)). Qed.
Lemma lem7239545 : term476 = True.
Proof. exact (TRANS (@lem7239540) (@lem7239544)). Qed.
Lemma lem7239546 : True = term476.
Proof. exact (SYM (@lem7239545)). Qed.
Lemma lem7239547 : term476.
Proof. exact (EQ_MP (@lem7239546) (@lem0)). Qed.
Lemma lem7239548 : term767 = term770.
Proof. exact (@lem7239537 (@lem7239547)). Qed.
Lemma lem7239550 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239551 : term402 = term403.
Proof. exact (@lem7239550 term189 term189). Qed.
Lemma lem7239552 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239553 : term405 = term189.
Proof. exact (EQ_MP (@lem7239552) (@lem940073)). Qed.
Lemma lem7239554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239555 : term403 = term340.
Proof. exact (MK_COMB (@lem7239554) (@lem7239553)). Qed.
Lemma lem7239556 : term402 = term340.
Proof. exact (TRANS (@lem7239551) (@lem7239555)). Qed.
Lemma lem7239558 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239559 : term488 = term328.
Proof. exact (@lem7239558 term189). Qed.
Lemma lem7239560 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239561 : term771 = term765.
Proof. exact (MK_COMB (@lem7239560) (@lem7239559)). Qed.
Lemma lem7239562 : term770 = term476.
Proof. exact (MK_COMB (@lem7239561) (@lem7239556)). Qed.
Lemma lem7239564 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239565 : term476 = term477.
Proof. exact (@lem7239564 (NUMERAL 0) term189). Qed.
Lemma lem7239566 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239567 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239568 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239567 h1) (fun h1 : term477 = True => @lem7239566)). Qed.
Lemma lem7239569 : term477 = True.
Proof. exact (EQ_MP (@lem7239568) (@lem7239566)). Qed.
Lemma lem7239570 : term476 = True.
Proof. exact (TRANS (@lem7239565) (@lem7239569)). Qed.
Lemma lem7239571 : term770 = True.
Proof. exact (TRANS (@lem7239562) (@lem7239570)). Qed.
Lemma lem7239572 : term767 = True.
Proof. exact (TRANS (@lem7239548) (@lem7239571)). Qed.
Lemma lem7239573 : term476 = True.
Proof. exact (TRANS (@lem7239525) (@lem7239572)). Qed.
Lemma lem7239574 : term764 = True.
Proof. exact (TRANS (@lem7239516) (@lem7239573)). Qed.
Lemma lem7239575 : True = term764.
Proof. exact (SYM (@lem7239574)). Qed.
Lemma lem7239576 : term764.
Proof. exact (EQ_MP (@lem7239575) (@lem0)). Qed.
Lemma lem7239577 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term828 _96883 _96886.
Proof. exact (conj (@lem7239576) (@lem7239511 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239579 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7239580 (_96883 : int) (_96886 : int) : term829 _96883 _96886.
Proof. exact (@lem7239579 term340 (term449 _96883 _96886)). Qed.
Lemma lem7239581 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term830 _96883 _96886.
Proof. exact (@lem7239580 _96883 _96886 (@lem7239577 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239582 (_96883 : int) (_96886 : int) : (term831 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (@lem1982733 (term449 _96883 _96886)). Qed.
Lemma lem7239583 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7239584 (_96883 : int) (_96886 : int) : (term832 _96883 _96886) = (term458 _96883 _96886).
Proof. exact (MK_COMB (@lem7239583) (@lem7239582 _96883 _96886)). Qed.
Lemma lem7239585 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7239586 (_96883 : int) (_96886 : int) : (term830 _96883 _96886) = (term459 _96883 _96886).
Proof. exact (MK_COMB (@lem7239584 _96883 _96886) (@lem7239585)). Qed.
Lemma lem7239587 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term459 _96883 _96886.
Proof. exact (EQ_MP (@lem7239586 _96883 _96886) (@lem7239581 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239589 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7239590 : term764 = term476.
Proof. exact (@lem7239589 term328 term340). Qed.
Lemma lem7239592 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239593 : term340 = term438.
Proof. exact (@lem7239592 term189). Qed.
Lemma lem7239595 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239596 : term328 = term390.
Proof. exact (@lem7239595 (NUMERAL 0)). Qed.
Lemma lem7239597 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239598 : term765 = term766.
Proof. exact (MK_COMB (@lem7239597) (@lem7239596)). Qed.
Lemma lem7239599 : term476 = term767.
Proof. exact (MK_COMB (@lem7239598) (@lem7239593)). Qed.
Lemma lem7239600 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7239602 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239603 : term476 = term477.
Proof. exact (@lem7239602 (NUMERAL 0) term189). Qed.
Lemma lem7239604 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239605 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239606 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239605 h1) (fun h1 : term477 = True => @lem7239604)). Qed.
Lemma lem7239607 : term477 = True.
Proof. exact (EQ_MP (@lem7239606) (@lem7239604)). Qed.
Lemma lem7239608 : term476 = True.
Proof. exact (TRANS (@lem7239603) (@lem7239607)). Qed.
Lemma lem7239609 : True = term476.
Proof. exact (SYM (@lem7239608)). Qed.
Lemma lem7239610 : term476.
Proof. exact (EQ_MP (@lem7239609) (@lem0)). Qed.
Lemma lem7239611 : term769.
Proof. exact (@lem7239600 (@lem7239610)). Qed.
Lemma lem7239613 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239614 : term476 = term477.
Proof. exact (@lem7239613 (NUMERAL 0) term189). Qed.
Lemma lem7239615 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239616 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239617 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239616 h1) (fun h1 : term477 = True => @lem7239615)). Qed.
Lemma lem7239618 : term477 = True.
Proof. exact (EQ_MP (@lem7239617) (@lem7239615)). Qed.
Lemma lem7239619 : term476 = True.
Proof. exact (TRANS (@lem7239614) (@lem7239618)). Qed.
Lemma lem7239620 : True = term476.
Proof. exact (SYM (@lem7239619)). Qed.
Lemma lem7239621 : term476.
Proof. exact (EQ_MP (@lem7239620) (@lem0)). Qed.
Lemma lem7239622 : term767 = term770.
Proof. exact (@lem7239611 (@lem7239621)). Qed.
Lemma lem7239624 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239625 : term402 = term403.
Proof. exact (@lem7239624 term189 term189). Qed.
Lemma lem7239626 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239627 : term405 = term189.
Proof. exact (EQ_MP (@lem7239626) (@lem940073)). Qed.
Lemma lem7239628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239629 : term403 = term340.
Proof. exact (MK_COMB (@lem7239628) (@lem7239627)). Qed.
Lemma lem7239630 : term402 = term340.
Proof. exact (TRANS (@lem7239625) (@lem7239629)). Qed.
Lemma lem7239632 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239633 : term488 = term328.
Proof. exact (@lem7239632 term189). Qed.
Lemma lem7239634 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239635 : term771 = term765.
Proof. exact (MK_COMB (@lem7239634) (@lem7239633)). Qed.
Lemma lem7239636 : term770 = term476.
Proof. exact (MK_COMB (@lem7239635) (@lem7239630)). Qed.
Lemma lem7239638 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239639 : term476 = term477.
Proof. exact (@lem7239638 (NUMERAL 0) term189). Qed.
Lemma lem7239640 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239641 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239642 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239641 h1) (fun h1 : term477 = True => @lem7239640)). Qed.
Lemma lem7239643 : term477 = True.
Proof. exact (EQ_MP (@lem7239642) (@lem7239640)). Qed.
Lemma lem7239644 : term476 = True.
Proof. exact (TRANS (@lem7239639) (@lem7239643)). Qed.
Lemma lem7239645 : term770 = True.
Proof. exact (TRANS (@lem7239636) (@lem7239644)). Qed.
Lemma lem7239646 : term767 = True.
Proof. exact (TRANS (@lem7239622) (@lem7239645)). Qed.
Lemma lem7239647 : term476 = True.
Proof. exact (TRANS (@lem7239599) (@lem7239646)). Qed.
Lemma lem7239648 : term764 = True.
Proof. exact (TRANS (@lem7239590) (@lem7239647)). Qed.
Lemma lem7239649 : True = term764.
Proof. exact (SYM (@lem7239648)). Qed.
Lemma lem7239650 : term764.
Proof. exact (EQ_MP (@lem7239649) (@lem0)). Qed.
Lemma lem7239651 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term833 _96883 _96886.
Proof. exact (conj (@lem7239650) (@lem7239513 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239653 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7239654 (_96883 : int) (_96886 : int) : term834 _96883 _96886.
Proof. exact (@lem7239653 term340 (term425 _96883 _96886)). Qed.
Lemma lem7239655 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term835 _96883 _96886.
Proof. exact (@lem7239654 _96883 _96886 (@lem7239651 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239656 (_96883 : int) (_96886 : int) : (term836 _96883 _96886) = (term425 _96883 _96886).
Proof. exact (@lem1982733 (term425 _96883 _96886)). Qed.
Lemma lem7239657 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7239658 (_96883 : int) (_96886 : int) : (term837 _96883 _96886) = (term427 _96883 _96886).
Proof. exact (MK_COMB (@lem7239657) (@lem7239656 _96883 _96886)). Qed.
Lemma lem7239659 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7239660 (_96883 : int) (_96886 : int) : (term835 _96883 _96886) = (term428 _96883 _96886).
Proof. exact (MK_COMB (@lem7239658 _96883 _96886) (@lem7239659)). Qed.
Lemma lem7239661 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term428 _96883 _96886.
Proof. exact (EQ_MP (@lem7239660 _96883 _96886) (@lem7239655 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239662 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term838 _96883 _96886.
Proof. exact (conj (@lem7239661 _96884 _96883 _96885 _96886 h1) (@lem7239587 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239664 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7239665 (_96883 : int) (_96886 : int) : term839 _96883 _96886.
Proof. exact (@lem7239664 (term425 _96883 _96886) (term449 _96883 _96886)). Qed.
Lemma lem7239666 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term840 _96883 _96886.
Proof. exact (@lem7239665 _96883 _96886 (@lem7239662 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239667 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = (term842 _96883 _96886).
Proof. exact (@lem1982753 (term418 _96883) (real_of_int _96883) (real_of_int _96886) (term448 _96886)). Qed.
Lemma lem7239668 (_96883 : int) : (term789 _96883) = (term790 _96883).
Proof. exact (@lem1982713 term393 (real_of_int _96883)). Qed.
Lemma lem7239670 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239671 : term340 = term438.
Proof. exact (@lem7239670 term189). Qed.
Lemma lem7239673 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7239674 : term393 = term394.
Proof. exact (@lem7239673 term189). Qed.
Lemma lem7239675 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239676 : term791 = term792.
Proof. exact (MK_COMB (@lem7239675) (@lem7239674)). Qed.
Lemma lem7239677 : term793 = term794.
Proof. exact (MK_COMB (@lem7239676) (@lem7239671)). Qed.
Lemma lem7239678 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7239680 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239681 : term476 = term477.
Proof. exact (@lem7239680 (NUMERAL 0) term189). Qed.
Lemma lem7239682 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239683 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239684 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239683 h1) (fun h1 : term477 = True => @lem7239682)). Qed.
Lemma lem7239685 : term477 = True.
Proof. exact (EQ_MP (@lem7239684) (@lem7239682)). Qed.
Lemma lem7239686 : term476 = True.
Proof. exact (TRANS (@lem7239681) (@lem7239685)). Qed.
Lemma lem7239687 : True = term476.
Proof. exact (SYM (@lem7239686)). Qed.
Lemma lem7239688 : term476.
Proof. exact (EQ_MP (@lem7239687) (@lem0)). Qed.
Lemma lem7239689 : term796.
Proof. exact (@lem7239678 (@lem7239688)). Qed.
Lemma lem7239691 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239692 : term476 = term477.
Proof. exact (@lem7239691 (NUMERAL 0) term189). Qed.
Lemma lem7239693 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239694 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239695 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239694 h1) (fun h1 : term477 = True => @lem7239693)). Qed.
Lemma lem7239696 : term477 = True.
Proof. exact (EQ_MP (@lem7239695) (@lem7239693)). Qed.
Lemma lem7239697 : term476 = True.
Proof. exact (TRANS (@lem7239692) (@lem7239696)). Qed.
Lemma lem7239698 : True = term476.
Proof. exact (SYM (@lem7239697)). Qed.
Lemma lem7239699 : term476.
Proof. exact (EQ_MP (@lem7239698) (@lem0)). Qed.
Lemma lem7239700 : term797.
Proof. exact (@lem7239689 (@lem7239699)). Qed.
Lemma lem7239702 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239703 : term476 = term477.
Proof. exact (@lem7239702 (NUMERAL 0) term189). Qed.
Lemma lem7239704 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239705 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239706 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239705 h1) (fun h1 : term477 = True => @lem7239704)). Qed.
Lemma lem7239707 : term477 = True.
Proof. exact (EQ_MP (@lem7239706) (@lem7239704)). Qed.
Lemma lem7239708 : term476 = True.
Proof. exact (TRANS (@lem7239703) (@lem7239707)). Qed.
Lemma lem7239709 : True = term476.
Proof. exact (SYM (@lem7239708)). Qed.
Lemma lem7239710 : term476.
Proof. exact (EQ_MP (@lem7239709) (@lem0)). Qed.
Lemma lem7239711 : term798.
Proof. exact (@lem7239700 (@lem7239710)). Qed.
Lemma lem7239713 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239714 : term402 = term403.
Proof. exact (@lem7239713 term189 term189). Qed.
Lemma lem7239715 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239716 : term405 = term189.
Proof. exact (EQ_MP (@lem7239715) (@lem940073)). Qed.
Lemma lem7239717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239718 : term403 = term340.
Proof. exact (MK_COMB (@lem7239717) (@lem7239716)). Qed.
Lemma lem7239719 : term402 = term340.
Proof. exact (TRANS (@lem7239714) (@lem7239718)). Qed.
Lemma lem7239721 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7239722 : term439 = term444.
Proof. exact (@lem7239721 term189 term189). Qed.
Lemma lem7239723 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239724 : term405 = term189.
Proof. exact (EQ_MP (@lem7239723) (@lem940073)). Qed.
Lemma lem7239725 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239726 : term403 = term340.
Proof. exact (MK_COMB (@lem7239725) (@lem7239724)). Qed.
Lemma lem7239727 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7239728 : term444 = term393.
Proof. exact (MK_COMB (@lem7239727) (@lem7239726)). Qed.
Lemma lem7239729 : term439 = term393.
Proof. exact (TRANS (@lem7239722) (@lem7239728)). Qed.
Lemma lem7239730 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239731 : term799 = term791.
Proof. exact (MK_COMB (@lem7239730) (@lem7239729)). Qed.
Lemma lem7239732 : term800 = term793.
Proof. exact (MK_COMB (@lem7239731) (@lem7239719)). Qed.
Lemma lem7239734 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7239735 : term793 = term328.
Proof. exact (@lem7239734 term189). Qed.
Lemma lem7239736 : term800 = term328.
Proof. exact (TRANS (@lem7239732) (@lem7239735)). Qed.
Lemma lem7239737 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239738 : term802 = term486.
Proof. exact (MK_COMB (@lem7239737) (@lem7239736)). Qed.
Lemma lem7239739 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7239740 : term803 = term488.
Proof. exact (MK_COMB (@lem7239738) (@lem7239739)). Qed.
Lemma lem7239742 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239743 : term488 = term328.
Proof. exact (@lem7239742 term189). Qed.
Lemma lem7239744 : term803 = term328.
Proof. exact (TRANS (@lem7239740) (@lem7239743)). Qed.
Lemma lem7239746 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239747 : term402 = term403.
Proof. exact (@lem7239746 term189 term189). Qed.
Lemma lem7239748 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239749 : term405 = term189.
Proof. exact (EQ_MP (@lem7239748) (@lem940073)). Qed.
Lemma lem7239750 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239751 : term403 = term340.
Proof. exact (MK_COMB (@lem7239750) (@lem7239749)). Qed.
Lemma lem7239752 : term402 = term340.
Proof. exact (TRANS (@lem7239747) (@lem7239751)). Qed.
Lemma lem7239753 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7239754 : term490 = term488.
Proof. exact (MK_COMB (@lem7239753) (@lem7239752)). Qed.
Lemma lem7239756 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239757 : term488 = term328.
Proof. exact (@lem7239756 term189). Qed.
Lemma lem7239758 : term490 = term328.
Proof. exact (TRANS (@lem7239754) (@lem7239757)). Qed.
Lemma lem7239759 : term328 = term490.
Proof. exact (SYM (@lem7239758)). Qed.
Lemma lem7239760 : term803 = term490.
Proof. exact (TRANS (@lem7239744) (@lem7239759)). Qed.
Lemma lem7239761 : term794 = term390.
Proof. exact (@lem7239711 (@lem7239760)). Qed.
Lemma lem7239762 : term793 = term390.
Proof. exact (TRANS (@lem7239677) (@lem7239761)). Qed.
Lemma lem7239764 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7239765 : term390 = term328.
Proof. exact (@lem7239764 term328). Qed.
Lemma lem7239766 : term793 = term328.
Proof. exact (TRANS (@lem7239762) (@lem7239765)). Qed.
Lemma lem7239767 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239768 : term804 = term486.
Proof. exact (MK_COMB (@lem7239767) (@lem7239766)). Qed.
Lemma lem7239769 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7239770 (_96883 : int) : (term790 _96883) = (term805 _96883).
Proof. exact (MK_COMB (@lem7239768) (@lem7239769 _96883)). Qed.
Lemma lem7239771 (_96883 : int) : (term789 _96883) = (term805 _96883).
Proof. exact (TRANS (@lem7239668 _96883) (@lem7239770 _96883)). Qed.
Lemma lem7239772 (_96883 : int) : (term805 _96883) = term328.
Proof. exact (@lem1982719 (real_of_int _96883)). Qed.
Lemma lem7239773 (_96883 : int) : (term789 _96883) = term328.
Proof. exact (TRANS (@lem7239771 _96883) (@lem7239772 _96883)). Qed.
Lemma lem7239774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239775 (_96883 : int) : (term806 _96883) = term807.
Proof. exact (MK_COMB (@lem7239774) (@lem7239773 _96883)). Qed.
Lemma lem7239776 (_96886 : int) : (term843 _96886) = (term809 _96886).
Proof. exact (@lem1982763 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7239777 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7239779 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239780 : term340 = term438.
Proof. exact (@lem7239779 term189). Qed.
Lemma lem7239782 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7239783 : term393 = term394.
Proof. exact (@lem7239782 term189). Qed.
Lemma lem7239784 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239785 : term791 = term792.
Proof. exact (MK_COMB (@lem7239784) (@lem7239783)). Qed.
Lemma lem7239786 : term793 = term794.
Proof. exact (MK_COMB (@lem7239785) (@lem7239780)). Qed.
Lemma lem7239787 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7239789 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239790 : term476 = term477.
Proof. exact (@lem7239789 (NUMERAL 0) term189). Qed.
Lemma lem7239791 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239792 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239793 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239792 h1) (fun h1 : term477 = True => @lem7239791)). Qed.
Lemma lem7239794 : term477 = True.
Proof. exact (EQ_MP (@lem7239793) (@lem7239791)). Qed.
Lemma lem7239795 : term476 = True.
Proof. exact (TRANS (@lem7239790) (@lem7239794)). Qed.
Lemma lem7239796 : True = term476.
Proof. exact (SYM (@lem7239795)). Qed.
Lemma lem7239797 : term476.
Proof. exact (EQ_MP (@lem7239796) (@lem0)). Qed.
Lemma lem7239798 : term796.
Proof. exact (@lem7239787 (@lem7239797)). Qed.
Lemma lem7239800 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239801 : term476 = term477.
Proof. exact (@lem7239800 (NUMERAL 0) term189). Qed.
Lemma lem7239802 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239803 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239804 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239803 h1) (fun h1 : term477 = True => @lem7239802)). Qed.
Lemma lem7239805 : term477 = True.
Proof. exact (EQ_MP (@lem7239804) (@lem7239802)). Qed.
Lemma lem7239806 : term476 = True.
Proof. exact (TRANS (@lem7239801) (@lem7239805)). Qed.
Lemma lem7239807 : True = term476.
Proof. exact (SYM (@lem7239806)). Qed.
Lemma lem7239808 : term476.
Proof. exact (EQ_MP (@lem7239807) (@lem0)). Qed.
Lemma lem7239809 : term797.
Proof. exact (@lem7239798 (@lem7239808)). Qed.
Lemma lem7239811 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239812 : term476 = term477.
Proof. exact (@lem7239811 (NUMERAL 0) term189). Qed.
Lemma lem7239813 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239814 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239815 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239814 h1) (fun h1 : term477 = True => @lem7239813)). Qed.
Lemma lem7239816 : term477 = True.
Proof. exact (EQ_MP (@lem7239815) (@lem7239813)). Qed.
Lemma lem7239817 : term476 = True.
Proof. exact (TRANS (@lem7239812) (@lem7239816)). Qed.
Lemma lem7239818 : True = term476.
Proof. exact (SYM (@lem7239817)). Qed.
Lemma lem7239819 : term476.
Proof. exact (EQ_MP (@lem7239818) (@lem0)). Qed.
Lemma lem7239820 : term798.
Proof. exact (@lem7239809 (@lem7239819)). Qed.
Lemma lem7239822 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239823 : term402 = term403.
Proof. exact (@lem7239822 term189 term189). Qed.
Lemma lem7239824 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239825 : term405 = term189.
Proof. exact (EQ_MP (@lem7239824) (@lem940073)). Qed.
Lemma lem7239826 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239827 : term403 = term340.
Proof. exact (MK_COMB (@lem7239826) (@lem7239825)). Qed.
Lemma lem7239828 : term402 = term340.
Proof. exact (TRANS (@lem7239823) (@lem7239827)). Qed.
Lemma lem7239830 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7239831 : term439 = term444.
Proof. exact (@lem7239830 term189 term189). Qed.
Lemma lem7239832 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239833 : term405 = term189.
Proof. exact (EQ_MP (@lem7239832) (@lem940073)). Qed.
Lemma lem7239834 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239835 : term403 = term340.
Proof. exact (MK_COMB (@lem7239834) (@lem7239833)). Qed.
Lemma lem7239836 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7239837 : term444 = term393.
Proof. exact (MK_COMB (@lem7239836) (@lem7239835)). Qed.
Lemma lem7239838 : term439 = term393.
Proof. exact (TRANS (@lem7239831) (@lem7239837)). Qed.
Lemma lem7239839 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239840 : term799 = term791.
Proof. exact (MK_COMB (@lem7239839) (@lem7239838)). Qed.
Lemma lem7239841 : term800 = term793.
Proof. exact (MK_COMB (@lem7239840) (@lem7239828)). Qed.
Lemma lem7239843 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7239844 : term793 = term328.
Proof. exact (@lem7239843 term189). Qed.
Lemma lem7239845 : term800 = term328.
Proof. exact (TRANS (@lem7239841) (@lem7239844)). Qed.
Lemma lem7239846 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239847 : term802 = term486.
Proof. exact (MK_COMB (@lem7239846) (@lem7239845)). Qed.
Lemma lem7239848 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7239849 : term803 = term488.
Proof. exact (MK_COMB (@lem7239847) (@lem7239848)). Qed.
Lemma lem7239851 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239852 : term488 = term328.
Proof. exact (@lem7239851 term189). Qed.
Lemma lem7239853 : term803 = term328.
Proof. exact (TRANS (@lem7239849) (@lem7239852)). Qed.
Lemma lem7239855 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7239856 : term402 = term403.
Proof. exact (@lem7239855 term189 term189). Qed.
Lemma lem7239857 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239858 : term405 = term189.
Proof. exact (EQ_MP (@lem7239857) (@lem940073)). Qed.
Lemma lem7239859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239860 : term403 = term340.
Proof. exact (MK_COMB (@lem7239859) (@lem7239858)). Qed.
Lemma lem7239861 : term402 = term340.
Proof. exact (TRANS (@lem7239856) (@lem7239860)). Qed.
Lemma lem7239862 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7239863 : term490 = term488.
Proof. exact (MK_COMB (@lem7239862) (@lem7239861)). Qed.
Lemma lem7239865 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239866 : term488 = term328.
Proof. exact (@lem7239865 term189). Qed.
Lemma lem7239867 : term490 = term328.
Proof. exact (TRANS (@lem7239863) (@lem7239866)). Qed.
Lemma lem7239868 : term328 = term490.
Proof. exact (SYM (@lem7239867)). Qed.
Lemma lem7239869 : term803 = term490.
Proof. exact (TRANS (@lem7239853) (@lem7239868)). Qed.
Lemma lem7239870 : term794 = term390.
Proof. exact (@lem7239820 (@lem7239869)). Qed.
Lemma lem7239871 : term793 = term390.
Proof. exact (TRANS (@lem7239786) (@lem7239870)). Qed.
Lemma lem7239873 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7239874 : term390 = term328.
Proof. exact (@lem7239873 term328). Qed.
Lemma lem7239875 : term793 = term328.
Proof. exact (TRANS (@lem7239871) (@lem7239874)). Qed.
Lemma lem7239876 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7239877 : term804 = term486.
Proof. exact (MK_COMB (@lem7239876) (@lem7239875)). Qed.
Lemma lem7239878 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7239879 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7239877) (@lem7239878 _96886)). Qed.
Lemma lem7239880 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7239777 _96886) (@lem7239879 _96886)). Qed.
Lemma lem7239881 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7239882 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7239880 _96886) (@lem7239881 _96886)). Qed.
Lemma lem7239883 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7239884 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7239883) (@lem7239882 _96886)). Qed.
Lemma lem7239885 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7239886 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7239884 _96886) (@lem7239885)). Qed.
Lemma lem7239887 (_96886 : int) : (term843 _96886) = term812.
Proof. exact (TRANS (@lem7239776 _96886) (@lem7239886 _96886)). Qed.
Lemma lem7239888 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7239889 (_96886 : int) : (term843 _96886) = term393.
Proof. exact (TRANS (@lem7239887 _96886) (@lem7239888)). Qed.
Lemma lem7239890 (_96883 : int) (_96886 : int) : (term842 _96883 _96886) = term812.
Proof. exact (MK_COMB (@lem7239775 _96883) (@lem7239889 _96886)). Qed.
Lemma lem7239891 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = term812.
Proof. exact (TRANS (@lem7239667 _96883 _96886) (@lem7239890 _96883 _96886)). Qed.
Lemma lem7239892 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7239893 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = term393.
Proof. exact (TRANS (@lem7239891 _96883 _96886) (@lem7239892)). Qed.
Lemma lem7239894 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7239895 (_96883 : int) (_96886 : int) : (term844 _96883 _96886) = term814.
Proof. exact (MK_COMB (@lem7239894) (@lem7239893 _96883 _96886)). Qed.
Lemma lem7239896 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7239897 (_96883 : int) (_96886 : int) : (term840 _96883 _96886) = term815.
Proof. exact (MK_COMB (@lem7239895 _96883 _96886) (@lem7239896)). Qed.
Lemma lem7239898 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7239897 _96883 _96886) (@lem7239666 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239900 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7239901 : term815 = term816.
Proof. exact (@lem7239900 term328 term393). Qed.
Lemma lem7239903 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7239904 : term393 = term394.
Proof. exact (@lem7239903 term189). Qed.
Lemma lem7239906 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239907 : term328 = term390.
Proof. exact (@lem7239906 (NUMERAL 0)). Qed.
Lemma lem7239908 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7239909 : term330 = term817.
Proof. exact (MK_COMB (@lem7239908) (@lem7239907)). Qed.
Lemma lem7239910 : term816 = term818.
Proof. exact (MK_COMB (@lem7239909) (@lem7239904)). Qed.
Lemma lem7239911 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7239913 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239914 : term476 = term477.
Proof. exact (@lem7239913 (NUMERAL 0) term189). Qed.
Lemma lem7239915 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239916 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239917 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239916 h1) (fun h1 : term477 = True => @lem7239915)). Qed.
Lemma lem7239918 : term477 = True.
Proof. exact (EQ_MP (@lem7239917) (@lem7239915)). Qed.
Lemma lem7239919 : term476 = True.
Proof. exact (TRANS (@lem7239914) (@lem7239918)). Qed.
Lemma lem7239920 : True = term476.
Proof. exact (SYM (@lem7239919)). Qed.
Lemma lem7239921 : term476.
Proof. exact (EQ_MP (@lem7239920) (@lem0)). Qed.
Lemma lem7239922 : term820.
Proof. exact (@lem7239911 (@lem7239921)). Qed.
Lemma lem7239924 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7239925 : term476 = term477.
Proof. exact (@lem7239924 (NUMERAL 0) term189). Qed.
Lemma lem7239926 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239927 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7239928 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239927 h1) (fun h1 : term477 = True => @lem7239926)). Qed.
Lemma lem7239929 : term477 = True.
Proof. exact (EQ_MP (@lem7239928) (@lem7239926)). Qed.
Lemma lem7239930 : term476 = True.
Proof. exact (TRANS (@lem7239925) (@lem7239929)). Qed.
Lemma lem7239931 : True = term476.
Proof. exact (SYM (@lem7239930)). Qed.
Lemma lem7239932 : term476.
Proof. exact (EQ_MP (@lem7239931) (@lem0)). Qed.
Lemma lem7239933 : term818 = term821.
Proof. exact (@lem7239922 (@lem7239932)). Qed.
Lemma lem7239935 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7239936 : term439 = term444.
Proof. exact (@lem7239935 term189 term189). Qed.
Lemma lem7239937 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7239938 : term405 = term189.
Proof. exact (EQ_MP (@lem7239937) (@lem940073)). Qed.
Lemma lem7239939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7239940 : term403 = term340.
Proof. exact (MK_COMB (@lem7239939) (@lem7239938)). Qed.
Lemma lem7239941 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7239942 : term444 = term393.
Proof. exact (MK_COMB (@lem7239941) (@lem7239940)). Qed.
Lemma lem7239943 : term439 = term393.
Proof. exact (TRANS (@lem7239936) (@lem7239942)). Qed.
Lemma lem7239945 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7239946 : term488 = term328.
Proof. exact (@lem7239945 term189). Qed.
Lemma lem7239947 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7239948 : term822 = term330.
Proof. exact (MK_COMB (@lem7239947) (@lem7239946)). Qed.
Lemma lem7239949 : term821 = term816.
Proof. exact (MK_COMB (@lem7239948) (@lem7239943)). Qed.
Lemma lem7239951 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7239952 : term816 = term825.
Proof. exact (@lem7239951 (NUMERAL 0) term189). Qed.
Lemma lem7239953 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7239954 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7239955 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7239954 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7239953)). Qed.
Lemma lem7239956 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7239955) (@lem7239953)). Qed.
Lemma lem7239957 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7239958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7239959 : term826 = (and True).
Proof. exact (MK_COMB (@lem7239958) (@lem7239957)). Qed.
Lemma lem7239960 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7239959) (@lem7239956)). Qed.
Lemma lem7239962 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7239963 : term825 = False.
Proof. exact (TRANS (@lem7239960) (@lem7239962)). Qed.
Lemma lem7239964 : term816 = False.
Proof. exact (TRANS (@lem7239952) (@lem7239963)). Qed.
Lemma lem7239965 : term821 = False.
Proof. exact (TRANS (@lem7239949) (@lem7239964)). Qed.
Lemma lem7239966 : term818 = False.
Proof. exact (TRANS (@lem7239933) (@lem7239965)). Qed.
Lemma lem7239967 : term816 = False.
Proof. exact (TRANS (@lem7239910) (@lem7239966)). Qed.
Lemma lem7239968 : term815 = False.
Proof. exact (TRANS (@lem7239901) (@lem7239967)). Qed.
Lemma lem7239969 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term827 _96884 _96883 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7239968) (@lem7239898 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239970 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term845 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7239971 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term754 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239970 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239973 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term718 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239971 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239975 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term682 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239973 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239977 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term646 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239975 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239979 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term610 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239977 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239981 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term574 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7239979 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239984 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term541 _96884 _96886.
Proof. exact (proj1 (@lem7239981 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239985 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term430 _96884 _96886.
Proof. exact (proj2 (@lem7239984 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239986 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term453 _96884 _96886.
Proof. exact (proj1 (@lem7239984 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7239990 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7239991 : term764 = term476.
Proof. exact (@lem7239990 term328 term340). Qed.
Lemma lem7239993 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239994 : term340 = term438.
Proof. exact (@lem7239993 term189). Qed.
Lemma lem7239996 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7239997 : term328 = term390.
Proof. exact (@lem7239996 (NUMERAL 0)). Qed.
Lemma lem7239998 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7239999 : term765 = term766.
Proof. exact (MK_COMB (@lem7239998) (@lem7239997)). Qed.
Lemma lem7240000 : term476 = term767.
Proof. exact (MK_COMB (@lem7239999) (@lem7239994)). Qed.
Lemma lem7240001 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7240003 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240004 : term476 = term477.
Proof. exact (@lem7240003 (NUMERAL 0) term189). Qed.
Lemma lem7240005 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240006 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240007 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240006 h1) (fun h1 : term477 = True => @lem7240005)). Qed.
Lemma lem7240008 : term477 = True.
Proof. exact (EQ_MP (@lem7240007) (@lem7240005)). Qed.
Lemma lem7240009 : term476 = True.
Proof. exact (TRANS (@lem7240004) (@lem7240008)). Qed.
Lemma lem7240010 : True = term476.
Proof. exact (SYM (@lem7240009)). Qed.
Lemma lem7240011 : term476.
Proof. exact (EQ_MP (@lem7240010) (@lem0)). Qed.
Lemma lem7240012 : term769.
Proof. exact (@lem7240001 (@lem7240011)). Qed.
Lemma lem7240014 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240015 : term476 = term477.
Proof. exact (@lem7240014 (NUMERAL 0) term189). Qed.
Lemma lem7240016 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240017 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240018 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240017 h1) (fun h1 : term477 = True => @lem7240016)). Qed.
Lemma lem7240019 : term477 = True.
Proof. exact (EQ_MP (@lem7240018) (@lem7240016)). Qed.
Lemma lem7240020 : term476 = True.
Proof. exact (TRANS (@lem7240015) (@lem7240019)). Qed.
Lemma lem7240021 : True = term476.
Proof. exact (SYM (@lem7240020)). Qed.
Lemma lem7240022 : term476.
Proof. exact (EQ_MP (@lem7240021) (@lem0)). Qed.
Lemma lem7240023 : term767 = term770.
Proof. exact (@lem7240012 (@lem7240022)). Qed.
Lemma lem7240025 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240026 : term402 = term403.
Proof. exact (@lem7240025 term189 term189). Qed.
Lemma lem7240027 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240028 : term405 = term189.
Proof. exact (EQ_MP (@lem7240027) (@lem940073)). Qed.
Lemma lem7240029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240030 : term403 = term340.
Proof. exact (MK_COMB (@lem7240029) (@lem7240028)). Qed.
Lemma lem7240031 : term402 = term340.
Proof. exact (TRANS (@lem7240026) (@lem7240030)). Qed.
Lemma lem7240033 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240034 : term488 = term328.
Proof. exact (@lem7240033 term189). Qed.
Lemma lem7240035 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240036 : term771 = term765.
Proof. exact (MK_COMB (@lem7240035) (@lem7240034)). Qed.
Lemma lem7240037 : term770 = term476.
Proof. exact (MK_COMB (@lem7240036) (@lem7240031)). Qed.
Lemma lem7240039 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240040 : term476 = term477.
Proof. exact (@lem7240039 (NUMERAL 0) term189). Qed.
Lemma lem7240041 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240042 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240043 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240042 h1) (fun h1 : term477 = True => @lem7240041)). Qed.
Lemma lem7240044 : term477 = True.
Proof. exact (EQ_MP (@lem7240043) (@lem7240041)). Qed.
Lemma lem7240045 : term476 = True.
Proof. exact (TRANS (@lem7240040) (@lem7240044)). Qed.
Lemma lem7240046 : term770 = True.
Proof. exact (TRANS (@lem7240037) (@lem7240045)). Qed.
Lemma lem7240047 : term767 = True.
Proof. exact (TRANS (@lem7240023) (@lem7240046)). Qed.
Lemma lem7240048 : term476 = True.
Proof. exact (TRANS (@lem7240000) (@lem7240047)). Qed.
Lemma lem7240049 : term764 = True.
Proof. exact (TRANS (@lem7239991) (@lem7240048)). Qed.
Lemma lem7240050 : True = term764.
Proof. exact (SYM (@lem7240049)). Qed.
Lemma lem7240051 : term764.
Proof. exact (EQ_MP (@lem7240050) (@lem0)). Qed.
Lemma lem7240052 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term772 _96884 _96886.
Proof. exact (conj (@lem7240051) (@lem7239985 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240054 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7240055 (_96884 : int) (_96886 : int) : term774 _96884 _96886.
Proof. exact (@lem7240054 term340 (term424 _96884 _96886)). Qed.
Lemma lem7240056 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term775 _96884 _96886.
Proof. exact (@lem7240055 _96884 _96886 (@lem7240052 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240057 (_96884 : int) (_96886 : int) : (term776 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982733 (term424 _96884 _96886)). Qed.
Lemma lem7240058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7240059 (_96884 : int) (_96886 : int) : (term777 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7240058) (@lem7240057 _96884 _96886)). Qed.
Lemma lem7240060 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7240061 (_96884 : int) (_96886 : int) : (term775 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7240059 _96884 _96886) (@lem7240060)). Qed.
Lemma lem7240062 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term430 _96884 _96886.
Proof. exact (EQ_MP (@lem7240061 _96884 _96886) (@lem7240056 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240064 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7240065 : term764 = term476.
Proof. exact (@lem7240064 term328 term340). Qed.
Lemma lem7240067 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240068 : term340 = term438.
Proof. exact (@lem7240067 term189). Qed.
Lemma lem7240070 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240071 : term328 = term390.
Proof. exact (@lem7240070 (NUMERAL 0)). Qed.
Lemma lem7240072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240073 : term765 = term766.
Proof. exact (MK_COMB (@lem7240072) (@lem7240071)). Qed.
Lemma lem7240074 : term476 = term767.
Proof. exact (MK_COMB (@lem7240073) (@lem7240068)). Qed.
Lemma lem7240075 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7240077 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240078 : term476 = term477.
Proof. exact (@lem7240077 (NUMERAL 0) term189). Qed.
Lemma lem7240079 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240080 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240081 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240080 h1) (fun h1 : term477 = True => @lem7240079)). Qed.
Lemma lem7240082 : term477 = True.
Proof. exact (EQ_MP (@lem7240081) (@lem7240079)). Qed.
Lemma lem7240083 : term476 = True.
Proof. exact (TRANS (@lem7240078) (@lem7240082)). Qed.
Lemma lem7240084 : True = term476.
Proof. exact (SYM (@lem7240083)). Qed.
Lemma lem7240085 : term476.
Proof. exact (EQ_MP (@lem7240084) (@lem0)). Qed.
Lemma lem7240086 : term769.
Proof. exact (@lem7240075 (@lem7240085)). Qed.
Lemma lem7240088 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240089 : term476 = term477.
Proof. exact (@lem7240088 (NUMERAL 0) term189). Qed.
Lemma lem7240090 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240091 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240092 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240091 h1) (fun h1 : term477 = True => @lem7240090)). Qed.
Lemma lem7240093 : term477 = True.
Proof. exact (EQ_MP (@lem7240092) (@lem7240090)). Qed.
Lemma lem7240094 : term476 = True.
Proof. exact (TRANS (@lem7240089) (@lem7240093)). Qed.
Lemma lem7240095 : True = term476.
Proof. exact (SYM (@lem7240094)). Qed.
Lemma lem7240096 : term476.
Proof. exact (EQ_MP (@lem7240095) (@lem0)). Qed.
Lemma lem7240097 : term767 = term770.
Proof. exact (@lem7240086 (@lem7240096)). Qed.
Lemma lem7240099 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240100 : term402 = term403.
Proof. exact (@lem7240099 term189 term189). Qed.
Lemma lem7240101 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240102 : term405 = term189.
Proof. exact (EQ_MP (@lem7240101) (@lem940073)). Qed.
Lemma lem7240103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240104 : term403 = term340.
Proof. exact (MK_COMB (@lem7240103) (@lem7240102)). Qed.
Lemma lem7240105 : term402 = term340.
Proof. exact (TRANS (@lem7240100) (@lem7240104)). Qed.
Lemma lem7240107 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240108 : term488 = term328.
Proof. exact (@lem7240107 term189). Qed.
Lemma lem7240109 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240110 : term771 = term765.
Proof. exact (MK_COMB (@lem7240109) (@lem7240108)). Qed.
Lemma lem7240111 : term770 = term476.
Proof. exact (MK_COMB (@lem7240110) (@lem7240105)). Qed.
Lemma lem7240113 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240114 : term476 = term477.
Proof. exact (@lem7240113 (NUMERAL 0) term189). Qed.
Lemma lem7240115 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240116 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240117 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240116 h1) (fun h1 : term477 = True => @lem7240115)). Qed.
Lemma lem7240118 : term477 = True.
Proof. exact (EQ_MP (@lem7240117) (@lem7240115)). Qed.
Lemma lem7240119 : term476 = True.
Proof. exact (TRANS (@lem7240114) (@lem7240118)). Qed.
Lemma lem7240120 : term770 = True.
Proof. exact (TRANS (@lem7240111) (@lem7240119)). Qed.
Lemma lem7240121 : term767 = True.
Proof. exact (TRANS (@lem7240097) (@lem7240120)). Qed.
Lemma lem7240122 : term476 = True.
Proof. exact (TRANS (@lem7240074) (@lem7240121)). Qed.
Lemma lem7240123 : term764 = True.
Proof. exact (TRANS (@lem7240065) (@lem7240122)). Qed.
Lemma lem7240124 : True = term764.
Proof. exact (SYM (@lem7240123)). Qed.
Lemma lem7240125 : term764.
Proof. exact (EQ_MP (@lem7240124) (@lem0)). Qed.
Lemma lem7240126 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term778 _96884 _96886.
Proof. exact (conj (@lem7240125) (@lem7239986 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240128 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7240129 (_96884 : int) (_96886 : int) : term779 _96884 _96886.
Proof. exact (@lem7240128 term340 (term450 _96884 _96886)). Qed.
Lemma lem7240130 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term780 _96884 _96886.
Proof. exact (@lem7240129 _96884 _96886 (@lem7240126 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240131 (_96884 : int) (_96886 : int) : (term781 _96884 _96886) = (term450 _96884 _96886).
Proof. exact (@lem1982733 (term450 _96884 _96886)). Qed.
Lemma lem7240132 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7240133 (_96884 : int) (_96886 : int) : (term782 _96884 _96886) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7240132) (@lem7240131 _96884 _96886)). Qed.
Lemma lem7240134 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7240135 (_96884 : int) (_96886 : int) : (term780 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7240133 _96884 _96886) (@lem7240134)). Qed.
Lemma lem7240136 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term453 _96884 _96886.
Proof. exact (EQ_MP (@lem7240135 _96884 _96886) (@lem7240130 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240137 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term541 _96884 _96886.
Proof. exact (conj (@lem7240136 _96884 _96883 _96885 _96886 h1) (@lem7240062 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240139 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7240140 (_96884 : int) (_96886 : int) : term784 _96884 _96886.
Proof. exact (@lem7240139 (term450 _96884 _96886) (term424 _96884 _96886)). Qed.
Lemma lem7240141 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term785 _96884 _96886.
Proof. exact (@lem7240140 _96884 _96886 (@lem7240137 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240142 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = (term787 _96884 _96886).
Proof. exact (@lem1982753 (term418 _96884) (real_of_int _96884) (term788 _96886) (term418 _96886)). Qed.
Lemma lem7240143 (_96884 : int) : (term789 _96884) = (term790 _96884).
Proof. exact (@lem1982713 term393 (real_of_int _96884)). Qed.
Lemma lem7240145 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240146 : term340 = term438.
Proof. exact (@lem7240145 term189). Qed.
Lemma lem7240148 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7240149 : term393 = term394.
Proof. exact (@lem7240148 term189). Qed.
Lemma lem7240150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240151 : term791 = term792.
Proof. exact (MK_COMB (@lem7240150) (@lem7240149)). Qed.
Lemma lem7240152 : term793 = term794.
Proof. exact (MK_COMB (@lem7240151) (@lem7240146)). Qed.
Lemma lem7240153 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7240155 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240156 : term476 = term477.
Proof. exact (@lem7240155 (NUMERAL 0) term189). Qed.
Lemma lem7240157 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240158 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240159 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240158 h1) (fun h1 : term477 = True => @lem7240157)). Qed.
Lemma lem7240160 : term477 = True.
Proof. exact (EQ_MP (@lem7240159) (@lem7240157)). Qed.
Lemma lem7240161 : term476 = True.
Proof. exact (TRANS (@lem7240156) (@lem7240160)). Qed.
Lemma lem7240162 : True = term476.
Proof. exact (SYM (@lem7240161)). Qed.
Lemma lem7240163 : term476.
Proof. exact (EQ_MP (@lem7240162) (@lem0)). Qed.
Lemma lem7240164 : term796.
Proof. exact (@lem7240153 (@lem7240163)). Qed.
Lemma lem7240166 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240167 : term476 = term477.
Proof. exact (@lem7240166 (NUMERAL 0) term189). Qed.
Lemma lem7240168 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240169 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240170 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240169 h1) (fun h1 : term477 = True => @lem7240168)). Qed.
Lemma lem7240171 : term477 = True.
Proof. exact (EQ_MP (@lem7240170) (@lem7240168)). Qed.
Lemma lem7240172 : term476 = True.
Proof. exact (TRANS (@lem7240167) (@lem7240171)). Qed.
Lemma lem7240173 : True = term476.
Proof. exact (SYM (@lem7240172)). Qed.
Lemma lem7240174 : term476.
Proof. exact (EQ_MP (@lem7240173) (@lem0)). Qed.
Lemma lem7240175 : term797.
Proof. exact (@lem7240164 (@lem7240174)). Qed.
Lemma lem7240177 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240178 : term476 = term477.
Proof. exact (@lem7240177 (NUMERAL 0) term189). Qed.
Lemma lem7240179 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240180 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240181 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240180 h1) (fun h1 : term477 = True => @lem7240179)). Qed.
Lemma lem7240182 : term477 = True.
Proof. exact (EQ_MP (@lem7240181) (@lem7240179)). Qed.
Lemma lem7240183 : term476 = True.
Proof. exact (TRANS (@lem7240178) (@lem7240182)). Qed.
Lemma lem7240184 : True = term476.
Proof. exact (SYM (@lem7240183)). Qed.
Lemma lem7240185 : term476.
Proof. exact (EQ_MP (@lem7240184) (@lem0)). Qed.
Lemma lem7240186 : term798.
Proof. exact (@lem7240175 (@lem7240185)). Qed.
Lemma lem7240188 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240189 : term402 = term403.
Proof. exact (@lem7240188 term189 term189). Qed.
Lemma lem7240190 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240191 : term405 = term189.
Proof. exact (EQ_MP (@lem7240190) (@lem940073)). Qed.
Lemma lem7240192 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240193 : term403 = term340.
Proof. exact (MK_COMB (@lem7240192) (@lem7240191)). Qed.
Lemma lem7240194 : term402 = term340.
Proof. exact (TRANS (@lem7240189) (@lem7240193)). Qed.
Lemma lem7240196 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7240197 : term439 = term444.
Proof. exact (@lem7240196 term189 term189). Qed.
Lemma lem7240198 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240199 : term405 = term189.
Proof. exact (EQ_MP (@lem7240198) (@lem940073)). Qed.
Lemma lem7240200 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240201 : term403 = term340.
Proof. exact (MK_COMB (@lem7240200) (@lem7240199)). Qed.
Lemma lem7240202 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7240203 : term444 = term393.
Proof. exact (MK_COMB (@lem7240202) (@lem7240201)). Qed.
Lemma lem7240204 : term439 = term393.
Proof. exact (TRANS (@lem7240197) (@lem7240203)). Qed.
Lemma lem7240205 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240206 : term799 = term791.
Proof. exact (MK_COMB (@lem7240205) (@lem7240204)). Qed.
Lemma lem7240207 : term800 = term793.
Proof. exact (MK_COMB (@lem7240206) (@lem7240194)). Qed.
Lemma lem7240209 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7240210 : term793 = term328.
Proof. exact (@lem7240209 term189). Qed.
Lemma lem7240211 : term800 = term328.
Proof. exact (TRANS (@lem7240207) (@lem7240210)). Qed.
Lemma lem7240212 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240213 : term802 = term486.
Proof. exact (MK_COMB (@lem7240212) (@lem7240211)). Qed.
Lemma lem7240214 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7240215 : term803 = term488.
Proof. exact (MK_COMB (@lem7240213) (@lem7240214)). Qed.
Lemma lem7240217 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240218 : term488 = term328.
Proof. exact (@lem7240217 term189). Qed.
Lemma lem7240219 : term803 = term328.
Proof. exact (TRANS (@lem7240215) (@lem7240218)). Qed.
Lemma lem7240221 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240222 : term402 = term403.
Proof. exact (@lem7240221 term189 term189). Qed.
Lemma lem7240223 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240224 : term405 = term189.
Proof. exact (EQ_MP (@lem7240223) (@lem940073)). Qed.
Lemma lem7240225 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240226 : term403 = term340.
Proof. exact (MK_COMB (@lem7240225) (@lem7240224)). Qed.
Lemma lem7240227 : term402 = term340.
Proof. exact (TRANS (@lem7240222) (@lem7240226)). Qed.
Lemma lem7240228 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7240229 : term490 = term488.
Proof. exact (MK_COMB (@lem7240228) (@lem7240227)). Qed.
Lemma lem7240231 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240232 : term488 = term328.
Proof. exact (@lem7240231 term189). Qed.
Lemma lem7240233 : term490 = term328.
Proof. exact (TRANS (@lem7240229) (@lem7240232)). Qed.
Lemma lem7240234 : term328 = term490.
Proof. exact (SYM (@lem7240233)). Qed.
Lemma lem7240235 : term803 = term490.
Proof. exact (TRANS (@lem7240219) (@lem7240234)). Qed.
Lemma lem7240236 : term794 = term390.
Proof. exact (@lem7240186 (@lem7240235)). Qed.
Lemma lem7240237 : term793 = term390.
Proof. exact (TRANS (@lem7240152) (@lem7240236)). Qed.
Lemma lem7240239 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7240240 : term390 = term328.
Proof. exact (@lem7240239 term328). Qed.
Lemma lem7240241 : term793 = term328.
Proof. exact (TRANS (@lem7240237) (@lem7240240)). Qed.
Lemma lem7240242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240243 : term804 = term486.
Proof. exact (MK_COMB (@lem7240242) (@lem7240241)). Qed.
Lemma lem7240244 (_96884 : int) : (real_of_int _96884) = (real_of_int _96884).
Proof. exact (eq_refl (real_of_int _96884)). Qed.
Lemma lem7240245 (_96884 : int) : (term790 _96884) = (term805 _96884).
Proof. exact (MK_COMB (@lem7240243) (@lem7240244 _96884)). Qed.
Lemma lem7240246 (_96884 : int) : (term789 _96884) = (term805 _96884).
Proof. exact (TRANS (@lem7240143 _96884) (@lem7240245 _96884)). Qed.
Lemma lem7240247 (_96884 : int) : (term805 _96884) = term328.
Proof. exact (@lem1982719 (real_of_int _96884)). Qed.
Lemma lem7240248 (_96884 : int) : (term789 _96884) = term328.
Proof. exact (TRANS (@lem7240246 _96884) (@lem7240247 _96884)). Qed.
Lemma lem7240249 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240250 (_96884 : int) : (term806 _96884) = term807.
Proof. exact (MK_COMB (@lem7240249) (@lem7240248 _96884)). Qed.
Lemma lem7240251 (_96886 : int) : (term808 _96886) = (term809 _96886).
Proof. exact (@lem1982759 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7240252 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7240254 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240255 : term340 = term438.
Proof. exact (@lem7240254 term189). Qed.
Lemma lem7240257 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7240258 : term393 = term394.
Proof. exact (@lem7240257 term189). Qed.
Lemma lem7240259 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240260 : term791 = term792.
Proof. exact (MK_COMB (@lem7240259) (@lem7240258)). Qed.
Lemma lem7240261 : term793 = term794.
Proof. exact (MK_COMB (@lem7240260) (@lem7240255)). Qed.
Lemma lem7240262 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7240264 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240265 : term476 = term477.
Proof. exact (@lem7240264 (NUMERAL 0) term189). Qed.
Lemma lem7240266 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240267 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240268 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240267 h1) (fun h1 : term477 = True => @lem7240266)). Qed.
Lemma lem7240269 : term477 = True.
Proof. exact (EQ_MP (@lem7240268) (@lem7240266)). Qed.
Lemma lem7240270 : term476 = True.
Proof. exact (TRANS (@lem7240265) (@lem7240269)). Qed.
Lemma lem7240271 : True = term476.
Proof. exact (SYM (@lem7240270)). Qed.
Lemma lem7240272 : term476.
Proof. exact (EQ_MP (@lem7240271) (@lem0)). Qed.
Lemma lem7240273 : term796.
Proof. exact (@lem7240262 (@lem7240272)). Qed.
Lemma lem7240275 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240276 : term476 = term477.
Proof. exact (@lem7240275 (NUMERAL 0) term189). Qed.
Lemma lem7240277 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240278 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240279 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240278 h1) (fun h1 : term477 = True => @lem7240277)). Qed.
Lemma lem7240280 : term477 = True.
Proof. exact (EQ_MP (@lem7240279) (@lem7240277)). Qed.
Lemma lem7240281 : term476 = True.
Proof. exact (TRANS (@lem7240276) (@lem7240280)). Qed.
Lemma lem7240282 : True = term476.
Proof. exact (SYM (@lem7240281)). Qed.
Lemma lem7240283 : term476.
Proof. exact (EQ_MP (@lem7240282) (@lem0)). Qed.
Lemma lem7240284 : term797.
Proof. exact (@lem7240273 (@lem7240283)). Qed.
Lemma lem7240286 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240287 : term476 = term477.
Proof. exact (@lem7240286 (NUMERAL 0) term189). Qed.
Lemma lem7240288 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240289 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240290 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240289 h1) (fun h1 : term477 = True => @lem7240288)). Qed.
Lemma lem7240291 : term477 = True.
Proof. exact (EQ_MP (@lem7240290) (@lem7240288)). Qed.
Lemma lem7240292 : term476 = True.
Proof. exact (TRANS (@lem7240287) (@lem7240291)). Qed.
Lemma lem7240293 : True = term476.
Proof. exact (SYM (@lem7240292)). Qed.
Lemma lem7240294 : term476.
Proof. exact (EQ_MP (@lem7240293) (@lem0)). Qed.
Lemma lem7240295 : term798.
Proof. exact (@lem7240284 (@lem7240294)). Qed.
Lemma lem7240297 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240298 : term402 = term403.
Proof. exact (@lem7240297 term189 term189). Qed.
Lemma lem7240299 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240300 : term405 = term189.
Proof. exact (EQ_MP (@lem7240299) (@lem940073)). Qed.
Lemma lem7240301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240302 : term403 = term340.
Proof. exact (MK_COMB (@lem7240301) (@lem7240300)). Qed.
Lemma lem7240303 : term402 = term340.
Proof. exact (TRANS (@lem7240298) (@lem7240302)). Qed.
Lemma lem7240305 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7240306 : term439 = term444.
Proof. exact (@lem7240305 term189 term189). Qed.
Lemma lem7240307 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240308 : term405 = term189.
Proof. exact (EQ_MP (@lem7240307) (@lem940073)). Qed.
Lemma lem7240309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240310 : term403 = term340.
Proof. exact (MK_COMB (@lem7240309) (@lem7240308)). Qed.
Lemma lem7240311 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7240312 : term444 = term393.
Proof. exact (MK_COMB (@lem7240311) (@lem7240310)). Qed.
Lemma lem7240313 : term439 = term393.
Proof. exact (TRANS (@lem7240306) (@lem7240312)). Qed.
Lemma lem7240314 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240315 : term799 = term791.
Proof. exact (MK_COMB (@lem7240314) (@lem7240313)). Qed.
Lemma lem7240316 : term800 = term793.
Proof. exact (MK_COMB (@lem7240315) (@lem7240303)). Qed.
Lemma lem7240318 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7240319 : term793 = term328.
Proof. exact (@lem7240318 term189). Qed.
Lemma lem7240320 : term800 = term328.
Proof. exact (TRANS (@lem7240316) (@lem7240319)). Qed.
Lemma lem7240321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240322 : term802 = term486.
Proof. exact (MK_COMB (@lem7240321) (@lem7240320)). Qed.
Lemma lem7240323 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7240324 : term803 = term488.
Proof. exact (MK_COMB (@lem7240322) (@lem7240323)). Qed.
Lemma lem7240326 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240327 : term488 = term328.
Proof. exact (@lem7240326 term189). Qed.
Lemma lem7240328 : term803 = term328.
Proof. exact (TRANS (@lem7240324) (@lem7240327)). Qed.
Lemma lem7240330 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240331 : term402 = term403.
Proof. exact (@lem7240330 term189 term189). Qed.
Lemma lem7240332 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240333 : term405 = term189.
Proof. exact (EQ_MP (@lem7240332) (@lem940073)). Qed.
Lemma lem7240334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240335 : term403 = term340.
Proof. exact (MK_COMB (@lem7240334) (@lem7240333)). Qed.
Lemma lem7240336 : term402 = term340.
Proof. exact (TRANS (@lem7240331) (@lem7240335)). Qed.
Lemma lem7240337 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7240338 : term490 = term488.
Proof. exact (MK_COMB (@lem7240337) (@lem7240336)). Qed.
Lemma lem7240340 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240341 : term488 = term328.
Proof. exact (@lem7240340 term189). Qed.
Lemma lem7240342 : term490 = term328.
Proof. exact (TRANS (@lem7240338) (@lem7240341)). Qed.
Lemma lem7240343 : term328 = term490.
Proof. exact (SYM (@lem7240342)). Qed.
Lemma lem7240344 : term803 = term490.
Proof. exact (TRANS (@lem7240328) (@lem7240343)). Qed.
Lemma lem7240345 : term794 = term390.
Proof. exact (@lem7240295 (@lem7240344)). Qed.
Lemma lem7240346 : term793 = term390.
Proof. exact (TRANS (@lem7240261) (@lem7240345)). Qed.
Lemma lem7240348 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7240349 : term390 = term328.
Proof. exact (@lem7240348 term328). Qed.
Lemma lem7240350 : term793 = term328.
Proof. exact (TRANS (@lem7240346) (@lem7240349)). Qed.
Lemma lem7240351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240352 : term804 = term486.
Proof. exact (MK_COMB (@lem7240351) (@lem7240350)). Qed.
Lemma lem7240353 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7240354 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7240352) (@lem7240353 _96886)). Qed.
Lemma lem7240355 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7240252 _96886) (@lem7240354 _96886)). Qed.
Lemma lem7240356 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7240357 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7240355 _96886) (@lem7240356 _96886)). Qed.
Lemma lem7240358 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240359 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7240358) (@lem7240357 _96886)). Qed.
Lemma lem7240360 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7240361 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7240359 _96886) (@lem7240360)). Qed.
Lemma lem7240362 (_96886 : int) : (term808 _96886) = term812.
Proof. exact (TRANS (@lem7240251 _96886) (@lem7240361 _96886)). Qed.
Lemma lem7240363 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7240364 (_96886 : int) : (term808 _96886) = term393.
Proof. exact (TRANS (@lem7240362 _96886) (@lem7240363)). Qed.
Lemma lem7240365 (_96884 : int) (_96886 : int) : (term787 _96884 _96886) = term812.
Proof. exact (MK_COMB (@lem7240250 _96884) (@lem7240364 _96886)). Qed.
Lemma lem7240366 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = term812.
Proof. exact (TRANS (@lem7240142 _96884 _96886) (@lem7240365 _96884 _96886)). Qed.
Lemma lem7240367 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7240368 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = term393.
Proof. exact (TRANS (@lem7240366 _96884 _96886) (@lem7240367)). Qed.
Lemma lem7240369 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7240370 (_96884 : int) (_96886 : int) : (term813 _96884 _96886) = term814.
Proof. exact (MK_COMB (@lem7240369) (@lem7240368 _96884 _96886)). Qed.
Lemma lem7240371 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7240372 (_96884 : int) (_96886 : int) : (term785 _96884 _96886) = term815.
Proof. exact (MK_COMB (@lem7240370 _96884 _96886) (@lem7240371)). Qed.
Lemma lem7240373 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7240372 _96884 _96886) (@lem7240141 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240375 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7240376 : term815 = term816.
Proof. exact (@lem7240375 term328 term393). Qed.
Lemma lem7240378 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7240379 : term393 = term394.
Proof. exact (@lem7240378 term189). Qed.
Lemma lem7240381 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240382 : term328 = term390.
Proof. exact (@lem7240381 (NUMERAL 0)). Qed.
Lemma lem7240383 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7240384 : term330 = term817.
Proof. exact (MK_COMB (@lem7240383) (@lem7240382)). Qed.
Lemma lem7240385 : term816 = term818.
Proof. exact (MK_COMB (@lem7240384) (@lem7240379)). Qed.
Lemma lem7240386 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7240388 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240389 : term476 = term477.
Proof. exact (@lem7240388 (NUMERAL 0) term189). Qed.
Lemma lem7240390 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240391 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240392 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240391 h1) (fun h1 : term477 = True => @lem7240390)). Qed.
Lemma lem7240393 : term477 = True.
Proof. exact (EQ_MP (@lem7240392) (@lem7240390)). Qed.
Lemma lem7240394 : term476 = True.
Proof. exact (TRANS (@lem7240389) (@lem7240393)). Qed.
Lemma lem7240395 : True = term476.
Proof. exact (SYM (@lem7240394)). Qed.
Lemma lem7240396 : term476.
Proof. exact (EQ_MP (@lem7240395) (@lem0)). Qed.
Lemma lem7240397 : term820.
Proof. exact (@lem7240386 (@lem7240396)). Qed.
Lemma lem7240399 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240400 : term476 = term477.
Proof. exact (@lem7240399 (NUMERAL 0) term189). Qed.
Lemma lem7240401 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240402 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240403 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240402 h1) (fun h1 : term477 = True => @lem7240401)). Qed.
Lemma lem7240404 : term477 = True.
Proof. exact (EQ_MP (@lem7240403) (@lem7240401)). Qed.
Lemma lem7240405 : term476 = True.
Proof. exact (TRANS (@lem7240400) (@lem7240404)). Qed.
Lemma lem7240406 : True = term476.
Proof. exact (SYM (@lem7240405)). Qed.
Lemma lem7240407 : term476.
Proof. exact (EQ_MP (@lem7240406) (@lem0)). Qed.
Lemma lem7240408 : term818 = term821.
Proof. exact (@lem7240397 (@lem7240407)). Qed.
Lemma lem7240410 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7240411 : term439 = term444.
Proof. exact (@lem7240410 term189 term189). Qed.
Lemma lem7240412 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240413 : term405 = term189.
Proof. exact (EQ_MP (@lem7240412) (@lem940073)). Qed.
Lemma lem7240414 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240415 : term403 = term340.
Proof. exact (MK_COMB (@lem7240414) (@lem7240413)). Qed.
Lemma lem7240416 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7240417 : term444 = term393.
Proof. exact (MK_COMB (@lem7240416) (@lem7240415)). Qed.
Lemma lem7240418 : term439 = term393.
Proof. exact (TRANS (@lem7240411) (@lem7240417)). Qed.
Lemma lem7240420 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240421 : term488 = term328.
Proof. exact (@lem7240420 term189). Qed.
Lemma lem7240422 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7240423 : term822 = term330.
Proof. exact (MK_COMB (@lem7240422) (@lem7240421)). Qed.
Lemma lem7240424 : term821 = term816.
Proof. exact (MK_COMB (@lem7240423) (@lem7240418)). Qed.
Lemma lem7240426 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7240427 : term816 = term825.
Proof. exact (@lem7240426 (NUMERAL 0) term189). Qed.
Lemma lem7240428 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240429 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7240430 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240429 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7240428)). Qed.
Lemma lem7240431 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7240430) (@lem7240428)). Qed.
Lemma lem7240432 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7240433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7240434 : term826 = (and True).
Proof. exact (MK_COMB (@lem7240433) (@lem7240432)). Qed.
Lemma lem7240435 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7240434) (@lem7240431)). Qed.
Lemma lem7240437 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7240438 : term825 = False.
Proof. exact (TRANS (@lem7240435) (@lem7240437)). Qed.
Lemma lem7240439 : term816 = False.
Proof. exact (TRANS (@lem7240427) (@lem7240438)). Qed.
Lemma lem7240440 : term821 = False.
Proof. exact (TRANS (@lem7240424) (@lem7240439)). Qed.
Lemma lem7240441 : term818 = False.
Proof. exact (TRANS (@lem7240408) (@lem7240440)). Qed.
Lemma lem7240442 : term816 = False.
Proof. exact (TRANS (@lem7240385) (@lem7240441)). Qed.
Lemma lem7240443 : term815 = False.
Proof. exact (TRANS (@lem7240376) (@lem7240442)). Qed.
Lemma lem7240444 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term845 _96884 _96883 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7240443) (@lem7240373 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240445 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term752 _96884 _96883 _96885 _96886) : False.
Proof. exact (or_elim (@lem7239494 _96884 _96883 _96885 _96886 h1) (fun h0 : term827 _96884 _96883 _96885 _96886 => @lem7239969 _96884 _96883 _96885 _96886 h0) (fun h0 : term845 _96884 _96883 _96885 _96886 => @lem7240444 _96884 _96883 _96885 _96886 h0)). Qed.
Lemma lem7240446 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term748 _96884 _96883 _96885 _96886) : term748 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7240447 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term846 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7240448 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term749 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240447 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240450 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term713 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240448 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240452 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term677 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240450 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240454 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term641 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240452 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240456 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term605 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240454 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240458 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term569 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240456 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240460 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term432 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240458 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240461 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term536 _96883 _96885 _96886.
Proof. exact (proj1 (@lem7240458 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240463 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term459 _96883 _96886.
Proof. exact (proj1 (@lem7240461 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240465 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term428 _96883 _96886.
Proof. exact (proj1 (@lem7240460 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240467 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7240468 : term764 = term476.
Proof. exact (@lem7240467 term328 term340). Qed.
Lemma lem7240470 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240471 : term340 = term438.
Proof. exact (@lem7240470 term189). Qed.
Lemma lem7240473 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240474 : term328 = term390.
Proof. exact (@lem7240473 (NUMERAL 0)). Qed.
Lemma lem7240475 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240476 : term765 = term766.
Proof. exact (MK_COMB (@lem7240475) (@lem7240474)). Qed.
Lemma lem7240477 : term476 = term767.
Proof. exact (MK_COMB (@lem7240476) (@lem7240471)). Qed.
Lemma lem7240478 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7240480 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240481 : term476 = term477.
Proof. exact (@lem7240480 (NUMERAL 0) term189). Qed.
Lemma lem7240482 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240483 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240484 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240483 h1) (fun h1 : term477 = True => @lem7240482)). Qed.
Lemma lem7240485 : term477 = True.
Proof. exact (EQ_MP (@lem7240484) (@lem7240482)). Qed.
Lemma lem7240486 : term476 = True.
Proof. exact (TRANS (@lem7240481) (@lem7240485)). Qed.
Lemma lem7240487 : True = term476.
Proof. exact (SYM (@lem7240486)). Qed.
Lemma lem7240488 : term476.
Proof. exact (EQ_MP (@lem7240487) (@lem0)). Qed.
Lemma lem7240489 : term769.
Proof. exact (@lem7240478 (@lem7240488)). Qed.
Lemma lem7240491 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240492 : term476 = term477.
Proof. exact (@lem7240491 (NUMERAL 0) term189). Qed.
Lemma lem7240493 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240494 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240495 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240494 h1) (fun h1 : term477 = True => @lem7240493)). Qed.
Lemma lem7240496 : term477 = True.
Proof. exact (EQ_MP (@lem7240495) (@lem7240493)). Qed.
Lemma lem7240497 : term476 = True.
Proof. exact (TRANS (@lem7240492) (@lem7240496)). Qed.
Lemma lem7240498 : True = term476.
Proof. exact (SYM (@lem7240497)). Qed.
Lemma lem7240499 : term476.
Proof. exact (EQ_MP (@lem7240498) (@lem0)). Qed.
Lemma lem7240500 : term767 = term770.
Proof. exact (@lem7240489 (@lem7240499)). Qed.
Lemma lem7240502 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240503 : term402 = term403.
Proof. exact (@lem7240502 term189 term189). Qed.
Lemma lem7240504 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240505 : term405 = term189.
Proof. exact (EQ_MP (@lem7240504) (@lem940073)). Qed.
Lemma lem7240506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240507 : term403 = term340.
Proof. exact (MK_COMB (@lem7240506) (@lem7240505)). Qed.
Lemma lem7240508 : term402 = term340.
Proof. exact (TRANS (@lem7240503) (@lem7240507)). Qed.
Lemma lem7240510 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240511 : term488 = term328.
Proof. exact (@lem7240510 term189). Qed.
Lemma lem7240512 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240513 : term771 = term765.
Proof. exact (MK_COMB (@lem7240512) (@lem7240511)). Qed.
Lemma lem7240514 : term770 = term476.
Proof. exact (MK_COMB (@lem7240513) (@lem7240508)). Qed.
Lemma lem7240516 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240517 : term476 = term477.
Proof. exact (@lem7240516 (NUMERAL 0) term189). Qed.
Lemma lem7240518 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240519 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240520 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240519 h1) (fun h1 : term477 = True => @lem7240518)). Qed.
Lemma lem7240521 : term477 = True.
Proof. exact (EQ_MP (@lem7240520) (@lem7240518)). Qed.
Lemma lem7240522 : term476 = True.
Proof. exact (TRANS (@lem7240517) (@lem7240521)). Qed.
Lemma lem7240523 : term770 = True.
Proof. exact (TRANS (@lem7240514) (@lem7240522)). Qed.
Lemma lem7240524 : term767 = True.
Proof. exact (TRANS (@lem7240500) (@lem7240523)). Qed.
Lemma lem7240525 : term476 = True.
Proof. exact (TRANS (@lem7240477) (@lem7240524)). Qed.
Lemma lem7240526 : term764 = True.
Proof. exact (TRANS (@lem7240468) (@lem7240525)). Qed.
Lemma lem7240527 : True = term764.
Proof. exact (SYM (@lem7240526)). Qed.
Lemma lem7240528 : term764.
Proof. exact (EQ_MP (@lem7240527) (@lem0)). Qed.
Lemma lem7240529 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term828 _96883 _96886.
Proof. exact (conj (@lem7240528) (@lem7240463 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240531 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7240532 (_96883 : int) (_96886 : int) : term829 _96883 _96886.
Proof. exact (@lem7240531 term340 (term449 _96883 _96886)). Qed.
Lemma lem7240533 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term830 _96883 _96886.
Proof. exact (@lem7240532 _96883 _96886 (@lem7240529 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240534 (_96883 : int) (_96886 : int) : (term831 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (@lem1982733 (term449 _96883 _96886)). Qed.
Lemma lem7240535 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7240536 (_96883 : int) (_96886 : int) : (term832 _96883 _96886) = (term458 _96883 _96886).
Proof. exact (MK_COMB (@lem7240535) (@lem7240534 _96883 _96886)). Qed.
Lemma lem7240537 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7240538 (_96883 : int) (_96886 : int) : (term830 _96883 _96886) = (term459 _96883 _96886).
Proof. exact (MK_COMB (@lem7240536 _96883 _96886) (@lem7240537)). Qed.
Lemma lem7240539 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term459 _96883 _96886.
Proof. exact (EQ_MP (@lem7240538 _96883 _96886) (@lem7240533 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240541 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7240542 : term764 = term476.
Proof. exact (@lem7240541 term328 term340). Qed.
Lemma lem7240544 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240545 : term340 = term438.
Proof. exact (@lem7240544 term189). Qed.
Lemma lem7240547 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240548 : term328 = term390.
Proof. exact (@lem7240547 (NUMERAL 0)). Qed.
Lemma lem7240549 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240550 : term765 = term766.
Proof. exact (MK_COMB (@lem7240549) (@lem7240548)). Qed.
Lemma lem7240551 : term476 = term767.
Proof. exact (MK_COMB (@lem7240550) (@lem7240545)). Qed.
Lemma lem7240552 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7240554 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240555 : term476 = term477.
Proof. exact (@lem7240554 (NUMERAL 0) term189). Qed.
Lemma lem7240556 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240557 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240558 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240557 h1) (fun h1 : term477 = True => @lem7240556)). Qed.
Lemma lem7240559 : term477 = True.
Proof. exact (EQ_MP (@lem7240558) (@lem7240556)). Qed.
Lemma lem7240560 : term476 = True.
Proof. exact (TRANS (@lem7240555) (@lem7240559)). Qed.
Lemma lem7240561 : True = term476.
Proof. exact (SYM (@lem7240560)). Qed.
Lemma lem7240562 : term476.
Proof. exact (EQ_MP (@lem7240561) (@lem0)). Qed.
Lemma lem7240563 : term769.
Proof. exact (@lem7240552 (@lem7240562)). Qed.
Lemma lem7240565 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240566 : term476 = term477.
Proof. exact (@lem7240565 (NUMERAL 0) term189). Qed.
Lemma lem7240567 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240568 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240569 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240568 h1) (fun h1 : term477 = True => @lem7240567)). Qed.
Lemma lem7240570 : term477 = True.
Proof. exact (EQ_MP (@lem7240569) (@lem7240567)). Qed.
Lemma lem7240571 : term476 = True.
Proof. exact (TRANS (@lem7240566) (@lem7240570)). Qed.
Lemma lem7240572 : True = term476.
Proof. exact (SYM (@lem7240571)). Qed.
Lemma lem7240573 : term476.
Proof. exact (EQ_MP (@lem7240572) (@lem0)). Qed.
Lemma lem7240574 : term767 = term770.
Proof. exact (@lem7240563 (@lem7240573)). Qed.
Lemma lem7240576 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240577 : term402 = term403.
Proof. exact (@lem7240576 term189 term189). Qed.
Lemma lem7240578 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240579 : term405 = term189.
Proof. exact (EQ_MP (@lem7240578) (@lem940073)). Qed.
Lemma lem7240580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240581 : term403 = term340.
Proof. exact (MK_COMB (@lem7240580) (@lem7240579)). Qed.
Lemma lem7240582 : term402 = term340.
Proof. exact (TRANS (@lem7240577) (@lem7240581)). Qed.
Lemma lem7240584 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240585 : term488 = term328.
Proof. exact (@lem7240584 term189). Qed.
Lemma lem7240586 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240587 : term771 = term765.
Proof. exact (MK_COMB (@lem7240586) (@lem7240585)). Qed.
Lemma lem7240588 : term770 = term476.
Proof. exact (MK_COMB (@lem7240587) (@lem7240582)). Qed.
Lemma lem7240590 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240591 : term476 = term477.
Proof. exact (@lem7240590 (NUMERAL 0) term189). Qed.
Lemma lem7240592 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240593 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240594 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240593 h1) (fun h1 : term477 = True => @lem7240592)). Qed.
Lemma lem7240595 : term477 = True.
Proof. exact (EQ_MP (@lem7240594) (@lem7240592)). Qed.
Lemma lem7240596 : term476 = True.
Proof. exact (TRANS (@lem7240591) (@lem7240595)). Qed.
Lemma lem7240597 : term770 = True.
Proof. exact (TRANS (@lem7240588) (@lem7240596)). Qed.
Lemma lem7240598 : term767 = True.
Proof. exact (TRANS (@lem7240574) (@lem7240597)). Qed.
Lemma lem7240599 : term476 = True.
Proof. exact (TRANS (@lem7240551) (@lem7240598)). Qed.
Lemma lem7240600 : term764 = True.
Proof. exact (TRANS (@lem7240542) (@lem7240599)). Qed.
Lemma lem7240601 : True = term764.
Proof. exact (SYM (@lem7240600)). Qed.
Lemma lem7240602 : term764.
Proof. exact (EQ_MP (@lem7240601) (@lem0)). Qed.
Lemma lem7240603 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term833 _96883 _96886.
Proof. exact (conj (@lem7240602) (@lem7240465 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240605 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7240606 (_96883 : int) (_96886 : int) : term834 _96883 _96886.
Proof. exact (@lem7240605 term340 (term425 _96883 _96886)). Qed.
Lemma lem7240607 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term835 _96883 _96886.
Proof. exact (@lem7240606 _96883 _96886 (@lem7240603 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240608 (_96883 : int) (_96886 : int) : (term836 _96883 _96886) = (term425 _96883 _96886).
Proof. exact (@lem1982733 (term425 _96883 _96886)). Qed.
Lemma lem7240609 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7240610 (_96883 : int) (_96886 : int) : (term837 _96883 _96886) = (term427 _96883 _96886).
Proof. exact (MK_COMB (@lem7240609) (@lem7240608 _96883 _96886)). Qed.
Lemma lem7240611 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7240612 (_96883 : int) (_96886 : int) : (term835 _96883 _96886) = (term428 _96883 _96886).
Proof. exact (MK_COMB (@lem7240610 _96883 _96886) (@lem7240611)). Qed.
Lemma lem7240613 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term428 _96883 _96886.
Proof. exact (EQ_MP (@lem7240612 _96883 _96886) (@lem7240607 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240614 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term838 _96883 _96886.
Proof. exact (conj (@lem7240613 _96884 _96883 _96885 _96886 h1) (@lem7240539 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240616 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7240617 (_96883 : int) (_96886 : int) : term839 _96883 _96886.
Proof. exact (@lem7240616 (term425 _96883 _96886) (term449 _96883 _96886)). Qed.
Lemma lem7240618 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term840 _96883 _96886.
Proof. exact (@lem7240617 _96883 _96886 (@lem7240614 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240619 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = (term842 _96883 _96886).
Proof. exact (@lem1982753 (term418 _96883) (real_of_int _96883) (real_of_int _96886) (term448 _96886)). Qed.
Lemma lem7240620 (_96883 : int) : (term789 _96883) = (term790 _96883).
Proof. exact (@lem1982713 term393 (real_of_int _96883)). Qed.
Lemma lem7240622 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240623 : term340 = term438.
Proof. exact (@lem7240622 term189). Qed.
Lemma lem7240625 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7240626 : term393 = term394.
Proof. exact (@lem7240625 term189). Qed.
Lemma lem7240627 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240628 : term791 = term792.
Proof. exact (MK_COMB (@lem7240627) (@lem7240626)). Qed.
Lemma lem7240629 : term793 = term794.
Proof. exact (MK_COMB (@lem7240628) (@lem7240623)). Qed.
Lemma lem7240630 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7240632 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240633 : term476 = term477.
Proof. exact (@lem7240632 (NUMERAL 0) term189). Qed.
Lemma lem7240634 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240635 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240636 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240635 h1) (fun h1 : term477 = True => @lem7240634)). Qed.
Lemma lem7240637 : term477 = True.
Proof. exact (EQ_MP (@lem7240636) (@lem7240634)). Qed.
Lemma lem7240638 : term476 = True.
Proof. exact (TRANS (@lem7240633) (@lem7240637)). Qed.
Lemma lem7240639 : True = term476.
Proof. exact (SYM (@lem7240638)). Qed.
Lemma lem7240640 : term476.
Proof. exact (EQ_MP (@lem7240639) (@lem0)). Qed.
Lemma lem7240641 : term796.
Proof. exact (@lem7240630 (@lem7240640)). Qed.
Lemma lem7240643 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240644 : term476 = term477.
Proof. exact (@lem7240643 (NUMERAL 0) term189). Qed.
Lemma lem7240645 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240646 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240647 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240646 h1) (fun h1 : term477 = True => @lem7240645)). Qed.
Lemma lem7240648 : term477 = True.
Proof. exact (EQ_MP (@lem7240647) (@lem7240645)). Qed.
Lemma lem7240649 : term476 = True.
Proof. exact (TRANS (@lem7240644) (@lem7240648)). Qed.
Lemma lem7240650 : True = term476.
Proof. exact (SYM (@lem7240649)). Qed.
Lemma lem7240651 : term476.
Proof. exact (EQ_MP (@lem7240650) (@lem0)). Qed.
Lemma lem7240652 : term797.
Proof. exact (@lem7240641 (@lem7240651)). Qed.
Lemma lem7240654 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240655 : term476 = term477.
Proof. exact (@lem7240654 (NUMERAL 0) term189). Qed.
Lemma lem7240656 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240657 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240658 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240657 h1) (fun h1 : term477 = True => @lem7240656)). Qed.
Lemma lem7240659 : term477 = True.
Proof. exact (EQ_MP (@lem7240658) (@lem7240656)). Qed.
Lemma lem7240660 : term476 = True.
Proof. exact (TRANS (@lem7240655) (@lem7240659)). Qed.
Lemma lem7240661 : True = term476.
Proof. exact (SYM (@lem7240660)). Qed.
Lemma lem7240662 : term476.
Proof. exact (EQ_MP (@lem7240661) (@lem0)). Qed.
Lemma lem7240663 : term798.
Proof. exact (@lem7240652 (@lem7240662)). Qed.
Lemma lem7240665 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240666 : term402 = term403.
Proof. exact (@lem7240665 term189 term189). Qed.
Lemma lem7240667 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240668 : term405 = term189.
Proof. exact (EQ_MP (@lem7240667) (@lem940073)). Qed.
Lemma lem7240669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240670 : term403 = term340.
Proof. exact (MK_COMB (@lem7240669) (@lem7240668)). Qed.
Lemma lem7240671 : term402 = term340.
Proof. exact (TRANS (@lem7240666) (@lem7240670)). Qed.
Lemma lem7240673 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7240674 : term439 = term444.
Proof. exact (@lem7240673 term189 term189). Qed.
Lemma lem7240675 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240676 : term405 = term189.
Proof. exact (EQ_MP (@lem7240675) (@lem940073)). Qed.
Lemma lem7240677 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240678 : term403 = term340.
Proof. exact (MK_COMB (@lem7240677) (@lem7240676)). Qed.
Lemma lem7240679 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7240680 : term444 = term393.
Proof. exact (MK_COMB (@lem7240679) (@lem7240678)). Qed.
Lemma lem7240681 : term439 = term393.
Proof. exact (TRANS (@lem7240674) (@lem7240680)). Qed.
Lemma lem7240682 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240683 : term799 = term791.
Proof. exact (MK_COMB (@lem7240682) (@lem7240681)). Qed.
Lemma lem7240684 : term800 = term793.
Proof. exact (MK_COMB (@lem7240683) (@lem7240671)). Qed.
Lemma lem7240686 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7240687 : term793 = term328.
Proof. exact (@lem7240686 term189). Qed.
Lemma lem7240688 : term800 = term328.
Proof. exact (TRANS (@lem7240684) (@lem7240687)). Qed.
Lemma lem7240689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240690 : term802 = term486.
Proof. exact (MK_COMB (@lem7240689) (@lem7240688)). Qed.
Lemma lem7240691 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7240692 : term803 = term488.
Proof. exact (MK_COMB (@lem7240690) (@lem7240691)). Qed.
Lemma lem7240694 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240695 : term488 = term328.
Proof. exact (@lem7240694 term189). Qed.
Lemma lem7240696 : term803 = term328.
Proof. exact (TRANS (@lem7240692) (@lem7240695)). Qed.
Lemma lem7240698 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240699 : term402 = term403.
Proof. exact (@lem7240698 term189 term189). Qed.
Lemma lem7240700 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240701 : term405 = term189.
Proof. exact (EQ_MP (@lem7240700) (@lem940073)). Qed.
Lemma lem7240702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240703 : term403 = term340.
Proof. exact (MK_COMB (@lem7240702) (@lem7240701)). Qed.
Lemma lem7240704 : term402 = term340.
Proof. exact (TRANS (@lem7240699) (@lem7240703)). Qed.
Lemma lem7240705 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7240706 : term490 = term488.
Proof. exact (MK_COMB (@lem7240705) (@lem7240704)). Qed.
Lemma lem7240708 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240709 : term488 = term328.
Proof. exact (@lem7240708 term189). Qed.
Lemma lem7240710 : term490 = term328.
Proof. exact (TRANS (@lem7240706) (@lem7240709)). Qed.
Lemma lem7240711 : term328 = term490.
Proof. exact (SYM (@lem7240710)). Qed.
Lemma lem7240712 : term803 = term490.
Proof. exact (TRANS (@lem7240696) (@lem7240711)). Qed.
Lemma lem7240713 : term794 = term390.
Proof. exact (@lem7240663 (@lem7240712)). Qed.
Lemma lem7240714 : term793 = term390.
Proof. exact (TRANS (@lem7240629) (@lem7240713)). Qed.
Lemma lem7240716 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7240717 : term390 = term328.
Proof. exact (@lem7240716 term328). Qed.
Lemma lem7240718 : term793 = term328.
Proof. exact (TRANS (@lem7240714) (@lem7240717)). Qed.
Lemma lem7240719 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240720 : term804 = term486.
Proof. exact (MK_COMB (@lem7240719) (@lem7240718)). Qed.
Lemma lem7240721 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7240722 (_96883 : int) : (term790 _96883) = (term805 _96883).
Proof. exact (MK_COMB (@lem7240720) (@lem7240721 _96883)). Qed.
Lemma lem7240723 (_96883 : int) : (term789 _96883) = (term805 _96883).
Proof. exact (TRANS (@lem7240620 _96883) (@lem7240722 _96883)). Qed.
Lemma lem7240724 (_96883 : int) : (term805 _96883) = term328.
Proof. exact (@lem1982719 (real_of_int _96883)). Qed.
Lemma lem7240725 (_96883 : int) : (term789 _96883) = term328.
Proof. exact (TRANS (@lem7240723 _96883) (@lem7240724 _96883)). Qed.
Lemma lem7240726 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240727 (_96883 : int) : (term806 _96883) = term807.
Proof. exact (MK_COMB (@lem7240726) (@lem7240725 _96883)). Qed.
Lemma lem7240728 (_96886 : int) : (term843 _96886) = (term809 _96886).
Proof. exact (@lem1982763 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7240729 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7240731 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240732 : term340 = term438.
Proof. exact (@lem7240731 term189). Qed.
Lemma lem7240734 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7240735 : term393 = term394.
Proof. exact (@lem7240734 term189). Qed.
Lemma lem7240736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240737 : term791 = term792.
Proof. exact (MK_COMB (@lem7240736) (@lem7240735)). Qed.
Lemma lem7240738 : term793 = term794.
Proof. exact (MK_COMB (@lem7240737) (@lem7240732)). Qed.
Lemma lem7240739 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7240741 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240742 : term476 = term477.
Proof. exact (@lem7240741 (NUMERAL 0) term189). Qed.
Lemma lem7240743 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240744 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240745 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240744 h1) (fun h1 : term477 = True => @lem7240743)). Qed.
Lemma lem7240746 : term477 = True.
Proof. exact (EQ_MP (@lem7240745) (@lem7240743)). Qed.
Lemma lem7240747 : term476 = True.
Proof. exact (TRANS (@lem7240742) (@lem7240746)). Qed.
Lemma lem7240748 : True = term476.
Proof. exact (SYM (@lem7240747)). Qed.
Lemma lem7240749 : term476.
Proof. exact (EQ_MP (@lem7240748) (@lem0)). Qed.
Lemma lem7240750 : term796.
Proof. exact (@lem7240739 (@lem7240749)). Qed.
Lemma lem7240752 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240753 : term476 = term477.
Proof. exact (@lem7240752 (NUMERAL 0) term189). Qed.
Lemma lem7240754 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240755 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240756 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240755 h1) (fun h1 : term477 = True => @lem7240754)). Qed.
Lemma lem7240757 : term477 = True.
Proof. exact (EQ_MP (@lem7240756) (@lem7240754)). Qed.
Lemma lem7240758 : term476 = True.
Proof. exact (TRANS (@lem7240753) (@lem7240757)). Qed.
Lemma lem7240759 : True = term476.
Proof. exact (SYM (@lem7240758)). Qed.
Lemma lem7240760 : term476.
Proof. exact (EQ_MP (@lem7240759) (@lem0)). Qed.
Lemma lem7240761 : term797.
Proof. exact (@lem7240750 (@lem7240760)). Qed.
Lemma lem7240763 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240764 : term476 = term477.
Proof. exact (@lem7240763 (NUMERAL 0) term189). Qed.
Lemma lem7240765 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240766 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240767 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240766 h1) (fun h1 : term477 = True => @lem7240765)). Qed.
Lemma lem7240768 : term477 = True.
Proof. exact (EQ_MP (@lem7240767) (@lem7240765)). Qed.
Lemma lem7240769 : term476 = True.
Proof. exact (TRANS (@lem7240764) (@lem7240768)). Qed.
Lemma lem7240770 : True = term476.
Proof. exact (SYM (@lem7240769)). Qed.
Lemma lem7240771 : term476.
Proof. exact (EQ_MP (@lem7240770) (@lem0)). Qed.
Lemma lem7240772 : term798.
Proof. exact (@lem7240761 (@lem7240771)). Qed.
Lemma lem7240774 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240775 : term402 = term403.
Proof. exact (@lem7240774 term189 term189). Qed.
Lemma lem7240776 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240777 : term405 = term189.
Proof. exact (EQ_MP (@lem7240776) (@lem940073)). Qed.
Lemma lem7240778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240779 : term403 = term340.
Proof. exact (MK_COMB (@lem7240778) (@lem7240777)). Qed.
Lemma lem7240780 : term402 = term340.
Proof. exact (TRANS (@lem7240775) (@lem7240779)). Qed.
Lemma lem7240782 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7240783 : term439 = term444.
Proof. exact (@lem7240782 term189 term189). Qed.
Lemma lem7240784 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240785 : term405 = term189.
Proof. exact (EQ_MP (@lem7240784) (@lem940073)). Qed.
Lemma lem7240786 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240787 : term403 = term340.
Proof. exact (MK_COMB (@lem7240786) (@lem7240785)). Qed.
Lemma lem7240788 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7240789 : term444 = term393.
Proof. exact (MK_COMB (@lem7240788) (@lem7240787)). Qed.
Lemma lem7240790 : term439 = term393.
Proof. exact (TRANS (@lem7240783) (@lem7240789)). Qed.
Lemma lem7240791 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240792 : term799 = term791.
Proof. exact (MK_COMB (@lem7240791) (@lem7240790)). Qed.
Lemma lem7240793 : term800 = term793.
Proof. exact (MK_COMB (@lem7240792) (@lem7240780)). Qed.
Lemma lem7240795 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7240796 : term793 = term328.
Proof. exact (@lem7240795 term189). Qed.
Lemma lem7240797 : term800 = term328.
Proof. exact (TRANS (@lem7240793) (@lem7240796)). Qed.
Lemma lem7240798 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240799 : term802 = term486.
Proof. exact (MK_COMB (@lem7240798) (@lem7240797)). Qed.
Lemma lem7240800 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7240801 : term803 = term488.
Proof. exact (MK_COMB (@lem7240799) (@lem7240800)). Qed.
Lemma lem7240803 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240804 : term488 = term328.
Proof. exact (@lem7240803 term189). Qed.
Lemma lem7240805 : term803 = term328.
Proof. exact (TRANS (@lem7240801) (@lem7240804)). Qed.
Lemma lem7240807 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240808 : term402 = term403.
Proof. exact (@lem7240807 term189 term189). Qed.
Lemma lem7240809 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240810 : term405 = term189.
Proof. exact (EQ_MP (@lem7240809) (@lem940073)). Qed.
Lemma lem7240811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240812 : term403 = term340.
Proof. exact (MK_COMB (@lem7240811) (@lem7240810)). Qed.
Lemma lem7240813 : term402 = term340.
Proof. exact (TRANS (@lem7240808) (@lem7240812)). Qed.
Lemma lem7240814 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7240815 : term490 = term488.
Proof. exact (MK_COMB (@lem7240814) (@lem7240813)). Qed.
Lemma lem7240817 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240818 : term488 = term328.
Proof. exact (@lem7240817 term189). Qed.
Lemma lem7240819 : term490 = term328.
Proof. exact (TRANS (@lem7240815) (@lem7240818)). Qed.
Lemma lem7240820 : term328 = term490.
Proof. exact (SYM (@lem7240819)). Qed.
Lemma lem7240821 : term803 = term490.
Proof. exact (TRANS (@lem7240805) (@lem7240820)). Qed.
Lemma lem7240822 : term794 = term390.
Proof. exact (@lem7240772 (@lem7240821)). Qed.
Lemma lem7240823 : term793 = term390.
Proof. exact (TRANS (@lem7240738) (@lem7240822)). Qed.
Lemma lem7240825 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7240826 : term390 = term328.
Proof. exact (@lem7240825 term328). Qed.
Lemma lem7240827 : term793 = term328.
Proof. exact (TRANS (@lem7240823) (@lem7240826)). Qed.
Lemma lem7240828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7240829 : term804 = term486.
Proof. exact (MK_COMB (@lem7240828) (@lem7240827)). Qed.
Lemma lem7240830 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7240831 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7240829) (@lem7240830 _96886)). Qed.
Lemma lem7240832 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7240729 _96886) (@lem7240831 _96886)). Qed.
Lemma lem7240833 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7240834 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7240832 _96886) (@lem7240833 _96886)). Qed.
Lemma lem7240835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7240836 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7240835) (@lem7240834 _96886)). Qed.
Lemma lem7240837 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7240838 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7240836 _96886) (@lem7240837)). Qed.
Lemma lem7240839 (_96886 : int) : (term843 _96886) = term812.
Proof. exact (TRANS (@lem7240728 _96886) (@lem7240838 _96886)). Qed.
Lemma lem7240840 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7240841 (_96886 : int) : (term843 _96886) = term393.
Proof. exact (TRANS (@lem7240839 _96886) (@lem7240840)). Qed.
Lemma lem7240842 (_96883 : int) (_96886 : int) : (term842 _96883 _96886) = term812.
Proof. exact (MK_COMB (@lem7240727 _96883) (@lem7240841 _96886)). Qed.
Lemma lem7240843 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = term812.
Proof. exact (TRANS (@lem7240619 _96883 _96886) (@lem7240842 _96883 _96886)). Qed.
Lemma lem7240844 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7240845 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = term393.
Proof. exact (TRANS (@lem7240843 _96883 _96886) (@lem7240844)). Qed.
Lemma lem7240846 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7240847 (_96883 : int) (_96886 : int) : (term844 _96883 _96886) = term814.
Proof. exact (MK_COMB (@lem7240846) (@lem7240845 _96883 _96886)). Qed.
Lemma lem7240848 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7240849 (_96883 : int) (_96886 : int) : (term840 _96883 _96886) = term815.
Proof. exact (MK_COMB (@lem7240847 _96883 _96886) (@lem7240848)). Qed.
Lemma lem7240850 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7240849 _96883 _96886) (@lem7240618 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240852 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7240853 : term815 = term816.
Proof. exact (@lem7240852 term328 term393). Qed.
Lemma lem7240855 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7240856 : term393 = term394.
Proof. exact (@lem7240855 term189). Qed.
Lemma lem7240858 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240859 : term328 = term390.
Proof. exact (@lem7240858 (NUMERAL 0)). Qed.
Lemma lem7240860 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7240861 : term330 = term817.
Proof. exact (MK_COMB (@lem7240860) (@lem7240859)). Qed.
Lemma lem7240862 : term816 = term818.
Proof. exact (MK_COMB (@lem7240861) (@lem7240856)). Qed.
Lemma lem7240863 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7240865 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240866 : term476 = term477.
Proof. exact (@lem7240865 (NUMERAL 0) term189). Qed.
Lemma lem7240867 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240868 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240869 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240868 h1) (fun h1 : term477 = True => @lem7240867)). Qed.
Lemma lem7240870 : term477 = True.
Proof. exact (EQ_MP (@lem7240869) (@lem7240867)). Qed.
Lemma lem7240871 : term476 = True.
Proof. exact (TRANS (@lem7240866) (@lem7240870)). Qed.
Lemma lem7240872 : True = term476.
Proof. exact (SYM (@lem7240871)). Qed.
Lemma lem7240873 : term476.
Proof. exact (EQ_MP (@lem7240872) (@lem0)). Qed.
Lemma lem7240874 : term820.
Proof. exact (@lem7240863 (@lem7240873)). Qed.
Lemma lem7240876 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240877 : term476 = term477.
Proof. exact (@lem7240876 (NUMERAL 0) term189). Qed.
Lemma lem7240878 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240879 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240880 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240879 h1) (fun h1 : term477 = True => @lem7240878)). Qed.
Lemma lem7240881 : term477 = True.
Proof. exact (EQ_MP (@lem7240880) (@lem7240878)). Qed.
Lemma lem7240882 : term476 = True.
Proof. exact (TRANS (@lem7240877) (@lem7240881)). Qed.
Lemma lem7240883 : True = term476.
Proof. exact (SYM (@lem7240882)). Qed.
Lemma lem7240884 : term476.
Proof. exact (EQ_MP (@lem7240883) (@lem0)). Qed.
Lemma lem7240885 : term818 = term821.
Proof. exact (@lem7240874 (@lem7240884)). Qed.
Lemma lem7240887 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7240888 : term439 = term444.
Proof. exact (@lem7240887 term189 term189). Qed.
Lemma lem7240889 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240890 : term405 = term189.
Proof. exact (EQ_MP (@lem7240889) (@lem940073)). Qed.
Lemma lem7240891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240892 : term403 = term340.
Proof. exact (MK_COMB (@lem7240891) (@lem7240890)). Qed.
Lemma lem7240893 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7240894 : term444 = term393.
Proof. exact (MK_COMB (@lem7240893) (@lem7240892)). Qed.
Lemma lem7240895 : term439 = term393.
Proof. exact (TRANS (@lem7240888) (@lem7240894)). Qed.
Lemma lem7240897 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240898 : term488 = term328.
Proof. exact (@lem7240897 term189). Qed.
Lemma lem7240899 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7240900 : term822 = term330.
Proof. exact (MK_COMB (@lem7240899) (@lem7240898)). Qed.
Lemma lem7240901 : term821 = term816.
Proof. exact (MK_COMB (@lem7240900) (@lem7240895)). Qed.
Lemma lem7240903 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7240904 : term816 = term825.
Proof. exact (@lem7240903 (NUMERAL 0) term189). Qed.
Lemma lem7240905 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240906 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7240907 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240906 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7240905)). Qed.
Lemma lem7240908 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7240907) (@lem7240905)). Qed.
Lemma lem7240909 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7240910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7240911 : term826 = (and True).
Proof. exact (MK_COMB (@lem7240910) (@lem7240909)). Qed.
Lemma lem7240912 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7240911) (@lem7240908)). Qed.
Lemma lem7240914 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7240915 : term825 = False.
Proof. exact (TRANS (@lem7240912) (@lem7240914)). Qed.
Lemma lem7240916 : term816 = False.
Proof. exact (TRANS (@lem7240904) (@lem7240915)). Qed.
Lemma lem7240917 : term821 = False.
Proof. exact (TRANS (@lem7240901) (@lem7240916)). Qed.
Lemma lem7240918 : term818 = False.
Proof. exact (TRANS (@lem7240885) (@lem7240917)). Qed.
Lemma lem7240919 : term816 = False.
Proof. exact (TRANS (@lem7240862) (@lem7240918)). Qed.
Lemma lem7240920 : term815 = False.
Proof. exact (TRANS (@lem7240853) (@lem7240919)). Qed.
Lemma lem7240921 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term846 _96884 _96883 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7240920) (@lem7240850 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240922 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term847 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7240923 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term750 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240922 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240925 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term714 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240923 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240927 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term678 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240925 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240929 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term642 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240927 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240931 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term606 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240929 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240933 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term570 _96884 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240931 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240935 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term432 _96883 _96885 _96886.
Proof. exact (proj2 (@lem7240933 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240936 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term537 _96884 _96885 _96886.
Proof. exact (proj1 (@lem7240933 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240937 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term453 _96885 _96886.
Proof. exact (proj2 (@lem7240936 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240939 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term430 _96885 _96886.
Proof. exact (proj2 (@lem7240935 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7240942 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7240943 : term764 = term476.
Proof. exact (@lem7240942 term328 term340). Qed.
Lemma lem7240945 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240946 : term340 = term438.
Proof. exact (@lem7240945 term189). Qed.
Lemma lem7240948 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7240949 : term328 = term390.
Proof. exact (@lem7240948 (NUMERAL 0)). Qed.
Lemma lem7240950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240951 : term765 = term766.
Proof. exact (MK_COMB (@lem7240950) (@lem7240949)). Qed.
Lemma lem7240952 : term476 = term767.
Proof. exact (MK_COMB (@lem7240951) (@lem7240946)). Qed.
Lemma lem7240953 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7240955 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240956 : term476 = term477.
Proof. exact (@lem7240955 (NUMERAL 0) term189). Qed.
Lemma lem7240957 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240958 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240959 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240958 h1) (fun h1 : term477 = True => @lem7240957)). Qed.
Lemma lem7240960 : term477 = True.
Proof. exact (EQ_MP (@lem7240959) (@lem7240957)). Qed.
Lemma lem7240961 : term476 = True.
Proof. exact (TRANS (@lem7240956) (@lem7240960)). Qed.
Lemma lem7240962 : True = term476.
Proof. exact (SYM (@lem7240961)). Qed.
Lemma lem7240963 : term476.
Proof. exact (EQ_MP (@lem7240962) (@lem0)). Qed.
Lemma lem7240964 : term769.
Proof. exact (@lem7240953 (@lem7240963)). Qed.
Lemma lem7240966 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240967 : term476 = term477.
Proof. exact (@lem7240966 (NUMERAL 0) term189). Qed.
Lemma lem7240968 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240969 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240970 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240969 h1) (fun h1 : term477 = True => @lem7240968)). Qed.
Lemma lem7240971 : term477 = True.
Proof. exact (EQ_MP (@lem7240970) (@lem7240968)). Qed.
Lemma lem7240972 : term476 = True.
Proof. exact (TRANS (@lem7240967) (@lem7240971)). Qed.
Lemma lem7240973 : True = term476.
Proof. exact (SYM (@lem7240972)). Qed.
Lemma lem7240974 : term476.
Proof. exact (EQ_MP (@lem7240973) (@lem0)). Qed.
Lemma lem7240975 : term767 = term770.
Proof. exact (@lem7240964 (@lem7240974)). Qed.
Lemma lem7240977 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7240978 : term402 = term403.
Proof. exact (@lem7240977 term189 term189). Qed.
Lemma lem7240979 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7240980 : term405 = term189.
Proof. exact (EQ_MP (@lem7240979) (@lem940073)). Qed.
Lemma lem7240981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7240982 : term403 = term340.
Proof. exact (MK_COMB (@lem7240981) (@lem7240980)). Qed.
Lemma lem7240983 : term402 = term340.
Proof. exact (TRANS (@lem7240978) (@lem7240982)). Qed.
Lemma lem7240985 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7240986 : term488 = term328.
Proof. exact (@lem7240985 term189). Qed.
Lemma lem7240987 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7240988 : term771 = term765.
Proof. exact (MK_COMB (@lem7240987) (@lem7240986)). Qed.
Lemma lem7240989 : term770 = term476.
Proof. exact (MK_COMB (@lem7240988) (@lem7240983)). Qed.
Lemma lem7240991 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7240992 : term476 = term477.
Proof. exact (@lem7240991 (NUMERAL 0) term189). Qed.
Lemma lem7240993 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7240994 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7240995 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7240994 h1) (fun h1 : term477 = True => @lem7240993)). Qed.
Lemma lem7240996 : term477 = True.
Proof. exact (EQ_MP (@lem7240995) (@lem7240993)). Qed.
Lemma lem7240997 : term476 = True.
Proof. exact (TRANS (@lem7240992) (@lem7240996)). Qed.
Lemma lem7240998 : term770 = True.
Proof. exact (TRANS (@lem7240989) (@lem7240997)). Qed.
Lemma lem7240999 : term767 = True.
Proof. exact (TRANS (@lem7240975) (@lem7240998)). Qed.
Lemma lem7241000 : term476 = True.
Proof. exact (TRANS (@lem7240952) (@lem7240999)). Qed.
Lemma lem7241001 : term764 = True.
Proof. exact (TRANS (@lem7240943) (@lem7241000)). Qed.
Lemma lem7241002 : True = term764.
Proof. exact (SYM (@lem7241001)). Qed.
Lemma lem7241003 : term764.
Proof. exact (EQ_MP (@lem7241002) (@lem0)). Qed.
Lemma lem7241004 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term772 _96885 _96886.
Proof. exact (conj (@lem7241003) (@lem7240939 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241006 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7241007 (_96885 : int) (_96886 : int) : term774 _96885 _96886.
Proof. exact (@lem7241006 term340 (term424 _96885 _96886)). Qed.
Lemma lem7241008 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term775 _96885 _96886.
Proof. exact (@lem7241007 _96885 _96886 (@lem7241004 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241009 (_96885 : int) (_96886 : int) : (term776 _96885 _96886) = (term424 _96885 _96886).
Proof. exact (@lem1982733 (term424 _96885 _96886)). Qed.
Lemma lem7241010 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241011 (_96885 : int) (_96886 : int) : (term777 _96885 _96886) = (term429 _96885 _96886).
Proof. exact (MK_COMB (@lem7241010) (@lem7241009 _96885 _96886)). Qed.
Lemma lem7241012 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241013 (_96885 : int) (_96886 : int) : (term775 _96885 _96886) = (term430 _96885 _96886).
Proof. exact (MK_COMB (@lem7241011 _96885 _96886) (@lem7241012)). Qed.
Lemma lem7241014 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term430 _96885 _96886.
Proof. exact (EQ_MP (@lem7241013 _96885 _96886) (@lem7241008 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241016 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7241017 : term764 = term476.
Proof. exact (@lem7241016 term328 term340). Qed.
Lemma lem7241019 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241020 : term340 = term438.
Proof. exact (@lem7241019 term189). Qed.
Lemma lem7241022 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241023 : term328 = term390.
Proof. exact (@lem7241022 (NUMERAL 0)). Qed.
Lemma lem7241024 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241025 : term765 = term766.
Proof. exact (MK_COMB (@lem7241024) (@lem7241023)). Qed.
Lemma lem7241026 : term476 = term767.
Proof. exact (MK_COMB (@lem7241025) (@lem7241020)). Qed.
Lemma lem7241027 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7241029 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241030 : term476 = term477.
Proof. exact (@lem7241029 (NUMERAL 0) term189). Qed.
Lemma lem7241031 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241032 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241033 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241032 h1) (fun h1 : term477 = True => @lem7241031)). Qed.
Lemma lem7241034 : term477 = True.
Proof. exact (EQ_MP (@lem7241033) (@lem7241031)). Qed.
Lemma lem7241035 : term476 = True.
Proof. exact (TRANS (@lem7241030) (@lem7241034)). Qed.
Lemma lem7241036 : True = term476.
Proof. exact (SYM (@lem7241035)). Qed.
Lemma lem7241037 : term476.
Proof. exact (EQ_MP (@lem7241036) (@lem0)). Qed.
Lemma lem7241038 : term769.
Proof. exact (@lem7241027 (@lem7241037)). Qed.
Lemma lem7241040 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241041 : term476 = term477.
Proof. exact (@lem7241040 (NUMERAL 0) term189). Qed.
Lemma lem7241042 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241043 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241044 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241043 h1) (fun h1 : term477 = True => @lem7241042)). Qed.
Lemma lem7241045 : term477 = True.
Proof. exact (EQ_MP (@lem7241044) (@lem7241042)). Qed.
Lemma lem7241046 : term476 = True.
Proof. exact (TRANS (@lem7241041) (@lem7241045)). Qed.
Lemma lem7241047 : True = term476.
Proof. exact (SYM (@lem7241046)). Qed.
Lemma lem7241048 : term476.
Proof. exact (EQ_MP (@lem7241047) (@lem0)). Qed.
Lemma lem7241049 : term767 = term770.
Proof. exact (@lem7241038 (@lem7241048)). Qed.
Lemma lem7241051 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241052 : term402 = term403.
Proof. exact (@lem7241051 term189 term189). Qed.
Lemma lem7241053 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241054 : term405 = term189.
Proof. exact (EQ_MP (@lem7241053) (@lem940073)). Qed.
Lemma lem7241055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241056 : term403 = term340.
Proof. exact (MK_COMB (@lem7241055) (@lem7241054)). Qed.
Lemma lem7241057 : term402 = term340.
Proof. exact (TRANS (@lem7241052) (@lem7241056)). Qed.
Lemma lem7241059 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241060 : term488 = term328.
Proof. exact (@lem7241059 term189). Qed.
Lemma lem7241061 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241062 : term771 = term765.
Proof. exact (MK_COMB (@lem7241061) (@lem7241060)). Qed.
Lemma lem7241063 : term770 = term476.
Proof. exact (MK_COMB (@lem7241062) (@lem7241057)). Qed.
Lemma lem7241065 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241066 : term476 = term477.
Proof. exact (@lem7241065 (NUMERAL 0) term189). Qed.
Lemma lem7241067 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241068 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241069 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241068 h1) (fun h1 : term477 = True => @lem7241067)). Qed.
Lemma lem7241070 : term477 = True.
Proof. exact (EQ_MP (@lem7241069) (@lem7241067)). Qed.
Lemma lem7241071 : term476 = True.
Proof. exact (TRANS (@lem7241066) (@lem7241070)). Qed.
Lemma lem7241072 : term770 = True.
Proof. exact (TRANS (@lem7241063) (@lem7241071)). Qed.
Lemma lem7241073 : term767 = True.
Proof. exact (TRANS (@lem7241049) (@lem7241072)). Qed.
Lemma lem7241074 : term476 = True.
Proof. exact (TRANS (@lem7241026) (@lem7241073)). Qed.
Lemma lem7241075 : term764 = True.
Proof. exact (TRANS (@lem7241017) (@lem7241074)). Qed.
Lemma lem7241076 : True = term764.
Proof. exact (SYM (@lem7241075)). Qed.
Lemma lem7241077 : term764.
Proof. exact (EQ_MP (@lem7241076) (@lem0)). Qed.
Lemma lem7241078 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term778 _96885 _96886.
Proof. exact (conj (@lem7241077) (@lem7240937 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241080 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7241081 (_96885 : int) (_96886 : int) : term779 _96885 _96886.
Proof. exact (@lem7241080 term340 (term450 _96885 _96886)). Qed.
Lemma lem7241082 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term780 _96885 _96886.
Proof. exact (@lem7241081 _96885 _96886 (@lem7241078 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241083 (_96885 : int) (_96886 : int) : (term781 _96885 _96886) = (term450 _96885 _96886).
Proof. exact (@lem1982733 (term450 _96885 _96886)). Qed.
Lemma lem7241084 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241085 (_96885 : int) (_96886 : int) : (term782 _96885 _96886) = (term452 _96885 _96886).
Proof. exact (MK_COMB (@lem7241084) (@lem7241083 _96885 _96886)). Qed.
Lemma lem7241086 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241087 (_96885 : int) (_96886 : int) : (term780 _96885 _96886) = (term453 _96885 _96886).
Proof. exact (MK_COMB (@lem7241085 _96885 _96886) (@lem7241086)). Qed.
Lemma lem7241088 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term453 _96885 _96886.
Proof. exact (EQ_MP (@lem7241087 _96885 _96886) (@lem7241082 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241089 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term541 _96885 _96886.
Proof. exact (conj (@lem7241088 _96884 _96883 _96885 _96886 h1) (@lem7241014 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241091 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7241092 (_96885 : int) (_96886 : int) : term784 _96885 _96886.
Proof. exact (@lem7241091 (term450 _96885 _96886) (term424 _96885 _96886)). Qed.
Lemma lem7241093 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term785 _96885 _96886.
Proof. exact (@lem7241092 _96885 _96886 (@lem7241089 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241094 (_96885 : int) (_96886 : int) : (term786 _96885 _96886) = (term787 _96885 _96886).
Proof. exact (@lem1982753 (term418 _96885) (real_of_int _96885) (term788 _96886) (term418 _96886)). Qed.
Lemma lem7241095 (_96885 : int) : (term789 _96885) = (term790 _96885).
Proof. exact (@lem1982713 term393 (real_of_int _96885)). Qed.
Lemma lem7241097 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241098 : term340 = term438.
Proof. exact (@lem7241097 term189). Qed.
Lemma lem7241100 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7241101 : term393 = term394.
Proof. exact (@lem7241100 term189). Qed.
Lemma lem7241102 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241103 : term791 = term792.
Proof. exact (MK_COMB (@lem7241102) (@lem7241101)). Qed.
Lemma lem7241104 : term793 = term794.
Proof. exact (MK_COMB (@lem7241103) (@lem7241098)). Qed.
Lemma lem7241105 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7241107 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241108 : term476 = term477.
Proof. exact (@lem7241107 (NUMERAL 0) term189). Qed.
Lemma lem7241109 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241110 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241111 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241110 h1) (fun h1 : term477 = True => @lem7241109)). Qed.
Lemma lem7241112 : term477 = True.
Proof. exact (EQ_MP (@lem7241111) (@lem7241109)). Qed.
Lemma lem7241113 : term476 = True.
Proof. exact (TRANS (@lem7241108) (@lem7241112)). Qed.
Lemma lem7241114 : True = term476.
Proof. exact (SYM (@lem7241113)). Qed.
Lemma lem7241115 : term476.
Proof. exact (EQ_MP (@lem7241114) (@lem0)). Qed.
Lemma lem7241116 : term796.
Proof. exact (@lem7241105 (@lem7241115)). Qed.
Lemma lem7241118 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241119 : term476 = term477.
Proof. exact (@lem7241118 (NUMERAL 0) term189). Qed.
Lemma lem7241120 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241121 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241122 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241121 h1) (fun h1 : term477 = True => @lem7241120)). Qed.
Lemma lem7241123 : term477 = True.
Proof. exact (EQ_MP (@lem7241122) (@lem7241120)). Qed.
Lemma lem7241124 : term476 = True.
Proof. exact (TRANS (@lem7241119) (@lem7241123)). Qed.
Lemma lem7241125 : True = term476.
Proof. exact (SYM (@lem7241124)). Qed.
Lemma lem7241126 : term476.
Proof. exact (EQ_MP (@lem7241125) (@lem0)). Qed.
Lemma lem7241127 : term797.
Proof. exact (@lem7241116 (@lem7241126)). Qed.
Lemma lem7241129 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241130 : term476 = term477.
Proof. exact (@lem7241129 (NUMERAL 0) term189). Qed.
Lemma lem7241131 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241132 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241133 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241132 h1) (fun h1 : term477 = True => @lem7241131)). Qed.
Lemma lem7241134 : term477 = True.
Proof. exact (EQ_MP (@lem7241133) (@lem7241131)). Qed.
Lemma lem7241135 : term476 = True.
Proof. exact (TRANS (@lem7241130) (@lem7241134)). Qed.
Lemma lem7241136 : True = term476.
Proof. exact (SYM (@lem7241135)). Qed.
Lemma lem7241137 : term476.
Proof. exact (EQ_MP (@lem7241136) (@lem0)). Qed.
Lemma lem7241138 : term798.
Proof. exact (@lem7241127 (@lem7241137)). Qed.
Lemma lem7241140 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241141 : term402 = term403.
Proof. exact (@lem7241140 term189 term189). Qed.
Lemma lem7241142 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241143 : term405 = term189.
Proof. exact (EQ_MP (@lem7241142) (@lem940073)). Qed.
Lemma lem7241144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241145 : term403 = term340.
Proof. exact (MK_COMB (@lem7241144) (@lem7241143)). Qed.
Lemma lem7241146 : term402 = term340.
Proof. exact (TRANS (@lem7241141) (@lem7241145)). Qed.
Lemma lem7241148 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7241149 : term439 = term444.
Proof. exact (@lem7241148 term189 term189). Qed.
Lemma lem7241150 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241151 : term405 = term189.
Proof. exact (EQ_MP (@lem7241150) (@lem940073)). Qed.
Lemma lem7241152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241153 : term403 = term340.
Proof. exact (MK_COMB (@lem7241152) (@lem7241151)). Qed.
Lemma lem7241154 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7241155 : term444 = term393.
Proof. exact (MK_COMB (@lem7241154) (@lem7241153)). Qed.
Lemma lem7241156 : term439 = term393.
Proof. exact (TRANS (@lem7241149) (@lem7241155)). Qed.
Lemma lem7241157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241158 : term799 = term791.
Proof. exact (MK_COMB (@lem7241157) (@lem7241156)). Qed.
Lemma lem7241159 : term800 = term793.
Proof. exact (MK_COMB (@lem7241158) (@lem7241146)). Qed.
Lemma lem7241161 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7241162 : term793 = term328.
Proof. exact (@lem7241161 term189). Qed.
Lemma lem7241163 : term800 = term328.
Proof. exact (TRANS (@lem7241159) (@lem7241162)). Qed.
Lemma lem7241164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241165 : term802 = term486.
Proof. exact (MK_COMB (@lem7241164) (@lem7241163)). Qed.
Lemma lem7241166 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7241167 : term803 = term488.
Proof. exact (MK_COMB (@lem7241165) (@lem7241166)). Qed.
Lemma lem7241169 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241170 : term488 = term328.
Proof. exact (@lem7241169 term189). Qed.
Lemma lem7241171 : term803 = term328.
Proof. exact (TRANS (@lem7241167) (@lem7241170)). Qed.
Lemma lem7241173 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241174 : term402 = term403.
Proof. exact (@lem7241173 term189 term189). Qed.
Lemma lem7241175 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241176 : term405 = term189.
Proof. exact (EQ_MP (@lem7241175) (@lem940073)). Qed.
Lemma lem7241177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241178 : term403 = term340.
Proof. exact (MK_COMB (@lem7241177) (@lem7241176)). Qed.
Lemma lem7241179 : term402 = term340.
Proof. exact (TRANS (@lem7241174) (@lem7241178)). Qed.
Lemma lem7241180 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7241181 : term490 = term488.
Proof. exact (MK_COMB (@lem7241180) (@lem7241179)). Qed.
Lemma lem7241183 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241184 : term488 = term328.
Proof. exact (@lem7241183 term189). Qed.
Lemma lem7241185 : term490 = term328.
Proof. exact (TRANS (@lem7241181) (@lem7241184)). Qed.
Lemma lem7241186 : term328 = term490.
Proof. exact (SYM (@lem7241185)). Qed.
Lemma lem7241187 : term803 = term490.
Proof. exact (TRANS (@lem7241171) (@lem7241186)). Qed.
Lemma lem7241188 : term794 = term390.
Proof. exact (@lem7241138 (@lem7241187)). Qed.
Lemma lem7241189 : term793 = term390.
Proof. exact (TRANS (@lem7241104) (@lem7241188)). Qed.
Lemma lem7241191 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7241192 : term390 = term328.
Proof. exact (@lem7241191 term328). Qed.
Lemma lem7241193 : term793 = term328.
Proof. exact (TRANS (@lem7241189) (@lem7241192)). Qed.
Lemma lem7241194 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241195 : term804 = term486.
Proof. exact (MK_COMB (@lem7241194) (@lem7241193)). Qed.
Lemma lem7241196 (_96885 : int) : (real_of_int _96885) = (real_of_int _96885).
Proof. exact (eq_refl (real_of_int _96885)). Qed.
Lemma lem7241197 (_96885 : int) : (term790 _96885) = (term805 _96885).
Proof. exact (MK_COMB (@lem7241195) (@lem7241196 _96885)). Qed.
Lemma lem7241198 (_96885 : int) : (term789 _96885) = (term805 _96885).
Proof. exact (TRANS (@lem7241095 _96885) (@lem7241197 _96885)). Qed.
Lemma lem7241199 (_96885 : int) : (term805 _96885) = term328.
Proof. exact (@lem1982719 (real_of_int _96885)). Qed.
Lemma lem7241200 (_96885 : int) : (term789 _96885) = term328.
Proof. exact (TRANS (@lem7241198 _96885) (@lem7241199 _96885)). Qed.
Lemma lem7241201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241202 (_96885 : int) : (term806 _96885) = term807.
Proof. exact (MK_COMB (@lem7241201) (@lem7241200 _96885)). Qed.
Lemma lem7241203 (_96886 : int) : (term808 _96886) = (term809 _96886).
Proof. exact (@lem1982759 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7241204 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7241206 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241207 : term340 = term438.
Proof. exact (@lem7241206 term189). Qed.
Lemma lem7241209 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7241210 : term393 = term394.
Proof. exact (@lem7241209 term189). Qed.
Lemma lem7241211 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241212 : term791 = term792.
Proof. exact (MK_COMB (@lem7241211) (@lem7241210)). Qed.
Lemma lem7241213 : term793 = term794.
Proof. exact (MK_COMB (@lem7241212) (@lem7241207)). Qed.
Lemma lem7241214 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7241216 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241217 : term476 = term477.
Proof. exact (@lem7241216 (NUMERAL 0) term189). Qed.
Lemma lem7241218 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241219 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241220 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241219 h1) (fun h1 : term477 = True => @lem7241218)). Qed.
Lemma lem7241221 : term477 = True.
Proof. exact (EQ_MP (@lem7241220) (@lem7241218)). Qed.
Lemma lem7241222 : term476 = True.
Proof. exact (TRANS (@lem7241217) (@lem7241221)). Qed.
Lemma lem7241223 : True = term476.
Proof. exact (SYM (@lem7241222)). Qed.
Lemma lem7241224 : term476.
Proof. exact (EQ_MP (@lem7241223) (@lem0)). Qed.
Lemma lem7241225 : term796.
Proof. exact (@lem7241214 (@lem7241224)). Qed.
Lemma lem7241227 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241228 : term476 = term477.
Proof. exact (@lem7241227 (NUMERAL 0) term189). Qed.
Lemma lem7241229 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241230 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241231 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241230 h1) (fun h1 : term477 = True => @lem7241229)). Qed.
Lemma lem7241232 : term477 = True.
Proof. exact (EQ_MP (@lem7241231) (@lem7241229)). Qed.
Lemma lem7241233 : term476 = True.
Proof. exact (TRANS (@lem7241228) (@lem7241232)). Qed.
Lemma lem7241234 : True = term476.
Proof. exact (SYM (@lem7241233)). Qed.
Lemma lem7241235 : term476.
Proof. exact (EQ_MP (@lem7241234) (@lem0)). Qed.
Lemma lem7241236 : term797.
Proof. exact (@lem7241225 (@lem7241235)). Qed.
Lemma lem7241238 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241239 : term476 = term477.
Proof. exact (@lem7241238 (NUMERAL 0) term189). Qed.
Lemma lem7241240 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241241 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241242 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241241 h1) (fun h1 : term477 = True => @lem7241240)). Qed.
Lemma lem7241243 : term477 = True.
Proof. exact (EQ_MP (@lem7241242) (@lem7241240)). Qed.
Lemma lem7241244 : term476 = True.
Proof. exact (TRANS (@lem7241239) (@lem7241243)). Qed.
Lemma lem7241245 : True = term476.
Proof. exact (SYM (@lem7241244)). Qed.
Lemma lem7241246 : term476.
Proof. exact (EQ_MP (@lem7241245) (@lem0)). Qed.
Lemma lem7241247 : term798.
Proof. exact (@lem7241236 (@lem7241246)). Qed.
Lemma lem7241249 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241250 : term402 = term403.
Proof. exact (@lem7241249 term189 term189). Qed.
Lemma lem7241251 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241252 : term405 = term189.
Proof. exact (EQ_MP (@lem7241251) (@lem940073)). Qed.
Lemma lem7241253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241254 : term403 = term340.
Proof. exact (MK_COMB (@lem7241253) (@lem7241252)). Qed.
Lemma lem7241255 : term402 = term340.
Proof. exact (TRANS (@lem7241250) (@lem7241254)). Qed.
Lemma lem7241257 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7241258 : term439 = term444.
Proof. exact (@lem7241257 term189 term189). Qed.
Lemma lem7241259 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241260 : term405 = term189.
Proof. exact (EQ_MP (@lem7241259) (@lem940073)). Qed.
Lemma lem7241261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241262 : term403 = term340.
Proof. exact (MK_COMB (@lem7241261) (@lem7241260)). Qed.
Lemma lem7241263 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7241264 : term444 = term393.
Proof. exact (MK_COMB (@lem7241263) (@lem7241262)). Qed.
Lemma lem7241265 : term439 = term393.
Proof. exact (TRANS (@lem7241258) (@lem7241264)). Qed.
Lemma lem7241266 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241267 : term799 = term791.
Proof. exact (MK_COMB (@lem7241266) (@lem7241265)). Qed.
Lemma lem7241268 : term800 = term793.
Proof. exact (MK_COMB (@lem7241267) (@lem7241255)). Qed.
Lemma lem7241270 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7241271 : term793 = term328.
Proof. exact (@lem7241270 term189). Qed.
Lemma lem7241272 : term800 = term328.
Proof. exact (TRANS (@lem7241268) (@lem7241271)). Qed.
Lemma lem7241273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241274 : term802 = term486.
Proof. exact (MK_COMB (@lem7241273) (@lem7241272)). Qed.
Lemma lem7241275 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7241276 : term803 = term488.
Proof. exact (MK_COMB (@lem7241274) (@lem7241275)). Qed.
Lemma lem7241278 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241279 : term488 = term328.
Proof. exact (@lem7241278 term189). Qed.
Lemma lem7241280 : term803 = term328.
Proof. exact (TRANS (@lem7241276) (@lem7241279)). Qed.
Lemma lem7241282 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241283 : term402 = term403.
Proof. exact (@lem7241282 term189 term189). Qed.
Lemma lem7241284 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241285 : term405 = term189.
Proof. exact (EQ_MP (@lem7241284) (@lem940073)). Qed.
Lemma lem7241286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241287 : term403 = term340.
Proof. exact (MK_COMB (@lem7241286) (@lem7241285)). Qed.
Lemma lem7241288 : term402 = term340.
Proof. exact (TRANS (@lem7241283) (@lem7241287)). Qed.
Lemma lem7241289 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7241290 : term490 = term488.
Proof. exact (MK_COMB (@lem7241289) (@lem7241288)). Qed.
Lemma lem7241292 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241293 : term488 = term328.
Proof. exact (@lem7241292 term189). Qed.
Lemma lem7241294 : term490 = term328.
Proof. exact (TRANS (@lem7241290) (@lem7241293)). Qed.
Lemma lem7241295 : term328 = term490.
Proof. exact (SYM (@lem7241294)). Qed.
Lemma lem7241296 : term803 = term490.
Proof. exact (TRANS (@lem7241280) (@lem7241295)). Qed.
Lemma lem7241297 : term794 = term390.
Proof. exact (@lem7241247 (@lem7241296)). Qed.
Lemma lem7241298 : term793 = term390.
Proof. exact (TRANS (@lem7241213) (@lem7241297)). Qed.
Lemma lem7241300 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7241301 : term390 = term328.
Proof. exact (@lem7241300 term328). Qed.
Lemma lem7241302 : term793 = term328.
Proof. exact (TRANS (@lem7241298) (@lem7241301)). Qed.
Lemma lem7241303 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241304 : term804 = term486.
Proof. exact (MK_COMB (@lem7241303) (@lem7241302)). Qed.
Lemma lem7241305 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7241306 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7241304) (@lem7241305 _96886)). Qed.
Lemma lem7241307 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7241204 _96886) (@lem7241306 _96886)). Qed.
Lemma lem7241308 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7241309 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7241307 _96886) (@lem7241308 _96886)). Qed.
Lemma lem7241310 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241311 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7241310) (@lem7241309 _96886)). Qed.
Lemma lem7241312 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7241313 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7241311 _96886) (@lem7241312)). Qed.
Lemma lem7241314 (_96886 : int) : (term808 _96886) = term812.
Proof. exact (TRANS (@lem7241203 _96886) (@lem7241313 _96886)). Qed.
Lemma lem7241315 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7241316 (_96886 : int) : (term808 _96886) = term393.
Proof. exact (TRANS (@lem7241314 _96886) (@lem7241315)). Qed.
Lemma lem7241317 (_96885 : int) (_96886 : int) : (term787 _96885 _96886) = term812.
Proof. exact (MK_COMB (@lem7241202 _96885) (@lem7241316 _96886)). Qed.
Lemma lem7241318 (_96885 : int) (_96886 : int) : (term786 _96885 _96886) = term812.
Proof. exact (TRANS (@lem7241094 _96885 _96886) (@lem7241317 _96885 _96886)). Qed.
Lemma lem7241319 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7241320 (_96885 : int) (_96886 : int) : (term786 _96885 _96886) = term393.
Proof. exact (TRANS (@lem7241318 _96885 _96886) (@lem7241319)). Qed.
Lemma lem7241321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241322 (_96885 : int) (_96886 : int) : (term813 _96885 _96886) = term814.
Proof. exact (MK_COMB (@lem7241321) (@lem7241320 _96885 _96886)). Qed.
Lemma lem7241323 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241324 (_96885 : int) (_96886 : int) : (term785 _96885 _96886) = term815.
Proof. exact (MK_COMB (@lem7241322 _96885 _96886) (@lem7241323)). Qed.
Lemma lem7241325 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7241324 _96885 _96886) (@lem7241093 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241327 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7241328 : term815 = term816.
Proof. exact (@lem7241327 term328 term393). Qed.
Lemma lem7241330 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7241331 : term393 = term394.
Proof. exact (@lem7241330 term189). Qed.
Lemma lem7241333 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241334 : term328 = term390.
Proof. exact (@lem7241333 (NUMERAL 0)). Qed.
Lemma lem7241335 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7241336 : term330 = term817.
Proof. exact (MK_COMB (@lem7241335) (@lem7241334)). Qed.
Lemma lem7241337 : term816 = term818.
Proof. exact (MK_COMB (@lem7241336) (@lem7241331)). Qed.
Lemma lem7241338 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7241340 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241341 : term476 = term477.
Proof. exact (@lem7241340 (NUMERAL 0) term189). Qed.
Lemma lem7241342 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241343 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241344 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241343 h1) (fun h1 : term477 = True => @lem7241342)). Qed.
Lemma lem7241345 : term477 = True.
Proof. exact (EQ_MP (@lem7241344) (@lem7241342)). Qed.
Lemma lem7241346 : term476 = True.
Proof. exact (TRANS (@lem7241341) (@lem7241345)). Qed.
Lemma lem7241347 : True = term476.
Proof. exact (SYM (@lem7241346)). Qed.
Lemma lem7241348 : term476.
Proof. exact (EQ_MP (@lem7241347) (@lem0)). Qed.
Lemma lem7241349 : term820.
Proof. exact (@lem7241338 (@lem7241348)). Qed.
Lemma lem7241351 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241352 : term476 = term477.
Proof. exact (@lem7241351 (NUMERAL 0) term189). Qed.
Lemma lem7241353 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241354 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241355 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241354 h1) (fun h1 : term477 = True => @lem7241353)). Qed.
Lemma lem7241356 : term477 = True.
Proof. exact (EQ_MP (@lem7241355) (@lem7241353)). Qed.
Lemma lem7241357 : term476 = True.
Proof. exact (TRANS (@lem7241352) (@lem7241356)). Qed.
Lemma lem7241358 : True = term476.
Proof. exact (SYM (@lem7241357)). Qed.
Lemma lem7241359 : term476.
Proof. exact (EQ_MP (@lem7241358) (@lem0)). Qed.
Lemma lem7241360 : term818 = term821.
Proof. exact (@lem7241349 (@lem7241359)). Qed.
Lemma lem7241362 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7241363 : term439 = term444.
Proof. exact (@lem7241362 term189 term189). Qed.
Lemma lem7241364 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241365 : term405 = term189.
Proof. exact (EQ_MP (@lem7241364) (@lem940073)). Qed.
Lemma lem7241366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241367 : term403 = term340.
Proof. exact (MK_COMB (@lem7241366) (@lem7241365)). Qed.
Lemma lem7241368 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7241369 : term444 = term393.
Proof. exact (MK_COMB (@lem7241368) (@lem7241367)). Qed.
Lemma lem7241370 : term439 = term393.
Proof. exact (TRANS (@lem7241363) (@lem7241369)). Qed.
Lemma lem7241372 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241373 : term488 = term328.
Proof. exact (@lem7241372 term189). Qed.
Lemma lem7241374 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7241375 : term822 = term330.
Proof. exact (MK_COMB (@lem7241374) (@lem7241373)). Qed.
Lemma lem7241376 : term821 = term816.
Proof. exact (MK_COMB (@lem7241375) (@lem7241370)). Qed.
Lemma lem7241378 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7241379 : term816 = term825.
Proof. exact (@lem7241378 (NUMERAL 0) term189). Qed.
Lemma lem7241380 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241381 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7241382 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241381 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7241380)). Qed.
Lemma lem7241383 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7241382) (@lem7241380)). Qed.
Lemma lem7241384 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7241385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7241386 : term826 = (and True).
Proof. exact (MK_COMB (@lem7241385) (@lem7241384)). Qed.
Lemma lem7241387 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7241386) (@lem7241383)). Qed.
Lemma lem7241389 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7241390 : term825 = False.
Proof. exact (TRANS (@lem7241387) (@lem7241389)). Qed.
Lemma lem7241391 : term816 = False.
Proof. exact (TRANS (@lem7241379) (@lem7241390)). Qed.
Lemma lem7241392 : term821 = False.
Proof. exact (TRANS (@lem7241376) (@lem7241391)). Qed.
Lemma lem7241393 : term818 = False.
Proof. exact (TRANS (@lem7241360) (@lem7241392)). Qed.
Lemma lem7241394 : term816 = False.
Proof. exact (TRANS (@lem7241337) (@lem7241393)). Qed.
Lemma lem7241395 : term815 = False.
Proof. exact (TRANS (@lem7241328) (@lem7241394)). Qed.
Lemma lem7241396 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term847 _96884 _96883 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7241395) (@lem7241325 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7241397 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term748 _96884 _96883 _96885 _96886) : False.
Proof. exact (or_elim (@lem7240446 _96884 _96883 _96885 _96886 h1) (fun h0 : term846 _96884 _96883 _96885 _96886 => @lem7240921 _96884 _96883 _96885 _96886 h0) (fun h0 : term847 _96884 _96883 _96885 _96886 => @lem7241396 _96884 _96883 _96885 _96886 h0)). Qed.
Lemma lem7241398 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term757 _96884 _96883 _96885 _96886) : False.
Proof. exact (or_elim (@lem7239493 _96884 _96883 _96885 _96886 h1) (fun h0 : term752 _96884 _96883 _96885 _96886 => @lem7240445 _96884 _96883 _96885 _96886 h0) (fun h0 : term748 _96884 _96883 _96885 _96886 => @lem7241397 _96884 _96883 _96885 _96886 h0)). Qed.
Lemma lem7241399 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term744 _96883 _96884 _96885 _96886) : term744 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7241400 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term739 _96884 _96885 _96883 _96886) : term739 _96884 _96885 _96883 _96886.
Proof. exact (h1). Qed.
Lemma lem7241401 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term848 _96885 _96884 _96883 _96886.
Proof. exact (h1). Qed.
Lemma lem7241402 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term740 _96885 _96884 _96883 _96886.
Proof. exact (proj2 (@lem7241401 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241404 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term704 _96885 _96884 _96883 _96886.
Proof. exact (proj2 (@lem7241402 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241406 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term668 _96885 _96884 _96883 _96886.
Proof. exact (proj2 (@lem7241404 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241408 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term632 _96885 _96884 _96883 _96886.
Proof. exact (proj2 (@lem7241406 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241410 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term596 _96885 _96884 _96883 _96886.
Proof. exact (proj2 (@lem7241408 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241412 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term560 _96884 _96883 _96886.
Proof. exact (proj2 (@lem7241410 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241414 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term459 _96883 _96886.
Proof. exact (proj2 (@lem7241412 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241415 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term432 _96883 _96884 _96886.
Proof. exact (proj1 (@lem7241412 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241417 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term428 _96883 _96886.
Proof. exact (proj1 (@lem7241415 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241419 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7241420 : term764 = term476.
Proof. exact (@lem7241419 term328 term340). Qed.
Lemma lem7241422 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241423 : term340 = term438.
Proof. exact (@lem7241422 term189). Qed.
Lemma lem7241425 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241426 : term328 = term390.
Proof. exact (@lem7241425 (NUMERAL 0)). Qed.
Lemma lem7241427 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241428 : term765 = term766.
Proof. exact (MK_COMB (@lem7241427) (@lem7241426)). Qed.
Lemma lem7241429 : term476 = term767.
Proof. exact (MK_COMB (@lem7241428) (@lem7241423)). Qed.
Lemma lem7241430 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7241432 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241433 : term476 = term477.
Proof. exact (@lem7241432 (NUMERAL 0) term189). Qed.
Lemma lem7241434 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241435 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241436 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241435 h1) (fun h1 : term477 = True => @lem7241434)). Qed.
Lemma lem7241437 : term477 = True.
Proof. exact (EQ_MP (@lem7241436) (@lem7241434)). Qed.
Lemma lem7241438 : term476 = True.
Proof. exact (TRANS (@lem7241433) (@lem7241437)). Qed.
Lemma lem7241439 : True = term476.
Proof. exact (SYM (@lem7241438)). Qed.
Lemma lem7241440 : term476.
Proof. exact (EQ_MP (@lem7241439) (@lem0)). Qed.
Lemma lem7241441 : term769.
Proof. exact (@lem7241430 (@lem7241440)). Qed.
Lemma lem7241443 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241444 : term476 = term477.
Proof. exact (@lem7241443 (NUMERAL 0) term189). Qed.
Lemma lem7241445 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241446 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241447 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241446 h1) (fun h1 : term477 = True => @lem7241445)). Qed.
Lemma lem7241448 : term477 = True.
Proof. exact (EQ_MP (@lem7241447) (@lem7241445)). Qed.
Lemma lem7241449 : term476 = True.
Proof. exact (TRANS (@lem7241444) (@lem7241448)). Qed.
Lemma lem7241450 : True = term476.
Proof. exact (SYM (@lem7241449)). Qed.
Lemma lem7241451 : term476.
Proof. exact (EQ_MP (@lem7241450) (@lem0)). Qed.
Lemma lem7241452 : term767 = term770.
Proof. exact (@lem7241441 (@lem7241451)). Qed.
Lemma lem7241454 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241455 : term402 = term403.
Proof. exact (@lem7241454 term189 term189). Qed.
Lemma lem7241456 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241457 : term405 = term189.
Proof. exact (EQ_MP (@lem7241456) (@lem940073)). Qed.
Lemma lem7241458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241459 : term403 = term340.
Proof. exact (MK_COMB (@lem7241458) (@lem7241457)). Qed.
Lemma lem7241460 : term402 = term340.
Proof. exact (TRANS (@lem7241455) (@lem7241459)). Qed.
Lemma lem7241462 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241463 : term488 = term328.
Proof. exact (@lem7241462 term189). Qed.
Lemma lem7241464 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241465 : term771 = term765.
Proof. exact (MK_COMB (@lem7241464) (@lem7241463)). Qed.
Lemma lem7241466 : term770 = term476.
Proof. exact (MK_COMB (@lem7241465) (@lem7241460)). Qed.
Lemma lem7241468 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241469 : term476 = term477.
Proof. exact (@lem7241468 (NUMERAL 0) term189). Qed.
Lemma lem7241470 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241471 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241472 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241471 h1) (fun h1 : term477 = True => @lem7241470)). Qed.
Lemma lem7241473 : term477 = True.
Proof. exact (EQ_MP (@lem7241472) (@lem7241470)). Qed.
Lemma lem7241474 : term476 = True.
Proof. exact (TRANS (@lem7241469) (@lem7241473)). Qed.
Lemma lem7241475 : term770 = True.
Proof. exact (TRANS (@lem7241466) (@lem7241474)). Qed.
Lemma lem7241476 : term767 = True.
Proof. exact (TRANS (@lem7241452) (@lem7241475)). Qed.
Lemma lem7241477 : term476 = True.
Proof. exact (TRANS (@lem7241429) (@lem7241476)). Qed.
Lemma lem7241478 : term764 = True.
Proof. exact (TRANS (@lem7241420) (@lem7241477)). Qed.
Lemma lem7241479 : True = term764.
Proof. exact (SYM (@lem7241478)). Qed.
Lemma lem7241480 : term764.
Proof. exact (EQ_MP (@lem7241479) (@lem0)). Qed.
Lemma lem7241481 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term828 _96883 _96886.
Proof. exact (conj (@lem7241480) (@lem7241414 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241483 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7241484 (_96883 : int) (_96886 : int) : term829 _96883 _96886.
Proof. exact (@lem7241483 term340 (term449 _96883 _96886)). Qed.
Lemma lem7241485 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term830 _96883 _96886.
Proof. exact (@lem7241484 _96883 _96886 (@lem7241481 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241486 (_96883 : int) (_96886 : int) : (term831 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (@lem1982733 (term449 _96883 _96886)). Qed.
Lemma lem7241487 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241488 (_96883 : int) (_96886 : int) : (term832 _96883 _96886) = (term458 _96883 _96886).
Proof. exact (MK_COMB (@lem7241487) (@lem7241486 _96883 _96886)). Qed.
Lemma lem7241489 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241490 (_96883 : int) (_96886 : int) : (term830 _96883 _96886) = (term459 _96883 _96886).
Proof. exact (MK_COMB (@lem7241488 _96883 _96886) (@lem7241489)). Qed.
Lemma lem7241491 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term459 _96883 _96886.
Proof. exact (EQ_MP (@lem7241490 _96883 _96886) (@lem7241485 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241493 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7241494 : term764 = term476.
Proof. exact (@lem7241493 term328 term340). Qed.
Lemma lem7241496 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241497 : term340 = term438.
Proof. exact (@lem7241496 term189). Qed.
Lemma lem7241499 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241500 : term328 = term390.
Proof. exact (@lem7241499 (NUMERAL 0)). Qed.
Lemma lem7241501 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241502 : term765 = term766.
Proof. exact (MK_COMB (@lem7241501) (@lem7241500)). Qed.
Lemma lem7241503 : term476 = term767.
Proof. exact (MK_COMB (@lem7241502) (@lem7241497)). Qed.
Lemma lem7241504 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7241506 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241507 : term476 = term477.
Proof. exact (@lem7241506 (NUMERAL 0) term189). Qed.
Lemma lem7241508 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241509 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241510 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241509 h1) (fun h1 : term477 = True => @lem7241508)). Qed.
Lemma lem7241511 : term477 = True.
Proof. exact (EQ_MP (@lem7241510) (@lem7241508)). Qed.
Lemma lem7241512 : term476 = True.
Proof. exact (TRANS (@lem7241507) (@lem7241511)). Qed.
Lemma lem7241513 : True = term476.
Proof. exact (SYM (@lem7241512)). Qed.
Lemma lem7241514 : term476.
Proof. exact (EQ_MP (@lem7241513) (@lem0)). Qed.
Lemma lem7241515 : term769.
Proof. exact (@lem7241504 (@lem7241514)). Qed.
Lemma lem7241517 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241518 : term476 = term477.
Proof. exact (@lem7241517 (NUMERAL 0) term189). Qed.
Lemma lem7241519 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241520 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241521 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241520 h1) (fun h1 : term477 = True => @lem7241519)). Qed.
Lemma lem7241522 : term477 = True.
Proof. exact (EQ_MP (@lem7241521) (@lem7241519)). Qed.
Lemma lem7241523 : term476 = True.
Proof. exact (TRANS (@lem7241518) (@lem7241522)). Qed.
Lemma lem7241524 : True = term476.
Proof. exact (SYM (@lem7241523)). Qed.
Lemma lem7241525 : term476.
Proof. exact (EQ_MP (@lem7241524) (@lem0)). Qed.
Lemma lem7241526 : term767 = term770.
Proof. exact (@lem7241515 (@lem7241525)). Qed.
Lemma lem7241528 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241529 : term402 = term403.
Proof. exact (@lem7241528 term189 term189). Qed.
Lemma lem7241530 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241531 : term405 = term189.
Proof. exact (EQ_MP (@lem7241530) (@lem940073)). Qed.
Lemma lem7241532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241533 : term403 = term340.
Proof. exact (MK_COMB (@lem7241532) (@lem7241531)). Qed.
Lemma lem7241534 : term402 = term340.
Proof. exact (TRANS (@lem7241529) (@lem7241533)). Qed.
Lemma lem7241536 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241537 : term488 = term328.
Proof. exact (@lem7241536 term189). Qed.
Lemma lem7241538 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241539 : term771 = term765.
Proof. exact (MK_COMB (@lem7241538) (@lem7241537)). Qed.
Lemma lem7241540 : term770 = term476.
Proof. exact (MK_COMB (@lem7241539) (@lem7241534)). Qed.
Lemma lem7241542 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241543 : term476 = term477.
Proof. exact (@lem7241542 (NUMERAL 0) term189). Qed.
Lemma lem7241544 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241545 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241546 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241545 h1) (fun h1 : term477 = True => @lem7241544)). Qed.
Lemma lem7241547 : term477 = True.
Proof. exact (EQ_MP (@lem7241546) (@lem7241544)). Qed.
Lemma lem7241548 : term476 = True.
Proof. exact (TRANS (@lem7241543) (@lem7241547)). Qed.
Lemma lem7241549 : term770 = True.
Proof. exact (TRANS (@lem7241540) (@lem7241548)). Qed.
Lemma lem7241550 : term767 = True.
Proof. exact (TRANS (@lem7241526) (@lem7241549)). Qed.
Lemma lem7241551 : term476 = True.
Proof. exact (TRANS (@lem7241503) (@lem7241550)). Qed.
Lemma lem7241552 : term764 = True.
Proof. exact (TRANS (@lem7241494) (@lem7241551)). Qed.
Lemma lem7241553 : True = term764.
Proof. exact (SYM (@lem7241552)). Qed.
Lemma lem7241554 : term764.
Proof. exact (EQ_MP (@lem7241553) (@lem0)). Qed.
Lemma lem7241555 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term833 _96883 _96886.
Proof. exact (conj (@lem7241554) (@lem7241417 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241557 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7241558 (_96883 : int) (_96886 : int) : term834 _96883 _96886.
Proof. exact (@lem7241557 term340 (term425 _96883 _96886)). Qed.
Lemma lem7241559 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term835 _96883 _96886.
Proof. exact (@lem7241558 _96883 _96886 (@lem7241555 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241560 (_96883 : int) (_96886 : int) : (term836 _96883 _96886) = (term425 _96883 _96886).
Proof. exact (@lem1982733 (term425 _96883 _96886)). Qed.
Lemma lem7241561 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241562 (_96883 : int) (_96886 : int) : (term837 _96883 _96886) = (term427 _96883 _96886).
Proof. exact (MK_COMB (@lem7241561) (@lem7241560 _96883 _96886)). Qed.
Lemma lem7241563 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241564 (_96883 : int) (_96886 : int) : (term835 _96883 _96886) = (term428 _96883 _96886).
Proof. exact (MK_COMB (@lem7241562 _96883 _96886) (@lem7241563)). Qed.
Lemma lem7241565 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term428 _96883 _96886.
Proof. exact (EQ_MP (@lem7241564 _96883 _96886) (@lem7241559 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241566 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term838 _96883 _96886.
Proof. exact (conj (@lem7241565 _96885 _96884 _96883 _96886 h1) (@lem7241491 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241568 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7241569 (_96883 : int) (_96886 : int) : term839 _96883 _96886.
Proof. exact (@lem7241568 (term425 _96883 _96886) (term449 _96883 _96886)). Qed.
Lemma lem7241570 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term840 _96883 _96886.
Proof. exact (@lem7241569 _96883 _96886 (@lem7241566 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241571 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = (term842 _96883 _96886).
Proof. exact (@lem1982753 (term418 _96883) (real_of_int _96883) (real_of_int _96886) (term448 _96886)). Qed.
Lemma lem7241572 (_96883 : int) : (term789 _96883) = (term790 _96883).
Proof. exact (@lem1982713 term393 (real_of_int _96883)). Qed.
Lemma lem7241574 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241575 : term340 = term438.
Proof. exact (@lem7241574 term189). Qed.
Lemma lem7241577 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7241578 : term393 = term394.
Proof. exact (@lem7241577 term189). Qed.
Lemma lem7241579 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241580 : term791 = term792.
Proof. exact (MK_COMB (@lem7241579) (@lem7241578)). Qed.
Lemma lem7241581 : term793 = term794.
Proof. exact (MK_COMB (@lem7241580) (@lem7241575)). Qed.
Lemma lem7241582 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7241584 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241585 : term476 = term477.
Proof. exact (@lem7241584 (NUMERAL 0) term189). Qed.
Lemma lem7241586 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241587 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241588 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241587 h1) (fun h1 : term477 = True => @lem7241586)). Qed.
Lemma lem7241589 : term477 = True.
Proof. exact (EQ_MP (@lem7241588) (@lem7241586)). Qed.
Lemma lem7241590 : term476 = True.
Proof. exact (TRANS (@lem7241585) (@lem7241589)). Qed.
Lemma lem7241591 : True = term476.
Proof. exact (SYM (@lem7241590)). Qed.
Lemma lem7241592 : term476.
Proof. exact (EQ_MP (@lem7241591) (@lem0)). Qed.
Lemma lem7241593 : term796.
Proof. exact (@lem7241582 (@lem7241592)). Qed.
Lemma lem7241595 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241596 : term476 = term477.
Proof. exact (@lem7241595 (NUMERAL 0) term189). Qed.
Lemma lem7241597 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241598 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241599 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241598 h1) (fun h1 : term477 = True => @lem7241597)). Qed.
Lemma lem7241600 : term477 = True.
Proof. exact (EQ_MP (@lem7241599) (@lem7241597)). Qed.
Lemma lem7241601 : term476 = True.
Proof. exact (TRANS (@lem7241596) (@lem7241600)). Qed.
Lemma lem7241602 : True = term476.
Proof. exact (SYM (@lem7241601)). Qed.
Lemma lem7241603 : term476.
Proof. exact (EQ_MP (@lem7241602) (@lem0)). Qed.
Lemma lem7241604 : term797.
Proof. exact (@lem7241593 (@lem7241603)). Qed.
Lemma lem7241606 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241607 : term476 = term477.
Proof. exact (@lem7241606 (NUMERAL 0) term189). Qed.
Lemma lem7241608 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241609 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241610 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241609 h1) (fun h1 : term477 = True => @lem7241608)). Qed.
Lemma lem7241611 : term477 = True.
Proof. exact (EQ_MP (@lem7241610) (@lem7241608)). Qed.
Lemma lem7241612 : term476 = True.
Proof. exact (TRANS (@lem7241607) (@lem7241611)). Qed.
Lemma lem7241613 : True = term476.
Proof. exact (SYM (@lem7241612)). Qed.
Lemma lem7241614 : term476.
Proof. exact (EQ_MP (@lem7241613) (@lem0)). Qed.
Lemma lem7241615 : term798.
Proof. exact (@lem7241604 (@lem7241614)). Qed.
Lemma lem7241617 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241618 : term402 = term403.
Proof. exact (@lem7241617 term189 term189). Qed.
Lemma lem7241619 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241620 : term405 = term189.
Proof. exact (EQ_MP (@lem7241619) (@lem940073)). Qed.
Lemma lem7241621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241622 : term403 = term340.
Proof. exact (MK_COMB (@lem7241621) (@lem7241620)). Qed.
Lemma lem7241623 : term402 = term340.
Proof. exact (TRANS (@lem7241618) (@lem7241622)). Qed.
Lemma lem7241625 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7241626 : term439 = term444.
Proof. exact (@lem7241625 term189 term189). Qed.
Lemma lem7241627 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241628 : term405 = term189.
Proof. exact (EQ_MP (@lem7241627) (@lem940073)). Qed.
Lemma lem7241629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241630 : term403 = term340.
Proof. exact (MK_COMB (@lem7241629) (@lem7241628)). Qed.
Lemma lem7241631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7241632 : term444 = term393.
Proof. exact (MK_COMB (@lem7241631) (@lem7241630)). Qed.
Lemma lem7241633 : term439 = term393.
Proof. exact (TRANS (@lem7241626) (@lem7241632)). Qed.
Lemma lem7241634 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241635 : term799 = term791.
Proof. exact (MK_COMB (@lem7241634) (@lem7241633)). Qed.
Lemma lem7241636 : term800 = term793.
Proof. exact (MK_COMB (@lem7241635) (@lem7241623)). Qed.
Lemma lem7241638 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7241639 : term793 = term328.
Proof. exact (@lem7241638 term189). Qed.
Lemma lem7241640 : term800 = term328.
Proof. exact (TRANS (@lem7241636) (@lem7241639)). Qed.
Lemma lem7241641 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241642 : term802 = term486.
Proof. exact (MK_COMB (@lem7241641) (@lem7241640)). Qed.
Lemma lem7241643 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7241644 : term803 = term488.
Proof. exact (MK_COMB (@lem7241642) (@lem7241643)). Qed.
Lemma lem7241646 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241647 : term488 = term328.
Proof. exact (@lem7241646 term189). Qed.
Lemma lem7241648 : term803 = term328.
Proof. exact (TRANS (@lem7241644) (@lem7241647)). Qed.
Lemma lem7241650 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241651 : term402 = term403.
Proof. exact (@lem7241650 term189 term189). Qed.
Lemma lem7241652 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241653 : term405 = term189.
Proof. exact (EQ_MP (@lem7241652) (@lem940073)). Qed.
Lemma lem7241654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241655 : term403 = term340.
Proof. exact (MK_COMB (@lem7241654) (@lem7241653)). Qed.
Lemma lem7241656 : term402 = term340.
Proof. exact (TRANS (@lem7241651) (@lem7241655)). Qed.
Lemma lem7241657 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7241658 : term490 = term488.
Proof. exact (MK_COMB (@lem7241657) (@lem7241656)). Qed.
Lemma lem7241660 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241661 : term488 = term328.
Proof. exact (@lem7241660 term189). Qed.
Lemma lem7241662 : term490 = term328.
Proof. exact (TRANS (@lem7241658) (@lem7241661)). Qed.
Lemma lem7241663 : term328 = term490.
Proof. exact (SYM (@lem7241662)). Qed.
Lemma lem7241664 : term803 = term490.
Proof. exact (TRANS (@lem7241648) (@lem7241663)). Qed.
Lemma lem7241665 : term794 = term390.
Proof. exact (@lem7241615 (@lem7241664)). Qed.
Lemma lem7241666 : term793 = term390.
Proof. exact (TRANS (@lem7241581) (@lem7241665)). Qed.
Lemma lem7241668 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7241669 : term390 = term328.
Proof. exact (@lem7241668 term328). Qed.
Lemma lem7241670 : term793 = term328.
Proof. exact (TRANS (@lem7241666) (@lem7241669)). Qed.
Lemma lem7241671 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241672 : term804 = term486.
Proof. exact (MK_COMB (@lem7241671) (@lem7241670)). Qed.
Lemma lem7241673 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7241674 (_96883 : int) : (term790 _96883) = (term805 _96883).
Proof. exact (MK_COMB (@lem7241672) (@lem7241673 _96883)). Qed.
Lemma lem7241675 (_96883 : int) : (term789 _96883) = (term805 _96883).
Proof. exact (TRANS (@lem7241572 _96883) (@lem7241674 _96883)). Qed.
Lemma lem7241676 (_96883 : int) : (term805 _96883) = term328.
Proof. exact (@lem1982719 (real_of_int _96883)). Qed.
Lemma lem7241677 (_96883 : int) : (term789 _96883) = term328.
Proof. exact (TRANS (@lem7241675 _96883) (@lem7241676 _96883)). Qed.
Lemma lem7241678 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241679 (_96883 : int) : (term806 _96883) = term807.
Proof. exact (MK_COMB (@lem7241678) (@lem7241677 _96883)). Qed.
Lemma lem7241680 (_96886 : int) : (term843 _96886) = (term809 _96886).
Proof. exact (@lem1982763 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7241681 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7241683 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241684 : term340 = term438.
Proof. exact (@lem7241683 term189). Qed.
Lemma lem7241686 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7241687 : term393 = term394.
Proof. exact (@lem7241686 term189). Qed.
Lemma lem7241688 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241689 : term791 = term792.
Proof. exact (MK_COMB (@lem7241688) (@lem7241687)). Qed.
Lemma lem7241690 : term793 = term794.
Proof. exact (MK_COMB (@lem7241689) (@lem7241684)). Qed.
Lemma lem7241691 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7241693 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241694 : term476 = term477.
Proof. exact (@lem7241693 (NUMERAL 0) term189). Qed.
Lemma lem7241695 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241696 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241697 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241696 h1) (fun h1 : term477 = True => @lem7241695)). Qed.
Lemma lem7241698 : term477 = True.
Proof. exact (EQ_MP (@lem7241697) (@lem7241695)). Qed.
Lemma lem7241699 : term476 = True.
Proof. exact (TRANS (@lem7241694) (@lem7241698)). Qed.
Lemma lem7241700 : True = term476.
Proof. exact (SYM (@lem7241699)). Qed.
Lemma lem7241701 : term476.
Proof. exact (EQ_MP (@lem7241700) (@lem0)). Qed.
Lemma lem7241702 : term796.
Proof. exact (@lem7241691 (@lem7241701)). Qed.
Lemma lem7241704 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241705 : term476 = term477.
Proof. exact (@lem7241704 (NUMERAL 0) term189). Qed.
Lemma lem7241706 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241707 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241708 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241707 h1) (fun h1 : term477 = True => @lem7241706)). Qed.
Lemma lem7241709 : term477 = True.
Proof. exact (EQ_MP (@lem7241708) (@lem7241706)). Qed.
Lemma lem7241710 : term476 = True.
Proof. exact (TRANS (@lem7241705) (@lem7241709)). Qed.
Lemma lem7241711 : True = term476.
Proof. exact (SYM (@lem7241710)). Qed.
Lemma lem7241712 : term476.
Proof. exact (EQ_MP (@lem7241711) (@lem0)). Qed.
Lemma lem7241713 : term797.
Proof. exact (@lem7241702 (@lem7241712)). Qed.
Lemma lem7241715 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241716 : term476 = term477.
Proof. exact (@lem7241715 (NUMERAL 0) term189). Qed.
Lemma lem7241717 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241718 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241719 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241718 h1) (fun h1 : term477 = True => @lem7241717)). Qed.
Lemma lem7241720 : term477 = True.
Proof. exact (EQ_MP (@lem7241719) (@lem7241717)). Qed.
Lemma lem7241721 : term476 = True.
Proof. exact (TRANS (@lem7241716) (@lem7241720)). Qed.
Lemma lem7241722 : True = term476.
Proof. exact (SYM (@lem7241721)). Qed.
Lemma lem7241723 : term476.
Proof. exact (EQ_MP (@lem7241722) (@lem0)). Qed.
Lemma lem7241724 : term798.
Proof. exact (@lem7241713 (@lem7241723)). Qed.
Lemma lem7241726 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241727 : term402 = term403.
Proof. exact (@lem7241726 term189 term189). Qed.
Lemma lem7241728 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241729 : term405 = term189.
Proof. exact (EQ_MP (@lem7241728) (@lem940073)). Qed.
Lemma lem7241730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241731 : term403 = term340.
Proof. exact (MK_COMB (@lem7241730) (@lem7241729)). Qed.
Lemma lem7241732 : term402 = term340.
Proof. exact (TRANS (@lem7241727) (@lem7241731)). Qed.
Lemma lem7241734 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7241735 : term439 = term444.
Proof. exact (@lem7241734 term189 term189). Qed.
Lemma lem7241736 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241737 : term405 = term189.
Proof. exact (EQ_MP (@lem7241736) (@lem940073)). Qed.
Lemma lem7241738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241739 : term403 = term340.
Proof. exact (MK_COMB (@lem7241738) (@lem7241737)). Qed.
Lemma lem7241740 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7241741 : term444 = term393.
Proof. exact (MK_COMB (@lem7241740) (@lem7241739)). Qed.
Lemma lem7241742 : term439 = term393.
Proof. exact (TRANS (@lem7241735) (@lem7241741)). Qed.
Lemma lem7241743 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241744 : term799 = term791.
Proof. exact (MK_COMB (@lem7241743) (@lem7241742)). Qed.
Lemma lem7241745 : term800 = term793.
Proof. exact (MK_COMB (@lem7241744) (@lem7241732)). Qed.
Lemma lem7241747 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7241748 : term793 = term328.
Proof. exact (@lem7241747 term189). Qed.
Lemma lem7241749 : term800 = term328.
Proof. exact (TRANS (@lem7241745) (@lem7241748)). Qed.
Lemma lem7241750 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241751 : term802 = term486.
Proof. exact (MK_COMB (@lem7241750) (@lem7241749)). Qed.
Lemma lem7241752 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7241753 : term803 = term488.
Proof. exact (MK_COMB (@lem7241751) (@lem7241752)). Qed.
Lemma lem7241755 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241756 : term488 = term328.
Proof. exact (@lem7241755 term189). Qed.
Lemma lem7241757 : term803 = term328.
Proof. exact (TRANS (@lem7241753) (@lem7241756)). Qed.
Lemma lem7241759 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241760 : term402 = term403.
Proof. exact (@lem7241759 term189 term189). Qed.
Lemma lem7241761 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241762 : term405 = term189.
Proof. exact (EQ_MP (@lem7241761) (@lem940073)). Qed.
Lemma lem7241763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241764 : term403 = term340.
Proof. exact (MK_COMB (@lem7241763) (@lem7241762)). Qed.
Lemma lem7241765 : term402 = term340.
Proof. exact (TRANS (@lem7241760) (@lem7241764)). Qed.
Lemma lem7241766 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7241767 : term490 = term488.
Proof. exact (MK_COMB (@lem7241766) (@lem7241765)). Qed.
Lemma lem7241769 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241770 : term488 = term328.
Proof. exact (@lem7241769 term189). Qed.
Lemma lem7241771 : term490 = term328.
Proof. exact (TRANS (@lem7241767) (@lem7241770)). Qed.
Lemma lem7241772 : term328 = term490.
Proof. exact (SYM (@lem7241771)). Qed.
Lemma lem7241773 : term803 = term490.
Proof. exact (TRANS (@lem7241757) (@lem7241772)). Qed.
Lemma lem7241774 : term794 = term390.
Proof. exact (@lem7241724 (@lem7241773)). Qed.
Lemma lem7241775 : term793 = term390.
Proof. exact (TRANS (@lem7241690) (@lem7241774)). Qed.
Lemma lem7241777 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7241778 : term390 = term328.
Proof. exact (@lem7241777 term328). Qed.
Lemma lem7241779 : term793 = term328.
Proof. exact (TRANS (@lem7241775) (@lem7241778)). Qed.
Lemma lem7241780 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7241781 : term804 = term486.
Proof. exact (MK_COMB (@lem7241780) (@lem7241779)). Qed.
Lemma lem7241782 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7241783 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7241781) (@lem7241782 _96886)). Qed.
Lemma lem7241784 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7241681 _96886) (@lem7241783 _96886)). Qed.
Lemma lem7241785 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7241786 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7241784 _96886) (@lem7241785 _96886)). Qed.
Lemma lem7241787 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7241788 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7241787) (@lem7241786 _96886)). Qed.
Lemma lem7241789 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7241790 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7241788 _96886) (@lem7241789)). Qed.
Lemma lem7241791 (_96886 : int) : (term843 _96886) = term812.
Proof. exact (TRANS (@lem7241680 _96886) (@lem7241790 _96886)). Qed.
Lemma lem7241792 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7241793 (_96886 : int) : (term843 _96886) = term393.
Proof. exact (TRANS (@lem7241791 _96886) (@lem7241792)). Qed.
Lemma lem7241794 (_96883 : int) (_96886 : int) : (term842 _96883 _96886) = term812.
Proof. exact (MK_COMB (@lem7241679 _96883) (@lem7241793 _96886)). Qed.
Lemma lem7241795 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = term812.
Proof. exact (TRANS (@lem7241571 _96883 _96886) (@lem7241794 _96883 _96886)). Qed.
Lemma lem7241796 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7241797 (_96883 : int) (_96886 : int) : (term841 _96883 _96886) = term393.
Proof. exact (TRANS (@lem7241795 _96883 _96886) (@lem7241796)). Qed.
Lemma lem7241798 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241799 (_96883 : int) (_96886 : int) : (term844 _96883 _96886) = term814.
Proof. exact (MK_COMB (@lem7241798) (@lem7241797 _96883 _96886)). Qed.
Lemma lem7241800 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241801 (_96883 : int) (_96886 : int) : (term840 _96883 _96886) = term815.
Proof. exact (MK_COMB (@lem7241799 _96883 _96886) (@lem7241800)). Qed.
Lemma lem7241802 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : term815.
Proof. exact (EQ_MP (@lem7241801 _96883 _96886) (@lem7241570 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241804 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7241805 : term815 = term816.
Proof. exact (@lem7241804 term328 term393). Qed.
Lemma lem7241807 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7241808 : term393 = term394.
Proof. exact (@lem7241807 term189). Qed.
Lemma lem7241810 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241811 : term328 = term390.
Proof. exact (@lem7241810 (NUMERAL 0)). Qed.
Lemma lem7241812 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7241813 : term330 = term817.
Proof. exact (MK_COMB (@lem7241812) (@lem7241811)). Qed.
Lemma lem7241814 : term816 = term818.
Proof. exact (MK_COMB (@lem7241813) (@lem7241808)). Qed.
Lemma lem7241815 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7241817 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241818 : term476 = term477.
Proof. exact (@lem7241817 (NUMERAL 0) term189). Qed.
Lemma lem7241819 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241820 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241821 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241820 h1) (fun h1 : term477 = True => @lem7241819)). Qed.
Lemma lem7241822 : term477 = True.
Proof. exact (EQ_MP (@lem7241821) (@lem7241819)). Qed.
Lemma lem7241823 : term476 = True.
Proof. exact (TRANS (@lem7241818) (@lem7241822)). Qed.
Lemma lem7241824 : True = term476.
Proof. exact (SYM (@lem7241823)). Qed.
Lemma lem7241825 : term476.
Proof. exact (EQ_MP (@lem7241824) (@lem0)). Qed.
Lemma lem7241826 : term820.
Proof. exact (@lem7241815 (@lem7241825)). Qed.
Lemma lem7241828 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241829 : term476 = term477.
Proof. exact (@lem7241828 (NUMERAL 0) term189). Qed.
Lemma lem7241830 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241831 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241832 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241831 h1) (fun h1 : term477 = True => @lem7241830)). Qed.
Lemma lem7241833 : term477 = True.
Proof. exact (EQ_MP (@lem7241832) (@lem7241830)). Qed.
Lemma lem7241834 : term476 = True.
Proof. exact (TRANS (@lem7241829) (@lem7241833)). Qed.
Lemma lem7241835 : True = term476.
Proof. exact (SYM (@lem7241834)). Qed.
Lemma lem7241836 : term476.
Proof. exact (EQ_MP (@lem7241835) (@lem0)). Qed.
Lemma lem7241837 : term818 = term821.
Proof. exact (@lem7241826 (@lem7241836)). Qed.
Lemma lem7241839 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7241840 : term439 = term444.
Proof. exact (@lem7241839 term189 term189). Qed.
Lemma lem7241841 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241842 : term405 = term189.
Proof. exact (EQ_MP (@lem7241841) (@lem940073)). Qed.
Lemma lem7241843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241844 : term403 = term340.
Proof. exact (MK_COMB (@lem7241843) (@lem7241842)). Qed.
Lemma lem7241845 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7241846 : term444 = term393.
Proof. exact (MK_COMB (@lem7241845) (@lem7241844)). Qed.
Lemma lem7241847 : term439 = term393.
Proof. exact (TRANS (@lem7241840) (@lem7241846)). Qed.
Lemma lem7241849 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241850 : term488 = term328.
Proof. exact (@lem7241849 term189). Qed.
Lemma lem7241851 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7241852 : term822 = term330.
Proof. exact (MK_COMB (@lem7241851) (@lem7241850)). Qed.
Lemma lem7241853 : term821 = term816.
Proof. exact (MK_COMB (@lem7241852) (@lem7241847)). Qed.
Lemma lem7241855 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7241856 : term816 = term825.
Proof. exact (@lem7241855 (NUMERAL 0) term189). Qed.
Lemma lem7241857 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241858 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7241859 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241858 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7241857)). Qed.
Lemma lem7241860 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7241859) (@lem7241857)). Qed.
Lemma lem7241861 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7241862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7241863 : term826 = (and True).
Proof. exact (MK_COMB (@lem7241862) (@lem7241861)). Qed.
Lemma lem7241864 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7241863) (@lem7241860)). Qed.
Lemma lem7241866 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7241867 : term825 = False.
Proof. exact (TRANS (@lem7241864) (@lem7241866)). Qed.
Lemma lem7241868 : term816 = False.
Proof. exact (TRANS (@lem7241856) (@lem7241867)). Qed.
Lemma lem7241869 : term821 = False.
Proof. exact (TRANS (@lem7241853) (@lem7241868)). Qed.
Lemma lem7241870 : term818 = False.
Proof. exact (TRANS (@lem7241837) (@lem7241869)). Qed.
Lemma lem7241871 : term816 = False.
Proof. exact (TRANS (@lem7241814) (@lem7241870)). Qed.
Lemma lem7241872 : term815 = False.
Proof. exact (TRANS (@lem7241805) (@lem7241871)). Qed.
Lemma lem7241873 (_96885 : int) (_96884 : int) (_96883 : int) (_96886 : int) (h1 : term848 _96885 _96884 _96883 _96886) : False.
Proof. exact (EQ_MP (@lem7241872) (@lem7241802 _96885 _96884 _96883 _96886 h1)). Qed.
Lemma lem7241874 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term849 _96884 _96885 _96883 _96886.
Proof. exact (h1). Qed.
Lemma lem7241875 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term741 _96884 _96885 _96883 _96886.
Proof. exact (proj2 (@lem7241874 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241877 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term705 _96884 _96885 _96883 _96886.
Proof. exact (proj2 (@lem7241875 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241879 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term669 _96884 _96885 _96883 _96886.
Proof. exact (proj2 (@lem7241877 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241881 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term633 _96884 _96885 _96883 _96886.
Proof. exact (proj2 (@lem7241879 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241883 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term597 _96884 _96885 _96883 _96886.
Proof. exact (proj2 (@lem7241881 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241884 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term421 _96883 _96884.
Proof. exact (proj1 (@lem7241881 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241885 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term561 _96884 _96885 _96883 _96886.
Proof. exact (proj2 (@lem7241883 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241887 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term459 _96883 _96886.
Proof. exact (proj2 (@lem7241885 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241888 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term455 _96884 _96885 _96886.
Proof. exact (proj1 (@lem7241885 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241890 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term453 _96884 _96886.
Proof. exact (proj1 (@lem7241888 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241892 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7241893 : term764 = term476.
Proof. exact (@lem7241892 term328 term340). Qed.
Lemma lem7241895 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241896 : term340 = term438.
Proof. exact (@lem7241895 term189). Qed.
Lemma lem7241898 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241899 : term328 = term390.
Proof. exact (@lem7241898 (NUMERAL 0)). Qed.
Lemma lem7241900 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241901 : term765 = term766.
Proof. exact (MK_COMB (@lem7241900) (@lem7241899)). Qed.
Lemma lem7241902 : term476 = term767.
Proof. exact (MK_COMB (@lem7241901) (@lem7241896)). Qed.
Lemma lem7241903 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7241905 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241906 : term476 = term477.
Proof. exact (@lem7241905 (NUMERAL 0) term189). Qed.
Lemma lem7241907 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241908 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241909 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241908 h1) (fun h1 : term477 = True => @lem7241907)). Qed.
Lemma lem7241910 : term477 = True.
Proof. exact (EQ_MP (@lem7241909) (@lem7241907)). Qed.
Lemma lem7241911 : term476 = True.
Proof. exact (TRANS (@lem7241906) (@lem7241910)). Qed.
Lemma lem7241912 : True = term476.
Proof. exact (SYM (@lem7241911)). Qed.
Lemma lem7241913 : term476.
Proof. exact (EQ_MP (@lem7241912) (@lem0)). Qed.
Lemma lem7241914 : term769.
Proof. exact (@lem7241903 (@lem7241913)). Qed.
Lemma lem7241916 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241917 : term476 = term477.
Proof. exact (@lem7241916 (NUMERAL 0) term189). Qed.
Lemma lem7241918 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241919 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241920 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241919 h1) (fun h1 : term477 = True => @lem7241918)). Qed.
Lemma lem7241921 : term477 = True.
Proof. exact (EQ_MP (@lem7241920) (@lem7241918)). Qed.
Lemma lem7241922 : term476 = True.
Proof. exact (TRANS (@lem7241917) (@lem7241921)). Qed.
Lemma lem7241923 : True = term476.
Proof. exact (SYM (@lem7241922)). Qed.
Lemma lem7241924 : term476.
Proof. exact (EQ_MP (@lem7241923) (@lem0)). Qed.
Lemma lem7241925 : term767 = term770.
Proof. exact (@lem7241914 (@lem7241924)). Qed.
Lemma lem7241927 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7241928 : term402 = term403.
Proof. exact (@lem7241927 term189 term189). Qed.
Lemma lem7241929 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7241930 : term405 = term189.
Proof. exact (EQ_MP (@lem7241929) (@lem940073)). Qed.
Lemma lem7241931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7241932 : term403 = term340.
Proof. exact (MK_COMB (@lem7241931) (@lem7241930)). Qed.
Lemma lem7241933 : term402 = term340.
Proof. exact (TRANS (@lem7241928) (@lem7241932)). Qed.
Lemma lem7241935 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7241936 : term488 = term328.
Proof. exact (@lem7241935 term189). Qed.
Lemma lem7241937 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241938 : term771 = term765.
Proof. exact (MK_COMB (@lem7241937) (@lem7241936)). Qed.
Lemma lem7241939 : term770 = term476.
Proof. exact (MK_COMB (@lem7241938) (@lem7241933)). Qed.
Lemma lem7241941 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241942 : term476 = term477.
Proof. exact (@lem7241941 (NUMERAL 0) term189). Qed.
Lemma lem7241943 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241944 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241945 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241944 h1) (fun h1 : term477 = True => @lem7241943)). Qed.
Lemma lem7241946 : term477 = True.
Proof. exact (EQ_MP (@lem7241945) (@lem7241943)). Qed.
Lemma lem7241947 : term476 = True.
Proof. exact (TRANS (@lem7241942) (@lem7241946)). Qed.
Lemma lem7241948 : term770 = True.
Proof. exact (TRANS (@lem7241939) (@lem7241947)). Qed.
Lemma lem7241949 : term767 = True.
Proof. exact (TRANS (@lem7241925) (@lem7241948)). Qed.
Lemma lem7241950 : term476 = True.
Proof. exact (TRANS (@lem7241902) (@lem7241949)). Qed.
Lemma lem7241951 : term764 = True.
Proof. exact (TRANS (@lem7241893) (@lem7241950)). Qed.
Lemma lem7241952 : True = term764.
Proof. exact (SYM (@lem7241951)). Qed.
Lemma lem7241953 : term764.
Proof. exact (EQ_MP (@lem7241952) (@lem0)). Qed.
Lemma lem7241954 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term778 _96884 _96886.
Proof. exact (conj (@lem7241953) (@lem7241890 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241956 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7241957 (_96884 : int) (_96886 : int) : term779 _96884 _96886.
Proof. exact (@lem7241956 term340 (term450 _96884 _96886)). Qed.
Lemma lem7241958 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term780 _96884 _96886.
Proof. exact (@lem7241957 _96884 _96886 (@lem7241954 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241959 (_96884 : int) (_96886 : int) : (term781 _96884 _96886) = (term450 _96884 _96886).
Proof. exact (@lem1982733 (term450 _96884 _96886)). Qed.
Lemma lem7241960 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7241961 (_96884 : int) (_96886 : int) : (term782 _96884 _96886) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7241960) (@lem7241959 _96884 _96886)). Qed.
Lemma lem7241962 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7241963 (_96884 : int) (_96886 : int) : (term780 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7241961 _96884 _96886) (@lem7241962)). Qed.
Lemma lem7241964 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term453 _96884 _96886.
Proof. exact (EQ_MP (@lem7241963 _96884 _96886) (@lem7241958 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7241966 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7241967 : term764 = term476.
Proof. exact (@lem7241966 term328 term340). Qed.
Lemma lem7241969 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241970 : term340 = term438.
Proof. exact (@lem7241969 term189). Qed.
Lemma lem7241972 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7241973 : term328 = term390.
Proof. exact (@lem7241972 (NUMERAL 0)). Qed.
Lemma lem7241974 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7241975 : term765 = term766.
Proof. exact (MK_COMB (@lem7241974) (@lem7241973)). Qed.
Lemma lem7241976 : term476 = term767.
Proof. exact (MK_COMB (@lem7241975) (@lem7241970)). Qed.
Lemma lem7241977 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7241979 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241980 : term476 = term477.
Proof. exact (@lem7241979 (NUMERAL 0) term189). Qed.
Lemma lem7241981 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241982 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241983 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241982 h1) (fun h1 : term477 = True => @lem7241981)). Qed.
Lemma lem7241984 : term477 = True.
Proof. exact (EQ_MP (@lem7241983) (@lem7241981)). Qed.
Lemma lem7241985 : term476 = True.
Proof. exact (TRANS (@lem7241980) (@lem7241984)). Qed.
Lemma lem7241986 : True = term476.
Proof. exact (SYM (@lem7241985)). Qed.
Lemma lem7241987 : term476.
Proof. exact (EQ_MP (@lem7241986) (@lem0)). Qed.
Lemma lem7241988 : term769.
Proof. exact (@lem7241977 (@lem7241987)). Qed.
Lemma lem7241990 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7241991 : term476 = term477.
Proof. exact (@lem7241990 (NUMERAL 0) term189). Qed.
Lemma lem7241992 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7241993 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7241994 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7241993 h1) (fun h1 : term477 = True => @lem7241992)). Qed.
Lemma lem7241995 : term477 = True.
Proof. exact (EQ_MP (@lem7241994) (@lem7241992)). Qed.
Lemma lem7241996 : term476 = True.
Proof. exact (TRANS (@lem7241991) (@lem7241995)). Qed.
Lemma lem7241997 : True = term476.
Proof. exact (SYM (@lem7241996)). Qed.
Lemma lem7241998 : term476.
Proof. exact (EQ_MP (@lem7241997) (@lem0)). Qed.
Lemma lem7241999 : term767 = term770.
Proof. exact (@lem7241988 (@lem7241998)). Qed.
Lemma lem7242001 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242002 : term402 = term403.
Proof. exact (@lem7242001 term189 term189). Qed.
Lemma lem7242003 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242004 : term405 = term189.
Proof. exact (EQ_MP (@lem7242003) (@lem940073)). Qed.
Lemma lem7242005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242006 : term403 = term340.
Proof. exact (MK_COMB (@lem7242005) (@lem7242004)). Qed.
Lemma lem7242007 : term402 = term340.
Proof. exact (TRANS (@lem7242002) (@lem7242006)). Qed.
Lemma lem7242009 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242010 : term488 = term328.
Proof. exact (@lem7242009 term189). Qed.
Lemma lem7242011 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242012 : term771 = term765.
Proof. exact (MK_COMB (@lem7242011) (@lem7242010)). Qed.
Lemma lem7242013 : term770 = term476.
Proof. exact (MK_COMB (@lem7242012) (@lem7242007)). Qed.
Lemma lem7242015 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242016 : term476 = term477.
Proof. exact (@lem7242015 (NUMERAL 0) term189). Qed.
Lemma lem7242017 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242018 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242019 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242018 h1) (fun h1 : term477 = True => @lem7242017)). Qed.
Lemma lem7242020 : term477 = True.
Proof. exact (EQ_MP (@lem7242019) (@lem7242017)). Qed.
Lemma lem7242021 : term476 = True.
Proof. exact (TRANS (@lem7242016) (@lem7242020)). Qed.
Lemma lem7242022 : term770 = True.
Proof. exact (TRANS (@lem7242013) (@lem7242021)). Qed.
Lemma lem7242023 : term767 = True.
Proof. exact (TRANS (@lem7241999) (@lem7242022)). Qed.
Lemma lem7242024 : term476 = True.
Proof. exact (TRANS (@lem7241976) (@lem7242023)). Qed.
Lemma lem7242025 : term764 = True.
Proof. exact (TRANS (@lem7241967) (@lem7242024)). Qed.
Lemma lem7242026 : True = term764.
Proof. exact (SYM (@lem7242025)). Qed.
Lemma lem7242027 : term764.
Proof. exact (EQ_MP (@lem7242026) (@lem0)). Qed.
Lemma lem7242028 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term828 _96883 _96886.
Proof. exact (conj (@lem7242027) (@lem7241887 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242030 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7242031 (_96883 : int) (_96886 : int) : term829 _96883 _96886.
Proof. exact (@lem7242030 term340 (term449 _96883 _96886)). Qed.
Lemma lem7242032 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term830 _96883 _96886.
Proof. exact (@lem7242031 _96883 _96886 (@lem7242028 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242033 (_96883 : int) (_96886 : int) : (term831 _96883 _96886) = (term449 _96883 _96886).
Proof. exact (@lem1982733 (term449 _96883 _96886)). Qed.
Lemma lem7242034 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242035 (_96883 : int) (_96886 : int) : (term832 _96883 _96886) = (term458 _96883 _96886).
Proof. exact (MK_COMB (@lem7242034) (@lem7242033 _96883 _96886)). Qed.
Lemma lem7242036 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242037 (_96883 : int) (_96886 : int) : (term830 _96883 _96886) = (term459 _96883 _96886).
Proof. exact (MK_COMB (@lem7242035 _96883 _96886) (@lem7242036)). Qed.
Lemma lem7242038 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term459 _96883 _96886.
Proof. exact (EQ_MP (@lem7242037 _96883 _96886) (@lem7242032 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242040 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7242041 : term764 = term476.
Proof. exact (@lem7242040 term328 term340). Qed.
Lemma lem7242043 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242044 : term340 = term438.
Proof. exact (@lem7242043 term189). Qed.
Lemma lem7242046 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242047 : term328 = term390.
Proof. exact (@lem7242046 (NUMERAL 0)). Qed.
Lemma lem7242048 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242049 : term765 = term766.
Proof. exact (MK_COMB (@lem7242048) (@lem7242047)). Qed.
Lemma lem7242050 : term476 = term767.
Proof. exact (MK_COMB (@lem7242049) (@lem7242044)). Qed.
Lemma lem7242051 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7242053 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242054 : term476 = term477.
Proof. exact (@lem7242053 (NUMERAL 0) term189). Qed.
Lemma lem7242055 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242056 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242057 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242056 h1) (fun h1 : term477 = True => @lem7242055)). Qed.
Lemma lem7242058 : term477 = True.
Proof. exact (EQ_MP (@lem7242057) (@lem7242055)). Qed.
Lemma lem7242059 : term476 = True.
Proof. exact (TRANS (@lem7242054) (@lem7242058)). Qed.
Lemma lem7242060 : True = term476.
Proof. exact (SYM (@lem7242059)). Qed.
Lemma lem7242061 : term476.
Proof. exact (EQ_MP (@lem7242060) (@lem0)). Qed.
Lemma lem7242062 : term769.
Proof. exact (@lem7242051 (@lem7242061)). Qed.
Lemma lem7242064 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242065 : term476 = term477.
Proof. exact (@lem7242064 (NUMERAL 0) term189). Qed.
Lemma lem7242066 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242067 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242068 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242067 h1) (fun h1 : term477 = True => @lem7242066)). Qed.
Lemma lem7242069 : term477 = True.
Proof. exact (EQ_MP (@lem7242068) (@lem7242066)). Qed.
Lemma lem7242070 : term476 = True.
Proof. exact (TRANS (@lem7242065) (@lem7242069)). Qed.
Lemma lem7242071 : True = term476.
Proof. exact (SYM (@lem7242070)). Qed.
Lemma lem7242072 : term476.
Proof. exact (EQ_MP (@lem7242071) (@lem0)). Qed.
Lemma lem7242073 : term767 = term770.
Proof. exact (@lem7242062 (@lem7242072)). Qed.
Lemma lem7242075 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242076 : term402 = term403.
Proof. exact (@lem7242075 term189 term189). Qed.
Lemma lem7242077 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242078 : term405 = term189.
Proof. exact (EQ_MP (@lem7242077) (@lem940073)). Qed.
Lemma lem7242079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242080 : term403 = term340.
Proof. exact (MK_COMB (@lem7242079) (@lem7242078)). Qed.
Lemma lem7242081 : term402 = term340.
Proof. exact (TRANS (@lem7242076) (@lem7242080)). Qed.
Lemma lem7242083 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242084 : term488 = term328.
Proof. exact (@lem7242083 term189). Qed.
Lemma lem7242085 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242086 : term771 = term765.
Proof. exact (MK_COMB (@lem7242085) (@lem7242084)). Qed.
Lemma lem7242087 : term770 = term476.
Proof. exact (MK_COMB (@lem7242086) (@lem7242081)). Qed.
Lemma lem7242089 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242090 : term476 = term477.
Proof. exact (@lem7242089 (NUMERAL 0) term189). Qed.
Lemma lem7242091 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242092 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242093 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242092 h1) (fun h1 : term477 = True => @lem7242091)). Qed.
Lemma lem7242094 : term477 = True.
Proof. exact (EQ_MP (@lem7242093) (@lem7242091)). Qed.
Lemma lem7242095 : term476 = True.
Proof. exact (TRANS (@lem7242090) (@lem7242094)). Qed.
Lemma lem7242096 : term770 = True.
Proof. exact (TRANS (@lem7242087) (@lem7242095)). Qed.
Lemma lem7242097 : term767 = True.
Proof. exact (TRANS (@lem7242073) (@lem7242096)). Qed.
Lemma lem7242098 : term476 = True.
Proof. exact (TRANS (@lem7242050) (@lem7242097)). Qed.
Lemma lem7242099 : term764 = True.
Proof. exact (TRANS (@lem7242041) (@lem7242098)). Qed.
Lemma lem7242100 : True = term764.
Proof. exact (SYM (@lem7242099)). Qed.
Lemma lem7242101 : term764.
Proof. exact (EQ_MP (@lem7242100) (@lem0)). Qed.
Lemma lem7242102 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term850 _96883 _96884.
Proof. exact (conj (@lem7242101) (@lem7241884 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242104 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7242105 (_96883 : int) (_96884 : int) : term851 _96883 _96884.
Proof. exact (@lem7242104 term340 (term417 _96883 _96884)). Qed.
Lemma lem7242106 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term852 _96883 _96884.
Proof. exact (@lem7242105 _96883 _96884 (@lem7242102 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242107 (_96883 : int) (_96884 : int) : (term853 _96883 _96884) = (term417 _96883 _96884).
Proof. exact (@lem1982733 (term417 _96883 _96884)). Qed.
Lemma lem7242108 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242109 (_96883 : int) (_96884 : int) : (term854 _96883 _96884) = (term420 _96883 _96884).
Proof. exact (MK_COMB (@lem7242108) (@lem7242107 _96883 _96884)). Qed.
Lemma lem7242110 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242111 (_96883 : int) (_96884 : int) : (term852 _96883 _96884) = (term421 _96883 _96884).
Proof. exact (MK_COMB (@lem7242109 _96883 _96884) (@lem7242110)). Qed.
Lemma lem7242112 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term421 _96883 _96884.
Proof. exact (EQ_MP (@lem7242111 _96883 _96884) (@lem7242106 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242113 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term855 _96884 _96883 _96886.
Proof. exact (conj (@lem7242112 _96884 _96885 _96883 _96886 h1) (@lem7242038 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242115 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7242116 (_96884 : int) (_96883 : int) (_96886 : int) : term856 _96884 _96883 _96886.
Proof. exact (@lem7242115 (term417 _96883 _96884) (term449 _96883 _96886)). Qed.
Lemma lem7242117 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term857 _96884 _96883 _96886.
Proof. exact (@lem7242116 _96884 _96883 _96886 (@lem7242113 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242118 (_96883 : int) (_96884 : int) (_96886 : int) : (term858 _96884 _96883 _96886) = (term859 _96883 _96884 _96886).
Proof. exact (@lem1982753 (term418 _96883) (real_of_int _96883) (term342 _96884) (term448 _96886)). Qed.
Lemma lem7242119 (_96883 : int) : (term789 _96883) = (term790 _96883).
Proof. exact (@lem1982713 term393 (real_of_int _96883)). Qed.
Lemma lem7242121 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242122 : term340 = term438.
Proof. exact (@lem7242121 term189). Qed.
Lemma lem7242124 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7242125 : term393 = term394.
Proof. exact (@lem7242124 term189). Qed.
Lemma lem7242126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242127 : term791 = term792.
Proof. exact (MK_COMB (@lem7242126) (@lem7242125)). Qed.
Lemma lem7242128 : term793 = term794.
Proof. exact (MK_COMB (@lem7242127) (@lem7242122)). Qed.
Lemma lem7242129 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7242131 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242132 : term476 = term477.
Proof. exact (@lem7242131 (NUMERAL 0) term189). Qed.
Lemma lem7242133 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242134 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242135 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242134 h1) (fun h1 : term477 = True => @lem7242133)). Qed.
Lemma lem7242136 : term477 = True.
Proof. exact (EQ_MP (@lem7242135) (@lem7242133)). Qed.
Lemma lem7242137 : term476 = True.
Proof. exact (TRANS (@lem7242132) (@lem7242136)). Qed.
Lemma lem7242138 : True = term476.
Proof. exact (SYM (@lem7242137)). Qed.
Lemma lem7242139 : term476.
Proof. exact (EQ_MP (@lem7242138) (@lem0)). Qed.
Lemma lem7242140 : term796.
Proof. exact (@lem7242129 (@lem7242139)). Qed.
Lemma lem7242142 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242143 : term476 = term477.
Proof. exact (@lem7242142 (NUMERAL 0) term189). Qed.
Lemma lem7242144 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242145 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242146 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242145 h1) (fun h1 : term477 = True => @lem7242144)). Qed.
Lemma lem7242147 : term477 = True.
Proof. exact (EQ_MP (@lem7242146) (@lem7242144)). Qed.
Lemma lem7242148 : term476 = True.
Proof. exact (TRANS (@lem7242143) (@lem7242147)). Qed.
Lemma lem7242149 : True = term476.
Proof. exact (SYM (@lem7242148)). Qed.
Lemma lem7242150 : term476.
Proof. exact (EQ_MP (@lem7242149) (@lem0)). Qed.
Lemma lem7242151 : term797.
Proof. exact (@lem7242140 (@lem7242150)). Qed.
Lemma lem7242153 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242154 : term476 = term477.
Proof. exact (@lem7242153 (NUMERAL 0) term189). Qed.
Lemma lem7242155 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242156 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242157 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242156 h1) (fun h1 : term477 = True => @lem7242155)). Qed.
Lemma lem7242158 : term477 = True.
Proof. exact (EQ_MP (@lem7242157) (@lem7242155)). Qed.
Lemma lem7242159 : term476 = True.
Proof. exact (TRANS (@lem7242154) (@lem7242158)). Qed.
Lemma lem7242160 : True = term476.
Proof. exact (SYM (@lem7242159)). Qed.
Lemma lem7242161 : term476.
Proof. exact (EQ_MP (@lem7242160) (@lem0)). Qed.
Lemma lem7242162 : term798.
Proof. exact (@lem7242151 (@lem7242161)). Qed.
Lemma lem7242164 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242165 : term402 = term403.
Proof. exact (@lem7242164 term189 term189). Qed.
Lemma lem7242166 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242167 : term405 = term189.
Proof. exact (EQ_MP (@lem7242166) (@lem940073)). Qed.
Lemma lem7242168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242169 : term403 = term340.
Proof. exact (MK_COMB (@lem7242168) (@lem7242167)). Qed.
Lemma lem7242170 : term402 = term340.
Proof. exact (TRANS (@lem7242165) (@lem7242169)). Qed.
Lemma lem7242172 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7242173 : term439 = term444.
Proof. exact (@lem7242172 term189 term189). Qed.
Lemma lem7242174 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242175 : term405 = term189.
Proof. exact (EQ_MP (@lem7242174) (@lem940073)). Qed.
Lemma lem7242176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242177 : term403 = term340.
Proof. exact (MK_COMB (@lem7242176) (@lem7242175)). Qed.
Lemma lem7242178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7242179 : term444 = term393.
Proof. exact (MK_COMB (@lem7242178) (@lem7242177)). Qed.
Lemma lem7242180 : term439 = term393.
Proof. exact (TRANS (@lem7242173) (@lem7242179)). Qed.
Lemma lem7242181 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242182 : term799 = term791.
Proof. exact (MK_COMB (@lem7242181) (@lem7242180)). Qed.
Lemma lem7242183 : term800 = term793.
Proof. exact (MK_COMB (@lem7242182) (@lem7242170)). Qed.
Lemma lem7242185 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7242186 : term793 = term328.
Proof. exact (@lem7242185 term189). Qed.
Lemma lem7242187 : term800 = term328.
Proof. exact (TRANS (@lem7242183) (@lem7242186)). Qed.
Lemma lem7242188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242189 : term802 = term486.
Proof. exact (MK_COMB (@lem7242188) (@lem7242187)). Qed.
Lemma lem7242190 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7242191 : term803 = term488.
Proof. exact (MK_COMB (@lem7242189) (@lem7242190)). Qed.
Lemma lem7242193 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242194 : term488 = term328.
Proof. exact (@lem7242193 term189). Qed.
Lemma lem7242195 : term803 = term328.
Proof. exact (TRANS (@lem7242191) (@lem7242194)). Qed.
Lemma lem7242197 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242198 : term402 = term403.
Proof. exact (@lem7242197 term189 term189). Qed.
Lemma lem7242199 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242200 : term405 = term189.
Proof. exact (EQ_MP (@lem7242199) (@lem940073)). Qed.
Lemma lem7242201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242202 : term403 = term340.
Proof. exact (MK_COMB (@lem7242201) (@lem7242200)). Qed.
Lemma lem7242203 : term402 = term340.
Proof. exact (TRANS (@lem7242198) (@lem7242202)). Qed.
Lemma lem7242204 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7242205 : term490 = term488.
Proof. exact (MK_COMB (@lem7242204) (@lem7242203)). Qed.
Lemma lem7242207 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242208 : term488 = term328.
Proof. exact (@lem7242207 term189). Qed.
Lemma lem7242209 : term490 = term328.
Proof. exact (TRANS (@lem7242205) (@lem7242208)). Qed.
Lemma lem7242210 : term328 = term490.
Proof. exact (SYM (@lem7242209)). Qed.
Lemma lem7242211 : term803 = term490.
Proof. exact (TRANS (@lem7242195) (@lem7242210)). Qed.
Lemma lem7242212 : term794 = term390.
Proof. exact (@lem7242162 (@lem7242211)). Qed.
Lemma lem7242213 : term793 = term390.
Proof. exact (TRANS (@lem7242128) (@lem7242212)). Qed.
Lemma lem7242215 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7242216 : term390 = term328.
Proof. exact (@lem7242215 term328). Qed.
Lemma lem7242217 : term793 = term328.
Proof. exact (TRANS (@lem7242213) (@lem7242216)). Qed.
Lemma lem7242218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242219 : term804 = term486.
Proof. exact (MK_COMB (@lem7242218) (@lem7242217)). Qed.
Lemma lem7242220 (_96883 : int) : (real_of_int _96883) = (real_of_int _96883).
Proof. exact (eq_refl (real_of_int _96883)). Qed.
Lemma lem7242221 (_96883 : int) : (term790 _96883) = (term805 _96883).
Proof. exact (MK_COMB (@lem7242219) (@lem7242220 _96883)). Qed.
Lemma lem7242222 (_96883 : int) : (term789 _96883) = (term805 _96883).
Proof. exact (TRANS (@lem7242119 _96883) (@lem7242221 _96883)). Qed.
Lemma lem7242223 (_96883 : int) : (term805 _96883) = term328.
Proof. exact (@lem1982719 (real_of_int _96883)). Qed.
Lemma lem7242224 (_96883 : int) : (term789 _96883) = term328.
Proof. exact (TRANS (@lem7242222 _96883) (@lem7242223 _96883)). Qed.
Lemma lem7242225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242226 (_96883 : int) : (term806 _96883) = term807.
Proof. exact (MK_COMB (@lem7242225) (@lem7242224 _96883)). Qed.
Lemma lem7242227 (_96884 : int) (_96886 : int) : (term466 _96884 _96886) = (term467 _96884 _96886).
Proof. exact (@lem1982755 (real_of_int _96884) term340 (term448 _96886)). Qed.
Lemma lem7242228 (_96886 : int) : (term468 _96886) = (term469 _96886).
Proof. exact (@lem1982757 (term418 _96886) term340 term393). Qed.
Lemma lem7242230 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7242231 : term393 = term394.
Proof. exact (@lem7242230 term189). Qed.
Lemma lem7242233 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242234 : term340 = term438.
Proof. exact (@lem7242233 term189). Qed.
Lemma lem7242235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242236 : term470 = term471.
Proof. exact (MK_COMB (@lem7242235) (@lem7242234)). Qed.
Lemma lem7242237 : term472 = term473.
Proof. exact (MK_COMB (@lem7242236) (@lem7242231)). Qed.
Lemma lem7242238 : term474.
Proof. exact (@lem1981473 term340 term340 term393 term340 term328 term340). Qed.
Lemma lem7242240 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242241 : term476 = term477.
Proof. exact (@lem7242240 (NUMERAL 0) term189). Qed.
Lemma lem7242242 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242243 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242244 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242243 h1) (fun h1 : term477 = True => @lem7242242)). Qed.
Lemma lem7242245 : term477 = True.
Proof. exact (EQ_MP (@lem7242244) (@lem7242242)). Qed.
Lemma lem7242246 : term476 = True.
Proof. exact (TRANS (@lem7242241) (@lem7242245)). Qed.
Lemma lem7242247 : True = term476.
Proof. exact (SYM (@lem7242246)). Qed.
Lemma lem7242248 : term476.
Proof. exact (EQ_MP (@lem7242247) (@lem0)). Qed.
Lemma lem7242249 : term479.
Proof. exact (@lem7242238 (@lem7242248)). Qed.
Lemma lem7242251 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242252 : term476 = term477.
Proof. exact (@lem7242251 (NUMERAL 0) term189). Qed.
Lemma lem7242253 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242254 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242255 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242254 h1) (fun h1 : term477 = True => @lem7242253)). Qed.
Lemma lem7242256 : term477 = True.
Proof. exact (EQ_MP (@lem7242255) (@lem7242253)). Qed.
Lemma lem7242257 : term476 = True.
Proof. exact (TRANS (@lem7242252) (@lem7242256)). Qed.
Lemma lem7242258 : True = term476.
Proof. exact (SYM (@lem7242257)). Qed.
Lemma lem7242259 : term476.
Proof. exact (EQ_MP (@lem7242258) (@lem0)). Qed.
Lemma lem7242260 : term480.
Proof. exact (@lem7242249 (@lem7242259)). Qed.
Lemma lem7242262 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242263 : term476 = term477.
Proof. exact (@lem7242262 (NUMERAL 0) term189). Qed.
Lemma lem7242264 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242265 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242266 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242265 h1) (fun h1 : term477 = True => @lem7242264)). Qed.
Lemma lem7242267 : term477 = True.
Proof. exact (EQ_MP (@lem7242266) (@lem7242264)). Qed.
Lemma lem7242268 : term476 = True.
Proof. exact (TRANS (@lem7242263) (@lem7242267)). Qed.
Lemma lem7242269 : True = term476.
Proof. exact (SYM (@lem7242268)). Qed.
Lemma lem7242270 : term476.
Proof. exact (EQ_MP (@lem7242269) (@lem0)). Qed.
Lemma lem7242271 : term481.
Proof. exact (@lem7242260 (@lem7242270)). Qed.
Lemma lem7242273 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7242274 : term439 = term444.
Proof. exact (@lem7242273 term189 term189). Qed.
Lemma lem7242275 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242276 : term405 = term189.
Proof. exact (EQ_MP (@lem7242275) (@lem940073)). Qed.
Lemma lem7242277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242278 : term403 = term340.
Proof. exact (MK_COMB (@lem7242277) (@lem7242276)). Qed.
Lemma lem7242279 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7242280 : term444 = term393.
Proof. exact (MK_COMB (@lem7242279) (@lem7242278)). Qed.
Lemma lem7242281 : term439 = term393.
Proof. exact (TRANS (@lem7242274) (@lem7242280)). Qed.
Lemma lem7242283 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242284 : term402 = term403.
Proof. exact (@lem7242283 term189 term189). Qed.
Lemma lem7242285 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242286 : term405 = term189.
Proof. exact (EQ_MP (@lem7242285) (@lem940073)). Qed.
Lemma lem7242287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242288 : term403 = term340.
Proof. exact (MK_COMB (@lem7242287) (@lem7242286)). Qed.
Lemma lem7242289 : term402 = term340.
Proof. exact (TRANS (@lem7242284) (@lem7242288)). Qed.
Lemma lem7242290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242291 : term482 = term470.
Proof. exact (MK_COMB (@lem7242290) (@lem7242289)). Qed.
Lemma lem7242292 : term483 = term472.
Proof. exact (MK_COMB (@lem7242291) (@lem7242281)). Qed.
Lemma lem7242294 (m : nat) : (term484 m) = term328.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7242295 : term472 = term328.
Proof. exact (@lem7242294 term189). Qed.
Lemma lem7242296 : term483 = term328.
Proof. exact (TRANS (@lem7242292) (@lem7242295)). Qed.
Lemma lem7242297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242298 : term485 = term486.
Proof. exact (MK_COMB (@lem7242297) (@lem7242296)). Qed.
Lemma lem7242299 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7242300 : term487 = term488.
Proof. exact (MK_COMB (@lem7242298) (@lem7242299)). Qed.
Lemma lem7242302 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242303 : term488 = term328.
Proof. exact (@lem7242302 term189). Qed.
Lemma lem7242304 : term487 = term328.
Proof. exact (TRANS (@lem7242300) (@lem7242303)). Qed.
Lemma lem7242306 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242307 : term402 = term403.
Proof. exact (@lem7242306 term189 term189). Qed.
Lemma lem7242308 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242309 : term405 = term189.
Proof. exact (EQ_MP (@lem7242308) (@lem940073)). Qed.
Lemma lem7242310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242311 : term403 = term340.
Proof. exact (MK_COMB (@lem7242310) (@lem7242309)). Qed.
Lemma lem7242312 : term402 = term340.
Proof. exact (TRANS (@lem7242307) (@lem7242311)). Qed.
Lemma lem7242313 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7242314 : term490 = term488.
Proof. exact (MK_COMB (@lem7242313) (@lem7242312)). Qed.
Lemma lem7242316 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242317 : term488 = term328.
Proof. exact (@lem7242316 term189). Qed.
Lemma lem7242318 : term490 = term328.
Proof. exact (TRANS (@lem7242314) (@lem7242317)). Qed.
Lemma lem7242319 : term328 = term490.
Proof. exact (SYM (@lem7242318)). Qed.
Lemma lem7242320 : term487 = term490.
Proof. exact (TRANS (@lem7242304) (@lem7242319)). Qed.
Lemma lem7242321 : term473 = term390.
Proof. exact (@lem7242271 (@lem7242320)). Qed.
Lemma lem7242322 : term472 = term390.
Proof. exact (TRANS (@lem7242237) (@lem7242321)). Qed.
Lemma lem7242324 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7242325 : term390 = term328.
Proof. exact (@lem7242324 term328). Qed.
Lemma lem7242326 : term472 = term328.
Proof. exact (TRANS (@lem7242322) (@lem7242325)). Qed.
Lemma lem7242327 (_96886 : int) : (term447 _96886) = (term447 _96886).
Proof. exact (eq_refl (term447 _96886)). Qed.
Lemma lem7242328 (_96886 : int) : (term469 _96886) = (term491 _96886).
Proof. exact (MK_COMB (@lem7242327 _96886) (@lem7242326)). Qed.
Lemma lem7242329 (_96886 : int) : (term468 _96886) = (term491 _96886).
Proof. exact (TRANS (@lem7242228 _96886) (@lem7242328 _96886)). Qed.
Lemma lem7242330 (_96886 : int) : (term491 _96886) = (term418 _96886).
Proof. exact (@lem1982723 (term418 _96886)). Qed.
Lemma lem7242331 (_96886 : int) : (term468 _96886) = (term418 _96886).
Proof. exact (TRANS (@lem7242329 _96886) (@lem7242330 _96886)). Qed.
Lemma lem7242332 (_96884 : int) : (term341 _96884) = (term341 _96884).
Proof. exact (eq_refl (term341 _96884)). Qed.
Lemma lem7242333 (_96884 : int) (_96886 : int) : (term467 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (MK_COMB (@lem7242332 _96884) (@lem7242331 _96886)). Qed.
Lemma lem7242334 (_96884 : int) (_96886 : int) : (term466 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (TRANS (@lem7242227 _96884 _96886) (@lem7242333 _96884 _96886)). Qed.
Lemma lem7242335 (_96883 : int) (_96884 : int) (_96886 : int) : (term859 _96883 _96884 _96886) = (term860 _96884 _96886).
Proof. exact (MK_COMB (@lem7242226 _96883) (@lem7242334 _96884 _96886)). Qed.
Lemma lem7242336 (_96883 : int) (_96884 : int) (_96886 : int) : (term858 _96884 _96883 _96886) = (term860 _96884 _96886).
Proof. exact (TRANS (@lem7242118 _96883 _96884 _96886) (@lem7242335 _96883 _96884 _96886)). Qed.
Lemma lem7242337 (_96884 : int) (_96886 : int) : (term860 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982721 (term424 _96884 _96886)). Qed.
Lemma lem7242338 (_96883 : int) (_96884 : int) (_96886 : int) : (term858 _96884 _96883 _96886) = (term424 _96884 _96886).
Proof. exact (TRANS (@lem7242336 _96883 _96884 _96886) (@lem7242337 _96884 _96886)). Qed.
Lemma lem7242339 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242340 (_96883 : int) (_96884 : int) (_96886 : int) : (term861 _96884 _96883 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7242339) (@lem7242338 _96883 _96884 _96886)). Qed.
Lemma lem7242341 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242342 (_96883 : int) (_96884 : int) (_96886 : int) : (term857 _96884 _96883 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7242340 _96883 _96884 _96886) (@lem7242341)). Qed.
Lemma lem7242343 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term430 _96884 _96886.
Proof. exact (EQ_MP (@lem7242342 _96883 _96884 _96886) (@lem7242117 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242345 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7242346 : term764 = term476.
Proof. exact (@lem7242345 term328 term340). Qed.
Lemma lem7242348 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242349 : term340 = term438.
Proof. exact (@lem7242348 term189). Qed.
Lemma lem7242351 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242352 : term328 = term390.
Proof. exact (@lem7242351 (NUMERAL 0)). Qed.
Lemma lem7242353 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242354 : term765 = term766.
Proof. exact (MK_COMB (@lem7242353) (@lem7242352)). Qed.
Lemma lem7242355 : term476 = term767.
Proof. exact (MK_COMB (@lem7242354) (@lem7242349)). Qed.
Lemma lem7242356 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7242358 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242359 : term476 = term477.
Proof. exact (@lem7242358 (NUMERAL 0) term189). Qed.
Lemma lem7242360 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242361 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242362 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242361 h1) (fun h1 : term477 = True => @lem7242360)). Qed.
Lemma lem7242363 : term477 = True.
Proof. exact (EQ_MP (@lem7242362) (@lem7242360)). Qed.
Lemma lem7242364 : term476 = True.
Proof. exact (TRANS (@lem7242359) (@lem7242363)). Qed.
Lemma lem7242365 : True = term476.
Proof. exact (SYM (@lem7242364)). Qed.
Lemma lem7242366 : term476.
Proof. exact (EQ_MP (@lem7242365) (@lem0)). Qed.
Lemma lem7242367 : term769.
Proof. exact (@lem7242356 (@lem7242366)). Qed.
Lemma lem7242369 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242370 : term476 = term477.
Proof. exact (@lem7242369 (NUMERAL 0) term189). Qed.
Lemma lem7242371 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242372 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242373 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242372 h1) (fun h1 : term477 = True => @lem7242371)). Qed.
Lemma lem7242374 : term477 = True.
Proof. exact (EQ_MP (@lem7242373) (@lem7242371)). Qed.
Lemma lem7242375 : term476 = True.
Proof. exact (TRANS (@lem7242370) (@lem7242374)). Qed.
Lemma lem7242376 : True = term476.
Proof. exact (SYM (@lem7242375)). Qed.
Lemma lem7242377 : term476.
Proof. exact (EQ_MP (@lem7242376) (@lem0)). Qed.
Lemma lem7242378 : term767 = term770.
Proof. exact (@lem7242367 (@lem7242377)). Qed.
Lemma lem7242380 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242381 : term402 = term403.
Proof. exact (@lem7242380 term189 term189). Qed.
Lemma lem7242382 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242383 : term405 = term189.
Proof. exact (EQ_MP (@lem7242382) (@lem940073)). Qed.
Lemma lem7242384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242385 : term403 = term340.
Proof. exact (MK_COMB (@lem7242384) (@lem7242383)). Qed.
Lemma lem7242386 : term402 = term340.
Proof. exact (TRANS (@lem7242381) (@lem7242385)). Qed.
Lemma lem7242388 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242389 : term488 = term328.
Proof. exact (@lem7242388 term189). Qed.
Lemma lem7242390 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242391 : term771 = term765.
Proof. exact (MK_COMB (@lem7242390) (@lem7242389)). Qed.
Lemma lem7242392 : term770 = term476.
Proof. exact (MK_COMB (@lem7242391) (@lem7242386)). Qed.
Lemma lem7242394 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242395 : term476 = term477.
Proof. exact (@lem7242394 (NUMERAL 0) term189). Qed.
Lemma lem7242396 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242397 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242398 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242397 h1) (fun h1 : term477 = True => @lem7242396)). Qed.
Lemma lem7242399 : term477 = True.
Proof. exact (EQ_MP (@lem7242398) (@lem7242396)). Qed.
Lemma lem7242400 : term476 = True.
Proof. exact (TRANS (@lem7242395) (@lem7242399)). Qed.
Lemma lem7242401 : term770 = True.
Proof. exact (TRANS (@lem7242392) (@lem7242400)). Qed.
Lemma lem7242402 : term767 = True.
Proof. exact (TRANS (@lem7242378) (@lem7242401)). Qed.
Lemma lem7242403 : term476 = True.
Proof. exact (TRANS (@lem7242355) (@lem7242402)). Qed.
Lemma lem7242404 : term764 = True.
Proof. exact (TRANS (@lem7242346) (@lem7242403)). Qed.
Lemma lem7242405 : True = term764.
Proof. exact (SYM (@lem7242404)). Qed.
Lemma lem7242406 : term764.
Proof. exact (EQ_MP (@lem7242405) (@lem0)). Qed.
Lemma lem7242407 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term772 _96884 _96886.
Proof. exact (conj (@lem7242406) (@lem7242343 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242409 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7242410 (_96884 : int) (_96886 : int) : term774 _96884 _96886.
Proof. exact (@lem7242409 term340 (term424 _96884 _96886)). Qed.
Lemma lem7242411 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term775 _96884 _96886.
Proof. exact (@lem7242410 _96884 _96886 (@lem7242407 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242412 (_96884 : int) (_96886 : int) : (term776 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982733 (term424 _96884 _96886)). Qed.
Lemma lem7242413 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242414 (_96884 : int) (_96886 : int) : (term777 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7242413) (@lem7242412 _96884 _96886)). Qed.
Lemma lem7242415 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242416 (_96884 : int) (_96886 : int) : (term775 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7242414 _96884 _96886) (@lem7242415)). Qed.
Lemma lem7242417 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term430 _96884 _96886.
Proof. exact (EQ_MP (@lem7242416 _96884 _96886) (@lem7242411 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242418 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term862 _96884 _96886.
Proof. exact (conj (@lem7242417 _96884 _96885 _96883 _96886 h1) (@lem7241964 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242420 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7242421 (_96884 : int) (_96886 : int) : term863 _96884 _96886.
Proof. exact (@lem7242420 (term424 _96884 _96886) (term450 _96884 _96886)). Qed.
Lemma lem7242422 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term864 _96884 _96886.
Proof. exact (@lem7242421 _96884 _96886 (@lem7242418 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242423 (_96884 : int) (_96886 : int) : (term865 _96884 _96886) = (term866 _96884 _96886).
Proof. exact (@lem1982753 (real_of_int _96884) (term418 _96884) (term418 _96886) (term788 _96886)). Qed.
Lemma lem7242424 (_96884 : int) : (term810 _96884) = (term790 _96884).
Proof. exact (@lem1982715 term393 (real_of_int _96884)). Qed.
Lemma lem7242426 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242427 : term340 = term438.
Proof. exact (@lem7242426 term189). Qed.
Lemma lem7242429 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7242430 : term393 = term394.
Proof. exact (@lem7242429 term189). Qed.
Lemma lem7242431 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242432 : term791 = term792.
Proof. exact (MK_COMB (@lem7242431) (@lem7242430)). Qed.
Lemma lem7242433 : term793 = term794.
Proof. exact (MK_COMB (@lem7242432) (@lem7242427)). Qed.
Lemma lem7242434 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7242436 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242437 : term476 = term477.
Proof. exact (@lem7242436 (NUMERAL 0) term189). Qed.
Lemma lem7242438 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242439 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242440 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242439 h1) (fun h1 : term477 = True => @lem7242438)). Qed.
Lemma lem7242441 : term477 = True.
Proof. exact (EQ_MP (@lem7242440) (@lem7242438)). Qed.
Lemma lem7242442 : term476 = True.
Proof. exact (TRANS (@lem7242437) (@lem7242441)). Qed.
Lemma lem7242443 : True = term476.
Proof. exact (SYM (@lem7242442)). Qed.
Lemma lem7242444 : term476.
Proof. exact (EQ_MP (@lem7242443) (@lem0)). Qed.
Lemma lem7242445 : term796.
Proof. exact (@lem7242434 (@lem7242444)). Qed.
Lemma lem7242447 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242448 : term476 = term477.
Proof. exact (@lem7242447 (NUMERAL 0) term189). Qed.
Lemma lem7242449 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242450 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242451 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242450 h1) (fun h1 : term477 = True => @lem7242449)). Qed.
Lemma lem7242452 : term477 = True.
Proof. exact (EQ_MP (@lem7242451) (@lem7242449)). Qed.
Lemma lem7242453 : term476 = True.
Proof. exact (TRANS (@lem7242448) (@lem7242452)). Qed.
Lemma lem7242454 : True = term476.
Proof. exact (SYM (@lem7242453)). Qed.
Lemma lem7242455 : term476.
Proof. exact (EQ_MP (@lem7242454) (@lem0)). Qed.
Lemma lem7242456 : term797.
Proof. exact (@lem7242445 (@lem7242455)). Qed.
Lemma lem7242458 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242459 : term476 = term477.
Proof. exact (@lem7242458 (NUMERAL 0) term189). Qed.
Lemma lem7242460 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242461 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242462 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242461 h1) (fun h1 : term477 = True => @lem7242460)). Qed.
Lemma lem7242463 : term477 = True.
Proof. exact (EQ_MP (@lem7242462) (@lem7242460)). Qed.
Lemma lem7242464 : term476 = True.
Proof. exact (TRANS (@lem7242459) (@lem7242463)). Qed.
Lemma lem7242465 : True = term476.
Proof. exact (SYM (@lem7242464)). Qed.
Lemma lem7242466 : term476.
Proof. exact (EQ_MP (@lem7242465) (@lem0)). Qed.
Lemma lem7242467 : term798.
Proof. exact (@lem7242456 (@lem7242466)). Qed.
Lemma lem7242469 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242470 : term402 = term403.
Proof. exact (@lem7242469 term189 term189). Qed.
Lemma lem7242471 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242472 : term405 = term189.
Proof. exact (EQ_MP (@lem7242471) (@lem940073)). Qed.
Lemma lem7242473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242474 : term403 = term340.
Proof. exact (MK_COMB (@lem7242473) (@lem7242472)). Qed.
Lemma lem7242475 : term402 = term340.
Proof. exact (TRANS (@lem7242470) (@lem7242474)). Qed.
Lemma lem7242477 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7242478 : term439 = term444.
Proof. exact (@lem7242477 term189 term189). Qed.
Lemma lem7242479 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242480 : term405 = term189.
Proof. exact (EQ_MP (@lem7242479) (@lem940073)). Qed.
Lemma lem7242481 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242482 : term403 = term340.
Proof. exact (MK_COMB (@lem7242481) (@lem7242480)). Qed.
Lemma lem7242483 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7242484 : term444 = term393.
Proof. exact (MK_COMB (@lem7242483) (@lem7242482)). Qed.
Lemma lem7242485 : term439 = term393.
Proof. exact (TRANS (@lem7242478) (@lem7242484)). Qed.
Lemma lem7242486 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242487 : term799 = term791.
Proof. exact (MK_COMB (@lem7242486) (@lem7242485)). Qed.
Lemma lem7242488 : term800 = term793.
Proof. exact (MK_COMB (@lem7242487) (@lem7242475)). Qed.
Lemma lem7242490 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7242491 : term793 = term328.
Proof. exact (@lem7242490 term189). Qed.
Lemma lem7242492 : term800 = term328.
Proof. exact (TRANS (@lem7242488) (@lem7242491)). Qed.
Lemma lem7242493 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242494 : term802 = term486.
Proof. exact (MK_COMB (@lem7242493) (@lem7242492)). Qed.
Lemma lem7242495 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7242496 : term803 = term488.
Proof. exact (MK_COMB (@lem7242494) (@lem7242495)). Qed.
Lemma lem7242498 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242499 : term488 = term328.
Proof. exact (@lem7242498 term189). Qed.
Lemma lem7242500 : term803 = term328.
Proof. exact (TRANS (@lem7242496) (@lem7242499)). Qed.
Lemma lem7242502 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242503 : term402 = term403.
Proof. exact (@lem7242502 term189 term189). Qed.
Lemma lem7242504 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242505 : term405 = term189.
Proof. exact (EQ_MP (@lem7242504) (@lem940073)). Qed.
Lemma lem7242506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242507 : term403 = term340.
Proof. exact (MK_COMB (@lem7242506) (@lem7242505)). Qed.
Lemma lem7242508 : term402 = term340.
Proof. exact (TRANS (@lem7242503) (@lem7242507)). Qed.
Lemma lem7242509 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7242510 : term490 = term488.
Proof. exact (MK_COMB (@lem7242509) (@lem7242508)). Qed.
Lemma lem7242512 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242513 : term488 = term328.
Proof. exact (@lem7242512 term189). Qed.
Lemma lem7242514 : term490 = term328.
Proof. exact (TRANS (@lem7242510) (@lem7242513)). Qed.
Lemma lem7242515 : term328 = term490.
Proof. exact (SYM (@lem7242514)). Qed.
Lemma lem7242516 : term803 = term490.
Proof. exact (TRANS (@lem7242500) (@lem7242515)). Qed.
Lemma lem7242517 : term794 = term390.
Proof. exact (@lem7242467 (@lem7242516)). Qed.
Lemma lem7242518 : term793 = term390.
Proof. exact (TRANS (@lem7242433) (@lem7242517)). Qed.
Lemma lem7242520 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7242521 : term390 = term328.
Proof. exact (@lem7242520 term328). Qed.
Lemma lem7242522 : term793 = term328.
Proof. exact (TRANS (@lem7242518) (@lem7242521)). Qed.
Lemma lem7242523 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242524 : term804 = term486.
Proof. exact (MK_COMB (@lem7242523) (@lem7242522)). Qed.
Lemma lem7242525 (_96884 : int) : (real_of_int _96884) = (real_of_int _96884).
Proof. exact (eq_refl (real_of_int _96884)). Qed.
Lemma lem7242526 (_96884 : int) : (term790 _96884) = (term805 _96884).
Proof. exact (MK_COMB (@lem7242524) (@lem7242525 _96884)). Qed.
Lemma lem7242527 (_96884 : int) : (term810 _96884) = (term805 _96884).
Proof. exact (TRANS (@lem7242424 _96884) (@lem7242526 _96884)). Qed.
Lemma lem7242528 (_96884 : int) : (term805 _96884) = term328.
Proof. exact (@lem1982719 (real_of_int _96884)). Qed.
Lemma lem7242529 (_96884 : int) : (term810 _96884) = term328.
Proof. exact (TRANS (@lem7242527 _96884) (@lem7242528 _96884)). Qed.
Lemma lem7242530 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242531 (_96884 : int) : (term811 _96884) = term807.
Proof. exact (MK_COMB (@lem7242530) (@lem7242529 _96884)). Qed.
Lemma lem7242532 (_96886 : int) : (term867 _96886) = (term868 _96886).
Proof. exact (@lem1982763 (term418 _96886) (real_of_int _96886) term393). Qed.
Lemma lem7242533 (_96886 : int) : (term789 _96886) = (term790 _96886).
Proof. exact (@lem1982713 term393 (real_of_int _96886)). Qed.
Lemma lem7242535 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242536 : term340 = term438.
Proof. exact (@lem7242535 term189). Qed.
Lemma lem7242538 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7242539 : term393 = term394.
Proof. exact (@lem7242538 term189). Qed.
Lemma lem7242540 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242541 : term791 = term792.
Proof. exact (MK_COMB (@lem7242540) (@lem7242539)). Qed.
Lemma lem7242542 : term793 = term794.
Proof. exact (MK_COMB (@lem7242541) (@lem7242536)). Qed.
Lemma lem7242543 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7242545 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242546 : term476 = term477.
Proof. exact (@lem7242545 (NUMERAL 0) term189). Qed.
Lemma lem7242547 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242548 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242549 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242548 h1) (fun h1 : term477 = True => @lem7242547)). Qed.
Lemma lem7242550 : term477 = True.
Proof. exact (EQ_MP (@lem7242549) (@lem7242547)). Qed.
Lemma lem7242551 : term476 = True.
Proof. exact (TRANS (@lem7242546) (@lem7242550)). Qed.
Lemma lem7242552 : True = term476.
Proof. exact (SYM (@lem7242551)). Qed.
Lemma lem7242553 : term476.
Proof. exact (EQ_MP (@lem7242552) (@lem0)). Qed.
Lemma lem7242554 : term796.
Proof. exact (@lem7242543 (@lem7242553)). Qed.
Lemma lem7242556 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242557 : term476 = term477.
Proof. exact (@lem7242556 (NUMERAL 0) term189). Qed.
Lemma lem7242558 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242559 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242560 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242559 h1) (fun h1 : term477 = True => @lem7242558)). Qed.
Lemma lem7242561 : term477 = True.
Proof. exact (EQ_MP (@lem7242560) (@lem7242558)). Qed.
Lemma lem7242562 : term476 = True.
Proof. exact (TRANS (@lem7242557) (@lem7242561)). Qed.
Lemma lem7242563 : True = term476.
Proof. exact (SYM (@lem7242562)). Qed.
Lemma lem7242564 : term476.
Proof. exact (EQ_MP (@lem7242563) (@lem0)). Qed.
Lemma lem7242565 : term797.
Proof. exact (@lem7242554 (@lem7242564)). Qed.
Lemma lem7242567 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242568 : term476 = term477.
Proof. exact (@lem7242567 (NUMERAL 0) term189). Qed.
Lemma lem7242569 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242570 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242571 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242570 h1) (fun h1 : term477 = True => @lem7242569)). Qed.
Lemma lem7242572 : term477 = True.
Proof. exact (EQ_MP (@lem7242571) (@lem7242569)). Qed.
Lemma lem7242573 : term476 = True.
Proof. exact (TRANS (@lem7242568) (@lem7242572)). Qed.
Lemma lem7242574 : True = term476.
Proof. exact (SYM (@lem7242573)). Qed.
Lemma lem7242575 : term476.
Proof. exact (EQ_MP (@lem7242574) (@lem0)). Qed.
Lemma lem7242576 : term798.
Proof. exact (@lem7242565 (@lem7242575)). Qed.
Lemma lem7242578 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242579 : term402 = term403.
Proof. exact (@lem7242578 term189 term189). Qed.
Lemma lem7242580 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242581 : term405 = term189.
Proof. exact (EQ_MP (@lem7242580) (@lem940073)). Qed.
Lemma lem7242582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242583 : term403 = term340.
Proof. exact (MK_COMB (@lem7242582) (@lem7242581)). Qed.
Lemma lem7242584 : term402 = term340.
Proof. exact (TRANS (@lem7242579) (@lem7242583)). Qed.
Lemma lem7242586 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7242587 : term439 = term444.
Proof. exact (@lem7242586 term189 term189). Qed.
Lemma lem7242588 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242589 : term405 = term189.
Proof. exact (EQ_MP (@lem7242588) (@lem940073)). Qed.
Lemma lem7242590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242591 : term403 = term340.
Proof. exact (MK_COMB (@lem7242590) (@lem7242589)). Qed.
Lemma lem7242592 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7242593 : term444 = term393.
Proof. exact (MK_COMB (@lem7242592) (@lem7242591)). Qed.
Lemma lem7242594 : term439 = term393.
Proof. exact (TRANS (@lem7242587) (@lem7242593)). Qed.
Lemma lem7242595 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242596 : term799 = term791.
Proof. exact (MK_COMB (@lem7242595) (@lem7242594)). Qed.
Lemma lem7242597 : term800 = term793.
Proof. exact (MK_COMB (@lem7242596) (@lem7242584)). Qed.
Lemma lem7242599 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7242600 : term793 = term328.
Proof. exact (@lem7242599 term189). Qed.
Lemma lem7242601 : term800 = term328.
Proof. exact (TRANS (@lem7242597) (@lem7242600)). Qed.
Lemma lem7242602 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242603 : term802 = term486.
Proof. exact (MK_COMB (@lem7242602) (@lem7242601)). Qed.
Lemma lem7242604 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7242605 : term803 = term488.
Proof. exact (MK_COMB (@lem7242603) (@lem7242604)). Qed.
Lemma lem7242607 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242608 : term488 = term328.
Proof. exact (@lem7242607 term189). Qed.
Lemma lem7242609 : term803 = term328.
Proof. exact (TRANS (@lem7242605) (@lem7242608)). Qed.
Lemma lem7242611 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242612 : term402 = term403.
Proof. exact (@lem7242611 term189 term189). Qed.
Lemma lem7242613 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242614 : term405 = term189.
Proof. exact (EQ_MP (@lem7242613) (@lem940073)). Qed.
Lemma lem7242615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242616 : term403 = term340.
Proof. exact (MK_COMB (@lem7242615) (@lem7242614)). Qed.
Lemma lem7242617 : term402 = term340.
Proof. exact (TRANS (@lem7242612) (@lem7242616)). Qed.
Lemma lem7242618 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7242619 : term490 = term488.
Proof. exact (MK_COMB (@lem7242618) (@lem7242617)). Qed.
Lemma lem7242621 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242622 : term488 = term328.
Proof. exact (@lem7242621 term189). Qed.
Lemma lem7242623 : term490 = term328.
Proof. exact (TRANS (@lem7242619) (@lem7242622)). Qed.
Lemma lem7242624 : term328 = term490.
Proof. exact (SYM (@lem7242623)). Qed.
Lemma lem7242625 : term803 = term490.
Proof. exact (TRANS (@lem7242609) (@lem7242624)). Qed.
Lemma lem7242626 : term794 = term390.
Proof. exact (@lem7242576 (@lem7242625)). Qed.
Lemma lem7242627 : term793 = term390.
Proof. exact (TRANS (@lem7242542) (@lem7242626)). Qed.
Lemma lem7242629 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7242630 : term390 = term328.
Proof. exact (@lem7242629 term328). Qed.
Lemma lem7242631 : term793 = term328.
Proof. exact (TRANS (@lem7242627) (@lem7242630)). Qed.
Lemma lem7242632 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7242633 : term804 = term486.
Proof. exact (MK_COMB (@lem7242632) (@lem7242631)). Qed.
Lemma lem7242634 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7242635 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7242633) (@lem7242634 _96886)). Qed.
Lemma lem7242636 (_96886 : int) : (term789 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7242533 _96886) (@lem7242635 _96886)). Qed.
Lemma lem7242637 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7242638 (_96886 : int) : (term789 _96886) = term328.
Proof. exact (TRANS (@lem7242636 _96886) (@lem7242637 _96886)). Qed.
Lemma lem7242639 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242640 (_96886 : int) : (term806 _96886) = term807.
Proof. exact (MK_COMB (@lem7242639) (@lem7242638 _96886)). Qed.
Lemma lem7242641 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7242642 (_96886 : int) : (term868 _96886) = term812.
Proof. exact (MK_COMB (@lem7242640 _96886) (@lem7242641)). Qed.
Lemma lem7242643 (_96886 : int) : (term867 _96886) = term812.
Proof. exact (TRANS (@lem7242532 _96886) (@lem7242642 _96886)). Qed.
Lemma lem7242644 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7242645 (_96886 : int) : (term867 _96886) = term393.
Proof. exact (TRANS (@lem7242643 _96886) (@lem7242644)). Qed.
Lemma lem7242646 (_96884 : int) (_96886 : int) : (term866 _96884 _96886) = term812.
Proof. exact (MK_COMB (@lem7242531 _96884) (@lem7242645 _96886)). Qed.
Lemma lem7242647 (_96884 : int) (_96886 : int) : (term865 _96884 _96886) = term812.
Proof. exact (TRANS (@lem7242423 _96884 _96886) (@lem7242646 _96884 _96886)). Qed.
Lemma lem7242648 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7242649 (_96884 : int) (_96886 : int) : (term865 _96884 _96886) = term393.
Proof. exact (TRANS (@lem7242647 _96884 _96886) (@lem7242648)). Qed.
Lemma lem7242650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242651 (_96884 : int) (_96886 : int) : (term869 _96884 _96886) = term814.
Proof. exact (MK_COMB (@lem7242650) (@lem7242649 _96884 _96886)). Qed.
Lemma lem7242652 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242653 (_96884 : int) (_96886 : int) : (term864 _96884 _96886) = term815.
Proof. exact (MK_COMB (@lem7242651 _96884 _96886) (@lem7242652)). Qed.
Lemma lem7242654 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : term815.
Proof. exact (EQ_MP (@lem7242653 _96884 _96886) (@lem7242422 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242656 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7242657 : term815 = term816.
Proof. exact (@lem7242656 term328 term393). Qed.
Lemma lem7242659 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7242660 : term393 = term394.
Proof. exact (@lem7242659 term189). Qed.
Lemma lem7242662 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242663 : term328 = term390.
Proof. exact (@lem7242662 (NUMERAL 0)). Qed.
Lemma lem7242664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7242665 : term330 = term817.
Proof. exact (MK_COMB (@lem7242664) (@lem7242663)). Qed.
Lemma lem7242666 : term816 = term818.
Proof. exact (MK_COMB (@lem7242665) (@lem7242660)). Qed.
Lemma lem7242667 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7242669 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242670 : term476 = term477.
Proof. exact (@lem7242669 (NUMERAL 0) term189). Qed.
Lemma lem7242671 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242672 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242673 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242672 h1) (fun h1 : term477 = True => @lem7242671)). Qed.
Lemma lem7242674 : term477 = True.
Proof. exact (EQ_MP (@lem7242673) (@lem7242671)). Qed.
Lemma lem7242675 : term476 = True.
Proof. exact (TRANS (@lem7242670) (@lem7242674)). Qed.
Lemma lem7242676 : True = term476.
Proof. exact (SYM (@lem7242675)). Qed.
Lemma lem7242677 : term476.
Proof. exact (EQ_MP (@lem7242676) (@lem0)). Qed.
Lemma lem7242678 : term820.
Proof. exact (@lem7242667 (@lem7242677)). Qed.
Lemma lem7242680 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242681 : term476 = term477.
Proof. exact (@lem7242680 (NUMERAL 0) term189). Qed.
Lemma lem7242682 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242683 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242684 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242683 h1) (fun h1 : term477 = True => @lem7242682)). Qed.
Lemma lem7242685 : term477 = True.
Proof. exact (EQ_MP (@lem7242684) (@lem7242682)). Qed.
Lemma lem7242686 : term476 = True.
Proof. exact (TRANS (@lem7242681) (@lem7242685)). Qed.
Lemma lem7242687 : True = term476.
Proof. exact (SYM (@lem7242686)). Qed.
Lemma lem7242688 : term476.
Proof. exact (EQ_MP (@lem7242687) (@lem0)). Qed.
Lemma lem7242689 : term818 = term821.
Proof. exact (@lem7242678 (@lem7242688)). Qed.
Lemma lem7242691 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7242692 : term439 = term444.
Proof. exact (@lem7242691 term189 term189). Qed.
Lemma lem7242693 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242694 : term405 = term189.
Proof. exact (EQ_MP (@lem7242693) (@lem940073)). Qed.
Lemma lem7242695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242696 : term403 = term340.
Proof. exact (MK_COMB (@lem7242695) (@lem7242694)). Qed.
Lemma lem7242697 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7242698 : term444 = term393.
Proof. exact (MK_COMB (@lem7242697) (@lem7242696)). Qed.
Lemma lem7242699 : term439 = term393.
Proof. exact (TRANS (@lem7242692) (@lem7242698)). Qed.
Lemma lem7242701 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242702 : term488 = term328.
Proof. exact (@lem7242701 term189). Qed.
Lemma lem7242703 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7242704 : term822 = term330.
Proof. exact (MK_COMB (@lem7242703) (@lem7242702)). Qed.
Lemma lem7242705 : term821 = term816.
Proof. exact (MK_COMB (@lem7242704) (@lem7242699)). Qed.
Lemma lem7242707 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7242708 : term816 = term825.
Proof. exact (@lem7242707 (NUMERAL 0) term189). Qed.
Lemma lem7242709 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242710 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7242711 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242710 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7242709)). Qed.
Lemma lem7242712 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7242711) (@lem7242709)). Qed.
Lemma lem7242713 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7242714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7242715 : term826 = (and True).
Proof. exact (MK_COMB (@lem7242714) (@lem7242713)). Qed.
Lemma lem7242716 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7242715) (@lem7242712)). Qed.
Lemma lem7242718 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7242719 : term825 = False.
Proof. exact (TRANS (@lem7242716) (@lem7242718)). Qed.
Lemma lem7242720 : term816 = False.
Proof. exact (TRANS (@lem7242708) (@lem7242719)). Qed.
Lemma lem7242721 : term821 = False.
Proof. exact (TRANS (@lem7242705) (@lem7242720)). Qed.
Lemma lem7242722 : term818 = False.
Proof. exact (TRANS (@lem7242689) (@lem7242721)). Qed.
Lemma lem7242723 : term816 = False.
Proof. exact (TRANS (@lem7242666) (@lem7242722)). Qed.
Lemma lem7242724 : term815 = False.
Proof. exact (TRANS (@lem7242657) (@lem7242723)). Qed.
Lemma lem7242725 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term849 _96884 _96885 _96883 _96886) : False.
Proof. exact (EQ_MP (@lem7242724) (@lem7242654 _96884 _96885 _96883 _96886 h1)). Qed.
Lemma lem7242726 (_96884 : int) (_96885 : int) (_96883 : int) (_96886 : int) (h1 : term739 _96884 _96885 _96883 _96886) : False.
Proof. exact (or_elim (@lem7241400 _96884 _96885 _96883 _96886 h1) (fun h0 : term848 _96885 _96884 _96883 _96886 => @lem7241873 _96885 _96884 _96883 _96886 h0) (fun h0 : term849 _96884 _96885 _96883 _96886 => @lem7242725 _96884 _96885 _96883 _96886 h0)). Qed.
Lemma lem7242727 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term735 _96883 _96884 _96885 _96886) : term735 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7242728 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term870 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7242729 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term736 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7242728 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242731 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term700 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7242729 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242733 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term664 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7242731 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242735 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term628 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7242733 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242737 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term592 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7242735 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242739 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term556 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7242737 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242740 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term428 _96884 _96885.
Proof. exact (proj1 (@lem7242737 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242741 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term453 _96885 _96886.
Proof. exact (proj2 (@lem7242739 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242742 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term432 _96883 _96884 _96886.
Proof. exact (proj1 (@lem7242739 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242743 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term430 _96884 _96886.
Proof. exact (proj2 (@lem7242742 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242746 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7242747 : term764 = term476.
Proof. exact (@lem7242746 term328 term340). Qed.
Lemma lem7242749 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242750 : term340 = term438.
Proof. exact (@lem7242749 term189). Qed.
Lemma lem7242752 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242753 : term328 = term390.
Proof. exact (@lem7242752 (NUMERAL 0)). Qed.
Lemma lem7242754 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242755 : term765 = term766.
Proof. exact (MK_COMB (@lem7242754) (@lem7242753)). Qed.
Lemma lem7242756 : term476 = term767.
Proof. exact (MK_COMB (@lem7242755) (@lem7242750)). Qed.
Lemma lem7242757 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7242759 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242760 : term476 = term477.
Proof. exact (@lem7242759 (NUMERAL 0) term189). Qed.
Lemma lem7242761 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242762 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242763 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242762 h1) (fun h1 : term477 = True => @lem7242761)). Qed.
Lemma lem7242764 : term477 = True.
Proof. exact (EQ_MP (@lem7242763) (@lem7242761)). Qed.
Lemma lem7242765 : term476 = True.
Proof. exact (TRANS (@lem7242760) (@lem7242764)). Qed.
Lemma lem7242766 : True = term476.
Proof. exact (SYM (@lem7242765)). Qed.
Lemma lem7242767 : term476.
Proof. exact (EQ_MP (@lem7242766) (@lem0)). Qed.
Lemma lem7242768 : term769.
Proof. exact (@lem7242757 (@lem7242767)). Qed.
Lemma lem7242770 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242771 : term476 = term477.
Proof. exact (@lem7242770 (NUMERAL 0) term189). Qed.
Lemma lem7242772 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242773 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242774 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242773 h1) (fun h1 : term477 = True => @lem7242772)). Qed.
Lemma lem7242775 : term477 = True.
Proof. exact (EQ_MP (@lem7242774) (@lem7242772)). Qed.
Lemma lem7242776 : term476 = True.
Proof. exact (TRANS (@lem7242771) (@lem7242775)). Qed.
Lemma lem7242777 : True = term476.
Proof. exact (SYM (@lem7242776)). Qed.
Lemma lem7242778 : term476.
Proof. exact (EQ_MP (@lem7242777) (@lem0)). Qed.
Lemma lem7242779 : term767 = term770.
Proof. exact (@lem7242768 (@lem7242778)). Qed.
Lemma lem7242781 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242782 : term402 = term403.
Proof. exact (@lem7242781 term189 term189). Qed.
Lemma lem7242783 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242784 : term405 = term189.
Proof. exact (EQ_MP (@lem7242783) (@lem940073)). Qed.
Lemma lem7242785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242786 : term403 = term340.
Proof. exact (MK_COMB (@lem7242785) (@lem7242784)). Qed.
Lemma lem7242787 : term402 = term340.
Proof. exact (TRANS (@lem7242782) (@lem7242786)). Qed.
Lemma lem7242789 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242790 : term488 = term328.
Proof. exact (@lem7242789 term189). Qed.
Lemma lem7242791 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242792 : term771 = term765.
Proof. exact (MK_COMB (@lem7242791) (@lem7242790)). Qed.
Lemma lem7242793 : term770 = term476.
Proof. exact (MK_COMB (@lem7242792) (@lem7242787)). Qed.
Lemma lem7242795 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242796 : term476 = term477.
Proof. exact (@lem7242795 (NUMERAL 0) term189). Qed.
Lemma lem7242797 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242798 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242799 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242798 h1) (fun h1 : term477 = True => @lem7242797)). Qed.
Lemma lem7242800 : term477 = True.
Proof. exact (EQ_MP (@lem7242799) (@lem7242797)). Qed.
Lemma lem7242801 : term476 = True.
Proof. exact (TRANS (@lem7242796) (@lem7242800)). Qed.
Lemma lem7242802 : term770 = True.
Proof. exact (TRANS (@lem7242793) (@lem7242801)). Qed.
Lemma lem7242803 : term767 = True.
Proof. exact (TRANS (@lem7242779) (@lem7242802)). Qed.
Lemma lem7242804 : term476 = True.
Proof. exact (TRANS (@lem7242756) (@lem7242803)). Qed.
Lemma lem7242805 : term764 = True.
Proof. exact (TRANS (@lem7242747) (@lem7242804)). Qed.
Lemma lem7242806 : True = term764.
Proof. exact (SYM (@lem7242805)). Qed.
Lemma lem7242807 : term764.
Proof. exact (EQ_MP (@lem7242806) (@lem0)). Qed.
Lemma lem7242808 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term772 _96884 _96886.
Proof. exact (conj (@lem7242807) (@lem7242743 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242810 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7242811 (_96884 : int) (_96886 : int) : term774 _96884 _96886.
Proof. exact (@lem7242810 term340 (term424 _96884 _96886)). Qed.
Lemma lem7242812 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term775 _96884 _96886.
Proof. exact (@lem7242811 _96884 _96886 (@lem7242808 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242813 (_96884 : int) (_96886 : int) : (term776 _96884 _96886) = (term424 _96884 _96886).
Proof. exact (@lem1982733 (term424 _96884 _96886)). Qed.
Lemma lem7242814 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242815 (_96884 : int) (_96886 : int) : (term777 _96884 _96886) = (term429 _96884 _96886).
Proof. exact (MK_COMB (@lem7242814) (@lem7242813 _96884 _96886)). Qed.
Lemma lem7242816 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242817 (_96884 : int) (_96886 : int) : (term775 _96884 _96886) = (term430 _96884 _96886).
Proof. exact (MK_COMB (@lem7242815 _96884 _96886) (@lem7242816)). Qed.
Lemma lem7242818 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term430 _96884 _96886.
Proof. exact (EQ_MP (@lem7242817 _96884 _96886) (@lem7242812 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242820 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7242821 : term764 = term476.
Proof. exact (@lem7242820 term328 term340). Qed.
Lemma lem7242823 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242824 : term340 = term438.
Proof. exact (@lem7242823 term189). Qed.
Lemma lem7242826 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242827 : term328 = term390.
Proof. exact (@lem7242826 (NUMERAL 0)). Qed.
Lemma lem7242828 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242829 : term765 = term766.
Proof. exact (MK_COMB (@lem7242828) (@lem7242827)). Qed.
Lemma lem7242830 : term476 = term767.
Proof. exact (MK_COMB (@lem7242829) (@lem7242824)). Qed.
Lemma lem7242831 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7242833 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242834 : term476 = term477.
Proof. exact (@lem7242833 (NUMERAL 0) term189). Qed.
Lemma lem7242835 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242836 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242837 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242836 h1) (fun h1 : term477 = True => @lem7242835)). Qed.
Lemma lem7242838 : term477 = True.
Proof. exact (EQ_MP (@lem7242837) (@lem7242835)). Qed.
Lemma lem7242839 : term476 = True.
Proof. exact (TRANS (@lem7242834) (@lem7242838)). Qed.
Lemma lem7242840 : True = term476.
Proof. exact (SYM (@lem7242839)). Qed.
Lemma lem7242841 : term476.
Proof. exact (EQ_MP (@lem7242840) (@lem0)). Qed.
Lemma lem7242842 : term769.
Proof. exact (@lem7242831 (@lem7242841)). Qed.
Lemma lem7242844 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242845 : term476 = term477.
Proof. exact (@lem7242844 (NUMERAL 0) term189). Qed.
Lemma lem7242846 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242847 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242848 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242847 h1) (fun h1 : term477 = True => @lem7242846)). Qed.
Lemma lem7242849 : term477 = True.
Proof. exact (EQ_MP (@lem7242848) (@lem7242846)). Qed.
Lemma lem7242850 : term476 = True.
Proof. exact (TRANS (@lem7242845) (@lem7242849)). Qed.
Lemma lem7242851 : True = term476.
Proof. exact (SYM (@lem7242850)). Qed.
Lemma lem7242852 : term476.
Proof. exact (EQ_MP (@lem7242851) (@lem0)). Qed.
Lemma lem7242853 : term767 = term770.
Proof. exact (@lem7242842 (@lem7242852)). Qed.
Lemma lem7242855 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242856 : term402 = term403.
Proof. exact (@lem7242855 term189 term189). Qed.
Lemma lem7242857 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242858 : term405 = term189.
Proof. exact (EQ_MP (@lem7242857) (@lem940073)). Qed.
Lemma lem7242859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242860 : term403 = term340.
Proof. exact (MK_COMB (@lem7242859) (@lem7242858)). Qed.
Lemma lem7242861 : term402 = term340.
Proof. exact (TRANS (@lem7242856) (@lem7242860)). Qed.
Lemma lem7242863 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242864 : term488 = term328.
Proof. exact (@lem7242863 term189). Qed.
Lemma lem7242865 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242866 : term771 = term765.
Proof. exact (MK_COMB (@lem7242865) (@lem7242864)). Qed.
Lemma lem7242867 : term770 = term476.
Proof. exact (MK_COMB (@lem7242866) (@lem7242861)). Qed.
Lemma lem7242869 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242870 : term476 = term477.
Proof. exact (@lem7242869 (NUMERAL 0) term189). Qed.
Lemma lem7242871 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242872 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242873 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242872 h1) (fun h1 : term477 = True => @lem7242871)). Qed.
Lemma lem7242874 : term477 = True.
Proof. exact (EQ_MP (@lem7242873) (@lem7242871)). Qed.
Lemma lem7242875 : term476 = True.
Proof. exact (TRANS (@lem7242870) (@lem7242874)). Qed.
Lemma lem7242876 : term770 = True.
Proof. exact (TRANS (@lem7242867) (@lem7242875)). Qed.
Lemma lem7242877 : term767 = True.
Proof. exact (TRANS (@lem7242853) (@lem7242876)). Qed.
Lemma lem7242878 : term476 = True.
Proof. exact (TRANS (@lem7242830) (@lem7242877)). Qed.
Lemma lem7242879 : term764 = True.
Proof. exact (TRANS (@lem7242821) (@lem7242878)). Qed.
Lemma lem7242880 : True = term764.
Proof. exact (SYM (@lem7242879)). Qed.
Lemma lem7242881 : term764.
Proof. exact (EQ_MP (@lem7242880) (@lem0)). Qed.
Lemma lem7242882 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term833 _96884 _96885.
Proof. exact (conj (@lem7242881) (@lem7242740 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242884 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7242885 (_96884 : int) (_96885 : int) : term834 _96884 _96885.
Proof. exact (@lem7242884 term340 (term425 _96884 _96885)). Qed.
Lemma lem7242886 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term835 _96884 _96885.
Proof. exact (@lem7242885 _96884 _96885 (@lem7242882 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242887 (_96884 : int) (_96885 : int) : (term836 _96884 _96885) = (term425 _96884 _96885).
Proof. exact (@lem1982733 (term425 _96884 _96885)). Qed.
Lemma lem7242888 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242889 (_96884 : int) (_96885 : int) : (term837 _96884 _96885) = (term427 _96884 _96885).
Proof. exact (MK_COMB (@lem7242888) (@lem7242887 _96884 _96885)). Qed.
Lemma lem7242890 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242891 (_96884 : int) (_96885 : int) : (term835 _96884 _96885) = (term428 _96884 _96885).
Proof. exact (MK_COMB (@lem7242889 _96884 _96885) (@lem7242890)). Qed.
Lemma lem7242892 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term428 _96884 _96885.
Proof. exact (EQ_MP (@lem7242891 _96884 _96885) (@lem7242886 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242894 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7242895 : term764 = term476.
Proof. exact (@lem7242894 term328 term340). Qed.
Lemma lem7242897 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242898 : term340 = term438.
Proof. exact (@lem7242897 term189). Qed.
Lemma lem7242900 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242901 : term328 = term390.
Proof. exact (@lem7242900 (NUMERAL 0)). Qed.
Lemma lem7242902 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242903 : term765 = term766.
Proof. exact (MK_COMB (@lem7242902) (@lem7242901)). Qed.
Lemma lem7242904 : term476 = term767.
Proof. exact (MK_COMB (@lem7242903) (@lem7242898)). Qed.
Lemma lem7242905 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7242907 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242908 : term476 = term477.
Proof. exact (@lem7242907 (NUMERAL 0) term189). Qed.
Lemma lem7242909 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242910 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242911 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242910 h1) (fun h1 : term477 = True => @lem7242909)). Qed.
Lemma lem7242912 : term477 = True.
Proof. exact (EQ_MP (@lem7242911) (@lem7242909)). Qed.
Lemma lem7242913 : term476 = True.
Proof. exact (TRANS (@lem7242908) (@lem7242912)). Qed.
Lemma lem7242914 : True = term476.
Proof. exact (SYM (@lem7242913)). Qed.
Lemma lem7242915 : term476.
Proof. exact (EQ_MP (@lem7242914) (@lem0)). Qed.
Lemma lem7242916 : term769.
Proof. exact (@lem7242905 (@lem7242915)). Qed.
Lemma lem7242918 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242919 : term476 = term477.
Proof. exact (@lem7242918 (NUMERAL 0) term189). Qed.
Lemma lem7242920 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242921 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242922 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242921 h1) (fun h1 : term477 = True => @lem7242920)). Qed.
Lemma lem7242923 : term477 = True.
Proof. exact (EQ_MP (@lem7242922) (@lem7242920)). Qed.
Lemma lem7242924 : term476 = True.
Proof. exact (TRANS (@lem7242919) (@lem7242923)). Qed.
Lemma lem7242925 : True = term476.
Proof. exact (SYM (@lem7242924)). Qed.
Lemma lem7242926 : term476.
Proof. exact (EQ_MP (@lem7242925) (@lem0)). Qed.
Lemma lem7242927 : term767 = term770.
Proof. exact (@lem7242916 (@lem7242926)). Qed.
Lemma lem7242929 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7242930 : term402 = term403.
Proof. exact (@lem7242929 term189 term189). Qed.
Lemma lem7242931 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7242932 : term405 = term189.
Proof. exact (EQ_MP (@lem7242931) (@lem940073)). Qed.
Lemma lem7242933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7242934 : term403 = term340.
Proof. exact (MK_COMB (@lem7242933) (@lem7242932)). Qed.
Lemma lem7242935 : term402 = term340.
Proof. exact (TRANS (@lem7242930) (@lem7242934)). Qed.
Lemma lem7242937 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7242938 : term488 = term328.
Proof. exact (@lem7242937 term189). Qed.
Lemma lem7242939 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7242940 : term771 = term765.
Proof. exact (MK_COMB (@lem7242939) (@lem7242938)). Qed.
Lemma lem7242941 : term770 = term476.
Proof. exact (MK_COMB (@lem7242940) (@lem7242935)). Qed.
Lemma lem7242943 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242944 : term476 = term477.
Proof. exact (@lem7242943 (NUMERAL 0) term189). Qed.
Lemma lem7242945 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242946 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242947 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242946 h1) (fun h1 : term477 = True => @lem7242945)). Qed.
Lemma lem7242948 : term477 = True.
Proof. exact (EQ_MP (@lem7242947) (@lem7242945)). Qed.
Lemma lem7242949 : term476 = True.
Proof. exact (TRANS (@lem7242944) (@lem7242948)). Qed.
Lemma lem7242950 : term770 = True.
Proof. exact (TRANS (@lem7242941) (@lem7242949)). Qed.
Lemma lem7242951 : term767 = True.
Proof. exact (TRANS (@lem7242927) (@lem7242950)). Qed.
Lemma lem7242952 : term476 = True.
Proof. exact (TRANS (@lem7242904) (@lem7242951)). Qed.
Lemma lem7242953 : term764 = True.
Proof. exact (TRANS (@lem7242895) (@lem7242952)). Qed.
Lemma lem7242954 : True = term764.
Proof. exact (SYM (@lem7242953)). Qed.
Lemma lem7242955 : term764.
Proof. exact (EQ_MP (@lem7242954) (@lem0)). Qed.
Lemma lem7242956 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term778 _96885 _96886.
Proof. exact (conj (@lem7242955) (@lem7242741 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242958 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7242959 (_96885 : int) (_96886 : int) : term779 _96885 _96886.
Proof. exact (@lem7242958 term340 (term450 _96885 _96886)). Qed.
Lemma lem7242960 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term780 _96885 _96886.
Proof. exact (@lem7242959 _96885 _96886 (@lem7242956 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242961 (_96885 : int) (_96886 : int) : (term781 _96885 _96886) = (term450 _96885 _96886).
Proof. exact (@lem1982733 (term450 _96885 _96886)). Qed.
Lemma lem7242962 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7242963 (_96885 : int) (_96886 : int) : (term782 _96885 _96886) = (term452 _96885 _96886).
Proof. exact (MK_COMB (@lem7242962) (@lem7242961 _96885 _96886)). Qed.
Lemma lem7242964 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7242965 (_96885 : int) (_96886 : int) : (term780 _96885 _96886) = (term453 _96885 _96886).
Proof. exact (MK_COMB (@lem7242963 _96885 _96886) (@lem7242964)). Qed.
Lemma lem7242966 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term453 _96885 _96886.
Proof. exact (EQ_MP (@lem7242965 _96885 _96886) (@lem7242960 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242967 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term871 _96886 _96884 _96885.
Proof. exact (conj (@lem7242966 _96883 _96884 _96885 _96886 h1) (@lem7242892 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242969 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7242970 (_96886 : int) (_96884 : int) (_96885 : int) : term872 _96886 _96884 _96885.
Proof. exact (@lem7242969 (term450 _96885 _96886) (term425 _96884 _96885)). Qed.
Lemma lem7242971 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term873 _96886 _96884 _96885.
Proof. exact (@lem7242970 _96886 _96884 _96885 (@lem7242967 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7242972 (_96884 : int) (_96886 : int) (_96885 : int) : (term874 _96886 _96884 _96885) = (term875 _96884 _96886 _96885).
Proof. exact (@lem1982757 (term418 _96884) (term450 _96885 _96886) (real_of_int _96885)). Qed.
Lemma lem7242973 (_96885 : int) (_96886 : int) : (term876 _96886 _96885) = (term877 _96885 _96886).
Proof. exact (@lem1982759 (term418 _96885) (real_of_int _96885) (term788 _96886)). Qed.
Lemma lem7242974 (_96885 : int) : (term789 _96885) = (term790 _96885).
Proof. exact (@lem1982713 term393 (real_of_int _96885)). Qed.
Lemma lem7242976 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7242977 : term340 = term438.
Proof. exact (@lem7242976 term189). Qed.
Lemma lem7242979 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7242980 : term393 = term394.
Proof. exact (@lem7242979 term189). Qed.
Lemma lem7242981 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7242982 : term791 = term792.
Proof. exact (MK_COMB (@lem7242981) (@lem7242980)). Qed.
Lemma lem7242983 : term793 = term794.
Proof. exact (MK_COMB (@lem7242982) (@lem7242977)). Qed.
Lemma lem7242984 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7242986 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242987 : term476 = term477.
Proof. exact (@lem7242986 (NUMERAL 0) term189). Qed.
Lemma lem7242988 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7242989 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7242990 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7242989 h1) (fun h1 : term477 = True => @lem7242988)). Qed.
Lemma lem7242991 : term477 = True.
Proof. exact (EQ_MP (@lem7242990) (@lem7242988)). Qed.
Lemma lem7242992 : term476 = True.
Proof. exact (TRANS (@lem7242987) (@lem7242991)). Qed.
Lemma lem7242993 : True = term476.
Proof. exact (SYM (@lem7242992)). Qed.
Lemma lem7242994 : term476.
Proof. exact (EQ_MP (@lem7242993) (@lem0)). Qed.
Lemma lem7242995 : term796.
Proof. exact (@lem7242984 (@lem7242994)). Qed.
Lemma lem7242997 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7242998 : term476 = term477.
Proof. exact (@lem7242997 (NUMERAL 0) term189). Qed.
Lemma lem7242999 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243000 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243001 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243000 h1) (fun h1 : term477 = True => @lem7242999)). Qed.
Lemma lem7243002 : term477 = True.
Proof. exact (EQ_MP (@lem7243001) (@lem7242999)). Qed.
Lemma lem7243003 : term476 = True.
Proof. exact (TRANS (@lem7242998) (@lem7243002)). Qed.
Lemma lem7243004 : True = term476.
Proof. exact (SYM (@lem7243003)). Qed.
Lemma lem7243005 : term476.
Proof. exact (EQ_MP (@lem7243004) (@lem0)). Qed.
Lemma lem7243006 : term797.
Proof. exact (@lem7242995 (@lem7243005)). Qed.
Lemma lem7243008 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243009 : term476 = term477.
Proof. exact (@lem7243008 (NUMERAL 0) term189). Qed.
Lemma lem7243010 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243011 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243012 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243011 h1) (fun h1 : term477 = True => @lem7243010)). Qed.
Lemma lem7243013 : term477 = True.
Proof. exact (EQ_MP (@lem7243012) (@lem7243010)). Qed.
Lemma lem7243014 : term476 = True.
Proof. exact (TRANS (@lem7243009) (@lem7243013)). Qed.
Lemma lem7243015 : True = term476.
Proof. exact (SYM (@lem7243014)). Qed.
Lemma lem7243016 : term476.
Proof. exact (EQ_MP (@lem7243015) (@lem0)). Qed.
Lemma lem7243017 : term798.
Proof. exact (@lem7243006 (@lem7243016)). Qed.
Lemma lem7243019 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243020 : term402 = term403.
Proof. exact (@lem7243019 term189 term189). Qed.
Lemma lem7243021 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243022 : term405 = term189.
Proof. exact (EQ_MP (@lem7243021) (@lem940073)). Qed.
Lemma lem7243023 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243024 : term403 = term340.
Proof. exact (MK_COMB (@lem7243023) (@lem7243022)). Qed.
Lemma lem7243025 : term402 = term340.
Proof. exact (TRANS (@lem7243020) (@lem7243024)). Qed.
Lemma lem7243027 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243028 : term439 = term444.
Proof. exact (@lem7243027 term189 term189). Qed.
Lemma lem7243029 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243030 : term405 = term189.
Proof. exact (EQ_MP (@lem7243029) (@lem940073)). Qed.
Lemma lem7243031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243032 : term403 = term340.
Proof. exact (MK_COMB (@lem7243031) (@lem7243030)). Qed.
Lemma lem7243033 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243034 : term444 = term393.
Proof. exact (MK_COMB (@lem7243033) (@lem7243032)). Qed.
Lemma lem7243035 : term439 = term393.
Proof. exact (TRANS (@lem7243028) (@lem7243034)). Qed.
Lemma lem7243036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243037 : term799 = term791.
Proof. exact (MK_COMB (@lem7243036) (@lem7243035)). Qed.
Lemma lem7243038 : term800 = term793.
Proof. exact (MK_COMB (@lem7243037) (@lem7243025)). Qed.
Lemma lem7243040 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7243041 : term793 = term328.
Proof. exact (@lem7243040 term189). Qed.
Lemma lem7243042 : term800 = term328.
Proof. exact (TRANS (@lem7243038) (@lem7243041)). Qed.
Lemma lem7243043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243044 : term802 = term486.
Proof. exact (MK_COMB (@lem7243043) (@lem7243042)). Qed.
Lemma lem7243045 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7243046 : term803 = term488.
Proof. exact (MK_COMB (@lem7243044) (@lem7243045)). Qed.
Lemma lem7243048 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243049 : term488 = term328.
Proof. exact (@lem7243048 term189). Qed.
Lemma lem7243050 : term803 = term328.
Proof. exact (TRANS (@lem7243046) (@lem7243049)). Qed.
Lemma lem7243052 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243053 : term402 = term403.
Proof. exact (@lem7243052 term189 term189). Qed.
Lemma lem7243054 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243055 : term405 = term189.
Proof. exact (EQ_MP (@lem7243054) (@lem940073)). Qed.
Lemma lem7243056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243057 : term403 = term340.
Proof. exact (MK_COMB (@lem7243056) (@lem7243055)). Qed.
Lemma lem7243058 : term402 = term340.
Proof. exact (TRANS (@lem7243053) (@lem7243057)). Qed.
Lemma lem7243059 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7243060 : term490 = term488.
Proof. exact (MK_COMB (@lem7243059) (@lem7243058)). Qed.
Lemma lem7243062 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243063 : term488 = term328.
Proof. exact (@lem7243062 term189). Qed.
Lemma lem7243064 : term490 = term328.
Proof. exact (TRANS (@lem7243060) (@lem7243063)). Qed.
Lemma lem7243065 : term328 = term490.
Proof. exact (SYM (@lem7243064)). Qed.
Lemma lem7243066 : term803 = term490.
Proof. exact (TRANS (@lem7243050) (@lem7243065)). Qed.
Lemma lem7243067 : term794 = term390.
Proof. exact (@lem7243017 (@lem7243066)). Qed.
Lemma lem7243068 : term793 = term390.
Proof. exact (TRANS (@lem7242983) (@lem7243067)). Qed.
Lemma lem7243070 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7243071 : term390 = term328.
Proof. exact (@lem7243070 term328). Qed.
Lemma lem7243072 : term793 = term328.
Proof. exact (TRANS (@lem7243068) (@lem7243071)). Qed.
Lemma lem7243073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243074 : term804 = term486.
Proof. exact (MK_COMB (@lem7243073) (@lem7243072)). Qed.
Lemma lem7243075 (_96885 : int) : (real_of_int _96885) = (real_of_int _96885).
Proof. exact (eq_refl (real_of_int _96885)). Qed.
Lemma lem7243076 (_96885 : int) : (term790 _96885) = (term805 _96885).
Proof. exact (MK_COMB (@lem7243074) (@lem7243075 _96885)). Qed.
Lemma lem7243077 (_96885 : int) : (term789 _96885) = (term805 _96885).
Proof. exact (TRANS (@lem7242974 _96885) (@lem7243076 _96885)). Qed.
Lemma lem7243078 (_96885 : int) : (term805 _96885) = term328.
Proof. exact (@lem1982719 (real_of_int _96885)). Qed.
Lemma lem7243079 (_96885 : int) : (term789 _96885) = term328.
Proof. exact (TRANS (@lem7243077 _96885) (@lem7243078 _96885)). Qed.
Lemma lem7243080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243081 (_96885 : int) : (term806 _96885) = term807.
Proof. exact (MK_COMB (@lem7243080) (@lem7243079 _96885)). Qed.
Lemma lem7243082 (_96886 : int) : (term788 _96886) = (term788 _96886).
Proof. exact (eq_refl (term788 _96886)). Qed.
Lemma lem7243083 (_96885 : int) (_96886 : int) : (term877 _96885 _96886) = (term878 _96886).
Proof. exact (MK_COMB (@lem7243081 _96885) (@lem7243082 _96886)). Qed.
Lemma lem7243084 (_96885 : int) (_96886 : int) : (term876 _96886 _96885) = (term878 _96886).
Proof. exact (TRANS (@lem7242973 _96885 _96886) (@lem7243083 _96885 _96886)). Qed.
Lemma lem7243085 (_96886 : int) : (term878 _96886) = (term788 _96886).
Proof. exact (@lem1982721 (term788 _96886)). Qed.
Lemma lem7243086 (_96885 : int) (_96886 : int) : (term876 _96886 _96885) = (term788 _96886).
Proof. exact (TRANS (@lem7243084 _96885 _96886) (@lem7243085 _96886)). Qed.
Lemma lem7243087 (_96884 : int) : (term447 _96884) = (term447 _96884).
Proof. exact (eq_refl (term447 _96884)). Qed.
Lemma lem7243088 (_96885 : int) (_96884 : int) (_96886 : int) : (term875 _96884 _96886 _96885) = (term450 _96884 _96886).
Proof. exact (MK_COMB (@lem7243087 _96884) (@lem7243086 _96885 _96886)). Qed.
Lemma lem7243089 (_96885 : int) (_96884 : int) (_96886 : int) : (term874 _96886 _96884 _96885) = (term450 _96884 _96886).
Proof. exact (TRANS (@lem7242972 _96884 _96886 _96885) (@lem7243088 _96885 _96884 _96886)). Qed.
Lemma lem7243090 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7243091 (_96885 : int) (_96884 : int) (_96886 : int) : (term879 _96886 _96884 _96885) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7243090) (@lem7243089 _96885 _96884 _96886)). Qed.
Lemma lem7243092 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7243093 (_96885 : int) (_96884 : int) (_96886 : int) : (term873 _96886 _96884 _96885) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7243091 _96885 _96884 _96886) (@lem7243092)). Qed.
Lemma lem7243094 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term453 _96884 _96886.
Proof. exact (EQ_MP (@lem7243093 _96885 _96884 _96886) (@lem7242971 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243096 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7243097 : term764 = term476.
Proof. exact (@lem7243096 term328 term340). Qed.
Lemma lem7243099 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243100 : term340 = term438.
Proof. exact (@lem7243099 term189). Qed.
Lemma lem7243102 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243103 : term328 = term390.
Proof. exact (@lem7243102 (NUMERAL 0)). Qed.
Lemma lem7243104 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7243105 : term765 = term766.
Proof. exact (MK_COMB (@lem7243104) (@lem7243103)). Qed.
Lemma lem7243106 : term476 = term767.
Proof. exact (MK_COMB (@lem7243105) (@lem7243100)). Qed.
Lemma lem7243107 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7243109 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243110 : term476 = term477.
Proof. exact (@lem7243109 (NUMERAL 0) term189). Qed.
Lemma lem7243111 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243112 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243113 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243112 h1) (fun h1 : term477 = True => @lem7243111)). Qed.
Lemma lem7243114 : term477 = True.
Proof. exact (EQ_MP (@lem7243113) (@lem7243111)). Qed.
Lemma lem7243115 : term476 = True.
Proof. exact (TRANS (@lem7243110) (@lem7243114)). Qed.
Lemma lem7243116 : True = term476.
Proof. exact (SYM (@lem7243115)). Qed.
Lemma lem7243117 : term476.
Proof. exact (EQ_MP (@lem7243116) (@lem0)). Qed.
Lemma lem7243118 : term769.
Proof. exact (@lem7243107 (@lem7243117)). Qed.
Lemma lem7243120 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243121 : term476 = term477.
Proof. exact (@lem7243120 (NUMERAL 0) term189). Qed.
Lemma lem7243122 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243123 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243124 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243123 h1) (fun h1 : term477 = True => @lem7243122)). Qed.
Lemma lem7243125 : term477 = True.
Proof. exact (EQ_MP (@lem7243124) (@lem7243122)). Qed.
Lemma lem7243126 : term476 = True.
Proof. exact (TRANS (@lem7243121) (@lem7243125)). Qed.
Lemma lem7243127 : True = term476.
Proof. exact (SYM (@lem7243126)). Qed.
Lemma lem7243128 : term476.
Proof. exact (EQ_MP (@lem7243127) (@lem0)). Qed.
Lemma lem7243129 : term767 = term770.
Proof. exact (@lem7243118 (@lem7243128)). Qed.
Lemma lem7243131 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243132 : term402 = term403.
Proof. exact (@lem7243131 term189 term189). Qed.
Lemma lem7243133 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243134 : term405 = term189.
Proof. exact (EQ_MP (@lem7243133) (@lem940073)). Qed.
Lemma lem7243135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243136 : term403 = term340.
Proof. exact (MK_COMB (@lem7243135) (@lem7243134)). Qed.
Lemma lem7243137 : term402 = term340.
Proof. exact (TRANS (@lem7243132) (@lem7243136)). Qed.
Lemma lem7243139 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243140 : term488 = term328.
Proof. exact (@lem7243139 term189). Qed.
Lemma lem7243141 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7243142 : term771 = term765.
Proof. exact (MK_COMB (@lem7243141) (@lem7243140)). Qed.
Lemma lem7243143 : term770 = term476.
Proof. exact (MK_COMB (@lem7243142) (@lem7243137)). Qed.
Lemma lem7243145 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243146 : term476 = term477.
Proof. exact (@lem7243145 (NUMERAL 0) term189). Qed.
Lemma lem7243147 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243148 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243149 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243148 h1) (fun h1 : term477 = True => @lem7243147)). Qed.
Lemma lem7243150 : term477 = True.
Proof. exact (EQ_MP (@lem7243149) (@lem7243147)). Qed.
Lemma lem7243151 : term476 = True.
Proof. exact (TRANS (@lem7243146) (@lem7243150)). Qed.
Lemma lem7243152 : term770 = True.
Proof. exact (TRANS (@lem7243143) (@lem7243151)). Qed.
Lemma lem7243153 : term767 = True.
Proof. exact (TRANS (@lem7243129) (@lem7243152)). Qed.
Lemma lem7243154 : term476 = True.
Proof. exact (TRANS (@lem7243106) (@lem7243153)). Qed.
Lemma lem7243155 : term764 = True.
Proof. exact (TRANS (@lem7243097) (@lem7243154)). Qed.
Lemma lem7243156 : True = term764.
Proof. exact (SYM (@lem7243155)). Qed.
Lemma lem7243157 : term764.
Proof. exact (EQ_MP (@lem7243156) (@lem0)). Qed.
Lemma lem7243158 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term778 _96884 _96886.
Proof. exact (conj (@lem7243157) (@lem7243094 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243160 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7243161 (_96884 : int) (_96886 : int) : term779 _96884 _96886.
Proof. exact (@lem7243160 term340 (term450 _96884 _96886)). Qed.
Lemma lem7243162 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term780 _96884 _96886.
Proof. exact (@lem7243161 _96884 _96886 (@lem7243158 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243163 (_96884 : int) (_96886 : int) : (term781 _96884 _96886) = (term450 _96884 _96886).
Proof. exact (@lem1982733 (term450 _96884 _96886)). Qed.
Lemma lem7243164 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7243165 (_96884 : int) (_96886 : int) : (term782 _96884 _96886) = (term452 _96884 _96886).
Proof. exact (MK_COMB (@lem7243164) (@lem7243163 _96884 _96886)). Qed.
Lemma lem7243166 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7243167 (_96884 : int) (_96886 : int) : (term780 _96884 _96886) = (term453 _96884 _96886).
Proof. exact (MK_COMB (@lem7243165 _96884 _96886) (@lem7243166)). Qed.
Lemma lem7243168 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term453 _96884 _96886.
Proof. exact (EQ_MP (@lem7243167 _96884 _96886) (@lem7243162 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243169 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term541 _96884 _96886.
Proof. exact (conj (@lem7243168 _96883 _96884 _96885 _96886 h1) (@lem7242818 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243171 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7243172 (_96884 : int) (_96886 : int) : term784 _96884 _96886.
Proof. exact (@lem7243171 (term450 _96884 _96886) (term424 _96884 _96886)). Qed.
Lemma lem7243173 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term785 _96884 _96886.
Proof. exact (@lem7243172 _96884 _96886 (@lem7243169 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243174 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = (term787 _96884 _96886).
Proof. exact (@lem1982753 (term418 _96884) (real_of_int _96884) (term788 _96886) (term418 _96886)). Qed.
Lemma lem7243175 (_96884 : int) : (term789 _96884) = (term790 _96884).
Proof. exact (@lem1982713 term393 (real_of_int _96884)). Qed.
Lemma lem7243177 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243178 : term340 = term438.
Proof. exact (@lem7243177 term189). Qed.
Lemma lem7243180 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7243181 : term393 = term394.
Proof. exact (@lem7243180 term189). Qed.
Lemma lem7243182 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243183 : term791 = term792.
Proof. exact (MK_COMB (@lem7243182) (@lem7243181)). Qed.
Lemma lem7243184 : term793 = term794.
Proof. exact (MK_COMB (@lem7243183) (@lem7243178)). Qed.
Lemma lem7243185 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7243187 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243188 : term476 = term477.
Proof. exact (@lem7243187 (NUMERAL 0) term189). Qed.
Lemma lem7243189 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243190 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243191 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243190 h1) (fun h1 : term477 = True => @lem7243189)). Qed.
Lemma lem7243192 : term477 = True.
Proof. exact (EQ_MP (@lem7243191) (@lem7243189)). Qed.
Lemma lem7243193 : term476 = True.
Proof. exact (TRANS (@lem7243188) (@lem7243192)). Qed.
Lemma lem7243194 : True = term476.
Proof. exact (SYM (@lem7243193)). Qed.
Lemma lem7243195 : term476.
Proof. exact (EQ_MP (@lem7243194) (@lem0)). Qed.
Lemma lem7243196 : term796.
Proof. exact (@lem7243185 (@lem7243195)). Qed.
Lemma lem7243198 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243199 : term476 = term477.
Proof. exact (@lem7243198 (NUMERAL 0) term189). Qed.
Lemma lem7243200 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243201 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243202 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243201 h1) (fun h1 : term477 = True => @lem7243200)). Qed.
Lemma lem7243203 : term477 = True.
Proof. exact (EQ_MP (@lem7243202) (@lem7243200)). Qed.
Lemma lem7243204 : term476 = True.
Proof. exact (TRANS (@lem7243199) (@lem7243203)). Qed.
Lemma lem7243205 : True = term476.
Proof. exact (SYM (@lem7243204)). Qed.
Lemma lem7243206 : term476.
Proof. exact (EQ_MP (@lem7243205) (@lem0)). Qed.
Lemma lem7243207 : term797.
Proof. exact (@lem7243196 (@lem7243206)). Qed.
Lemma lem7243209 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243210 : term476 = term477.
Proof. exact (@lem7243209 (NUMERAL 0) term189). Qed.
Lemma lem7243211 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243212 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243213 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243212 h1) (fun h1 : term477 = True => @lem7243211)). Qed.
Lemma lem7243214 : term477 = True.
Proof. exact (EQ_MP (@lem7243213) (@lem7243211)). Qed.
Lemma lem7243215 : term476 = True.
Proof. exact (TRANS (@lem7243210) (@lem7243214)). Qed.
Lemma lem7243216 : True = term476.
Proof. exact (SYM (@lem7243215)). Qed.
Lemma lem7243217 : term476.
Proof. exact (EQ_MP (@lem7243216) (@lem0)). Qed.
Lemma lem7243218 : term798.
Proof. exact (@lem7243207 (@lem7243217)). Qed.
Lemma lem7243220 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243221 : term402 = term403.
Proof. exact (@lem7243220 term189 term189). Qed.
Lemma lem7243222 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243223 : term405 = term189.
Proof. exact (EQ_MP (@lem7243222) (@lem940073)). Qed.
Lemma lem7243224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243225 : term403 = term340.
Proof. exact (MK_COMB (@lem7243224) (@lem7243223)). Qed.
Lemma lem7243226 : term402 = term340.
Proof. exact (TRANS (@lem7243221) (@lem7243225)). Qed.
Lemma lem7243228 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243229 : term439 = term444.
Proof. exact (@lem7243228 term189 term189). Qed.
Lemma lem7243230 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243231 : term405 = term189.
Proof. exact (EQ_MP (@lem7243230) (@lem940073)). Qed.
Lemma lem7243232 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243233 : term403 = term340.
Proof. exact (MK_COMB (@lem7243232) (@lem7243231)). Qed.
Lemma lem7243234 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243235 : term444 = term393.
Proof. exact (MK_COMB (@lem7243234) (@lem7243233)). Qed.
Lemma lem7243236 : term439 = term393.
Proof. exact (TRANS (@lem7243229) (@lem7243235)). Qed.
Lemma lem7243237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243238 : term799 = term791.
Proof. exact (MK_COMB (@lem7243237) (@lem7243236)). Qed.
Lemma lem7243239 : term800 = term793.
Proof. exact (MK_COMB (@lem7243238) (@lem7243226)). Qed.
Lemma lem7243241 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7243242 : term793 = term328.
Proof. exact (@lem7243241 term189). Qed.
Lemma lem7243243 : term800 = term328.
Proof. exact (TRANS (@lem7243239) (@lem7243242)). Qed.
Lemma lem7243244 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243245 : term802 = term486.
Proof. exact (MK_COMB (@lem7243244) (@lem7243243)). Qed.
Lemma lem7243246 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7243247 : term803 = term488.
Proof. exact (MK_COMB (@lem7243245) (@lem7243246)). Qed.
Lemma lem7243249 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243250 : term488 = term328.
Proof. exact (@lem7243249 term189). Qed.
Lemma lem7243251 : term803 = term328.
Proof. exact (TRANS (@lem7243247) (@lem7243250)). Qed.
Lemma lem7243253 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243254 : term402 = term403.
Proof. exact (@lem7243253 term189 term189). Qed.
Lemma lem7243255 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243256 : term405 = term189.
Proof. exact (EQ_MP (@lem7243255) (@lem940073)). Qed.
Lemma lem7243257 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243258 : term403 = term340.
Proof. exact (MK_COMB (@lem7243257) (@lem7243256)). Qed.
Lemma lem7243259 : term402 = term340.
Proof. exact (TRANS (@lem7243254) (@lem7243258)). Qed.
Lemma lem7243260 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7243261 : term490 = term488.
Proof. exact (MK_COMB (@lem7243260) (@lem7243259)). Qed.
Lemma lem7243263 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243264 : term488 = term328.
Proof. exact (@lem7243263 term189). Qed.
Lemma lem7243265 : term490 = term328.
Proof. exact (TRANS (@lem7243261) (@lem7243264)). Qed.
Lemma lem7243266 : term328 = term490.
Proof. exact (SYM (@lem7243265)). Qed.
Lemma lem7243267 : term803 = term490.
Proof. exact (TRANS (@lem7243251) (@lem7243266)). Qed.
Lemma lem7243268 : term794 = term390.
Proof. exact (@lem7243218 (@lem7243267)). Qed.
Lemma lem7243269 : term793 = term390.
Proof. exact (TRANS (@lem7243184) (@lem7243268)). Qed.
Lemma lem7243271 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7243272 : term390 = term328.
Proof. exact (@lem7243271 term328). Qed.
Lemma lem7243273 : term793 = term328.
Proof. exact (TRANS (@lem7243269) (@lem7243272)). Qed.
Lemma lem7243274 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243275 : term804 = term486.
Proof. exact (MK_COMB (@lem7243274) (@lem7243273)). Qed.
Lemma lem7243276 (_96884 : int) : (real_of_int _96884) = (real_of_int _96884).
Proof. exact (eq_refl (real_of_int _96884)). Qed.
Lemma lem7243277 (_96884 : int) : (term790 _96884) = (term805 _96884).
Proof. exact (MK_COMB (@lem7243275) (@lem7243276 _96884)). Qed.
Lemma lem7243278 (_96884 : int) : (term789 _96884) = (term805 _96884).
Proof. exact (TRANS (@lem7243175 _96884) (@lem7243277 _96884)). Qed.
Lemma lem7243279 (_96884 : int) : (term805 _96884) = term328.
Proof. exact (@lem1982719 (real_of_int _96884)). Qed.
Lemma lem7243280 (_96884 : int) : (term789 _96884) = term328.
Proof. exact (TRANS (@lem7243278 _96884) (@lem7243279 _96884)). Qed.
Lemma lem7243281 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243282 (_96884 : int) : (term806 _96884) = term807.
Proof. exact (MK_COMB (@lem7243281) (@lem7243280 _96884)). Qed.
Lemma lem7243283 (_96886 : int) : (term808 _96886) = (term809 _96886).
Proof. exact (@lem1982759 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7243284 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7243286 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243287 : term340 = term438.
Proof. exact (@lem7243286 term189). Qed.
Lemma lem7243289 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7243290 : term393 = term394.
Proof. exact (@lem7243289 term189). Qed.
Lemma lem7243291 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243292 : term791 = term792.
Proof. exact (MK_COMB (@lem7243291) (@lem7243290)). Qed.
Lemma lem7243293 : term793 = term794.
Proof. exact (MK_COMB (@lem7243292) (@lem7243287)). Qed.
Lemma lem7243294 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7243296 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243297 : term476 = term477.
Proof. exact (@lem7243296 (NUMERAL 0) term189). Qed.
Lemma lem7243298 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243299 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243300 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243299 h1) (fun h1 : term477 = True => @lem7243298)). Qed.
Lemma lem7243301 : term477 = True.
Proof. exact (EQ_MP (@lem7243300) (@lem7243298)). Qed.
Lemma lem7243302 : term476 = True.
Proof. exact (TRANS (@lem7243297) (@lem7243301)). Qed.
Lemma lem7243303 : True = term476.
Proof. exact (SYM (@lem7243302)). Qed.
Lemma lem7243304 : term476.
Proof. exact (EQ_MP (@lem7243303) (@lem0)). Qed.
Lemma lem7243305 : term796.
Proof. exact (@lem7243294 (@lem7243304)). Qed.
Lemma lem7243307 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243308 : term476 = term477.
Proof. exact (@lem7243307 (NUMERAL 0) term189). Qed.
Lemma lem7243309 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243310 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243311 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243310 h1) (fun h1 : term477 = True => @lem7243309)). Qed.
Lemma lem7243312 : term477 = True.
Proof. exact (EQ_MP (@lem7243311) (@lem7243309)). Qed.
Lemma lem7243313 : term476 = True.
Proof. exact (TRANS (@lem7243308) (@lem7243312)). Qed.
Lemma lem7243314 : True = term476.
Proof. exact (SYM (@lem7243313)). Qed.
Lemma lem7243315 : term476.
Proof. exact (EQ_MP (@lem7243314) (@lem0)). Qed.
Lemma lem7243316 : term797.
Proof. exact (@lem7243305 (@lem7243315)). Qed.
Lemma lem7243318 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243319 : term476 = term477.
Proof. exact (@lem7243318 (NUMERAL 0) term189). Qed.
Lemma lem7243320 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243321 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243322 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243321 h1) (fun h1 : term477 = True => @lem7243320)). Qed.
Lemma lem7243323 : term477 = True.
Proof. exact (EQ_MP (@lem7243322) (@lem7243320)). Qed.
Lemma lem7243324 : term476 = True.
Proof. exact (TRANS (@lem7243319) (@lem7243323)). Qed.
Lemma lem7243325 : True = term476.
Proof. exact (SYM (@lem7243324)). Qed.
Lemma lem7243326 : term476.
Proof. exact (EQ_MP (@lem7243325) (@lem0)). Qed.
Lemma lem7243327 : term798.
Proof. exact (@lem7243316 (@lem7243326)). Qed.
Lemma lem7243329 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243330 : term402 = term403.
Proof. exact (@lem7243329 term189 term189). Qed.
Lemma lem7243331 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243332 : term405 = term189.
Proof. exact (EQ_MP (@lem7243331) (@lem940073)). Qed.
Lemma lem7243333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243334 : term403 = term340.
Proof. exact (MK_COMB (@lem7243333) (@lem7243332)). Qed.
Lemma lem7243335 : term402 = term340.
Proof. exact (TRANS (@lem7243330) (@lem7243334)). Qed.
Lemma lem7243337 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243338 : term439 = term444.
Proof. exact (@lem7243337 term189 term189). Qed.
Lemma lem7243339 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243340 : term405 = term189.
Proof. exact (EQ_MP (@lem7243339) (@lem940073)). Qed.
Lemma lem7243341 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243342 : term403 = term340.
Proof. exact (MK_COMB (@lem7243341) (@lem7243340)). Qed.
Lemma lem7243343 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243344 : term444 = term393.
Proof. exact (MK_COMB (@lem7243343) (@lem7243342)). Qed.
Lemma lem7243345 : term439 = term393.
Proof. exact (TRANS (@lem7243338) (@lem7243344)). Qed.
Lemma lem7243346 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243347 : term799 = term791.
Proof. exact (MK_COMB (@lem7243346) (@lem7243345)). Qed.
Lemma lem7243348 : term800 = term793.
Proof. exact (MK_COMB (@lem7243347) (@lem7243335)). Qed.
Lemma lem7243350 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7243351 : term793 = term328.
Proof. exact (@lem7243350 term189). Qed.
Lemma lem7243352 : term800 = term328.
Proof. exact (TRANS (@lem7243348) (@lem7243351)). Qed.
Lemma lem7243353 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243354 : term802 = term486.
Proof. exact (MK_COMB (@lem7243353) (@lem7243352)). Qed.
Lemma lem7243355 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7243356 : term803 = term488.
Proof. exact (MK_COMB (@lem7243354) (@lem7243355)). Qed.
Lemma lem7243358 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243359 : term488 = term328.
Proof. exact (@lem7243358 term189). Qed.
Lemma lem7243360 : term803 = term328.
Proof. exact (TRANS (@lem7243356) (@lem7243359)). Qed.
Lemma lem7243362 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243363 : term402 = term403.
Proof. exact (@lem7243362 term189 term189). Qed.
Lemma lem7243364 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243365 : term405 = term189.
Proof. exact (EQ_MP (@lem7243364) (@lem940073)). Qed.
Lemma lem7243366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243367 : term403 = term340.
Proof. exact (MK_COMB (@lem7243366) (@lem7243365)). Qed.
Lemma lem7243368 : term402 = term340.
Proof. exact (TRANS (@lem7243363) (@lem7243367)). Qed.
Lemma lem7243369 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7243370 : term490 = term488.
Proof. exact (MK_COMB (@lem7243369) (@lem7243368)). Qed.
Lemma lem7243372 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243373 : term488 = term328.
Proof. exact (@lem7243372 term189). Qed.
Lemma lem7243374 : term490 = term328.
Proof. exact (TRANS (@lem7243370) (@lem7243373)). Qed.
Lemma lem7243375 : term328 = term490.
Proof. exact (SYM (@lem7243374)). Qed.
Lemma lem7243376 : term803 = term490.
Proof. exact (TRANS (@lem7243360) (@lem7243375)). Qed.
Lemma lem7243377 : term794 = term390.
Proof. exact (@lem7243327 (@lem7243376)). Qed.
Lemma lem7243378 : term793 = term390.
Proof. exact (TRANS (@lem7243293) (@lem7243377)). Qed.
Lemma lem7243380 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7243381 : term390 = term328.
Proof. exact (@lem7243380 term328). Qed.
Lemma lem7243382 : term793 = term328.
Proof. exact (TRANS (@lem7243378) (@lem7243381)). Qed.
Lemma lem7243383 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243384 : term804 = term486.
Proof. exact (MK_COMB (@lem7243383) (@lem7243382)). Qed.
Lemma lem7243385 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7243386 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7243384) (@lem7243385 _96886)). Qed.
Lemma lem7243387 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7243284 _96886) (@lem7243386 _96886)). Qed.
Lemma lem7243388 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7243389 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7243387 _96886) (@lem7243388 _96886)). Qed.
Lemma lem7243390 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243391 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7243390) (@lem7243389 _96886)). Qed.
Lemma lem7243392 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7243393 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7243391 _96886) (@lem7243392)). Qed.
Lemma lem7243394 (_96886 : int) : (term808 _96886) = term812.
Proof. exact (TRANS (@lem7243283 _96886) (@lem7243393 _96886)). Qed.
Lemma lem7243395 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7243396 (_96886 : int) : (term808 _96886) = term393.
Proof. exact (TRANS (@lem7243394 _96886) (@lem7243395)). Qed.
Lemma lem7243397 (_96884 : int) (_96886 : int) : (term787 _96884 _96886) = term812.
Proof. exact (MK_COMB (@lem7243282 _96884) (@lem7243396 _96886)). Qed.
Lemma lem7243398 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = term812.
Proof. exact (TRANS (@lem7243174 _96884 _96886) (@lem7243397 _96884 _96886)). Qed.
Lemma lem7243399 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7243400 (_96884 : int) (_96886 : int) : (term786 _96884 _96886) = term393.
Proof. exact (TRANS (@lem7243398 _96884 _96886) (@lem7243399)). Qed.
Lemma lem7243401 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7243402 (_96884 : int) (_96886 : int) : (term813 _96884 _96886) = term814.
Proof. exact (MK_COMB (@lem7243401) (@lem7243400 _96884 _96886)). Qed.
Lemma lem7243403 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7243404 (_96884 : int) (_96886 : int) : (term785 _96884 _96886) = term815.
Proof. exact (MK_COMB (@lem7243402 _96884 _96886) (@lem7243403)). Qed.
Lemma lem7243405 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7243404 _96884 _96886) (@lem7243173 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243407 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7243408 : term815 = term816.
Proof. exact (@lem7243407 term328 term393). Qed.
Lemma lem7243410 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7243411 : term393 = term394.
Proof. exact (@lem7243410 term189). Qed.
Lemma lem7243413 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243414 : term328 = term390.
Proof. exact (@lem7243413 (NUMERAL 0)). Qed.
Lemma lem7243415 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7243416 : term330 = term817.
Proof. exact (MK_COMB (@lem7243415) (@lem7243414)). Qed.
Lemma lem7243417 : term816 = term818.
Proof. exact (MK_COMB (@lem7243416) (@lem7243411)). Qed.
Lemma lem7243418 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7243420 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243421 : term476 = term477.
Proof. exact (@lem7243420 (NUMERAL 0) term189). Qed.
Lemma lem7243422 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243423 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243424 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243423 h1) (fun h1 : term477 = True => @lem7243422)). Qed.
Lemma lem7243425 : term477 = True.
Proof. exact (EQ_MP (@lem7243424) (@lem7243422)). Qed.
Lemma lem7243426 : term476 = True.
Proof. exact (TRANS (@lem7243421) (@lem7243425)). Qed.
Lemma lem7243427 : True = term476.
Proof. exact (SYM (@lem7243426)). Qed.
Lemma lem7243428 : term476.
Proof. exact (EQ_MP (@lem7243427) (@lem0)). Qed.
Lemma lem7243429 : term820.
Proof. exact (@lem7243418 (@lem7243428)). Qed.
Lemma lem7243431 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243432 : term476 = term477.
Proof. exact (@lem7243431 (NUMERAL 0) term189). Qed.
Lemma lem7243433 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243434 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243435 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243434 h1) (fun h1 : term477 = True => @lem7243433)). Qed.
Lemma lem7243436 : term477 = True.
Proof. exact (EQ_MP (@lem7243435) (@lem7243433)). Qed.
Lemma lem7243437 : term476 = True.
Proof. exact (TRANS (@lem7243432) (@lem7243436)). Qed.
Lemma lem7243438 : True = term476.
Proof. exact (SYM (@lem7243437)). Qed.
Lemma lem7243439 : term476.
Proof. exact (EQ_MP (@lem7243438) (@lem0)). Qed.
Lemma lem7243440 : term818 = term821.
Proof. exact (@lem7243429 (@lem7243439)). Qed.
Lemma lem7243442 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243443 : term439 = term444.
Proof. exact (@lem7243442 term189 term189). Qed.
Lemma lem7243444 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243445 : term405 = term189.
Proof. exact (EQ_MP (@lem7243444) (@lem940073)). Qed.
Lemma lem7243446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243447 : term403 = term340.
Proof. exact (MK_COMB (@lem7243446) (@lem7243445)). Qed.
Lemma lem7243448 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243449 : term444 = term393.
Proof. exact (MK_COMB (@lem7243448) (@lem7243447)). Qed.
Lemma lem7243450 : term439 = term393.
Proof. exact (TRANS (@lem7243443) (@lem7243449)). Qed.
Lemma lem7243452 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243453 : term488 = term328.
Proof. exact (@lem7243452 term189). Qed.
Lemma lem7243454 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7243455 : term822 = term330.
Proof. exact (MK_COMB (@lem7243454) (@lem7243453)). Qed.
Lemma lem7243456 : term821 = term816.
Proof. exact (MK_COMB (@lem7243455) (@lem7243450)). Qed.
Lemma lem7243458 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7243459 : term816 = term825.
Proof. exact (@lem7243458 (NUMERAL 0) term189). Qed.
Lemma lem7243460 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243461 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7243462 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243461 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7243460)). Qed.
Lemma lem7243463 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7243462) (@lem7243460)). Qed.
Lemma lem7243464 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7243465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7243466 : term826 = (and True).
Proof. exact (MK_COMB (@lem7243465) (@lem7243464)). Qed.
Lemma lem7243467 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7243466) (@lem7243463)). Qed.
Lemma lem7243469 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7243470 : term825 = False.
Proof. exact (TRANS (@lem7243467) (@lem7243469)). Qed.
Lemma lem7243471 : term816 = False.
Proof. exact (TRANS (@lem7243459) (@lem7243470)). Qed.
Lemma lem7243472 : term821 = False.
Proof. exact (TRANS (@lem7243456) (@lem7243471)). Qed.
Lemma lem7243473 : term818 = False.
Proof. exact (TRANS (@lem7243440) (@lem7243472)). Qed.
Lemma lem7243474 : term816 = False.
Proof. exact (TRANS (@lem7243417) (@lem7243473)). Qed.
Lemma lem7243475 : term815 = False.
Proof. exact (TRANS (@lem7243408) (@lem7243474)). Qed.
Lemma lem7243476 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term870 _96883 _96884 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7243475) (@lem7243405 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243477 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term880 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7243478 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term737 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7243477 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243480 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term701 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7243478 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243482 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term665 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7243480 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243484 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term629 _96883 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7243482 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243486 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term593 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7243484 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243488 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term557 _96884 _96885 _96886.
Proof. exact (proj2 (@lem7243486 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243490 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term453 _96885 _96886.
Proof. exact (proj2 (@lem7243488 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243491 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term455 _96884 _96885 _96886.
Proof. exact (proj1 (@lem7243488 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243492 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term430 _96885 _96886.
Proof. exact (proj2 (@lem7243491 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243495 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7243496 : term764 = term476.
Proof. exact (@lem7243495 term328 term340). Qed.
Lemma lem7243498 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243499 : term340 = term438.
Proof. exact (@lem7243498 term189). Qed.
Lemma lem7243501 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243502 : term328 = term390.
Proof. exact (@lem7243501 (NUMERAL 0)). Qed.
Lemma lem7243503 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7243504 : term765 = term766.
Proof. exact (MK_COMB (@lem7243503) (@lem7243502)). Qed.
Lemma lem7243505 : term476 = term767.
Proof. exact (MK_COMB (@lem7243504) (@lem7243499)). Qed.
Lemma lem7243506 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7243508 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243509 : term476 = term477.
Proof. exact (@lem7243508 (NUMERAL 0) term189). Qed.
Lemma lem7243510 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243511 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243512 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243511 h1) (fun h1 : term477 = True => @lem7243510)). Qed.
Lemma lem7243513 : term477 = True.
Proof. exact (EQ_MP (@lem7243512) (@lem7243510)). Qed.
Lemma lem7243514 : term476 = True.
Proof. exact (TRANS (@lem7243509) (@lem7243513)). Qed.
Lemma lem7243515 : True = term476.
Proof. exact (SYM (@lem7243514)). Qed.
Lemma lem7243516 : term476.
Proof. exact (EQ_MP (@lem7243515) (@lem0)). Qed.
Lemma lem7243517 : term769.
Proof. exact (@lem7243506 (@lem7243516)). Qed.
Lemma lem7243519 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243520 : term476 = term477.
Proof. exact (@lem7243519 (NUMERAL 0) term189). Qed.
Lemma lem7243521 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243522 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243523 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243522 h1) (fun h1 : term477 = True => @lem7243521)). Qed.
Lemma lem7243524 : term477 = True.
Proof. exact (EQ_MP (@lem7243523) (@lem7243521)). Qed.
Lemma lem7243525 : term476 = True.
Proof. exact (TRANS (@lem7243520) (@lem7243524)). Qed.
Lemma lem7243526 : True = term476.
Proof. exact (SYM (@lem7243525)). Qed.
Lemma lem7243527 : term476.
Proof. exact (EQ_MP (@lem7243526) (@lem0)). Qed.
Lemma lem7243528 : term767 = term770.
Proof. exact (@lem7243517 (@lem7243527)). Qed.
Lemma lem7243530 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243531 : term402 = term403.
Proof. exact (@lem7243530 term189 term189). Qed.
Lemma lem7243532 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243533 : term405 = term189.
Proof. exact (EQ_MP (@lem7243532) (@lem940073)). Qed.
Lemma lem7243534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243535 : term403 = term340.
Proof. exact (MK_COMB (@lem7243534) (@lem7243533)). Qed.
Lemma lem7243536 : term402 = term340.
Proof. exact (TRANS (@lem7243531) (@lem7243535)). Qed.
Lemma lem7243538 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243539 : term488 = term328.
Proof. exact (@lem7243538 term189). Qed.
Lemma lem7243540 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7243541 : term771 = term765.
Proof. exact (MK_COMB (@lem7243540) (@lem7243539)). Qed.
Lemma lem7243542 : term770 = term476.
Proof. exact (MK_COMB (@lem7243541) (@lem7243536)). Qed.
Lemma lem7243544 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243545 : term476 = term477.
Proof. exact (@lem7243544 (NUMERAL 0) term189). Qed.
Lemma lem7243546 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243547 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243548 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243547 h1) (fun h1 : term477 = True => @lem7243546)). Qed.
Lemma lem7243549 : term477 = True.
Proof. exact (EQ_MP (@lem7243548) (@lem7243546)). Qed.
Lemma lem7243550 : term476 = True.
Proof. exact (TRANS (@lem7243545) (@lem7243549)). Qed.
Lemma lem7243551 : term770 = True.
Proof. exact (TRANS (@lem7243542) (@lem7243550)). Qed.
Lemma lem7243552 : term767 = True.
Proof. exact (TRANS (@lem7243528) (@lem7243551)). Qed.
Lemma lem7243553 : term476 = True.
Proof. exact (TRANS (@lem7243505) (@lem7243552)). Qed.
Lemma lem7243554 : term764 = True.
Proof. exact (TRANS (@lem7243496) (@lem7243553)). Qed.
Lemma lem7243555 : True = term764.
Proof. exact (SYM (@lem7243554)). Qed.
Lemma lem7243556 : term764.
Proof. exact (EQ_MP (@lem7243555) (@lem0)). Qed.
Lemma lem7243557 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term772 _96885 _96886.
Proof. exact (conj (@lem7243556) (@lem7243492 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243559 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7243560 (_96885 : int) (_96886 : int) : term774 _96885 _96886.
Proof. exact (@lem7243559 term340 (term424 _96885 _96886)). Qed.
Lemma lem7243561 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term775 _96885 _96886.
Proof. exact (@lem7243560 _96885 _96886 (@lem7243557 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243562 (_96885 : int) (_96886 : int) : (term776 _96885 _96886) = (term424 _96885 _96886).
Proof. exact (@lem1982733 (term424 _96885 _96886)). Qed.
Lemma lem7243563 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7243564 (_96885 : int) (_96886 : int) : (term777 _96885 _96886) = (term429 _96885 _96886).
Proof. exact (MK_COMB (@lem7243563) (@lem7243562 _96885 _96886)). Qed.
Lemma lem7243565 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7243566 (_96885 : int) (_96886 : int) : (term775 _96885 _96886) = (term430 _96885 _96886).
Proof. exact (MK_COMB (@lem7243564 _96885 _96886) (@lem7243565)). Qed.
Lemma lem7243567 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term430 _96885 _96886.
Proof. exact (EQ_MP (@lem7243566 _96885 _96886) (@lem7243561 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243569 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7243570 : term764 = term476.
Proof. exact (@lem7243569 term328 term340). Qed.
Lemma lem7243572 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243573 : term340 = term438.
Proof. exact (@lem7243572 term189). Qed.
Lemma lem7243575 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243576 : term328 = term390.
Proof. exact (@lem7243575 (NUMERAL 0)). Qed.
Lemma lem7243577 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7243578 : term765 = term766.
Proof. exact (MK_COMB (@lem7243577) (@lem7243576)). Qed.
Lemma lem7243579 : term476 = term767.
Proof. exact (MK_COMB (@lem7243578) (@lem7243573)). Qed.
Lemma lem7243580 : term768.
Proof. exact (@lem1980255 term328 term340 term340 term340). Qed.
Lemma lem7243582 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243583 : term476 = term477.
Proof. exact (@lem7243582 (NUMERAL 0) term189). Qed.
Lemma lem7243584 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243585 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243586 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243585 h1) (fun h1 : term477 = True => @lem7243584)). Qed.
Lemma lem7243587 : term477 = True.
Proof. exact (EQ_MP (@lem7243586) (@lem7243584)). Qed.
Lemma lem7243588 : term476 = True.
Proof. exact (TRANS (@lem7243583) (@lem7243587)). Qed.
Lemma lem7243589 : True = term476.
Proof. exact (SYM (@lem7243588)). Qed.
Lemma lem7243590 : term476.
Proof. exact (EQ_MP (@lem7243589) (@lem0)). Qed.
Lemma lem7243591 : term769.
Proof. exact (@lem7243580 (@lem7243590)). Qed.
Lemma lem7243593 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243594 : term476 = term477.
Proof. exact (@lem7243593 (NUMERAL 0) term189). Qed.
Lemma lem7243595 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243596 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243597 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243596 h1) (fun h1 : term477 = True => @lem7243595)). Qed.
Lemma lem7243598 : term477 = True.
Proof. exact (EQ_MP (@lem7243597) (@lem7243595)). Qed.
Lemma lem7243599 : term476 = True.
Proof. exact (TRANS (@lem7243594) (@lem7243598)). Qed.
Lemma lem7243600 : True = term476.
Proof. exact (SYM (@lem7243599)). Qed.
Lemma lem7243601 : term476.
Proof. exact (EQ_MP (@lem7243600) (@lem0)). Qed.
Lemma lem7243602 : term767 = term770.
Proof. exact (@lem7243591 (@lem7243601)). Qed.
Lemma lem7243604 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243605 : term402 = term403.
Proof. exact (@lem7243604 term189 term189). Qed.
Lemma lem7243606 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243607 : term405 = term189.
Proof. exact (EQ_MP (@lem7243606) (@lem940073)). Qed.
Lemma lem7243608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243609 : term403 = term340.
Proof. exact (MK_COMB (@lem7243608) (@lem7243607)). Qed.
Lemma lem7243610 : term402 = term340.
Proof. exact (TRANS (@lem7243605) (@lem7243609)). Qed.
Lemma lem7243612 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243613 : term488 = term328.
Proof. exact (@lem7243612 term189). Qed.
Lemma lem7243614 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7243615 : term771 = term765.
Proof. exact (MK_COMB (@lem7243614) (@lem7243613)). Qed.
Lemma lem7243616 : term770 = term476.
Proof. exact (MK_COMB (@lem7243615) (@lem7243610)). Qed.
Lemma lem7243618 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243619 : term476 = term477.
Proof. exact (@lem7243618 (NUMERAL 0) term189). Qed.
Lemma lem7243620 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243621 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243622 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243621 h1) (fun h1 : term477 = True => @lem7243620)). Qed.
Lemma lem7243623 : term477 = True.
Proof. exact (EQ_MP (@lem7243622) (@lem7243620)). Qed.
Lemma lem7243624 : term476 = True.
Proof. exact (TRANS (@lem7243619) (@lem7243623)). Qed.
Lemma lem7243625 : term770 = True.
Proof. exact (TRANS (@lem7243616) (@lem7243624)). Qed.
Lemma lem7243626 : term767 = True.
Proof. exact (TRANS (@lem7243602) (@lem7243625)). Qed.
Lemma lem7243627 : term476 = True.
Proof. exact (TRANS (@lem7243579) (@lem7243626)). Qed.
Lemma lem7243628 : term764 = True.
Proof. exact (TRANS (@lem7243570) (@lem7243627)). Qed.
Lemma lem7243629 : True = term764.
Proof. exact (SYM (@lem7243628)). Qed.
Lemma lem7243630 : term764.
Proof. exact (EQ_MP (@lem7243629) (@lem0)). Qed.
Lemma lem7243631 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term778 _96885 _96886.
Proof. exact (conj (@lem7243630) (@lem7243490 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243633 (x : real) (y : real) : term773 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7243634 (_96885 : int) (_96886 : int) : term779 _96885 _96886.
Proof. exact (@lem7243633 term340 (term450 _96885 _96886)). Qed.
Lemma lem7243635 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term780 _96885 _96886.
Proof. exact (@lem7243634 _96885 _96886 (@lem7243631 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243636 (_96885 : int) (_96886 : int) : (term781 _96885 _96886) = (term450 _96885 _96886).
Proof. exact (@lem1982733 (term450 _96885 _96886)). Qed.
Lemma lem7243637 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7243638 (_96885 : int) (_96886 : int) : (term782 _96885 _96886) = (term452 _96885 _96886).
Proof. exact (MK_COMB (@lem7243637) (@lem7243636 _96885 _96886)). Qed.
Lemma lem7243639 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7243640 (_96885 : int) (_96886 : int) : (term780 _96885 _96886) = (term453 _96885 _96886).
Proof. exact (MK_COMB (@lem7243638 _96885 _96886) (@lem7243639)). Qed.
Lemma lem7243641 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term453 _96885 _96886.
Proof. exact (EQ_MP (@lem7243640 _96885 _96886) (@lem7243635 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243642 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term541 _96885 _96886.
Proof. exact (conj (@lem7243641 _96883 _96884 _96885 _96886 h1) (@lem7243567 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243644 (x : real) (y : real) : term783 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7243645 (_96885 : int) (_96886 : int) : term784 _96885 _96886.
Proof. exact (@lem7243644 (term450 _96885 _96886) (term424 _96885 _96886)). Qed.
Lemma lem7243646 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term785 _96885 _96886.
Proof. exact (@lem7243645 _96885 _96886 (@lem7243642 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243647 (_96885 : int) (_96886 : int) : (term786 _96885 _96886) = (term787 _96885 _96886).
Proof. exact (@lem1982753 (term418 _96885) (real_of_int _96885) (term788 _96886) (term418 _96886)). Qed.
Lemma lem7243648 (_96885 : int) : (term789 _96885) = (term790 _96885).
Proof. exact (@lem1982713 term393 (real_of_int _96885)). Qed.
Lemma lem7243650 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243651 : term340 = term438.
Proof. exact (@lem7243650 term189). Qed.
Lemma lem7243653 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7243654 : term393 = term394.
Proof. exact (@lem7243653 term189). Qed.
Lemma lem7243655 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243656 : term791 = term792.
Proof. exact (MK_COMB (@lem7243655) (@lem7243654)). Qed.
Lemma lem7243657 : term793 = term794.
Proof. exact (MK_COMB (@lem7243656) (@lem7243651)). Qed.
Lemma lem7243658 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7243660 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243661 : term476 = term477.
Proof. exact (@lem7243660 (NUMERAL 0) term189). Qed.
Lemma lem7243662 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243663 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243664 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243663 h1) (fun h1 : term477 = True => @lem7243662)). Qed.
Lemma lem7243665 : term477 = True.
Proof. exact (EQ_MP (@lem7243664) (@lem7243662)). Qed.
Lemma lem7243666 : term476 = True.
Proof. exact (TRANS (@lem7243661) (@lem7243665)). Qed.
Lemma lem7243667 : True = term476.
Proof. exact (SYM (@lem7243666)). Qed.
Lemma lem7243668 : term476.
Proof. exact (EQ_MP (@lem7243667) (@lem0)). Qed.
Lemma lem7243669 : term796.
Proof. exact (@lem7243658 (@lem7243668)). Qed.
Lemma lem7243671 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243672 : term476 = term477.
Proof. exact (@lem7243671 (NUMERAL 0) term189). Qed.
Lemma lem7243673 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243674 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243675 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243674 h1) (fun h1 : term477 = True => @lem7243673)). Qed.
Lemma lem7243676 : term477 = True.
Proof. exact (EQ_MP (@lem7243675) (@lem7243673)). Qed.
Lemma lem7243677 : term476 = True.
Proof. exact (TRANS (@lem7243672) (@lem7243676)). Qed.
Lemma lem7243678 : True = term476.
Proof. exact (SYM (@lem7243677)). Qed.
Lemma lem7243679 : term476.
Proof. exact (EQ_MP (@lem7243678) (@lem0)). Qed.
Lemma lem7243680 : term797.
Proof. exact (@lem7243669 (@lem7243679)). Qed.
Lemma lem7243682 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243683 : term476 = term477.
Proof. exact (@lem7243682 (NUMERAL 0) term189). Qed.
Lemma lem7243684 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243685 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243686 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243685 h1) (fun h1 : term477 = True => @lem7243684)). Qed.
Lemma lem7243687 : term477 = True.
Proof. exact (EQ_MP (@lem7243686) (@lem7243684)). Qed.
Lemma lem7243688 : term476 = True.
Proof. exact (TRANS (@lem7243683) (@lem7243687)). Qed.
Lemma lem7243689 : True = term476.
Proof. exact (SYM (@lem7243688)). Qed.
Lemma lem7243690 : term476.
Proof. exact (EQ_MP (@lem7243689) (@lem0)). Qed.
Lemma lem7243691 : term798.
Proof. exact (@lem7243680 (@lem7243690)). Qed.
Lemma lem7243693 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243694 : term402 = term403.
Proof. exact (@lem7243693 term189 term189). Qed.
Lemma lem7243695 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243696 : term405 = term189.
Proof. exact (EQ_MP (@lem7243695) (@lem940073)). Qed.
Lemma lem7243697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243698 : term403 = term340.
Proof. exact (MK_COMB (@lem7243697) (@lem7243696)). Qed.
Lemma lem7243699 : term402 = term340.
Proof. exact (TRANS (@lem7243694) (@lem7243698)). Qed.
Lemma lem7243701 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243702 : term439 = term444.
Proof. exact (@lem7243701 term189 term189). Qed.
Lemma lem7243703 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243704 : term405 = term189.
Proof. exact (EQ_MP (@lem7243703) (@lem940073)). Qed.
Lemma lem7243705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243706 : term403 = term340.
Proof. exact (MK_COMB (@lem7243705) (@lem7243704)). Qed.
Lemma lem7243707 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243708 : term444 = term393.
Proof. exact (MK_COMB (@lem7243707) (@lem7243706)). Qed.
Lemma lem7243709 : term439 = term393.
Proof. exact (TRANS (@lem7243702) (@lem7243708)). Qed.
Lemma lem7243710 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243711 : term799 = term791.
Proof. exact (MK_COMB (@lem7243710) (@lem7243709)). Qed.
Lemma lem7243712 : term800 = term793.
Proof. exact (MK_COMB (@lem7243711) (@lem7243699)). Qed.
Lemma lem7243714 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7243715 : term793 = term328.
Proof. exact (@lem7243714 term189). Qed.
Lemma lem7243716 : term800 = term328.
Proof. exact (TRANS (@lem7243712) (@lem7243715)). Qed.
Lemma lem7243717 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243718 : term802 = term486.
Proof. exact (MK_COMB (@lem7243717) (@lem7243716)). Qed.
Lemma lem7243719 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7243720 : term803 = term488.
Proof. exact (MK_COMB (@lem7243718) (@lem7243719)). Qed.
Lemma lem7243722 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243723 : term488 = term328.
Proof. exact (@lem7243722 term189). Qed.
Lemma lem7243724 : term803 = term328.
Proof. exact (TRANS (@lem7243720) (@lem7243723)). Qed.
Lemma lem7243726 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243727 : term402 = term403.
Proof. exact (@lem7243726 term189 term189). Qed.
Lemma lem7243728 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243729 : term405 = term189.
Proof. exact (EQ_MP (@lem7243728) (@lem940073)). Qed.
Lemma lem7243730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243731 : term403 = term340.
Proof. exact (MK_COMB (@lem7243730) (@lem7243729)). Qed.
Lemma lem7243732 : term402 = term340.
Proof. exact (TRANS (@lem7243727) (@lem7243731)). Qed.
Lemma lem7243733 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7243734 : term490 = term488.
Proof. exact (MK_COMB (@lem7243733) (@lem7243732)). Qed.
Lemma lem7243736 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243737 : term488 = term328.
Proof. exact (@lem7243736 term189). Qed.
Lemma lem7243738 : term490 = term328.
Proof. exact (TRANS (@lem7243734) (@lem7243737)). Qed.
Lemma lem7243739 : term328 = term490.
Proof. exact (SYM (@lem7243738)). Qed.
Lemma lem7243740 : term803 = term490.
Proof. exact (TRANS (@lem7243724) (@lem7243739)). Qed.
Lemma lem7243741 : term794 = term390.
Proof. exact (@lem7243691 (@lem7243740)). Qed.
Lemma lem7243742 : term793 = term390.
Proof. exact (TRANS (@lem7243657) (@lem7243741)). Qed.
Lemma lem7243744 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7243745 : term390 = term328.
Proof. exact (@lem7243744 term328). Qed.
Lemma lem7243746 : term793 = term328.
Proof. exact (TRANS (@lem7243742) (@lem7243745)). Qed.
Lemma lem7243747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243748 : term804 = term486.
Proof. exact (MK_COMB (@lem7243747) (@lem7243746)). Qed.
Lemma lem7243749 (_96885 : int) : (real_of_int _96885) = (real_of_int _96885).
Proof. exact (eq_refl (real_of_int _96885)). Qed.
Lemma lem7243750 (_96885 : int) : (term790 _96885) = (term805 _96885).
Proof. exact (MK_COMB (@lem7243748) (@lem7243749 _96885)). Qed.
Lemma lem7243751 (_96885 : int) : (term789 _96885) = (term805 _96885).
Proof. exact (TRANS (@lem7243648 _96885) (@lem7243750 _96885)). Qed.
Lemma lem7243752 (_96885 : int) : (term805 _96885) = term328.
Proof. exact (@lem1982719 (real_of_int _96885)). Qed.
Lemma lem7243753 (_96885 : int) : (term789 _96885) = term328.
Proof. exact (TRANS (@lem7243751 _96885) (@lem7243752 _96885)). Qed.
Lemma lem7243754 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243755 (_96885 : int) : (term806 _96885) = term807.
Proof. exact (MK_COMB (@lem7243754) (@lem7243753 _96885)). Qed.
Lemma lem7243756 (_96886 : int) : (term808 _96886) = (term809 _96886).
Proof. exact (@lem1982759 (real_of_int _96886) (term418 _96886) term393). Qed.
Lemma lem7243757 (_96886 : int) : (term810 _96886) = (term790 _96886).
Proof. exact (@lem1982715 term393 (real_of_int _96886)). Qed.
Lemma lem7243759 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243760 : term340 = term438.
Proof. exact (@lem7243759 term189). Qed.
Lemma lem7243762 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7243763 : term393 = term394.
Proof. exact (@lem7243762 term189). Qed.
Lemma lem7243764 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243765 : term791 = term792.
Proof. exact (MK_COMB (@lem7243764) (@lem7243763)). Qed.
Lemma lem7243766 : term793 = term794.
Proof. exact (MK_COMB (@lem7243765) (@lem7243760)). Qed.
Lemma lem7243767 : term795.
Proof. exact (@lem1981473 term393 term340 term340 term340 term328 term340). Qed.
Lemma lem7243769 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243770 : term476 = term477.
Proof. exact (@lem7243769 (NUMERAL 0) term189). Qed.
Lemma lem7243771 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243772 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243773 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243772 h1) (fun h1 : term477 = True => @lem7243771)). Qed.
Lemma lem7243774 : term477 = True.
Proof. exact (EQ_MP (@lem7243773) (@lem7243771)). Qed.
Lemma lem7243775 : term476 = True.
Proof. exact (TRANS (@lem7243770) (@lem7243774)). Qed.
Lemma lem7243776 : True = term476.
Proof. exact (SYM (@lem7243775)). Qed.
Lemma lem7243777 : term476.
Proof. exact (EQ_MP (@lem7243776) (@lem0)). Qed.
Lemma lem7243778 : term796.
Proof. exact (@lem7243767 (@lem7243777)). Qed.
Lemma lem7243780 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243781 : term476 = term477.
Proof. exact (@lem7243780 (NUMERAL 0) term189). Qed.
Lemma lem7243782 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243783 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243784 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243783 h1) (fun h1 : term477 = True => @lem7243782)). Qed.
Lemma lem7243785 : term477 = True.
Proof. exact (EQ_MP (@lem7243784) (@lem7243782)). Qed.
Lemma lem7243786 : term476 = True.
Proof. exact (TRANS (@lem7243781) (@lem7243785)). Qed.
Lemma lem7243787 : True = term476.
Proof. exact (SYM (@lem7243786)). Qed.
Lemma lem7243788 : term476.
Proof. exact (EQ_MP (@lem7243787) (@lem0)). Qed.
Lemma lem7243789 : term797.
Proof. exact (@lem7243778 (@lem7243788)). Qed.
Lemma lem7243791 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243792 : term476 = term477.
Proof. exact (@lem7243791 (NUMERAL 0) term189). Qed.
Lemma lem7243793 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243794 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243795 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243794 h1) (fun h1 : term477 = True => @lem7243793)). Qed.
Lemma lem7243796 : term477 = True.
Proof. exact (EQ_MP (@lem7243795) (@lem7243793)). Qed.
Lemma lem7243797 : term476 = True.
Proof. exact (TRANS (@lem7243792) (@lem7243796)). Qed.
Lemma lem7243798 : True = term476.
Proof. exact (SYM (@lem7243797)). Qed.
Lemma lem7243799 : term476.
Proof. exact (EQ_MP (@lem7243798) (@lem0)). Qed.
Lemma lem7243800 : term798.
Proof. exact (@lem7243789 (@lem7243799)). Qed.
Lemma lem7243802 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243803 : term402 = term403.
Proof. exact (@lem7243802 term189 term189). Qed.
Lemma lem7243804 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243805 : term405 = term189.
Proof. exact (EQ_MP (@lem7243804) (@lem940073)). Qed.
Lemma lem7243806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243807 : term403 = term340.
Proof. exact (MK_COMB (@lem7243806) (@lem7243805)). Qed.
Lemma lem7243808 : term402 = term340.
Proof. exact (TRANS (@lem7243803) (@lem7243807)). Qed.
Lemma lem7243810 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243811 : term439 = term444.
Proof. exact (@lem7243810 term189 term189). Qed.
Lemma lem7243812 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243813 : term405 = term189.
Proof. exact (EQ_MP (@lem7243812) (@lem940073)). Qed.
Lemma lem7243814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243815 : term403 = term340.
Proof. exact (MK_COMB (@lem7243814) (@lem7243813)). Qed.
Lemma lem7243816 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243817 : term444 = term393.
Proof. exact (MK_COMB (@lem7243816) (@lem7243815)). Qed.
Lemma lem7243818 : term439 = term393.
Proof. exact (TRANS (@lem7243811) (@lem7243817)). Qed.
Lemma lem7243819 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243820 : term799 = term791.
Proof. exact (MK_COMB (@lem7243819) (@lem7243818)). Qed.
Lemma lem7243821 : term800 = term793.
Proof. exact (MK_COMB (@lem7243820) (@lem7243808)). Qed.
Lemma lem7243823 (m : nat) : (term801 m) = term328.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7243824 : term793 = term328.
Proof. exact (@lem7243823 term189). Qed.
Lemma lem7243825 : term800 = term328.
Proof. exact (TRANS (@lem7243821) (@lem7243824)). Qed.
Lemma lem7243826 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243827 : term802 = term486.
Proof. exact (MK_COMB (@lem7243826) (@lem7243825)). Qed.
Lemma lem7243828 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem7243829 : term803 = term488.
Proof. exact (MK_COMB (@lem7243827) (@lem7243828)). Qed.
Lemma lem7243831 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243832 : term488 = term328.
Proof. exact (@lem7243831 term189). Qed.
Lemma lem7243833 : term803 = term328.
Proof. exact (TRANS (@lem7243829) (@lem7243832)). Qed.
Lemma lem7243835 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7243836 : term402 = term403.
Proof. exact (@lem7243835 term189 term189). Qed.
Lemma lem7243837 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243838 : term405 = term189.
Proof. exact (EQ_MP (@lem7243837) (@lem940073)). Qed.
Lemma lem7243839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243840 : term403 = term340.
Proof. exact (MK_COMB (@lem7243839) (@lem7243838)). Qed.
Lemma lem7243841 : term402 = term340.
Proof. exact (TRANS (@lem7243836) (@lem7243840)). Qed.
Lemma lem7243842 : term486 = term486.
Proof. exact (eq_refl term486). Qed.
Lemma lem7243843 : term490 = term488.
Proof. exact (MK_COMB (@lem7243842) (@lem7243841)). Qed.
Lemma lem7243845 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243846 : term488 = term328.
Proof. exact (@lem7243845 term189). Qed.
Lemma lem7243847 : term490 = term328.
Proof. exact (TRANS (@lem7243843) (@lem7243846)). Qed.
Lemma lem7243848 : term328 = term490.
Proof. exact (SYM (@lem7243847)). Qed.
Lemma lem7243849 : term803 = term490.
Proof. exact (TRANS (@lem7243833) (@lem7243848)). Qed.
Lemma lem7243850 : term794 = term390.
Proof. exact (@lem7243800 (@lem7243849)). Qed.
Lemma lem7243851 : term793 = term390.
Proof. exact (TRANS (@lem7243766) (@lem7243850)). Qed.
Lemma lem7243853 (x : real) : (term409 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7243854 : term390 = term328.
Proof. exact (@lem7243853 term328). Qed.
Lemma lem7243855 : term793 = term328.
Proof. exact (TRANS (@lem7243851) (@lem7243854)). Qed.
Lemma lem7243856 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7243857 : term804 = term486.
Proof. exact (MK_COMB (@lem7243856) (@lem7243855)). Qed.
Lemma lem7243858 (_96886 : int) : (real_of_int _96886) = (real_of_int _96886).
Proof. exact (eq_refl (real_of_int _96886)). Qed.
Lemma lem7243859 (_96886 : int) : (term790 _96886) = (term805 _96886).
Proof. exact (MK_COMB (@lem7243857) (@lem7243858 _96886)). Qed.
Lemma lem7243860 (_96886 : int) : (term810 _96886) = (term805 _96886).
Proof. exact (TRANS (@lem7243757 _96886) (@lem7243859 _96886)). Qed.
Lemma lem7243861 (_96886 : int) : (term805 _96886) = term328.
Proof. exact (@lem1982719 (real_of_int _96886)). Qed.
Lemma lem7243862 (_96886 : int) : (term810 _96886) = term328.
Proof. exact (TRANS (@lem7243860 _96886) (@lem7243861 _96886)). Qed.
Lemma lem7243863 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7243864 (_96886 : int) : (term811 _96886) = term807.
Proof. exact (MK_COMB (@lem7243863) (@lem7243862 _96886)). Qed.
Lemma lem7243865 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem7243866 (_96886 : int) : (term809 _96886) = term812.
Proof. exact (MK_COMB (@lem7243864 _96886) (@lem7243865)). Qed.
Lemma lem7243867 (_96886 : int) : (term808 _96886) = term812.
Proof. exact (TRANS (@lem7243756 _96886) (@lem7243866 _96886)). Qed.
Lemma lem7243868 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7243869 (_96886 : int) : (term808 _96886) = term393.
Proof. exact (TRANS (@lem7243867 _96886) (@lem7243868)). Qed.
Lemma lem7243870 (_96885 : int) (_96886 : int) : (term787 _96885 _96886) = term812.
Proof. exact (MK_COMB (@lem7243755 _96885) (@lem7243869 _96886)). Qed.
Lemma lem7243871 (_96885 : int) (_96886 : int) : (term786 _96885 _96886) = term812.
Proof. exact (TRANS (@lem7243647 _96885 _96886) (@lem7243870 _96885 _96886)). Qed.
Lemma lem7243872 : term812 = term393.
Proof. exact (@lem1982721 term393). Qed.
Lemma lem7243873 (_96885 : int) (_96886 : int) : (term786 _96885 _96886) = term393.
Proof. exact (TRANS (@lem7243871 _96885 _96886) (@lem7243872)). Qed.
Lemma lem7243874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7243875 (_96885 : int) (_96886 : int) : (term813 _96885 _96886) = term814.
Proof. exact (MK_COMB (@lem7243874) (@lem7243873 _96885 _96886)). Qed.
Lemma lem7243876 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem7243877 (_96885 : int) (_96886 : int) : (term785 _96885 _96886) = term815.
Proof. exact (MK_COMB (@lem7243875 _96885 _96886) (@lem7243876)). Qed.
Lemma lem7243878 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : term815.
Proof. exact (EQ_MP (@lem7243877 _96885 _96886) (@lem7243646 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243880 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7243881 : term815 = term816.
Proof. exact (@lem7243880 term328 term393). Qed.
Lemma lem7243883 (x : nat) : (term391 x) = (term392 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7243884 : term393 = term394.
Proof. exact (@lem7243883 term189). Qed.
Lemma lem7243886 (x : nat) : (real_of_num x) = (term389 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7243887 : term328 = term390.
Proof. exact (@lem7243886 (NUMERAL 0)). Qed.
Lemma lem7243888 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7243889 : term330 = term817.
Proof. exact (MK_COMB (@lem7243888) (@lem7243887)). Qed.
Lemma lem7243890 : term816 = term818.
Proof. exact (MK_COMB (@lem7243889) (@lem7243884)). Qed.
Lemma lem7243891 : term819.
Proof. exact (@lem1980026 term328 term340 term393 term340). Qed.
Lemma lem7243893 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243894 : term476 = term477.
Proof. exact (@lem7243893 (NUMERAL 0) term189). Qed.
Lemma lem7243895 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243896 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243897 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243896 h1) (fun h1 : term477 = True => @lem7243895)). Qed.
Lemma lem7243898 : term477 = True.
Proof. exact (EQ_MP (@lem7243897) (@lem7243895)). Qed.
Lemma lem7243899 : term476 = True.
Proof. exact (TRANS (@lem7243894) (@lem7243898)). Qed.
Lemma lem7243900 : True = term476.
Proof. exact (SYM (@lem7243899)). Qed.
Lemma lem7243901 : term476.
Proof. exact (EQ_MP (@lem7243900) (@lem0)). Qed.
Lemma lem7243902 : term820.
Proof. exact (@lem7243891 (@lem7243901)). Qed.
Lemma lem7243904 (m : nat) (n : nat) : (term475 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7243905 : term476 = term477.
Proof. exact (@lem7243904 (NUMERAL 0) term189). Qed.
Lemma lem7243906 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243907 (h1 : term478 = (BIT1 0)) : term477 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7243908 : (term478 = (BIT1 0)) = (term477 = True).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243907 h1) (fun h1 : term477 = True => @lem7243906)). Qed.
Lemma lem7243909 : term477 = True.
Proof. exact (EQ_MP (@lem7243908) (@lem7243906)). Qed.
Lemma lem7243910 : term476 = True.
Proof. exact (TRANS (@lem7243905) (@lem7243909)). Qed.
Lemma lem7243911 : True = term476.
Proof. exact (SYM (@lem7243910)). Qed.
Lemma lem7243912 : term476.
Proof. exact (EQ_MP (@lem7243911) (@lem0)). Qed.
Lemma lem7243913 : term818 = term821.
Proof. exact (@lem7243902 (@lem7243912)). Qed.
Lemma lem7243915 (m : nat) (n : nat) : (term442 m n) = (term443 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7243916 : term439 = term444.
Proof. exact (@lem7243915 term189 term189). Qed.
Lemma lem7243917 : (term404 = (BIT1 0)) = (term405 = term189).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7243918 : term405 = term189.
Proof. exact (EQ_MP (@lem7243917) (@lem940073)). Qed.
Lemma lem7243919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7243920 : term403 = term340.
Proof. exact (MK_COMB (@lem7243919) (@lem7243918)). Qed.
Lemma lem7243921 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7243922 : term444 = term393.
Proof. exact (MK_COMB (@lem7243921) (@lem7243920)). Qed.
Lemma lem7243923 : term439 = term393.
Proof. exact (TRANS (@lem7243916) (@lem7243922)). Qed.
Lemma lem7243925 (x : nat) : (term489 x) = term328.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7243926 : term488 = term328.
Proof. exact (@lem7243925 term189). Qed.
Lemma lem7243927 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7243928 : term822 = term330.
Proof. exact (MK_COMB (@lem7243927) (@lem7243926)). Qed.
Lemma lem7243929 : term821 = term816.
Proof. exact (MK_COMB (@lem7243928) (@lem7243923)). Qed.
Lemma lem7243931 (m : nat) (n : nat) : (term823 m n) = (term824 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7243932 : term816 = term825.
Proof. exact (@lem7243931 (NUMERAL 0) term189). Qed.
Lemma lem7243933 : term478 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7243934 (h1 : term478 = (BIT1 0)) : (term189 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7243935 : (term478 = (BIT1 0)) = ((term189 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term478 = (BIT1 0) => @lem7243934 h1) (fun h1 : (term189 = (NUMERAL 0)) = False => @lem7243933)). Qed.
Lemma lem7243936 : (term189 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7243935) (@lem7243933)). Qed.
Lemma lem7243937 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7243938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7243939 : term826 = (and True).
Proof. exact (MK_COMB (@lem7243938) (@lem7243937)). Qed.
Lemma lem7243940 : term825 = (True /\ False).
Proof. exact (MK_COMB (@lem7243939) (@lem7243936)). Qed.
Lemma lem7243942 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7243943 : term825 = False.
Proof. exact (TRANS (@lem7243940) (@lem7243942)). Qed.
Lemma lem7243944 : term816 = False.
Proof. exact (TRANS (@lem7243932) (@lem7243943)). Qed.
Lemma lem7243945 : term821 = False.
Proof. exact (TRANS (@lem7243929) (@lem7243944)). Qed.
Lemma lem7243946 : term818 = False.
Proof. exact (TRANS (@lem7243913) (@lem7243945)). Qed.
Lemma lem7243947 : term816 = False.
Proof. exact (TRANS (@lem7243890) (@lem7243946)). Qed.
Lemma lem7243948 : term815 = False.
Proof. exact (TRANS (@lem7243881) (@lem7243947)). Qed.
Lemma lem7243949 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term880 _96883 _96884 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7243948) (@lem7243878 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243950 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term735 _96883 _96884 _96885 _96886) : False.
Proof. exact (or_elim (@lem7242727 _96883 _96884 _96885 _96886 h1) (fun h0 : term870 _96883 _96884 _96885 _96886 => @lem7243476 _96883 _96884 _96885 _96886 h0) (fun h0 : term880 _96883 _96884 _96885 _96886 => @lem7243949 _96883 _96884 _96885 _96886 h0)). Qed.
Lemma lem7243951 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term744 _96883 _96884 _96885 _96886) : False.
Proof. exact (or_elim (@lem7241399 _96883 _96884 _96885 _96886 h1) (fun h0 : term739 _96884 _96885 _96883 _96886 => @lem7242726 _96884 _96885 _96883 _96886 h0) (fun h0 : term735 _96883 _96884 _96885 _96886 => @lem7243950 _96883 _96884 _96885 _96886 h0)). Qed.
Lemma lem7243952 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term760 _96883 _96884 _96885 _96886) : False.
Proof. exact (or_elim (@lem7239492 _96883 _96884 _96885 _96886 h1) (fun h0 : term757 _96884 _96883 _96885 _96886 => @lem7241398 _96884 _96883 _96885 _96886 h0) (fun h0 : term744 _96883 _96884 _96885 _96886 => @lem7243951 _96883 _96884 _96885 _96886 h0)). Qed.
Lemma lem7243953 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term762 _96883 _96884 _96885 _96886) : False.
Proof. exact (or_elim (@lem7239016 _96883 _96884 _96885 _96886 h1) (fun h0 : term763 _96883 _96884 _96885 _96886 => @lem7239491 _96883 _96884 _96885 _96886 h0) (fun h0 : term760 _96883 _96884 _96885 _96886 => @lem7243952 _96883 _96884 _96885 _96886 h0)). Qed.
Lemma lem7243955 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term762 _96883 _96884 _96885 _96886) : term762 _96883 _96884 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7243956 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term762 _96883 _96884 _96885 _96886) : (term762 _96883 _96884 _96885 _96886) = False.
Proof. exact (prop_ext (fun h2 : term762 _96883 _96884 _96885 _96886 => @lem7243953 _96883 _96884 _96885 _96886 h1) (fun h2 : False => @lem7243955 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243957 (_96883 : int) (_96884 : int) (_96885 : int) (_96886 : int) (h1 : term762 _96883 _96884 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7243956 _96883 _96884 _96885 _96886 h1) (@lem7243955 _96883 _96884 _96885 _96886 h1)). Qed.
Lemma lem7243958 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term385 _96884 _96883 _96885 _96886) : term385 _96884 _96883 _96885 _96886.
Proof. exact (h1). Qed.
Lemma lem7243959 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term385 _96884 _96883 _96885 _96886) : term762 _96883 _96884 _96885 _96886.
Proof. exact (EQ_MP (@lem7238964 _96883 _96884 _96885 _96886) (@lem7243958 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7243960 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term385 _96884 _96883 _96885 _96886) : (term762 _96883 _96884 _96885 _96886) = False.
Proof. exact (prop_ext (fun h2 : term762 _96883 _96884 _96885 _96886 => @lem7243957 _96883 _96884 _96885 _96886 h2) (fun h2 : False => @lem7243959 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7243961 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) (h1 : term385 _96884 _96883 _96885 _96886) : False.
Proof. exact (EQ_MP (@lem7243960 _96884 _96883 _96885 _96886 h1) (@lem7243959 _96884 _96883 _96885 _96886 h1)). Qed.
Lemma lem7243962 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : term881 _96884 _96883 _96885 _96886.
Proof. exact (fun h0 : term385 _96884 _96883 _96885 _96886 => @lem7243961 _96884 _96883 _96885 _96886 h0). Qed.
Lemma lem7243963 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : term882 _96884 _96883 _96885 _96886.
Proof. exact (@lem1386578 (term883 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7243966 (_96884 : int) (_96883 : int) (_96885 : int) (_96886 : int) : term883 _96884 _96883 _96885 _96886.
Proof. exact (@lem7243963 _96884 _96883 _96885 _96886 (@lem7243962 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7243967 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term383 _96884 _96883 _96885 _96886) = (term321 _96884 _96883 _96886 _96885).
Proof. exact (SYM (@lem7237159 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7243968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7243969 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : (term883 _96884 _96883 _96885 _96886) = (term232 _96884 _96883 _96886 _96885).
Proof. exact (MK_COMB (@lem7243968) (@lem7243967 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7243970 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : term232 _96884 _96883 _96886 _96885.
Proof. exact (EQ_MP (@lem7243969 _96884 _96883 _96886 _96885) (@lem7243966 _96884 _96883 _96885 _96886)). Qed.
Lemma lem7243971 (_96884 : int) (_96883 : int) (_96886 : int) (_96885 : int) : term233 _96884 _96883 _96886 _96885.
Proof. exact (EQ_MP (@lem7236512 _96884 _96883 _96886 _96885) (@lem7243970 _96884 _96883 _96886 _96885)). Qed.
Lemma lem7243972 (n : nat) (m : nat) (x : nat) (p : nat) : term884 n m x p.
Proof. exact (@lem7243971 (int_of_num n) (int_of_num m) (int_of_num x) (int_of_num p)). Qed.
Lemma lem7243973 (n : nat) (m : nat) (x : nat) (p : nat) : term885 n m x p.
Proof. exact (@lem7243972 n m x p (@lem7236502 m)). Qed.
Lemma lem7243974 (n : nat) (m : nat) (x : nat) (p : nat) : term886 n m x p.
Proof. exact (@lem7243973 n m x p (@lem7236505 n)). Qed.
Lemma lem7243975 (n : nat) (m : nat) (x : nat) (p : nat) : term887 n m x p.
Proof. exact (@lem7243974 n m x p (@lem7236508 p)). Qed.
Lemma lem7243976 (n : nat) (m : nat) (x : nat) (p : nat) : term227 n m x p.
Proof. exact (@lem7243975 n m x p (@lem7236511 x)). Qed.
Lemma lem7243977 (n : nat) (m : nat) (p : nat) : term229 n m p.
Proof. exact (fun x : nat => @lem7243976 n m x p). Qed.
Lemma lem7243978 (n : nat) (m : nat) (p : nat) : (term229 n m p) = (term91 n m p).
Proof. exact (SYM (@lem7236499 n m p)). Qed.
Lemma lem7243979 (n : nat) (m : nat) (p : nat) : term91 n m p.
Proof. exact (EQ_MP (@lem7243978 n m p) (@lem7243977 n m p)). Qed.
Lemma lem7243980 (n : nat) (m : nat) (p : nat) : (term91 n m p) = ((term91 n m p) = True).
Proof. exact (@lem7 (term91 n m p)). Qed.
Lemma lem7243981 (n : nat) (m : nat) (p : nat) : (term91 n m p) = True.
Proof. exact (EQ_MP (@lem7243980 n m p) (@lem7243979 n m p)). Qed.
Lemma lem7243982 (n : nat) (m : nat) (p : nat) : True = (term91 n m p).
Proof. exact (SYM (@lem7243981 n m p)). Qed.
Lemma lem7243983 (n : nat) (m : nat) (p : nat) : term91 n m p.
Proof. exact (EQ_MP (@lem7243982 n m p) (@lem0)). Qed.
Lemma lem7243984 (p : nat) (m : nat) (n : nat) (h1 : term44 m n) : term89 n m p.
Proof. exact (@lem7243983 n m p (@lem7235649 m n h1)). Qed.
Lemma lem7243985 (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : term85 n m p.
Proof. exact (@lem7243984 p m n h1 (@lem7235648 n p h2)). Qed.
Lemma lem7243986 (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : term86 n m p.
Proof. exact (EQ_MP (@lem7235817 n m p) (@lem7243985 m n p h1 h2)). Qed.
Lemma lem7243987 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : (term888 m n p f) = (term889 m p f).
Proof. exact (@lem7235653 n m p f (@lem7243986 m n p h1 h2)). Qed.
Lemma lem7243988 (m : nat) (n : nat) (p : nat) (h1 : term43 m n p) : Peano.le n p.
Proof. exact (proj2 (@lem7235647 m n p h1)). Qed.
Lemma lem7243989 (m : nat) (n : nat) (p : nat) (h1 : term43 m n p) : term44 m n.
Proof. exact (proj1 (@lem7235647 m n p h1)). Qed.
Lemma lem7243990 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : (Peano.le n p) = ((term888 m n p f) = (term889 m p f)).
Proof. exact (prop_ext (fun h3 : Peano.le n p => @lem7243987 f m n p h1 h2) (fun h3 : (term888 m n p f) = (term889 m p f) => @lem7235648 n p h2)). Qed.
Lemma lem7243991 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : (term888 m n p f) = (term889 m p f).
Proof. exact (EQ_MP (@lem7243990 f m n p h1 h2) (@lem7235648 n p h2)). Qed.
Lemma lem7243992 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : (term44 m n) = ((term888 m n p f) = (term889 m p f)).
Proof. exact (prop_ext (fun h3 : term44 m n => @lem7243991 f m n p h1 h2) (fun h3 : (term888 m n p f) = (term889 m p f) => @lem7235649 m n h1)). Qed.
Lemma lem7243993 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term44 m n) (h2 : Peano.le n p) : (term888 m n p f) = (term889 m p f).
Proof. exact (EQ_MP (@lem7243992 f m n p h1 h2) (@lem7235649 m n h1)). Qed.
Lemma lem7243994 (f : nat -> real) (p : nat) (m : nat) (n : nat) (h1 : term43 m n p) (h2 : term44 m n) : (Peano.le n p) = ((term888 m n p f) = (term889 m p f)).
Proof. exact (prop_ext (fun h3 : Peano.le n p => @lem7243993 f m n p h2 h3) (fun h3 : (term888 m n p f) = (term889 m p f) => @lem7243988 m n p h1)). Qed.
Lemma lem7243995 (f : nat -> real) (p : nat) (m : nat) (n : nat) (h1 : term43 m n p) (h2 : term44 m n) : (term888 m n p f) = (term889 m p f).
Proof. exact (EQ_MP (@lem7243994 f p m n h1 h2) (@lem7243988 m n p h1)). Qed.
Lemma lem7243996 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term43 m n p) : (term44 m n) = ((term888 m n p f) = (term889 m p f)).
Proof. exact (prop_ext (fun h2 : term44 m n => @lem7243995 f p m n h1 h2) (fun h2 : (term888 m n p f) = (term889 m p f) => @lem7243989 m n p h1)). Qed.
Lemma lem7243997 (f : nat -> real) (m : nat) (n : nat) (p : nat) (h1 : term43 m n p) : (term888 m n p f) = (term889 m p f).
Proof. exact (EQ_MP (@lem7243996 f m n p h1) (@lem7243989 m n p h1)). Qed.
Lemma lem7243998 (n : nat) (m : nat) (p : nat) (f : nat -> real) : term890 n m p f.
Proof. exact (fun h0 : term43 m n p => @lem7243997 f m n p h0). Qed.
Lemma lem7244003 (n : nat) (m : nat) (f : nat -> real) : term891 n m f.
Proof. exact (fun p : nat => @lem7243998 n m p f). Qed.
Lemma lem7244008 (m : nat) (f : nat -> real) : term892 m f.
Proof. exact (fun n : nat => @lem7244003 n m f). Qed.
Lemma lem7244013 (f : nat -> real) : term893 f.
Proof. exact (fun m : nat => @lem7244008 m f). Qed.
Lemma lem7244018 : term894.
Proof. exact (fun f : nat -> real => @lem7244013 f). Qed.
