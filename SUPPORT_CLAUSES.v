Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPPORT_CLAUSES_term_abbrevs.
Require Import COND_RAND_spec.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IN_DELETE_spec.
Require Import IN_DIFF_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import IN_INTER_spec.
Require Import IN_UNION_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import o_THM_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm82_spec.
Lemma lem5720612 {A B : Type'} (b : Prop) : term0 A B b.
Proof. exact (@lem12958 A B b). Qed.
Lemma lem5720613 {A B : Type'} (b : Prop) : (term0 A B b) = (term1 A B b).
Proof. exact (eq_refl (term0 A B b)). Qed.
Lemma lem5720614 {A B : Type'} (b : Prop) : term1 A B b.
Proof. exact (EQ_MP (@lem5720613 A B b) (@lem5720612 A B b)). Qed.
Lemma lem5720615 {A B : Type'} (b : Prop) (f : A -> B) : term2 A B b f.
Proof. exact (@lem5720614 A B b f). Qed.
Lemma lem5720616 {A B : Type'} (b : Prop) (f : A -> B) : (term2 A B b f) = (term3 A B b f).
Proof. exact (eq_refl (term2 A B b f)). Qed.
Lemma lem5720617 {A B : Type'} (b : Prop) (f : A -> B) : term3 A B b f.
Proof. exact (EQ_MP (@lem5720616 A B b f) (@lem5720615 A B b f)). Qed.
Lemma lem5720618 {A B : Type'} (b : Prop) (f : A -> B) (x : A) : term4 A B b f x.
Proof. exact (@lem5720617 A B b f x). Qed.
Lemma lem5720619 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : (term4 A B b f x) = (term5 A B b x f).
Proof. exact (eq_refl (term4 A B b f x)). Qed.
Lemma lem5720620 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : term5 A B b x f.
Proof. exact (EQ_MP (@lem5720619 A B b x f) (@lem5720618 A B b f x)). Qed.
Lemma lem5720621 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : term6 A B b x f y.
Proof. exact (@lem5720620 A B b x f y). Qed.
Lemma lem5720622 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term6 A B b x f y) = ((term7 A B f b x y) = (term8 A B b x f y)).
Proof. exact (eq_refl (term6 A B b x f y)). Qed.
Lemma lem5720624 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem5720625 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem5720626 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem5720625 A s) (@lem5720624 A s)). Qed.
Lemma lem5720627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem5720626 A s t). Qed.
Lemma lem5720628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem5720629 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem5720628 A s t) (@lem5720627 A s t)). Qed.
Lemma lem5720630 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem5720629 A s t x). Qed.
Lemma lem5720631 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem5720633 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem5720634 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem5720635 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem5720634 A s) (@lem5720633 A s)). Qed.
Lemma lem5720636 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem5720635 A s t). Qed.
Lemma lem5720637 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term19 A s t).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem5720638 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (EQ_MP (@lem5720637 A s t) (@lem5720636 A s t)). Qed.
Lemma lem5720639 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term20 A s t x.
Proof. exact (@lem5720638 A s t x). Qed.
Lemma lem5720640 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term20 A s t x) = ((term21 A x s t) = (term22 A s x t)).
Proof. exact (eq_refl (term20 A s t x)). Qed.
Lemma lem5720642 {A : Type'} (s : A -> Prop) : term23 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem5720643 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A s).
Proof. exact (eq_refl (term23 A s)). Qed.
Lemma lem5720644 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (EQ_MP (@lem5720643 A s) (@lem5720642 A s)). Qed.
Lemma lem5720645 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term25 A s t.
Proof. exact (@lem5720644 A s t). Qed.
Lemma lem5720646 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term26 A s t).
Proof. exact (eq_refl (term25 A s t)). Qed.
Lemma lem5720647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (EQ_MP (@lem5720646 A s t) (@lem5720645 A s t)). Qed.
Lemma lem5720648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term27 A s t x.
Proof. exact (@lem5720647 A s t x). Qed.
Lemma lem5720649 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A s t x) = ((term28 A x s t) = (term29 A s x t)).
Proof. exact (eq_refl (term27 A s t x)). Qed.
Lemma lem5720651 {A : Type'} (x : A) : term30 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5720652 {A : Type'} (x : A) : (term30 A x) = (term31 A x).
Proof. exact (eq_refl (term30 A x)). Qed.
Lemma lem5720653 {A : Type'} (x : A) : term31 A x.
Proof. exact (EQ_MP (@lem5720652 A x) (@lem5720651 A x)). Qed.
Lemma lem5720654 {A : Type'} (x : A) : term32 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5720656 {A B : Type'} (y : B) : term33 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem5720657 {A B : Type'} (y : B) : (term33 A B y) = (term34 A B y).
Proof. exact (eq_refl (term33 A B y)). Qed.
Lemma lem5720658 {A B : Type'} (y : B) : term34 A B y.
Proof. exact (EQ_MP (@lem5720657 A B y) (@lem5720656 A B y)). Qed.
Lemma lem5720659 {A B : Type'} (y : B) (s : A -> Prop) : term35 A B y s.
Proof. exact (@lem5720658 A B y s). Qed.
Lemma lem5720660 {A B : Type'} (y : B) (s : A -> Prop) : (term35 A B y s) = (term36 A B y s).
Proof. exact (eq_refl (term35 A B y s)). Qed.
Lemma lem5720661 {A B : Type'} (y : B) (s : A -> Prop) : term36 A B y s.
Proof. exact (EQ_MP (@lem5720660 A B y s) (@lem5720659 A B y s)). Qed.
Lemma lem5720662 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term37 A B y s f.
Proof. exact (@lem5720661 A B y s f). Qed.
Lemma lem5720663 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term37 A B y s f) = ((term38 A B y f s) = (term39 A B y f s)).
Proof. exact (eq_refl (term37 A B y s f)). Qed.
Lemma lem5720665 {A B C : Type'} (f : B -> C) : term40 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem5720666 {A B C : Type'} (f : B -> C) : (term40 A B C f) = (term41 A B C f).
Proof. exact (eq_refl (term40 A B C f)). Qed.
Lemma lem5720667 {A B C : Type'} (f : B -> C) : term41 A B C f.
Proof. exact (EQ_MP (@lem5720666 A B C f) (@lem5720665 A B C f)). Qed.
Lemma lem5720668 {A B C : Type'} (f : B -> C) (g : A -> B) : term42 A B C f g.
Proof. exact (@lem5720667 A B C f g). Qed.
Lemma lem5720669 {A B C : Type'} (f : B -> C) (g : A -> B) : (term42 A B C f g) = (term43 A B C f g).
Proof. exact (eq_refl (term42 A B C f g)). Qed.
Lemma lem5720670 {A B C : Type'} (f : B -> C) (g : A -> B) : term43 A B C f g.
Proof. exact (EQ_MP (@lem5720669 A B C f g) (@lem5720668 A B C f g)). Qed.
Lemma lem5720671 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term44 A B C f g x.
Proof. exact (@lem5720670 A B C f g x). Qed.
Lemma lem5720672 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term44 A B C f g x) = ((@o A B C f g x) = (term45 A B C f g x)).
Proof. exact (eq_refl (term44 A B C f g x)). Qed.
Lemma lem5720674 {A : Type'} (s : A -> Prop) : term46 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem5720675 {A : Type'} (s : A -> Prop) : (term46 A s) = (term47 A s).
Proof. exact (eq_refl (term46 A s)). Qed.
Lemma lem5720676 {A : Type'} (s : A -> Prop) : term47 A s.
Proof. exact (EQ_MP (@lem5720675 A s) (@lem5720674 A s)). Qed.
Lemma lem5720677 {A : Type'} (s : A -> Prop) (x : A) : term48 A s x.
Proof. exact (@lem5720676 A s x). Qed.
Lemma lem5720678 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term49 A s x).
Proof. exact (eq_refl (term48 A s x)). Qed.
Lemma lem5720679 {A : Type'} (s : A -> Prop) (x : A) : term49 A s x.
Proof. exact (EQ_MP (@lem5720678 A s x) (@lem5720677 A s x)). Qed.
Lemma lem5720680 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term50 A s x y.
Proof. exact (@lem5720679 A s x y). Qed.
Lemma lem5720681 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term50 A s x y) = ((term51 A x s y) = (term52 A s x y)).
Proof. exact (eq_refl (term50 A s x y)). Qed.
Lemma lem5720683 {A : Type'} (x : A) : term53 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5720684 {A : Type'} (x : A) : (term53 A x) = (term54 A x).
Proof. exact (eq_refl (term53 A x)). Qed.
Lemma lem5720685 {A : Type'} (x : A) : term54 A x.
Proof. exact (EQ_MP (@lem5720684 A x) (@lem5720683 A x)). Qed.
Lemma lem5720686 {A : Type'} (x : A) (y : A) : term55 A x y.
Proof. exact (@lem5720685 A x y). Qed.
Lemma lem5720687 {A : Type'} (y : A) (x : A) : (term55 A x y) = (term56 A y x).
Proof. exact (eq_refl (term55 A x y)). Qed.
Lemma lem5720688 {A : Type'} (y : A) (x : A) : term56 A y x.
Proof. exact (EQ_MP (@lem5720687 A y x) (@lem5720686 A x y)). Qed.
Lemma lem5720689 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term57 A y x s.
Proof. exact (@lem5720688 A y x s). Qed.
Lemma lem5720690 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term57 A y x s) = ((term58 A x y s) = (term59 A y x s)).
Proof. exact (eq_refl (term57 A y x s)). Qed.
Lemma lem5720716 {_83095 : Type'} : term60 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5720717 {_83095 : Type'} (p : _83095 -> Prop) : term61 _83095 p.
Proof. exact (@lem5720716 _83095 p). Qed.
Lemma lem5720718 {_83095 : Type'} (p : _83095 -> Prop) : (term61 _83095 p) = (term62 _83095 p).
Proof. exact (eq_refl (term61 _83095 p)). Qed.
Lemma lem5720719 {_83095 : Type'} (p : _83095 -> Prop) : term62 _83095 p.
Proof. exact (EQ_MP (@lem5720718 _83095 p) (@lem5720717 _83095 p)). Qed.
Lemma lem5720720 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term63 _83095 p x.
Proof. exact (@lem5720719 _83095 p x). Qed.
Lemma lem5720721 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term63 _83095 p x) = ((term64 _83095 x p) = (p x)).
Proof. exact (eq_refl (term63 _83095 p x)). Qed.
Lemma lem5720730 {A : Type'} (s : A -> Prop) : term65 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5720731 {A : Type'} (s : A -> Prop) : (term65 A s) = (term66 A s).
Proof. exact (eq_refl (term65 A s)). Qed.
Lemma lem5720732 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (EQ_MP (@lem5720731 A s) (@lem5720730 A s)). Qed.
Lemma lem5720733 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term67 A s t.
Proof. exact (@lem5720732 A s t). Qed.
Lemma lem5720734 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = ((s = t) = (term68 A s t)).
Proof. exact (eq_refl (term67 A s t)). Qed.
Lemma lem5720736 {A B : Type'} (s : A -> Prop) : term69 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem5720737 {A B : Type'} (s : A -> Prop) : (term69 A B s) = (term70 A B s).
Proof. exact (eq_refl (term69 A B s)). Qed.
Lemma lem5720738 {A B : Type'} (s : A -> Prop) : term70 A B s.
Proof. exact (EQ_MP (@lem5720737 A B s) (@lem5720736 A B s)). Qed.
Lemma lem5720739 {A B : Type'} (s : A -> Prop) (f : A -> B) : term71 A B s f.
Proof. exact (@lem5720738 A B s f). Qed.
Lemma lem5720740 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term72 A B s f).
Proof. exact (eq_refl (term71 A B s f)). Qed.
Lemma lem5720741 {A B : Type'} (s : A -> Prop) (f : A -> B) : term72 A B s f.
Proof. exact (EQ_MP (@lem5720740 A B s f) (@lem5720739 A B s f)). Qed.
Lemma lem5720742 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term73 A B s f op.
Proof. exact (@lem5720741 A B s f op). Qed.
Lemma lem5720743 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term73 A B s f op) = ((@support A B op f s) = (term74 A B s f op)).
Proof. exact (eq_refl (term73 A B s f op)). Qed.
Lemma lem5720766 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5720767 {_119963 : Type'} (s : _119963 -> Prop) (t : _119963 -> Prop) : (s = t) = (term68 _119963 s t).
Proof. exact (@lem5720766 _119963 s t). Qed.
Lemma lem5720768 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : ((@support _119963 _120196 op f (@EMPTY _119963)) = (@EMPTY _119963)) = (term75 _119963 _120196 op f).
Proof. exact (@lem5720767 _119963 (@support _119963 _120196 op f (@EMPTY _119963)) (@EMPTY _119963)). Qed.
Lemma lem5720798 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5720799 {_119963 _120196 : Type'} (s : _119963 -> Prop) (f : _119963 -> _120196) (op : type1400 _120196) : (@support _119963 _120196 op f s) = (term74 _119963 _120196 s f op).
Proof. exact (@lem5720798 _119963 _120196 s f op). Qed.
Lemma lem5720800 {_119963 _120196 : Type'} (f : _119963 -> _120196) (op : type1400 _120196) : (@support _119963 _120196 op f (@EMPTY _119963)) = (term76 _119963 _120196 f op).
Proof. exact (@lem5720799 _119963 _120196 (@EMPTY _119963) f op). Qed.
Lemma lem5720836 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5720654 A x (@lem5720653 A x)). Qed.
Lemma lem5720837 {_119963 : Type'} (x : _119963) : (@IN _119963 x (@EMPTY _119963)) = False.
Proof. exact (@lem5720836 _119963 x). Qed.
Lemma lem5720840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5720841 {_119963 : Type'} (x : _119963) : (term77 _119963 x) = (and False).
Proof. exact (MK_COMB (@lem5720840) (@lem5720837 _119963 x)). Qed.
Lemma lem5720870 {_119963 _120196 : Type'} (f : _119963 -> _120196) (x : _119963) (op : type1400 _120196) : (term78 _119963 _120196 f x op) = (term78 _119963 _120196 f x op).
Proof. exact (eq_refl (term78 _119963 _120196 f x op)). Qed.
Lemma lem5720871 {_119963 _120196 : Type'} (f : _119963 -> _120196) (x : _119963) (op : type1400 _120196) : (term79 _119963 _120196 f x op) = (term80 _119963 _120196 f x op).
Proof. exact (MK_COMB (@lem5720841 _119963 x) (@lem5720870 _119963 _120196 f x op)). Qed.
Lemma lem5720873 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5720874 {_119963 _120196 : Type'} (f : _119963 -> _120196) (x : _119963) (op : type1400 _120196) : (term80 _119963 _120196 f x op) = False.
Proof. exact (@lem5720873 (term78 _119963 _120196 f x op)). Qed.
Lemma lem5720877 {_119963 _120196 : Type'} (f : _119963 -> _120196) (x : _119963) (op : type1400 _120196) : (term79 _119963 _120196 f x op) = False.
Proof. exact (TRANS (@lem5720871 _119963 _120196 f x op) (@lem5720874 _119963 _120196 f x op)). Qed.
Lemma lem5720878 {_119963 : Type'} (GEN_PVAR_237 : _119963) : (@SETSPEC _119963 GEN_PVAR_237) = (@SETSPEC _119963 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119963 GEN_PVAR_237)). Qed.
Lemma lem5720879 {_119963 _120196 : Type'} (f : _119963 -> _120196) (x : _119963) (op : type1400 _120196) (GEN_PVAR_237 : _119963) : (term81 _119963 _120196 GEN_PVAR_237 f x op) = (@SETSPEC _119963 GEN_PVAR_237 False).
Proof. exact (MK_COMB (@lem5720878 _119963 GEN_PVAR_237) (@lem5720877 _119963 _120196 f x op)). Qed.
Lemma lem5720884 {_119963 : Type'} (x : _119963) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5720885 {_119963 _120196 : Type'} (f : _119963 -> _120196) (op : type1400 _120196) (GEN_PVAR_237 : _119963) (x : _119963) : (term82 _119963 _120196 GEN_PVAR_237 f op x) = (@SETSPEC _119963 GEN_PVAR_237 False x).
Proof. exact (MK_COMB (@lem5720879 _119963 _120196 f x op GEN_PVAR_237) (@lem5720884 _119963 x)). Qed.
Lemma lem5720888 {_119963 _120196 : Type'} (f : _119963 -> _120196) (op : type1400 _120196) (GEN_PVAR_237 : _119963) : (term83 _119963 _120196 GEN_PVAR_237 f op) = (term84 _119963 GEN_PVAR_237).
Proof. exact (fun_ext (fun x : _119963 => @lem5720885 _119963 _120196 f op GEN_PVAR_237 x)). Qed.
Lemma lem5720891 {_119963 : Type'} : (@ex _119963) = (@ex _119963).
Proof. exact (eq_refl (@ex _119963)). Qed.
Lemma lem5720892 {_119963 _120196 : Type'} (f : _119963 -> _120196) (op : type1400 _120196) (GEN_PVAR_237 : _119963) : (term85 _119963 _120196 GEN_PVAR_237 f op) = (term86 _119963 GEN_PVAR_237).
Proof. exact (MK_COMB (@lem5720891 _119963) (@lem5720888 _119963 _120196 f op GEN_PVAR_237)). Qed.
Lemma lem5720899 {_119963 _120196 : Type'} (f : _119963 -> _120196) (op : type1400 _120196) : (term87 _119963 _120196 f op) = (term88 _119963).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119963 => @lem5720892 _119963 _120196 f op GEN_PVAR_237)). Qed.
Lemma lem5720902 {_119963 : Type'} : (@GSPEC _119963) = (@GSPEC _119963).
Proof. exact (eq_refl (@GSPEC _119963)). Qed.
Lemma lem5720903 {_119963 _120196 : Type'} (f : _119963 -> _120196) (op : type1400 _120196) : (term76 _119963 _120196 f op) = (term89 _119963).
Proof. exact (MK_COMB (@lem5720902 _119963) (@lem5720899 _119963 _120196 f op)). Qed.
Lemma lem5720906 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (@support _119963 _120196 op f (@EMPTY _119963)) = (term89 _119963).
Proof. exact (TRANS (@lem5720800 _119963 _120196 f op) (@lem5720903 _119963 _120196 f op)). Qed.
Lemma lem5720907 {_119963 : Type'} (x : _119963) : (@IN _119963 x) = (@IN _119963 x).
Proof. exact (eq_refl (@IN _119963 x)). Qed.
Lemma lem5720908 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) (x : _119963) : (term90 _119963 _120196 x op f) = (term91 _119963 x).
Proof. exact (MK_COMB (@lem5720907 _119963 x) (@lem5720906 _119963 _120196 op f)). Qed.
Lemma lem5720910 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5720911 {_119963 : Type'} (p : _119963 -> Prop) (x : _119963) : (term64 _119963 x p) = (p x).
Proof. exact (@lem5720910 _119963 p x). Qed.
Lemma lem5720912 {_119963 : Type'} (x : _119963) : (term92 _119963 x) = (term93 _119963 x).
Proof. exact (@lem5720911 _119963 (term94 _119963) x). Qed.
Lemma lem5720913 {_119963 : Type'} (x : _119963) : (term93 _119963 x) = False.
Proof. exact (eq_refl (term93 _119963 x)). Qed.
Lemma lem5720914 {_119963 : Type'} (GEN_PVAR_237 : _119963) : (@SETSPEC _119963 GEN_PVAR_237) = (@SETSPEC _119963 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119963 GEN_PVAR_237)). Qed.
Lemma lem5720915 {_119963 : Type'} (x : _119963) (GEN_PVAR_237 : _119963) : (term95 _119963 GEN_PVAR_237 x) = (@SETSPEC _119963 GEN_PVAR_237 False).
Proof. exact (MK_COMB (@lem5720914 _119963 GEN_PVAR_237) (@lem5720913 _119963 x)). Qed.
Lemma lem5720916 {_119963 : Type'} (x : _119963) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5720917 {_119963 : Type'} (GEN_PVAR_237 : _119963) (x : _119963) : (term96 _119963 GEN_PVAR_237 x) = (@SETSPEC _119963 GEN_PVAR_237 False x).
Proof. exact (MK_COMB (@lem5720915 _119963 x GEN_PVAR_237) (@lem5720916 _119963 x)). Qed.
Lemma lem5720918 {_119963 : Type'} (GEN_PVAR_237 : _119963) : (term97 _119963 GEN_PVAR_237) = (term84 _119963 GEN_PVAR_237).
Proof. exact (fun_ext (fun x : _119963 => @lem5720917 _119963 GEN_PVAR_237 x)). Qed.
Lemma lem5720919 {_119963 : Type'} : (@ex _119963) = (@ex _119963).
Proof. exact (eq_refl (@ex _119963)). Qed.
Lemma lem5720920 {_119963 : Type'} (GEN_PVAR_237 : _119963) : (term98 _119963 GEN_PVAR_237) = (term86 _119963 GEN_PVAR_237).
Proof. exact (MK_COMB (@lem5720919 _119963) (@lem5720918 _119963 GEN_PVAR_237)). Qed.
Lemma lem5720921 {_119963 : Type'} : (term99 _119963) = (term88 _119963).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119963 => @lem5720920 _119963 GEN_PVAR_237)). Qed.
Lemma lem5720922 {_119963 : Type'} : (@GSPEC _119963) = (@GSPEC _119963).
Proof. exact (eq_refl (@GSPEC _119963)). Qed.
Lemma lem5720923 {_119963 : Type'} : (term100 _119963) = (term89 _119963).
Proof. exact (MK_COMB (@lem5720922 _119963) (@lem5720921 _119963)). Qed.
Lemma lem5720924 {_119963 : Type'} (x : _119963) : (@IN _119963 x) = (@IN _119963 x).
Proof. exact (eq_refl (@IN _119963 x)). Qed.
Lemma lem5720925 {_119963 : Type'} (x : _119963) : (term92 _119963 x) = (term91 _119963 x).
Proof. exact (MK_COMB (@lem5720924 _119963 x) (@lem5720923 _119963)). Qed.
Lemma lem5720926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5720927 {_119963 : Type'} (x : _119963) : (term101 _119963 x) = (term102 _119963 x).
Proof. exact (MK_COMB (@lem5720926) (@lem5720925 _119963 x)). Qed.
Lemma lem5720928 {_119963 : Type'} (x : _119963) : (term93 _119963 x) = False.
Proof. exact (eq_refl (term93 _119963 x)). Qed.
Lemma lem5720929 {_119963 : Type'} (x : _119963) : ((term92 _119963 x) = (term93 _119963 x)) = ((term91 _119963 x) = False).
Proof. exact (MK_COMB (@lem5720927 _119963 x) (@lem5720928 _119963 x)). Qed.
Lemma lem5720930 {_119963 : Type'} (x : _119963) : (term91 _119963 x) = False.
Proof. exact (EQ_MP (@lem5720929 _119963 x) (@lem5720912 _119963 x)). Qed.
Lemma lem5720933 {_119963 _120196 : Type'} (x : _119963) (op : type1400 _120196) (f : _119963 -> _120196) : (term90 _119963 _120196 x op f) = False.
Proof. exact (TRANS (@lem5720908 _119963 _120196 op f x) (@lem5720930 _119963 x)). Qed.
Lemma lem5720934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5720935 {_119963 _120196 : Type'} (x : _119963) (op : type1400 _120196) (f : _119963 -> _120196) : (term103 _119963 _120196 x op f) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5720934) (@lem5720933 _119963 _120196 x op f)). Qed.
Lemma lem5720939 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5720654 A x (@lem5720653 A x)). Qed.
Lemma lem5720940 {_119963 : Type'} (x : _119963) : (@IN _119963 x (@EMPTY _119963)) = False.
Proof. exact (@lem5720939 _119963 x). Qed.
Lemma lem5720943 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) (x : _119963) : ((term90 _119963 _120196 x op f) = (@IN _119963 x (@EMPTY _119963))) = (False = False).
Proof. exact (MK_COMB (@lem5720935 _119963 _120196 x op f) (@lem5720940 _119963 x)). Qed.
Lemma lem5720945 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5720946 : (False = False) = (~ False).
Proof. exact (@lem5720945 False). Qed.
Lemma lem5720948 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5720951 : (False = False) = True.
Proof. exact (TRANS (@lem5720946) (@lem5720948)). Qed.
Lemma lem5720952 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) (x : _119963) : ((term90 _119963 _120196 x op f) = (@IN _119963 x (@EMPTY _119963))) = True.
Proof. exact (TRANS (@lem5720943 _119963 _120196 op f x) (@lem5720951)). Qed.
Lemma lem5720953 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (term104 _119963 _120196 op f) = (term105 _119963).
Proof. exact (fun_ext (fun x : _119963 => @lem5720952 _119963 _120196 op f x)). Qed.
Lemma lem5720956 {_119963 : Type'} : (@all _119963) = (@all _119963).
Proof. exact (eq_refl (@all _119963)). Qed.
Lemma lem5720957 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (term75 _119963 _120196 op f) = (term106 _119963).
Proof. exact (MK_COMB (@lem5720956 _119963) (@lem5720953 _119963 _120196 op f)). Qed.
Lemma lem5720959 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5720960 {_119963 : Type'} (t : Prop) : (term107 _119963 t) = t.
Proof. exact (@lem5720959 _119963 t). Qed.
Lemma lem5720961 {_119963 : Type'} : (term106 _119963) = True.
Proof. exact (@lem5720960 _119963 True). Qed.
Lemma lem5720964 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (term75 _119963 _120196 op f) = True.
Proof. exact (TRANS (@lem5720957 _119963 _120196 op f) (@lem5720961 _119963)). Qed.
Lemma lem5720965 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : ((@support _119963 _120196 op f (@EMPTY _119963)) = (@EMPTY _119963)) = True.
Proof. exact (TRANS (@lem5720768 _119963 _120196 op f) (@lem5720964 _119963 _120196 op f)). Qed.
Lemma lem5720966 {_119963 _120196 : Type'} (op : type1400 _120196) : (term108 _119963 _120196 op) = (term109 _119963 _120196).
Proof. exact (fun_ext (fun f : _119963 -> _120196 => @lem5720965 _119963 _120196 op f)). Qed.
Lemma lem5720969 {_119963 _120196 : Type'} : (@all (_119963 -> _120196)) = (@all (_119963 -> _120196)).
Proof. exact (eq_refl (@all (_119963 -> _120196))). Qed.
Lemma lem5720970 {_119963 _120196 : Type'} (op : type1400 _120196) : (term110 _119963 _120196 op) = (term111 _119963 _120196).
Proof. exact (MK_COMB (@lem5720969 _119963 _120196) (@lem5720966 _119963 _120196 op)). Qed.
Lemma lem5720972 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5720973 {_119963 _120196 : Type'} (t : Prop) : (term112 _119963 _120196 t) = t.
Proof. exact (@lem5720972 (_119963 -> _120196) t). Qed.
Lemma lem5720974 {_119963 _120196 : Type'} : (term111 _119963 _120196) = True.
Proof. exact (@lem5720973 _119963 _120196 True). Qed.
Lemma lem5720977 {_119963 _120196 : Type'} (op : type1400 _120196) : (term110 _119963 _120196 op) = True.
Proof. exact (TRANS (@lem5720970 _119963 _120196 op) (@lem5720974 _119963 _120196)). Qed.
Lemma lem5720978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5720979 {_119963 _120196 : Type'} (op : type1400 _120196) : (term113 _119963 _120196 op) = (and True).
Proof. exact (MK_COMB (@lem5720978) (@lem5720977 _119963 _120196 op)). Qed.
Lemma lem5721023 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5721024 {_120011 : Type'} (s : _120011 -> Prop) (t : _120011 -> Prop) : (s = t) = (term68 _120011 s t).
Proof. exact (@lem5721023 _120011 s t). Qed.
Lemma lem5721025 {_120011 _120196 : Type'} (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) (s : _120011 -> Prop) : ((term114 _120011 _120196 op f x s) = (term115 _120011 _120196 x op f s)) = (term116 _120011 _120196 x op f s).
Proof. exact (@lem5721024 _120011 (term114 _120011 _120196 op f x s) (term115 _120011 _120196 x op f s)). Qed.
Lemma lem5721055 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5721056 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (@support _120011 _120196 op f s) = (term74 _120011 _120196 s f op).
Proof. exact (@lem5721055 _120011 _120196 s f op). Qed.
Lemma lem5721057 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term114 _120011 _120196 op f x s) = (term117 _120011 _120196 x s f op).
Proof. exact (@lem5721056 _120011 _120196 (@INSERT _120011 x s) f op). Qed.
Lemma lem5721093 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term58 A x y s) = (term59 A y x s).
Proof. exact (EQ_MP (@lem5720690 A y x s) (@lem5720689 A y x s)). Qed.
Lemma lem5721094 {_120011 : Type'} (y : _120011) (x : _120011) (s : _120011 -> Prop) : (term58 _120011 x y s) = (term59 _120011 y x s).
Proof. exact (@lem5721093 _120011 y x s). Qed.
Lemma lem5721095 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) : (term58 _120011 x' x s) = (term59 _120011 x x' s).
Proof. exact (@lem5721094 _120011 x x' s). Qed.
Lemma lem5721128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5721129 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) : (term118 _120011 x' x s) = (term119 _120011 x x' s).
Proof. exact (MK_COMB (@lem5721128) (@lem5721095 _120011 x x' s)). Qed.
Lemma lem5721158 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x' op).
Proof. exact (eq_refl (term78 _120011 _120196 f x' op)). Qed.
Lemma lem5721159 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term120 _120011 _120196 x s f x' op) = (term121 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5721129 _120011 x x' s) (@lem5721158 _120011 _120196 f x' op)). Qed.
Lemma lem5721164 {_120011 : Type'} (GEN_PVAR_237 : _120011) : (@SETSPEC _120011 GEN_PVAR_237) = (@SETSPEC _120011 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120011 GEN_PVAR_237)). Qed.
Lemma lem5721165 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term122 _120011 _120196 GEN_PVAR_237 x s f x' op) = (term123 _120011 _120196 GEN_PVAR_237 x s f x' op).
Proof. exact (MK_COMB (@lem5721164 _120011 GEN_PVAR_237) (@lem5721159 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721170 {_120011 : Type'} (x' : _120011) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5721171 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term124 _120011 _120196 GEN_PVAR_237 x s f op x') = (term125 _120011 _120196 GEN_PVAR_237 x s f op x').
Proof. exact (MK_COMB (@lem5721165 _120011 _120196 GEN_PVAR_237 x s f x' op) (@lem5721170 _120011 x')). Qed.
Lemma lem5721174 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term126 _120011 _120196 GEN_PVAR_237 x s f op) = (term127 _120011 _120196 GEN_PVAR_237 x s f op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5721171 _120011 _120196 GEN_PVAR_237 x s f op x')). Qed.
Lemma lem5721177 {_120011 : Type'} : (@ex _120011) = (@ex _120011).
Proof. exact (eq_refl (@ex _120011)). Qed.
Lemma lem5721178 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term128 _120011 _120196 GEN_PVAR_237 x s f op) = (term129 _120011 _120196 GEN_PVAR_237 x s f op).
Proof. exact (MK_COMB (@lem5721177 _120011) (@lem5721174 _120011 _120196 GEN_PVAR_237 x s f op)). Qed.
Lemma lem5721185 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term130 _120011 _120196 x s f op) = (term131 _120011 _120196 x s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120011 => @lem5721178 _120011 _120196 GEN_PVAR_237 x s f op)). Qed.
Lemma lem5721188 {_120011 : Type'} : (@GSPEC _120011) = (@GSPEC _120011).
Proof. exact (eq_refl (@GSPEC _120011)). Qed.
Lemma lem5721189 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term117 _120011 _120196 x s f op) = (term132 _120011 _120196 x s f op).
Proof. exact (MK_COMB (@lem5721188 _120011) (@lem5721185 _120011 _120196 x s f op)). Qed.
Lemma lem5721192 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term114 _120011 _120196 op f x s) = (term132 _120011 _120196 x s f op).
Proof. exact (TRANS (@lem5721057 _120011 _120196 x s f op) (@lem5721189 _120011 _120196 x s f op)). Qed.
Lemma lem5721193 {_120011 : Type'} (x' : _120011) : (@IN _120011 x') = (@IN _120011 x').
Proof. exact (eq_refl (@IN _120011 x')). Qed.
Lemma lem5721194 {_120011 _120196 : Type'} (x' : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term133 _120011 _120196 x' op f x s) = (term134 _120011 _120196 x' x s f op).
Proof. exact (MK_COMB (@lem5721193 _120011 x') (@lem5721192 _120011 _120196 x s f op)). Qed.
Lemma lem5721196 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5721197 {_120011 : Type'} (p : _120011 -> Prop) (x : _120011) : (term64 _120011 x p) = (p x).
Proof. exact (@lem5721196 _120011 p x). Qed.
Lemma lem5721198 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term135 _120011 _120196 x' x s f op) = (term136 _120011 _120196 x s f op x').
Proof. exact (@lem5721197 _120011 (term137 _120011 _120196 x s f op) x'). Qed.
Lemma lem5721199 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term136 _120011 _120196 x s f op x') = (term121 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term136 _120011 _120196 x s f op x')). Qed.
Lemma lem5721200 {_120011 : Type'} (GEN_PVAR_237 : _120011) : (@SETSPEC _120011 GEN_PVAR_237) = (@SETSPEC _120011 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120011 GEN_PVAR_237)). Qed.
Lemma lem5721201 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term138 _120011 _120196 GEN_PVAR_237 x s f op x') = (term123 _120011 _120196 GEN_PVAR_237 x s f x' op).
Proof. exact (MK_COMB (@lem5721200 _120011 GEN_PVAR_237) (@lem5721199 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721202 {_120011 : Type'} (x' : _120011) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5721203 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term139 _120011 _120196 GEN_PVAR_237 x s f op x') = (term125 _120011 _120196 GEN_PVAR_237 x s f op x').
Proof. exact (MK_COMB (@lem5721201 _120011 _120196 GEN_PVAR_237 x s f x' op) (@lem5721202 _120011 x')). Qed.
Lemma lem5721204 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term140 _120011 _120196 GEN_PVAR_237 x s f op) = (term127 _120011 _120196 GEN_PVAR_237 x s f op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5721203 _120011 _120196 GEN_PVAR_237 x s f op x')). Qed.
Lemma lem5721205 {_120011 : Type'} : (@ex _120011) = (@ex _120011).
Proof. exact (eq_refl (@ex _120011)). Qed.
Lemma lem5721206 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term141 _120011 _120196 GEN_PVAR_237 x s f op) = (term129 _120011 _120196 GEN_PVAR_237 x s f op).
Proof. exact (MK_COMB (@lem5721205 _120011) (@lem5721204 _120011 _120196 GEN_PVAR_237 x s f op)). Qed.
Lemma lem5721207 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term142 _120011 _120196 x s f op) = (term131 _120011 _120196 x s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120011 => @lem5721206 _120011 _120196 GEN_PVAR_237 x s f op)). Qed.
Lemma lem5721208 {_120011 : Type'} : (@GSPEC _120011) = (@GSPEC _120011).
Proof. exact (eq_refl (@GSPEC _120011)). Qed.
Lemma lem5721209 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term143 _120011 _120196 x s f op) = (term132 _120011 _120196 x s f op).
Proof. exact (MK_COMB (@lem5721208 _120011) (@lem5721207 _120011 _120196 x s f op)). Qed.
Lemma lem5721210 {_120011 : Type'} (x' : _120011) : (@IN _120011 x') = (@IN _120011 x').
Proof. exact (eq_refl (@IN _120011 x')). Qed.
Lemma lem5721211 {_120011 _120196 : Type'} (x' : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term135 _120011 _120196 x' x s f op) = (term134 _120011 _120196 x' x s f op).
Proof. exact (MK_COMB (@lem5721210 _120011 x') (@lem5721209 _120011 _120196 x s f op)). Qed.
Lemma lem5721212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5721213 {_120011 _120196 : Type'} (x' : _120011) (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term144 _120011 _120196 x' x s f op) = (term145 _120011 _120196 x' x s f op).
Proof. exact (MK_COMB (@lem5721212) (@lem5721211 _120011 _120196 x' x s f op)). Qed.
Lemma lem5721214 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term136 _120011 _120196 x s f op x') = (term121 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term136 _120011 _120196 x s f op x')). Qed.
Lemma lem5721215 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term135 _120011 _120196 x' x s f op) = (term136 _120011 _120196 x s f op x')) = ((term134 _120011 _120196 x' x s f op) = (term121 _120011 _120196 x s f x' op)).
Proof. exact (MK_COMB (@lem5721213 _120011 _120196 x' x s f op) (@lem5721214 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721216 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term134 _120011 _120196 x' x s f op) = (term121 _120011 _120196 x s f x' op).
Proof. exact (EQ_MP (@lem5721215 _120011 _120196 x s f x' op) (@lem5721198 _120011 _120196 x s f op x')). Qed.
Lemma lem5721283 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term133 _120011 _120196 x' op f x s) = (term121 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5721194 _120011 _120196 x' x s f op) (@lem5721216 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5721285 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term146 _120011 _120196 x' op f x s) = (term147 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5721284) (@lem5721283 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721289 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term7 A B f b x y) = (term8 A B b x f y).
Proof. exact (EQ_MP (@lem5720622 A B b x f y) (@lem5720621 A B b x f y)). Qed.
Lemma lem5721290 {_120011 : Type'} (b : Prop) (x : _120011 -> Prop) (f : type686 _120011) (y : _120011 -> Prop) : (term148 _120011 f b x y) = (term149 _120011 b x f y).
Proof. exact (@lem5721289 (_120011 -> Prop) Prop b x f y). Qed.
Lemma lem5721291 {_120011 _120196 : Type'} (x' : _120011) (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) (s : _120011 -> Prop) : (term150 _120011 _120196 x' x op f s) = (term151 _120011 _120196 x' x op f s).
Proof. exact (@lem5721290 _120011 ((f x) = (@neutral _120196 op)) (@support _120011 _120196 op f s) (@IN _120011 x') (term152 _120011 _120196 x op f s)). Qed.
Lemma lem5721333 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5721334 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (@support _120011 _120196 op f s) = (term74 _120011 _120196 s f op).
Proof. exact (@lem5721333 _120011 _120196 s f op). Qed.
Lemma lem5721407 {_120011 : Type'} (x' : _120011) : (@IN _120011 x') = (@IN _120011 x').
Proof. exact (eq_refl (@IN _120011 x')). Qed.
Lemma lem5721408 {_120011 _120196 : Type'} (x' : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term153 _120011 _120196 x' op f s) = (term154 _120011 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5721407 _120011 x') (@lem5721334 _120011 _120196 s f op)). Qed.
Lemma lem5721410 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5721411 {_120011 : Type'} (p : _120011 -> Prop) (x : _120011) : (term64 _120011 x p) = (p x).
Proof. exact (@lem5721410 _120011 p x). Qed.
Lemma lem5721412 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term155 _120011 _120196 x' s f op) = (term156 _120011 _120196 s f op x').
Proof. exact (@lem5721411 _120011 (term157 _120011 _120196 s f op) x'). Qed.
Lemma lem5721413 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term156 _120011 _120196 s f op x) = (term158 _120011 _120196 s f x op).
Proof. exact (eq_refl (term156 _120011 _120196 s f op x)). Qed.
Lemma lem5721414 {_120011 : Type'} (GEN_PVAR_237 : _120011) : (@SETSPEC _120011 GEN_PVAR_237) = (@SETSPEC _120011 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120011 GEN_PVAR_237)). Qed.
Lemma lem5721415 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term159 _120011 _120196 GEN_PVAR_237 s f op x) = (term160 _120011 _120196 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5721414 _120011 GEN_PVAR_237) (@lem5721413 _120011 _120196 s f x op)). Qed.
Lemma lem5721416 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5721417 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x : _120011) : (term161 _120011 _120196 GEN_PVAR_237 s f op x) = (term162 _120011 _120196 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5721415 _120011 _120196 GEN_PVAR_237 s f x op) (@lem5721416 _120011 x)). Qed.
Lemma lem5721418 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term163 _120011 _120196 GEN_PVAR_237 s f op) = (term164 _120011 _120196 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _120011 => @lem5721417 _120011 _120196 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5721419 {_120011 : Type'} : (@ex _120011) = (@ex _120011).
Proof. exact (eq_refl (@ex _120011)). Qed.
Lemma lem5721420 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term165 _120011 _120196 GEN_PVAR_237 s f op) = (term166 _120011 _120196 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5721419 _120011) (@lem5721418 _120011 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5721421 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term167 _120011 _120196 s f op) = (term168 _120011 _120196 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120011 => @lem5721420 _120011 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5721422 {_120011 : Type'} : (@GSPEC _120011) = (@GSPEC _120011).
Proof. exact (eq_refl (@GSPEC _120011)). Qed.
Lemma lem5721423 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term169 _120011 _120196 s f op) = (term74 _120011 _120196 s f op).
Proof. exact (MK_COMB (@lem5721422 _120011) (@lem5721421 _120011 _120196 s f op)). Qed.
Lemma lem5721424 {_120011 : Type'} (x' : _120011) : (@IN _120011 x') = (@IN _120011 x').
Proof. exact (eq_refl (@IN _120011 x')). Qed.
Lemma lem5721425 {_120011 _120196 : Type'} (x' : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term155 _120011 _120196 x' s f op) = (term154 _120011 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5721424 _120011 x') (@lem5721423 _120011 _120196 s f op)). Qed.
Lemma lem5721426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5721427 {_120011 _120196 : Type'} (x' : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term170 _120011 _120196 x' s f op) = (term171 _120011 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5721426) (@lem5721425 _120011 _120196 x' s f op)). Qed.
Lemma lem5721428 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term156 _120011 _120196 s f op x') = (term158 _120011 _120196 s f x' op).
Proof. exact (eq_refl (term156 _120011 _120196 s f op x')). Qed.
Lemma lem5721429 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term155 _120011 _120196 x' s f op) = (term156 _120011 _120196 s f op x')) = ((term154 _120011 _120196 x' s f op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (MK_COMB (@lem5721427 _120011 _120196 x' s f op) (@lem5721428 _120011 _120196 s f x' op)). Qed.
Lemma lem5721430 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term154 _120011 _120196 x' s f op) = (term158 _120011 _120196 s f x' op).
Proof. exact (EQ_MP (@lem5721429 _120011 _120196 s f x' op) (@lem5721412 _120011 _120196 s f op x')). Qed.
Lemma lem5721475 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term153 _120011 _120196 x' op f s) = (term158 _120011 _120196 s f x' op).
Proof. exact (TRANS (@lem5721408 _120011 _120196 x' s f op) (@lem5721430 _120011 _120196 s f x' op)). Qed.
Lemma lem5721476 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term172 _120011 _120196 f x op) = (term172 _120011 _120196 f x op).
Proof. exact (eq_refl (term172 _120011 _120196 f x op)). Qed.
Lemma lem5721477 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term173 _120011 _120196 x x' op f s) = (term174 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5721476 _120011 _120196 f x op) (@lem5721475 _120011 _120196 s f x' op)). Qed.
Lemma lem5721481 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term58 A x y s) = (term59 A y x s).
Proof. exact (EQ_MP (@lem5720690 A y x s) (@lem5720689 A y x s)). Qed.
Lemma lem5721482 {_120011 : Type'} (y : _120011) (x : _120011) (s : _120011 -> Prop) : (term58 _120011 x y s) = (term59 _120011 y x s).
Proof. exact (@lem5721481 _120011 y x s). Qed.
Lemma lem5721483 {_120011 _120196 : Type'} (x : _120011) (x' : _120011) (op : type1400 _120196) (f : _120011 -> _120196) (s : _120011 -> Prop) : (term175 _120011 _120196 x' x op f s) = (term176 _120011 _120196 x x' op f s).
Proof. exact (@lem5721482 _120011 x x' (@support _120011 _120196 op f s)). Qed.
Lemma lem5721515 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5721516 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (@support _120011 _120196 op f s) = (term74 _120011 _120196 s f op).
Proof. exact (@lem5721515 _120011 _120196 s f op). Qed.
Lemma lem5721589 {_120011 : Type'} (x' : _120011) : (@IN _120011 x') = (@IN _120011 x').
Proof. exact (eq_refl (@IN _120011 x')). Qed.
Lemma lem5721590 {_120011 _120196 : Type'} (x' : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term153 _120011 _120196 x' op f s) = (term154 _120011 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5721589 _120011 x') (@lem5721516 _120011 _120196 s f op)). Qed.
Lemma lem5721592 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5721593 {_120011 : Type'} (p : _120011 -> Prop) (x : _120011) : (term64 _120011 x p) = (p x).
Proof. exact (@lem5721592 _120011 p x). Qed.
Lemma lem5721594 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term155 _120011 _120196 x' s f op) = (term156 _120011 _120196 s f op x').
Proof. exact (@lem5721593 _120011 (term157 _120011 _120196 s f op) x'). Qed.
Lemma lem5721595 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term156 _120011 _120196 s f op x) = (term158 _120011 _120196 s f x op).
Proof. exact (eq_refl (term156 _120011 _120196 s f op x)). Qed.
Lemma lem5721596 {_120011 : Type'} (GEN_PVAR_237 : _120011) : (@SETSPEC _120011 GEN_PVAR_237) = (@SETSPEC _120011 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120011 GEN_PVAR_237)). Qed.
Lemma lem5721597 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term159 _120011 _120196 GEN_PVAR_237 s f op x) = (term160 _120011 _120196 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5721596 _120011 GEN_PVAR_237) (@lem5721595 _120011 _120196 s f x op)). Qed.
Lemma lem5721598 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5721599 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x : _120011) : (term161 _120011 _120196 GEN_PVAR_237 s f op x) = (term162 _120011 _120196 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5721597 _120011 _120196 GEN_PVAR_237 s f x op) (@lem5721598 _120011 x)). Qed.
Lemma lem5721600 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term163 _120011 _120196 GEN_PVAR_237 s f op) = (term164 _120011 _120196 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _120011 => @lem5721599 _120011 _120196 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5721601 {_120011 : Type'} : (@ex _120011) = (@ex _120011).
Proof. exact (eq_refl (@ex _120011)). Qed.
Lemma lem5721602 {_120011 _120196 : Type'} (GEN_PVAR_237 : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term165 _120011 _120196 GEN_PVAR_237 s f op) = (term166 _120011 _120196 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5721601 _120011) (@lem5721600 _120011 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5721603 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term167 _120011 _120196 s f op) = (term168 _120011 _120196 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120011 => @lem5721602 _120011 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5721604 {_120011 : Type'} : (@GSPEC _120011) = (@GSPEC _120011).
Proof. exact (eq_refl (@GSPEC _120011)). Qed.
Lemma lem5721605 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term169 _120011 _120196 s f op) = (term74 _120011 _120196 s f op).
Proof. exact (MK_COMB (@lem5721604 _120011) (@lem5721603 _120011 _120196 s f op)). Qed.
Lemma lem5721606 {_120011 : Type'} (x' : _120011) : (@IN _120011 x') = (@IN _120011 x').
Proof. exact (eq_refl (@IN _120011 x')). Qed.
Lemma lem5721607 {_120011 _120196 : Type'} (x' : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term155 _120011 _120196 x' s f op) = (term154 _120011 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5721606 _120011 x') (@lem5721605 _120011 _120196 s f op)). Qed.
Lemma lem5721608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5721609 {_120011 _120196 : Type'} (x' : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term170 _120011 _120196 x' s f op) = (term171 _120011 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5721608) (@lem5721607 _120011 _120196 x' s f op)). Qed.
Lemma lem5721610 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term156 _120011 _120196 s f op x') = (term158 _120011 _120196 s f x' op).
Proof. exact (eq_refl (term156 _120011 _120196 s f op x')). Qed.
Lemma lem5721611 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term155 _120011 _120196 x' s f op) = (term156 _120011 _120196 s f op x')) = ((term154 _120011 _120196 x' s f op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (MK_COMB (@lem5721609 _120011 _120196 x' s f op) (@lem5721610 _120011 _120196 s f x' op)). Qed.
Lemma lem5721612 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term154 _120011 _120196 x' s f op) = (term158 _120011 _120196 s f x' op).
Proof. exact (EQ_MP (@lem5721611 _120011 _120196 s f x' op) (@lem5721594 _120011 _120196 s f op x')). Qed.
Lemma lem5721657 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term153 _120011 _120196 x' op f s) = (term158 _120011 _120196 s f x' op).
Proof. exact (TRANS (@lem5721590 _120011 _120196 x' s f op) (@lem5721612 _120011 _120196 s f x' op)). Qed.
Lemma lem5721658 {_120011 : Type'} (x' : _120011) (x : _120011) : (term177 _120011 x' x) = (term177 _120011 x' x).
Proof. exact (eq_refl (term177 _120011 x' x)). Qed.
Lemma lem5721659 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term176 _120011 _120196 x x' op f s) = (term178 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5721658 _120011 x' x) (@lem5721657 _120011 _120196 s f x' op)). Qed.
Lemma lem5721664 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term175 _120011 _120196 x' x op f s) = (term178 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5721483 _120011 _120196 x x' op f s) (@lem5721659 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721665 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term151 _120011 _120196 x' x op f s) = (term179 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5721477 _120011 _120196 x s f x' op) (@lem5721664 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721670 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term150 _120011 _120196 x' x op f s) = (term179 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5721291 _120011 _120196 x' x op f s) (@lem5721665 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721671 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term133 _120011 _120196 x' op f x s) = (term150 _120011 _120196 x' x op f s)) = ((term121 _120011 _120196 x s f x' op) = (term179 _120011 _120196 x s f x' op)).
Proof. exact (MK_COMB (@lem5721285 _120011 _120196 x s f x' op) (@lem5721670 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721677 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term7 A B f b x y) = (term8 A B b x f y).
Proof. exact (EQ_MP (@lem5720622 A B b x f y) (@lem5720621 A B b x f y)). Qed.
Lemma lem5721678 (b : Prop) (x : Prop) (f : Prop -> Prop) (y : Prop) : (term180 f b x y) = (term181 b x f y).
Proof. exact (@lem5721677 Prop Prop b x f y). Qed.
Lemma lem5721679 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term121 _120011 _120196 x s f x' op) = (term179 _120011 _120196 x s f x' op)) = (term182 _120011 _120196 x s f x' op).
Proof. exact (@lem5721678 ((f x) = (@neutral _120196 op)) (term158 _120011 _120196 s f x' op) (term147 _120011 _120196 x s f x' op) (term178 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721974 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term133 _120011 _120196 x' op f x s) = (term150 _120011 _120196 x' x op f s)) = (term182 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5721671 _120011 _120196 x s f x' op) (@lem5721679 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721975 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term183 _120011 _120196 x op f s) = (term184 _120011 _120196 x s f op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5721974 _120011 _120196 x s f x' op)). Qed.
Lemma lem5721978 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5721979 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : (term116 _120011 _120196 x op f s) = (term185 _120011 _120196 x s f op).
Proof. exact (MK_COMB (@lem5721978 _120011) (@lem5721975 _120011 _120196 x s f op)). Qed.
Lemma lem5721986 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : ((term114 _120011 _120196 op f x s) = (term115 _120011 _120196 x op f s)) = (term185 _120011 _120196 x s f op).
Proof. exact (TRANS (@lem5721025 _120011 _120196 x op f s) (@lem5721979 _120011 _120196 x s f op)). Qed.
Lemma lem5721987 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (op : type1400 _120196) : (term186 _120011 _120196 x op f) = (term187 _120011 _120196 x f op).
Proof. exact (fun_ext (fun s : _120011 -> Prop => @lem5721986 _120011 _120196 x s f op)). Qed.
Lemma lem5721990 {_120011 : Type'} : (@all (_120011 -> Prop)) = (@all (_120011 -> Prop)).
Proof. exact (eq_refl (@all (_120011 -> Prop))). Qed.
Lemma lem5721991 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (op : type1400 _120196) : (term188 _120011 _120196 x op f) = (term189 _120011 _120196 x f op).
Proof. exact (MK_COMB (@lem5721990 _120011) (@lem5721987 _120011 _120196 x f op)). Qed.
Lemma lem5721998 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term190 _120011 _120196 op f) = (term191 _120011 _120196 f op).
Proof. exact (fun_ext (fun x : _120011 => @lem5721991 _120011 _120196 x f op)). Qed.
Lemma lem5722001 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5722002 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term192 _120011 _120196 op f) = (term193 _120011 _120196 f op).
Proof. exact (MK_COMB (@lem5722001 _120011) (@lem5721998 _120011 _120196 f op)). Qed.
Lemma lem5722009 {_120011 _120196 : Type'} (op : type1400 _120196) : (term194 _120011 _120196 op) = (term195 _120011 _120196 op).
Proof. exact (fun_ext (fun f : _120011 -> _120196 => @lem5722002 _120011 _120196 f op)). Qed.
Lemma lem5722012 {_120011 _120196 : Type'} : (@all (_120011 -> _120196)) = (@all (_120011 -> _120196)).
Proof. exact (eq_refl (@all (_120011 -> _120196))). Qed.
Lemma lem5722013 {_120011 _120196 : Type'} (op : type1400 _120196) : (term196 _120011 _120196 op) = (term197 _120011 _120196 op).
Proof. exact (MK_COMB (@lem5722012 _120011 _120196) (@lem5722009 _120011 _120196 op)). Qed.
Lemma lem5722020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5722021 {_120011 _120196 : Type'} (op : type1400 _120196) : (term198 _120011 _120196 op) = (term199 _120011 _120196 op).
Proof. exact (MK_COMB (@lem5722020) (@lem5722013 _120011 _120196 op)). Qed.
Lemma lem5722065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5722066 {_120044 : Type'} (s : _120044 -> Prop) (t : _120044 -> Prop) : (s = t) = (term68 _120044 s t).
Proof. exact (@lem5722065 _120044 s t). Qed.
Lemma lem5722067 {_120044 _120196 : Type'} (op : type1400 _120196) (f : _120044 -> _120196) (s : _120044 -> Prop) (x : _120044) : ((term200 _120044 _120196 op f s x) = (term201 _120044 _120196 op f s x)) = (term202 _120044 _120196 op f s x).
Proof. exact (@lem5722066 _120044 (term200 _120044 _120196 op f s x) (term201 _120044 _120196 op f s x)). Qed.
Lemma lem5722097 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5722098 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (@support _120044 _120196 op f s) = (term74 _120044 _120196 s f op).
Proof. exact (@lem5722097 _120044 _120196 s f op). Qed.
Lemma lem5722099 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term200 _120044 _120196 op f s x) = (term203 _120044 _120196 s x f op).
Proof. exact (@lem5722098 _120044 _120196 (@DELETE _120044 s x) f op). Qed.
Lemma lem5722135 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term51 A x s y) = (term52 A s x y).
Proof. exact (EQ_MP (@lem5720681 A s x y) (@lem5720680 A s x y)). Qed.
Lemma lem5722136 {_120044 : Type'} (s : _120044 -> Prop) (x : _120044) (y : _120044) : (term51 _120044 x s y) = (term52 _120044 s x y).
Proof. exact (@lem5722135 _120044 s x y). Qed.
Lemma lem5722137 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term51 _120044 x' s x) = (term52 _120044 s x' x).
Proof. exact (@lem5722136 _120044 s x' x). Qed.
Lemma lem5722174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5722175 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term204 _120044 x' s x) = (term205 _120044 s x' x).
Proof. exact (MK_COMB (@lem5722174) (@lem5722137 _120044 s x' x)). Qed.
Lemma lem5722204 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term78 _120044 _120196 f x' op) = (term78 _120044 _120196 f x' op).
Proof. exact (eq_refl (term78 _120044 _120196 f x' op)). Qed.
Lemma lem5722205 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term206 _120044 _120196 s x f x' op) = (term207 _120044 _120196 s x f x' op).
Proof. exact (MK_COMB (@lem5722175 _120044 s x' x) (@lem5722204 _120044 _120196 f x' op)). Qed.
Lemma lem5722210 {_120044 : Type'} (GEN_PVAR_237 : _120044) : (@SETSPEC _120044 GEN_PVAR_237) = (@SETSPEC _120044 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120044 GEN_PVAR_237)). Qed.
Lemma lem5722211 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term208 _120044 _120196 GEN_PVAR_237 s x f x' op) = (term209 _120044 _120196 GEN_PVAR_237 s x f x' op).
Proof. exact (MK_COMB (@lem5722210 _120044 GEN_PVAR_237) (@lem5722205 _120044 _120196 s x f x' op)). Qed.
Lemma lem5722216 {_120044 : Type'} (x' : _120044) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5722217 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) : (term210 _120044 _120196 GEN_PVAR_237 s x f op x') = (term211 _120044 _120196 GEN_PVAR_237 s x f op x').
Proof. exact (MK_COMB (@lem5722211 _120044 _120196 GEN_PVAR_237 s x f x' op) (@lem5722216 _120044 x')). Qed.
Lemma lem5722220 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term212 _120044 _120196 GEN_PVAR_237 s x f op) = (term213 _120044 _120196 GEN_PVAR_237 s x f op).
Proof. exact (fun_ext (fun x' : _120044 => @lem5722217 _120044 _120196 GEN_PVAR_237 s x f op x')). Qed.
Lemma lem5722223 {_120044 : Type'} : (@ex _120044) = (@ex _120044).
Proof. exact (eq_refl (@ex _120044)). Qed.
Lemma lem5722224 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term214 _120044 _120196 GEN_PVAR_237 s x f op) = (term215 _120044 _120196 GEN_PVAR_237 s x f op).
Proof. exact (MK_COMB (@lem5722223 _120044) (@lem5722220 _120044 _120196 GEN_PVAR_237 s x f op)). Qed.
Lemma lem5722231 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term216 _120044 _120196 s x f op) = (term217 _120044 _120196 s x f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120044 => @lem5722224 _120044 _120196 GEN_PVAR_237 s x f op)). Qed.
Lemma lem5722234 {_120044 : Type'} : (@GSPEC _120044) = (@GSPEC _120044).
Proof. exact (eq_refl (@GSPEC _120044)). Qed.
Lemma lem5722235 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term203 _120044 _120196 s x f op) = (term218 _120044 _120196 s x f op).
Proof. exact (MK_COMB (@lem5722234 _120044) (@lem5722231 _120044 _120196 s x f op)). Qed.
Lemma lem5722238 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term200 _120044 _120196 op f s x) = (term218 _120044 _120196 s x f op).
Proof. exact (TRANS (@lem5722099 _120044 _120196 s x f op) (@lem5722235 _120044 _120196 s x f op)). Qed.
Lemma lem5722239 {_120044 : Type'} (x' : _120044) : (@IN _120044 x') = (@IN _120044 x').
Proof. exact (eq_refl (@IN _120044 x')). Qed.
Lemma lem5722240 {_120044 _120196 : Type'} (x' : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term219 _120044 _120196 x' op f s x) = (term220 _120044 _120196 x' s x f op).
Proof. exact (MK_COMB (@lem5722239 _120044 x') (@lem5722238 _120044 _120196 s x f op)). Qed.
Lemma lem5722242 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5722243 {_120044 : Type'} (p : _120044 -> Prop) (x : _120044) : (term64 _120044 x p) = (p x).
Proof. exact (@lem5722242 _120044 p x). Qed.
Lemma lem5722244 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) : (term221 _120044 _120196 x' s x f op) = (term222 _120044 _120196 s x f op x').
Proof. exact (@lem5722243 _120044 (term223 _120044 _120196 s x f op) x'). Qed.
Lemma lem5722245 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term222 _120044 _120196 s x f op x') = (term207 _120044 _120196 s x f x' op).
Proof. exact (eq_refl (term222 _120044 _120196 s x f op x')). Qed.
Lemma lem5722246 {_120044 : Type'} (GEN_PVAR_237 : _120044) : (@SETSPEC _120044 GEN_PVAR_237) = (@SETSPEC _120044 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120044 GEN_PVAR_237)). Qed.
Lemma lem5722247 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term224 _120044 _120196 GEN_PVAR_237 s x f op x') = (term209 _120044 _120196 GEN_PVAR_237 s x f x' op).
Proof. exact (MK_COMB (@lem5722246 _120044 GEN_PVAR_237) (@lem5722245 _120044 _120196 s x f x' op)). Qed.
Lemma lem5722248 {_120044 : Type'} (x' : _120044) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5722249 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) : (term225 _120044 _120196 GEN_PVAR_237 s x f op x') = (term211 _120044 _120196 GEN_PVAR_237 s x f op x').
Proof. exact (MK_COMB (@lem5722247 _120044 _120196 GEN_PVAR_237 s x f x' op) (@lem5722248 _120044 x')). Qed.
Lemma lem5722250 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term226 _120044 _120196 GEN_PVAR_237 s x f op) = (term213 _120044 _120196 GEN_PVAR_237 s x f op).
Proof. exact (fun_ext (fun x' : _120044 => @lem5722249 _120044 _120196 GEN_PVAR_237 s x f op x')). Qed.
Lemma lem5722251 {_120044 : Type'} : (@ex _120044) = (@ex _120044).
Proof. exact (eq_refl (@ex _120044)). Qed.
Lemma lem5722252 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term227 _120044 _120196 GEN_PVAR_237 s x f op) = (term215 _120044 _120196 GEN_PVAR_237 s x f op).
Proof. exact (MK_COMB (@lem5722251 _120044) (@lem5722250 _120044 _120196 GEN_PVAR_237 s x f op)). Qed.
Lemma lem5722253 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term228 _120044 _120196 s x f op) = (term217 _120044 _120196 s x f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120044 => @lem5722252 _120044 _120196 GEN_PVAR_237 s x f op)). Qed.
Lemma lem5722254 {_120044 : Type'} : (@GSPEC _120044) = (@GSPEC _120044).
Proof. exact (eq_refl (@GSPEC _120044)). Qed.
Lemma lem5722255 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term229 _120044 _120196 s x f op) = (term218 _120044 _120196 s x f op).
Proof. exact (MK_COMB (@lem5722254 _120044) (@lem5722253 _120044 _120196 s x f op)). Qed.
Lemma lem5722256 {_120044 : Type'} (x' : _120044) : (@IN _120044 x') = (@IN _120044 x').
Proof. exact (eq_refl (@IN _120044 x')). Qed.
Lemma lem5722257 {_120044 _120196 : Type'} (x' : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term221 _120044 _120196 x' s x f op) = (term220 _120044 _120196 x' s x f op).
Proof. exact (MK_COMB (@lem5722256 _120044 x') (@lem5722255 _120044 _120196 s x f op)). Qed.
Lemma lem5722258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5722259 {_120044 _120196 : Type'} (x' : _120044) (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (op : type1400 _120196) : (term230 _120044 _120196 x' s x f op) = (term231 _120044 _120196 x' s x f op).
Proof. exact (MK_COMB (@lem5722258) (@lem5722257 _120044 _120196 x' s x f op)). Qed.
Lemma lem5722260 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term222 _120044 _120196 s x f op x') = (term207 _120044 _120196 s x f x' op).
Proof. exact (eq_refl (term222 _120044 _120196 s x f op x')). Qed.
Lemma lem5722261 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : ((term221 _120044 _120196 x' s x f op) = (term222 _120044 _120196 s x f op x')) = ((term220 _120044 _120196 x' s x f op) = (term207 _120044 _120196 s x f x' op)).
Proof. exact (MK_COMB (@lem5722259 _120044 _120196 x' s x f op) (@lem5722260 _120044 _120196 s x f x' op)). Qed.
Lemma lem5722262 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term220 _120044 _120196 x' s x f op) = (term207 _120044 _120196 s x f x' op).
Proof. exact (EQ_MP (@lem5722261 _120044 _120196 s x f x' op) (@lem5722244 _120044 _120196 s x f op x')). Qed.
Lemma lem5722333 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term219 _120044 _120196 x' op f s x) = (term207 _120044 _120196 s x f x' op).
Proof. exact (TRANS (@lem5722240 _120044 _120196 x' s x f op) (@lem5722262 _120044 _120196 s x f x' op)). Qed.
Lemma lem5722334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5722335 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term232 _120044 _120196 x' op f s x) = (term233 _120044 _120196 s x f x' op).
Proof. exact (MK_COMB (@lem5722334) (@lem5722333 _120044 _120196 s x f x' op)). Qed.
Lemma lem5722339 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term51 A x s y) = (term52 A s x y).
Proof. exact (EQ_MP (@lem5720681 A s x y) (@lem5720680 A s x y)). Qed.
Lemma lem5722340 {_120044 : Type'} (s : _120044 -> Prop) (x : _120044) (y : _120044) : (term51 _120044 x s y) = (term52 _120044 s x y).
Proof. exact (@lem5722339 _120044 s x y). Qed.
Lemma lem5722341 {_120044 _120196 : Type'} (op : type1400 _120196) (f : _120044 -> _120196) (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term234 _120044 _120196 x' op f s x) = (term235 _120044 _120196 op f s x' x).
Proof. exact (@lem5722340 _120044 (@support _120044 _120196 op f s) x' x). Qed.
Lemma lem5722359 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5722360 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (@support _120044 _120196 op f s) = (term74 _120044 _120196 s f op).
Proof. exact (@lem5722359 _120044 _120196 s f op). Qed.
Lemma lem5722433 {_120044 : Type'} (x' : _120044) : (@IN _120044 x') = (@IN _120044 x').
Proof. exact (eq_refl (@IN _120044 x')). Qed.
Lemma lem5722434 {_120044 _120196 : Type'} (x' : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term153 _120044 _120196 x' op f s) = (term154 _120044 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5722433 _120044 x') (@lem5722360 _120044 _120196 s f op)). Qed.
Lemma lem5722436 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5722437 {_120044 : Type'} (p : _120044 -> Prop) (x : _120044) : (term64 _120044 x p) = (p x).
Proof. exact (@lem5722436 _120044 p x). Qed.
Lemma lem5722438 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) : (term155 _120044 _120196 x' s f op) = (term156 _120044 _120196 s f op x').
Proof. exact (@lem5722437 _120044 (term157 _120044 _120196 s f op) x'). Qed.
Lemma lem5722439 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x : _120044) (op : type1400 _120196) : (term156 _120044 _120196 s f op x) = (term158 _120044 _120196 s f x op).
Proof. exact (eq_refl (term156 _120044 _120196 s f op x)). Qed.
Lemma lem5722440 {_120044 : Type'} (GEN_PVAR_237 : _120044) : (@SETSPEC _120044 GEN_PVAR_237) = (@SETSPEC _120044 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120044 GEN_PVAR_237)). Qed.
Lemma lem5722441 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (x : _120044) (op : type1400 _120196) : (term159 _120044 _120196 GEN_PVAR_237 s f op x) = (term160 _120044 _120196 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5722440 _120044 GEN_PVAR_237) (@lem5722439 _120044 _120196 s f x op)). Qed.
Lemma lem5722442 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5722443 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : (term161 _120044 _120196 GEN_PVAR_237 s f op x) = (term162 _120044 _120196 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5722441 _120044 _120196 GEN_PVAR_237 s f x op) (@lem5722442 _120044 x)). Qed.
Lemma lem5722444 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term163 _120044 _120196 GEN_PVAR_237 s f op) = (term164 _120044 _120196 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _120044 => @lem5722443 _120044 _120196 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5722445 {_120044 : Type'} : (@ex _120044) = (@ex _120044).
Proof. exact (eq_refl (@ex _120044)). Qed.
Lemma lem5722446 {_120044 _120196 : Type'} (GEN_PVAR_237 : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term165 _120044 _120196 GEN_PVAR_237 s f op) = (term166 _120044 _120196 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5722445 _120044) (@lem5722444 _120044 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5722447 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term167 _120044 _120196 s f op) = (term168 _120044 _120196 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120044 => @lem5722446 _120044 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5722448 {_120044 : Type'} : (@GSPEC _120044) = (@GSPEC _120044).
Proof. exact (eq_refl (@GSPEC _120044)). Qed.
Lemma lem5722449 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term169 _120044 _120196 s f op) = (term74 _120044 _120196 s f op).
Proof. exact (MK_COMB (@lem5722448 _120044) (@lem5722447 _120044 _120196 s f op)). Qed.
Lemma lem5722450 {_120044 : Type'} (x' : _120044) : (@IN _120044 x') = (@IN _120044 x').
Proof. exact (eq_refl (@IN _120044 x')). Qed.
Lemma lem5722451 {_120044 _120196 : Type'} (x' : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term155 _120044 _120196 x' s f op) = (term154 _120044 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5722450 _120044 x') (@lem5722449 _120044 _120196 s f op)). Qed.
Lemma lem5722452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5722453 {_120044 _120196 : Type'} (x' : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) : (term170 _120044 _120196 x' s f op) = (term171 _120044 _120196 x' s f op).
Proof. exact (MK_COMB (@lem5722452) (@lem5722451 _120044 _120196 x' s f op)). Qed.
Lemma lem5722454 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term156 _120044 _120196 s f op x') = (term158 _120044 _120196 s f x' op).
Proof. exact (eq_refl (term156 _120044 _120196 s f op x')). Qed.
Lemma lem5722455 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : ((term155 _120044 _120196 x' s f op) = (term156 _120044 _120196 s f op x')) = ((term154 _120044 _120196 x' s f op) = (term158 _120044 _120196 s f x' op)).
Proof. exact (MK_COMB (@lem5722453 _120044 _120196 x' s f op) (@lem5722454 _120044 _120196 s f x' op)). Qed.
Lemma lem5722456 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term154 _120044 _120196 x' s f op) = (term158 _120044 _120196 s f x' op).
Proof. exact (EQ_MP (@lem5722455 _120044 _120196 s f x' op) (@lem5722438 _120044 _120196 s f op x')). Qed.
Lemma lem5722501 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term153 _120044 _120196 x' op f s) = (term158 _120044 _120196 s f x' op).
Proof. exact (TRANS (@lem5722434 _120044 _120196 x' s f op) (@lem5722456 _120044 _120196 s f x' op)). Qed.
Lemma lem5722502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5722503 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term236 _120044 _120196 x' op f s) = (term237 _120044 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5722502) (@lem5722501 _120044 _120196 s f x' op)). Qed.
Lemma lem5722524 {_120044 : Type'} (x' : _120044) (x : _120044) : (term238 _120044 x' x) = (term238 _120044 x' x).
Proof. exact (eq_refl (term238 _120044 x' x)). Qed.
Lemma lem5722525 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term235 _120044 _120196 op f s x' x) = (term239 _120044 _120196 s f op x' x).
Proof. exact (MK_COMB (@lem5722503 _120044 _120196 s f x' op) (@lem5722524 _120044 x' x)). Qed.
Lemma lem5722530 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term234 _120044 _120196 x' op f s x) = (term239 _120044 _120196 s f op x' x).
Proof. exact (TRANS (@lem5722341 _120044 _120196 op f s x' x) (@lem5722525 _120044 _120196 s f op x' x)). Qed.
Lemma lem5722531 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : ((term219 _120044 _120196 x' op f s x) = (term234 _120044 _120196 x' op f s x)) = ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)).
Proof. exact (MK_COMB (@lem5722335 _120044 _120196 s x f x' op) (@lem5722530 _120044 _120196 s f op x' x)). Qed.
Lemma lem5722538 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : (term240 _120044 _120196 op f s x) = (term241 _120044 _120196 s f op x).
Proof. exact (fun_ext (fun x' : _120044 => @lem5722531 _120044 _120196 s f op x' x)). Qed.
Lemma lem5722541 {_120044 : Type'} : (@all _120044) = (@all _120044).
Proof. exact (eq_refl (@all _120044)). Qed.
Lemma lem5722542 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : (term202 _120044 _120196 op f s x) = (term242 _120044 _120196 s f op x).
Proof. exact (MK_COMB (@lem5722541 _120044) (@lem5722538 _120044 _120196 s f op x)). Qed.
Lemma lem5722549 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : ((term200 _120044 _120196 op f s x) = (term201 _120044 _120196 op f s x)) = (term242 _120044 _120196 s f op x).
Proof. exact (TRANS (@lem5722067 _120044 _120196 op f s x) (@lem5722542 _120044 _120196 s f op x)). Qed.
Lemma lem5722550 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : (term243 _120044 _120196 op f x) = (term244 _120044 _120196 f op x).
Proof. exact (fun_ext (fun s : _120044 -> Prop => @lem5722549 _120044 _120196 s f op x)). Qed.
Lemma lem5722553 {_120044 : Type'} : (@all (_120044 -> Prop)) = (@all (_120044 -> Prop)).
Proof. exact (eq_refl (@all (_120044 -> Prop))). Qed.
Lemma lem5722554 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : (term245 _120044 _120196 op f x) = (term246 _120044 _120196 f op x).
Proof. exact (MK_COMB (@lem5722553 _120044) (@lem5722550 _120044 _120196 f op x)). Qed.
Lemma lem5722561 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) : (term247 _120044 _120196 op f) = (term248 _120044 _120196 f op).
Proof. exact (fun_ext (fun x : _120044 => @lem5722554 _120044 _120196 f op x)). Qed.
Lemma lem5722564 {_120044 : Type'} : (@all _120044) = (@all _120044).
Proof. exact (eq_refl (@all _120044)). Qed.
Lemma lem5722565 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) : (term249 _120044 _120196 op f) = (term250 _120044 _120196 f op).
Proof. exact (MK_COMB (@lem5722564 _120044) (@lem5722561 _120044 _120196 f op)). Qed.
Lemma lem5722572 {_120044 _120196 : Type'} (op : type1400 _120196) : (term251 _120044 _120196 op) = (term252 _120044 _120196 op).
Proof. exact (fun_ext (fun f : _120044 -> _120196 => @lem5722565 _120044 _120196 f op)). Qed.
Lemma lem5722575 {_120044 _120196 : Type'} : (@all (_120044 -> _120196)) = (@all (_120044 -> _120196)).
Proof. exact (eq_refl (@all (_120044 -> _120196))). Qed.
Lemma lem5722576 {_120044 _120196 : Type'} (op : type1400 _120196) : (term253 _120044 _120196 op) = (term254 _120044 _120196 op).
Proof. exact (MK_COMB (@lem5722575 _120044 _120196) (@lem5722572 _120044 _120196 op)). Qed.
Lemma lem5722583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5722584 {_120044 _120196 : Type'} (op : type1400 _120196) : (term255 _120044 _120196 op) = (term256 _120044 _120196 op).
Proof. exact (MK_COMB (@lem5722583) (@lem5722576 _120044 _120196 op)). Qed.
Lemma lem5722628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5722629 {_120082 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) : (s = t) = (term68 _120082 s t).
Proof. exact (@lem5722628 _120082 s t). Qed.
Lemma lem5722630 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : ((term257 _120082 _120196 op f s t) = (term258 _120082 _120196 s op f t)) = (term259 _120082 _120196 s op f t).
Proof. exact (@lem5722629 _120082 (term257 _120082 _120196 op f s t) (term258 _120082 _120196 s op f t)). Qed.
Lemma lem5722660 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5722661 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (@support _120082 _120196 op f s) = (term74 _120082 _120196 s f op).
Proof. exact (@lem5722660 _120082 _120196 s f op). Qed.
Lemma lem5722662 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term257 _120082 _120196 op f s t) = (term260 _120082 _120196 s t f op).
Proof. exact (@lem5722661 _120082 _120196 (@UNION _120082 s t) f op). Qed.
Lemma lem5722698 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem5720649 A s x t) (@lem5720648 A s t x)). Qed.
Lemma lem5722699 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) : (term28 _120082 x s t) = (term29 _120082 s x t).
Proof. exact (@lem5722698 _120082 s x t). Qed.
Lemma lem5722728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5722729 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) : (term261 _120082 x s t) = (term262 _120082 s x t).
Proof. exact (MK_COMB (@lem5722728) (@lem5722699 _120082 s x t)). Qed.
Lemma lem5722758 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term78 _120082 _120196 f x op).
Proof. exact (eq_refl (term78 _120082 _120196 f x op)). Qed.
Lemma lem5722759 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term263 _120082 _120196 s t f x op) = (term264 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5722729 _120082 s x t) (@lem5722758 _120082 _120196 f x op)). Qed.
Lemma lem5722764 {_120082 : Type'} (GEN_PVAR_237 : _120082) : (@SETSPEC _120082 GEN_PVAR_237) = (@SETSPEC _120082 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120082 GEN_PVAR_237)). Qed.
Lemma lem5722765 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term265 _120082 _120196 GEN_PVAR_237 s t f x op) = (term266 _120082 _120196 GEN_PVAR_237 s t f x op).
Proof. exact (MK_COMB (@lem5722764 _120082 GEN_PVAR_237) (@lem5722759 _120082 _120196 s t f x op)). Qed.
Lemma lem5722770 {_120082 : Type'} (x : _120082) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5722771 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term267 _120082 _120196 GEN_PVAR_237 s t f op x) = (term268 _120082 _120196 GEN_PVAR_237 s t f op x).
Proof. exact (MK_COMB (@lem5722765 _120082 _120196 GEN_PVAR_237 s t f x op) (@lem5722770 _120082 x)). Qed.
Lemma lem5722774 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term269 _120082 _120196 GEN_PVAR_237 s t f op) = (term270 _120082 _120196 GEN_PVAR_237 s t f op).
Proof. exact (fun_ext (fun x : _120082 => @lem5722771 _120082 _120196 GEN_PVAR_237 s t f op x)). Qed.
Lemma lem5722777 {_120082 : Type'} : (@ex _120082) = (@ex _120082).
Proof. exact (eq_refl (@ex _120082)). Qed.
Lemma lem5722778 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term271 _120082 _120196 GEN_PVAR_237 s t f op) = (term272 _120082 _120196 GEN_PVAR_237 s t f op).
Proof. exact (MK_COMB (@lem5722777 _120082) (@lem5722774 _120082 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5722785 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term273 _120082 _120196 s t f op) = (term274 _120082 _120196 s t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120082 => @lem5722778 _120082 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5722788 {_120082 : Type'} : (@GSPEC _120082) = (@GSPEC _120082).
Proof. exact (eq_refl (@GSPEC _120082)). Qed.
Lemma lem5722789 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term260 _120082 _120196 s t f op) = (term275 _120082 _120196 s t f op).
Proof. exact (MK_COMB (@lem5722788 _120082) (@lem5722785 _120082 _120196 s t f op)). Qed.
Lemma lem5722792 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term257 _120082 _120196 op f s t) = (term275 _120082 _120196 s t f op).
Proof. exact (TRANS (@lem5722662 _120082 _120196 s t f op) (@lem5722789 _120082 _120196 s t f op)). Qed.
Lemma lem5722793 {_120082 : Type'} (x : _120082) : (@IN _120082 x) = (@IN _120082 x).
Proof. exact (eq_refl (@IN _120082 x)). Qed.
Lemma lem5722794 {_120082 _120196 : Type'} (x : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term276 _120082 _120196 x op f s t) = (term277 _120082 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5722793 _120082 x) (@lem5722792 _120082 _120196 s t f op)). Qed.
Lemma lem5722796 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5722797 {_120082 : Type'} (p : _120082 -> Prop) (x : _120082) : (term64 _120082 x p) = (p x).
Proof. exact (@lem5722796 _120082 p x). Qed.
Lemma lem5722798 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term278 _120082 _120196 x s t f op) = (term279 _120082 _120196 s t f op x).
Proof. exact (@lem5722797 _120082 (term280 _120082 _120196 s t f op) x). Qed.
Lemma lem5722799 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term279 _120082 _120196 s t f op x) = (term264 _120082 _120196 s t f x op).
Proof. exact (eq_refl (term279 _120082 _120196 s t f op x)). Qed.
Lemma lem5722800 {_120082 : Type'} (GEN_PVAR_237 : _120082) : (@SETSPEC _120082 GEN_PVAR_237) = (@SETSPEC _120082 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120082 GEN_PVAR_237)). Qed.
Lemma lem5722801 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term281 _120082 _120196 GEN_PVAR_237 s t f op x) = (term266 _120082 _120196 GEN_PVAR_237 s t f x op).
Proof. exact (MK_COMB (@lem5722800 _120082 GEN_PVAR_237) (@lem5722799 _120082 _120196 s t f x op)). Qed.
Lemma lem5722802 {_120082 : Type'} (x : _120082) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5722803 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term282 _120082 _120196 GEN_PVAR_237 s t f op x) = (term268 _120082 _120196 GEN_PVAR_237 s t f op x).
Proof. exact (MK_COMB (@lem5722801 _120082 _120196 GEN_PVAR_237 s t f x op) (@lem5722802 _120082 x)). Qed.
Lemma lem5722804 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term283 _120082 _120196 GEN_PVAR_237 s t f op) = (term270 _120082 _120196 GEN_PVAR_237 s t f op).
Proof. exact (fun_ext (fun x : _120082 => @lem5722803 _120082 _120196 GEN_PVAR_237 s t f op x)). Qed.
Lemma lem5722805 {_120082 : Type'} : (@ex _120082) = (@ex _120082).
Proof. exact (eq_refl (@ex _120082)). Qed.
Lemma lem5722806 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term284 _120082 _120196 GEN_PVAR_237 s t f op) = (term272 _120082 _120196 GEN_PVAR_237 s t f op).
Proof. exact (MK_COMB (@lem5722805 _120082) (@lem5722804 _120082 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5722807 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term285 _120082 _120196 s t f op) = (term274 _120082 _120196 s t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120082 => @lem5722806 _120082 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5722808 {_120082 : Type'} : (@GSPEC _120082) = (@GSPEC _120082).
Proof. exact (eq_refl (@GSPEC _120082)). Qed.
Lemma lem5722809 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term286 _120082 _120196 s t f op) = (term275 _120082 _120196 s t f op).
Proof. exact (MK_COMB (@lem5722808 _120082) (@lem5722807 _120082 _120196 s t f op)). Qed.
Lemma lem5722810 {_120082 : Type'} (x : _120082) : (@IN _120082 x) = (@IN _120082 x).
Proof. exact (eq_refl (@IN _120082 x)). Qed.
Lemma lem5722811 {_120082 _120196 : Type'} (x : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term278 _120082 _120196 x s t f op) = (term277 _120082 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5722810 _120082 x) (@lem5722809 _120082 _120196 s t f op)). Qed.
Lemma lem5722812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5722813 {_120082 _120196 : Type'} (x : _120082) (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term287 _120082 _120196 x s t f op) = (term288 _120082 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5722812) (@lem5722811 _120082 _120196 x s t f op)). Qed.
Lemma lem5722814 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term279 _120082 _120196 s t f op x) = (term264 _120082 _120196 s t f x op).
Proof. exact (eq_refl (term279 _120082 _120196 s t f op x)). Qed.
Lemma lem5722815 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term278 _120082 _120196 x s t f op) = (term279 _120082 _120196 s t f op x)) = ((term277 _120082 _120196 x s t f op) = (term264 _120082 _120196 s t f x op)).
Proof. exact (MK_COMB (@lem5722813 _120082 _120196 x s t f op) (@lem5722814 _120082 _120196 s t f x op)). Qed.
Lemma lem5722816 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term277 _120082 _120196 x s t f op) = (term264 _120082 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5722815 _120082 _120196 s t f x op) (@lem5722798 _120082 _120196 s t f op x)). Qed.
Lemma lem5722879 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term276 _120082 _120196 x op f s t) = (term264 _120082 _120196 s t f x op).
Proof. exact (TRANS (@lem5722794 _120082 _120196 x s t f op) (@lem5722816 _120082 _120196 s t f x op)). Qed.
Lemma lem5722880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5722881 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term289 _120082 _120196 x op f s t) = (term290 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5722880) (@lem5722879 _120082 _120196 s t f x op)). Qed.
Lemma lem5722885 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem5720649 A s x t) (@lem5720648 A s t x)). Qed.
Lemma lem5722886 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) : (term28 _120082 x s t) = (term29 _120082 s x t).
Proof. exact (@lem5722885 _120082 s x t). Qed.
Lemma lem5722887 {_120082 _120196 : Type'} (s : _120082 -> Prop) (x : _120082) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : (term291 _120082 _120196 x s op f t) = (term292 _120082 _120196 s x op f t).
Proof. exact (@lem5722886 _120082 (@support _120082 _120196 op f s) x (@support _120082 _120196 op f t)). Qed.
Lemma lem5722905 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5722906 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (@support _120082 _120196 op f s) = (term74 _120082 _120196 s f op).
Proof. exact (@lem5722905 _120082 _120196 s f op). Qed.
Lemma lem5722979 {_120082 : Type'} (x : _120082) : (@IN _120082 x) = (@IN _120082 x).
Proof. exact (eq_refl (@IN _120082 x)). Qed.
Lemma lem5722980 {_120082 _120196 : Type'} (x : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term153 _120082 _120196 x op f s) = (term154 _120082 _120196 x s f op).
Proof. exact (MK_COMB (@lem5722979 _120082 x) (@lem5722906 _120082 _120196 s f op)). Qed.
Lemma lem5722982 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5722983 {_120082 : Type'} (p : _120082 -> Prop) (x : _120082) : (term64 _120082 x p) = (p x).
Proof. exact (@lem5722982 _120082 p x). Qed.
Lemma lem5722984 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term155 _120082 _120196 x s f op) = (term156 _120082 _120196 s f op x).
Proof. exact (@lem5722983 _120082 (term157 _120082 _120196 s f op) x). Qed.
Lemma lem5722985 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term156 _120082 _120196 s f op x) = (term158 _120082 _120196 s f x op).
Proof. exact (eq_refl (term156 _120082 _120196 s f op x)). Qed.
Lemma lem5722986 {_120082 : Type'} (GEN_PVAR_237 : _120082) : (@SETSPEC _120082 GEN_PVAR_237) = (@SETSPEC _120082 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120082 GEN_PVAR_237)). Qed.
Lemma lem5722987 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term159 _120082 _120196 GEN_PVAR_237 s f op x) = (term160 _120082 _120196 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5722986 _120082 GEN_PVAR_237) (@lem5722985 _120082 _120196 s f x op)). Qed.
Lemma lem5722988 {_120082 : Type'} (x : _120082) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5722989 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term161 _120082 _120196 GEN_PVAR_237 s f op x) = (term162 _120082 _120196 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5722987 _120082 _120196 GEN_PVAR_237 s f x op) (@lem5722988 _120082 x)). Qed.
Lemma lem5722990 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term163 _120082 _120196 GEN_PVAR_237 s f op) = (term164 _120082 _120196 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _120082 => @lem5722989 _120082 _120196 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5722991 {_120082 : Type'} : (@ex _120082) = (@ex _120082).
Proof. exact (eq_refl (@ex _120082)). Qed.
Lemma lem5722992 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term165 _120082 _120196 GEN_PVAR_237 s f op) = (term166 _120082 _120196 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5722991 _120082) (@lem5722990 _120082 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5722993 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term167 _120082 _120196 s f op) = (term168 _120082 _120196 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120082 => @lem5722992 _120082 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5722994 {_120082 : Type'} : (@GSPEC _120082) = (@GSPEC _120082).
Proof. exact (eq_refl (@GSPEC _120082)). Qed.
Lemma lem5722995 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term169 _120082 _120196 s f op) = (term74 _120082 _120196 s f op).
Proof. exact (MK_COMB (@lem5722994 _120082) (@lem5722993 _120082 _120196 s f op)). Qed.
Lemma lem5722996 {_120082 : Type'} (x : _120082) : (@IN _120082 x) = (@IN _120082 x).
Proof. exact (eq_refl (@IN _120082 x)). Qed.
Lemma lem5722997 {_120082 _120196 : Type'} (x : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term155 _120082 _120196 x s f op) = (term154 _120082 _120196 x s f op).
Proof. exact (MK_COMB (@lem5722996 _120082 x) (@lem5722995 _120082 _120196 s f op)). Qed.
Lemma lem5722998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5722999 {_120082 _120196 : Type'} (x : _120082) (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term170 _120082 _120196 x s f op) = (term171 _120082 _120196 x s f op).
Proof. exact (MK_COMB (@lem5722998) (@lem5722997 _120082 _120196 x s f op)). Qed.
Lemma lem5723000 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term156 _120082 _120196 s f op x) = (term158 _120082 _120196 s f x op).
Proof. exact (eq_refl (term156 _120082 _120196 s f op x)). Qed.
Lemma lem5723001 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term155 _120082 _120196 x s f op) = (term156 _120082 _120196 s f op x)) = ((term154 _120082 _120196 x s f op) = (term158 _120082 _120196 s f x op)).
Proof. exact (MK_COMB (@lem5722999 _120082 _120196 x s f op) (@lem5723000 _120082 _120196 s f x op)). Qed.
Lemma lem5723002 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term154 _120082 _120196 x s f op) = (term158 _120082 _120196 s f x op).
Proof. exact (EQ_MP (@lem5723001 _120082 _120196 s f x op) (@lem5722984 _120082 _120196 s f op x)). Qed.
Lemma lem5723047 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term153 _120082 _120196 x op f s) = (term158 _120082 _120196 s f x op).
Proof. exact (TRANS (@lem5722980 _120082 _120196 x s f op) (@lem5723002 _120082 _120196 s f x op)). Qed.
Lemma lem5723048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5723049 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term293 _120082 _120196 x op f s) = (term294 _120082 _120196 s f x op).
Proof. exact (MK_COMB (@lem5723048) (@lem5723047 _120082 _120196 s f x op)). Qed.
Lemma lem5723061 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5723062 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (@support _120082 _120196 op f s) = (term74 _120082 _120196 s f op).
Proof. exact (@lem5723061 _120082 _120196 s f op). Qed.
Lemma lem5723063 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (@support _120082 _120196 op f t) = (term74 _120082 _120196 t f op).
Proof. exact (@lem5723062 _120082 _120196 t f op). Qed.
Lemma lem5723136 {_120082 : Type'} (x : _120082) : (@IN _120082 x) = (@IN _120082 x).
Proof. exact (eq_refl (@IN _120082 x)). Qed.
Lemma lem5723137 {_120082 _120196 : Type'} (x : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term153 _120082 _120196 x op f t) = (term154 _120082 _120196 x t f op).
Proof. exact (MK_COMB (@lem5723136 _120082 x) (@lem5723063 _120082 _120196 t f op)). Qed.
Lemma lem5723139 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5723140 {_120082 : Type'} (p : _120082 -> Prop) (x : _120082) : (term64 _120082 x p) = (p x).
Proof. exact (@lem5723139 _120082 p x). Qed.
Lemma lem5723141 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term155 _120082 _120196 x t f op) = (term156 _120082 _120196 t f op x).
Proof. exact (@lem5723140 _120082 (term157 _120082 _120196 t f op) x). Qed.
Lemma lem5723142 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term156 _120082 _120196 t f op x) = (term158 _120082 _120196 t f x op).
Proof. exact (eq_refl (term156 _120082 _120196 t f op x)). Qed.
Lemma lem5723143 {_120082 : Type'} (GEN_PVAR_237 : _120082) : (@SETSPEC _120082 GEN_PVAR_237) = (@SETSPEC _120082 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120082 GEN_PVAR_237)). Qed.
Lemma lem5723144 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term159 _120082 _120196 GEN_PVAR_237 t f op x) = (term160 _120082 _120196 GEN_PVAR_237 t f x op).
Proof. exact (MK_COMB (@lem5723143 _120082 GEN_PVAR_237) (@lem5723142 _120082 _120196 t f x op)). Qed.
Lemma lem5723145 {_120082 : Type'} (x : _120082) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5723146 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) : (term161 _120082 _120196 GEN_PVAR_237 t f op x) = (term162 _120082 _120196 GEN_PVAR_237 t f op x).
Proof. exact (MK_COMB (@lem5723144 _120082 _120196 GEN_PVAR_237 t f x op) (@lem5723145 _120082 x)). Qed.
Lemma lem5723147 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term163 _120082 _120196 GEN_PVAR_237 t f op) = (term164 _120082 _120196 GEN_PVAR_237 t f op).
Proof. exact (fun_ext (fun x : _120082 => @lem5723146 _120082 _120196 GEN_PVAR_237 t f op x)). Qed.
Lemma lem5723148 {_120082 : Type'} : (@ex _120082) = (@ex _120082).
Proof. exact (eq_refl (@ex _120082)). Qed.
Lemma lem5723149 {_120082 _120196 : Type'} (GEN_PVAR_237 : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term165 _120082 _120196 GEN_PVAR_237 t f op) = (term166 _120082 _120196 GEN_PVAR_237 t f op).
Proof. exact (MK_COMB (@lem5723148 _120082) (@lem5723147 _120082 _120196 GEN_PVAR_237 t f op)). Qed.
Lemma lem5723150 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term167 _120082 _120196 t f op) = (term168 _120082 _120196 t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120082 => @lem5723149 _120082 _120196 GEN_PVAR_237 t f op)). Qed.
Lemma lem5723151 {_120082 : Type'} : (@GSPEC _120082) = (@GSPEC _120082).
Proof. exact (eq_refl (@GSPEC _120082)). Qed.
Lemma lem5723152 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term169 _120082 _120196 t f op) = (term74 _120082 _120196 t f op).
Proof. exact (MK_COMB (@lem5723151 _120082) (@lem5723150 _120082 _120196 t f op)). Qed.
Lemma lem5723153 {_120082 : Type'} (x : _120082) : (@IN _120082 x) = (@IN _120082 x).
Proof. exact (eq_refl (@IN _120082 x)). Qed.
Lemma lem5723154 {_120082 _120196 : Type'} (x : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term155 _120082 _120196 x t f op) = (term154 _120082 _120196 x t f op).
Proof. exact (MK_COMB (@lem5723153 _120082 x) (@lem5723152 _120082 _120196 t f op)). Qed.
Lemma lem5723155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5723156 {_120082 _120196 : Type'} (x : _120082) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term170 _120082 _120196 x t f op) = (term171 _120082 _120196 x t f op).
Proof. exact (MK_COMB (@lem5723155) (@lem5723154 _120082 _120196 x t f op)). Qed.
Lemma lem5723157 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term156 _120082 _120196 t f op x) = (term158 _120082 _120196 t f x op).
Proof. exact (eq_refl (term156 _120082 _120196 t f op x)). Qed.
Lemma lem5723158 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term155 _120082 _120196 x t f op) = (term156 _120082 _120196 t f op x)) = ((term154 _120082 _120196 x t f op) = (term158 _120082 _120196 t f x op)).
Proof. exact (MK_COMB (@lem5723156 _120082 _120196 x t f op) (@lem5723157 _120082 _120196 t f x op)). Qed.
Lemma lem5723159 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term154 _120082 _120196 x t f op) = (term158 _120082 _120196 t f x op).
Proof. exact (EQ_MP (@lem5723158 _120082 _120196 t f x op) (@lem5723141 _120082 _120196 t f op x)). Qed.
Lemma lem5723204 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term153 _120082 _120196 x op f t) = (term158 _120082 _120196 t f x op).
Proof. exact (TRANS (@lem5723137 _120082 _120196 x t f op) (@lem5723159 _120082 _120196 t f x op)). Qed.
Lemma lem5723205 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term292 _120082 _120196 s x op f t) = (term295 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5723049 _120082 _120196 s f x op) (@lem5723204 _120082 _120196 t f x op)). Qed.
Lemma lem5723210 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term291 _120082 _120196 x s op f t) = (term295 _120082 _120196 s t f x op).
Proof. exact (TRANS (@lem5722887 _120082 _120196 s x op f t) (@lem5723205 _120082 _120196 s t f x op)). Qed.
Lemma lem5723211 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term276 _120082 _120196 x op f s t) = (term291 _120082 _120196 x s op f t)) = ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)).
Proof. exact (MK_COMB (@lem5722881 _120082 _120196 s t f x op) (@lem5723210 _120082 _120196 s t f x op)). Qed.
Lemma lem5723218 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term296 _120082 _120196 s op f t) = (term297 _120082 _120196 s t f op).
Proof. exact (fun_ext (fun x : _120082 => @lem5723211 _120082 _120196 s t f x op)). Qed.
Lemma lem5723221 {_120082 : Type'} : (@all _120082) = (@all _120082).
Proof. exact (eq_refl (@all _120082)). Qed.
Lemma lem5723222 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term259 _120082 _120196 s op f t) = (term298 _120082 _120196 s t f op).
Proof. exact (MK_COMB (@lem5723221 _120082) (@lem5723218 _120082 _120196 s t f op)). Qed.
Lemma lem5723229 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : ((term257 _120082 _120196 op f s t) = (term258 _120082 _120196 s op f t)) = (term298 _120082 _120196 s t f op).
Proof. exact (TRANS (@lem5722630 _120082 _120196 s op f t) (@lem5723222 _120082 _120196 s t f op)). Qed.
Lemma lem5723230 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term299 _120082 _120196 s op f) = (term300 _120082 _120196 s f op).
Proof. exact (fun_ext (fun t : _120082 -> Prop => @lem5723229 _120082 _120196 s t f op)). Qed.
Lemma lem5723233 {_120082 : Type'} : (@all (_120082 -> Prop)) = (@all (_120082 -> Prop)).
Proof. exact (eq_refl (@all (_120082 -> Prop))). Qed.
Lemma lem5723234 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : (term301 _120082 _120196 s op f) = (term302 _120082 _120196 s f op).
Proof. exact (MK_COMB (@lem5723233 _120082) (@lem5723230 _120082 _120196 s f op)). Qed.
Lemma lem5723241 {_120082 _120196 : Type'} (f : _120082 -> _120196) (op : type1400 _120196) : (term303 _120082 _120196 op f) = (term304 _120082 _120196 f op).
Proof. exact (fun_ext (fun s : _120082 -> Prop => @lem5723234 _120082 _120196 s f op)). Qed.
Lemma lem5723244 {_120082 : Type'} : (@all (_120082 -> Prop)) = (@all (_120082 -> Prop)).
Proof. exact (eq_refl (@all (_120082 -> Prop))). Qed.
Lemma lem5723245 {_120082 _120196 : Type'} (f : _120082 -> _120196) (op : type1400 _120196) : (term305 _120082 _120196 op f) = (term306 _120082 _120196 f op).
Proof. exact (MK_COMB (@lem5723244 _120082) (@lem5723241 _120082 _120196 f op)). Qed.
Lemma lem5723252 {_120082 _120196 : Type'} (op : type1400 _120196) : (term307 _120082 _120196 op) = (term308 _120082 _120196 op).
Proof. exact (fun_ext (fun f : _120082 -> _120196 => @lem5723245 _120082 _120196 f op)). Qed.
Lemma lem5723255 {_120082 _120196 : Type'} : (@all (_120082 -> _120196)) = (@all (_120082 -> _120196)).
Proof. exact (eq_refl (@all (_120082 -> _120196))). Qed.
Lemma lem5723256 {_120082 _120196 : Type'} (op : type1400 _120196) : (term309 _120082 _120196 op) = (term310 _120082 _120196 op).
Proof. exact (MK_COMB (@lem5723255 _120082 _120196) (@lem5723252 _120082 _120196 op)). Qed.
Lemma lem5723263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5723264 {_120082 _120196 : Type'} (op : type1400 _120196) : (term311 _120082 _120196 op) = (term312 _120082 _120196 op).
Proof. exact (MK_COMB (@lem5723263) (@lem5723256 _120082 _120196 op)). Qed.
Lemma lem5723308 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5723309 {_120120 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) : (s = t) = (term68 _120120 s t).
Proof. exact (@lem5723308 _120120 s t). Qed.
Lemma lem5723310 {_120120 _120196 : Type'} (s : _120120 -> Prop) (op : type1400 _120196) (f : _120120 -> _120196) (t : _120120 -> Prop) : ((term313 _120120 _120196 op f s t) = (term314 _120120 _120196 s op f t)) = (term315 _120120 _120196 s op f t).
Proof. exact (@lem5723309 _120120 (term313 _120120 _120196 op f s t) (term314 _120120 _120196 s op f t)). Qed.
Lemma lem5723340 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5723341 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (@support _120120 _120196 op f s) = (term74 _120120 _120196 s f op).
Proof. exact (@lem5723340 _120120 _120196 s f op). Qed.
Lemma lem5723342 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term313 _120120 _120196 op f s t) = (term316 _120120 _120196 s t f op).
Proof. exact (@lem5723341 _120120 _120196 (@INTER _120120 s t) f op). Qed.
Lemma lem5723378 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem5720640 A s x t) (@lem5720639 A s t x)). Qed.
Lemma lem5723379 {_120120 : Type'} (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) : (term21 _120120 x s t) = (term22 _120120 s x t).
Proof. exact (@lem5723378 _120120 s x t). Qed.
Lemma lem5723408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5723409 {_120120 : Type'} (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) : (term317 _120120 x s t) = (term318 _120120 s x t).
Proof. exact (MK_COMB (@lem5723408) (@lem5723379 _120120 s x t)). Qed.
Lemma lem5723438 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term78 _120120 _120196 f x op) = (term78 _120120 _120196 f x op).
Proof. exact (eq_refl (term78 _120120 _120196 f x op)). Qed.
Lemma lem5723439 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term319 _120120 _120196 s t f x op) = (term320 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5723409 _120120 s x t) (@lem5723438 _120120 _120196 f x op)). Qed.
Lemma lem5723444 {_120120 : Type'} (GEN_PVAR_237 : _120120) : (@SETSPEC _120120 GEN_PVAR_237) = (@SETSPEC _120120 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120120 GEN_PVAR_237)). Qed.
Lemma lem5723445 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term321 _120120 _120196 GEN_PVAR_237 s t f x op) = (term322 _120120 _120196 GEN_PVAR_237 s t f x op).
Proof. exact (MK_COMB (@lem5723444 _120120 GEN_PVAR_237) (@lem5723439 _120120 _120196 s t f x op)). Qed.
Lemma lem5723450 {_120120 : Type'} (x : _120120) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5723451 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term323 _120120 _120196 GEN_PVAR_237 s t f op x) = (term324 _120120 _120196 GEN_PVAR_237 s t f op x).
Proof. exact (MK_COMB (@lem5723445 _120120 _120196 GEN_PVAR_237 s t f x op) (@lem5723450 _120120 x)). Qed.
Lemma lem5723454 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term325 _120120 _120196 GEN_PVAR_237 s t f op) = (term326 _120120 _120196 GEN_PVAR_237 s t f op).
Proof. exact (fun_ext (fun x : _120120 => @lem5723451 _120120 _120196 GEN_PVAR_237 s t f op x)). Qed.
Lemma lem5723457 {_120120 : Type'} : (@ex _120120) = (@ex _120120).
Proof. exact (eq_refl (@ex _120120)). Qed.
Lemma lem5723458 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term327 _120120 _120196 GEN_PVAR_237 s t f op) = (term328 _120120 _120196 GEN_PVAR_237 s t f op).
Proof. exact (MK_COMB (@lem5723457 _120120) (@lem5723454 _120120 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5723465 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term329 _120120 _120196 s t f op) = (term330 _120120 _120196 s t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120120 => @lem5723458 _120120 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5723468 {_120120 : Type'} : (@GSPEC _120120) = (@GSPEC _120120).
Proof. exact (eq_refl (@GSPEC _120120)). Qed.
Lemma lem5723469 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term316 _120120 _120196 s t f op) = (term331 _120120 _120196 s t f op).
Proof. exact (MK_COMB (@lem5723468 _120120) (@lem5723465 _120120 _120196 s t f op)). Qed.
Lemma lem5723472 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term313 _120120 _120196 op f s t) = (term331 _120120 _120196 s t f op).
Proof. exact (TRANS (@lem5723342 _120120 _120196 s t f op) (@lem5723469 _120120 _120196 s t f op)). Qed.
Lemma lem5723473 {_120120 : Type'} (x : _120120) : (@IN _120120 x) = (@IN _120120 x).
Proof. exact (eq_refl (@IN _120120 x)). Qed.
Lemma lem5723474 {_120120 _120196 : Type'} (x : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term332 _120120 _120196 x op f s t) = (term333 _120120 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5723473 _120120 x) (@lem5723472 _120120 _120196 s t f op)). Qed.
Lemma lem5723476 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5723477 {_120120 : Type'} (p : _120120 -> Prop) (x : _120120) : (term64 _120120 x p) = (p x).
Proof. exact (@lem5723476 _120120 p x). Qed.
Lemma lem5723478 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term334 _120120 _120196 x s t f op) = (term335 _120120 _120196 s t f op x).
Proof. exact (@lem5723477 _120120 (term336 _120120 _120196 s t f op) x). Qed.
Lemma lem5723479 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term335 _120120 _120196 s t f op x) = (term320 _120120 _120196 s t f x op).
Proof. exact (eq_refl (term335 _120120 _120196 s t f op x)). Qed.
Lemma lem5723480 {_120120 : Type'} (GEN_PVAR_237 : _120120) : (@SETSPEC _120120 GEN_PVAR_237) = (@SETSPEC _120120 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120120 GEN_PVAR_237)). Qed.
Lemma lem5723481 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term337 _120120 _120196 GEN_PVAR_237 s t f op x) = (term322 _120120 _120196 GEN_PVAR_237 s t f x op).
Proof. exact (MK_COMB (@lem5723480 _120120 GEN_PVAR_237) (@lem5723479 _120120 _120196 s t f x op)). Qed.
Lemma lem5723482 {_120120 : Type'} (x : _120120) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5723483 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term338 _120120 _120196 GEN_PVAR_237 s t f op x) = (term324 _120120 _120196 GEN_PVAR_237 s t f op x).
Proof. exact (MK_COMB (@lem5723481 _120120 _120196 GEN_PVAR_237 s t f x op) (@lem5723482 _120120 x)). Qed.
Lemma lem5723484 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term339 _120120 _120196 GEN_PVAR_237 s t f op) = (term326 _120120 _120196 GEN_PVAR_237 s t f op).
Proof. exact (fun_ext (fun x : _120120 => @lem5723483 _120120 _120196 GEN_PVAR_237 s t f op x)). Qed.
Lemma lem5723485 {_120120 : Type'} : (@ex _120120) = (@ex _120120).
Proof. exact (eq_refl (@ex _120120)). Qed.
Lemma lem5723486 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term340 _120120 _120196 GEN_PVAR_237 s t f op) = (term328 _120120 _120196 GEN_PVAR_237 s t f op).
Proof. exact (MK_COMB (@lem5723485 _120120) (@lem5723484 _120120 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5723487 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term341 _120120 _120196 s t f op) = (term330 _120120 _120196 s t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120120 => @lem5723486 _120120 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5723488 {_120120 : Type'} : (@GSPEC _120120) = (@GSPEC _120120).
Proof. exact (eq_refl (@GSPEC _120120)). Qed.
Lemma lem5723489 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term342 _120120 _120196 s t f op) = (term331 _120120 _120196 s t f op).
Proof. exact (MK_COMB (@lem5723488 _120120) (@lem5723487 _120120 _120196 s t f op)). Qed.
Lemma lem5723490 {_120120 : Type'} (x : _120120) : (@IN _120120 x) = (@IN _120120 x).
Proof. exact (eq_refl (@IN _120120 x)). Qed.
Lemma lem5723491 {_120120 _120196 : Type'} (x : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term334 _120120 _120196 x s t f op) = (term333 _120120 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5723490 _120120 x) (@lem5723489 _120120 _120196 s t f op)). Qed.
Lemma lem5723492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5723493 {_120120 _120196 : Type'} (x : _120120) (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term343 _120120 _120196 x s t f op) = (term344 _120120 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5723492) (@lem5723491 _120120 _120196 x s t f op)). Qed.
Lemma lem5723494 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term335 _120120 _120196 s t f op x) = (term320 _120120 _120196 s t f x op).
Proof. exact (eq_refl (term335 _120120 _120196 s t f op x)). Qed.
Lemma lem5723495 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term334 _120120 _120196 x s t f op) = (term335 _120120 _120196 s t f op x)) = ((term333 _120120 _120196 x s t f op) = (term320 _120120 _120196 s t f x op)).
Proof. exact (MK_COMB (@lem5723493 _120120 _120196 x s t f op) (@lem5723494 _120120 _120196 s t f x op)). Qed.
Lemma lem5723496 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term333 _120120 _120196 x s t f op) = (term320 _120120 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5723495 _120120 _120196 s t f x op) (@lem5723478 _120120 _120196 s t f op x)). Qed.
Lemma lem5723559 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term332 _120120 _120196 x op f s t) = (term320 _120120 _120196 s t f x op).
Proof. exact (TRANS (@lem5723474 _120120 _120196 x s t f op) (@lem5723496 _120120 _120196 s t f x op)). Qed.
Lemma lem5723560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5723561 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term345 _120120 _120196 x op f s t) = (term346 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5723560) (@lem5723559 _120120 _120196 s t f x op)). Qed.
Lemma lem5723565 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem5720640 A s x t) (@lem5720639 A s t x)). Qed.
Lemma lem5723566 {_120120 : Type'} (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) : (term21 _120120 x s t) = (term22 _120120 s x t).
Proof. exact (@lem5723565 _120120 s x t). Qed.
Lemma lem5723567 {_120120 _120196 : Type'} (s : _120120 -> Prop) (x : _120120) (op : type1400 _120196) (f : _120120 -> _120196) (t : _120120 -> Prop) : (term347 _120120 _120196 x s op f t) = (term348 _120120 _120196 s x op f t).
Proof. exact (@lem5723566 _120120 (@support _120120 _120196 op f s) x (@support _120120 _120196 op f t)). Qed.
Lemma lem5723585 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5723586 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (@support _120120 _120196 op f s) = (term74 _120120 _120196 s f op).
Proof. exact (@lem5723585 _120120 _120196 s f op). Qed.
Lemma lem5723659 {_120120 : Type'} (x : _120120) : (@IN _120120 x) = (@IN _120120 x).
Proof. exact (eq_refl (@IN _120120 x)). Qed.
Lemma lem5723660 {_120120 _120196 : Type'} (x : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term153 _120120 _120196 x op f s) = (term154 _120120 _120196 x s f op).
Proof. exact (MK_COMB (@lem5723659 _120120 x) (@lem5723586 _120120 _120196 s f op)). Qed.
Lemma lem5723662 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5723663 {_120120 : Type'} (p : _120120 -> Prop) (x : _120120) : (term64 _120120 x p) = (p x).
Proof. exact (@lem5723662 _120120 p x). Qed.
Lemma lem5723664 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term155 _120120 _120196 x s f op) = (term156 _120120 _120196 s f op x).
Proof. exact (@lem5723663 _120120 (term157 _120120 _120196 s f op) x). Qed.
Lemma lem5723665 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term156 _120120 _120196 s f op x) = (term158 _120120 _120196 s f x op).
Proof. exact (eq_refl (term156 _120120 _120196 s f op x)). Qed.
Lemma lem5723666 {_120120 : Type'} (GEN_PVAR_237 : _120120) : (@SETSPEC _120120 GEN_PVAR_237) = (@SETSPEC _120120 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120120 GEN_PVAR_237)). Qed.
Lemma lem5723667 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term159 _120120 _120196 GEN_PVAR_237 s f op x) = (term160 _120120 _120196 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5723666 _120120 GEN_PVAR_237) (@lem5723665 _120120 _120196 s f x op)). Qed.
Lemma lem5723668 {_120120 : Type'} (x : _120120) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5723669 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term161 _120120 _120196 GEN_PVAR_237 s f op x) = (term162 _120120 _120196 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5723667 _120120 _120196 GEN_PVAR_237 s f x op) (@lem5723668 _120120 x)). Qed.
Lemma lem5723670 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term163 _120120 _120196 GEN_PVAR_237 s f op) = (term164 _120120 _120196 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _120120 => @lem5723669 _120120 _120196 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5723671 {_120120 : Type'} : (@ex _120120) = (@ex _120120).
Proof. exact (eq_refl (@ex _120120)). Qed.
Lemma lem5723672 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term165 _120120 _120196 GEN_PVAR_237 s f op) = (term166 _120120 _120196 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5723671 _120120) (@lem5723670 _120120 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5723673 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term167 _120120 _120196 s f op) = (term168 _120120 _120196 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120120 => @lem5723672 _120120 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5723674 {_120120 : Type'} : (@GSPEC _120120) = (@GSPEC _120120).
Proof. exact (eq_refl (@GSPEC _120120)). Qed.
Lemma lem5723675 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term169 _120120 _120196 s f op) = (term74 _120120 _120196 s f op).
Proof. exact (MK_COMB (@lem5723674 _120120) (@lem5723673 _120120 _120196 s f op)). Qed.
Lemma lem5723676 {_120120 : Type'} (x : _120120) : (@IN _120120 x) = (@IN _120120 x).
Proof. exact (eq_refl (@IN _120120 x)). Qed.
Lemma lem5723677 {_120120 _120196 : Type'} (x : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term155 _120120 _120196 x s f op) = (term154 _120120 _120196 x s f op).
Proof. exact (MK_COMB (@lem5723676 _120120 x) (@lem5723675 _120120 _120196 s f op)). Qed.
Lemma lem5723678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5723679 {_120120 _120196 : Type'} (x : _120120) (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term170 _120120 _120196 x s f op) = (term171 _120120 _120196 x s f op).
Proof. exact (MK_COMB (@lem5723678) (@lem5723677 _120120 _120196 x s f op)). Qed.
Lemma lem5723680 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term156 _120120 _120196 s f op x) = (term158 _120120 _120196 s f x op).
Proof. exact (eq_refl (term156 _120120 _120196 s f op x)). Qed.
Lemma lem5723681 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term155 _120120 _120196 x s f op) = (term156 _120120 _120196 s f op x)) = ((term154 _120120 _120196 x s f op) = (term158 _120120 _120196 s f x op)).
Proof. exact (MK_COMB (@lem5723679 _120120 _120196 x s f op) (@lem5723680 _120120 _120196 s f x op)). Qed.
Lemma lem5723682 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term154 _120120 _120196 x s f op) = (term158 _120120 _120196 s f x op).
Proof. exact (EQ_MP (@lem5723681 _120120 _120196 s f x op) (@lem5723664 _120120 _120196 s f op x)). Qed.
Lemma lem5723727 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term153 _120120 _120196 x op f s) = (term158 _120120 _120196 s f x op).
Proof. exact (TRANS (@lem5723660 _120120 _120196 x s f op) (@lem5723682 _120120 _120196 s f x op)). Qed.
Lemma lem5723728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5723729 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term236 _120120 _120196 x op f s) = (term237 _120120 _120196 s f x op).
Proof. exact (MK_COMB (@lem5723728) (@lem5723727 _120120 _120196 s f x op)). Qed.
Lemma lem5723741 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5723742 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (@support _120120 _120196 op f s) = (term74 _120120 _120196 s f op).
Proof. exact (@lem5723741 _120120 _120196 s f op). Qed.
Lemma lem5723743 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (@support _120120 _120196 op f t) = (term74 _120120 _120196 t f op).
Proof. exact (@lem5723742 _120120 _120196 t f op). Qed.
Lemma lem5723816 {_120120 : Type'} (x : _120120) : (@IN _120120 x) = (@IN _120120 x).
Proof. exact (eq_refl (@IN _120120 x)). Qed.
Lemma lem5723817 {_120120 _120196 : Type'} (x : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term153 _120120 _120196 x op f t) = (term154 _120120 _120196 x t f op).
Proof. exact (MK_COMB (@lem5723816 _120120 x) (@lem5723743 _120120 _120196 t f op)). Qed.
Lemma lem5723819 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5723820 {_120120 : Type'} (p : _120120 -> Prop) (x : _120120) : (term64 _120120 x p) = (p x).
Proof. exact (@lem5723819 _120120 p x). Qed.
Lemma lem5723821 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term155 _120120 _120196 x t f op) = (term156 _120120 _120196 t f op x).
Proof. exact (@lem5723820 _120120 (term157 _120120 _120196 t f op) x). Qed.
Lemma lem5723822 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term156 _120120 _120196 t f op x) = (term158 _120120 _120196 t f x op).
Proof. exact (eq_refl (term156 _120120 _120196 t f op x)). Qed.
Lemma lem5723823 {_120120 : Type'} (GEN_PVAR_237 : _120120) : (@SETSPEC _120120 GEN_PVAR_237) = (@SETSPEC _120120 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120120 GEN_PVAR_237)). Qed.
Lemma lem5723824 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term159 _120120 _120196 GEN_PVAR_237 t f op x) = (term160 _120120 _120196 GEN_PVAR_237 t f x op).
Proof. exact (MK_COMB (@lem5723823 _120120 GEN_PVAR_237) (@lem5723822 _120120 _120196 t f x op)). Qed.
Lemma lem5723825 {_120120 : Type'} (x : _120120) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5723826 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) (x : _120120) : (term161 _120120 _120196 GEN_PVAR_237 t f op x) = (term162 _120120 _120196 GEN_PVAR_237 t f op x).
Proof. exact (MK_COMB (@lem5723824 _120120 _120196 GEN_PVAR_237 t f x op) (@lem5723825 _120120 x)). Qed.
Lemma lem5723827 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term163 _120120 _120196 GEN_PVAR_237 t f op) = (term164 _120120 _120196 GEN_PVAR_237 t f op).
Proof. exact (fun_ext (fun x : _120120 => @lem5723826 _120120 _120196 GEN_PVAR_237 t f op x)). Qed.
Lemma lem5723828 {_120120 : Type'} : (@ex _120120) = (@ex _120120).
Proof. exact (eq_refl (@ex _120120)). Qed.
Lemma lem5723829 {_120120 _120196 : Type'} (GEN_PVAR_237 : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term165 _120120 _120196 GEN_PVAR_237 t f op) = (term166 _120120 _120196 GEN_PVAR_237 t f op).
Proof. exact (MK_COMB (@lem5723828 _120120) (@lem5723827 _120120 _120196 GEN_PVAR_237 t f op)). Qed.
Lemma lem5723830 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term167 _120120 _120196 t f op) = (term168 _120120 _120196 t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120120 => @lem5723829 _120120 _120196 GEN_PVAR_237 t f op)). Qed.
Lemma lem5723831 {_120120 : Type'} : (@GSPEC _120120) = (@GSPEC _120120).
Proof. exact (eq_refl (@GSPEC _120120)). Qed.
Lemma lem5723832 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term169 _120120 _120196 t f op) = (term74 _120120 _120196 t f op).
Proof. exact (MK_COMB (@lem5723831 _120120) (@lem5723830 _120120 _120196 t f op)). Qed.
Lemma lem5723833 {_120120 : Type'} (x : _120120) : (@IN _120120 x) = (@IN _120120 x).
Proof. exact (eq_refl (@IN _120120 x)). Qed.
Lemma lem5723834 {_120120 _120196 : Type'} (x : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term155 _120120 _120196 x t f op) = (term154 _120120 _120196 x t f op).
Proof. exact (MK_COMB (@lem5723833 _120120 x) (@lem5723832 _120120 _120196 t f op)). Qed.
Lemma lem5723835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5723836 {_120120 _120196 : Type'} (x : _120120) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term170 _120120 _120196 x t f op) = (term171 _120120 _120196 x t f op).
Proof. exact (MK_COMB (@lem5723835) (@lem5723834 _120120 _120196 x t f op)). Qed.
Lemma lem5723837 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term156 _120120 _120196 t f op x) = (term158 _120120 _120196 t f x op).
Proof. exact (eq_refl (term156 _120120 _120196 t f op x)). Qed.
Lemma lem5723838 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term155 _120120 _120196 x t f op) = (term156 _120120 _120196 t f op x)) = ((term154 _120120 _120196 x t f op) = (term158 _120120 _120196 t f x op)).
Proof. exact (MK_COMB (@lem5723836 _120120 _120196 x t f op) (@lem5723837 _120120 _120196 t f x op)). Qed.
Lemma lem5723839 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term154 _120120 _120196 x t f op) = (term158 _120120 _120196 t f x op).
Proof. exact (EQ_MP (@lem5723838 _120120 _120196 t f x op) (@lem5723821 _120120 _120196 t f op x)). Qed.
Lemma lem5723884 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term153 _120120 _120196 x op f t) = (term158 _120120 _120196 t f x op).
Proof. exact (TRANS (@lem5723817 _120120 _120196 x t f op) (@lem5723839 _120120 _120196 t f x op)). Qed.
Lemma lem5723885 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term348 _120120 _120196 s x op f t) = (term349 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5723729 _120120 _120196 s f x op) (@lem5723884 _120120 _120196 t f x op)). Qed.
Lemma lem5723890 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term347 _120120 _120196 x s op f t) = (term349 _120120 _120196 s t f x op).
Proof. exact (TRANS (@lem5723567 _120120 _120196 s x op f t) (@lem5723885 _120120 _120196 s t f x op)). Qed.
Lemma lem5723891 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term332 _120120 _120196 x op f s t) = (term347 _120120 _120196 x s op f t)) = ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)).
Proof. exact (MK_COMB (@lem5723561 _120120 _120196 s t f x op) (@lem5723890 _120120 _120196 s t f x op)). Qed.
Lemma lem5723898 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term350 _120120 _120196 s op f t) = (term351 _120120 _120196 s t f op).
Proof. exact (fun_ext (fun x : _120120 => @lem5723891 _120120 _120196 s t f x op)). Qed.
Lemma lem5723901 {_120120 : Type'} : (@all _120120) = (@all _120120).
Proof. exact (eq_refl (@all _120120)). Qed.
Lemma lem5723902 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term315 _120120 _120196 s op f t) = (term352 _120120 _120196 s t f op).
Proof. exact (MK_COMB (@lem5723901 _120120) (@lem5723898 _120120 _120196 s t f op)). Qed.
Lemma lem5723909 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : ((term313 _120120 _120196 op f s t) = (term314 _120120 _120196 s op f t)) = (term352 _120120 _120196 s t f op).
Proof. exact (TRANS (@lem5723310 _120120 _120196 s op f t) (@lem5723902 _120120 _120196 s t f op)). Qed.
Lemma lem5723910 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term353 _120120 _120196 s op f) = (term354 _120120 _120196 s f op).
Proof. exact (fun_ext (fun t : _120120 -> Prop => @lem5723909 _120120 _120196 s t f op)). Qed.
Lemma lem5723913 {_120120 : Type'} : (@all (_120120 -> Prop)) = (@all (_120120 -> Prop)).
Proof. exact (eq_refl (@all (_120120 -> Prop))). Qed.
Lemma lem5723914 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : (term355 _120120 _120196 s op f) = (term356 _120120 _120196 s f op).
Proof. exact (MK_COMB (@lem5723913 _120120) (@lem5723910 _120120 _120196 s f op)). Qed.
Lemma lem5723921 {_120120 _120196 : Type'} (f : _120120 -> _120196) (op : type1400 _120196) : (term357 _120120 _120196 op f) = (term358 _120120 _120196 f op).
Proof. exact (fun_ext (fun s : _120120 -> Prop => @lem5723914 _120120 _120196 s f op)). Qed.
Lemma lem5723924 {_120120 : Type'} : (@all (_120120 -> Prop)) = (@all (_120120 -> Prop)).
Proof. exact (eq_refl (@all (_120120 -> Prop))). Qed.
Lemma lem5723925 {_120120 _120196 : Type'} (f : _120120 -> _120196) (op : type1400 _120196) : (term359 _120120 _120196 op f) = (term360 _120120 _120196 f op).
Proof. exact (MK_COMB (@lem5723924 _120120) (@lem5723921 _120120 _120196 f op)). Qed.
Lemma lem5723932 {_120120 _120196 : Type'} (op : type1400 _120196) : (term361 _120120 _120196 op) = (term362 _120120 _120196 op).
Proof. exact (fun_ext (fun f : _120120 -> _120196 => @lem5723925 _120120 _120196 f op)). Qed.
Lemma lem5723935 {_120120 _120196 : Type'} : (@all (_120120 -> _120196)) = (@all (_120120 -> _120196)).
Proof. exact (eq_refl (@all (_120120 -> _120196))). Qed.
Lemma lem5723936 {_120120 _120196 : Type'} (op : type1400 _120196) : (term363 _120120 _120196 op) = (term364 _120120 _120196 op).
Proof. exact (MK_COMB (@lem5723935 _120120 _120196) (@lem5723932 _120120 _120196 op)). Qed.
Lemma lem5723943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5723944 {_120120 _120196 : Type'} (op : type1400 _120196) : (term365 _120120 _120196 op) = (term366 _120120 _120196 op).
Proof. exact (MK_COMB (@lem5723943) (@lem5723936 _120120 _120196 op)). Qed.
Lemma lem5723988 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5723989 {_120158 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) : (s = t) = (term68 _120158 s t).
Proof. exact (@lem5723988 _120158 s t). Qed.
Lemma lem5723990 {_120158 _120196 : Type'} (s : _120158 -> Prop) (op : type1400 _120196) (f : _120158 -> _120196) (t : _120158 -> Prop) : ((term367 _120158 _120196 op f s t) = (term368 _120158 _120196 s op f t)) = (term369 _120158 _120196 s op f t).
Proof. exact (@lem5723989 _120158 (term367 _120158 _120196 op f s t) (term368 _120158 _120196 s op f t)). Qed.
Lemma lem5724020 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5724021 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (@support _120158 _120196 op f s) = (term74 _120158 _120196 s f op).
Proof. exact (@lem5724020 _120158 _120196 s f op). Qed.
Lemma lem5724022 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term367 _120158 _120196 op f s t) = (term370 _120158 _120196 s t f op).
Proof. exact (@lem5724021 _120158 _120196 (@DIFF _120158 s t) f op). Qed.
Lemma lem5724058 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem5720631 A s x t) (@lem5720630 A s t x)). Qed.
Lemma lem5724059 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term14 _120158 x s t) = (term15 _120158 s x t).
Proof. exact (@lem5724058 _120158 s x t). Qed.
Lemma lem5724092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5724093 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term371 _120158 x s t) = (term372 _120158 s x t).
Proof. exact (MK_COMB (@lem5724092) (@lem5724059 _120158 s x t)). Qed.
Lemma lem5724122 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term78 _120158 _120196 f x op) = (term78 _120158 _120196 f x op).
Proof. exact (eq_refl (term78 _120158 _120196 f x op)). Qed.
Lemma lem5724123 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term373 _120158 _120196 s t f x op) = (term374 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5724093 _120158 s x t) (@lem5724122 _120158 _120196 f x op)). Qed.
Lemma lem5724128 {_120158 : Type'} (GEN_PVAR_237 : _120158) : (@SETSPEC _120158 GEN_PVAR_237) = (@SETSPEC _120158 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120158 GEN_PVAR_237)). Qed.
Lemma lem5724129 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term375 _120158 _120196 GEN_PVAR_237 s t f x op) = (term376 _120158 _120196 GEN_PVAR_237 s t f x op).
Proof. exact (MK_COMB (@lem5724128 _120158 GEN_PVAR_237) (@lem5724123 _120158 _120196 s t f x op)). Qed.
Lemma lem5724134 {_120158 : Type'} (x : _120158) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5724135 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term377 _120158 _120196 GEN_PVAR_237 s t f op x) = (term378 _120158 _120196 GEN_PVAR_237 s t f op x).
Proof. exact (MK_COMB (@lem5724129 _120158 _120196 GEN_PVAR_237 s t f x op) (@lem5724134 _120158 x)). Qed.
Lemma lem5724138 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term379 _120158 _120196 GEN_PVAR_237 s t f op) = (term380 _120158 _120196 GEN_PVAR_237 s t f op).
Proof. exact (fun_ext (fun x : _120158 => @lem5724135 _120158 _120196 GEN_PVAR_237 s t f op x)). Qed.
Lemma lem5724141 {_120158 : Type'} : (@ex _120158) = (@ex _120158).
Proof. exact (eq_refl (@ex _120158)). Qed.
Lemma lem5724142 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term381 _120158 _120196 GEN_PVAR_237 s t f op) = (term382 _120158 _120196 GEN_PVAR_237 s t f op).
Proof. exact (MK_COMB (@lem5724141 _120158) (@lem5724138 _120158 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5724149 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term383 _120158 _120196 s t f op) = (term384 _120158 _120196 s t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120158 => @lem5724142 _120158 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5724152 {_120158 : Type'} : (@GSPEC _120158) = (@GSPEC _120158).
Proof. exact (eq_refl (@GSPEC _120158)). Qed.
Lemma lem5724153 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term370 _120158 _120196 s t f op) = (term385 _120158 _120196 s t f op).
Proof. exact (MK_COMB (@lem5724152 _120158) (@lem5724149 _120158 _120196 s t f op)). Qed.
Lemma lem5724156 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term367 _120158 _120196 op f s t) = (term385 _120158 _120196 s t f op).
Proof. exact (TRANS (@lem5724022 _120158 _120196 s t f op) (@lem5724153 _120158 _120196 s t f op)). Qed.
Lemma lem5724157 {_120158 : Type'} (x : _120158) : (@IN _120158 x) = (@IN _120158 x).
Proof. exact (eq_refl (@IN _120158 x)). Qed.
Lemma lem5724158 {_120158 _120196 : Type'} (x : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term386 _120158 _120196 x op f s t) = (term387 _120158 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5724157 _120158 x) (@lem5724156 _120158 _120196 s t f op)). Qed.
Lemma lem5724160 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5724161 {_120158 : Type'} (p : _120158 -> Prop) (x : _120158) : (term64 _120158 x p) = (p x).
Proof. exact (@lem5724160 _120158 p x). Qed.
Lemma lem5724162 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term388 _120158 _120196 x s t f op) = (term389 _120158 _120196 s t f op x).
Proof. exact (@lem5724161 _120158 (term390 _120158 _120196 s t f op) x). Qed.
Lemma lem5724163 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term389 _120158 _120196 s t f op x) = (term374 _120158 _120196 s t f x op).
Proof. exact (eq_refl (term389 _120158 _120196 s t f op x)). Qed.
Lemma lem5724164 {_120158 : Type'} (GEN_PVAR_237 : _120158) : (@SETSPEC _120158 GEN_PVAR_237) = (@SETSPEC _120158 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120158 GEN_PVAR_237)). Qed.
Lemma lem5724165 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term391 _120158 _120196 GEN_PVAR_237 s t f op x) = (term376 _120158 _120196 GEN_PVAR_237 s t f x op).
Proof. exact (MK_COMB (@lem5724164 _120158 GEN_PVAR_237) (@lem5724163 _120158 _120196 s t f x op)). Qed.
Lemma lem5724166 {_120158 : Type'} (x : _120158) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5724167 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term392 _120158 _120196 GEN_PVAR_237 s t f op x) = (term378 _120158 _120196 GEN_PVAR_237 s t f op x).
Proof. exact (MK_COMB (@lem5724165 _120158 _120196 GEN_PVAR_237 s t f x op) (@lem5724166 _120158 x)). Qed.
Lemma lem5724168 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term393 _120158 _120196 GEN_PVAR_237 s t f op) = (term380 _120158 _120196 GEN_PVAR_237 s t f op).
Proof. exact (fun_ext (fun x : _120158 => @lem5724167 _120158 _120196 GEN_PVAR_237 s t f op x)). Qed.
Lemma lem5724169 {_120158 : Type'} : (@ex _120158) = (@ex _120158).
Proof. exact (eq_refl (@ex _120158)). Qed.
Lemma lem5724170 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term394 _120158 _120196 GEN_PVAR_237 s t f op) = (term382 _120158 _120196 GEN_PVAR_237 s t f op).
Proof. exact (MK_COMB (@lem5724169 _120158) (@lem5724168 _120158 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5724171 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term395 _120158 _120196 s t f op) = (term384 _120158 _120196 s t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120158 => @lem5724170 _120158 _120196 GEN_PVAR_237 s t f op)). Qed.
Lemma lem5724172 {_120158 : Type'} : (@GSPEC _120158) = (@GSPEC _120158).
Proof. exact (eq_refl (@GSPEC _120158)). Qed.
Lemma lem5724173 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term396 _120158 _120196 s t f op) = (term385 _120158 _120196 s t f op).
Proof. exact (MK_COMB (@lem5724172 _120158) (@lem5724171 _120158 _120196 s t f op)). Qed.
Lemma lem5724174 {_120158 : Type'} (x : _120158) : (@IN _120158 x) = (@IN _120158 x).
Proof. exact (eq_refl (@IN _120158 x)). Qed.
Lemma lem5724175 {_120158 _120196 : Type'} (x : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term388 _120158 _120196 x s t f op) = (term387 _120158 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5724174 _120158 x) (@lem5724173 _120158 _120196 s t f op)). Qed.
Lemma lem5724176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5724177 {_120158 _120196 : Type'} (x : _120158) (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term397 _120158 _120196 x s t f op) = (term398 _120158 _120196 x s t f op).
Proof. exact (MK_COMB (@lem5724176) (@lem5724175 _120158 _120196 x s t f op)). Qed.
Lemma lem5724178 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term389 _120158 _120196 s t f op x) = (term374 _120158 _120196 s t f x op).
Proof. exact (eq_refl (term389 _120158 _120196 s t f op x)). Qed.
Lemma lem5724179 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term388 _120158 _120196 x s t f op) = (term389 _120158 _120196 s t f op x)) = ((term387 _120158 _120196 x s t f op) = (term374 _120158 _120196 s t f x op)).
Proof. exact (MK_COMB (@lem5724177 _120158 _120196 x s t f op) (@lem5724178 _120158 _120196 s t f x op)). Qed.
Lemma lem5724180 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term387 _120158 _120196 x s t f op) = (term374 _120158 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5724179 _120158 _120196 s t f x op) (@lem5724162 _120158 _120196 s t f op x)). Qed.
Lemma lem5724247 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term386 _120158 _120196 x op f s t) = (term374 _120158 _120196 s t f x op).
Proof. exact (TRANS (@lem5724158 _120158 _120196 x s t f op) (@lem5724180 _120158 _120196 s t f x op)). Qed.
Lemma lem5724248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5724249 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term399 _120158 _120196 x op f s t) = (term400 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5724248) (@lem5724247 _120158 _120196 s t f x op)). Qed.
Lemma lem5724253 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem5720631 A s x t) (@lem5720630 A s t x)). Qed.
Lemma lem5724254 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term14 _120158 x s t) = (term15 _120158 s x t).
Proof. exact (@lem5724253 _120158 s x t). Qed.
Lemma lem5724255 {_120158 _120196 : Type'} (s : _120158 -> Prop) (x : _120158) (op : type1400 _120196) (f : _120158 -> _120196) (t : _120158 -> Prop) : (term401 _120158 _120196 x s op f t) = (term402 _120158 _120196 s x op f t).
Proof. exact (@lem5724254 _120158 (@support _120158 _120196 op f s) x (@support _120158 _120196 op f t)). Qed.
Lemma lem5724273 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5724274 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (@support _120158 _120196 op f s) = (term74 _120158 _120196 s f op).
Proof. exact (@lem5724273 _120158 _120196 s f op). Qed.
Lemma lem5724347 {_120158 : Type'} (x : _120158) : (@IN _120158 x) = (@IN _120158 x).
Proof. exact (eq_refl (@IN _120158 x)). Qed.
Lemma lem5724348 {_120158 _120196 : Type'} (x : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term153 _120158 _120196 x op f s) = (term154 _120158 _120196 x s f op).
Proof. exact (MK_COMB (@lem5724347 _120158 x) (@lem5724274 _120158 _120196 s f op)). Qed.
Lemma lem5724350 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5724351 {_120158 : Type'} (p : _120158 -> Prop) (x : _120158) : (term64 _120158 x p) = (p x).
Proof. exact (@lem5724350 _120158 p x). Qed.
Lemma lem5724352 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term155 _120158 _120196 x s f op) = (term156 _120158 _120196 s f op x).
Proof. exact (@lem5724351 _120158 (term157 _120158 _120196 s f op) x). Qed.
Lemma lem5724353 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term156 _120158 _120196 s f op x) = (term158 _120158 _120196 s f x op).
Proof. exact (eq_refl (term156 _120158 _120196 s f op x)). Qed.
Lemma lem5724354 {_120158 : Type'} (GEN_PVAR_237 : _120158) : (@SETSPEC _120158 GEN_PVAR_237) = (@SETSPEC _120158 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120158 GEN_PVAR_237)). Qed.
Lemma lem5724355 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term159 _120158 _120196 GEN_PVAR_237 s f op x) = (term160 _120158 _120196 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5724354 _120158 GEN_PVAR_237) (@lem5724353 _120158 _120196 s f x op)). Qed.
Lemma lem5724356 {_120158 : Type'} (x : _120158) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5724357 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term161 _120158 _120196 GEN_PVAR_237 s f op x) = (term162 _120158 _120196 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5724355 _120158 _120196 GEN_PVAR_237 s f x op) (@lem5724356 _120158 x)). Qed.
Lemma lem5724358 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term163 _120158 _120196 GEN_PVAR_237 s f op) = (term164 _120158 _120196 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _120158 => @lem5724357 _120158 _120196 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5724359 {_120158 : Type'} : (@ex _120158) = (@ex _120158).
Proof. exact (eq_refl (@ex _120158)). Qed.
Lemma lem5724360 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term165 _120158 _120196 GEN_PVAR_237 s f op) = (term166 _120158 _120196 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5724359 _120158) (@lem5724358 _120158 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5724361 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term167 _120158 _120196 s f op) = (term168 _120158 _120196 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120158 => @lem5724360 _120158 _120196 GEN_PVAR_237 s f op)). Qed.
Lemma lem5724362 {_120158 : Type'} : (@GSPEC _120158) = (@GSPEC _120158).
Proof. exact (eq_refl (@GSPEC _120158)). Qed.
Lemma lem5724363 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term169 _120158 _120196 s f op) = (term74 _120158 _120196 s f op).
Proof. exact (MK_COMB (@lem5724362 _120158) (@lem5724361 _120158 _120196 s f op)). Qed.
Lemma lem5724364 {_120158 : Type'} (x : _120158) : (@IN _120158 x) = (@IN _120158 x).
Proof. exact (eq_refl (@IN _120158 x)). Qed.
Lemma lem5724365 {_120158 _120196 : Type'} (x : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term155 _120158 _120196 x s f op) = (term154 _120158 _120196 x s f op).
Proof. exact (MK_COMB (@lem5724364 _120158 x) (@lem5724363 _120158 _120196 s f op)). Qed.
Lemma lem5724366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5724367 {_120158 _120196 : Type'} (x : _120158) (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term170 _120158 _120196 x s f op) = (term171 _120158 _120196 x s f op).
Proof. exact (MK_COMB (@lem5724366) (@lem5724365 _120158 _120196 x s f op)). Qed.
Lemma lem5724368 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term156 _120158 _120196 s f op x) = (term158 _120158 _120196 s f x op).
Proof. exact (eq_refl (term156 _120158 _120196 s f op x)). Qed.
Lemma lem5724369 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term155 _120158 _120196 x s f op) = (term156 _120158 _120196 s f op x)) = ((term154 _120158 _120196 x s f op) = (term158 _120158 _120196 s f x op)).
Proof. exact (MK_COMB (@lem5724367 _120158 _120196 x s f op) (@lem5724368 _120158 _120196 s f x op)). Qed.
Lemma lem5724370 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term154 _120158 _120196 x s f op) = (term158 _120158 _120196 s f x op).
Proof. exact (EQ_MP (@lem5724369 _120158 _120196 s f x op) (@lem5724352 _120158 _120196 s f op x)). Qed.
Lemma lem5724415 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term153 _120158 _120196 x op f s) = (term158 _120158 _120196 s f x op).
Proof. exact (TRANS (@lem5724348 _120158 _120196 x s f op) (@lem5724370 _120158 _120196 s f x op)). Qed.
Lemma lem5724416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5724417 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term236 _120158 _120196 x op f s) = (term237 _120158 _120196 s f x op).
Proof. exact (MK_COMB (@lem5724416) (@lem5724415 _120158 _120196 s f x op)). Qed.
Lemma lem5724433 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5724434 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (@support _120158 _120196 op f s) = (term74 _120158 _120196 s f op).
Proof. exact (@lem5724433 _120158 _120196 s f op). Qed.
Lemma lem5724435 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (@support _120158 _120196 op f t) = (term74 _120158 _120196 t f op).
Proof. exact (@lem5724434 _120158 _120196 t f op). Qed.
Lemma lem5724508 {_120158 : Type'} (x : _120158) : (@IN _120158 x) = (@IN _120158 x).
Proof. exact (eq_refl (@IN _120158 x)). Qed.
Lemma lem5724509 {_120158 _120196 : Type'} (x : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term153 _120158 _120196 x op f t) = (term154 _120158 _120196 x t f op).
Proof. exact (MK_COMB (@lem5724508 _120158 x) (@lem5724435 _120158 _120196 t f op)). Qed.
Lemma lem5724511 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5724512 {_120158 : Type'} (p : _120158 -> Prop) (x : _120158) : (term64 _120158 x p) = (p x).
Proof. exact (@lem5724511 _120158 p x). Qed.
Lemma lem5724513 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term155 _120158 _120196 x t f op) = (term156 _120158 _120196 t f op x).
Proof. exact (@lem5724512 _120158 (term157 _120158 _120196 t f op) x). Qed.
Lemma lem5724514 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term156 _120158 _120196 t f op x) = (term158 _120158 _120196 t f x op).
Proof. exact (eq_refl (term156 _120158 _120196 t f op x)). Qed.
Lemma lem5724515 {_120158 : Type'} (GEN_PVAR_237 : _120158) : (@SETSPEC _120158 GEN_PVAR_237) = (@SETSPEC _120158 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120158 GEN_PVAR_237)). Qed.
Lemma lem5724516 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term159 _120158 _120196 GEN_PVAR_237 t f op x) = (term160 _120158 _120196 GEN_PVAR_237 t f x op).
Proof. exact (MK_COMB (@lem5724515 _120158 GEN_PVAR_237) (@lem5724514 _120158 _120196 t f x op)). Qed.
Lemma lem5724517 {_120158 : Type'} (x : _120158) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5724518 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) (x : _120158) : (term161 _120158 _120196 GEN_PVAR_237 t f op x) = (term162 _120158 _120196 GEN_PVAR_237 t f op x).
Proof. exact (MK_COMB (@lem5724516 _120158 _120196 GEN_PVAR_237 t f x op) (@lem5724517 _120158 x)). Qed.
Lemma lem5724519 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term163 _120158 _120196 GEN_PVAR_237 t f op) = (term164 _120158 _120196 GEN_PVAR_237 t f op).
Proof. exact (fun_ext (fun x : _120158 => @lem5724518 _120158 _120196 GEN_PVAR_237 t f op x)). Qed.
Lemma lem5724520 {_120158 : Type'} : (@ex _120158) = (@ex _120158).
Proof. exact (eq_refl (@ex _120158)). Qed.
Lemma lem5724521 {_120158 _120196 : Type'} (GEN_PVAR_237 : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term165 _120158 _120196 GEN_PVAR_237 t f op) = (term166 _120158 _120196 GEN_PVAR_237 t f op).
Proof. exact (MK_COMB (@lem5724520 _120158) (@lem5724519 _120158 _120196 GEN_PVAR_237 t f op)). Qed.
Lemma lem5724522 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term167 _120158 _120196 t f op) = (term168 _120158 _120196 t f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120158 => @lem5724521 _120158 _120196 GEN_PVAR_237 t f op)). Qed.
Lemma lem5724523 {_120158 : Type'} : (@GSPEC _120158) = (@GSPEC _120158).
Proof. exact (eq_refl (@GSPEC _120158)). Qed.
Lemma lem5724524 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term169 _120158 _120196 t f op) = (term74 _120158 _120196 t f op).
Proof. exact (MK_COMB (@lem5724523 _120158) (@lem5724522 _120158 _120196 t f op)). Qed.
Lemma lem5724525 {_120158 : Type'} (x : _120158) : (@IN _120158 x) = (@IN _120158 x).
Proof. exact (eq_refl (@IN _120158 x)). Qed.
Lemma lem5724526 {_120158 _120196 : Type'} (x : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term155 _120158 _120196 x t f op) = (term154 _120158 _120196 x t f op).
Proof. exact (MK_COMB (@lem5724525 _120158 x) (@lem5724524 _120158 _120196 t f op)). Qed.
Lemma lem5724527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5724528 {_120158 _120196 : Type'} (x : _120158) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term170 _120158 _120196 x t f op) = (term171 _120158 _120196 x t f op).
Proof. exact (MK_COMB (@lem5724527) (@lem5724526 _120158 _120196 x t f op)). Qed.
Lemma lem5724529 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term156 _120158 _120196 t f op x) = (term158 _120158 _120196 t f x op).
Proof. exact (eq_refl (term156 _120158 _120196 t f op x)). Qed.
Lemma lem5724530 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term155 _120158 _120196 x t f op) = (term156 _120158 _120196 t f op x)) = ((term154 _120158 _120196 x t f op) = (term158 _120158 _120196 t f x op)).
Proof. exact (MK_COMB (@lem5724528 _120158 _120196 x t f op) (@lem5724529 _120158 _120196 t f x op)). Qed.
Lemma lem5724531 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term154 _120158 _120196 x t f op) = (term158 _120158 _120196 t f x op).
Proof. exact (EQ_MP (@lem5724530 _120158 _120196 t f x op) (@lem5724513 _120158 _120196 t f op x)). Qed.
Lemma lem5724576 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term153 _120158 _120196 x op f t) = (term158 _120158 _120196 t f x op).
Proof. exact (TRANS (@lem5724509 _120158 _120196 x t f op) (@lem5724531 _120158 _120196 t f x op)). Qed.
Lemma lem5724577 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5724578 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term403 _120158 _120196 x op f t) = (term404 _120158 _120196 t f x op).
Proof. exact (MK_COMB (@lem5724577) (@lem5724576 _120158 _120196 t f x op)). Qed.
Lemma lem5724581 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term402 _120158 _120196 s x op f t) = (term405 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5724417 _120158 _120196 s f x op) (@lem5724578 _120158 _120196 t f x op)). Qed.
Lemma lem5724586 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term401 _120158 _120196 x s op f t) = (term405 _120158 _120196 s t f x op).
Proof. exact (TRANS (@lem5724255 _120158 _120196 s x op f t) (@lem5724581 _120158 _120196 s t f x op)). Qed.
Lemma lem5724587 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term386 _120158 _120196 x op f s t) = (term401 _120158 _120196 x s op f t)) = ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)).
Proof. exact (MK_COMB (@lem5724249 _120158 _120196 s t f x op) (@lem5724586 _120158 _120196 s t f x op)). Qed.
Lemma lem5724594 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term406 _120158 _120196 s op f t) = (term407 _120158 _120196 s t f op).
Proof. exact (fun_ext (fun x : _120158 => @lem5724587 _120158 _120196 s t f x op)). Qed.
Lemma lem5724597 {_120158 : Type'} : (@all _120158) = (@all _120158).
Proof. exact (eq_refl (@all _120158)). Qed.
Lemma lem5724598 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term369 _120158 _120196 s op f t) = (term408 _120158 _120196 s t f op).
Proof. exact (MK_COMB (@lem5724597 _120158) (@lem5724594 _120158 _120196 s t f op)). Qed.
Lemma lem5724605 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : ((term367 _120158 _120196 op f s t) = (term368 _120158 _120196 s op f t)) = (term408 _120158 _120196 s t f op).
Proof. exact (TRANS (@lem5723990 _120158 _120196 s op f t) (@lem5724598 _120158 _120196 s t f op)). Qed.
Lemma lem5724606 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term409 _120158 _120196 s op f) = (term410 _120158 _120196 s f op).
Proof. exact (fun_ext (fun t : _120158 -> Prop => @lem5724605 _120158 _120196 s t f op)). Qed.
Lemma lem5724609 {_120158 : Type'} : (@all (_120158 -> Prop)) = (@all (_120158 -> Prop)).
Proof. exact (eq_refl (@all (_120158 -> Prop))). Qed.
Lemma lem5724610 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : (term411 _120158 _120196 s op f) = (term412 _120158 _120196 s f op).
Proof. exact (MK_COMB (@lem5724609 _120158) (@lem5724606 _120158 _120196 s f op)). Qed.
Lemma lem5724617 {_120158 _120196 : Type'} (f : _120158 -> _120196) (op : type1400 _120196) : (term413 _120158 _120196 op f) = (term414 _120158 _120196 f op).
Proof. exact (fun_ext (fun s : _120158 -> Prop => @lem5724610 _120158 _120196 s f op)). Qed.
Lemma lem5724620 {_120158 : Type'} : (@all (_120158 -> Prop)) = (@all (_120158 -> Prop)).
Proof. exact (eq_refl (@all (_120158 -> Prop))). Qed.
Lemma lem5724621 {_120158 _120196 : Type'} (f : _120158 -> _120196) (op : type1400 _120196) : (term415 _120158 _120196 op f) = (term416 _120158 _120196 f op).
Proof. exact (MK_COMB (@lem5724620 _120158) (@lem5724617 _120158 _120196 f op)). Qed.
Lemma lem5724628 {_120158 _120196 : Type'} (op : type1400 _120196) : (term417 _120158 _120196 op) = (term418 _120158 _120196 op).
Proof. exact (fun_ext (fun f : _120158 -> _120196 => @lem5724621 _120158 _120196 f op)). Qed.
Lemma lem5724631 {_120158 _120196 : Type'} : (@all (_120158 -> _120196)) = (@all (_120158 -> _120196)).
Proof. exact (eq_refl (@all (_120158 -> _120196))). Qed.
Lemma lem5724632 {_120158 _120196 : Type'} (op : type1400 _120196) : (term419 _120158 _120196 op) = (term420 _120158 _120196 op).
Proof. exact (MK_COMB (@lem5724631 _120158 _120196) (@lem5724628 _120158 _120196 op)). Qed.
Lemma lem5724639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5724640 {_120158 _120196 : Type'} (op : type1400 _120196) : (term421 _120158 _120196 op) = (term422 _120158 _120196 op).
Proof. exact (MK_COMB (@lem5724639) (@lem5724632 _120158 _120196 op)). Qed.
Lemma lem5724676 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term68 A s t).
Proof. exact (EQ_MP (@lem5720734 A s t) (@lem5720733 A s t)). Qed.
Lemma lem5724677 {_120186 : Type'} (s : _120186 -> Prop) (t : _120186 -> Prop) : (s = t) = (term68 _120186 s t).
Proof. exact (@lem5724676 _120186 s t). Qed.
Lemma lem5724678 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) (g : _120186 -> _120196) (f : _120195 -> _120186) (s : _120195 -> Prop) : ((term423 _120186 _120195 _120196 op g f s) = (term424 _120186 _120195 _120196 op g f s)) = (term425 _120186 _120195 _120196 op g f s).
Proof. exact (@lem5724677 _120186 (term423 _120186 _120195 _120196 op g f s) (term424 _120186 _120195 _120196 op g f s)). Qed.
Lemma lem5724708 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5724709 {_120186 _120196 : Type'} (s : _120186 -> Prop) (f : _120186 -> _120196) (op : type1400 _120196) : (@support _120186 _120196 op f s) = (term74 _120186 _120196 s f op).
Proof. exact (@lem5724708 _120186 _120196 s f op). Qed.
Lemma lem5724710 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term423 _120186 _120195 _120196 op g f s) = (term426 _120186 _120195 _120196 f s g op).
Proof. exact (@lem5724709 _120186 _120196 (@IMAGE _120195 _120186 f s) g op). Qed.
Lemma lem5724746 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term38 A B y f s) = (term39 A B y f s).
Proof. exact (EQ_MP (@lem5720663 A B y f s) (@lem5720662 A B y s f)). Qed.
Lemma lem5724747 {_120186 _120195 : Type'} (y : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term427 _120186 _120195 y f s) = (term428 _120186 _120195 y f s).
Proof. exact (@lem5724746 _120195 _120186 y f s). Qed.
Lemma lem5724748 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term427 _120186 _120195 x f s) = (term428 _120186 _120195 x f s).
Proof. exact (@lem5724747 _120186 _120195 x f s). Qed.
Lemma lem5724795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5724796 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term429 _120186 _120195 x f s) = (term430 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5724795) (@lem5724748 _120186 _120195 x f s)). Qed.
Lemma lem5724825 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term78 _120186 _120196 g x op) = (term78 _120186 _120196 g x op).
Proof. exact (eq_refl (term78 _120186 _120196 g x op)). Qed.
Lemma lem5724826 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term431 _120186 _120195 _120196 f s g x op) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5724796 _120186 _120195 x f s) (@lem5724825 _120186 _120196 g x op)). Qed.
Lemma lem5724831 {_120186 : Type'} (GEN_PVAR_237 : _120186) : (@SETSPEC _120186 GEN_PVAR_237) = (@SETSPEC _120186 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120186 GEN_PVAR_237)). Qed.
Lemma lem5724832 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term433 _120186 _120195 _120196 GEN_PVAR_237 f s g x op) = (term434 _120186 _120195 _120196 GEN_PVAR_237 f s g x op).
Proof. exact (MK_COMB (@lem5724831 _120186 GEN_PVAR_237) (@lem5724826 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5724837 {_120186 : Type'} (x : _120186) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5724838 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) (x : _120186) : (term435 _120186 _120195 _120196 GEN_PVAR_237 f s g op x) = (term436 _120186 _120195 _120196 GEN_PVAR_237 f s g op x).
Proof. exact (MK_COMB (@lem5724832 _120186 _120195 _120196 GEN_PVAR_237 f s g x op) (@lem5724837 _120186 x)). Qed.
Lemma lem5724841 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term437 _120186 _120195 _120196 GEN_PVAR_237 f s g op) = (term438 _120186 _120195 _120196 GEN_PVAR_237 f s g op).
Proof. exact (fun_ext (fun x : _120186 => @lem5724838 _120186 _120195 _120196 GEN_PVAR_237 f s g op x)). Qed.
Lemma lem5724844 {_120186 : Type'} : (@ex _120186) = (@ex _120186).
Proof. exact (eq_refl (@ex _120186)). Qed.
Lemma lem5724845 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term439 _120186 _120195 _120196 GEN_PVAR_237 f s g op) = (term440 _120186 _120195 _120196 GEN_PVAR_237 f s g op).
Proof. exact (MK_COMB (@lem5724844 _120186) (@lem5724841 _120186 _120195 _120196 GEN_PVAR_237 f s g op)). Qed.
Lemma lem5724852 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term441 _120186 _120195 _120196 f s g op) = (term442 _120186 _120195 _120196 f s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120186 => @lem5724845 _120186 _120195 _120196 GEN_PVAR_237 f s g op)). Qed.
Lemma lem5724855 {_120186 : Type'} : (@GSPEC _120186) = (@GSPEC _120186).
Proof. exact (eq_refl (@GSPEC _120186)). Qed.
Lemma lem5724856 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term426 _120186 _120195 _120196 f s g op) = (term443 _120186 _120195 _120196 f s g op).
Proof. exact (MK_COMB (@lem5724855 _120186) (@lem5724852 _120186 _120195 _120196 f s g op)). Qed.
Lemma lem5724859 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term423 _120186 _120195 _120196 op g f s) = (term443 _120186 _120195 _120196 f s g op).
Proof. exact (TRANS (@lem5724710 _120186 _120195 _120196 f s g op) (@lem5724856 _120186 _120195 _120196 f s g op)). Qed.
Lemma lem5724860 {_120186 : Type'} (x : _120186) : (@IN _120186 x) = (@IN _120186 x).
Proof. exact (eq_refl (@IN _120186 x)). Qed.
Lemma lem5724861 {_120186 _120195 _120196 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term444 _120186 _120195 _120196 x op g f s) = (term445 _120186 _120195 _120196 x f s g op).
Proof. exact (MK_COMB (@lem5724860 _120186 x) (@lem5724859 _120186 _120195 _120196 f s g op)). Qed.
Lemma lem5724863 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5724864 {_120186 : Type'} (p : _120186 -> Prop) (x : _120186) : (term64 _120186 x p) = (p x).
Proof. exact (@lem5724863 _120186 p x). Qed.
Lemma lem5724865 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) (x : _120186) : (term446 _120186 _120195 _120196 x f s g op) = (term447 _120186 _120195 _120196 f s g op x).
Proof. exact (@lem5724864 _120186 (term448 _120186 _120195 _120196 f s g op) x). Qed.
Lemma lem5724866 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term447 _120186 _120195 _120196 f s g op x) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (eq_refl (term447 _120186 _120195 _120196 f s g op x)). Qed.
Lemma lem5724867 {_120186 : Type'} (GEN_PVAR_237 : _120186) : (@SETSPEC _120186 GEN_PVAR_237) = (@SETSPEC _120186 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120186 GEN_PVAR_237)). Qed.
Lemma lem5724868 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term449 _120186 _120195 _120196 GEN_PVAR_237 f s g op x) = (term434 _120186 _120195 _120196 GEN_PVAR_237 f s g x op).
Proof. exact (MK_COMB (@lem5724867 _120186 GEN_PVAR_237) (@lem5724866 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5724869 {_120186 : Type'} (x : _120186) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5724870 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) (x : _120186) : (term450 _120186 _120195 _120196 GEN_PVAR_237 f s g op x) = (term436 _120186 _120195 _120196 GEN_PVAR_237 f s g op x).
Proof. exact (MK_COMB (@lem5724868 _120186 _120195 _120196 GEN_PVAR_237 f s g x op) (@lem5724869 _120186 x)). Qed.
Lemma lem5724871 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term451 _120186 _120195 _120196 GEN_PVAR_237 f s g op) = (term438 _120186 _120195 _120196 GEN_PVAR_237 f s g op).
Proof. exact (fun_ext (fun x : _120186 => @lem5724870 _120186 _120195 _120196 GEN_PVAR_237 f s g op x)). Qed.
Lemma lem5724872 {_120186 : Type'} : (@ex _120186) = (@ex _120186).
Proof. exact (eq_refl (@ex _120186)). Qed.
Lemma lem5724873 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term452 _120186 _120195 _120196 GEN_PVAR_237 f s g op) = (term440 _120186 _120195 _120196 GEN_PVAR_237 f s g op).
Proof. exact (MK_COMB (@lem5724872 _120186) (@lem5724871 _120186 _120195 _120196 GEN_PVAR_237 f s g op)). Qed.
Lemma lem5724874 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term453 _120186 _120195 _120196 f s g op) = (term442 _120186 _120195 _120196 f s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120186 => @lem5724873 _120186 _120195 _120196 GEN_PVAR_237 f s g op)). Qed.
Lemma lem5724875 {_120186 : Type'} : (@GSPEC _120186) = (@GSPEC _120186).
Proof. exact (eq_refl (@GSPEC _120186)). Qed.
Lemma lem5724876 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term454 _120186 _120195 _120196 f s g op) = (term443 _120186 _120195 _120196 f s g op).
Proof. exact (MK_COMB (@lem5724875 _120186) (@lem5724874 _120186 _120195 _120196 f s g op)). Qed.
Lemma lem5724877 {_120186 : Type'} (x : _120186) : (@IN _120186 x) = (@IN _120186 x).
Proof. exact (eq_refl (@IN _120186 x)). Qed.
Lemma lem5724878 {_120186 _120195 _120196 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term446 _120186 _120195 _120196 x f s g op) = (term445 _120186 _120195 _120196 x f s g op).
Proof. exact (MK_COMB (@lem5724877 _120186 x) (@lem5724876 _120186 _120195 _120196 f s g op)). Qed.
Lemma lem5724879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5724880 {_120186 _120195 _120196 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (op : type1400 _120196) : (term455 _120186 _120195 _120196 x f s g op) = (term456 _120186 _120195 _120196 x f s g op).
Proof. exact (MK_COMB (@lem5724879) (@lem5724878 _120186 _120195 _120196 x f s g op)). Qed.
Lemma lem5724881 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term447 _120186 _120195 _120196 f s g op x) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (eq_refl (term447 _120186 _120195 _120196 f s g op x)). Qed.
Lemma lem5724882 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : ((term446 _120186 _120195 _120196 x f s g op) = (term447 _120186 _120195 _120196 f s g op x)) = ((term445 _120186 _120195 _120196 x f s g op) = (term432 _120186 _120195 _120196 f s g x op)).
Proof. exact (MK_COMB (@lem5724880 _120186 _120195 _120196 x f s g op) (@lem5724881 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5724883 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term445 _120186 _120195 _120196 x f s g op) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (EQ_MP (@lem5724882 _120186 _120195 _120196 f s g x op) (@lem5724865 _120186 _120195 _120196 f s g op x)). Qed.
Lemma lem5724964 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term444 _120186 _120195 _120196 x op g f s) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (TRANS (@lem5724861 _120186 _120195 _120196 x f s g op) (@lem5724883 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5724965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5724966 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term457 _120186 _120195 _120196 x op g f s) = (term458 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5724965) (@lem5724964 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5724970 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term38 A B y f s) = (term39 A B y f s).
Proof. exact (EQ_MP (@lem5720663 A B y f s) (@lem5720662 A B y s f)). Qed.
Lemma lem5724971 {_120186 _120195 : Type'} (y : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term427 _120186 _120195 y f s) = (term428 _120186 _120195 y f s).
Proof. exact (@lem5724970 _120195 _120186 y f s). Qed.
Lemma lem5724972 {_120186 _120195 _120196 : Type'} (x : _120186) (op : type1400 _120196) (g : _120186 -> _120196) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term459 _120186 _120195 _120196 x op g f s) = (term460 _120186 _120195 _120196 x op g f s).
Proof. exact (@lem5724971 _120186 _120195 x f (term461 _120186 _120195 _120196 op g f s)). Qed.
Lemma lem5725018 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term74 A B s f op).
Proof. exact (EQ_MP (@lem5720743 A B s f op) (@lem5720742 A B s f op)). Qed.
Lemma lem5725019 {_120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120196) (op : type1400 _120196) : (@support _120195 _120196 op f s) = (term74 _120195 _120196 s f op).
Proof. exact (@lem5725018 _120195 _120196 s f op). Qed.
Lemma lem5725020 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term461 _120186 _120195 _120196 op g f s) = (term462 _120186 _120195 _120196 s g f op).
Proof. exact (@lem5725019 _120195 _120196 s (@o _120195 _120186 _120196 g f) op). Qed.
Lemma lem5725080 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term45 A B C f g x).
Proof. exact (EQ_MP (@lem5720672 A B C f g x) (@lem5720671 A B C f g x)). Qed.
Lemma lem5725081 {_120186 _120195 _120196 : Type'} (f : _120186 -> _120196) (g : _120195 -> _120186) (x : _120195) : (@o _120195 _120186 _120196 f g x) = (term463 _120186 _120195 _120196 f g x).
Proof. exact (@lem5725080 _120195 _120186 _120196 f g x). Qed.
Lemma lem5725082 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) : (@o _120195 _120186 _120196 g f x) = (term463 _120186 _120195 _120196 g f x).
Proof. exact (@lem5725081 _120186 _120195 _120196 g f x). Qed.
Lemma lem5725093 {_120196 : Type'} : (@eq _120196) = (@eq _120196).
Proof. exact (eq_refl (@eq _120196)). Qed.
Lemma lem5725094 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) : (term464 _120186 _120195 _120196 g f x) = (term465 _120186 _120195 _120196 g f x).
Proof. exact (MK_COMB (@lem5725093 _120196) (@lem5725082 _120186 _120195 _120196 g f x)). Qed.
Lemma lem5725103 {_120196 : Type'} (op : type1400 _120196) : (@neutral _120196 op) = (@neutral _120196 op).
Proof. exact (eq_refl (@neutral _120196 op)). Qed.
Lemma lem5725104 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : ((@o _120195 _120186 _120196 g f x) = (@neutral _120196 op)) = ((term463 _120186 _120195 _120196 g f x) = (@neutral _120196 op)).
Proof. exact (MK_COMB (@lem5725094 _120186 _120195 _120196 g f x) (@lem5725103 _120196 op)). Qed.
Lemma lem5725111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5725112 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term466 _120186 _120195 _120196 g f x op) = (term467 _120186 _120195 _120196 g f x op).
Proof. exact (MK_COMB (@lem5725111) (@lem5725104 _120186 _120195 _120196 g f x op)). Qed.
Lemma lem5725115 {_120195 : Type'} (x : _120195) (s : _120195 -> Prop) : (term468 _120195 x s) = (term468 _120195 x s).
Proof. exact (eq_refl (term468 _120195 x s)). Qed.
Lemma lem5725116 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term469 _120186 _120195 _120196 s g f x op) = (term470 _120186 _120195 _120196 s g f x op).
Proof. exact (MK_COMB (@lem5725115 _120195 x s) (@lem5725112 _120186 _120195 _120196 g f x op)). Qed.
Lemma lem5725121 {_120195 : Type'} (GEN_PVAR_237 : _120195) : (@SETSPEC _120195 GEN_PVAR_237) = (@SETSPEC _120195 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120195 GEN_PVAR_237)). Qed.
Lemma lem5725122 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term471 _120186 _120195 _120196 GEN_PVAR_237 s g f x op) = (term472 _120186 _120195 _120196 GEN_PVAR_237 s g f x op).
Proof. exact (MK_COMB (@lem5725121 _120195 GEN_PVAR_237) (@lem5725116 _120186 _120195 _120196 s g f x op)). Qed.
Lemma lem5725127 {_120195 : Type'} (x : _120195) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5725128 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (x : _120195) : (term473 _120186 _120195 _120196 GEN_PVAR_237 s g f op x) = (term474 _120186 _120195 _120196 GEN_PVAR_237 s g f op x).
Proof. exact (MK_COMB (@lem5725122 _120186 _120195 _120196 GEN_PVAR_237 s g f x op) (@lem5725127 _120195 x)). Qed.
Lemma lem5725131 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term475 _120186 _120195 _120196 GEN_PVAR_237 s g f op) = (term476 _120186 _120195 _120196 GEN_PVAR_237 s g f op).
Proof. exact (fun_ext (fun x : _120195 => @lem5725128 _120186 _120195 _120196 GEN_PVAR_237 s g f op x)). Qed.
Lemma lem5725134 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5725135 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term477 _120186 _120195 _120196 GEN_PVAR_237 s g f op) = (term478 _120186 _120195 _120196 GEN_PVAR_237 s g f op).
Proof. exact (MK_COMB (@lem5725134 _120195) (@lem5725131 _120186 _120195 _120196 GEN_PVAR_237 s g f op)). Qed.
Lemma lem5725142 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term479 _120186 _120195 _120196 s g f op) = (term480 _120186 _120195 _120196 s g f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120195 => @lem5725135 _120186 _120195 _120196 GEN_PVAR_237 s g f op)). Qed.
Lemma lem5725145 {_120195 : Type'} : (@GSPEC _120195) = (@GSPEC _120195).
Proof. exact (eq_refl (@GSPEC _120195)). Qed.
Lemma lem5725146 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term462 _120186 _120195 _120196 s g f op) = (term481 _120186 _120195 _120196 s g f op).
Proof. exact (MK_COMB (@lem5725145 _120195) (@lem5725142 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725149 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term461 _120186 _120195 _120196 op g f s) = (term481 _120186 _120195 _120196 s g f op).
Proof. exact (TRANS (@lem5725020 _120186 _120195 _120196 s g f op) (@lem5725146 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725150 {_120195 : Type'} (x : _120195) : (@IN _120195 x) = (@IN _120195 x).
Proof. exact (eq_refl (@IN _120195 x)). Qed.
Lemma lem5725151 {_120186 _120195 _120196 : Type'} (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term482 _120186 _120195 _120196 x op g f s) = (term483 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5725150 _120195 x) (@lem5725149 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725153 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5720721 _83095 p x) (@lem5720720 _83095 p x)). Qed.
Lemma lem5725154 {_120195 : Type'} (p : _120195 -> Prop) (x : _120195) : (term64 _120195 x p) = (p x).
Proof. exact (@lem5725153 _120195 p x). Qed.
Lemma lem5725155 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (x : _120195) : (term484 _120186 _120195 _120196 x s g f op) = (term485 _120186 _120195 _120196 s g f op x).
Proof. exact (@lem5725154 _120195 (term486 _120186 _120195 _120196 s g f op) x). Qed.
Lemma lem5725156 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term485 _120186 _120195 _120196 s g f op x) = (term470 _120186 _120195 _120196 s g f x op).
Proof. exact (eq_refl (term485 _120186 _120195 _120196 s g f op x)). Qed.
Lemma lem5725157 {_120195 : Type'} (GEN_PVAR_237 : _120195) : (@SETSPEC _120195 GEN_PVAR_237) = (@SETSPEC _120195 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _120195 GEN_PVAR_237)). Qed.
Lemma lem5725158 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term487 _120186 _120195 _120196 GEN_PVAR_237 s g f op x) = (term472 _120186 _120195 _120196 GEN_PVAR_237 s g f x op).
Proof. exact (MK_COMB (@lem5725157 _120195 GEN_PVAR_237) (@lem5725156 _120186 _120195 _120196 s g f x op)). Qed.
Lemma lem5725159 {_120195 : Type'} (x : _120195) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5725160 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (x : _120195) : (term488 _120186 _120195 _120196 GEN_PVAR_237 s g f op x) = (term474 _120186 _120195 _120196 GEN_PVAR_237 s g f op x).
Proof. exact (MK_COMB (@lem5725158 _120186 _120195 _120196 GEN_PVAR_237 s g f x op) (@lem5725159 _120195 x)). Qed.
Lemma lem5725161 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term489 _120186 _120195 _120196 GEN_PVAR_237 s g f op) = (term476 _120186 _120195 _120196 GEN_PVAR_237 s g f op).
Proof. exact (fun_ext (fun x : _120195 => @lem5725160 _120186 _120195 _120196 GEN_PVAR_237 s g f op x)). Qed.
Lemma lem5725162 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5725163 {_120186 _120195 _120196 : Type'} (GEN_PVAR_237 : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term490 _120186 _120195 _120196 GEN_PVAR_237 s g f op) = (term478 _120186 _120195 _120196 GEN_PVAR_237 s g f op).
Proof. exact (MK_COMB (@lem5725162 _120195) (@lem5725161 _120186 _120195 _120196 GEN_PVAR_237 s g f op)). Qed.
Lemma lem5725164 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term491 _120186 _120195 _120196 s g f op) = (term480 _120186 _120195 _120196 s g f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _120195 => @lem5725163 _120186 _120195 _120196 GEN_PVAR_237 s g f op)). Qed.
Lemma lem5725165 {_120195 : Type'} : (@GSPEC _120195) = (@GSPEC _120195).
Proof. exact (eq_refl (@GSPEC _120195)). Qed.
Lemma lem5725166 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term492 _120186 _120195 _120196 s g f op) = (term481 _120186 _120195 _120196 s g f op).
Proof. exact (MK_COMB (@lem5725165 _120195) (@lem5725164 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725167 {_120195 : Type'} (x : _120195) : (@IN _120195 x) = (@IN _120195 x).
Proof. exact (eq_refl (@IN _120195 x)). Qed.
Lemma lem5725168 {_120186 _120195 _120196 : Type'} (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term484 _120186 _120195 _120196 x s g f op) = (term483 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5725167 _120195 x) (@lem5725166 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5725170 {_120186 _120195 _120196 : Type'} (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term493 _120186 _120195 _120196 x s g f op) = (term494 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5725169) (@lem5725168 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5725171 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term485 _120186 _120195 _120196 s g f op x) = (term470 _120186 _120195 _120196 s g f x op).
Proof. exact (eq_refl (term485 _120186 _120195 _120196 s g f op x)). Qed.
Lemma lem5725172 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : ((term484 _120186 _120195 _120196 x s g f op) = (term485 _120186 _120195 _120196 s g f op x)) = ((term483 _120186 _120195 _120196 x s g f op) = (term470 _120186 _120195 _120196 s g f x op)).
Proof. exact (MK_COMB (@lem5725170 _120186 _120195 _120196 x s g f op) (@lem5725171 _120186 _120195 _120196 s g f x op)). Qed.
Lemma lem5725173 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term483 _120186 _120195 _120196 x s g f op) = (term470 _120186 _120195 _120196 s g f x op).
Proof. exact (EQ_MP (@lem5725172 _120186 _120195 _120196 s g f x op) (@lem5725155 _120186 _120195 _120196 s g f op x)). Qed.
Lemma lem5725222 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term482 _120186 _120195 _120196 x op g f s) = (term470 _120186 _120195 _120196 s g f x op).
Proof. exact (TRANS (@lem5725151 _120186 _120195 _120196 x s g f op) (@lem5725173 _120186 _120195 _120196 s g f x op)). Qed.
Lemma lem5725223 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) : (term495 _120186 _120195 x f x') = (term495 _120186 _120195 x f x').
Proof. exact (eq_refl (term495 _120186 _120195 x f x')). Qed.
Lemma lem5725224 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term496 _120186 _120195 _120196 x x' op g f s) = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5725223 _120186 _120195 x f x') (@lem5725222 _120186 _120195 _120196 s g f x' op)). Qed.
Lemma lem5725229 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term498 _120186 _120195 _120196 x op g f s) = (term499 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5725224 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5725232 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5725233 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term460 _120186 _120195 _120196 x op g f s) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5725232 _120195) (@lem5725229 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5725240 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term459 _120186 _120195 _120196 x op g f s) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (TRANS (@lem5724972 _120186 _120195 _120196 x op g f s) (@lem5725233 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5725241 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term444 _120186 _120195 _120196 x op g f s) = (term459 _120186 _120195 _120196 x op g f s)) = ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)).
Proof. exact (MK_COMB (@lem5724966 _120186 _120195 _120196 f s g x op) (@lem5725240 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5725248 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term501 _120186 _120195 _120196 op g f s) = (term502 _120186 _120195 _120196 s g f op).
Proof. exact (fun_ext (fun x : _120186 => @lem5725241 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5725251 {_120186 : Type'} : (@all _120186) = (@all _120186).
Proof. exact (eq_refl (@all _120186)). Qed.
Lemma lem5725252 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term425 _120186 _120195 _120196 op g f s) = (term503 _120186 _120195 _120196 s g f op).
Proof. exact (MK_COMB (@lem5725251 _120186) (@lem5725248 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725259 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term423 _120186 _120195 _120196 op g f s) = (term424 _120186 _120195 _120196 op g f s)) = (term503 _120186 _120195 _120196 s g f op).
Proof. exact (TRANS (@lem5724678 _120186 _120195 _120196 op g f s) (@lem5725252 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725260 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term504 _120186 _120195 _120196 op g f) = (term505 _120186 _120195 _120196 g f op).
Proof. exact (fun_ext (fun s : _120195 -> Prop => @lem5725259 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5725263 {_120195 : Type'} : (@all (_120195 -> Prop)) = (@all (_120195 -> Prop)).
Proof. exact (eq_refl (@all (_120195 -> Prop))). Qed.
Lemma lem5725264 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term506 _120186 _120195 _120196 op g f) = (term507 _120186 _120195 _120196 g f op).
Proof. exact (MK_COMB (@lem5725263 _120195) (@lem5725260 _120186 _120195 _120196 g f op)). Qed.
Lemma lem5725271 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term508 _120186 _120195 _120196 op f) = (term509 _120186 _120195 _120196 f op).
Proof. exact (fun_ext (fun g : _120186 -> _120196 => @lem5725264 _120186 _120195 _120196 g f op)). Qed.
Lemma lem5725274 {_120186 _120196 : Type'} : (@all (_120186 -> _120196)) = (@all (_120186 -> _120196)).
Proof. exact (eq_refl (@all (_120186 -> _120196))). Qed.
Lemma lem5725275 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term510 _120186 _120195 _120196 op f) = (term511 _120186 _120195 _120196 f op).
Proof. exact (MK_COMB (@lem5725274 _120186 _120196) (@lem5725271 _120186 _120195 _120196 f op)). Qed.
Lemma lem5725282 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term512 _120186 _120195 _120196 op) = (term513 _120186 _120195 _120196 op).
Proof. exact (fun_ext (fun f : _120195 -> _120186 => @lem5725275 _120186 _120195 _120196 f op)). Qed.
Lemma lem5725285 {_120186 _120195 : Type'} : (@all (_120195 -> _120186)) = (@all (_120195 -> _120186)).
Proof. exact (eq_refl (@all (_120195 -> _120186))). Qed.
Lemma lem5725286 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term514 _120186 _120195 _120196 op) = (term515 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5725285 _120186 _120195) (@lem5725282 _120186 _120195 _120196 op)). Qed.
Lemma lem5725293 {_120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term516 _120158 _120186 _120195 _120196 op) = (term517 _120158 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5724640 _120158 _120196 op) (@lem5725286 _120186 _120195 _120196 op)). Qed.
Lemma lem5725298 {_120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term518 _120120 _120158 _120186 _120195 _120196 op) = (term519 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5723944 _120120 _120196 op) (@lem5725293 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5725303 {_120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term520 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term521 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5723264 _120082 _120196 op) (@lem5725298 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5725308 {_120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term522 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term523 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5722584 _120044 _120196 op) (@lem5725303 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5725313 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term524 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term525 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5722021 _120011 _120196 op) (@lem5725308 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5725318 {_119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term526 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term527 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5720979 _119963 _120196 op) (@lem5725313 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5725320 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5725321 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term527 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term525 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (@lem5725320 (term525 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5726732 {_119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term526 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term525 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (TRANS (@lem5725318 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) (@lem5725321 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5726733 {_119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term525 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) = (term526 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op).
Proof. exact (SYM (@lem5726732 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5726734 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term180 _476 _475 _474 _477) = (term528 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem5726735 (_474 : Prop) (_475 : Prop) (_477 : Prop) : (term529 _475 _474 _477) = (term530 _474 _475 _477).
Proof. exact (@lem5726734 _474 _475 term531 _477). Qed.
Lemma lem5726736 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term532 _120011 _120196 x s f x' op) = (term533 _120011 _120196 x s f x' op).
Proof. exact (@lem5726735 ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)) ((f x) = (@neutral _120196 op)) ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op))). Qed.
Lemma lem5726737 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term534 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)).
Proof. exact (eq_refl (term534 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726738 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term535 _120011 _120196 f x op) = (term535 _120011 _120196 f x op).
Proof. exact (eq_refl (term535 _120011 _120196 f x op)). Qed.
Lemma lem5726739 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term536 _120011 _120196 x s f x' op) = (term537 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726738 _120011 _120196 f x op) (@lem5726737 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726740 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term538 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (eq_refl (term538 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726741 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term539 _120011 _120196 f x op) = (term539 _120011 _120196 f x op).
Proof. exact (eq_refl (term539 _120011 _120196 f x op)). Qed.
Lemma lem5726742 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term540 _120011 _120196 x s f x' op) = (term541 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726741 _120011 _120196 f x op) (@lem5726740 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5726744 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term542 _120011 _120196 x s f x' op) = (term543 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726743) (@lem5726742 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726745 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term533 _120011 _120196 x s f x' op) = (term544 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726744 _120011 _120196 x s f x' op) (@lem5726739 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726746 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term532 _120011 _120196 x s f x' op) = (term182 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term532 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5726748 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term545 _120011 _120196 x s f x' op) = (term546 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726747) (@lem5726746 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726749 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term532 _120011 _120196 x s f x' op) = (term533 _120011 _120196 x s f x' op)) = ((term182 _120011 _120196 x s f x' op) = (term544 _120011 _120196 x s f x' op)).
Proof. exact (MK_COMB (@lem5726748 _120011 _120196 x s f x' op) (@lem5726745 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726750 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term182 _120011 _120196 x s f x' op) = (term544 _120011 _120196 x s f x' op).
Proof. exact (EQ_MP (@lem5726749 _120011 _120196 x s f x' op) (@lem5726736 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726751 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term544 _120011 _120196 x s f x' op) = (term182 _120011 _120196 x s f x' op).
Proof. exact (SYM (@lem5726750 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726752 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5726769 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term78 _120011 _120196 f x op.
Proof. exact (h1). Qed.
Lemma lem5726787 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5726788 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)) = (term548 _120011 _120196 x s f x' op).
Proof. exact (@lem5726787 ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op))). Qed.
Lemma lem5726789 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term548 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (SYM (@lem5726788 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726790 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) : term549 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5726793 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term550 _120011 _120196 x s f x' op) : term550 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5726794 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term551 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term550 _120011 _120196 x s f x' op => @lem5726793 _120011 _120196 x s f x' op h0). Qed.
Lemma lem5726795 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term551 _120011 _120196 x s f x' op) : term551 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5726796 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term550 _120011 _120196 x s f x' op) : term550 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5726797 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term550 _120011 _120196 x s f x' op) (h2 : term551 _120011 _120196 x s f x' op) : term550 _120011 _120196 x s f x' op.
Proof. exact (@lem5726795 _120011 _120196 x s f x' op h2 (@lem5726796 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5726798 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term550 _120011 _120196 x s f x' op) : term552 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term551 _120011 _120196 x s f x' op => @lem5726797 _120011 _120196 x s f x' op h1 h0). Qed.
Lemma lem5726799 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term551 _120011 _120196 x s f x' op) : term551 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5726800 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term550 _120011 _120196 x s f x' op) (h2 : term551 _120011 _120196 x s f x' op) : term550 _120011 _120196 x s f x' op.
Proof. exact (@lem5726798 _120011 _120196 x s f x' op h1 (@lem5726799 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5726801 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term551 _120011 _120196 x s f x' op) : term551 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term550 _120011 _120196 x s f x' op => @lem5726800 _120011 _120196 x s f x' op h0 h1). Qed.
Lemma lem5726802 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term553 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term551 _120011 _120196 x s f x' op => @lem5726801 _120011 _120196 x s f x' op h0). Qed.
Lemma lem5726805 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term551 _120011 _120196 x s f x' op.
Proof. exact (@lem5726802 _120011 _120196 x s f x' op (@lem5726794 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726806 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term551 _120011 _120196 x s f x' op.
Proof. exact (@lem5726805 _120011 _120196 x s f x' op). Qed.
Lemma lem5726830 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5726831 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term548 _120011 _120196 x s f x' op) = (term554 _120011 _120196 x s f x' op).
Proof. exact (@lem5726830 (term549 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726833 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5726834 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term554 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (@lem5726833 ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op))). Qed.
Lemma lem5726835 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term548 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (TRANS (@lem5726831 _120011 _120196 x s f x' op) (@lem5726834 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726842 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term539 _120011 _120196 f x op) = (term539 _120011 _120196 f x op).
Proof. exact (eq_refl (term539 _120011 _120196 f x op)). Qed.
Lemma lem5726843 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term550 _120011 _120196 x s f x' op) = (term541 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726842 _120011 _120196 f x op) (@lem5726835 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726846 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term556 _120011 _120196 s f x' op) = (term557 _120011 _120196 s f x' op).
Proof. exact (fun_ext (fun x : _120011 => @lem5726843 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726847 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5726848 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term558 _120011 _120196 s f x' op) = (term559 _120011 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5726847 _120011) (@lem5726846 _120011 _120196 s f x' op)). Qed.
Lemma lem5726853 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term560 _120011 _120196 f x' op) = (term561 _120011 _120196 f x' op).
Proof. exact (fun_ext (fun s : _120011 -> Prop => @lem5726848 _120011 _120196 s f x' op)). Qed.
Lemma lem5726854 {_120011 : Type'} : (@all (_120011 -> Prop)) = (@all (_120011 -> Prop)).
Proof. exact (eq_refl (@all (_120011 -> Prop))). Qed.
Lemma lem5726855 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term562 _120011 _120196 f x' op) = (term563 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5726854 _120011) (@lem5726853 _120011 _120196 f x' op)). Qed.
Lemma lem5726860 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term564 _120011 _120196 x' op) = (term565 _120011 _120196 x' op).
Proof. exact (fun_ext (fun f : _120011 -> _120196 => @lem5726855 _120011 _120196 f x' op)). Qed.
Lemma lem5726861 {_120011 _120196 : Type'} : (@all (_120011 -> _120196)) = (@all (_120011 -> _120196)).
Proof. exact (eq_refl (@all (_120011 -> _120196))). Qed.
Lemma lem5726862 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term566 _120011 _120196 x' op) = (term567 _120011 _120196 x' op).
Proof. exact (MK_COMB (@lem5726861 _120011 _120196) (@lem5726860 _120011 _120196 x' op)). Qed.
Lemma lem5726867 {_120011 _120196 : Type'} (op : type1400 _120196) : (term568 _120011 _120196 op) = (term569 _120011 _120196 op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5726862 _120011 _120196 x' op)). Qed.
Lemma lem5726868 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5726869 {_120011 _120196 : Type'} (op : type1400 _120196) : (term570 _120011 _120196 op) = (term571 _120011 _120196 op).
Proof. exact (MK_COMB (@lem5726868 _120011) (@lem5726867 _120011 _120196 op)). Qed.
Lemma lem5726874 {_120011 _120196 : Type'} : (term572 _120011 _120196) = (term573 _120011 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5726869 _120011 _120196 op)). Qed.
Lemma lem5726875 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5726884 {_120011 _120196 : Type'} : (term574 _120011 _120196) = (term575 _120011 _120196).
Proof. exact (MK_COMB (@lem5726875 _120196) (@lem5726874 _120011 _120196)). Qed.
Lemma lem5726909 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term541 _120011 _120196 x s f x' op) = (term541 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term541 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726910 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term557 _120011 _120196 s f x' op) = (term557 _120011 _120196 s f x' op).
Proof. exact (fun_ext (fun x : _120011 => @lem5726909 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726911 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5726912 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term559 _120011 _120196 s f x' op) = (term559 _120011 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5726911 _120011) (@lem5726910 _120011 _120196 s f x' op)). Qed.
Lemma lem5726913 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term561 _120011 _120196 f x' op) = (term561 _120011 _120196 f x' op).
Proof. exact (fun_ext (fun s : _120011 -> Prop => @lem5726912 _120011 _120196 s f x' op)). Qed.
Lemma lem5726914 {_120011 : Type'} : (@all (_120011 -> Prop)) = (@all (_120011 -> Prop)).
Proof. exact (eq_refl (@all (_120011 -> Prop))). Qed.
Lemma lem5726915 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term563 _120011 _120196 f x' op) = (term563 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5726914 _120011) (@lem5726913 _120011 _120196 f x' op)). Qed.
Lemma lem5726916 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term565 _120011 _120196 x' op) = (term565 _120011 _120196 x' op).
Proof. exact (fun_ext (fun f : _120011 -> _120196 => @lem5726915 _120011 _120196 f x' op)). Qed.
Lemma lem5726917 {_120011 _120196 : Type'} : (@all (_120011 -> _120196)) = (@all (_120011 -> _120196)).
Proof. exact (eq_refl (@all (_120011 -> _120196))). Qed.
Lemma lem5726918 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term567 _120011 _120196 x' op) = (term567 _120011 _120196 x' op).
Proof. exact (MK_COMB (@lem5726917 _120011 _120196) (@lem5726916 _120011 _120196 x' op)). Qed.
Lemma lem5726919 {_120011 _120196 : Type'} (op : type1400 _120196) : (term569 _120011 _120196 op) = (term569 _120011 _120196 op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5726918 _120011 _120196 x' op)). Qed.
Lemma lem5726920 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5726921 {_120011 _120196 : Type'} (op : type1400 _120196) : (term571 _120011 _120196 op) = (term571 _120011 _120196 op).
Proof. exact (MK_COMB (@lem5726920 _120011) (@lem5726919 _120011 _120196 op)). Qed.
Lemma lem5726922 {_120011 _120196 : Type'} : (term573 _120011 _120196) = (term573 _120011 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5726921 _120011 _120196 op)). Qed.
Lemma lem5726923 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5726924 {_120011 _120196 : Type'} : (term575 _120011 _120196) = (term575 _120011 _120196).
Proof. exact (MK_COMB (@lem5726923 _120196) (@lem5726922 _120011 _120196)). Qed.
Lemma lem5726965 {_120011 _120196 : Type'} : (term574 _120011 _120196) = (term575 _120011 _120196).
Proof. exact (TRANS (@lem5726884 _120011 _120196) (@lem5726924 _120011 _120196)). Qed.
Lemma lem5726966 {_120011 _120196 : Type'} : (term575 _120011 _120196) = (term574 _120011 _120196).
Proof. exact (SYM (@lem5726965 _120011 _120196)). Qed.
Lemma lem5726969 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5726970 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)) = (term548 _120011 _120196 x s f x' op).
Proof. exact (@lem5726969 ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op))). Qed.
Lemma lem5726971 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term548 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (SYM (@lem5726970 _120011 _120196 x s f x' op)). Qed.
Lemma lem5726972 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) : term549 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5726978 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5726987 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) : (term576 _120011 x x' s) = (term577 _120011 x x' s).
Proof. exact (@lem17160 (x' = x) (@IN _120011 x' s)). Qed.
Lemma lem5726994 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term578 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5726995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5726996 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) : (term579 _120011 x x' s) = (term580 _120011 x x' s).
Proof. exact (MK_COMB (@lem5726995) (@lem5726987 _120011 x x' s)). Qed.
Lemma lem5726997 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term581 _120011 _120196 x s f x' op) = (term582 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5726996 _120011 x x' s) (@lem5726994 _120011 _120196 f x' op)). Qed.
Lemma lem5726998 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term583 _120011 _120196 x s f x' op) = (term581 _120011 _120196 x s f x' op).
Proof. exact (@lem17045 (term59 _120011 x x' s) (term78 _120011 _120196 f x' op)). Qed.
Lemma lem5726999 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term583 _120011 _120196 x s f x' op) = (term582 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5726998 _120011 _120196 x s f x' op) (@lem5726997 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727008 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term578 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5727010 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term584 _120011 x' s) = (term584 _120011 x' s).
Proof. exact (eq_refl (term584 _120011 x' s)). Qed.
Lemma lem5727011 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term585 _120011 _120196 s f x' op) = (term586 _120011 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5727010 _120011 x' s) (@lem5727008 _120011 _120196 f x' op)). Qed.
Lemma lem5727012 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term404 _120011 _120196 s f x' op) = (term585 _120011 _120196 s f x' op).
Proof. exact (@lem17045 (@IN _120011 x' s) (term78 _120011 _120196 f x' op)). Qed.
Lemma lem5727013 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term404 _120011 _120196 s f x' op) = (term586 _120011 _120196 s f x' op).
Proof. exact (TRANS (@lem5727012 _120011 _120196 s f x' op) (@lem5727011 _120011 _120196 s f x' op)). Qed.
Lemma lem5727016 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term158 _120011 _120196 s f x' op) = (term158 _120011 _120196 s f x' op).
Proof. exact (eq_refl (term158 _120011 _120196 s f x' op)). Qed.
Lemma lem5727017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5727018 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term587 _120011 _120196 x s f x' op) = (term588 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5727017) (@lem5726999 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727019 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term589 _120011 _120196 x s f x' op) = (term590 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5727018 _120011 _120196 x s f x' op) (@lem5727016 _120011 _120196 s f x' op)). Qed.
Lemma lem5727021 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term591 _120011 _120196 x s f x' op) = (term591 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term591 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727022 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term592 _120011 _120196 x s f x' op) = (term593 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5727021 _120011 _120196 x s f x' op) (@lem5727013 _120011 _120196 s f x' op)). Qed.
Lemma lem5727023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5727024 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term594 _120011 _120196 x s f x' op) = (term595 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5727023) (@lem5727022 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727025 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term596 _120011 _120196 x s f x' op) = (term597 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5727024 _120011 _120196 x s f x' op) (@lem5727019 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727026 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term549 _120011 _120196 x s f x' op) = (term596 _120011 _120196 x s f x' op).
Proof. exact (@lem17646 (term121 _120011 _120196 x s f x' op) (term158 _120011 _120196 s f x' op)). Qed.
Lemma lem5727031 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term549 _120011 _120196 x s f x' op) = (term597 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5727026 _120011 _120196 x s f x' op) (@lem5727025 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727042 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727146 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) : term597 _120011 _120196 x s f x' op.
Proof. exact (EQ_MP (@lem5727031 _120011 _120196 x s f x' op) (@lem5726972 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727147 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term593 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727148 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : term590 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727149 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term586 _120011 _120196 s f x' op.
Proof. exact (proj2 (@lem5727147 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727150 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term121 _120011 _120196 x s f x' op.
Proof. exact (proj1 (@lem5727147 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727152 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term59 _120011 x x' s.
Proof. exact (proj1 (@lem5727150 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727159 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : term158 _120011 _120196 s f x' op.
Proof. exact (proj2 (@lem5727148 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727160 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : term582 _120011 _120196 x s f x' op.
Proof. exact (proj1 (@lem5727148 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727163 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term577 _120011 x x' s.
Proof. exact (h1). Qed.
Lemma lem5727170 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727178 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5727194 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5727198 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727210 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5727214 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) : term598 _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5727230 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727266 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727268 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727270 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5727150 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727272 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5727278 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5727150 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727280 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5727282 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727288 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5727290 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) : term598 _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5727294 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5727150 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727298 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727308 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term598 _120011 x' s.
Proof. exact (proj2 (@lem5727163 _120011 x x' s h1)). Qed.
Lemma lem5727314 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5727159 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727316 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727344 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727345 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term599 _120011 _120196 f op) = (term599 _120011 _120196 f op).
Proof. exact (eq_refl (term599 _120011 _120196 f op)). Qed.
Lemma lem5727346 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x).
Proof. exact (MK_COMB (@lem5727345 _120011 _120196 f op) (@lem5727272 _120011 x' x h1)). Qed.
Lemma lem5727347 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term600 _120011 _120196 f op x) = (term78 _120011 _120196 f x op).
Proof. exact (eq_refl (term600 _120011 _120196 f op x)). Qed.
Lemma lem5727348 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term601 _120011 _120196 f op x') = (term601 _120011 _120196 f op x').
Proof. exact (eq_refl (term601 _120011 _120196 f op x')). Qed.
Lemma lem5727349 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x)) = ((term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x op)).
Proof. exact (MK_COMB (@lem5727348 _120011 _120196 f op x') (@lem5727347 _120011 _120196 f x op)). Qed.
Lemma lem5727350 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x' op).
Proof. exact (eq_refl (term600 _120011 _120196 f op x')). Qed.
Lemma lem5727351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5727352 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term601 _120011 _120196 f op x') = (term602 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5727351) (@lem5727350 _120011 _120196 f x' op)). Qed.
Lemma lem5727353 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term78 _120011 _120196 f x op).
Proof. exact (eq_refl (term78 _120011 _120196 f x op)). Qed.
Lemma lem5727354 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x op)) = ((term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op)).
Proof. exact (MK_COMB (@lem5727352 _120011 _120196 f x' op) (@lem5727353 _120011 _120196 f x op)). Qed.
Lemma lem5727355 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x)) = ((term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op)).
Proof. exact (TRANS (@lem5727349 _120011 _120196 x' f x op) (@lem5727354 _120011 _120196 x' f x op)). Qed.
Lemma lem5727356 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op).
Proof. exact (EQ_MP (@lem5727355 _120011 _120196 x' f x op) (@lem5727346 _120011 _120196 f op x' x h1)). Qed.
Lemma lem5727357 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) : term78 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5727356 _120011 _120196 f op x' x h2) (@lem5727270 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727399 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term599 _120011 _120196 f op) = (term599 _120011 _120196 f op).
Proof. exact (eq_refl (term599 _120011 _120196 f op)). Qed.
Lemma lem5727400 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x).
Proof. exact (MK_COMB (@lem5727399 _120011 _120196 f op) (@lem5727280 _120011 x' x h1)). Qed.
Lemma lem5727401 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term600 _120011 _120196 f op x) = (term78 _120011 _120196 f x op).
Proof. exact (eq_refl (term600 _120011 _120196 f op x)). Qed.
Lemma lem5727402 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term601 _120011 _120196 f op x') = (term601 _120011 _120196 f op x').
Proof. exact (eq_refl (term601 _120011 _120196 f op x')). Qed.
Lemma lem5727403 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x)) = ((term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x op)).
Proof. exact (MK_COMB (@lem5727402 _120011 _120196 f op x') (@lem5727401 _120011 _120196 f x op)). Qed.
Lemma lem5727404 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x' op).
Proof. exact (eq_refl (term600 _120011 _120196 f op x')). Qed.
Lemma lem5727405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5727406 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term601 _120011 _120196 f op x') = (term602 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5727405) (@lem5727404 _120011 _120196 f x' op)). Qed.
Lemma lem5727407 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term78 _120011 _120196 f x op).
Proof. exact (eq_refl (term78 _120011 _120196 f x op)). Qed.
Lemma lem5727408 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x op)) = ((term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op)).
Proof. exact (MK_COMB (@lem5727406 _120011 _120196 f x' op) (@lem5727407 _120011 _120196 f x op)). Qed.
Lemma lem5727409 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x)) = ((term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op)).
Proof. exact (TRANS (@lem5727403 _120011 _120196 x' f x op) (@lem5727408 _120011 _120196 x' f x op)). Qed.
Lemma lem5727410 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op).
Proof. exact (EQ_MP (@lem5727409 _120011 _120196 x' f x op) (@lem5727400 _120011 _120196 f op x' x h1)). Qed.
Lemma lem5727411 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) : term78 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5727410 _120011 _120196 f op x' x h2) (@lem5727278 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727412 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term603 _120011 _120196 f op) = (term603 _120011 _120196 f op).
Proof. exact (eq_refl (term603 _120011 _120196 f op)). Qed.
Lemma lem5727413 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x).
Proof. exact (MK_COMB (@lem5727412 _120011 _120196 f op) (@lem5727280 _120011 x' x h1)). Qed.
Lemma lem5727414 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term604 _120011 _120196 f op x) = ((f x) = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120011 _120196 f op x)). Qed.
Lemma lem5727415 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term605 _120011 _120196 f op x') = (term605 _120011 _120196 f op x').
Proof. exact (eq_refl (term605 _120011 _120196 f op x')). Qed.
Lemma lem5727416 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x)) = ((term604 _120011 _120196 f op x') = ((f x) = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5727415 _120011 _120196 f op x') (@lem5727414 _120011 _120196 f x op)). Qed.
Lemma lem5727417 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term604 _120011 _120196 f op x') = ((f x') = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120011 _120196 f op x')). Qed.
Lemma lem5727418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5727419 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term605 _120011 _120196 f op x') = (term606 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5727418) (@lem5727417 _120011 _120196 f x' op)). Qed.
Lemma lem5727420 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((f x) = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op)).
Proof. exact (eq_refl ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5727421 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = ((f x) = (@neutral _120196 op))) = (((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5727419 _120011 _120196 f x' op) (@lem5727420 _120011 _120196 f x op)). Qed.
Lemma lem5727422 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x)) = (((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op))).
Proof. exact (TRANS (@lem5727416 _120011 _120196 x' f x op) (@lem5727421 _120011 _120196 x' f x op)). Qed.
Lemma lem5727423 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : ((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op)).
Proof. exact (EQ_MP (@lem5727422 _120011 _120196 x' f x op) (@lem5727413 _120011 _120196 f op x' x h1)). Qed.
Lemma lem5727469 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727470 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120011 _120196 f x op.
Proof. exact (fun h0 : term78 _120011 _120196 f x op => @lem5727469 _120011 _120196 f x op h1). Qed.
Lemma lem5727472 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727473 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5727472 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5727474 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5727473 _120011 _120196 f x op) (@lem5727470 _120011 _120196 f x op h1)). Qed.
Lemma lem5727477 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5727479 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term609 _120011 _120196 f x op).
Proof. exact (@lem5727477 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5727482 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) : term609 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5727479 _120011 _120196 f x op) (@lem5727357 _120011 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5727485 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5727482 _120011 _120196 s f op x' x h1 h2 (@lem5727474 _120011 _120196 f x op h3)). Qed.
Lemma lem5727486 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5727485 _120011 _120196 s x' f x op h1 h2 h3). Qed.
Lemma lem5727488 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727489 : term610 = False.
Proof. exact (@lem5727488 False). Qed.
Lemma lem5727490 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727489) (@lem5727486 _120011 _120196 s x' f x op h1 h2 h3)). Qed.
Lemma lem5727514 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5727423 _120011 _120196 f op x' x h1) (@lem5727282 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727515 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x op.
Proof. exact (fun h0 : term78 _120011 _120196 f x op => @lem5727514 _120011 _120196 x f x' op h1 h2). Qed.
Lemma lem5727517 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727518 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5727517 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5727519 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5727518 _120011 _120196 f x op) (@lem5727515 _120011 _120196 x f x' op h1 h2)). Qed.
Lemma lem5727522 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5727524 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term609 _120011 _120196 f x op).
Proof. exact (@lem5727522 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5727527 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) : term609 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5727524 _120011 _120196 f x op) (@lem5727411 _120011 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5727530 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5727527 _120011 _120196 s f op x' x h1 h2 (@lem5727519 _120011 _120196 x f x' op h2 h3)). Qed.
Lemma lem5727531 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5727530 _120011 _120196 s x f x' op h1 h2 h3). Qed.
Lemma lem5727533 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727534 : term610 = False.
Proof. exact (@lem5727533 False). Qed.
Lemma lem5727580 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5727581 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : term611 _120011 x' s.
Proof. exact (fun h0 : term598 _120011 x' s => @lem5727580 _120011 x' s h1). Qed.
Lemma lem5727583 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727584 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term611 _120011 x' s) = (@IN _120011 x' s).
Proof. exact (@lem5727583 (@IN _120011 x' s)). Qed.
Lemma lem5727585 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (EQ_MP (@lem5727584 _120011 x' s) (@lem5727581 _120011 x' s h1)). Qed.
Lemma lem5727588 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5727590 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term598 _120011 x' s) = (term612 _120011 x' s).
Proof. exact (@lem5727588 (@IN _120011 x' s)). Qed.
Lemma lem5727593 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) : term612 _120011 x' s.
Proof. exact (EQ_MP (@lem5727590 _120011 x' s) (@lem5727290 _120011 x' s h1)). Qed.
Lemma lem5727596 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (@lem5727593 _120011 x' s h1 (@lem5727585 _120011 x' s h2)). Qed.
Lemma lem5727597 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : term610.
Proof. exact (fun h0 : ~ False => @lem5727596 _120011 x' s h1 h2). Qed.
Lemma lem5727599 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727600 : term610 = False.
Proof. exact (@lem5727599 False). Qed.
Lemma lem5727601 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727600) (@lem5727597 _120011 x' s h1 h2)). Qed.
Lemma lem5727646 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727647 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x' op.
Proof. exact (fun h0 : term78 _120011 _120196 f x' op => @lem5727646 _120011 _120196 f x' op h1). Qed.
Lemma lem5727649 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727650 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem5727649 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5727651 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5727650 _120011 _120196 f x' op) (@lem5727647 _120011 _120196 f x' op h1)). Qed.
Lemma lem5727654 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5727656 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x' op) = (term609 _120011 _120196 f x' op).
Proof. exact (@lem5727654 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5727659 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) : term609 _120011 _120196 f x' op.
Proof. exact (EQ_MP (@lem5727656 _120011 _120196 f x' op) (@lem5727294 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727662 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5727659 _120011 _120196 x s f x' op h1 (@lem5727651 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727663 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5727662 _120011 _120196 x s f x' op h1 h2). Qed.
Lemma lem5727665 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727666 : term610 = False.
Proof. exact (@lem5727665 False). Qed.
Lemma lem5727667 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727666) (@lem5727663 _120011 _120196 x s f x' op h1 h2)). Qed.
Lemma lem5727712 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : @IN _120011 x' s.
Proof. exact (proj1 (@lem5727159 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727713 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : term611 _120011 x' s.
Proof. exact (fun h0 : term598 _120011 x' s => @lem5727712 _120011 _120196 x s f x' op h1). Qed.
Lemma lem5727715 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727716 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term611 _120011 x' s) = (@IN _120011 x' s).
Proof. exact (@lem5727715 (@IN _120011 x' s)). Qed.
Lemma lem5727717 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : @IN _120011 x' s.
Proof. exact (EQ_MP (@lem5727716 _120011 x' s) (@lem5727713 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727720 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5727722 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term598 _120011 x' s) = (term612 _120011 x' s).
Proof. exact (@lem5727720 (@IN _120011 x' s)). Qed.
Lemma lem5727725 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term612 _120011 x' s.
Proof. exact (EQ_MP (@lem5727722 _120011 x' s) (@lem5727308 _120011 x x' s h1)). Qed.
Lemma lem5727728 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term577 _120011 x x' s) (h2 : term590 _120011 _120196 x s f x' op) : False.
Proof. exact (@lem5727725 _120011 x x' s h1 (@lem5727717 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5727729 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term577 _120011 x x' s) (h2 : term590 _120011 _120196 x s f x' op) : term610.
Proof. exact (fun h0 : ~ False => @lem5727728 _120011 _120196 x s f x' op h1 h2). Qed.
Lemma lem5727731 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727732 : term610 = False.
Proof. exact (@lem5727731 False). Qed.
Lemma lem5727733 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term577 _120011 x x' s) (h2 : term590 _120011 _120196 x s f x' op) : False.
Proof. exact (EQ_MP (@lem5727732) (@lem5727729 _120011 _120196 x s f x' op h1 h2)). Qed.
Lemma lem5727778 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5727779 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x' op.
Proof. exact (fun h0 : term78 _120011 _120196 f x' op => @lem5727778 _120011 _120196 f x' op h1). Qed.
Lemma lem5727781 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727782 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem5727781 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5727783 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5727782 _120011 _120196 f x' op) (@lem5727779 _120011 _120196 f x' op h1)). Qed.
Lemma lem5727786 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5727788 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x' op) = (term609 _120011 _120196 f x' op).
Proof. exact (@lem5727786 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5727791 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : term609 _120011 _120196 f x' op.
Proof. exact (EQ_MP (@lem5727788 _120011 _120196 f x' op) (@lem5727314 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727794 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5727791 _120011 _120196 x s f x' op h1 (@lem5727783 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727795 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5727794 _120011 _120196 x s f x' op h1 h2). Qed.
Lemma lem5727797 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5727798 : term610 = False.
Proof. exact (@lem5727797 False). Qed.
Lemma lem5727799 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727798) (@lem5727795 _120011 _120196 x s f x' op h1 h2)). Qed.
Lemma lem5727800 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727534) (@lem5727531 _120011 _120196 s x f x' op h1 h2 h3)). Qed.
Lemma lem5727801 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral _120196 op) => @lem5727490 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727344 _120011 _120196 f x op h3)). Qed.
Lemma lem5727803 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727801 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727344 _120011 _120196 f x op h3)). Qed.
Lemma lem5727804 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5727799 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727316 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727805 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727804 _120011 _120196 x s f x' op h1 h2) (@lem5727316 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727806 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5727667 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727298 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727807 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727806 _120011 _120196 x s f x' op h1 h2) (@lem5727298 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727808 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (term598 _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120011 x' s => @lem5727601 _120011 x' s h1 h2) (fun h3 : False => @lem5727290 _120011 x' s h1)). Qed.
Lemma lem5727809 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727808 _120011 x' s h1 h2) (@lem5727290 _120011 x' s h1)). Qed.
Lemma lem5727810 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (@IN _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120011 x' s => @lem5727809 _120011 x' s h1 h2) (fun h3 : False => @lem5727288 _120011 x' s h2)). Qed.
Lemma lem5727811 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727810 _120011 x' s h1 h2) (@lem5727288 _120011 x' s h2)). Qed.
Lemma lem5727812 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5727800 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5727282 _120011 _120196 f x' op h3)). Qed.
Lemma lem5727813 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727812 _120011 _120196 s x f x' op h1 h2 h3) (@lem5727282 _120011 _120196 f x' op h3)). Qed.
Lemma lem5727814 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5727813 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5727280 _120011 x' x h2)). Qed.
Lemma lem5727815 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727814 _120011 _120196 s x f x' op h1 h2 h3) (@lem5727280 _120011 x' x h2)). Qed.
Lemma lem5727816 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5727803 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727272 _120011 x' x h2)). Qed.
Lemma lem5727817 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727816 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727272 _120011 x' x h2)). Qed.
Lemma lem5727818 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral _120196 op) => @lem5727817 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727268 _120011 _120196 f x op h3)). Qed.
Lemma lem5727819 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727818 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727268 _120011 _120196 f x op h3)). Qed.
Lemma lem5727820 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5727805 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727266 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727821 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727820 _120011 _120196 x s f x' op h1 h2) (@lem5727266 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727822 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5727807 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727230 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727823 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727822 _120011 _120196 x s f x' op h1 h2) (@lem5727230 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727824 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (term598 _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120011 x' s => @lem5727811 _120011 x' s h1 h2) (fun h3 : False => @lem5727214 _120011 x' s h1)). Qed.
Lemma lem5727825 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727824 _120011 x' s h1 h2) (@lem5727214 _120011 x' s h1)). Qed.
Lemma lem5727826 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (@IN _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120011 x' s => @lem5727825 _120011 x' s h1 h2) (fun h3 : False => @lem5727210 _120011 x' s h2)). Qed.
Lemma lem5727827 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727826 _120011 x' s h1 h2) (@lem5727210 _120011 x' s h2)). Qed.
Lemma lem5727828 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5727815 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5727198 _120011 _120196 f x' op h3)). Qed.
Lemma lem5727829 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727828 _120011 _120196 s x f x' op h1 h2 h3) (@lem5727198 _120011 _120196 f x' op h3)). Qed.
Lemma lem5727830 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5727829 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5727194 _120011 x' x h2)). Qed.
Lemma lem5727831 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727830 _120011 _120196 s x f x' op h1 h2 h3) (@lem5727194 _120011 x' x h2)). Qed.
Lemma lem5727832 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5727819 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727178 _120011 x' x h2)). Qed.
Lemma lem5727833 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727832 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727178 _120011 x' x h2)). Qed.
Lemma lem5727834 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral _120196 op) => @lem5727833 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727170 _120011 _120196 f x op h3)). Qed.
Lemma lem5727835 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727834 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727170 _120011 _120196 f x op h3)). Qed.
Lemma lem5727836 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5727821 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727266 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727837 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727836 _120011 _120196 x s f x' op h1 h2) (@lem5727266 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727838 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5727823 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727230 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727839 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727838 _120011 _120196 x s f x' op h1 h2) (@lem5727230 _120011 _120196 f x' op h2)). Qed.
Lemma lem5727840 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (term598 _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120011 x' s => @lem5727827 _120011 x' s h1 h2) (fun h3 : False => @lem5727214 _120011 x' s h1)). Qed.
Lemma lem5727841 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727840 _120011 x' s h1 h2) (@lem5727214 _120011 x' s h1)). Qed.
Lemma lem5727842 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (@IN _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120011 x' s => @lem5727841 _120011 x' s h1 h2) (fun h3 : False => @lem5727210 _120011 x' s h2)). Qed.
Lemma lem5727843 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5727842 _120011 x' s h1 h2) (@lem5727210 _120011 x' s h2)). Qed.
Lemma lem5727844 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5727831 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5727198 _120011 _120196 f x' op h3)). Qed.
Lemma lem5727845 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727844 _120011 _120196 s x f x' op h1 h2 h3) (@lem5727198 _120011 _120196 f x' op h3)). Qed.
Lemma lem5727846 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5727845 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5727194 _120011 x' x h2)). Qed.
Lemma lem5727847 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727846 _120011 _120196 s x f x' op h1 h2 h3) (@lem5727194 _120011 x' x h2)). Qed.
Lemma lem5727848 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5727835 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727178 _120011 x' x h2)). Qed.
Lemma lem5727849 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727848 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727178 _120011 x' x h2)). Qed.
Lemma lem5727850 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral _120196 op) => @lem5727849 _120011 _120196 s x' f x op h1 h2 h3) (fun h4 : False => @lem5727170 _120011 _120196 f x op h3)). Qed.
Lemma lem5727851 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727850 _120011 _120196 s x' f x op h1 h2 h3) (@lem5727170 _120011 _120196 f x op h3)). Qed.
Lemma lem5727852 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term590 _120011 _120196 x s f x' op) : False.
Proof. exact (or_elim (@lem5727160 _120011 _120196 x s f x' op h1) (fun h0 : term577 _120011 x x' s => @lem5727733 _120011 _120196 x s f x' op h0 h1) (fun h0 : (f x') = (@neutral _120196 op) => @lem5727837 _120011 _120196 x s f x' op h1 h0)). Qed.
Lemma lem5727853 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (s : _120011 -> Prop) (h1 : term593 _120011 _120196 x s f x' op) (h2 : @IN _120011 x' s) : False.
Proof. exact (or_elim (@lem5727149 _120011 _120196 x s f x' op h1) (fun h0 : term598 _120011 x' s => @lem5727843 _120011 x' s h0 h2) (fun h0 : (f x') = (@neutral _120196 op) => @lem5727839 _120011 _120196 x s f x' op h1 h0)). Qed.
Lemma lem5727854 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (or_elim (@lem5727149 _120011 _120196 x s f x' op h1) (fun h0 : term598 _120011 x' s => @lem5727851 _120011 _120196 s x' f x op h1 h2 h3) (fun h0 : (f x') = (@neutral _120196 op) => @lem5727847 _120011 _120196 s x f x' op h1 h2 h0)). Qed.
Lemma lem5727855 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term593 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (or_elim (@lem5727152 _120011 _120196 x s f x' op h1) (fun h0 : x' = x => @lem5727854 _120011 _120196 s x' f x op h1 h0 h2) (fun h0 : @IN _120011 x' s => @lem5727853 _120011 _120196 x f op x' s h1 h0)). Qed.
Lemma lem5727856 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (or_elim (@lem5727146 _120011 _120196 x s f x' op h1) (fun h0 : term593 _120011 _120196 x s f x' op => @lem5727855 _120011 _120196 s x' f x op h0 h2) (fun h0 : term590 _120011 _120196 x s f x' op => @lem5727852 _120011 _120196 x s f x' op h0)). Qed.
Lemma lem5727857 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5727856 _120011 _120196 s x' f x op h1 h2) (fun h3 : False => @lem5727042 _120011 _120196 f x op h2)). Qed.
Lemma lem5727858 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727857 _120011 _120196 s x' f x op h1 h2) (@lem5727042 _120011 _120196 f x op h2)). Qed.
Lemma lem5727859 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5727858 _120011 _120196 s x' f x op h1 h2) (fun h3 : False => @lem5726978 _120011 _120196 f x op h2)). Qed.
Lemma lem5727860 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727859 _120011 _120196 s x' f x op h1 h2) (@lem5726978 _120011 _120196 f x op h2)). Qed.
Lemma lem5727861 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : (term549 _120011 _120196 x s f x' op) = False.
Proof. exact (prop_ext (fun h3 : term549 _120011 _120196 x s f x' op => @lem5727860 _120011 _120196 s x' f x op h1 h2) (fun h3 : False => @lem5726972 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727862 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727861 _120011 _120196 s x' f x op h1 h2) (@lem5726972 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727863 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term548 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term549 _120011 _120196 x s f x' op => @lem5727862 _120011 _120196 s x' f x op h0 h1). Qed.
Lemma lem5727864 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op).
Proof. exact (EQ_MP (@lem5726971 _120011 _120196 x s f x' op) (@lem5727863 _120011 _120196 s x' f x op h1)). Qed.
Lemma lem5727865 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term541 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : (f x) = (@neutral _120196 op) => @lem5727864 _120011 _120196 s x' f x op h0). Qed.
Lemma lem5727870 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term559 _120011 _120196 s f x' op.
Proof. exact (fun x : _120011 => @lem5727865 _120011 _120196 x s f x' op). Qed.
Lemma lem5727875 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term563 _120011 _120196 f x' op.
Proof. exact (fun s : _120011 -> Prop => @lem5727870 _120011 _120196 s f x' op). Qed.
Lemma lem5727880 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : term567 _120011 _120196 x' op.
Proof. exact (fun f : _120011 -> _120196 => @lem5727875 _120011 _120196 f x' op). Qed.
Lemma lem5727885 {_120011 _120196 : Type'} (op : type1400 _120196) : term571 _120011 _120196 op.
Proof. exact (fun x' : _120011 => @lem5727880 _120011 _120196 x' op). Qed.
Lemma lem5727890 {_120011 _120196 : Type'} : term575 _120011 _120196.
Proof. exact (fun op : type1400 _120196 => @lem5727885 _120011 _120196 op). Qed.
Lemma lem5727891 {_120011 _120196 : Type'} : term574 _120011 _120196.
Proof. exact (EQ_MP (@lem5726966 _120011 _120196) (@lem5727890 _120011 _120196)). Qed.
Lemma lem5727892 {_120011 _120196 : Type'} (op : type1400 _120196) : term613 _120011 _120196 op.
Proof. exact (@lem5727891 _120011 _120196 op). Qed.
Lemma lem5727893 {_120011 _120196 : Type'} (op : type1400 _120196) : (term613 _120011 _120196 op) = (term570 _120011 _120196 op).
Proof. exact (eq_refl (term613 _120011 _120196 op)). Qed.
Lemma lem5727894 {_120011 _120196 : Type'} (op : type1400 _120196) : term570 _120011 _120196 op.
Proof. exact (EQ_MP (@lem5727893 _120011 _120196 op) (@lem5727892 _120011 _120196 op)). Qed.
Lemma lem5727895 {_120011 _120196 : Type'} (op : type1400 _120196) (x' : _120011) : term614 _120011 _120196 op x'.
Proof. exact (@lem5727894 _120011 _120196 op x'). Qed.
Lemma lem5727896 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term614 _120011 _120196 op x') = (term566 _120011 _120196 x' op).
Proof. exact (eq_refl (term614 _120011 _120196 op x')). Qed.
Lemma lem5727897 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : term566 _120011 _120196 x' op.
Proof. exact (EQ_MP (@lem5727896 _120011 _120196 x' op) (@lem5727895 _120011 _120196 op x')). Qed.
Lemma lem5727898 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) (f : _120011 -> _120196) : term615 _120011 _120196 x' op f.
Proof. exact (@lem5727897 _120011 _120196 x' op f). Qed.
Lemma lem5727899 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term615 _120011 _120196 x' op f) = (term562 _120011 _120196 f x' op).
Proof. exact (eq_refl (term615 _120011 _120196 x' op f)). Qed.
Lemma lem5727900 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term562 _120011 _120196 f x' op.
Proof. exact (EQ_MP (@lem5727899 _120011 _120196 f x' op) (@lem5727898 _120011 _120196 x' op f)). Qed.
Lemma lem5727901 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (s : _120011 -> Prop) : term616 _120011 _120196 f x' op s.
Proof. exact (@lem5727900 _120011 _120196 f x' op s). Qed.
Lemma lem5727902 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term616 _120011 _120196 f x' op s) = (term558 _120011 _120196 s f x' op).
Proof. exact (eq_refl (term616 _120011 _120196 f x' op s)). Qed.
Lemma lem5727903 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term558 _120011 _120196 s f x' op.
Proof. exact (EQ_MP (@lem5727902 _120011 _120196 s f x' op) (@lem5727901 _120011 _120196 f x' op s)). Qed.
Lemma lem5727904 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (x : _120011) : term617 _120011 _120196 s f x' op x.
Proof. exact (@lem5727903 _120011 _120196 s f x' op x). Qed.
Lemma lem5727905 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term617 _120011 _120196 s f x' op x) = (term550 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term617 _120011 _120196 s f x' op x)). Qed.
Lemma lem5727906 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term550 _120011 _120196 x s f x' op.
Proof. exact (EQ_MP (@lem5727905 _120011 _120196 x s f x' op) (@lem5727904 _120011 _120196 s f x' op x)). Qed.
Lemma lem5727908 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term550 _120011 _120196 x s f x' op.
Proof. exact (@lem5726806 _120011 _120196 x s f x' op (@lem5727906 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727909 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term548 _120011 _120196 x s f x' op.
Proof. exact (@lem5727908 _120011 _120196 x s f x' op (@lem5726752 _120011 _120196 f x op h1)). Qed.
Lemma lem5727910 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5727909 _120011 _120196 s x' f x op h2 (@lem5726790 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727911 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : (term549 _120011 _120196 x s f x' op) = False.
Proof. exact (prop_ext (fun h3 : term549 _120011 _120196 x s f x' op => @lem5727910 _120011 _120196 s x' f x op h1 h2) (fun h3 : False => @lem5726790 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727912 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term549 _120011 _120196 x s f x' op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5727911 _120011 _120196 s x' f x op h1 h2) (@lem5726790 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727913 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term548 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term549 _120011 _120196 x s f x' op => @lem5727912 _120011 _120196 s x' f x op h0 h1). Qed.
Lemma lem5727916 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5727917 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)) = (term618 _120011 _120196 x s f x' op).
Proof. exact (@lem5727916 ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op))). Qed.
Lemma lem5727918 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term618 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)).
Proof. exact (SYM (@lem5727917 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727919 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term619 _120011 _120196 x s f x' op) : term619 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727922 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term620 _120011 _120196 x s f x' op) : term620 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727923 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term621 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term620 _120011 _120196 x s f x' op => @lem5727922 _120011 _120196 x s f x' op h0). Qed.
Lemma lem5727924 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term621 _120011 _120196 x s f x' op) : term621 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727925 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term620 _120011 _120196 x s f x' op) : term620 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727926 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term620 _120011 _120196 x s f x' op) (h2 : term621 _120011 _120196 x s f x' op) : term620 _120011 _120196 x s f x' op.
Proof. exact (@lem5727924 _120011 _120196 x s f x' op h2 (@lem5727925 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5727927 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term620 _120011 _120196 x s f x' op) : term622 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term621 _120011 _120196 x s f x' op => @lem5727926 _120011 _120196 x s f x' op h1 h0). Qed.
Lemma lem5727928 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term621 _120011 _120196 x s f x' op) : term621 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5727929 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term620 _120011 _120196 x s f x' op) (h2 : term621 _120011 _120196 x s f x' op) : term620 _120011 _120196 x s f x' op.
Proof. exact (@lem5727927 _120011 _120196 x s f x' op h1 (@lem5727928 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5727930 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term621 _120011 _120196 x s f x' op) : term621 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term620 _120011 _120196 x s f x' op => @lem5727929 _120011 _120196 x s f x' op h0 h1). Qed.
Lemma lem5727931 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term623 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term621 _120011 _120196 x s f x' op => @lem5727930 _120011 _120196 x s f x' op h0). Qed.
Lemma lem5727934 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term621 _120011 _120196 x s f x' op.
Proof. exact (@lem5727931 _120011 _120196 x s f x' op (@lem5727923 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727935 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term621 _120011 _120196 x s f x' op.
Proof. exact (@lem5727934 _120011 _120196 x s f x' op). Qed.
Lemma lem5727959 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5727960 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term618 _120011 _120196 x s f x' op) = (term624 _120011 _120196 x s f x' op).
Proof. exact (@lem5727959 (term619 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727962 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5727963 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term624 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)).
Proof. exact (@lem5727962 ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op))). Qed.
Lemma lem5727964 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term618 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)).
Proof. exact (TRANS (@lem5727960 _120011 _120196 x s f x' op) (@lem5727963 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727973 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term535 _120011 _120196 f x op) = (term535 _120011 _120196 f x op).
Proof. exact (eq_refl (term535 _120011 _120196 f x op)). Qed.
Lemma lem5727974 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term620 _120011 _120196 x s f x' op) = (term537 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5727973 _120011 _120196 f x op) (@lem5727964 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727977 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term625 _120011 _120196 s f x' op) = (term626 _120011 _120196 s f x' op).
Proof. exact (fun_ext (fun x : _120011 => @lem5727974 _120011 _120196 x s f x' op)). Qed.
Lemma lem5727978 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5727979 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term627 _120011 _120196 s f x' op) = (term628 _120011 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5727978 _120011) (@lem5727977 _120011 _120196 s f x' op)). Qed.
Lemma lem5727984 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term629 _120011 _120196 f x' op) = (term630 _120011 _120196 f x' op).
Proof. exact (fun_ext (fun s : _120011 -> Prop => @lem5727979 _120011 _120196 s f x' op)). Qed.
Lemma lem5727985 {_120011 : Type'} : (@all (_120011 -> Prop)) = (@all (_120011 -> Prop)).
Proof. exact (eq_refl (@all (_120011 -> Prop))). Qed.
Lemma lem5727986 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term631 _120011 _120196 f x' op) = (term632 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5727985 _120011) (@lem5727984 _120011 _120196 f x' op)). Qed.
Lemma lem5727991 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term633 _120011 _120196 x' op) = (term634 _120011 _120196 x' op).
Proof. exact (fun_ext (fun f : _120011 -> _120196 => @lem5727986 _120011 _120196 f x' op)). Qed.
Lemma lem5727992 {_120011 _120196 : Type'} : (@all (_120011 -> _120196)) = (@all (_120011 -> _120196)).
Proof. exact (eq_refl (@all (_120011 -> _120196))). Qed.
Lemma lem5727993 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term635 _120011 _120196 x' op) = (term636 _120011 _120196 x' op).
Proof. exact (MK_COMB (@lem5727992 _120011 _120196) (@lem5727991 _120011 _120196 x' op)). Qed.
Lemma lem5727998 {_120011 _120196 : Type'} (op : type1400 _120196) : (term637 _120011 _120196 op) = (term638 _120011 _120196 op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5727993 _120011 _120196 x' op)). Qed.
Lemma lem5727999 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5728000 {_120011 _120196 : Type'} (op : type1400 _120196) : (term639 _120011 _120196 op) = (term640 _120011 _120196 op).
Proof. exact (MK_COMB (@lem5727999 _120011) (@lem5727998 _120011 _120196 op)). Qed.
Lemma lem5728005 {_120011 _120196 : Type'} : (term641 _120011 _120196) = (term642 _120011 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5728000 _120011 _120196 op)). Qed.
Lemma lem5728006 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5728015 {_120011 _120196 : Type'} : (term643 _120011 _120196) = (term644 _120011 _120196).
Proof. exact (MK_COMB (@lem5728006 _120196) (@lem5728005 _120011 _120196)). Qed.
Lemma lem5728046 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term537 _120011 _120196 x s f x' op) = (term537 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term537 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728047 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term626 _120011 _120196 s f x' op) = (term626 _120011 _120196 s f x' op).
Proof. exact (fun_ext (fun x : _120011 => @lem5728046 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728048 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5728049 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term628 _120011 _120196 s f x' op) = (term628 _120011 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5728048 _120011) (@lem5728047 _120011 _120196 s f x' op)). Qed.
Lemma lem5728050 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term630 _120011 _120196 f x' op) = (term630 _120011 _120196 f x' op).
Proof. exact (fun_ext (fun s : _120011 -> Prop => @lem5728049 _120011 _120196 s f x' op)). Qed.
Lemma lem5728051 {_120011 : Type'} : (@all (_120011 -> Prop)) = (@all (_120011 -> Prop)).
Proof. exact (eq_refl (@all (_120011 -> Prop))). Qed.
Lemma lem5728052 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term632 _120011 _120196 f x' op) = (term632 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5728051 _120011) (@lem5728050 _120011 _120196 f x' op)). Qed.
Lemma lem5728053 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term634 _120011 _120196 x' op) = (term634 _120011 _120196 x' op).
Proof. exact (fun_ext (fun f : _120011 -> _120196 => @lem5728052 _120011 _120196 f x' op)). Qed.
Lemma lem5728054 {_120011 _120196 : Type'} : (@all (_120011 -> _120196)) = (@all (_120011 -> _120196)).
Proof. exact (eq_refl (@all (_120011 -> _120196))). Qed.
Lemma lem5728055 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term636 _120011 _120196 x' op) = (term636 _120011 _120196 x' op).
Proof. exact (MK_COMB (@lem5728054 _120011 _120196) (@lem5728053 _120011 _120196 x' op)). Qed.
Lemma lem5728056 {_120011 _120196 : Type'} (op : type1400 _120196) : (term638 _120011 _120196 op) = (term638 _120011 _120196 op).
Proof. exact (fun_ext (fun x' : _120011 => @lem5728055 _120011 _120196 x' op)). Qed.
Lemma lem5728057 {_120011 : Type'} : (@all _120011) = (@all _120011).
Proof. exact (eq_refl (@all _120011)). Qed.
Lemma lem5728058 {_120011 _120196 : Type'} (op : type1400 _120196) : (term640 _120011 _120196 op) = (term640 _120011 _120196 op).
Proof. exact (MK_COMB (@lem5728057 _120011) (@lem5728056 _120011 _120196 op)). Qed.
Lemma lem5728059 {_120011 _120196 : Type'} : (term642 _120011 _120196) = (term642 _120011 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5728058 _120011 _120196 op)). Qed.
Lemma lem5728060 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5728061 {_120011 _120196 : Type'} : (term644 _120011 _120196) = (term644 _120011 _120196).
Proof. exact (MK_COMB (@lem5728060 _120196) (@lem5728059 _120011 _120196)). Qed.
Lemma lem5728104 {_120011 _120196 : Type'} : (term643 _120011 _120196) = (term644 _120011 _120196).
Proof. exact (TRANS (@lem5728015 _120011 _120196) (@lem5728061 _120011 _120196)). Qed.
Lemma lem5728105 {_120011 _120196 : Type'} : (term644 _120011 _120196) = (term643 _120011 _120196).
Proof. exact (SYM (@lem5728104 _120011 _120196)). Qed.
Lemma lem5728108 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5728109 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)) = (term618 _120011 _120196 x s f x' op).
Proof. exact (@lem5728108 ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op))). Qed.
Lemma lem5728110 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term618 _120011 _120196 x s f x' op) = ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)).
Proof. exact (SYM (@lem5728109 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728111 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term619 _120011 _120196 x s f x' op) : term619 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5728117 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term78 _120011 _120196 f x op.
Proof. exact (h1). Qed.
Lemma lem5728126 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) : (term576 _120011 x x' s) = (term577 _120011 x x' s).
Proof. exact (@lem17160 (x' = x) (@IN _120011 x' s)). Qed.
Lemma lem5728133 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term578 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5728134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5728135 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) : (term579 _120011 x x' s) = (term580 _120011 x x' s).
Proof. exact (MK_COMB (@lem5728134) (@lem5728126 _120011 x x' s)). Qed.
Lemma lem5728136 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term581 _120011 _120196 x s f x' op) = (term582 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728135 _120011 x x' s) (@lem5728133 _120011 _120196 f x' op)). Qed.
Lemma lem5728137 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term583 _120011 _120196 x s f x' op) = (term581 _120011 _120196 x s f x' op).
Proof. exact (@lem17045 (term59 _120011 x x' s) (term78 _120011 _120196 f x' op)). Qed.
Lemma lem5728138 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term583 _120011 _120196 x s f x' op) = (term582 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5728137 _120011 _120196 x s f x' op) (@lem5728136 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728149 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term578 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5728151 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term584 _120011 x' s) = (term584 _120011 x' s).
Proof. exact (eq_refl (term584 _120011 x' s)). Qed.
Lemma lem5728152 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term585 _120011 _120196 s f x' op) = (term586 _120011 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5728151 _120011 x' s) (@lem5728149 _120011 _120196 f x' op)). Qed.
Lemma lem5728153 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term404 _120011 _120196 s f x' op) = (term585 _120011 _120196 s f x' op).
Proof. exact (@lem17045 (@IN _120011 x' s) (term78 _120011 _120196 f x' op)). Qed.
Lemma lem5728154 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term404 _120011 _120196 s f x' op) = (term586 _120011 _120196 s f x' op).
Proof. exact (TRANS (@lem5728153 _120011 _120196 s f x' op) (@lem5728152 _120011 _120196 s f x' op)). Qed.
Lemma lem5728159 {_120011 : Type'} (x' : _120011) (x : _120011) : (term645 _120011 x' x) = (term645 _120011 x' x).
Proof. exact (eq_refl (term645 _120011 x' x)). Qed.
Lemma lem5728160 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term646 _120011 _120196 x s f x' op) = (term647 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728159 _120011 x' x) (@lem5728154 _120011 _120196 s f x' op)). Qed.
Lemma lem5728161 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term648 _120011 _120196 x s f x' op) = (term646 _120011 _120196 x s f x' op).
Proof. exact (@lem17160 (x' = x) (term158 _120011 _120196 s f x' op)). Qed.
Lemma lem5728162 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term648 _120011 _120196 x s f x' op) = (term647 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5728161 _120011 _120196 x s f x' op) (@lem5728160 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728165 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term178 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term178 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5728167 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term587 _120011 _120196 x s f x' op) = (term588 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728166) (@lem5728138 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728168 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term649 _120011 _120196 x s f x' op) = (term650 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728167 _120011 _120196 x s f x' op) (@lem5728165 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728170 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term591 _120011 _120196 x s f x' op) = (term591 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term591 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728171 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term651 _120011 _120196 x s f x' op) = (term652 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728170 _120011 _120196 x s f x' op) (@lem5728162 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5728173 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term653 _120011 _120196 x s f x' op) = (term654 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728172) (@lem5728171 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728174 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term655 _120011 _120196 x s f x' op) = (term656 _120011 _120196 x s f x' op).
Proof. exact (MK_COMB (@lem5728173 _120011 _120196 x s f x' op) (@lem5728168 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728175 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term619 _120011 _120196 x s f x' op) = (term655 _120011 _120196 x s f x' op).
Proof. exact (@lem17646 (term121 _120011 _120196 x s f x' op) (term178 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728180 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term619 _120011 _120196 x s f x' op) = (term656 _120011 _120196 x s f x' op).
Proof. exact (TRANS (@lem5728175 _120011 _120196 x s f x' op) (@lem5728174 _120011 _120196 x s f x' op)). Qed.
Lemma lem5728193 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term78 _120011 _120196 f x op.
Proof. exact (h1). Qed.
Lemma lem5728315 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term619 _120011 _120196 x s f x' op) : term656 _120011 _120196 x s f x' op.
Proof. exact (EQ_MP (@lem5728180 _120011 _120196 x s f x' op) (@lem5728111 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728316 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term652 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5728317 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term650 _120011 _120196 x s f x' op) : term650 _120011 _120196 x s f x' op.
Proof. exact (h1). Qed.
Lemma lem5728318 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term647 _120011 _120196 x s f x' op.
Proof. exact (proj2 (@lem5728316 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728319 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term121 _120011 _120196 x s f x' op.
Proof. exact (proj1 (@lem5728316 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728320 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term586 _120011 _120196 s f x' op.
Proof. exact (proj2 (@lem5728318 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728323 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term59 _120011 x x' s.
Proof. exact (proj1 (@lem5728319 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728330 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term650 _120011 _120196 x s f x' op) : term178 _120011 _120196 x s f x' op.
Proof. exact (proj2 (@lem5728317 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728331 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term650 _120011 _120196 x s f x' op) : term582 _120011 _120196 x s f x' op.
Proof. exact (proj1 (@lem5728317 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728333 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) : term158 _120011 _120196 s f x' op.
Proof. exact (h1). Qed.
Lemma lem5728334 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term577 _120011 x x' s.
Proof. exact (h1). Qed.
Lemma lem5728340 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term577 _120011 x x' s.
Proof. exact (h1). Qed.
Lemma lem5728359 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728379 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728383 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728399 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5728403 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) : term598 _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5728423 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728431 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728443 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term78 _120011 _120196 f x op.
Proof. exact (h1). Qed.
Lemma lem5728447 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728451 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728487 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728491 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term238 _120011 x' x.
Proof. exact (proj1 (@lem5728318 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728495 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728503 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5728319 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728505 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728507 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728515 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5728517 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) : term598 _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5728523 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5728319 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728527 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728531 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728533 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term238 _120011 x' x.
Proof. exact (proj1 (@lem5728334 _120011 x x' s h1)). Qed.
Lemma lem5728537 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term78 _120011 _120196 f x op.
Proof. exact (h1). Qed.
Lemma lem5728539 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5728541 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728551 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term598 _120011 x' s.
Proof. exact (proj2 (@lem5728340 _120011 x x' s h1)). Qed.
Lemma lem5728557 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) : term78 _120011 _120196 f x' op.
Proof. exact (proj2 (@lem5728333 _120011 _120196 s f x' op h1)). Qed.
Lemma lem5728559 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5728588 {_120011 : Type'} (x : _120011) : (term657 _120011 x) = (term657 _120011 x).
Proof. exact (eq_refl (term657 _120011 x)). Qed.
Lemma lem5728589 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : (term658 _120011 x x') = (term659 _120011 x).
Proof. exact (MK_COMB (@lem5728588 _120011 x) (@lem5728495 _120011 x' x h1)). Qed.
Lemma lem5728590 {_120011 : Type'} (x : _120011) : (term659 _120011 x) = (term660 _120011 x).
Proof. exact (eq_refl (term659 _120011 x)). Qed.
Lemma lem5728591 {_120011 : Type'} (x : _120011) (x' : _120011) : (term661 _120011 x x') = (term661 _120011 x x').
Proof. exact (eq_refl (term661 _120011 x x')). Qed.
Lemma lem5728592 {_120011 : Type'} (x' : _120011) (x : _120011) : ((term658 _120011 x x') = (term659 _120011 x)) = ((term658 _120011 x x') = (term660 _120011 x)).
Proof. exact (MK_COMB (@lem5728591 _120011 x x') (@lem5728590 _120011 x)). Qed.
Lemma lem5728593 {_120011 : Type'} (x' : _120011) (x : _120011) : (term658 _120011 x x') = (term238 _120011 x' x).
Proof. exact (eq_refl (term658 _120011 x x')). Qed.
Lemma lem5728594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5728595 {_120011 : Type'} (x' : _120011) (x : _120011) : (term661 _120011 x x') = (term662 _120011 x' x).
Proof. exact (MK_COMB (@lem5728594) (@lem5728593 _120011 x' x)). Qed.
Lemma lem5728596 {_120011 : Type'} (x : _120011) : (term660 _120011 x) = (term660 _120011 x).
Proof. exact (eq_refl (term660 _120011 x)). Qed.
Lemma lem5728597 {_120011 : Type'} (x' : _120011) (x : _120011) : ((term658 _120011 x x') = (term660 _120011 x)) = ((term238 _120011 x' x) = (term660 _120011 x)).
Proof. exact (MK_COMB (@lem5728595 _120011 x' x) (@lem5728596 _120011 x)). Qed.
Lemma lem5728598 {_120011 : Type'} (x' : _120011) (x : _120011) : ((term658 _120011 x x') = (term659 _120011 x)) = ((term238 _120011 x' x) = (term660 _120011 x)).
Proof. exact (TRANS (@lem5728592 _120011 x' x) (@lem5728597 _120011 x' x)). Qed.
Lemma lem5728599 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : (term238 _120011 x' x) = (term660 _120011 x).
Proof. exact (EQ_MP (@lem5728598 _120011 x' x) (@lem5728589 _120011 x' x h1)). Qed.
Lemma lem5728600 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : term660 _120011 x.
Proof. exact (EQ_MP (@lem5728599 _120011 x' x h2) (@lem5728491 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728668 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term599 _120011 _120196 f op) = (term599 _120011 _120196 f op).
Proof. exact (eq_refl (term599 _120011 _120196 f op)). Qed.
Lemma lem5728669 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x).
Proof. exact (MK_COMB (@lem5728668 _120011 _120196 f op) (@lem5728505 _120011 x' x h1)). Qed.
Lemma lem5728670 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term600 _120011 _120196 f op x) = (term78 _120011 _120196 f x op).
Proof. exact (eq_refl (term600 _120011 _120196 f op x)). Qed.
Lemma lem5728671 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term601 _120011 _120196 f op x') = (term601 _120011 _120196 f op x').
Proof. exact (eq_refl (term601 _120011 _120196 f op x')). Qed.
Lemma lem5728672 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x)) = ((term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x op)).
Proof. exact (MK_COMB (@lem5728671 _120011 _120196 f op x') (@lem5728670 _120011 _120196 f x op)). Qed.
Lemma lem5728673 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x' op).
Proof. exact (eq_refl (term600 _120011 _120196 f op x')). Qed.
Lemma lem5728674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5728675 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term601 _120011 _120196 f op x') = (term602 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5728674) (@lem5728673 _120011 _120196 f x' op)). Qed.
Lemma lem5728676 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term78 _120011 _120196 f x op).
Proof. exact (eq_refl (term78 _120011 _120196 f x op)). Qed.
Lemma lem5728677 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term78 _120011 _120196 f x op)) = ((term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op)).
Proof. exact (MK_COMB (@lem5728675 _120011 _120196 f x' op) (@lem5728676 _120011 _120196 f x op)). Qed.
Lemma lem5728678 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term600 _120011 _120196 f op x') = (term600 _120011 _120196 f op x)) = ((term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op)).
Proof. exact (TRANS (@lem5728672 _120011 _120196 x' f x op) (@lem5728677 _120011 _120196 x' f x op)). Qed.
Lemma lem5728679 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term78 _120011 _120196 f x' op) = (term78 _120011 _120196 f x op).
Proof. exact (EQ_MP (@lem5728678 _120011 _120196 x' f x op) (@lem5728669 _120011 _120196 f op x' x h1)). Qed.
Lemma lem5728680 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : term78 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5728679 _120011 _120196 f op x' x h2) (@lem5728503 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5728681 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term603 _120011 _120196 f op) = (term603 _120011 _120196 f op).
Proof. exact (eq_refl (term603 _120011 _120196 f op)). Qed.
Lemma lem5728682 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x).
Proof. exact (MK_COMB (@lem5728681 _120011 _120196 f op) (@lem5728505 _120011 x' x h1)). Qed.
Lemma lem5728683 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term604 _120011 _120196 f op x) = ((f x) = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120011 _120196 f op x)). Qed.
Lemma lem5728684 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term605 _120011 _120196 f op x') = (term605 _120011 _120196 f op x').
Proof. exact (eq_refl (term605 _120011 _120196 f op x')). Qed.
Lemma lem5728685 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x)) = ((term604 _120011 _120196 f op x') = ((f x) = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5728684 _120011 _120196 f op x') (@lem5728683 _120011 _120196 f x op)). Qed.
Lemma lem5728686 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term604 _120011 _120196 f op x') = ((f x') = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120011 _120196 f op x')). Qed.
Lemma lem5728687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5728688 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term605 _120011 _120196 f op x') = (term606 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5728687) (@lem5728686 _120011 _120196 f x' op)). Qed.
Lemma lem5728689 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((f x) = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op)).
Proof. exact (eq_refl ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5728690 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = ((f x) = (@neutral _120196 op))) = (((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5728688 _120011 _120196 f x' op) (@lem5728689 _120011 _120196 f x op)). Qed.
Lemma lem5728691 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x)) = (((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op))).
Proof. exact (TRANS (@lem5728685 _120011 _120196 x' f x op) (@lem5728690 _120011 _120196 x' f x op)). Qed.
Lemma lem5728692 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : ((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op)).
Proof. exact (EQ_MP (@lem5728691 _120011 _120196 x' f x op) (@lem5728682 _120011 _120196 f op x' x h1)). Qed.
Lemma lem5728722 {_120011 : Type'} (x : _120011) : (term657 _120011 x) = (term657 _120011 x).
Proof. exact (eq_refl (term657 _120011 x)). Qed.
Lemma lem5728723 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : (term658 _120011 x x') = (term659 _120011 x).
Proof. exact (MK_COMB (@lem5728722 _120011 x) (@lem5728531 _120011 x' x h1)). Qed.
Lemma lem5728724 {_120011 : Type'} (x : _120011) : (term659 _120011 x) = (term660 _120011 x).
Proof. exact (eq_refl (term659 _120011 x)). Qed.
Lemma lem5728725 {_120011 : Type'} (x : _120011) (x' : _120011) : (term661 _120011 x x') = (term661 _120011 x x').
Proof. exact (eq_refl (term661 _120011 x x')). Qed.
Lemma lem5728726 {_120011 : Type'} (x' : _120011) (x : _120011) : ((term658 _120011 x x') = (term659 _120011 x)) = ((term658 _120011 x x') = (term660 _120011 x)).
Proof. exact (MK_COMB (@lem5728725 _120011 x x') (@lem5728724 _120011 x)). Qed.
Lemma lem5728727 {_120011 : Type'} (x' : _120011) (x : _120011) : (term658 _120011 x x') = (term238 _120011 x' x).
Proof. exact (eq_refl (term658 _120011 x x')). Qed.
Lemma lem5728728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5728729 {_120011 : Type'} (x' : _120011) (x : _120011) : (term661 _120011 x x') = (term662 _120011 x' x).
Proof. exact (MK_COMB (@lem5728728) (@lem5728727 _120011 x' x)). Qed.
Lemma lem5728730 {_120011 : Type'} (x : _120011) : (term660 _120011 x) = (term660 _120011 x).
Proof. exact (eq_refl (term660 _120011 x)). Qed.
Lemma lem5728731 {_120011 : Type'} (x' : _120011) (x : _120011) : ((term658 _120011 x x') = (term660 _120011 x)) = ((term238 _120011 x' x) = (term660 _120011 x)).
Proof. exact (MK_COMB (@lem5728729 _120011 x' x) (@lem5728730 _120011 x)). Qed.
Lemma lem5728732 {_120011 : Type'} (x' : _120011) (x : _120011) : ((term658 _120011 x x') = (term659 _120011 x)) = ((term238 _120011 x' x) = (term660 _120011 x)).
Proof. exact (TRANS (@lem5728726 _120011 x' x) (@lem5728731 _120011 x' x)). Qed.
Lemma lem5728733 {_120011 : Type'} (x' : _120011) (x : _120011) (h1 : x' = x) : (term238 _120011 x' x) = (term660 _120011 x).
Proof. exact (EQ_MP (@lem5728732 _120011 x' x) (@lem5728723 _120011 x' x h1)). Qed.
Lemma lem5728734 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : term660 _120011 x.
Proof. exact (EQ_MP (@lem5728733 _120011 x' x h2) (@lem5728533 _120011 x x' s h1)). Qed.
Lemma lem5728775 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term78 _120011 _120196 f x op.
Proof. exact (h1). Qed.
Lemma lem5728776 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : (term603 _120011 _120196 f op) = (term603 _120011 _120196 f op).
Proof. exact (eq_refl (term603 _120011 _120196 f op)). Qed.
Lemma lem5728777 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : (term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x).
Proof. exact (MK_COMB (@lem5728776 _120011 _120196 f op) (@lem5728539 _120011 x' x h1)). Qed.
Lemma lem5728778 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term604 _120011 _120196 f op x) = ((f x) = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120011 _120196 f op x)). Qed.
Lemma lem5728779 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) : (term605 _120011 _120196 f op x') = (term605 _120011 _120196 f op x').
Proof. exact (eq_refl (term605 _120011 _120196 f op x')). Qed.
Lemma lem5728780 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x)) = ((term604 _120011 _120196 f op x') = ((f x) = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5728779 _120011 _120196 f op x') (@lem5728778 _120011 _120196 f x op)). Qed.
Lemma lem5728781 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term604 _120011 _120196 f op x') = ((f x') = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120011 _120196 f op x')). Qed.
Lemma lem5728782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5728783 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term605 _120011 _120196 f op x') = (term606 _120011 _120196 f x' op).
Proof. exact (MK_COMB (@lem5728782) (@lem5728781 _120011 _120196 f x' op)). Qed.
Lemma lem5728784 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((f x) = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op)).
Proof. exact (eq_refl ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5728785 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = ((f x) = (@neutral _120196 op))) = (((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5728783 _120011 _120196 f x' op) (@lem5728784 _120011 _120196 f x op)). Qed.
Lemma lem5728786 {_120011 _120196 : Type'} (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : ((term604 _120011 _120196 f op x') = (term604 _120011 _120196 f op x)) = (((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op))).
Proof. exact (TRANS (@lem5728780 _120011 _120196 x' f x op) (@lem5728785 _120011 _120196 x' f x op)). Qed.
Lemma lem5728787 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : x' = x) : ((f x') = (@neutral _120196 op)) = ((f x) = (@neutral _120196 op)).
Proof. exact (EQ_MP (@lem5728786 _120011 _120196 x' f x op) (@lem5728777 _120011 _120196 f op x' x h1)). Qed.
Lemma lem5728833 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (@lem21386 _120011 x). Qed.
Lemma lem5728834 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (@lem5728833 _120011 x). Qed.
Lemma lem5728835 {_120011 : Type'} (x : _120011) : term663 _120011 x.
Proof. exact (fun h0 : term660 _120011 x => @lem5728834 _120011 x). Qed.
Lemma lem5728837 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5728838 {_120011 : Type'} (x : _120011) : (term663 _120011 x) = (x = x).
Proof. exact (@lem5728837 (x = x)). Qed.
Lemma lem5728839 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (EQ_MP (@lem5728838 _120011 x) (@lem5728835 _120011 x)). Qed.
Lemma lem5728842 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5728844 {_120011 : Type'} (x : _120011) : (term660 _120011 x) = (term664 _120011 x).
Proof. exact (@lem5728842 (x = x)). Qed.
Lemma lem5728847 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : term664 _120011 x.
Proof. exact (EQ_MP (@lem5728844 _120011 x) (@lem5728600 _120011 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5728850 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : False.
Proof. exact (@lem5728847 _120011 _120196 s f op x' x h1 h2 (@lem5728839 _120011 x)). Qed.
Lemma lem5728851 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : term610.
Proof. exact (fun h0 : ~ False => @lem5728850 _120011 _120196 s f op x' x h1 h2). Qed.
Lemma lem5728853 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5728854 : term610 = False.
Proof. exact (@lem5728853 False). Qed.
Lemma lem5728879 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5728692 _120011 _120196 f op x' x h1) (@lem5728507 _120011 _120196 f x' op h2)). Qed.
Lemma lem5728880 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x op.
Proof. exact (fun h0 : term78 _120011 _120196 f x op => @lem5728879 _120011 _120196 x f x' op h1 h2). Qed.
Lemma lem5728882 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5728883 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5728882 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5728884 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5728883 _120011 _120196 f x op) (@lem5728880 _120011 _120196 x f x' op h1 h2)). Qed.
Lemma lem5728887 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5728889 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term609 _120011 _120196 f x op).
Proof. exact (@lem5728887 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5728892 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : term609 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5728889 _120011 _120196 f x op) (@lem5728680 _120011 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5728895 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5728892 _120011 _120196 s f op x' x h1 h2 (@lem5728884 _120011 _120196 x f x' op h2 h3)). Qed.
Lemma lem5728896 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5728895 _120011 _120196 s x f x' op h1 h2 h3). Qed.
Lemma lem5728898 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5728899 : term610 = False.
Proof. exact (@lem5728898 False). Qed.
Lemma lem5728945 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (h1). Qed.
Lemma lem5728946 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : term611 _120011 x' s.
Proof. exact (fun h0 : term598 _120011 x' s => @lem5728945 _120011 x' s h1). Qed.
Lemma lem5728948 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5728949 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term611 _120011 x' s) = (@IN _120011 x' s).
Proof. exact (@lem5728948 (@IN _120011 x' s)). Qed.
Lemma lem5728950 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : @IN _120011 x' s) : @IN _120011 x' s.
Proof. exact (EQ_MP (@lem5728949 _120011 x' s) (@lem5728946 _120011 x' s h1)). Qed.
Lemma lem5728953 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5728955 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term598 _120011 x' s) = (term612 _120011 x' s).
Proof. exact (@lem5728953 (@IN _120011 x' s)). Qed.
Lemma lem5728958 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) : term612 _120011 x' s.
Proof. exact (EQ_MP (@lem5728955 _120011 x' s) (@lem5728517 _120011 x' s h1)). Qed.
Lemma lem5728961 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (@lem5728958 _120011 x' s h1 (@lem5728950 _120011 x' s h2)). Qed.
Lemma lem5728962 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : term610.
Proof. exact (fun h0 : ~ False => @lem5728961 _120011 x' s h1 h2). Qed.
Lemma lem5728964 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5728965 : term610 = False.
Proof. exact (@lem5728964 False). Qed.
Lemma lem5728966 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5728965) (@lem5728962 _120011 x' s h1 h2)). Qed.
Lemma lem5729011 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5729012 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x' op.
Proof. exact (fun h0 : term78 _120011 _120196 f x' op => @lem5729011 _120011 _120196 f x' op h1). Qed.
Lemma lem5729014 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729015 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem5729014 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5729016 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5729015 _120011 _120196 f x' op) (@lem5729012 _120011 _120196 f x' op h1)). Qed.
Lemma lem5729019 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5729021 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x' op) = (term609 _120011 _120196 f x' op).
Proof. exact (@lem5729019 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5729024 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : term609 _120011 _120196 f x' op.
Proof. exact (EQ_MP (@lem5729021 _120011 _120196 f x' op) (@lem5728523 _120011 _120196 x s f x' op h1)). Qed.
Lemma lem5729027 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5729024 _120011 _120196 x s f x' op h1 (@lem5729016 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729028 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5729027 _120011 _120196 x s f x' op h1 h2). Qed.
Lemma lem5729030 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729031 : term610 = False.
Proof. exact (@lem5729030 False). Qed.
Lemma lem5729032 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729031) (@lem5729028 _120011 _120196 x s f x' op h1 h2)). Qed.
Lemma lem5729077 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (@lem21386 _120011 x). Qed.
Lemma lem5729078 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (@lem5729077 _120011 x). Qed.
Lemma lem5729079 {_120011 : Type'} (x : _120011) : term663 _120011 x.
Proof. exact (fun h0 : term660 _120011 x => @lem5729078 _120011 x). Qed.
Lemma lem5729081 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729082 {_120011 : Type'} (x : _120011) : (term663 _120011 x) = (x = x).
Proof. exact (@lem5729081 (x = x)). Qed.
Lemma lem5729083 {_120011 : Type'} (x : _120011) : x = x.
Proof. exact (EQ_MP (@lem5729082 _120011 x) (@lem5729079 _120011 x)). Qed.
Lemma lem5729086 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5729088 {_120011 : Type'} (x : _120011) : (term660 _120011 x) = (term664 _120011 x).
Proof. exact (@lem5729086 (x = x)). Qed.
Lemma lem5729091 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : term664 _120011 x.
Proof. exact (EQ_MP (@lem5729088 _120011 x) (@lem5728734 _120011 s x' x h1 h2)). Qed.
Lemma lem5729094 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : False.
Proof. exact (@lem5729091 _120011 s x' x h1 h2 (@lem5729083 _120011 x)). Qed.
Lemma lem5729095 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : term610.
Proof. exact (fun h0 : ~ False => @lem5729094 _120011 s x' x h1 h2). Qed.
Lemma lem5729097 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729098 : term610 = False.
Proof. exact (@lem5729097 False). Qed.
Lemma lem5729123 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5728787 _120011 _120196 f op x' x h1) (@lem5728541 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729124 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x op.
Proof. exact (fun h0 : term78 _120011 _120196 f x op => @lem5729123 _120011 _120196 x f x' op h1 h2). Qed.
Lemma lem5729126 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729127 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5729126 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5729128 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : x' = x) (h2 : (f x') = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5729127 _120011 _120196 f x op) (@lem5729124 _120011 _120196 x f x' op h1 h2)). Qed.
Lemma lem5729131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5729133 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x op) = (term609 _120011 _120196 f x op).
Proof. exact (@lem5729131 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5729136 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term609 _120011 _120196 f x op.
Proof. exact (EQ_MP (@lem5729133 _120011 _120196 f x op) (@lem5728775 _120011 _120196 f x op h1)). Qed.
Lemma lem5729139 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5729136 _120011 _120196 f x op h1 (@lem5729128 _120011 _120196 x f x' op h2 h3)). Qed.
Lemma lem5729140 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5729139 _120011 _120196 x f x' op h1 h2 h3). Qed.
Lemma lem5729142 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729143 : term610 = False.
Proof. exact (@lem5729142 False). Qed.
Lemma lem5729144 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729143) (@lem5729140 _120011 _120196 x f x' op h1 h2 h3)). Qed.
Lemma lem5729189 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) : @IN _120011 x' s.
Proof. exact (proj1 (@lem5728333 _120011 _120196 s f x' op h1)). Qed.
Lemma lem5729190 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) : term611 _120011 x' s.
Proof. exact (fun h0 : term598 _120011 x' s => @lem5729189 _120011 _120196 s f x' op h1). Qed.
Lemma lem5729192 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729193 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term611 _120011 x' s) = (@IN _120011 x' s).
Proof. exact (@lem5729192 (@IN _120011 x' s)). Qed.
Lemma lem5729194 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) : @IN _120011 x' s.
Proof. exact (EQ_MP (@lem5729193 _120011 x' s) (@lem5729190 _120011 _120196 s f x' op h1)). Qed.
Lemma lem5729197 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5729199 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) : (term598 _120011 x' s) = (term612 _120011 x' s).
Proof. exact (@lem5729197 (@IN _120011 x' s)). Qed.
Lemma lem5729202 {_120011 : Type'} (x : _120011) (x' : _120011) (s : _120011 -> Prop) (h1 : term577 _120011 x x' s) : term612 _120011 x' s.
Proof. exact (EQ_MP (@lem5729199 _120011 x' s) (@lem5728551 _120011 x x' s h1)). Qed.
Lemma lem5729205 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term577 _120011 x x' s) (h2 : term158 _120011 _120196 s f x' op) : False.
Proof. exact (@lem5729202 _120011 x x' s h1 (@lem5729194 _120011 _120196 s f x' op h2)). Qed.
Lemma lem5729206 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term577 _120011 x x' s) (h2 : term158 _120011 _120196 s f x' op) : term610.
Proof. exact (fun h0 : ~ False => @lem5729205 _120011 _120196 x s f x' op h1 h2). Qed.
Lemma lem5729208 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729209 : term610 = False.
Proof. exact (@lem5729208 False). Qed.
Lemma lem5729210 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term577 _120011 x x' s) (h2 : term158 _120011 _120196 s f x' op) : False.
Proof. exact (EQ_MP (@lem5729209) (@lem5729206 _120011 _120196 x s f x' op h1 h2)). Qed.
Lemma lem5729255 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5729256 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : term607 _120011 _120196 f x' op.
Proof. exact (fun h0 : term78 _120011 _120196 f x' op => @lem5729255 _120011 _120196 f x' op h1). Qed.
Lemma lem5729258 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729259 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term607 _120011 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem5729258 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5729260 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5729259 _120011 _120196 f x' op) (@lem5729256 _120011 _120196 f x' op h1)). Qed.
Lemma lem5729263 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5729265 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term78 _120011 _120196 f x' op) = (term609 _120011 _120196 f x' op).
Proof. exact (@lem5729263 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5729268 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) : term609 _120011 _120196 f x' op.
Proof. exact (EQ_MP (@lem5729265 _120011 _120196 f x' op) (@lem5728557 _120011 _120196 s f x' op h1)). Qed.
Lemma lem5729271 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5729268 _120011 _120196 s f x' op h1 (@lem5729260 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729272 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5729271 _120011 _120196 s f x' op h1 h2). Qed.
Lemma lem5729274 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5729275 : term610 = False.
Proof. exact (@lem5729274 False). Qed.
Lemma lem5729276 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729275) (@lem5729272 _120011 _120196 s f x' op h1 h2)). Qed.
Lemma lem5729277 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (term78 _120011 _120196 f x op) = False.
Proof. exact (prop_ext (fun h4 : term78 _120011 _120196 f x op => @lem5729144 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728775 _120011 _120196 f x op h1)). Qed.
Lemma lem5729279 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729277 _120011 _120196 x f x' op h1 h2 h3) (@lem5728775 _120011 _120196 f x op h1)). Qed.
Lemma lem5729280 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729098) (@lem5729095 _120011 s x' x h1 h2)). Qed.
Lemma lem5729281 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5728899) (@lem5728896 _120011 _120196 s x f x' op h1 h2 h3)). Qed.
Lemma lem5729282 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5728854) (@lem5728851 _120011 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5729283 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5729276 _120011 _120196 s f x' op h1 h2) (fun h3 : False => @lem5728559 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729284 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729283 _120011 _120196 s f x' op h1 h2) (@lem5728559 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729285 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5729279 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728541 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729286 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729285 _120011 _120196 x f x' op h1 h2 h3) (@lem5728541 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729287 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5729286 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728539 _120011 x' x h2)). Qed.
Lemma lem5729288 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729287 _120011 _120196 x f x' op h1 h2 h3) (@lem5728539 _120011 x' x h2)). Qed.
Lemma lem5729289 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (term78 _120011 _120196 f x op) = False.
Proof. exact (prop_ext (fun h4 : term78 _120011 _120196 f x op => @lem5729288 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728537 _120011 _120196 f x op h1)). Qed.
Lemma lem5729290 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729289 _120011 _120196 x f x' op h1 h2 h3) (@lem5728537 _120011 _120196 f x op h1)). Qed.
Lemma lem5729291 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5729280 _120011 s x' x h1 h2) (fun h3 : False => @lem5728531 _120011 x' x h2)). Qed.
Lemma lem5729292 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729291 _120011 s x' x h1 h2) (@lem5728531 _120011 x' x h2)). Qed.
Lemma lem5729293 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5729032 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5728527 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729294 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729293 _120011 _120196 x s f x' op h1 h2) (@lem5728527 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729295 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (term598 _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120011 x' s => @lem5728966 _120011 x' s h1 h2) (fun h3 : False => @lem5728517 _120011 x' s h1)). Qed.
Lemma lem5729296 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5729295 _120011 x' s h1 h2) (@lem5728517 _120011 x' s h1)). Qed.
Lemma lem5729297 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (@IN _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120011 x' s => @lem5729296 _120011 x' s h1 h2) (fun h3 : False => @lem5728515 _120011 x' s h2)). Qed.
Lemma lem5729298 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5729297 _120011 x' s h1 h2) (@lem5728515 _120011 x' s h2)). Qed.
Lemma lem5729299 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5729281 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5728507 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729300 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729299 _120011 _120196 s x f x' op h1 h2 h3) (@lem5728507 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729301 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5729300 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5728505 _120011 x' x h2)). Qed.
Lemma lem5729302 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729301 _120011 _120196 s x f x' op h1 h2 h3) (@lem5728505 _120011 x' x h2)). Qed.
Lemma lem5729303 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5729282 _120011 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5728495 _120011 x' x h2)). Qed.
Lemma lem5729304 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729303 _120011 _120196 s f op x' x h1 h2) (@lem5728495 _120011 x' x h2)). Qed.
Lemma lem5729305 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5729284 _120011 _120196 s f x' op h1 h2) (fun h3 : False => @lem5728487 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729306 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729305 _120011 _120196 s f x' op h1 h2) (@lem5728487 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729307 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5729290 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728451 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729308 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729307 _120011 _120196 x f x' op h1 h2 h3) (@lem5728451 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729309 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5729308 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728447 _120011 x' x h2)). Qed.
Lemma lem5729310 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729309 _120011 _120196 x f x' op h1 h2 h3) (@lem5728447 _120011 x' x h2)). Qed.
Lemma lem5729311 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (term78 _120011 _120196 f x op) = False.
Proof. exact (prop_ext (fun h4 : term78 _120011 _120196 f x op => @lem5729310 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728443 _120011 _120196 f x op h1)). Qed.
Lemma lem5729312 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729311 _120011 _120196 x f x' op h1 h2 h3) (@lem5728443 _120011 _120196 f x op h1)). Qed.
Lemma lem5729313 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5729292 _120011 s x' x h1 h2) (fun h3 : False => @lem5728431 _120011 x' x h2)). Qed.
Lemma lem5729314 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729313 _120011 s x' x h1 h2) (@lem5728431 _120011 x' x h2)). Qed.
Lemma lem5729315 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5729294 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5728423 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729316 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729315 _120011 _120196 x s f x' op h1 h2) (@lem5728423 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729317 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (term598 _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120011 x' s => @lem5729298 _120011 x' s h1 h2) (fun h3 : False => @lem5728403 _120011 x' s h1)). Qed.
Lemma lem5729318 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5729317 _120011 x' s h1 h2) (@lem5728403 _120011 x' s h1)). Qed.
Lemma lem5729319 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (@IN _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120011 x' s => @lem5729318 _120011 x' s h1 h2) (fun h3 : False => @lem5728399 _120011 x' s h2)). Qed.
Lemma lem5729320 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5729319 _120011 x' s h1 h2) (@lem5728399 _120011 x' s h2)). Qed.
Lemma lem5729321 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5729302 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5728383 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729322 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729321 _120011 _120196 s x f x' op h1 h2 h3) (@lem5728383 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729323 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5729322 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5728379 _120011 x' x h2)). Qed.
Lemma lem5729324 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729323 _120011 _120196 s x f x' op h1 h2 h3) (@lem5728379 _120011 x' x h2)). Qed.
Lemma lem5729325 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5729304 _120011 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5728359 _120011 x' x h2)). Qed.
Lemma lem5729326 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729325 _120011 _120196 s f op x' x h1 h2) (@lem5728359 _120011 x' x h2)). Qed.
Lemma lem5729327 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5729306 _120011 _120196 s f x' op h1 h2) (fun h3 : False => @lem5728487 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729328 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729327 _120011 _120196 s f x' op h1 h2) (@lem5728487 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729329 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5729312 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728451 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729330 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729329 _120011 _120196 x f x' op h1 h2 h3) (@lem5728451 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729331 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5729330 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728447 _120011 x' x h2)). Qed.
Lemma lem5729332 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729331 _120011 _120196 x f x' op h1 h2 h3) (@lem5728447 _120011 x' x h2)). Qed.
Lemma lem5729333 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (term78 _120011 _120196 f x op) = False.
Proof. exact (prop_ext (fun h4 : term78 _120011 _120196 f x op => @lem5729332 _120011 _120196 x f x' op h1 h2 h3) (fun h4 : False => @lem5728443 _120011 _120196 f x op h1)). Qed.
Lemma lem5729334 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729333 _120011 _120196 x f x' op h1 h2 h3) (@lem5728443 _120011 _120196 f x op h1)). Qed.
Lemma lem5729335 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5729314 _120011 s x' x h1 h2) (fun h3 : False => @lem5728431 _120011 x' x h2)). Qed.
Lemma lem5729336 {_120011 : Type'} (s : _120011 -> Prop) (x' : _120011) (x : _120011) (h1 : term577 _120011 x x' s) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729335 _120011 s x' x h1 h2) (@lem5728431 _120011 x' x h2)). Qed.
Lemma lem5729337 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5729316 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5728423 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729338 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729337 _120011 _120196 x s f x' op h1 h2) (@lem5728423 _120011 _120196 f x' op h2)). Qed.
Lemma lem5729339 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (term598 _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120011 x' s => @lem5729320 _120011 x' s h1 h2) (fun h3 : False => @lem5728403 _120011 x' s h1)). Qed.
Lemma lem5729340 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5729339 _120011 x' s h1 h2) (@lem5728403 _120011 x' s h1)). Qed.
Lemma lem5729341 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : (@IN _120011 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120011 x' s => @lem5729340 _120011 x' s h1 h2) (fun h3 : False => @lem5728399 _120011 x' s h2)). Qed.
Lemma lem5729342 {_120011 : Type'} (x' : _120011) (s : _120011 -> Prop) (h1 : term598 _120011 x' s) (h2 : @IN _120011 x' s) : False.
Proof. exact (EQ_MP (@lem5729341 _120011 x' s h1 h2) (@lem5728399 _120011 x' s h2)). Qed.
Lemma lem5729343 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h4 : (f x') = (@neutral _120196 op) => @lem5729324 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5728383 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729344 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729343 _120011 _120196 s x f x' op h1 h2 h3) (@lem5728383 _120011 _120196 f x' op h3)). Qed.
Lemma lem5729345 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5729344 _120011 _120196 s x f x' op h1 h2 h3) (fun h4 : False => @lem5728379 _120011 x' x h2)). Qed.
Lemma lem5729346 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x : _120011) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) (h3 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5729345 _120011 _120196 s x f x' op h1 h2 h3) (@lem5728379 _120011 x' x h2)). Qed.
Lemma lem5729347 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5729326 _120011 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5728359 _120011 x' x h2)). Qed.
Lemma lem5729348 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5729347 _120011 _120196 s f op x' x h1 h2) (@lem5728359 _120011 x' x h2)). Qed.
Lemma lem5729349 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term158 _120011 _120196 s f x' op) (h2 : term650 _120011 _120196 x s f x' op) : False.
Proof. exact (or_elim (@lem5728331 _120011 _120196 x s f x' op h2) (fun h0 : term577 _120011 x x' s => @lem5729210 _120011 _120196 x s f x' op h0 h1) (fun h0 : (f x') = (@neutral _120196 op) => @lem5729328 _120011 _120196 s f x' op h1 h0)). Qed.
Lemma lem5729350 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term78 _120011 _120196 f x op) (h2 : term650 _120011 _120196 x s f x' op) (h3 : x' = x) : False.
Proof. exact (or_elim (@lem5728331 _120011 _120196 x s f x' op h2) (fun h0 : term577 _120011 x x' s => @lem5729336 _120011 s x' x h0 h3) (fun h0 : (f x') = (@neutral _120196 op) => @lem5729334 _120011 _120196 x f x' op h1 h3 h0)). Qed.
Lemma lem5729351 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term650 _120011 _120196 x s f x' op) : False.
Proof. exact (or_elim (@lem5728330 _120011 _120196 x s f x' op h2) (fun h0 : x' = x => @lem5729350 _120011 _120196 s f op x' x h1 h2 h0) (fun h0 : term158 _120011 _120196 s f x' op => @lem5729349 _120011 _120196 x s f x' op h0 h2)). Qed.
Lemma lem5729352 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (s : _120011 -> Prop) (h1 : term652 _120011 _120196 x s f x' op) (h2 : @IN _120011 x' s) : False.
Proof. exact (or_elim (@lem5728320 _120011 _120196 x s f x' op h1) (fun h0 : term598 _120011 x' s => @lem5729342 _120011 x' s h0 h2) (fun h0 : (f x') = (@neutral _120196 op) => @lem5729338 _120011 _120196 x s f x' op h1 h0)). Qed.
Lemma lem5729353 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) (x' : _120011) (x : _120011) (h1 : term652 _120011 _120196 x s f x' op) (h2 : x' = x) : False.
Proof. exact (or_elim (@lem5728320 _120011 _120196 x s f x' op h1) (fun h0 : term598 _120011 x' s => @lem5729348 _120011 _120196 s f op x' x h1 h2) (fun h0 : (f x') = (@neutral _120196 op) => @lem5729346 _120011 _120196 s x f x' op h1 h2 h0)). Qed.
Lemma lem5729354 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term652 _120011 _120196 x s f x' op) : False.
Proof. exact (or_elim (@lem5728323 _120011 _120196 x s f x' op h1) (fun h0 : x' = x => @lem5729353 _120011 _120196 s f op x' x h1 h0) (fun h0 : @IN _120011 x' s => @lem5729352 _120011 _120196 x f op x' s h1 h0)). Qed.
Lemma lem5729355 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : False.
Proof. exact (or_elim (@lem5728315 _120011 _120196 x s f x' op h2) (fun h0 : term652 _120011 _120196 x s f x' op => @lem5729354 _120011 _120196 x s f x' op h0) (fun h0 : term650 _120011 _120196 x s f x' op => @lem5729351 _120011 _120196 x s f x' op h1 h0)). Qed.
Lemma lem5729356 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : (term78 _120011 _120196 f x op) = False.
Proof. exact (prop_ext (fun h3 : term78 _120011 _120196 f x op => @lem5729355 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5728193 _120011 _120196 f x op h1)). Qed.
Lemma lem5729357 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : False.
Proof. exact (EQ_MP (@lem5729356 _120011 _120196 x s f x' op h1 h2) (@lem5728193 _120011 _120196 f x op h1)). Qed.
Lemma lem5729358 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : (term78 _120011 _120196 f x op) = False.
Proof. exact (prop_ext (fun h3 : term78 _120011 _120196 f x op => @lem5729357 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5728117 _120011 _120196 f x op h1)). Qed.
Lemma lem5729359 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : False.
Proof. exact (EQ_MP (@lem5729358 _120011 _120196 x s f x' op h1 h2) (@lem5728117 _120011 _120196 f x op h1)). Qed.
Lemma lem5729360 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : (term619 _120011 _120196 x s f x' op) = False.
Proof. exact (prop_ext (fun h3 : term619 _120011 _120196 x s f x' op => @lem5729359 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5728111 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5729361 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : False.
Proof. exact (EQ_MP (@lem5729360 _120011 _120196 x s f x' op h1 h2) (@lem5728111 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5729362 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term618 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term619 _120011 _120196 x s f x' op => @lem5729361 _120011 _120196 x s f x' op h1 h0). Qed.
Lemma lem5729363 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : (term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op).
Proof. exact (EQ_MP (@lem5728110 _120011 _120196 x s f x' op) (@lem5729362 _120011 _120196 s x' f x op h1)). Qed.
Lemma lem5729364 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term537 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term78 _120011 _120196 f x op => @lem5729363 _120011 _120196 s x' f x op h0). Qed.
Lemma lem5729369 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term628 _120011 _120196 s f x' op.
Proof. exact (fun x : _120011 => @lem5729364 _120011 _120196 x s f x' op). Qed.
Lemma lem5729374 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term632 _120011 _120196 f x' op.
Proof. exact (fun s : _120011 -> Prop => @lem5729369 _120011 _120196 s f x' op). Qed.
Lemma lem5729379 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : term636 _120011 _120196 x' op.
Proof. exact (fun f : _120011 -> _120196 => @lem5729374 _120011 _120196 f x' op). Qed.
Lemma lem5729384 {_120011 _120196 : Type'} (op : type1400 _120196) : term640 _120011 _120196 op.
Proof. exact (fun x' : _120011 => @lem5729379 _120011 _120196 x' op). Qed.
Lemma lem5729389 {_120011 _120196 : Type'} : term644 _120011 _120196.
Proof. exact (fun op : type1400 _120196 => @lem5729384 _120011 _120196 op). Qed.
Lemma lem5729390 {_120011 _120196 : Type'} : term643 _120011 _120196.
Proof. exact (EQ_MP (@lem5728105 _120011 _120196) (@lem5729389 _120011 _120196)). Qed.
Lemma lem5729391 {_120011 _120196 : Type'} (op : type1400 _120196) : term665 _120011 _120196 op.
Proof. exact (@lem5729390 _120011 _120196 op). Qed.
Lemma lem5729392 {_120011 _120196 : Type'} (op : type1400 _120196) : (term665 _120011 _120196 op) = (term639 _120011 _120196 op).
Proof. exact (eq_refl (term665 _120011 _120196 op)). Qed.
Lemma lem5729393 {_120011 _120196 : Type'} (op : type1400 _120196) : term639 _120011 _120196 op.
Proof. exact (EQ_MP (@lem5729392 _120011 _120196 op) (@lem5729391 _120011 _120196 op)). Qed.
Lemma lem5729394 {_120011 _120196 : Type'} (op : type1400 _120196) (x' : _120011) : term666 _120011 _120196 op x'.
Proof. exact (@lem5729393 _120011 _120196 op x'). Qed.
Lemma lem5729395 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : (term666 _120011 _120196 op x') = (term635 _120011 _120196 x' op).
Proof. exact (eq_refl (term666 _120011 _120196 op x')). Qed.
Lemma lem5729396 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) : term635 _120011 _120196 x' op.
Proof. exact (EQ_MP (@lem5729395 _120011 _120196 x' op) (@lem5729394 _120011 _120196 op x')). Qed.
Lemma lem5729397 {_120011 _120196 : Type'} (x' : _120011) (op : type1400 _120196) (f : _120011 -> _120196) : term667 _120011 _120196 x' op f.
Proof. exact (@lem5729396 _120011 _120196 x' op f). Qed.
Lemma lem5729398 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term667 _120011 _120196 x' op f) = (term631 _120011 _120196 f x' op).
Proof. exact (eq_refl (term667 _120011 _120196 x' op f)). Qed.
Lemma lem5729399 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term631 _120011 _120196 f x' op.
Proof. exact (EQ_MP (@lem5729398 _120011 _120196 f x' op) (@lem5729397 _120011 _120196 x' op f)). Qed.
Lemma lem5729400 {_120011 _120196 : Type'} (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (s : _120011 -> Prop) : term668 _120011 _120196 f x' op s.
Proof. exact (@lem5729399 _120011 _120196 f x' op s). Qed.
Lemma lem5729401 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term668 _120011 _120196 f x' op s) = (term627 _120011 _120196 s f x' op).
Proof. exact (eq_refl (term668 _120011 _120196 f x' op s)). Qed.
Lemma lem5729402 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term627 _120011 _120196 s f x' op.
Proof. exact (EQ_MP (@lem5729401 _120011 _120196 s f x' op) (@lem5729400 _120011 _120196 f x' op s)). Qed.
Lemma lem5729403 {_120011 _120196 : Type'} (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (x : _120011) : term669 _120011 _120196 s f x' op x.
Proof. exact (@lem5729402 _120011 _120196 s f x' op x). Qed.
Lemma lem5729404 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : (term669 _120011 _120196 s f x' op x) = (term620 _120011 _120196 x s f x' op).
Proof. exact (eq_refl (term669 _120011 _120196 s f x' op x)). Qed.
Lemma lem5729405 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term620 _120011 _120196 x s f x' op.
Proof. exact (EQ_MP (@lem5729404 _120011 _120196 x s f x' op) (@lem5729403 _120011 _120196 s f x' op x)). Qed.
Lemma lem5729407 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term620 _120011 _120196 x s f x' op.
Proof. exact (@lem5727935 _120011 _120196 x s f x' op (@lem5729405 _120011 _120196 x s f x' op)). Qed.
Lemma lem5729408 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term618 _120011 _120196 x s f x' op.
Proof. exact (@lem5729407 _120011 _120196 x s f x' op (@lem5726769 _120011 _120196 f x op h1)). Qed.
Lemma lem5729409 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : False.
Proof. exact (@lem5729408 _120011 _120196 s x' f x op h1 (@lem5727919 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5729410 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : (term619 _120011 _120196 x s f x' op) = False.
Proof. exact (prop_ext (fun h3 : term619 _120011 _120196 x s f x' op => @lem5729409 _120011 _120196 x s f x' op h1 h2) (fun h3 : False => @lem5727919 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5729411 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) (h2 : term619 _120011 _120196 x s f x' op) : False.
Proof. exact (EQ_MP (@lem5729410 _120011 _120196 x s f x' op h1 h2) (@lem5727919 _120011 _120196 x s f x' op h2)). Qed.
Lemma lem5729412 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : term618 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term619 _120011 _120196 x s f x' op => @lem5729411 _120011 _120196 x s f x' op h1 h0). Qed.
Lemma lem5729415 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5729416 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)) = (term670 _120044 _120196 s f op x' x).
Proof. exact (@lem5729415 ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x))). Qed.
Lemma lem5729417 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term670 _120044 _120196 s f op x' x) = ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)).
Proof. exact (SYM (@lem5729416 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729418 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : term671 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729421 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term670 _120044 _120196 s f op x' x) : term670 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729422 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term672 _120044 _120196 s f op x' x.
Proof. exact (fun h0 : term670 _120044 _120196 s f op x' x => @lem5729421 _120044 _120196 s f op x' x h0). Qed.
Lemma lem5729423 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term672 _120044 _120196 s f op x' x) : term672 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729424 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term670 _120044 _120196 s f op x' x) : term670 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729425 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term670 _120044 _120196 s f op x' x) (h2 : term672 _120044 _120196 s f op x' x) : term670 _120044 _120196 s f op x' x.
Proof. exact (@lem5729423 _120044 _120196 s f op x' x h2 (@lem5729424 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729426 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term670 _120044 _120196 s f op x' x) : term673 _120044 _120196 s f op x' x.
Proof. exact (fun h0 : term672 _120044 _120196 s f op x' x => @lem5729425 _120044 _120196 s f op x' x h1 h0). Qed.
Lemma lem5729427 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term672 _120044 _120196 s f op x' x) : term672 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729428 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term670 _120044 _120196 s f op x' x) (h2 : term672 _120044 _120196 s f op x' x) : term670 _120044 _120196 s f op x' x.
Proof. exact (@lem5729426 _120044 _120196 s f op x' x h1 (@lem5729427 _120044 _120196 s f op x' x h2)). Qed.
Lemma lem5729429 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term672 _120044 _120196 s f op x' x) : term672 _120044 _120196 s f op x' x.
Proof. exact (fun h0 : term670 _120044 _120196 s f op x' x => @lem5729428 _120044 _120196 s f op x' x h0 h1). Qed.
Lemma lem5729430 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term674 _120044 _120196 s f op x' x.
Proof. exact (fun h0 : term672 _120044 _120196 s f op x' x => @lem5729429 _120044 _120196 s f op x' x h0). Qed.
Lemma lem5729433 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term672 _120044 _120196 s f op x' x.
Proof. exact (@lem5729430 _120044 _120196 s f op x' x (@lem5729422 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729434 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term672 _120044 _120196 s f op x' x.
Proof. exact (@lem5729433 _120044 _120196 s f op x' x). Qed.
Lemma lem5729456 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5729457 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term670 _120044 _120196 s f op x' x) = (term675 _120044 _120196 s f op x' x).
Proof. exact (@lem5729456 (term671 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729459 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5729460 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term675 _120044 _120196 s f op x' x) = ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)).
Proof. exact (@lem5729459 ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x))). Qed.
Lemma lem5729461 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term670 _120044 _120196 s f op x' x) = ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)).
Proof. exact (TRANS (@lem5729457 _120044 _120196 s f op x' x) (@lem5729460 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729470 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term676 _120044 _120196 f op x' x) = (term677 _120044 _120196 f op x' x).
Proof. exact (fun_ext (fun s : _120044 -> Prop => @lem5729461 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729471 {_120044 : Type'} : (@all (_120044 -> Prop)) = (@all (_120044 -> Prop)).
Proof. exact (eq_refl (@all (_120044 -> Prop))). Qed.
Lemma lem5729472 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term678 _120044 _120196 f op x' x) = (term679 _120044 _120196 f op x' x).
Proof. exact (MK_COMB (@lem5729471 _120044) (@lem5729470 _120044 _120196 f op x' x)). Qed.
Lemma lem5729477 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : (term680 _120044 _120196 op x' x) = (term681 _120044 _120196 op x' x).
Proof. exact (fun_ext (fun f : _120044 -> _120196 => @lem5729472 _120044 _120196 f op x' x)). Qed.
Lemma lem5729478 {_120044 _120196 : Type'} : (@all (_120044 -> _120196)) = (@all (_120044 -> _120196)).
Proof. exact (eq_refl (@all (_120044 -> _120196))). Qed.
Lemma lem5729479 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : (term682 _120044 _120196 op x' x) = (term683 _120044 _120196 op x' x).
Proof. exact (MK_COMB (@lem5729478 _120044 _120196) (@lem5729477 _120044 _120196 op x' x)). Qed.
Lemma lem5729484 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : (term684 _120044 _120196 x' x) = (term685 _120044 _120196 x' x).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5729479 _120044 _120196 op x' x)). Qed.
Lemma lem5729485 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5729486 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : (term686 _120044 _120196 x' x) = (term687 _120044 _120196 x' x).
Proof. exact (MK_COMB (@lem5729485 _120196) (@lem5729484 _120044 _120196 x' x)). Qed.
Lemma lem5729491 {_120044 _120196 : Type'} (x : _120044) : (term688 _120044 _120196 x) = (term689 _120044 _120196 x).
Proof. exact (fun_ext (fun x' : _120044 => @lem5729486 _120044 _120196 x' x)). Qed.
Lemma lem5729492 {_120044 : Type'} : (@all _120044) = (@all _120044).
Proof. exact (eq_refl (@all _120044)). Qed.
Lemma lem5729493 {_120044 _120196 : Type'} (x : _120044) : (term690 _120044 _120196 x) = (term691 _120044 _120196 x).
Proof. exact (MK_COMB (@lem5729492 _120044) (@lem5729491 _120044 _120196 x)). Qed.
Lemma lem5729498 {_120044 _120196 : Type'} : (term692 _120044 _120196) = (term693 _120044 _120196).
Proof. exact (fun_ext (fun x : _120044 => @lem5729493 _120044 _120196 x)). Qed.
Lemma lem5729499 {_120044 : Type'} : (@all _120044) = (@all _120044).
Proof. exact (eq_refl (@all _120044)). Qed.
Lemma lem5729508 {_120044 _120196 : Type'} : (term694 _120044 _120196) = (term695 _120044 _120196).
Proof. exact (MK_COMB (@lem5729499 _120044) (@lem5729498 _120044 _120196)). Qed.
Lemma lem5729537 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)) = ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)).
Proof. exact (eq_refl ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x))). Qed.
Lemma lem5729538 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term677 _120044 _120196 f op x' x) = (term677 _120044 _120196 f op x' x).
Proof. exact (fun_ext (fun s : _120044 -> Prop => @lem5729537 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729539 {_120044 : Type'} : (@all (_120044 -> Prop)) = (@all (_120044 -> Prop)).
Proof. exact (eq_refl (@all (_120044 -> Prop))). Qed.
Lemma lem5729540 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term679 _120044 _120196 f op x' x) = (term679 _120044 _120196 f op x' x).
Proof. exact (MK_COMB (@lem5729539 _120044) (@lem5729538 _120044 _120196 f op x' x)). Qed.
Lemma lem5729541 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : (term681 _120044 _120196 op x' x) = (term681 _120044 _120196 op x' x).
Proof. exact (fun_ext (fun f : _120044 -> _120196 => @lem5729540 _120044 _120196 f op x' x)). Qed.
Lemma lem5729542 {_120044 _120196 : Type'} : (@all (_120044 -> _120196)) = (@all (_120044 -> _120196)).
Proof. exact (eq_refl (@all (_120044 -> _120196))). Qed.
Lemma lem5729543 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : (term683 _120044 _120196 op x' x) = (term683 _120044 _120196 op x' x).
Proof. exact (MK_COMB (@lem5729542 _120044 _120196) (@lem5729541 _120044 _120196 op x' x)). Qed.
Lemma lem5729544 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : (term685 _120044 _120196 x' x) = (term685 _120044 _120196 x' x).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5729543 _120044 _120196 op x' x)). Qed.
Lemma lem5729545 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5729546 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : (term687 _120044 _120196 x' x) = (term687 _120044 _120196 x' x).
Proof. exact (MK_COMB (@lem5729545 _120196) (@lem5729544 _120044 _120196 x' x)). Qed.
Lemma lem5729547 {_120044 _120196 : Type'} (x : _120044) : (term689 _120044 _120196 x) = (term689 _120044 _120196 x).
Proof. exact (fun_ext (fun x' : _120044 => @lem5729546 _120044 _120196 x' x)). Qed.
Lemma lem5729548 {_120044 : Type'} : (@all _120044) = (@all _120044).
Proof. exact (eq_refl (@all _120044)). Qed.
Lemma lem5729549 {_120044 _120196 : Type'} (x : _120044) : (term691 _120044 _120196 x) = (term691 _120044 _120196 x).
Proof. exact (MK_COMB (@lem5729548 _120044) (@lem5729547 _120044 _120196 x)). Qed.
Lemma lem5729550 {_120044 _120196 : Type'} : (term693 _120044 _120196) = (term693 _120044 _120196).
Proof. exact (fun_ext (fun x : _120044 => @lem5729549 _120044 _120196 x)). Qed.
Lemma lem5729551 {_120044 : Type'} : (@all _120044) = (@all _120044).
Proof. exact (eq_refl (@all _120044)). Qed.
Lemma lem5729552 {_120044 _120196 : Type'} : (term695 _120044 _120196) = (term695 _120044 _120196).
Proof. exact (MK_COMB (@lem5729551 _120044) (@lem5729550 _120044 _120196)). Qed.
Lemma lem5729593 {_120044 _120196 : Type'} : (term694 _120044 _120196) = (term695 _120044 _120196).
Proof. exact (TRANS (@lem5729508 _120044 _120196) (@lem5729552 _120044 _120196)). Qed.
Lemma lem5729594 {_120044 _120196 : Type'} : (term695 _120044 _120196) = (term694 _120044 _120196).
Proof. exact (SYM (@lem5729593 _120044 _120196)). Qed.
Lemma lem5729596 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5729597 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)) = (term670 _120044 _120196 s f op x' x).
Proof. exact (@lem5729596 ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x))). Qed.
Lemma lem5729598 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term670 _120044 _120196 s f op x' x) = ((term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x)).
Proof. exact (SYM (@lem5729597 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729599 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : term671 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729605 {_120044 : Type'} (x' : _120044) (x : _120044) : (term696 _120044 x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem5729607 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) : (term584 _120044 x' s) = (term584 _120044 x' s).
Proof. exact (eq_refl (term584 _120044 x' s)). Qed.
Lemma lem5729608 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term697 _120044 s x' x) = (term698 _120044 s x' x).
Proof. exact (MK_COMB (@lem5729607 _120044 x' s) (@lem5729605 _120044 x' x)). Qed.
Lemma lem5729609 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term699 _120044 s x' x) = (term697 _120044 s x' x).
Proof. exact (@lem17045 (@IN _120044 x' s) (term238 _120044 x' x)). Qed.
Lemma lem5729610 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term699 _120044 s x' x) = (term698 _120044 s x' x).
Proof. exact (TRANS (@lem5729609 _120044 s x' x) (@lem5729608 _120044 s x' x)). Qed.
Lemma lem5729617 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term578 _120044 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5729618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5729619 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) : (term700 _120044 s x' x) = (term701 _120044 s x' x).
Proof. exact (MK_COMB (@lem5729618) (@lem5729610 _120044 s x' x)). Qed.
Lemma lem5729620 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term702 _120044 _120196 s x f x' op) = (term703 _120044 _120196 s x f x' op).
Proof. exact (MK_COMB (@lem5729619 _120044 s x' x) (@lem5729617 _120044 _120196 f x' op)). Qed.
Lemma lem5729621 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term704 _120044 _120196 s x f x' op) = (term702 _120044 _120196 s x f x' op).
Proof. exact (@lem17045 (term52 _120044 s x' x) (term78 _120044 _120196 f x' op)). Qed.
Lemma lem5729622 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term704 _120044 _120196 s x f x' op) = (term703 _120044 _120196 s x f x' op).
Proof. exact (TRANS (@lem5729621 _120044 _120196 s x f x' op) (@lem5729620 _120044 _120196 s x f x' op)). Qed.
Lemma lem5729631 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term578 _120044 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5729633 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) : (term584 _120044 x' s) = (term584 _120044 x' s).
Proof. exact (eq_refl (term584 _120044 x' s)). Qed.
Lemma lem5729634 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term585 _120044 _120196 s f x' op) = (term586 _120044 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5729633 _120044 x' s) (@lem5729631 _120044 _120196 f x' op)). Qed.
Lemma lem5729635 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term404 _120044 _120196 s f x' op) = (term585 _120044 _120196 s f x' op).
Proof. exact (@lem17045 (@IN _120044 x' s) (term78 _120044 _120196 f x' op)). Qed.
Lemma lem5729636 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term404 _120044 _120196 s f x' op) = (term586 _120044 _120196 s f x' op).
Proof. exact (TRANS (@lem5729635 _120044 _120196 s f x' op) (@lem5729634 _120044 _120196 s f x' op)). Qed.
Lemma lem5729643 {_120044 : Type'} (x' : _120044) (x : _120044) : (term696 _120044 x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem5729644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5729645 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term705 _120044 _120196 s f x' op) = (term706 _120044 _120196 s f x' op).
Proof. exact (MK_COMB (@lem5729644) (@lem5729636 _120044 _120196 s f x' op)). Qed.
Lemma lem5729646 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term707 _120044 _120196 s f op x' x) = (term708 _120044 _120196 s f op x' x).
Proof. exact (MK_COMB (@lem5729645 _120044 _120196 s f x' op) (@lem5729643 _120044 x' x)). Qed.
Lemma lem5729647 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term709 _120044 _120196 s f op x' x) = (term707 _120044 _120196 s f op x' x).
Proof. exact (@lem17045 (term158 _120044 _120196 s f x' op) (term238 _120044 x' x)). Qed.
Lemma lem5729648 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term709 _120044 _120196 s f op x' x) = (term708 _120044 _120196 s f op x' x).
Proof. exact (TRANS (@lem5729647 _120044 _120196 s f op x' x) (@lem5729646 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729651 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term239 _120044 _120196 s f op x' x) = (term239 _120044 _120196 s f op x' x).
Proof. exact (eq_refl (term239 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5729653 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term710 _120044 _120196 s x f x' op) = (term711 _120044 _120196 s x f x' op).
Proof. exact (MK_COMB (@lem5729652) (@lem5729622 _120044 _120196 s x f x' op)). Qed.
Lemma lem5729654 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term712 _120044 _120196 s f op x' x) = (term713 _120044 _120196 s f op x' x).
Proof. exact (MK_COMB (@lem5729653 _120044 _120196 s x f x' op) (@lem5729651 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729656 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term714 _120044 _120196 s x f x' op) = (term714 _120044 _120196 s x f x' op).
Proof. exact (eq_refl (term714 _120044 _120196 s x f x' op)). Qed.
Lemma lem5729657 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term715 _120044 _120196 s f op x' x) = (term716 _120044 _120196 s f op x' x).
Proof. exact (MK_COMB (@lem5729656 _120044 _120196 s x f x' op) (@lem5729648 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5729659 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term717 _120044 _120196 s f op x' x) = (term718 _120044 _120196 s f op x' x).
Proof. exact (MK_COMB (@lem5729658) (@lem5729657 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729660 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term719 _120044 _120196 s f op x' x) = (term720 _120044 _120196 s f op x' x).
Proof. exact (MK_COMB (@lem5729659 _120044 _120196 s f op x' x) (@lem5729654 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729661 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term671 _120044 _120196 s f op x' x) = (term719 _120044 _120196 s f op x' x).
Proof. exact (@lem17646 (term207 _120044 _120196 s x f x' op) (term239 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729666 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term671 _120044 _120196 s f op x' x) = (term720 _120044 _120196 s f op x' x).
Proof. exact (TRANS (@lem5729661 _120044 _120196 s f op x' x) (@lem5729660 _120044 _120196 s f op x' x)). Qed.
Lemma lem5729789 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : term720 _120044 _120196 s f op x' x.
Proof. exact (EQ_MP (@lem5729666 _120044 _120196 s f op x' x) (@lem5729599 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729790 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term716 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729791 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term713 _120044 _120196 s f op x' x.
Proof. exact (h1). Qed.
Lemma lem5729792 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term708 _120044 _120196 s f op x' x.
Proof. exact (proj2 (@lem5729790 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729793 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term207 _120044 _120196 s x f x' op.
Proof. exact (proj1 (@lem5729790 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729795 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term52 _120044 s x' x.
Proof. exact (proj1 (@lem5729793 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729798 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term586 _120044 _120196 s f x' op) : term586 _120044 _120196 s f x' op.
Proof. exact (h1). Qed.
Lemma lem5729802 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term239 _120044 _120196 s f op x' x.
Proof. exact (proj2 (@lem5729791 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729803 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term703 _120044 _120196 s x f x' op.
Proof. exact (proj1 (@lem5729791 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729805 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term158 _120044 _120196 s f x' op.
Proof. exact (proj1 (@lem5729802 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729808 {_120044 : Type'} (s : _120044 -> Prop) (x' : _120044) (x : _120044) (h1 : term698 _120044 s x' x) : term698 _120044 s x' x.
Proof. exact (h1). Qed.
Lemma lem5729827 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) (h1 : term598 _120044 x' s) : term598 _120044 x' s.
Proof. exact (h1). Qed.
Lemma lem5729843 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5729859 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5729875 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) (h1 : term598 _120044 x' s) : term598 _120044 x' s.
Proof. exact (h1). Qed.
Lemma lem5729891 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5729907 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5729915 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) (h1 : term598 _120044 x' s) : term598 _120044 x' s.
Proof. exact (h1). Qed.
Lemma lem5729917 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term78 _120044 _120196 f x' op.
Proof. exact (proj2 (@lem5729793 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729923 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5729929 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term238 _120044 x' x.
Proof. exact (proj2 (@lem5729795 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729931 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5729939 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) (h1 : term598 _120044 x' s) : term598 _120044 x' s.
Proof. exact (h1). Qed.
Lemma lem5729941 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term238 _120044 x' x.
Proof. exact (proj2 (@lem5729802 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729947 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5729953 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term78 _120044 _120196 f x' op.
Proof. exact (proj2 (@lem5729805 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5729955 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5729996 {_120044 : Type'} (x : _120044) : (term657 _120044 x) = (term657 _120044 x).
Proof. exact (eq_refl (term657 _120044 x)). Qed.
Lemma lem5729997 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : (term658 _120044 x x') = (term659 _120044 x).
Proof. exact (MK_COMB (@lem5729996 _120044 x) (@lem5729931 _120044 x' x h1)). Qed.
Lemma lem5729998 {_120044 : Type'} (x : _120044) : (term659 _120044 x) = (term660 _120044 x).
Proof. exact (eq_refl (term659 _120044 x)). Qed.
Lemma lem5729999 {_120044 : Type'} (x : _120044) (x' : _120044) : (term661 _120044 x x') = (term661 _120044 x x').
Proof. exact (eq_refl (term661 _120044 x x')). Qed.
Lemma lem5730000 {_120044 : Type'} (x' : _120044) (x : _120044) : ((term658 _120044 x x') = (term659 _120044 x)) = ((term658 _120044 x x') = (term660 _120044 x)).
Proof. exact (MK_COMB (@lem5729999 _120044 x x') (@lem5729998 _120044 x)). Qed.
Lemma lem5730001 {_120044 : Type'} (x' : _120044) (x : _120044) : (term658 _120044 x x') = (term238 _120044 x' x).
Proof. exact (eq_refl (term658 _120044 x x')). Qed.
Lemma lem5730002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5730003 {_120044 : Type'} (x' : _120044) (x : _120044) : (term661 _120044 x x') = (term662 _120044 x' x).
Proof. exact (MK_COMB (@lem5730002) (@lem5730001 _120044 x' x)). Qed.
Lemma lem5730004 {_120044 : Type'} (x : _120044) : (term660 _120044 x) = (term660 _120044 x).
Proof. exact (eq_refl (term660 _120044 x)). Qed.
Lemma lem5730005 {_120044 : Type'} (x' : _120044) (x : _120044) : ((term658 _120044 x x') = (term660 _120044 x)) = ((term238 _120044 x' x) = (term660 _120044 x)).
Proof. exact (MK_COMB (@lem5730003 _120044 x' x) (@lem5730004 _120044 x)). Qed.
Lemma lem5730006 {_120044 : Type'} (x' : _120044) (x : _120044) : ((term658 _120044 x x') = (term659 _120044 x)) = ((term238 _120044 x' x) = (term660 _120044 x)).
Proof. exact (TRANS (@lem5730000 _120044 x' x) (@lem5730005 _120044 x' x)). Qed.
Lemma lem5730007 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : (term238 _120044 x' x) = (term660 _120044 x).
Proof. exact (EQ_MP (@lem5730006 _120044 x' x) (@lem5729997 _120044 x' x h1)). Qed.
Lemma lem5730008 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : term660 _120044 x.
Proof. exact (EQ_MP (@lem5730007 _120044 x' x h2) (@lem5729929 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730023 {_120044 : Type'} (x : _120044) : (term657 _120044 x) = (term657 _120044 x).
Proof. exact (eq_refl (term657 _120044 x)). Qed.
Lemma lem5730024 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : (term658 _120044 x x') = (term659 _120044 x).
Proof. exact (MK_COMB (@lem5730023 _120044 x) (@lem5729947 _120044 x' x h1)). Qed.
Lemma lem5730025 {_120044 : Type'} (x : _120044) : (term659 _120044 x) = (term660 _120044 x).
Proof. exact (eq_refl (term659 _120044 x)). Qed.
Lemma lem5730026 {_120044 : Type'} (x : _120044) (x' : _120044) : (term661 _120044 x x') = (term661 _120044 x x').
Proof. exact (eq_refl (term661 _120044 x x')). Qed.
Lemma lem5730027 {_120044 : Type'} (x' : _120044) (x : _120044) : ((term658 _120044 x x') = (term659 _120044 x)) = ((term658 _120044 x x') = (term660 _120044 x)).
Proof. exact (MK_COMB (@lem5730026 _120044 x x') (@lem5730025 _120044 x)). Qed.
Lemma lem5730028 {_120044 : Type'} (x' : _120044) (x : _120044) : (term658 _120044 x x') = (term238 _120044 x' x).
Proof. exact (eq_refl (term658 _120044 x x')). Qed.
Lemma lem5730029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5730030 {_120044 : Type'} (x' : _120044) (x : _120044) : (term661 _120044 x x') = (term662 _120044 x' x).
Proof. exact (MK_COMB (@lem5730029) (@lem5730028 _120044 x' x)). Qed.
Lemma lem5730031 {_120044 : Type'} (x : _120044) : (term660 _120044 x) = (term660 _120044 x).
Proof. exact (eq_refl (term660 _120044 x)). Qed.
Lemma lem5730032 {_120044 : Type'} (x' : _120044) (x : _120044) : ((term658 _120044 x x') = (term660 _120044 x)) = ((term238 _120044 x' x) = (term660 _120044 x)).
Proof. exact (MK_COMB (@lem5730030 _120044 x' x) (@lem5730031 _120044 x)). Qed.
Lemma lem5730033 {_120044 : Type'} (x' : _120044) (x : _120044) : ((term658 _120044 x x') = (term659 _120044 x)) = ((term238 _120044 x' x) = (term660 _120044 x)).
Proof. exact (TRANS (@lem5730027 _120044 x' x) (@lem5730032 _120044 x' x)). Qed.
Lemma lem5730034 {_120044 : Type'} (x' : _120044) (x : _120044) (h1 : x' = x) : (term238 _120044 x' x) = (term660 _120044 x).
Proof. exact (EQ_MP (@lem5730033 _120044 x' x) (@lem5730024 _120044 x' x h1)). Qed.
Lemma lem5730035 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : term660 _120044 x.
Proof. exact (EQ_MP (@lem5730034 _120044 x' x h2) (@lem5729941 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730106 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : @IN _120044 x' s.
Proof. exact (proj1 (@lem5729795 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730107 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term611 _120044 x' s.
Proof. exact (fun h0 : term598 _120044 x' s => @lem5730106 _120044 _120196 s f op x' x h1). Qed.
Lemma lem5730109 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730110 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) : (term611 _120044 x' s) = (@IN _120044 x' s).
Proof. exact (@lem5730109 (@IN _120044 x' s)). Qed.
Lemma lem5730111 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : @IN _120044 x' s.
Proof. exact (EQ_MP (@lem5730110 _120044 x' s) (@lem5730107 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730114 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5730116 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) : (term598 _120044 x' s) = (term612 _120044 x' s).
Proof. exact (@lem5730114 (@IN _120044 x' s)). Qed.
Lemma lem5730119 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) (h1 : term598 _120044 x' s) : term612 _120044 x' s.
Proof. exact (EQ_MP (@lem5730116 _120044 x' s) (@lem5729915 _120044 x' s h1)). Qed.
Lemma lem5730122 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : False.
Proof. exact (@lem5730119 _120044 x' s h1 (@lem5730111 _120044 _120196 s f op x' x h2)). Qed.
Lemma lem5730123 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : term610.
Proof. exact (fun h0 : ~ False => @lem5730122 _120044 _120196 s f op x' x h1 h2). Qed.
Lemma lem5730125 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730126 : term610 = False.
Proof. exact (@lem5730125 False). Qed.
Lemma lem5730127 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730126) (@lem5730123 _120044 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5730172 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5730173 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : term607 _120044 _120196 f x' op.
Proof. exact (fun h0 : term78 _120044 _120196 f x' op => @lem5730172 _120044 _120196 f x' op h1). Qed.
Lemma lem5730175 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730176 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term607 _120044 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem5730175 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5730177 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5730176 _120044 _120196 f x' op) (@lem5730173 _120044 _120196 f x' op h1)). Qed.
Lemma lem5730180 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5730182 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term78 _120044 _120196 f x' op) = (term609 _120044 _120196 f x' op).
Proof. exact (@lem5730180 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5730185 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : term609 _120044 _120196 f x' op.
Proof. exact (EQ_MP (@lem5730182 _120044 _120196 f x' op) (@lem5729917 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730188 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5730185 _120044 _120196 s f op x' x h1 (@lem5730177 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730189 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5730188 _120044 _120196 s x f x' op h1 h2). Qed.
Lemma lem5730191 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730192 : term610 = False.
Proof. exact (@lem5730191 False). Qed.
Lemma lem5730193 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730192) (@lem5730189 _120044 _120196 s x f x' op h1 h2)). Qed.
Lemma lem5730238 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (@lem21386 _120044 x). Qed.
Lemma lem5730239 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (@lem5730238 _120044 x). Qed.
Lemma lem5730240 {_120044 : Type'} (x : _120044) : term663 _120044 x.
Proof. exact (fun h0 : term660 _120044 x => @lem5730239 _120044 x). Qed.
Lemma lem5730242 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730243 {_120044 : Type'} (x : _120044) : (term663 _120044 x) = (x = x).
Proof. exact (@lem5730242 (x = x)). Qed.
Lemma lem5730244 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (EQ_MP (@lem5730243 _120044 x) (@lem5730240 _120044 x)). Qed.
Lemma lem5730247 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5730249 {_120044 : Type'} (x : _120044) : (term660 _120044 x) = (term664 _120044 x).
Proof. exact (@lem5730247 (x = x)). Qed.
Lemma lem5730252 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : term664 _120044 x.
Proof. exact (EQ_MP (@lem5730249 _120044 x) (@lem5730008 _120044 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5730255 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (@lem5730252 _120044 _120196 s f op x' x h1 h2 (@lem5730244 _120044 x)). Qed.
Lemma lem5730256 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : term610.
Proof. exact (fun h0 : ~ False => @lem5730255 _120044 _120196 s f op x' x h1 h2). Qed.
Lemma lem5730258 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730259 : term610 = False.
Proof. exact (@lem5730258 False). Qed.
Lemma lem5730305 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : @IN _120044 x' s.
Proof. exact (proj1 (@lem5729805 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730306 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term611 _120044 x' s.
Proof. exact (fun h0 : term598 _120044 x' s => @lem5730305 _120044 _120196 s f op x' x h1). Qed.
Lemma lem5730308 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730309 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) : (term611 _120044 x' s) = (@IN _120044 x' s).
Proof. exact (@lem5730308 (@IN _120044 x' s)). Qed.
Lemma lem5730310 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : @IN _120044 x' s.
Proof. exact (EQ_MP (@lem5730309 _120044 x' s) (@lem5730306 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730313 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5730315 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) : (term598 _120044 x' s) = (term612 _120044 x' s).
Proof. exact (@lem5730313 (@IN _120044 x' s)). Qed.
Lemma lem5730318 {_120044 : Type'} (x' : _120044) (s : _120044 -> Prop) (h1 : term598 _120044 x' s) : term612 _120044 x' s.
Proof. exact (EQ_MP (@lem5730315 _120044 x' s) (@lem5729939 _120044 x' s h1)). Qed.
Lemma lem5730321 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : False.
Proof. exact (@lem5730318 _120044 x' s h1 (@lem5730310 _120044 _120196 s f op x' x h2)). Qed.
Lemma lem5730322 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : term610.
Proof. exact (fun h0 : ~ False => @lem5730321 _120044 _120196 s f op x' x h1 h2). Qed.
Lemma lem5730324 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730325 : term610 = False.
Proof. exact (@lem5730324 False). Qed.
Lemma lem5730326 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730325) (@lem5730322 _120044 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5730371 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (@lem21386 _120044 x). Qed.
Lemma lem5730372 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (@lem5730371 _120044 x). Qed.
Lemma lem5730373 {_120044 : Type'} (x : _120044) : term663 _120044 x.
Proof. exact (fun h0 : term660 _120044 x => @lem5730372 _120044 x). Qed.
Lemma lem5730375 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730376 {_120044 : Type'} (x : _120044) : (term663 _120044 x) = (x = x).
Proof. exact (@lem5730375 (x = x)). Qed.
Lemma lem5730377 {_120044 : Type'} (x : _120044) : x = x.
Proof. exact (EQ_MP (@lem5730376 _120044 x) (@lem5730373 _120044 x)). Qed.
Lemma lem5730380 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5730382 {_120044 : Type'} (x : _120044) : (term660 _120044 x) = (term664 _120044 x).
Proof. exact (@lem5730380 (x = x)). Qed.
Lemma lem5730385 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : term664 _120044 x.
Proof. exact (EQ_MP (@lem5730382 _120044 x) (@lem5730035 _120044 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5730388 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (@lem5730385 _120044 _120196 s f op x' x h1 h2 (@lem5730377 _120044 x)). Qed.
Lemma lem5730389 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : term610.
Proof. exact (fun h0 : ~ False => @lem5730388 _120044 _120196 s f op x' x h1 h2). Qed.
Lemma lem5730391 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730392 : term610 = False.
Proof. exact (@lem5730391 False). Qed.
Lemma lem5730438 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5730439 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : term607 _120044 _120196 f x' op.
Proof. exact (fun h0 : term78 _120044 _120196 f x' op => @lem5730438 _120044 _120196 f x' op h1). Qed.
Lemma lem5730441 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730442 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term607 _120044 _120196 f x' op) = ((f x') = (@neutral _120196 op)).
Proof. exact (@lem5730441 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5730443 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : (f x') = (@neutral _120196 op)) : (f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5730442 _120044 _120196 f x' op) (@lem5730439 _120044 _120196 f x' op h1)). Qed.
Lemma lem5730446 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5730448 {_120044 _120196 : Type'} (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) : (term78 _120044 _120196 f x' op) = (term609 _120044 _120196 f x' op).
Proof. exact (@lem5730446 ((f x') = (@neutral _120196 op))). Qed.
Lemma lem5730451 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : term609 _120044 _120196 f x' op.
Proof. exact (EQ_MP (@lem5730448 _120044 _120196 f x' op) (@lem5729953 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730454 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (@lem5730451 _120044 _120196 s f op x' x h1 (@lem5730443 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730455 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5730454 _120044 _120196 s x f x' op h1 h2). Qed.
Lemma lem5730457 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5730458 : term610 = False.
Proof. exact (@lem5730457 False). Qed.
Lemma lem5730459 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730458) (@lem5730455 _120044 _120196 s x f x' op h1 h2)). Qed.
Lemma lem5730460 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730392) (@lem5730389 _120044 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5730461 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730259) (@lem5730256 _120044 _120196 s f op x' x h1 h2)). Qed.
Lemma lem5730462 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5730459 _120044 _120196 s x f x' op h1 h2) (fun h3 : False => @lem5729955 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730463 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730462 _120044 _120196 s x f x' op h1 h2) (@lem5729955 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730464 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5730460 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729947 _120044 x' x h2)). Qed.
Lemma lem5730465 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730464 _120044 _120196 s f op x' x h1 h2) (@lem5729947 _120044 x' x h2)). Qed.
Lemma lem5730466 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : (term598 _120044 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120044 x' s => @lem5730326 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729939 _120044 x' s h1)). Qed.
Lemma lem5730467 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730466 _120044 _120196 s f op x' x h1 h2) (@lem5729939 _120044 x' s h1)). Qed.
Lemma lem5730468 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5730461 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729931 _120044 x' x h2)). Qed.
Lemma lem5730469 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730468 _120044 _120196 s f op x' x h1 h2) (@lem5729931 _120044 x' x h2)). Qed.
Lemma lem5730470 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5730193 _120044 _120196 s x f x' op h1 h2) (fun h3 : False => @lem5729923 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730471 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730470 _120044 _120196 s x f x' op h1 h2) (@lem5729923 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730472 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : (term598 _120044 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120044 x' s => @lem5730127 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729915 _120044 x' s h1)). Qed.
Lemma lem5730473 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730472 _120044 _120196 s f op x' x h1 h2) (@lem5729915 _120044 x' s h1)). Qed.
Lemma lem5730474 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5730463 _120044 _120196 s x f x' op h1 h2) (fun h3 : False => @lem5729907 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730475 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730474 _120044 _120196 s x f x' op h1 h2) (@lem5729907 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730476 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5730465 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729891 _120044 x' x h2)). Qed.
Lemma lem5730477 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730476 _120044 _120196 s f op x' x h1 h2) (@lem5729891 _120044 x' x h2)). Qed.
Lemma lem5730478 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : (term598 _120044 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120044 x' s => @lem5730467 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729875 _120044 x' s h1)). Qed.
Lemma lem5730479 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730478 _120044 _120196 s f op x' x h1 h2) (@lem5729875 _120044 x' s h1)). Qed.
Lemma lem5730480 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5730469 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729859 _120044 x' x h2)). Qed.
Lemma lem5730481 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730480 _120044 _120196 s f op x' x h1 h2) (@lem5729859 _120044 x' x h2)). Qed.
Lemma lem5730482 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5730471 _120044 _120196 s x f x' op h1 h2) (fun h3 : False => @lem5729843 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730483 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730482 _120044 _120196 s x f x' op h1 h2) (@lem5729843 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730484 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : (term598 _120044 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120044 x' s => @lem5730473 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729827 _120044 x' s h1)). Qed.
Lemma lem5730485 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730484 _120044 _120196 s f op x' x h1 h2) (@lem5729827 _120044 x' s h1)). Qed.
Lemma lem5730486 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5730475 _120044 _120196 s x f x' op h1 h2) (fun h3 : False => @lem5729907 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730487 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term713 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730486 _120044 _120196 s x f x' op h1 h2) (@lem5729907 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730488 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5730477 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729891 _120044 x' x h2)). Qed.
Lemma lem5730489 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730488 _120044 _120196 s f op x' x h1 h2) (@lem5729891 _120044 x' x h2)). Qed.
Lemma lem5730490 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : (term598 _120044 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120044 x' s => @lem5730479 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729875 _120044 x' s h1)). Qed.
Lemma lem5730491 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term713 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730490 _120044 _120196 s f op x' x h1 h2) (@lem5729875 _120044 x' s h1)). Qed.
Lemma lem5730492 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5730481 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729859 _120044 x' x h2)). Qed.
Lemma lem5730493 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5730492 _120044 _120196 s f op x' x h1 h2) (@lem5729859 _120044 x' x h2)). Qed.
Lemma lem5730494 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : ((f x') = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral _120196 op) => @lem5730483 _120044 _120196 s x f x' op h1 h2) (fun h3 : False => @lem5729843 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730495 {_120044 _120196 : Type'} (s : _120044 -> Prop) (x : _120044) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : (f x') = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5730494 _120044 _120196 s x f x' op h1 h2) (@lem5729843 _120044 _120196 f x' op h2)). Qed.
Lemma lem5730496 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : (term598 _120044 x' s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120044 x' s => @lem5730485 _120044 _120196 s f op x' x h1 h2) (fun h3 : False => @lem5729827 _120044 x' s h1)). Qed.
Lemma lem5730497 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term598 _120044 x' s) (h2 : term716 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730496 _120044 _120196 s f op x' x h1 h2) (@lem5729827 _120044 x' s h1)). Qed.
Lemma lem5730498 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (s : _120044 -> Prop) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) (h2 : term698 _120044 s x' x) : False.
Proof. exact (or_elim (@lem5729808 _120044 s x' x h2) (fun h0 : term598 _120044 x' s => @lem5730491 _120044 _120196 s f op x' x h0 h1) (fun h0 : x' = x => @lem5730489 _120044 _120196 s f op x' x h1 h0)). Qed.
Lemma lem5730499 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term713 _120044 _120196 s f op x' x) : False.
Proof. exact (or_elim (@lem5729803 _120044 _120196 s f op x' x h1) (fun h0 : term698 _120044 s x' x => @lem5730498 _120044 _120196 f op s x' x h1 h0) (fun h0 : (f x') = (@neutral _120196 op) => @lem5730487 _120044 _120196 s x f x' op h1 h0)). Qed.
Lemma lem5730500 {_120044 _120196 : Type'} (x : _120044) (s : _120044 -> Prop) (f : _120044 -> _120196) (x' : _120044) (op : type1400 _120196) (h1 : term716 _120044 _120196 s f op x' x) (h2 : term586 _120044 _120196 s f x' op) : False.
Proof. exact (or_elim (@lem5729798 _120044 _120196 s f x' op h2) (fun h0 : term598 _120044 x' s => @lem5730497 _120044 _120196 s f op x' x h0 h1) (fun h0 : (f x') = (@neutral _120196 op) => @lem5730495 _120044 _120196 s x f x' op h1 h0)). Qed.
Lemma lem5730501 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term716 _120044 _120196 s f op x' x) : False.
Proof. exact (or_elim (@lem5729792 _120044 _120196 s f op x' x h1) (fun h0 : term586 _120044 _120196 s f x' op => @lem5730500 _120044 _120196 x s f x' op h1 h0) (fun h0 : x' = x => @lem5730493 _120044 _120196 s f op x' x h1 h0)). Qed.
Lemma lem5730502 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : False.
Proof. exact (or_elim (@lem5729789 _120044 _120196 s f op x' x h1) (fun h0 : term716 _120044 _120196 s f op x' x => @lem5730501 _120044 _120196 s f op x' x h0) (fun h0 : term713 _120044 _120196 s f op x' x => @lem5730499 _120044 _120196 s f op x' x h0)). Qed.
Lemma lem5730503 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : (term671 _120044 _120196 s f op x' x) = False.
Proof. exact (prop_ext (fun h2 : term671 _120044 _120196 s f op x' x => @lem5730502 _120044 _120196 s f op x' x h1) (fun h2 : False => @lem5729599 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730504 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730503 _120044 _120196 s f op x' x h1) (@lem5729599 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730505 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term670 _120044 _120196 s f op x' x.
Proof. exact (fun h0 : term671 _120044 _120196 s f op x' x => @lem5730504 _120044 _120196 s f op x' x h0). Qed.
Lemma lem5730506 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x).
Proof. exact (EQ_MP (@lem5729598 _120044 _120196 s f op x' x) (@lem5730505 _120044 _120196 s f op x' x)). Qed.
Lemma lem5730511 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term679 _120044 _120196 f op x' x.
Proof. exact (fun s : _120044 -> Prop => @lem5730506 _120044 _120196 s f op x' x). Qed.
Lemma lem5730516 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : term683 _120044 _120196 op x' x.
Proof. exact (fun f : _120044 -> _120196 => @lem5730511 _120044 _120196 f op x' x). Qed.
Lemma lem5730521 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : term687 _120044 _120196 x' x.
Proof. exact (fun op : type1400 _120196 => @lem5730516 _120044 _120196 op x' x). Qed.
Lemma lem5730526 {_120044 _120196 : Type'} (x : _120044) : term691 _120044 _120196 x.
Proof. exact (fun x' : _120044 => @lem5730521 _120044 _120196 x' x). Qed.
Lemma lem5730531 {_120044 _120196 : Type'} : term695 _120044 _120196.
Proof. exact (fun x : _120044 => @lem5730526 _120044 _120196 x). Qed.
Lemma lem5730532 {_120044 _120196 : Type'} : term694 _120044 _120196.
Proof. exact (EQ_MP (@lem5729594 _120044 _120196) (@lem5730531 _120044 _120196)). Qed.
Lemma lem5730533 {_120044 _120196 : Type'} (x : _120044) : term721 _120044 _120196 x.
Proof. exact (@lem5730532 _120044 _120196 x). Qed.
Lemma lem5730534 {_120044 _120196 : Type'} (x : _120044) : (term721 _120044 _120196 x) = (term690 _120044 _120196 x).
Proof. exact (eq_refl (term721 _120044 _120196 x)). Qed.
Lemma lem5730535 {_120044 _120196 : Type'} (x : _120044) : term690 _120044 _120196 x.
Proof. exact (EQ_MP (@lem5730534 _120044 _120196 x) (@lem5730533 _120044 _120196 x)). Qed.
Lemma lem5730536 {_120044 _120196 : Type'} (x : _120044) (x' : _120044) : term722 _120044 _120196 x x'.
Proof. exact (@lem5730535 _120044 _120196 x x'). Qed.
Lemma lem5730537 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : (term722 _120044 _120196 x x') = (term686 _120044 _120196 x' x).
Proof. exact (eq_refl (term722 _120044 _120196 x x')). Qed.
Lemma lem5730538 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) : term686 _120044 _120196 x' x.
Proof. exact (EQ_MP (@lem5730537 _120044 _120196 x' x) (@lem5730536 _120044 _120196 x x')). Qed.
Lemma lem5730539 {_120044 _120196 : Type'} (x' : _120044) (x : _120044) (op : type1400 _120196) : term723 _120044 _120196 x' x op.
Proof. exact (@lem5730538 _120044 _120196 x' x op). Qed.
Lemma lem5730540 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : (term723 _120044 _120196 x' x op) = (term682 _120044 _120196 op x' x).
Proof. exact (eq_refl (term723 _120044 _120196 x' x op)). Qed.
Lemma lem5730541 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) : term682 _120044 _120196 op x' x.
Proof. exact (EQ_MP (@lem5730540 _120044 _120196 op x' x) (@lem5730539 _120044 _120196 x' x op)). Qed.
Lemma lem5730542 {_120044 _120196 : Type'} (op : type1400 _120196) (x' : _120044) (x : _120044) (f : _120044 -> _120196) : term724 _120044 _120196 op x' x f.
Proof. exact (@lem5730541 _120044 _120196 op x' x f). Qed.
Lemma lem5730543 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term724 _120044 _120196 op x' x f) = (term678 _120044 _120196 f op x' x).
Proof. exact (eq_refl (term724 _120044 _120196 op x' x f)). Qed.
Lemma lem5730544 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term678 _120044 _120196 f op x' x.
Proof. exact (EQ_MP (@lem5730543 _120044 _120196 f op x' x) (@lem5730542 _120044 _120196 op x' x f)). Qed.
Lemma lem5730545 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (s : _120044 -> Prop) : term725 _120044 _120196 f op x' x s.
Proof. exact (@lem5730544 _120044 _120196 f op x' x s). Qed.
Lemma lem5730546 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term725 _120044 _120196 f op x' x s) = (term670 _120044 _120196 s f op x' x).
Proof. exact (eq_refl (term725 _120044 _120196 f op x' x s)). Qed.
Lemma lem5730547 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term670 _120044 _120196 s f op x' x.
Proof. exact (EQ_MP (@lem5730546 _120044 _120196 s f op x' x) (@lem5730545 _120044 _120196 f op x' x s)). Qed.
Lemma lem5730549 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term670 _120044 _120196 s f op x' x.
Proof. exact (@lem5729434 _120044 _120196 s f op x' x (@lem5730547 _120044 _120196 s f op x' x)). Qed.
Lemma lem5730550 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : False.
Proof. exact (@lem5730549 _120044 _120196 s f op x' x (@lem5729418 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730551 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : (term671 _120044 _120196 s f op x' x) = False.
Proof. exact (prop_ext (fun h2 : term671 _120044 _120196 s f op x' x => @lem5730550 _120044 _120196 s f op x' x h1) (fun h2 : False => @lem5729418 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730552 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) (h1 : term671 _120044 _120196 s f op x' x) : False.
Proof. exact (EQ_MP (@lem5730551 _120044 _120196 s f op x' x h1) (@lem5729418 _120044 _120196 s f op x' x h1)). Qed.
Lemma lem5730553 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : term670 _120044 _120196 s f op x' x.
Proof. exact (fun h0 : term671 _120044 _120196 s f op x' x => @lem5730552 _120044 _120196 s f op x' x h0). Qed.
Lemma lem5730554 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x' : _120044) (x : _120044) : (term207 _120044 _120196 s x f x' op) = (term239 _120044 _120196 s f op x' x).
Proof. exact (EQ_MP (@lem5729417 _120044 _120196 s f op x' x) (@lem5730553 _120044 _120196 s f op x' x)). Qed.
Lemma lem5730556 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5730557 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)) = (term726 _120082 _120196 s t f x op).
Proof. exact (@lem5730556 ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op))). Qed.
Lemma lem5730558 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term726 _120082 _120196 s t f x op) = ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)).
Proof. exact (SYM (@lem5730557 _120082 _120196 s t f x op)). Qed.
Lemma lem5730559 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : term727 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730562 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term726 _120082 _120196 s t f x op) : term726 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730563 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term728 _120082 _120196 s t f x op.
Proof. exact (fun h0 : term726 _120082 _120196 s t f x op => @lem5730562 _120082 _120196 s t f x op h0). Qed.
Lemma lem5730564 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term728 _120082 _120196 s t f x op) : term728 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730565 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term726 _120082 _120196 s t f x op) : term726 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730566 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term726 _120082 _120196 s t f x op) (h2 : term728 _120082 _120196 s t f x op) : term726 _120082 _120196 s t f x op.
Proof. exact (@lem5730564 _120082 _120196 s t f x op h2 (@lem5730565 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730567 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term726 _120082 _120196 s t f x op) : term729 _120082 _120196 s t f x op.
Proof. exact (fun h0 : term728 _120082 _120196 s t f x op => @lem5730566 _120082 _120196 s t f x op h1 h0). Qed.
Lemma lem5730568 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term728 _120082 _120196 s t f x op) : term728 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730569 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term726 _120082 _120196 s t f x op) (h2 : term728 _120082 _120196 s t f x op) : term726 _120082 _120196 s t f x op.
Proof. exact (@lem5730567 _120082 _120196 s t f x op h1 (@lem5730568 _120082 _120196 s t f x op h2)). Qed.
Lemma lem5730570 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term728 _120082 _120196 s t f x op) : term728 _120082 _120196 s t f x op.
Proof. exact (fun h0 : term726 _120082 _120196 s t f x op => @lem5730569 _120082 _120196 s t f x op h0 h1). Qed.
Lemma lem5730571 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term730 _120082 _120196 s t f x op.
Proof. exact (fun h0 : term728 _120082 _120196 s t f x op => @lem5730570 _120082 _120196 s t f x op h0). Qed.
Lemma lem5730574 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term728 _120082 _120196 s t f x op.
Proof. exact (@lem5730571 _120082 _120196 s t f x op (@lem5730563 _120082 _120196 s t f x op)). Qed.
Lemma lem5730575 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term728 _120082 _120196 s t f x op.
Proof. exact (@lem5730574 _120082 _120196 s t f x op). Qed.
Lemma lem5730597 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5730598 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term726 _120082 _120196 s t f x op) = (term731 _120082 _120196 s t f x op).
Proof. exact (@lem5730597 (term727 _120082 _120196 s t f x op)). Qed.
Lemma lem5730600 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5730601 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term731 _120082 _120196 s t f x op) = ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)).
Proof. exact (@lem5730600 ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op))). Qed.
Lemma lem5730602 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term726 _120082 _120196 s t f x op) = ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)).
Proof. exact (TRANS (@lem5730598 _120082 _120196 s t f x op) (@lem5730601 _120082 _120196 s t f x op)). Qed.
Lemma lem5730613 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term732 _120082 _120196 t f x op) = (term733 _120082 _120196 t f x op).
Proof. exact (fun_ext (fun s : _120082 -> Prop => @lem5730602 _120082 _120196 s t f x op)). Qed.
Lemma lem5730614 {_120082 : Type'} : (@all (_120082 -> Prop)) = (@all (_120082 -> Prop)).
Proof. exact (eq_refl (@all (_120082 -> Prop))). Qed.
Lemma lem5730615 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term734 _120082 _120196 t f x op) = (term735 _120082 _120196 t f x op).
Proof. exact (MK_COMB (@lem5730614 _120082) (@lem5730613 _120082 _120196 t f x op)). Qed.
Lemma lem5730620 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term736 _120082 _120196 f x op) = (term737 _120082 _120196 f x op).
Proof. exact (fun_ext (fun t : _120082 -> Prop => @lem5730615 _120082 _120196 t f x op)). Qed.
Lemma lem5730621 {_120082 : Type'} : (@all (_120082 -> Prop)) = (@all (_120082 -> Prop)).
Proof. exact (eq_refl (@all (_120082 -> Prop))). Qed.
Lemma lem5730622 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term738 _120082 _120196 f x op) = (term739 _120082 _120196 f x op).
Proof. exact (MK_COMB (@lem5730621 _120082) (@lem5730620 _120082 _120196 f x op)). Qed.
Lemma lem5730627 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : (term740 _120082 _120196 x op) = (term741 _120082 _120196 x op).
Proof. exact (fun_ext (fun f : _120082 -> _120196 => @lem5730622 _120082 _120196 f x op)). Qed.
Lemma lem5730628 {_120082 _120196 : Type'} : (@all (_120082 -> _120196)) = (@all (_120082 -> _120196)).
Proof. exact (eq_refl (@all (_120082 -> _120196))). Qed.
Lemma lem5730629 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : (term742 _120082 _120196 x op) = (term743 _120082 _120196 x op).
Proof. exact (MK_COMB (@lem5730628 _120082 _120196) (@lem5730627 _120082 _120196 x op)). Qed.
Lemma lem5730634 {_120082 _120196 : Type'} (op : type1400 _120196) : (term744 _120082 _120196 op) = (term745 _120082 _120196 op).
Proof. exact (fun_ext (fun x : _120082 => @lem5730629 _120082 _120196 x op)). Qed.
Lemma lem5730635 {_120082 : Type'} : (@all _120082) = (@all _120082).
Proof. exact (eq_refl (@all _120082)). Qed.
Lemma lem5730636 {_120082 _120196 : Type'} (op : type1400 _120196) : (term746 _120082 _120196 op) = (term747 _120082 _120196 op).
Proof. exact (MK_COMB (@lem5730635 _120082) (@lem5730634 _120082 _120196 op)). Qed.
Lemma lem5730641 {_120082 _120196 : Type'} : (term748 _120082 _120196) = (term749 _120082 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5730636 _120082 _120196 op)). Qed.
Lemma lem5730642 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5730651 {_120082 _120196 : Type'} : (term750 _120082 _120196) = (term751 _120082 _120196).
Proof. exact (MK_COMB (@lem5730642 _120196) (@lem5730641 _120082 _120196)). Qed.
Lemma lem5730682 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)) = ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)).
Proof. exact (eq_refl ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op))). Qed.
Lemma lem5730683 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term733 _120082 _120196 t f x op) = (term733 _120082 _120196 t f x op).
Proof. exact (fun_ext (fun s : _120082 -> Prop => @lem5730682 _120082 _120196 s t f x op)). Qed.
Lemma lem5730684 {_120082 : Type'} : (@all (_120082 -> Prop)) = (@all (_120082 -> Prop)).
Proof. exact (eq_refl (@all (_120082 -> Prop))). Qed.
Lemma lem5730685 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term735 _120082 _120196 t f x op) = (term735 _120082 _120196 t f x op).
Proof. exact (MK_COMB (@lem5730684 _120082) (@lem5730683 _120082 _120196 t f x op)). Qed.
Lemma lem5730686 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term737 _120082 _120196 f x op) = (term737 _120082 _120196 f x op).
Proof. exact (fun_ext (fun t : _120082 -> Prop => @lem5730685 _120082 _120196 t f x op)). Qed.
Lemma lem5730687 {_120082 : Type'} : (@all (_120082 -> Prop)) = (@all (_120082 -> Prop)).
Proof. exact (eq_refl (@all (_120082 -> Prop))). Qed.
Lemma lem5730688 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term739 _120082 _120196 f x op) = (term739 _120082 _120196 f x op).
Proof. exact (MK_COMB (@lem5730687 _120082) (@lem5730686 _120082 _120196 f x op)). Qed.
Lemma lem5730689 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : (term741 _120082 _120196 x op) = (term741 _120082 _120196 x op).
Proof. exact (fun_ext (fun f : _120082 -> _120196 => @lem5730688 _120082 _120196 f x op)). Qed.
Lemma lem5730690 {_120082 _120196 : Type'} : (@all (_120082 -> _120196)) = (@all (_120082 -> _120196)).
Proof. exact (eq_refl (@all (_120082 -> _120196))). Qed.
Lemma lem5730691 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : (term743 _120082 _120196 x op) = (term743 _120082 _120196 x op).
Proof. exact (MK_COMB (@lem5730690 _120082 _120196) (@lem5730689 _120082 _120196 x op)). Qed.
Lemma lem5730692 {_120082 _120196 : Type'} (op : type1400 _120196) : (term745 _120082 _120196 op) = (term745 _120082 _120196 op).
Proof. exact (fun_ext (fun x : _120082 => @lem5730691 _120082 _120196 x op)). Qed.
Lemma lem5730693 {_120082 : Type'} : (@all _120082) = (@all _120082).
Proof. exact (eq_refl (@all _120082)). Qed.
Lemma lem5730694 {_120082 _120196 : Type'} (op : type1400 _120196) : (term747 _120082 _120196 op) = (term747 _120082 _120196 op).
Proof. exact (MK_COMB (@lem5730693 _120082) (@lem5730692 _120082 _120196 op)). Qed.
Lemma lem5730695 {_120082 _120196 : Type'} : (term749 _120082 _120196) = (term749 _120082 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5730694 _120082 _120196 op)). Qed.
Lemma lem5730696 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5730697 {_120082 _120196 : Type'} : (term751 _120082 _120196) = (term751 _120082 _120196).
Proof. exact (MK_COMB (@lem5730696 _120196) (@lem5730695 _120082 _120196)). Qed.
Lemma lem5730740 {_120082 _120196 : Type'} : (term750 _120082 _120196) = (term751 _120082 _120196).
Proof. exact (TRANS (@lem5730651 _120082 _120196) (@lem5730697 _120082 _120196)). Qed.
Lemma lem5730741 {_120082 _120196 : Type'} : (term751 _120082 _120196) = (term750 _120082 _120196).
Proof. exact (SYM (@lem5730740 _120082 _120196)). Qed.
Lemma lem5730743 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5730744 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)) = (term726 _120082 _120196 s t f x op).
Proof. exact (@lem5730743 ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op))). Qed.
Lemma lem5730745 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term726 _120082 _120196 s t f x op) = ((term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op)).
Proof. exact (SYM (@lem5730744 _120082 _120196 s t f x op)). Qed.
Lemma lem5730746 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : term727 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730755 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) : (term752 _120082 s x t) = (term753 _120082 s x t).
Proof. exact (@lem17160 (@IN _120082 x s) (@IN _120082 x t)). Qed.
Lemma lem5730762 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term578 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5730763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5730764 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) : (term754 _120082 s x t) = (term755 _120082 s x t).
Proof. exact (MK_COMB (@lem5730763) (@lem5730755 _120082 s x t)). Qed.
Lemma lem5730765 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term756 _120082 _120196 s t f x op) = (term757 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730764 _120082 s x t) (@lem5730762 _120082 _120196 f x op)). Qed.
Lemma lem5730766 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term758 _120082 _120196 s t f x op) = (term756 _120082 _120196 s t f x op).
Proof. exact (@lem17045 (term29 _120082 s x t) (term78 _120082 _120196 f x op)). Qed.
Lemma lem5730767 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term758 _120082 _120196 s t f x op) = (term757 _120082 _120196 s t f x op).
Proof. exact (TRANS (@lem5730766 _120082 _120196 s t f x op) (@lem5730765 _120082 _120196 s t f x op)). Qed.
Lemma lem5730776 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term578 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5730778 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term584 _120082 x s) = (term584 _120082 x s).
Proof. exact (eq_refl (term584 _120082 x s)). Qed.
Lemma lem5730779 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term585 _120082 _120196 s f x op) = (term586 _120082 _120196 s f x op).
Proof. exact (MK_COMB (@lem5730778 _120082 x s) (@lem5730776 _120082 _120196 f x op)). Qed.
Lemma lem5730780 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term404 _120082 _120196 s f x op) = (term585 _120082 _120196 s f x op).
Proof. exact (@lem17045 (@IN _120082 x s) (term78 _120082 _120196 f x op)). Qed.
Lemma lem5730781 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term404 _120082 _120196 s f x op) = (term586 _120082 _120196 s f x op).
Proof. exact (TRANS (@lem5730780 _120082 _120196 s f x op) (@lem5730779 _120082 _120196 s f x op)). Qed.
Lemma lem5730790 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term578 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5730792 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term584 _120082 x t) = (term584 _120082 x t).
Proof. exact (eq_refl (term584 _120082 x t)). Qed.
Lemma lem5730793 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term585 _120082 _120196 t f x op) = (term586 _120082 _120196 t f x op).
Proof. exact (MK_COMB (@lem5730792 _120082 x t) (@lem5730790 _120082 _120196 f x op)). Qed.
Lemma lem5730794 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term404 _120082 _120196 t f x op) = (term585 _120082 _120196 t f x op).
Proof. exact (@lem17045 (@IN _120082 x t) (term78 _120082 _120196 f x op)). Qed.
Lemma lem5730795 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term404 _120082 _120196 t f x op) = (term586 _120082 _120196 t f x op).
Proof. exact (TRANS (@lem5730794 _120082 _120196 t f x op) (@lem5730793 _120082 _120196 t f x op)). Qed.
Lemma lem5730799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5730800 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term759 _120082 _120196 s f x op) = (term760 _120082 _120196 s f x op).
Proof. exact (MK_COMB (@lem5730799) (@lem5730781 _120082 _120196 s f x op)). Qed.
Lemma lem5730801 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term761 _120082 _120196 s t f x op) = (term762 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730800 _120082 _120196 s f x op) (@lem5730795 _120082 _120196 t f x op)). Qed.
Lemma lem5730802 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term763 _120082 _120196 s t f x op) = (term761 _120082 _120196 s t f x op).
Proof. exact (@lem17160 (term158 _120082 _120196 s f x op) (term158 _120082 _120196 t f x op)). Qed.
Lemma lem5730803 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term763 _120082 _120196 s t f x op) = (term762 _120082 _120196 s t f x op).
Proof. exact (TRANS (@lem5730802 _120082 _120196 s t f x op) (@lem5730801 _120082 _120196 s t f x op)). Qed.
Lemma lem5730806 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term295 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op).
Proof. exact (eq_refl (term295 _120082 _120196 s t f x op)). Qed.
Lemma lem5730807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5730808 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term764 _120082 _120196 s t f x op) = (term765 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730807) (@lem5730767 _120082 _120196 s t f x op)). Qed.
Lemma lem5730809 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term766 _120082 _120196 s t f x op) = (term767 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730808 _120082 _120196 s t f x op) (@lem5730806 _120082 _120196 s t f x op)). Qed.
Lemma lem5730811 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term768 _120082 _120196 s t f x op) = (term768 _120082 _120196 s t f x op).
Proof. exact (eq_refl (term768 _120082 _120196 s t f x op)). Qed.
Lemma lem5730812 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term769 _120082 _120196 s t f x op) = (term770 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730811 _120082 _120196 s t f x op) (@lem5730803 _120082 _120196 s t f x op)). Qed.
Lemma lem5730813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5730814 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term771 _120082 _120196 s t f x op) = (term772 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730813) (@lem5730812 _120082 _120196 s t f x op)). Qed.
Lemma lem5730815 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term773 _120082 _120196 s t f x op) = (term774 _120082 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5730814 _120082 _120196 s t f x op) (@lem5730809 _120082 _120196 s t f x op)). Qed.
Lemma lem5730816 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term727 _120082 _120196 s t f x op) = (term773 _120082 _120196 s t f x op).
Proof. exact (@lem17646 (term264 _120082 _120196 s t f x op) (term295 _120082 _120196 s t f x op)). Qed.
Lemma lem5730821 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term727 _120082 _120196 s t f x op) = (term774 _120082 _120196 s t f x op).
Proof. exact (TRANS (@lem5730816 _120082 _120196 s t f x op) (@lem5730815 _120082 _120196 s t f x op)). Qed.
Lemma lem5730970 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : term774 _120082 _120196 s t f x op.
Proof. exact (EQ_MP (@lem5730821 _120082 _120196 s t f x op) (@lem5730746 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730971 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term770 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730972 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term767 _120082 _120196 s t f x op) : term767 _120082 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5730973 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term762 _120082 _120196 s t f x op.
Proof. exact (proj2 (@lem5730971 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730974 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term264 _120082 _120196 s t f x op.
Proof. exact (proj1 (@lem5730971 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730975 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term586 _120082 _120196 t f x op.
Proof. exact (proj2 (@lem5730973 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730976 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term586 _120082 _120196 s f x op.
Proof. exact (proj1 (@lem5730973 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730978 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term29 _120082 s x t.
Proof. exact (proj1 (@lem5730974 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730993 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term767 _120082 _120196 s t f x op) : term295 _120082 _120196 s t f x op.
Proof. exact (proj2 (@lem5730972 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730994 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term767 _120082 _120196 s t f x op) : term757 _120082 _120196 s t f x op.
Proof. exact (proj1 (@lem5730972 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5730995 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) : term158 _120082 _120196 s f x op.
Proof. exact (h1). Qed.
Lemma lem5730996 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) : term158 _120082 _120196 t f x op.
Proof. exact (h1). Qed.
Lemma lem5730999 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) (h1 : term753 _120082 s x t) : term753 _120082 s x t.
Proof. exact (h1). Qed.
Lemma lem5731005 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) (h1 : term753 _120082 s x t) : term753 _120082 s x t.
Proof. exact (h1). Qed.
Lemma lem5731016 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731024 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) : term598 _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731040 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731048 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731056 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) : term598 _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731068 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731072 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731080 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731084 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) : term598 _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731096 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731100 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) : term598 _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731116 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731132 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731136 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731164 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731192 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731196 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731200 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) : term598 _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731202 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term78 _120082 _120196 f x op.
Proof. exact (proj2 (@lem5730974 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731208 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731212 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731216 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) : term598 _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731218 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term78 _120082 _120196 f x op.
Proof. exact (proj2 (@lem5730974 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731222 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731224 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731228 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731230 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) : term598 _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731236 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731238 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) : term598 _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731242 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term78 _120082 _120196 f x op.
Proof. exact (proj2 (@lem5730974 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731246 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731250 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term78 _120082 _120196 f x op.
Proof. exact (proj2 (@lem5730974 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731254 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731256 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731262 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) (h1 : term753 _120082 s x t) : term598 _120082 x s.
Proof. exact (proj1 (@lem5730999 _120082 s x t h1)). Qed.
Lemma lem5731268 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) : term78 _120082 _120196 f x op.
Proof. exact (proj2 (@lem5730995 _120082 _120196 s f x op h1)). Qed.
Lemma lem5731270 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731278 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) (h1 : term753 _120082 s x t) : term598 _120082 x t.
Proof. exact (proj2 (@lem5731005 _120082 s x t h1)). Qed.
Lemma lem5731282 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) : term78 _120082 _120196 f x op.
Proof. exact (proj2 (@lem5730996 _120082 _120196 t f x op h1)). Qed.
Lemma lem5731284 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731329 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731330 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : term611 _120082 x s.
Proof. exact (fun h0 : term598 _120082 x s => @lem5731329 _120082 x s h1). Qed.
Lemma lem5731332 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731333 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term611 _120082 x s) = (@IN _120082 x s).
Proof. exact (@lem5731332 (@IN _120082 x s)). Qed.
Lemma lem5731334 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (EQ_MP (@lem5731333 _120082 x s) (@lem5731330 _120082 x s h1)). Qed.
Lemma lem5731337 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731339 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term598 _120082 x s) = (term612 _120082 x s).
Proof. exact (@lem5731337 (@IN _120082 x s)). Qed.
Lemma lem5731342 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) : term612 _120082 x s.
Proof. exact (EQ_MP (@lem5731339 _120082 x s) (@lem5731200 _120082 x s h1)). Qed.
Lemma lem5731345 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (@lem5731342 _120082 x s h1 (@lem5731334 _120082 x s h2)). Qed.
Lemma lem5731346 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : term610.
Proof. exact (fun h0 : ~ False => @lem5731345 _120082 x s h1 h2). Qed.
Lemma lem5731348 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731349 : term610 = False.
Proof. exact (@lem5731348 False). Qed.
Lemma lem5731350 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5731349) (@lem5731346 _120082 x s h1 h2)). Qed.
Lemma lem5731395 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731396 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120082 _120196 f x op.
Proof. exact (fun h0 : term78 _120082 _120196 f x op => @lem5731395 _120082 _120196 f x op h1). Qed.
Lemma lem5731398 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731399 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term607 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5731398 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731400 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5731399 _120082 _120196 f x op) (@lem5731396 _120082 _120196 f x op h1)). Qed.
Lemma lem5731403 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731405 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term609 _120082 _120196 f x op).
Proof. exact (@lem5731403 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731408 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term609 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5731405 _120082 _120196 f x op) (@lem5731202 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731411 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5731408 _120082 _120196 s t f x op h1 (@lem5731400 _120082 _120196 f x op h2)). Qed.
Lemma lem5731412 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5731411 _120082 _120196 s t f x op h1 h2). Qed.
Lemma lem5731414 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731415 : term610 = False.
Proof. exact (@lem5731414 False). Qed.
Lemma lem5731416 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5731415) (@lem5731412 _120082 _120196 s t f x op h1 h2)). Qed.
Lemma lem5731461 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (h1). Qed.
Lemma lem5731462 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : term611 _120082 x s.
Proof. exact (fun h0 : term598 _120082 x s => @lem5731461 _120082 x s h1). Qed.
Lemma lem5731464 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731465 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term611 _120082 x s) = (@IN _120082 x s).
Proof. exact (@lem5731464 (@IN _120082 x s)). Qed.
Lemma lem5731466 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : @IN _120082 x s) : @IN _120082 x s.
Proof. exact (EQ_MP (@lem5731465 _120082 x s) (@lem5731462 _120082 x s h1)). Qed.
Lemma lem5731469 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731471 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term598 _120082 x s) = (term612 _120082 x s).
Proof. exact (@lem5731469 (@IN _120082 x s)). Qed.
Lemma lem5731474 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) : term612 _120082 x s.
Proof. exact (EQ_MP (@lem5731471 _120082 x s) (@lem5731216 _120082 x s h1)). Qed.
Lemma lem5731477 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (@lem5731474 _120082 x s h1 (@lem5731466 _120082 x s h2)). Qed.
Lemma lem5731478 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : term610.
Proof. exact (fun h0 : ~ False => @lem5731477 _120082 x s h1 h2). Qed.
Lemma lem5731480 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731481 : term610 = False.
Proof. exact (@lem5731480 False). Qed.
Lemma lem5731482 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5731481) (@lem5731478 _120082 x s h1 h2)). Qed.
Lemma lem5731527 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731528 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120082 _120196 f x op.
Proof. exact (fun h0 : term78 _120082 _120196 f x op => @lem5731527 _120082 _120196 f x op h1). Qed.
Lemma lem5731530 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731531 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term607 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5731530 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731532 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5731531 _120082 _120196 f x op) (@lem5731528 _120082 _120196 f x op h1)). Qed.
Lemma lem5731535 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731537 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term609 _120082 _120196 f x op).
Proof. exact (@lem5731535 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731540 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term609 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5731537 _120082 _120196 f x op) (@lem5731218 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731543 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5731540 _120082 _120196 s t f x op h1 (@lem5731532 _120082 _120196 f x op h2)). Qed.
Lemma lem5731544 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5731543 _120082 _120196 s t f x op h1 h2). Qed.
Lemma lem5731546 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731547 : term610 = False.
Proof. exact (@lem5731546 False). Qed.
Lemma lem5731548 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5731547) (@lem5731544 _120082 _120196 s t f x op h1 h2)). Qed.
Lemma lem5731593 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731594 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : term611 _120082 x t.
Proof. exact (fun h0 : term598 _120082 x t => @lem5731593 _120082 x t h1). Qed.
Lemma lem5731596 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731597 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term611 _120082 x t) = (@IN _120082 x t).
Proof. exact (@lem5731596 (@IN _120082 x t)). Qed.
Lemma lem5731598 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (EQ_MP (@lem5731597 _120082 x t) (@lem5731594 _120082 x t h1)). Qed.
Lemma lem5731601 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731603 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term598 _120082 x t) = (term612 _120082 x t).
Proof. exact (@lem5731601 (@IN _120082 x t)). Qed.
Lemma lem5731606 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) : term612 _120082 x t.
Proof. exact (EQ_MP (@lem5731603 _120082 x t) (@lem5731230 _120082 x t h1)). Qed.
Lemma lem5731609 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (@lem5731606 _120082 x t h1 (@lem5731598 _120082 x t h2)). Qed.
Lemma lem5731610 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : term610.
Proof. exact (fun h0 : ~ False => @lem5731609 _120082 x t h1 h2). Qed.
Lemma lem5731612 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731613 : term610 = False.
Proof. exact (@lem5731612 False). Qed.
Lemma lem5731614 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5731613) (@lem5731610 _120082 x t h1 h2)). Qed.
Lemma lem5731659 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (h1). Qed.
Lemma lem5731660 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : term611 _120082 x t.
Proof. exact (fun h0 : term598 _120082 x t => @lem5731659 _120082 x t h1). Qed.
Lemma lem5731662 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731663 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term611 _120082 x t) = (@IN _120082 x t).
Proof. exact (@lem5731662 (@IN _120082 x t)). Qed.
Lemma lem5731664 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : @IN _120082 x t) : @IN _120082 x t.
Proof. exact (EQ_MP (@lem5731663 _120082 x t) (@lem5731660 _120082 x t h1)). Qed.
Lemma lem5731667 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731669 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term598 _120082 x t) = (term612 _120082 x t).
Proof. exact (@lem5731667 (@IN _120082 x t)). Qed.
Lemma lem5731672 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) : term612 _120082 x t.
Proof. exact (EQ_MP (@lem5731669 _120082 x t) (@lem5731238 _120082 x t h1)). Qed.
Lemma lem5731675 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (@lem5731672 _120082 x t h1 (@lem5731664 _120082 x t h2)). Qed.
Lemma lem5731676 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : term610.
Proof. exact (fun h0 : ~ False => @lem5731675 _120082 x t h1 h2). Qed.
Lemma lem5731678 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731679 : term610 = False.
Proof. exact (@lem5731678 False). Qed.
Lemma lem5731680 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5731679) (@lem5731676 _120082 x t h1 h2)). Qed.
Lemma lem5731725 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731726 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120082 _120196 f x op.
Proof. exact (fun h0 : term78 _120082 _120196 f x op => @lem5731725 _120082 _120196 f x op h1). Qed.
Lemma lem5731728 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731729 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term607 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5731728 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731730 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5731729 _120082 _120196 f x op) (@lem5731726 _120082 _120196 f x op h1)). Qed.
Lemma lem5731733 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731735 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term609 _120082 _120196 f x op).
Proof. exact (@lem5731733 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731738 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term609 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5731735 _120082 _120196 f x op) (@lem5731242 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731741 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5731738 _120082 _120196 s t f x op h1 (@lem5731730 _120082 _120196 f x op h2)). Qed.
Lemma lem5731742 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5731741 _120082 _120196 s t f x op h1 h2). Qed.
Lemma lem5731744 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731745 : term610 = False.
Proof. exact (@lem5731744 False). Qed.
Lemma lem5731746 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5731745) (@lem5731742 _120082 _120196 s t f x op h1 h2)). Qed.
Lemma lem5731791 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731792 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120082 _120196 f x op.
Proof. exact (fun h0 : term78 _120082 _120196 f x op => @lem5731791 _120082 _120196 f x op h1). Qed.
Lemma lem5731794 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731795 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term607 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5731794 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731796 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5731795 _120082 _120196 f x op) (@lem5731792 _120082 _120196 f x op h1)). Qed.
Lemma lem5731799 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731801 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term609 _120082 _120196 f x op).
Proof. exact (@lem5731799 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731804 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : term609 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5731801 _120082 _120196 f x op) (@lem5731250 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5731807 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5731804 _120082 _120196 s t f x op h1 (@lem5731796 _120082 _120196 f x op h2)). Qed.
Lemma lem5731808 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5731807 _120082 _120196 s t f x op h1 h2). Qed.
Lemma lem5731810 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731811 : term610 = False.
Proof. exact (@lem5731810 False). Qed.
Lemma lem5731812 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5731811) (@lem5731808 _120082 _120196 s t f x op h1 h2)). Qed.
Lemma lem5731857 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) : @IN _120082 x s.
Proof. exact (proj1 (@lem5730995 _120082 _120196 s f x op h1)). Qed.
Lemma lem5731858 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) : term611 _120082 x s.
Proof. exact (fun h0 : term598 _120082 x s => @lem5731857 _120082 _120196 s f x op h1). Qed.
Lemma lem5731860 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731861 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term611 _120082 x s) = (@IN _120082 x s).
Proof. exact (@lem5731860 (@IN _120082 x s)). Qed.
Lemma lem5731862 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) : @IN _120082 x s.
Proof. exact (EQ_MP (@lem5731861 _120082 x s) (@lem5731858 _120082 _120196 s f x op h1)). Qed.
Lemma lem5731865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731867 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) : (term598 _120082 x s) = (term612 _120082 x s).
Proof. exact (@lem5731865 (@IN _120082 x s)). Qed.
Lemma lem5731870 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) (h1 : term753 _120082 s x t) : term612 _120082 x s.
Proof. exact (EQ_MP (@lem5731867 _120082 x s) (@lem5731262 _120082 s x t h1)). Qed.
Lemma lem5731873 {_120082 _120196 : Type'} (t : _120082 -> Prop) (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term753 _120082 s x t) (h2 : term158 _120082 _120196 s f x op) : False.
Proof. exact (@lem5731870 _120082 s x t h1 (@lem5731862 _120082 _120196 s f x op h2)). Qed.
Lemma lem5731874 {_120082 _120196 : Type'} (t : _120082 -> Prop) (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term753 _120082 s x t) (h2 : term158 _120082 _120196 s f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5731873 _120082 _120196 t s f x op h1 h2). Qed.
Lemma lem5731876 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731877 : term610 = False.
Proof. exact (@lem5731876 False). Qed.
Lemma lem5731878 {_120082 _120196 : Type'} (t : _120082 -> Prop) (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term753 _120082 s x t) (h2 : term158 _120082 _120196 s f x op) : False.
Proof. exact (EQ_MP (@lem5731877) (@lem5731874 _120082 _120196 t s f x op h1 h2)). Qed.
Lemma lem5731923 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5731924 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120082 _120196 f x op.
Proof. exact (fun h0 : term78 _120082 _120196 f x op => @lem5731923 _120082 _120196 f x op h1). Qed.
Lemma lem5731926 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731927 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term607 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5731926 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731928 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5731927 _120082 _120196 f x op) (@lem5731924 _120082 _120196 f x op h1)). Qed.
Lemma lem5731931 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731933 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term609 _120082 _120196 f x op).
Proof. exact (@lem5731931 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5731936 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) : term609 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5731933 _120082 _120196 f x op) (@lem5731268 _120082 _120196 s f x op h1)). Qed.
Lemma lem5731939 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5731936 _120082 _120196 s f x op h1 (@lem5731928 _120082 _120196 f x op h2)). Qed.
Lemma lem5731940 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5731939 _120082 _120196 s f x op h1 h2). Qed.
Lemma lem5731942 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731943 : term610 = False.
Proof. exact (@lem5731942 False). Qed.
Lemma lem5731944 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5731943) (@lem5731940 _120082 _120196 s f x op h1 h2)). Qed.
Lemma lem5731989 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) : @IN _120082 x t.
Proof. exact (proj1 (@lem5730996 _120082 _120196 t f x op h1)). Qed.
Lemma lem5731990 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) : term611 _120082 x t.
Proof. exact (fun h0 : term598 _120082 x t => @lem5731989 _120082 _120196 t f x op h1). Qed.
Lemma lem5731992 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5731993 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term611 _120082 x t) = (@IN _120082 x t).
Proof. exact (@lem5731992 (@IN _120082 x t)). Qed.
Lemma lem5731994 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) : @IN _120082 x t.
Proof. exact (EQ_MP (@lem5731993 _120082 x t) (@lem5731990 _120082 _120196 t f x op h1)). Qed.
Lemma lem5731997 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5731999 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) : (term598 _120082 x t) = (term612 _120082 x t).
Proof. exact (@lem5731997 (@IN _120082 x t)). Qed.
Lemma lem5732002 {_120082 : Type'} (s : _120082 -> Prop) (x : _120082) (t : _120082 -> Prop) (h1 : term753 _120082 s x t) : term612 _120082 x t.
Proof. exact (EQ_MP (@lem5731999 _120082 x t) (@lem5731278 _120082 s x t h1)). Qed.
Lemma lem5732005 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term753 _120082 s x t) (h2 : term158 _120082 _120196 t f x op) : False.
Proof. exact (@lem5732002 _120082 s x t h1 (@lem5731994 _120082 _120196 t f x op h2)). Qed.
Lemma lem5732006 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term753 _120082 s x t) (h2 : term158 _120082 _120196 t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5732005 _120082 _120196 s t f x op h1 h2). Qed.
Lemma lem5732008 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732009 : term610 = False.
Proof. exact (@lem5732008 False). Qed.
Lemma lem5732010 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term753 _120082 s x t) (h2 : term158 _120082 _120196 t f x op) : False.
Proof. exact (EQ_MP (@lem5732009) (@lem5732006 _120082 _120196 s t f x op h1 h2)). Qed.
Lemma lem5732055 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732056 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120082 _120196 f x op.
Proof. exact (fun h0 : term78 _120082 _120196 f x op => @lem5732055 _120082 _120196 f x op h1). Qed.
Lemma lem5732058 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732059 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term607 _120082 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5732058 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732060 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5732059 _120082 _120196 f x op) (@lem5732056 _120082 _120196 f x op h1)). Qed.
Lemma lem5732063 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5732065 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term78 _120082 _120196 f x op) = (term609 _120082 _120196 f x op).
Proof. exact (@lem5732063 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732068 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) : term609 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5732065 _120082 _120196 f x op) (@lem5731282 _120082 _120196 t f x op h1)). Qed.
Lemma lem5732071 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5732068 _120082 _120196 t f x op h1 (@lem5732060 _120082 _120196 f x op h2)). Qed.
Lemma lem5732072 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5732071 _120082 _120196 t f x op h1 h2). Qed.
Lemma lem5732074 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732075 : term610 = False.
Proof. exact (@lem5732074 False). Qed.
Lemma lem5732076 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732075) (@lem5732072 _120082 _120196 t f x op h1 h2)). Qed.
Lemma lem5732077 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732076 _120082 _120196 t f x op h1 h2) (fun h3 : False => @lem5731284 _120082 _120196 f x op h2)). Qed.
Lemma lem5732078 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732077 _120082 _120196 t f x op h1 h2) (@lem5731284 _120082 _120196 f x op h2)). Qed.
Lemma lem5732079 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5731944 _120082 _120196 s f x op h1 h2) (fun h3 : False => @lem5731270 _120082 _120196 f x op h2)). Qed.
Lemma lem5732080 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732079 _120082 _120196 s f x op h1 h2) (@lem5731270 _120082 _120196 f x op h2)). Qed.
Lemma lem5732081 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5731812 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731256 _120082 _120196 f x op h2)). Qed.
Lemma lem5732082 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732081 _120082 _120196 s t f x op h1 h2) (@lem5731256 _120082 _120196 f x op h2)). Qed.
Lemma lem5732083 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732082 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731254 _120082 _120196 f x op h2)). Qed.
Lemma lem5732084 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732083 _120082 _120196 s t f x op h1 h2) (@lem5731254 _120082 _120196 f x op h2)). Qed.
Lemma lem5732085 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5731746 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731246 _120082 _120196 f x op h2)). Qed.
Lemma lem5732086 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732085 _120082 _120196 s t f x op h1 h2) (@lem5731246 _120082 _120196 f x op h2)). Qed.
Lemma lem5732087 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (term598 _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x t => @lem5731680 _120082 x t h1 h2) (fun h3 : False => @lem5731238 _120082 x t h1)). Qed.
Lemma lem5732088 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732087 _120082 x t h1 h2) (@lem5731238 _120082 x t h1)). Qed.
Lemma lem5732089 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (@IN _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x t => @lem5732088 _120082 x t h1 h2) (fun h3 : False => @lem5731236 _120082 x t h2)). Qed.
Lemma lem5732090 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732089 _120082 x t h1 h2) (@lem5731236 _120082 x t h2)). Qed.
Lemma lem5732091 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (term598 _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x t => @lem5731614 _120082 x t h1 h2) (fun h3 : False => @lem5731230 _120082 x t h1)). Qed.
Lemma lem5732092 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732091 _120082 x t h1 h2) (@lem5731230 _120082 x t h1)). Qed.
Lemma lem5732093 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (@IN _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x t => @lem5732092 _120082 x t h1 h2) (fun h3 : False => @lem5731228 _120082 x t h2)). Qed.
Lemma lem5732094 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732093 _120082 x t h1 h2) (@lem5731228 _120082 x t h2)). Qed.
Lemma lem5732095 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5731548 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731224 _120082 _120196 f x op h2)). Qed.
Lemma lem5732096 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732095 _120082 _120196 s t f x op h1 h2) (@lem5731224 _120082 _120196 f x op h2)). Qed.
Lemma lem5732097 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732096 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731222 _120082 _120196 f x op h2)). Qed.
Lemma lem5732098 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732097 _120082 _120196 s t f x op h1 h2) (@lem5731222 _120082 _120196 f x op h2)). Qed.
Lemma lem5732099 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (term598 _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x s => @lem5731482 _120082 x s h1 h2) (fun h3 : False => @lem5731216 _120082 x s h1)). Qed.
Lemma lem5732100 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732099 _120082 x s h1 h2) (@lem5731216 _120082 x s h1)). Qed.
Lemma lem5732101 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (@IN _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x s => @lem5732100 _120082 x s h1 h2) (fun h3 : False => @lem5731212 _120082 x s h2)). Qed.
Lemma lem5732102 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732101 _120082 x s h1 h2) (@lem5731212 _120082 x s h2)). Qed.
Lemma lem5732103 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5731416 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731208 _120082 _120196 f x op h2)). Qed.
Lemma lem5732104 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732103 _120082 _120196 s t f x op h1 h2) (@lem5731208 _120082 _120196 f x op h2)). Qed.
Lemma lem5732105 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (term598 _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x s => @lem5731350 _120082 x s h1 h2) (fun h3 : False => @lem5731200 _120082 x s h1)). Qed.
Lemma lem5732106 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732105 _120082 x s h1 h2) (@lem5731200 _120082 x s h1)). Qed.
Lemma lem5732107 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (@IN _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x s => @lem5732106 _120082 x s h1 h2) (fun h3 : False => @lem5731196 _120082 x s h2)). Qed.
Lemma lem5732108 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732107 _120082 x s h1 h2) (@lem5731196 _120082 x s h2)). Qed.
Lemma lem5732109 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732078 _120082 _120196 t f x op h1 h2) (fun h3 : False => @lem5731192 _120082 _120196 f x op h2)). Qed.
Lemma lem5732110 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732109 _120082 _120196 t f x op h1 h2) (@lem5731192 _120082 _120196 f x op h2)). Qed.
Lemma lem5732111 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732080 _120082 _120196 s f x op h1 h2) (fun h3 : False => @lem5731164 _120082 _120196 f x op h2)). Qed.
Lemma lem5732112 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732111 _120082 _120196 s f x op h1 h2) (@lem5731164 _120082 _120196 f x op h2)). Qed.
Lemma lem5732113 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732084 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731136 _120082 _120196 f x op h2)). Qed.
Lemma lem5732114 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732113 _120082 _120196 s t f x op h1 h2) (@lem5731136 _120082 _120196 f x op h2)). Qed.
Lemma lem5732115 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732114 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731132 _120082 _120196 f x op h2)). Qed.
Lemma lem5732116 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732115 _120082 _120196 s t f x op h1 h2) (@lem5731132 _120082 _120196 f x op h2)). Qed.
Lemma lem5732117 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732086 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731116 _120082 _120196 f x op h2)). Qed.
Lemma lem5732118 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732117 _120082 _120196 s t f x op h1 h2) (@lem5731116 _120082 _120196 f x op h2)). Qed.
Lemma lem5732119 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (term598 _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x t => @lem5732090 _120082 x t h1 h2) (fun h3 : False => @lem5731100 _120082 x t h1)). Qed.
Lemma lem5732120 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732119 _120082 x t h1 h2) (@lem5731100 _120082 x t h1)). Qed.
Lemma lem5732121 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (@IN _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x t => @lem5732120 _120082 x t h1 h2) (fun h3 : False => @lem5731096 _120082 x t h2)). Qed.
Lemma lem5732122 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732121 _120082 x t h1 h2) (@lem5731096 _120082 x t h2)). Qed.
Lemma lem5732123 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (term598 _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x t => @lem5732094 _120082 x t h1 h2) (fun h3 : False => @lem5731084 _120082 x t h1)). Qed.
Lemma lem5732124 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732123 _120082 x t h1 h2) (@lem5731084 _120082 x t h1)). Qed.
Lemma lem5732125 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (@IN _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x t => @lem5732124 _120082 x t h1 h2) (fun h3 : False => @lem5731080 _120082 x t h2)). Qed.
Lemma lem5732126 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732125 _120082 x t h1 h2) (@lem5731080 _120082 x t h2)). Qed.
Lemma lem5732127 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732098 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731072 _120082 _120196 f x op h2)). Qed.
Lemma lem5732128 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732127 _120082 _120196 s t f x op h1 h2) (@lem5731072 _120082 _120196 f x op h2)). Qed.
Lemma lem5732129 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732128 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731068 _120082 _120196 f x op h2)). Qed.
Lemma lem5732130 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732129 _120082 _120196 s t f x op h1 h2) (@lem5731068 _120082 _120196 f x op h2)). Qed.
Lemma lem5732131 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (term598 _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x s => @lem5732102 _120082 x s h1 h2) (fun h3 : False => @lem5731056 _120082 x s h1)). Qed.
Lemma lem5732132 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732131 _120082 x s h1 h2) (@lem5731056 _120082 x s h1)). Qed.
Lemma lem5732133 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (@IN _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x s => @lem5732132 _120082 x s h1 h2) (fun h3 : False => @lem5731048 _120082 x s h2)). Qed.
Lemma lem5732134 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732133 _120082 x s h1 h2) (@lem5731048 _120082 x s h2)). Qed.
Lemma lem5732135 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732104 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731040 _120082 _120196 f x op h2)). Qed.
Lemma lem5732136 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732135 _120082 _120196 s t f x op h1 h2) (@lem5731040 _120082 _120196 f x op h2)). Qed.
Lemma lem5732137 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (term598 _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x s => @lem5732108 _120082 x s h1 h2) (fun h3 : False => @lem5731024 _120082 x s h1)). Qed.
Lemma lem5732138 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732137 _120082 x s h1 h2) (@lem5731024 _120082 x s h1)). Qed.
Lemma lem5732139 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (@IN _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x s => @lem5732138 _120082 x s h1 h2) (fun h3 : False => @lem5731016 _120082 x s h2)). Qed.
Lemma lem5732140 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732139 _120082 x s h1 h2) (@lem5731016 _120082 x s h2)). Qed.
Lemma lem5732141 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732110 _120082 _120196 t f x op h1 h2) (fun h3 : False => @lem5731192 _120082 _120196 f x op h2)). Qed.
Lemma lem5732142 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732141 _120082 _120196 t f x op h1 h2) (@lem5731192 _120082 _120196 f x op h2)). Qed.
Lemma lem5732143 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732112 _120082 _120196 s f x op h1 h2) (fun h3 : False => @lem5731164 _120082 _120196 f x op h2)). Qed.
Lemma lem5732144 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732143 _120082 _120196 s f x op h1 h2) (@lem5731164 _120082 _120196 f x op h2)). Qed.
Lemma lem5732145 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732116 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731136 _120082 _120196 f x op h2)). Qed.
Lemma lem5732146 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732145 _120082 _120196 s t f x op h1 h2) (@lem5731136 _120082 _120196 f x op h2)). Qed.
Lemma lem5732147 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732146 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731132 _120082 _120196 f x op h2)). Qed.
Lemma lem5732148 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732147 _120082 _120196 s t f x op h1 h2) (@lem5731132 _120082 _120196 f x op h2)). Qed.
Lemma lem5732149 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732118 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731116 _120082 _120196 f x op h2)). Qed.
Lemma lem5732150 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732149 _120082 _120196 s t f x op h1 h2) (@lem5731116 _120082 _120196 f x op h2)). Qed.
Lemma lem5732151 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (term598 _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x t => @lem5732122 _120082 x t h1 h2) (fun h3 : False => @lem5731100 _120082 x t h1)). Qed.
Lemma lem5732152 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732151 _120082 x t h1 h2) (@lem5731100 _120082 x t h1)). Qed.
Lemma lem5732153 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (@IN _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x t => @lem5732152 _120082 x t h1 h2) (fun h3 : False => @lem5731096 _120082 x t h2)). Qed.
Lemma lem5732154 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732153 _120082 x t h1 h2) (@lem5731096 _120082 x t h2)). Qed.
Lemma lem5732155 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (term598 _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x t => @lem5732126 _120082 x t h1 h2) (fun h3 : False => @lem5731084 _120082 x t h1)). Qed.
Lemma lem5732156 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732155 _120082 x t h1 h2) (@lem5731084 _120082 x t h1)). Qed.
Lemma lem5732157 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : (@IN _120082 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x t => @lem5732156 _120082 x t h1 h2) (fun h3 : False => @lem5731080 _120082 x t h2)). Qed.
Lemma lem5732158 {_120082 : Type'} (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : @IN _120082 x t) : False.
Proof. exact (EQ_MP (@lem5732157 _120082 x t h1 h2) (@lem5731080 _120082 x t h2)). Qed.
Lemma lem5732159 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732130 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731072 _120082 _120196 f x op h2)). Qed.
Lemma lem5732160 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732159 _120082 _120196 s t f x op h1 h2) (@lem5731072 _120082 _120196 f x op h2)). Qed.
Lemma lem5732161 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732160 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731068 _120082 _120196 f x op h2)). Qed.
Lemma lem5732162 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732161 _120082 _120196 s t f x op h1 h2) (@lem5731068 _120082 _120196 f x op h2)). Qed.
Lemma lem5732163 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (term598 _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x s => @lem5732134 _120082 x s h1 h2) (fun h3 : False => @lem5731056 _120082 x s h1)). Qed.
Lemma lem5732164 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732163 _120082 x s h1 h2) (@lem5731056 _120082 x s h1)). Qed.
Lemma lem5732165 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (@IN _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x s => @lem5732164 _120082 x s h1 h2) (fun h3 : False => @lem5731048 _120082 x s h2)). Qed.
Lemma lem5732166 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732165 _120082 x s h1 h2) (@lem5731048 _120082 x s h2)). Qed.
Lemma lem5732167 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732136 _120082 _120196 s t f x op h1 h2) (fun h3 : False => @lem5731040 _120082 _120196 f x op h2)). Qed.
Lemma lem5732168 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732167 _120082 _120196 s t f x op h1 h2) (@lem5731040 _120082 _120196 f x op h2)). Qed.
Lemma lem5732169 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (term598 _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120082 x s => @lem5732140 _120082 x s h1 h2) (fun h3 : False => @lem5731024 _120082 x s h1)). Qed.
Lemma lem5732170 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732169 _120082 x s h1 h2) (@lem5731024 _120082 x s h1)). Qed.
Lemma lem5732171 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : (@IN _120082 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _120082 x s => @lem5732170 _120082 x s h1 h2) (fun h3 : False => @lem5731016 _120082 x s h2)). Qed.
Lemma lem5732172 {_120082 : Type'} (x : _120082) (s : _120082 -> Prop) (h1 : term598 _120082 x s) (h2 : @IN _120082 x s) : False.
Proof. exact (EQ_MP (@lem5732171 _120082 x s h1 h2) (@lem5731016 _120082 x s h2)). Qed.
Lemma lem5732173 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 t f x op) (h2 : term767 _120082 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5730994 _120082 _120196 s t f x op h2) (fun h0 : term753 _120082 s x t => @lem5732010 _120082 _120196 s t f x op h0 h1) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732142 _120082 _120196 t f x op h1 h0)). Qed.
Lemma lem5732174 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term158 _120082 _120196 s f x op) (h2 : term767 _120082 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5730994 _120082 _120196 s t f x op h2) (fun h0 : term753 _120082 s x t => @lem5731878 _120082 _120196 t s f x op h0 h1) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732144 _120082 _120196 s f x op h1 h0)). Qed.
Lemma lem5732175 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term767 _120082 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5730993 _120082 _120196 s t f x op h1) (fun h0 : term158 _120082 _120196 s f x op => @lem5732174 _120082 _120196 s t f x op h0 h1) (fun h0 : term158 _120082 _120196 t f x op => @lem5732173 _120082 _120196 s t f x op h0 h1)). Qed.
Lemma lem5732176 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (or_elim (@lem5730976 _120082 _120196 s t f x op h1) (fun h0 : term598 _120082 x s => @lem5732150 _120082 _120196 s t f x op h1 h2) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732148 _120082 _120196 s t f x op h1 h2)). Qed.
Lemma lem5732177 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) (t : _120082 -> Prop) (h1 : term598 _120082 x t) (h2 : term770 _120082 _120196 s t f x op) (h3 : @IN _120082 x t) : False.
Proof. exact (or_elim (@lem5730976 _120082 _120196 s t f x op h2) (fun h0 : term598 _120082 x s => @lem5732158 _120082 x t h1 h3) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732154 _120082 x t h1 h3)). Qed.
Lemma lem5732178 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) (t : _120082 -> Prop) (h1 : term770 _120082 _120196 s t f x op) (h2 : @IN _120082 x t) : False.
Proof. exact (or_elim (@lem5730975 _120082 _120196 s t f x op h1) (fun h0 : term598 _120082 x t => @lem5732177 _120082 _120196 s f op x t h0 h1 h2) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732176 _120082 _120196 s t f x op h1 h0)). Qed.
Lemma lem5732179 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) (s : _120082 -> Prop) (h1 : term770 _120082 _120196 s t f x op) (h2 : @IN _120082 x s) : False.
Proof. exact (or_elim (@lem5730976 _120082 _120196 s t f x op h1) (fun h0 : term598 _120082 x s => @lem5732166 _120082 x s h0 h2) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732162 _120082 _120196 s t f x op h1 h0)). Qed.
Lemma lem5732180 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) (s : _120082 -> Prop) (h1 : term770 _120082 _120196 s t f x op) (h2 : @IN _120082 x s) : False.
Proof. exact (or_elim (@lem5730976 _120082 _120196 s t f x op h1) (fun h0 : term598 _120082 x s => @lem5732172 _120082 x s h0 h2) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732168 _120082 _120196 s t f x op h1 h0)). Qed.
Lemma lem5732181 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) (x : _120082) (s : _120082 -> Prop) (h1 : term770 _120082 _120196 s t f x op) (h2 : @IN _120082 x s) : False.
Proof. exact (or_elim (@lem5730975 _120082 _120196 s t f x op h1) (fun h0 : term598 _120082 x t => @lem5732180 _120082 _120196 t f op x s h1 h2) (fun h0 : (f x) = (@neutral _120196 op) => @lem5732179 _120082 _120196 t f op x s h1 h2)). Qed.
Lemma lem5732182 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term770 _120082 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5730978 _120082 _120196 s t f x op h1) (fun h0 : @IN _120082 x s => @lem5732181 _120082 _120196 t f op x s h1 h0) (fun h0 : @IN _120082 x t => @lem5732178 _120082 _120196 s f op x t h1 h0)). Qed.
Lemma lem5732183 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5730970 _120082 _120196 s t f x op h1) (fun h0 : term770 _120082 _120196 s t f x op => @lem5732182 _120082 _120196 s t f x op h0) (fun h0 : term767 _120082 _120196 s t f x op => @lem5732175 _120082 _120196 s t f x op h0)). Qed.
Lemma lem5732184 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : (term727 _120082 _120196 s t f x op) = False.
Proof. exact (prop_ext (fun h2 : term727 _120082 _120196 s t f x op => @lem5732183 _120082 _120196 s t f x op h1) (fun h2 : False => @lem5730746 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5732185 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5732184 _120082 _120196 s t f x op h1) (@lem5730746 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5732186 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term726 _120082 _120196 s t f x op.
Proof. exact (fun h0 : term727 _120082 _120196 s t f x op => @lem5732185 _120082 _120196 s t f x op h0). Qed.
Lemma lem5732187 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5730745 _120082 _120196 s t f x op) (@lem5732186 _120082 _120196 s t f x op)). Qed.
Lemma lem5732192 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term735 _120082 _120196 t f x op.
Proof. exact (fun s : _120082 -> Prop => @lem5732187 _120082 _120196 s t f x op). Qed.
Lemma lem5732197 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term739 _120082 _120196 f x op.
Proof. exact (fun t : _120082 -> Prop => @lem5732192 _120082 _120196 t f x op). Qed.
Lemma lem5732202 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : term743 _120082 _120196 x op.
Proof. exact (fun f : _120082 -> _120196 => @lem5732197 _120082 _120196 f x op). Qed.
Lemma lem5732207 {_120082 _120196 : Type'} (op : type1400 _120196) : term747 _120082 _120196 op.
Proof. exact (fun x : _120082 => @lem5732202 _120082 _120196 x op). Qed.
Lemma lem5732212 {_120082 _120196 : Type'} : term751 _120082 _120196.
Proof. exact (fun op : type1400 _120196 => @lem5732207 _120082 _120196 op). Qed.
Lemma lem5732213 {_120082 _120196 : Type'} : term750 _120082 _120196.
Proof. exact (EQ_MP (@lem5730741 _120082 _120196) (@lem5732212 _120082 _120196)). Qed.
Lemma lem5732214 {_120082 _120196 : Type'} (op : type1400 _120196) : term775 _120082 _120196 op.
Proof. exact (@lem5732213 _120082 _120196 op). Qed.
Lemma lem5732215 {_120082 _120196 : Type'} (op : type1400 _120196) : (term775 _120082 _120196 op) = (term746 _120082 _120196 op).
Proof. exact (eq_refl (term775 _120082 _120196 op)). Qed.
Lemma lem5732216 {_120082 _120196 : Type'} (op : type1400 _120196) : term746 _120082 _120196 op.
Proof. exact (EQ_MP (@lem5732215 _120082 _120196 op) (@lem5732214 _120082 _120196 op)). Qed.
Lemma lem5732217 {_120082 _120196 : Type'} (op : type1400 _120196) (x : _120082) : term776 _120082 _120196 op x.
Proof. exact (@lem5732216 _120082 _120196 op x). Qed.
Lemma lem5732218 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : (term776 _120082 _120196 op x) = (term742 _120082 _120196 x op).
Proof. exact (eq_refl (term776 _120082 _120196 op x)). Qed.
Lemma lem5732219 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) : term742 _120082 _120196 x op.
Proof. exact (EQ_MP (@lem5732218 _120082 _120196 x op) (@lem5732217 _120082 _120196 op x)). Qed.
Lemma lem5732220 {_120082 _120196 : Type'} (x : _120082) (op : type1400 _120196) (f : _120082 -> _120196) : term777 _120082 _120196 x op f.
Proof. exact (@lem5732219 _120082 _120196 x op f). Qed.
Lemma lem5732221 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term777 _120082 _120196 x op f) = (term738 _120082 _120196 f x op).
Proof. exact (eq_refl (term777 _120082 _120196 x op f)). Qed.
Lemma lem5732222 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term738 _120082 _120196 f x op.
Proof. exact (EQ_MP (@lem5732221 _120082 _120196 f x op) (@lem5732220 _120082 _120196 x op f)). Qed.
Lemma lem5732223 {_120082 _120196 : Type'} (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (t : _120082 -> Prop) : term778 _120082 _120196 f x op t.
Proof. exact (@lem5732222 _120082 _120196 f x op t). Qed.
Lemma lem5732224 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term778 _120082 _120196 f x op t) = (term734 _120082 _120196 t f x op).
Proof. exact (eq_refl (term778 _120082 _120196 f x op t)). Qed.
Lemma lem5732225 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term734 _120082 _120196 t f x op.
Proof. exact (EQ_MP (@lem5732224 _120082 _120196 t f x op) (@lem5732223 _120082 _120196 f x op t)). Qed.
Lemma lem5732226 {_120082 _120196 : Type'} (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (s : _120082 -> Prop) : term779 _120082 _120196 t f x op s.
Proof. exact (@lem5732225 _120082 _120196 t f x op s). Qed.
Lemma lem5732227 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term779 _120082 _120196 t f x op s) = (term726 _120082 _120196 s t f x op).
Proof. exact (eq_refl (term779 _120082 _120196 t f x op s)). Qed.
Lemma lem5732228 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term726 _120082 _120196 s t f x op.
Proof. exact (EQ_MP (@lem5732227 _120082 _120196 s t f x op) (@lem5732226 _120082 _120196 t f x op s)). Qed.
Lemma lem5732230 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term726 _120082 _120196 s t f x op.
Proof. exact (@lem5730575 _120082 _120196 s t f x op (@lem5732228 _120082 _120196 s t f x op)). Qed.
Lemma lem5732231 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : False.
Proof. exact (@lem5732230 _120082 _120196 s t f x op (@lem5730559 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5732232 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : (term727 _120082 _120196 s t f x op) = False.
Proof. exact (prop_ext (fun h2 : term727 _120082 _120196 s t f x op => @lem5732231 _120082 _120196 s t f x op h1) (fun h2 : False => @lem5730559 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5732233 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) (h1 : term727 _120082 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5732232 _120082 _120196 s t f x op h1) (@lem5730559 _120082 _120196 s t f x op h1)). Qed.
Lemma lem5732234 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : term726 _120082 _120196 s t f x op.
Proof. exact (fun h0 : term727 _120082 _120196 s t f x op => @lem5732233 _120082 _120196 s t f x op h0). Qed.
Lemma lem5732235 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (x : _120082) (op : type1400 _120196) : (term264 _120082 _120196 s t f x op) = (term295 _120082 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5730558 _120082 _120196 s t f x op) (@lem5732234 _120082 _120196 s t f x op)). Qed.
Lemma lem5732237 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5732238 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)) = (term780 _120120 _120196 s t f x op).
Proof. exact (@lem5732237 ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op))). Qed.
Lemma lem5732239 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term780 _120120 _120196 s t f x op) = ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)).
Proof. exact (SYM (@lem5732238 _120120 _120196 s t f x op)). Qed.
Lemma lem5732240 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : term781 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732243 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term780 _120120 _120196 s t f x op) : term780 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732244 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term782 _120120 _120196 s t f x op.
Proof. exact (fun h0 : term780 _120120 _120196 s t f x op => @lem5732243 _120120 _120196 s t f x op h0). Qed.
Lemma lem5732245 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term782 _120120 _120196 s t f x op) : term782 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732246 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term780 _120120 _120196 s t f x op) : term780 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732247 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term780 _120120 _120196 s t f x op) (h2 : term782 _120120 _120196 s t f x op) : term780 _120120 _120196 s t f x op.
Proof. exact (@lem5732245 _120120 _120196 s t f x op h2 (@lem5732246 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732248 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term780 _120120 _120196 s t f x op) : term783 _120120 _120196 s t f x op.
Proof. exact (fun h0 : term782 _120120 _120196 s t f x op => @lem5732247 _120120 _120196 s t f x op h1 h0). Qed.
Lemma lem5732249 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term782 _120120 _120196 s t f x op) : term782 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732250 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term780 _120120 _120196 s t f x op) (h2 : term782 _120120 _120196 s t f x op) : term780 _120120 _120196 s t f x op.
Proof. exact (@lem5732248 _120120 _120196 s t f x op h1 (@lem5732249 _120120 _120196 s t f x op h2)). Qed.
Lemma lem5732251 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term782 _120120 _120196 s t f x op) : term782 _120120 _120196 s t f x op.
Proof. exact (fun h0 : term780 _120120 _120196 s t f x op => @lem5732250 _120120 _120196 s t f x op h0 h1). Qed.
Lemma lem5732252 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term784 _120120 _120196 s t f x op.
Proof. exact (fun h0 : term782 _120120 _120196 s t f x op => @lem5732251 _120120 _120196 s t f x op h0). Qed.
Lemma lem5732255 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term782 _120120 _120196 s t f x op.
Proof. exact (@lem5732252 _120120 _120196 s t f x op (@lem5732244 _120120 _120196 s t f x op)). Qed.
Lemma lem5732256 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term782 _120120 _120196 s t f x op.
Proof. exact (@lem5732255 _120120 _120196 s t f x op). Qed.
Lemma lem5732278 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5732279 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term780 _120120 _120196 s t f x op) = (term785 _120120 _120196 s t f x op).
Proof. exact (@lem5732278 (term781 _120120 _120196 s t f x op)). Qed.
Lemma lem5732281 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5732282 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term785 _120120 _120196 s t f x op) = ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)).
Proof. exact (@lem5732281 ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op))). Qed.
Lemma lem5732283 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term780 _120120 _120196 s t f x op) = ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)).
Proof. exact (TRANS (@lem5732279 _120120 _120196 s t f x op) (@lem5732282 _120120 _120196 s t f x op)). Qed.
Lemma lem5732294 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term786 _120120 _120196 t f x op) = (term787 _120120 _120196 t f x op).
Proof. exact (fun_ext (fun s : _120120 -> Prop => @lem5732283 _120120 _120196 s t f x op)). Qed.
Lemma lem5732295 {_120120 : Type'} : (@all (_120120 -> Prop)) = (@all (_120120 -> Prop)).
Proof. exact (eq_refl (@all (_120120 -> Prop))). Qed.
Lemma lem5732296 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term788 _120120 _120196 t f x op) = (term789 _120120 _120196 t f x op).
Proof. exact (MK_COMB (@lem5732295 _120120) (@lem5732294 _120120 _120196 t f x op)). Qed.
Lemma lem5732301 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term790 _120120 _120196 f x op) = (term791 _120120 _120196 f x op).
Proof. exact (fun_ext (fun t : _120120 -> Prop => @lem5732296 _120120 _120196 t f x op)). Qed.
Lemma lem5732302 {_120120 : Type'} : (@all (_120120 -> Prop)) = (@all (_120120 -> Prop)).
Proof. exact (eq_refl (@all (_120120 -> Prop))). Qed.
Lemma lem5732303 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term792 _120120 _120196 f x op) = (term793 _120120 _120196 f x op).
Proof. exact (MK_COMB (@lem5732302 _120120) (@lem5732301 _120120 _120196 f x op)). Qed.
Lemma lem5732308 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : (term794 _120120 _120196 x op) = (term795 _120120 _120196 x op).
Proof. exact (fun_ext (fun f : _120120 -> _120196 => @lem5732303 _120120 _120196 f x op)). Qed.
Lemma lem5732309 {_120120 _120196 : Type'} : (@all (_120120 -> _120196)) = (@all (_120120 -> _120196)).
Proof. exact (eq_refl (@all (_120120 -> _120196))). Qed.
Lemma lem5732310 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : (term796 _120120 _120196 x op) = (term797 _120120 _120196 x op).
Proof. exact (MK_COMB (@lem5732309 _120120 _120196) (@lem5732308 _120120 _120196 x op)). Qed.
Lemma lem5732315 {_120120 _120196 : Type'} (op : type1400 _120196) : (term798 _120120 _120196 op) = (term799 _120120 _120196 op).
Proof. exact (fun_ext (fun x : _120120 => @lem5732310 _120120 _120196 x op)). Qed.
Lemma lem5732316 {_120120 : Type'} : (@all _120120) = (@all _120120).
Proof. exact (eq_refl (@all _120120)). Qed.
Lemma lem5732317 {_120120 _120196 : Type'} (op : type1400 _120196) : (term800 _120120 _120196 op) = (term801 _120120 _120196 op).
Proof. exact (MK_COMB (@lem5732316 _120120) (@lem5732315 _120120 _120196 op)). Qed.
Lemma lem5732322 {_120120 _120196 : Type'} : (term802 _120120 _120196) = (term803 _120120 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5732317 _120120 _120196 op)). Qed.
Lemma lem5732323 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5732332 {_120120 _120196 : Type'} : (term804 _120120 _120196) = (term805 _120120 _120196).
Proof. exact (MK_COMB (@lem5732323 _120196) (@lem5732322 _120120 _120196)). Qed.
Lemma lem5732363 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)) = ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)).
Proof. exact (eq_refl ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op))). Qed.
Lemma lem5732364 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term787 _120120 _120196 t f x op) = (term787 _120120 _120196 t f x op).
Proof. exact (fun_ext (fun s : _120120 -> Prop => @lem5732363 _120120 _120196 s t f x op)). Qed.
Lemma lem5732365 {_120120 : Type'} : (@all (_120120 -> Prop)) = (@all (_120120 -> Prop)).
Proof. exact (eq_refl (@all (_120120 -> Prop))). Qed.
Lemma lem5732366 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term789 _120120 _120196 t f x op) = (term789 _120120 _120196 t f x op).
Proof. exact (MK_COMB (@lem5732365 _120120) (@lem5732364 _120120 _120196 t f x op)). Qed.
Lemma lem5732367 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term791 _120120 _120196 f x op) = (term791 _120120 _120196 f x op).
Proof. exact (fun_ext (fun t : _120120 -> Prop => @lem5732366 _120120 _120196 t f x op)). Qed.
Lemma lem5732368 {_120120 : Type'} : (@all (_120120 -> Prop)) = (@all (_120120 -> Prop)).
Proof. exact (eq_refl (@all (_120120 -> Prop))). Qed.
Lemma lem5732369 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term793 _120120 _120196 f x op) = (term793 _120120 _120196 f x op).
Proof. exact (MK_COMB (@lem5732368 _120120) (@lem5732367 _120120 _120196 f x op)). Qed.
Lemma lem5732370 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : (term795 _120120 _120196 x op) = (term795 _120120 _120196 x op).
Proof. exact (fun_ext (fun f : _120120 -> _120196 => @lem5732369 _120120 _120196 f x op)). Qed.
Lemma lem5732371 {_120120 _120196 : Type'} : (@all (_120120 -> _120196)) = (@all (_120120 -> _120196)).
Proof. exact (eq_refl (@all (_120120 -> _120196))). Qed.
Lemma lem5732372 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : (term797 _120120 _120196 x op) = (term797 _120120 _120196 x op).
Proof. exact (MK_COMB (@lem5732371 _120120 _120196) (@lem5732370 _120120 _120196 x op)). Qed.
Lemma lem5732373 {_120120 _120196 : Type'} (op : type1400 _120196) : (term799 _120120 _120196 op) = (term799 _120120 _120196 op).
Proof. exact (fun_ext (fun x : _120120 => @lem5732372 _120120 _120196 x op)). Qed.
Lemma lem5732374 {_120120 : Type'} : (@all _120120) = (@all _120120).
Proof. exact (eq_refl (@all _120120)). Qed.
Lemma lem5732375 {_120120 _120196 : Type'} (op : type1400 _120196) : (term801 _120120 _120196 op) = (term801 _120120 _120196 op).
Proof. exact (MK_COMB (@lem5732374 _120120) (@lem5732373 _120120 _120196 op)). Qed.
Lemma lem5732376 {_120120 _120196 : Type'} : (term803 _120120 _120196) = (term803 _120120 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5732375 _120120 _120196 op)). Qed.
Lemma lem5732377 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5732378 {_120120 _120196 : Type'} : (term805 _120120 _120196) = (term805 _120120 _120196).
Proof. exact (MK_COMB (@lem5732377 _120196) (@lem5732376 _120120 _120196)). Qed.
Lemma lem5732421 {_120120 _120196 : Type'} : (term804 _120120 _120196) = (term805 _120120 _120196).
Proof. exact (TRANS (@lem5732332 _120120 _120196) (@lem5732378 _120120 _120196)). Qed.
Lemma lem5732422 {_120120 _120196 : Type'} : (term805 _120120 _120196) = (term804 _120120 _120196).
Proof. exact (SYM (@lem5732421 _120120 _120196)). Qed.
Lemma lem5732424 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5732425 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)) = (term780 _120120 _120196 s t f x op).
Proof. exact (@lem5732424 ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op))). Qed.
Lemma lem5732426 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term780 _120120 _120196 s t f x op) = ((term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op)).
Proof. exact (SYM (@lem5732425 _120120 _120196 s t f x op)). Qed.
Lemma lem5732427 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : term781 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732436 {_120120 : Type'} (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) : (term806 _120120 s x t) = (term807 _120120 s x t).
Proof. exact (@lem17045 (@IN _120120 x s) (@IN _120120 x t)). Qed.
Lemma lem5732443 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term578 _120120 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5732445 {_120120 : Type'} (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) : (term808 _120120 s x t) = (term809 _120120 s x t).
Proof. exact (MK_COMB (@lem5732444) (@lem5732436 _120120 s x t)). Qed.
Lemma lem5732446 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term810 _120120 _120196 s t f x op) = (term811 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732445 _120120 s x t) (@lem5732443 _120120 _120196 f x op)). Qed.
Lemma lem5732447 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term812 _120120 _120196 s t f x op) = (term810 _120120 _120196 s t f x op).
Proof. exact (@lem17045 (term22 _120120 s x t) (term78 _120120 _120196 f x op)). Qed.
Lemma lem5732448 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term812 _120120 _120196 s t f x op) = (term811 _120120 _120196 s t f x op).
Proof. exact (TRANS (@lem5732447 _120120 _120196 s t f x op) (@lem5732446 _120120 _120196 s t f x op)). Qed.
Lemma lem5732457 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term578 _120120 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732459 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) : (term584 _120120 x s) = (term584 _120120 x s).
Proof. exact (eq_refl (term584 _120120 x s)). Qed.
Lemma lem5732460 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term585 _120120 _120196 s f x op) = (term586 _120120 _120196 s f x op).
Proof. exact (MK_COMB (@lem5732459 _120120 x s) (@lem5732457 _120120 _120196 f x op)). Qed.
Lemma lem5732461 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term404 _120120 _120196 s f x op) = (term585 _120120 _120196 s f x op).
Proof. exact (@lem17045 (@IN _120120 x s) (term78 _120120 _120196 f x op)). Qed.
Lemma lem5732462 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term404 _120120 _120196 s f x op) = (term586 _120120 _120196 s f x op).
Proof. exact (TRANS (@lem5732461 _120120 _120196 s f x op) (@lem5732460 _120120 _120196 s f x op)). Qed.
Lemma lem5732471 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term578 _120120 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732473 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) : (term584 _120120 x t) = (term584 _120120 x t).
Proof. exact (eq_refl (term584 _120120 x t)). Qed.
Lemma lem5732474 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term585 _120120 _120196 t f x op) = (term586 _120120 _120196 t f x op).
Proof. exact (MK_COMB (@lem5732473 _120120 x t) (@lem5732471 _120120 _120196 f x op)). Qed.
Lemma lem5732475 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term404 _120120 _120196 t f x op) = (term585 _120120 _120196 t f x op).
Proof. exact (@lem17045 (@IN _120120 x t) (term78 _120120 _120196 f x op)). Qed.
Lemma lem5732476 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term404 _120120 _120196 t f x op) = (term586 _120120 _120196 t f x op).
Proof. exact (TRANS (@lem5732475 _120120 _120196 t f x op) (@lem5732474 _120120 _120196 t f x op)). Qed.
Lemma lem5732480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5732481 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term705 _120120 _120196 s f x op) = (term706 _120120 _120196 s f x op).
Proof. exact (MK_COMB (@lem5732480) (@lem5732462 _120120 _120196 s f x op)). Qed.
Lemma lem5732482 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term813 _120120 _120196 s t f x op) = (term814 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732481 _120120 _120196 s f x op) (@lem5732476 _120120 _120196 t f x op)). Qed.
Lemma lem5732483 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term815 _120120 _120196 s t f x op) = (term813 _120120 _120196 s t f x op).
Proof. exact (@lem17045 (term158 _120120 _120196 s f x op) (term158 _120120 _120196 t f x op)). Qed.
Lemma lem5732484 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term815 _120120 _120196 s t f x op) = (term814 _120120 _120196 s t f x op).
Proof. exact (TRANS (@lem5732483 _120120 _120196 s t f x op) (@lem5732482 _120120 _120196 s t f x op)). Qed.
Lemma lem5732487 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term349 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op).
Proof. exact (eq_refl (term349 _120120 _120196 s t f x op)). Qed.
Lemma lem5732488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5732489 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term816 _120120 _120196 s t f x op) = (term817 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732488) (@lem5732448 _120120 _120196 s t f x op)). Qed.
Lemma lem5732490 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term818 _120120 _120196 s t f x op) = (term819 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732489 _120120 _120196 s t f x op) (@lem5732487 _120120 _120196 s t f x op)). Qed.
Lemma lem5732492 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term820 _120120 _120196 s t f x op) = (term820 _120120 _120196 s t f x op).
Proof. exact (eq_refl (term820 _120120 _120196 s t f x op)). Qed.
Lemma lem5732493 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term821 _120120 _120196 s t f x op) = (term822 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732492 _120120 _120196 s t f x op) (@lem5732484 _120120 _120196 s t f x op)). Qed.
Lemma lem5732494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5732495 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term823 _120120 _120196 s t f x op) = (term824 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732494) (@lem5732493 _120120 _120196 s t f x op)). Qed.
Lemma lem5732496 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term825 _120120 _120196 s t f x op) = (term826 _120120 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5732495 _120120 _120196 s t f x op) (@lem5732490 _120120 _120196 s t f x op)). Qed.
Lemma lem5732497 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term781 _120120 _120196 s t f x op) = (term825 _120120 _120196 s t f x op).
Proof. exact (@lem17646 (term320 _120120 _120196 s t f x op) (term349 _120120 _120196 s t f x op)). Qed.
Lemma lem5732502 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term781 _120120 _120196 s t f x op) = (term826 _120120 _120196 s t f x op).
Proof. exact (TRANS (@lem5732497 _120120 _120196 s t f x op) (@lem5732496 _120120 _120196 s t f x op)). Qed.
Lemma lem5732651 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : term826 _120120 _120196 s t f x op.
Proof. exact (EQ_MP (@lem5732502 _120120 _120196 s t f x op) (@lem5732427 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732652 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term822 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732653 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term819 _120120 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5732654 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term814 _120120 _120196 s t f x op.
Proof. exact (proj2 (@lem5732652 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732655 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term320 _120120 _120196 s t f x op.
Proof. exact (proj1 (@lem5732652 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732657 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term22 _120120 s x t.
Proof. exact (proj1 (@lem5732655 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732660 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term586 _120120 _120196 s f x op) : term586 _120120 _120196 s f x op.
Proof. exact (h1). Qed.
Lemma lem5732661 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term586 _120120 _120196 t f x op) : term586 _120120 _120196 t f x op.
Proof. exact (h1). Qed.
Lemma lem5732666 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term349 _120120 _120196 s t f x op.
Proof. exact (proj2 (@lem5732653 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732667 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term811 _120120 _120196 s t f x op.
Proof. exact (proj1 (@lem5732653 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732668 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term158 _120120 _120196 t f x op.
Proof. exact (proj2 (@lem5732666 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732669 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term158 _120120 _120196 s f x op.
Proof. exact (proj1 (@lem5732666 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732674 {_120120 : Type'} (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) (h1 : term807 _120120 s x t) : term807 _120120 s x t.
Proof. exact (h1). Qed.
Lemma lem5732693 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) (h1 : term598 _120120 x s) : term598 _120120 x s.
Proof. exact (h1). Qed.
Lemma lem5732709 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732725 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) (h1 : term598 _120120 x t) : term598 _120120 x t.
Proof. exact (h1). Qed.
Lemma lem5732741 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732761 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) (h1 : term598 _120120 x s) : term598 _120120 x s.
Proof. exact (h1). Qed.
Lemma lem5732781 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) (h1 : term598 _120120 x t) : term598 _120120 x t.
Proof. exact (h1). Qed.
Lemma lem5732801 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732809 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) (h1 : term598 _120120 x s) : term598 _120120 x s.
Proof. exact (h1). Qed.
Lemma lem5732811 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term78 _120120 _120196 f x op.
Proof. exact (proj2 (@lem5732655 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732817 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732825 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) (h1 : term598 _120120 x t) : term598 _120120 x t.
Proof. exact (h1). Qed.
Lemma lem5732827 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term78 _120120 _120196 f x op.
Proof. exact (proj2 (@lem5732655 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732833 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732843 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) (h1 : term598 _120120 x s) : term598 _120120 x s.
Proof. exact (h1). Qed.
Lemma lem5732853 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) (h1 : term598 _120120 x t) : term598 _120120 x t.
Proof. exact (h1). Qed.
Lemma lem5732857 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term78 _120120 _120196 f x op.
Proof. exact (proj2 (@lem5732668 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732863 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732908 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : @IN _120120 x s.
Proof. exact (proj1 (@lem5732657 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732909 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term611 _120120 x s.
Proof. exact (fun h0 : term598 _120120 x s => @lem5732908 _120120 _120196 s t f x op h1). Qed.
Lemma lem5732911 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732912 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) : (term611 _120120 x s) = (@IN _120120 x s).
Proof. exact (@lem5732911 (@IN _120120 x s)). Qed.
Lemma lem5732913 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : @IN _120120 x s.
Proof. exact (EQ_MP (@lem5732912 _120120 x s) (@lem5732909 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732916 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5732918 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) : (term598 _120120 x s) = (term612 _120120 x s).
Proof. exact (@lem5732916 (@IN _120120 x s)). Qed.
Lemma lem5732921 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) (h1 : term598 _120120 x s) : term612 _120120 x s.
Proof. exact (EQ_MP (@lem5732918 _120120 x s) (@lem5732809 _120120 x s h1)). Qed.
Lemma lem5732924 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (@lem5732921 _120120 x s h1 (@lem5732913 _120120 _120196 s t f x op h2)). Qed.
Lemma lem5732925 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5732924 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5732927 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732928 : term610 = False.
Proof. exact (@lem5732927 False). Qed.
Lemma lem5732929 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5732928) (@lem5732925 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5732974 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5732975 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120120 _120196 f x op.
Proof. exact (fun h0 : term78 _120120 _120196 f x op => @lem5732974 _120120 _120196 f x op h1). Qed.
Lemma lem5732977 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732978 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term607 _120120 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5732977 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732979 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5732978 _120120 _120196 f x op) (@lem5732975 _120120 _120196 f x op h1)). Qed.
Lemma lem5732982 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5732984 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term78 _120120 _120196 f x op) = (term609 _120120 _120196 f x op).
Proof. exact (@lem5732982 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5732987 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term609 _120120 _120196 f x op.
Proof. exact (EQ_MP (@lem5732984 _120120 _120196 f x op) (@lem5732811 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5732990 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5732987 _120120 _120196 s t f x op h1 (@lem5732979 _120120 _120196 f x op h2)). Qed.
Lemma lem5732991 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5732990 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5732993 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5732994 : term610 = False.
Proof. exact (@lem5732993 False). Qed.
Lemma lem5732995 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5732994) (@lem5732991 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5733040 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : @IN _120120 x t.
Proof. exact (proj2 (@lem5732657 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733041 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term611 _120120 x t.
Proof. exact (fun h0 : term598 _120120 x t => @lem5733040 _120120 _120196 s t f x op h1). Qed.
Lemma lem5733043 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733044 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) : (term611 _120120 x t) = (@IN _120120 x t).
Proof. exact (@lem5733043 (@IN _120120 x t)). Qed.
Lemma lem5733045 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : @IN _120120 x t.
Proof. exact (EQ_MP (@lem5733044 _120120 x t) (@lem5733041 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733048 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5733050 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) : (term598 _120120 x t) = (term612 _120120 x t).
Proof. exact (@lem5733048 (@IN _120120 x t)). Qed.
Lemma lem5733053 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) (h1 : term598 _120120 x t) : term612 _120120 x t.
Proof. exact (EQ_MP (@lem5733050 _120120 x t) (@lem5732825 _120120 x t h1)). Qed.
Lemma lem5733056 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (@lem5733053 _120120 x t h1 (@lem5733045 _120120 _120196 s t f x op h2)). Qed.
Lemma lem5733057 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5733056 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5733059 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733060 : term610 = False.
Proof. exact (@lem5733059 False). Qed.
Lemma lem5733061 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733060) (@lem5733057 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5733106 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5733107 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120120 _120196 f x op.
Proof. exact (fun h0 : term78 _120120 _120196 f x op => @lem5733106 _120120 _120196 f x op h1). Qed.
Lemma lem5733109 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733110 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term607 _120120 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5733109 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733111 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5733110 _120120 _120196 f x op) (@lem5733107 _120120 _120196 f x op h1)). Qed.
Lemma lem5733114 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5733116 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term78 _120120 _120196 f x op) = (term609 _120120 _120196 f x op).
Proof. exact (@lem5733114 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733119 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : term609 _120120 _120196 f x op.
Proof. exact (EQ_MP (@lem5733116 _120120 _120196 f x op) (@lem5732827 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733122 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5733119 _120120 _120196 s t f x op h1 (@lem5733111 _120120 _120196 f x op h2)). Qed.
Lemma lem5733123 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5733122 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5733125 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733126 : term610 = False.
Proof. exact (@lem5733125 False). Qed.
Lemma lem5733127 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733126) (@lem5733123 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5733172 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : @IN _120120 x s.
Proof. exact (proj1 (@lem5732669 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733173 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term611 _120120 x s.
Proof. exact (fun h0 : term598 _120120 x s => @lem5733172 _120120 _120196 s t f x op h1). Qed.
Lemma lem5733175 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733176 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) : (term611 _120120 x s) = (@IN _120120 x s).
Proof. exact (@lem5733175 (@IN _120120 x s)). Qed.
Lemma lem5733177 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : @IN _120120 x s.
Proof. exact (EQ_MP (@lem5733176 _120120 x s) (@lem5733173 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733180 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5733182 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) : (term598 _120120 x s) = (term612 _120120 x s).
Proof. exact (@lem5733180 (@IN _120120 x s)). Qed.
Lemma lem5733185 {_120120 : Type'} (x : _120120) (s : _120120 -> Prop) (h1 : term598 _120120 x s) : term612 _120120 x s.
Proof. exact (EQ_MP (@lem5733182 _120120 x s) (@lem5732843 _120120 x s h1)). Qed.
Lemma lem5733188 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (@lem5733185 _120120 x s h1 (@lem5733177 _120120 _120196 s t f x op h2)). Qed.
Lemma lem5733189 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5733188 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5733191 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733192 : term610 = False.
Proof. exact (@lem5733191 False). Qed.
Lemma lem5733193 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733192) (@lem5733189 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5733238 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : @IN _120120 x t.
Proof. exact (proj1 (@lem5732668 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733239 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term611 _120120 x t.
Proof. exact (fun h0 : term598 _120120 x t => @lem5733238 _120120 _120196 s t f x op h1). Qed.
Lemma lem5733241 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733242 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) : (term611 _120120 x t) = (@IN _120120 x t).
Proof. exact (@lem5733241 (@IN _120120 x t)). Qed.
Lemma lem5733243 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : @IN _120120 x t.
Proof. exact (EQ_MP (@lem5733242 _120120 x t) (@lem5733239 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733246 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5733248 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) : (term598 _120120 x t) = (term612 _120120 x t).
Proof. exact (@lem5733246 (@IN _120120 x t)). Qed.
Lemma lem5733251 {_120120 : Type'} (x : _120120) (t : _120120 -> Prop) (h1 : term598 _120120 x t) : term612 _120120 x t.
Proof. exact (EQ_MP (@lem5733248 _120120 x t) (@lem5732853 _120120 x t h1)). Qed.
Lemma lem5733254 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (@lem5733251 _120120 x t h1 (@lem5733243 _120120 _120196 s t f x op h2)). Qed.
Lemma lem5733255 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5733254 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5733257 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733258 : term610 = False.
Proof. exact (@lem5733257 False). Qed.
Lemma lem5733259 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733258) (@lem5733255 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5733304 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5733305 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120120 _120196 f x op.
Proof. exact (fun h0 : term78 _120120 _120196 f x op => @lem5733304 _120120 _120196 f x op h1). Qed.
Lemma lem5733307 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733308 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term607 _120120 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5733307 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733309 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5733308 _120120 _120196 f x op) (@lem5733305 _120120 _120196 f x op h1)). Qed.
Lemma lem5733312 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5733314 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term78 _120120 _120196 f x op) = (term609 _120120 _120196 f x op).
Proof. exact (@lem5733312 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733317 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : term609 _120120 _120196 f x op.
Proof. exact (EQ_MP (@lem5733314 _120120 _120196 f x op) (@lem5732857 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733320 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5733317 _120120 _120196 s t f x op h1 (@lem5733309 _120120 _120196 f x op h2)). Qed.
Lemma lem5733321 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5733320 _120120 _120196 s t f x op h1 h2). Qed.
Lemma lem5733323 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5733324 : term610 = False.
Proof. exact (@lem5733323 False). Qed.
Lemma lem5733325 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733324) (@lem5733321 _120120 _120196 s t f x op h1 h2)). Qed.
Lemma lem5733326 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733325 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732863 _120120 _120196 f x op h2)). Qed.
Lemma lem5733327 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733326 _120120 _120196 s t f x op h1 h2) (@lem5732863 _120120 _120196 f x op h2)). Qed.
Lemma lem5733328 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : (term598 _120120 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x t => @lem5733259 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732853 _120120 x t h1)). Qed.
Lemma lem5733329 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733328 _120120 _120196 s t f x op h1 h2) (@lem5732853 _120120 x t h1)). Qed.
Lemma lem5733330 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : (term598 _120120 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x s => @lem5733193 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732843 _120120 x s h1)). Qed.
Lemma lem5733331 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733330 _120120 _120196 s t f x op h1 h2) (@lem5732843 _120120 x s h1)). Qed.
Lemma lem5733332 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733127 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732833 _120120 _120196 f x op h2)). Qed.
Lemma lem5733333 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733332 _120120 _120196 s t f x op h1 h2) (@lem5732833 _120120 _120196 f x op h2)). Qed.
Lemma lem5733334 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : (term598 _120120 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x t => @lem5733061 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732825 _120120 x t h1)). Qed.
Lemma lem5733335 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733334 _120120 _120196 s t f x op h1 h2) (@lem5732825 _120120 x t h1)). Qed.
Lemma lem5733336 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5732995 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732817 _120120 _120196 f x op h2)). Qed.
Lemma lem5733337 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733336 _120120 _120196 s t f x op h1 h2) (@lem5732817 _120120 _120196 f x op h2)). Qed.
Lemma lem5733338 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : (term598 _120120 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x s => @lem5732929 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732809 _120120 x s h1)). Qed.
Lemma lem5733339 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733338 _120120 _120196 s t f x op h1 h2) (@lem5732809 _120120 x s h1)). Qed.
Lemma lem5733340 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733327 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732801 _120120 _120196 f x op h2)). Qed.
Lemma lem5733341 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733340 _120120 _120196 s t f x op h1 h2) (@lem5732801 _120120 _120196 f x op h2)). Qed.
Lemma lem5733342 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : (term598 _120120 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x t => @lem5733329 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732781 _120120 x t h1)). Qed.
Lemma lem5733343 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733342 _120120 _120196 s t f x op h1 h2) (@lem5732781 _120120 x t h1)). Qed.
Lemma lem5733344 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : (term598 _120120 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x s => @lem5733331 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732761 _120120 x s h1)). Qed.
Lemma lem5733345 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733344 _120120 _120196 s t f x op h1 h2) (@lem5732761 _120120 x s h1)). Qed.
Lemma lem5733346 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733333 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732741 _120120 _120196 f x op h2)). Qed.
Lemma lem5733347 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733346 _120120 _120196 s t f x op h1 h2) (@lem5732741 _120120 _120196 f x op h2)). Qed.
Lemma lem5733348 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : (term598 _120120 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x t => @lem5733335 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732725 _120120 x t h1)). Qed.
Lemma lem5733349 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733348 _120120 _120196 s t f x op h1 h2) (@lem5732725 _120120 x t h1)). Qed.
Lemma lem5733350 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733337 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732709 _120120 _120196 f x op h2)). Qed.
Lemma lem5733351 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733350 _120120 _120196 s t f x op h1 h2) (@lem5732709 _120120 _120196 f x op h2)). Qed.
Lemma lem5733352 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : (term598 _120120 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x s => @lem5733339 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732693 _120120 x s h1)). Qed.
Lemma lem5733353 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733352 _120120 _120196 s t f x op h1 h2) (@lem5732693 _120120 x s h1)). Qed.
Lemma lem5733354 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733341 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732801 _120120 _120196 f x op h2)). Qed.
Lemma lem5733355 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733354 _120120 _120196 s t f x op h1 h2) (@lem5732801 _120120 _120196 f x op h2)). Qed.
Lemma lem5733356 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : (term598 _120120 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x t => @lem5733343 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732781 _120120 x t h1)). Qed.
Lemma lem5733357 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733356 _120120 _120196 s t f x op h1 h2) (@lem5732781 _120120 x t h1)). Qed.
Lemma lem5733358 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : (term598 _120120 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x s => @lem5733345 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732761 _120120 x s h1)). Qed.
Lemma lem5733359 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733358 _120120 _120196 s t f x op h1 h2) (@lem5732761 _120120 x s h1)). Qed.
Lemma lem5733360 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733347 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732741 _120120 _120196 f x op h2)). Qed.
Lemma lem5733361 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733360 _120120 _120196 s t f x op h1 h2) (@lem5732741 _120120 _120196 f x op h2)). Qed.
Lemma lem5733362 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : (term598 _120120 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x t => @lem5733349 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732725 _120120 x t h1)). Qed.
Lemma lem5733363 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x t) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733362 _120120 _120196 s t f x op h1 h2) (@lem5732725 _120120 x t h1)). Qed.
Lemma lem5733364 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5733351 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732709 _120120 _120196 f x op h2)). Qed.
Lemma lem5733365 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5733364 _120120 _120196 s t f x op h1 h2) (@lem5732709 _120120 _120196 f x op h2)). Qed.
Lemma lem5733366 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : (term598 _120120 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120120 x s => @lem5733353 _120120 _120196 s t f x op h1 h2) (fun h3 : False => @lem5732693 _120120 x s h1)). Qed.
Lemma lem5733367 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term598 _120120 x s) (h2 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733366 _120120 _120196 s t f x op h1 h2) (@lem5732693 _120120 x s h1)). Qed.
Lemma lem5733368 {_120120 _120196 : Type'} (f : _120120 -> _120196) (op : type1400 _120196) (s : _120120 -> Prop) (x : _120120) (t : _120120 -> Prop) (h1 : term819 _120120 _120196 s t f x op) (h2 : term807 _120120 s x t) : False.
Proof. exact (or_elim (@lem5732674 _120120 s x t h2) (fun h0 : term598 _120120 x s => @lem5733359 _120120 _120196 s t f x op h0 h1) (fun h0 : term598 _120120 x t => @lem5733357 _120120 _120196 s t f x op h0 h1)). Qed.
Lemma lem5733369 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term819 _120120 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5732667 _120120 _120196 s t f x op h1) (fun h0 : term807 _120120 s x t => @lem5733368 _120120 _120196 f op s x t h1 h0) (fun h0 : (f x) = (@neutral _120196 op) => @lem5733355 _120120 _120196 s t f x op h1 h0)). Qed.
Lemma lem5733370 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : term586 _120120 _120196 t f x op) : False.
Proof. exact (or_elim (@lem5732661 _120120 _120196 t f x op h2) (fun h0 : term598 _120120 x t => @lem5733363 _120120 _120196 s t f x op h0 h1) (fun h0 : (f x) = (@neutral _120196 op) => @lem5733361 _120120 _120196 s t f x op h1 h0)). Qed.
Lemma lem5733371 {_120120 _120196 : Type'} (t : _120120 -> Prop) (s : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) (h2 : term586 _120120 _120196 s f x op) : False.
Proof. exact (or_elim (@lem5732660 _120120 _120196 s f x op h2) (fun h0 : term598 _120120 x s => @lem5733367 _120120 _120196 s t f x op h0 h1) (fun h0 : (f x) = (@neutral _120196 op) => @lem5733365 _120120 _120196 s t f x op h1 h0)). Qed.
Lemma lem5733372 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term822 _120120 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5732654 _120120 _120196 s t f x op h1) (fun h0 : term586 _120120 _120196 s f x op => @lem5733371 _120120 _120196 t s f x op h1 h0) (fun h0 : term586 _120120 _120196 t f x op => @lem5733370 _120120 _120196 s t f x op h1 h0)). Qed.
Lemma lem5733373 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5732651 _120120 _120196 s t f x op h1) (fun h0 : term822 _120120 _120196 s t f x op => @lem5733372 _120120 _120196 s t f x op h0) (fun h0 : term819 _120120 _120196 s t f x op => @lem5733369 _120120 _120196 s t f x op h0)). Qed.
Lemma lem5733374 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : (term781 _120120 _120196 s t f x op) = False.
Proof. exact (prop_ext (fun h2 : term781 _120120 _120196 s t f x op => @lem5733373 _120120 _120196 s t f x op h1) (fun h2 : False => @lem5732427 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733375 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733374 _120120 _120196 s t f x op h1) (@lem5732427 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733376 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term780 _120120 _120196 s t f x op.
Proof. exact (fun h0 : term781 _120120 _120196 s t f x op => @lem5733375 _120120 _120196 s t f x op h0). Qed.
Lemma lem5733377 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5732426 _120120 _120196 s t f x op) (@lem5733376 _120120 _120196 s t f x op)). Qed.
Lemma lem5733382 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term789 _120120 _120196 t f x op.
Proof. exact (fun s : _120120 -> Prop => @lem5733377 _120120 _120196 s t f x op). Qed.
Lemma lem5733387 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term793 _120120 _120196 f x op.
Proof. exact (fun t : _120120 -> Prop => @lem5733382 _120120 _120196 t f x op). Qed.
Lemma lem5733392 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : term797 _120120 _120196 x op.
Proof. exact (fun f : _120120 -> _120196 => @lem5733387 _120120 _120196 f x op). Qed.
Lemma lem5733397 {_120120 _120196 : Type'} (op : type1400 _120196) : term801 _120120 _120196 op.
Proof. exact (fun x : _120120 => @lem5733392 _120120 _120196 x op). Qed.
Lemma lem5733402 {_120120 _120196 : Type'} : term805 _120120 _120196.
Proof. exact (fun op : type1400 _120196 => @lem5733397 _120120 _120196 op). Qed.
Lemma lem5733403 {_120120 _120196 : Type'} : term804 _120120 _120196.
Proof. exact (EQ_MP (@lem5732422 _120120 _120196) (@lem5733402 _120120 _120196)). Qed.
Lemma lem5733404 {_120120 _120196 : Type'} (op : type1400 _120196) : term827 _120120 _120196 op.
Proof. exact (@lem5733403 _120120 _120196 op). Qed.
Lemma lem5733405 {_120120 _120196 : Type'} (op : type1400 _120196) : (term827 _120120 _120196 op) = (term800 _120120 _120196 op).
Proof. exact (eq_refl (term827 _120120 _120196 op)). Qed.
Lemma lem5733406 {_120120 _120196 : Type'} (op : type1400 _120196) : term800 _120120 _120196 op.
Proof. exact (EQ_MP (@lem5733405 _120120 _120196 op) (@lem5733404 _120120 _120196 op)). Qed.
Lemma lem5733407 {_120120 _120196 : Type'} (op : type1400 _120196) (x : _120120) : term828 _120120 _120196 op x.
Proof. exact (@lem5733406 _120120 _120196 op x). Qed.
Lemma lem5733408 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : (term828 _120120 _120196 op x) = (term796 _120120 _120196 x op).
Proof. exact (eq_refl (term828 _120120 _120196 op x)). Qed.
Lemma lem5733409 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) : term796 _120120 _120196 x op.
Proof. exact (EQ_MP (@lem5733408 _120120 _120196 x op) (@lem5733407 _120120 _120196 op x)). Qed.
Lemma lem5733410 {_120120 _120196 : Type'} (x : _120120) (op : type1400 _120196) (f : _120120 -> _120196) : term829 _120120 _120196 x op f.
Proof. exact (@lem5733409 _120120 _120196 x op f). Qed.
Lemma lem5733411 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term829 _120120 _120196 x op f) = (term792 _120120 _120196 f x op).
Proof. exact (eq_refl (term829 _120120 _120196 x op f)). Qed.
Lemma lem5733412 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term792 _120120 _120196 f x op.
Proof. exact (EQ_MP (@lem5733411 _120120 _120196 f x op) (@lem5733410 _120120 _120196 x op f)). Qed.
Lemma lem5733413 {_120120 _120196 : Type'} (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (t : _120120 -> Prop) : term830 _120120 _120196 f x op t.
Proof. exact (@lem5733412 _120120 _120196 f x op t). Qed.
Lemma lem5733414 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term830 _120120 _120196 f x op t) = (term788 _120120 _120196 t f x op).
Proof. exact (eq_refl (term830 _120120 _120196 f x op t)). Qed.
Lemma lem5733415 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term788 _120120 _120196 t f x op.
Proof. exact (EQ_MP (@lem5733414 _120120 _120196 t f x op) (@lem5733413 _120120 _120196 f x op t)). Qed.
Lemma lem5733416 {_120120 _120196 : Type'} (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (s : _120120 -> Prop) : term831 _120120 _120196 t f x op s.
Proof. exact (@lem5733415 _120120 _120196 t f x op s). Qed.
Lemma lem5733417 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term831 _120120 _120196 t f x op s) = (term780 _120120 _120196 s t f x op).
Proof. exact (eq_refl (term831 _120120 _120196 t f x op s)). Qed.
Lemma lem5733418 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term780 _120120 _120196 s t f x op.
Proof. exact (EQ_MP (@lem5733417 _120120 _120196 s t f x op) (@lem5733416 _120120 _120196 t f x op s)). Qed.
Lemma lem5733420 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term780 _120120 _120196 s t f x op.
Proof. exact (@lem5732256 _120120 _120196 s t f x op (@lem5733418 _120120 _120196 s t f x op)). Qed.
Lemma lem5733421 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : False.
Proof. exact (@lem5733420 _120120 _120196 s t f x op (@lem5732240 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733422 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : (term781 _120120 _120196 s t f x op) = False.
Proof. exact (prop_ext (fun h2 : term781 _120120 _120196 s t f x op => @lem5733421 _120120 _120196 s t f x op h1) (fun h2 : False => @lem5732240 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733423 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) (h1 : term781 _120120 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5733422 _120120 _120196 s t f x op h1) (@lem5732240 _120120 _120196 s t f x op h1)). Qed.
Lemma lem5733424 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : term780 _120120 _120196 s t f x op.
Proof. exact (fun h0 : term781 _120120 _120196 s t f x op => @lem5733423 _120120 _120196 s t f x op h0). Qed.
Lemma lem5733425 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (x : _120120) (op : type1400 _120196) : (term320 _120120 _120196 s t f x op) = (term349 _120120 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5732239 _120120 _120196 s t f x op) (@lem5733424 _120120 _120196 s t f x op)). Qed.
Lemma lem5733427 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5733428 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)) = (term832 _120158 _120196 s t f x op).
Proof. exact (@lem5733427 ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op))). Qed.
Lemma lem5733429 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term832 _120158 _120196 s t f x op) = ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)).
Proof. exact (SYM (@lem5733428 _120158 _120196 s t f x op)). Qed.
Lemma lem5733430 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : term833 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733433 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term832 _120158 _120196 s t f x op) : term832 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733434 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term834 _120158 _120196 s t f x op.
Proof. exact (fun h0 : term832 _120158 _120196 s t f x op => @lem5733433 _120158 _120196 s t f x op h0). Qed.
Lemma lem5733435 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term834 _120158 _120196 s t f x op) : term834 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733436 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term832 _120158 _120196 s t f x op) : term832 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733437 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term832 _120158 _120196 s t f x op) (h2 : term834 _120158 _120196 s t f x op) : term832 _120158 _120196 s t f x op.
Proof. exact (@lem5733435 _120158 _120196 s t f x op h2 (@lem5733436 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733438 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term832 _120158 _120196 s t f x op) : term835 _120158 _120196 s t f x op.
Proof. exact (fun h0 : term834 _120158 _120196 s t f x op => @lem5733437 _120158 _120196 s t f x op h1 h0). Qed.
Lemma lem5733439 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term834 _120158 _120196 s t f x op) : term834 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733440 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term832 _120158 _120196 s t f x op) (h2 : term834 _120158 _120196 s t f x op) : term832 _120158 _120196 s t f x op.
Proof. exact (@lem5733438 _120158 _120196 s t f x op h1 (@lem5733439 _120158 _120196 s t f x op h2)). Qed.
Lemma lem5733441 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term834 _120158 _120196 s t f x op) : term834 _120158 _120196 s t f x op.
Proof. exact (fun h0 : term832 _120158 _120196 s t f x op => @lem5733440 _120158 _120196 s t f x op h0 h1). Qed.
Lemma lem5733442 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term836 _120158 _120196 s t f x op.
Proof. exact (fun h0 : term834 _120158 _120196 s t f x op => @lem5733441 _120158 _120196 s t f x op h0). Qed.
Lemma lem5733445 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term834 _120158 _120196 s t f x op.
Proof. exact (@lem5733442 _120158 _120196 s t f x op (@lem5733434 _120158 _120196 s t f x op)). Qed.
Lemma lem5733446 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term834 _120158 _120196 s t f x op.
Proof. exact (@lem5733445 _120158 _120196 s t f x op). Qed.
Lemma lem5733468 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5733469 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term832 _120158 _120196 s t f x op) = (term837 _120158 _120196 s t f x op).
Proof. exact (@lem5733468 (term833 _120158 _120196 s t f x op)). Qed.
Lemma lem5733471 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5733472 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term837 _120158 _120196 s t f x op) = ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)).
Proof. exact (@lem5733471 ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op))). Qed.
Lemma lem5733473 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term832 _120158 _120196 s t f x op) = ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)).
Proof. exact (TRANS (@lem5733469 _120158 _120196 s t f x op) (@lem5733472 _120158 _120196 s t f x op)). Qed.
Lemma lem5733484 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term838 _120158 _120196 t f x op) = (term839 _120158 _120196 t f x op).
Proof. exact (fun_ext (fun s : _120158 -> Prop => @lem5733473 _120158 _120196 s t f x op)). Qed.
Lemma lem5733485 {_120158 : Type'} : (@all (_120158 -> Prop)) = (@all (_120158 -> Prop)).
Proof. exact (eq_refl (@all (_120158 -> Prop))). Qed.
Lemma lem5733486 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term840 _120158 _120196 t f x op) = (term841 _120158 _120196 t f x op).
Proof. exact (MK_COMB (@lem5733485 _120158) (@lem5733484 _120158 _120196 t f x op)). Qed.
Lemma lem5733491 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term842 _120158 _120196 f x op) = (term843 _120158 _120196 f x op).
Proof. exact (fun_ext (fun t : _120158 -> Prop => @lem5733486 _120158 _120196 t f x op)). Qed.
Lemma lem5733492 {_120158 : Type'} : (@all (_120158 -> Prop)) = (@all (_120158 -> Prop)).
Proof. exact (eq_refl (@all (_120158 -> Prop))). Qed.
Lemma lem5733493 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term844 _120158 _120196 f x op) = (term845 _120158 _120196 f x op).
Proof. exact (MK_COMB (@lem5733492 _120158) (@lem5733491 _120158 _120196 f x op)). Qed.
Lemma lem5733498 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : (term846 _120158 _120196 x op) = (term847 _120158 _120196 x op).
Proof. exact (fun_ext (fun f : _120158 -> _120196 => @lem5733493 _120158 _120196 f x op)). Qed.
Lemma lem5733499 {_120158 _120196 : Type'} : (@all (_120158 -> _120196)) = (@all (_120158 -> _120196)).
Proof. exact (eq_refl (@all (_120158 -> _120196))). Qed.
Lemma lem5733500 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : (term848 _120158 _120196 x op) = (term849 _120158 _120196 x op).
Proof. exact (MK_COMB (@lem5733499 _120158 _120196) (@lem5733498 _120158 _120196 x op)). Qed.
Lemma lem5733505 {_120158 _120196 : Type'} (op : type1400 _120196) : (term850 _120158 _120196 op) = (term851 _120158 _120196 op).
Proof. exact (fun_ext (fun x : _120158 => @lem5733500 _120158 _120196 x op)). Qed.
Lemma lem5733506 {_120158 : Type'} : (@all _120158) = (@all _120158).
Proof. exact (eq_refl (@all _120158)). Qed.
Lemma lem5733507 {_120158 _120196 : Type'} (op : type1400 _120196) : (term852 _120158 _120196 op) = (term853 _120158 _120196 op).
Proof. exact (MK_COMB (@lem5733506 _120158) (@lem5733505 _120158 _120196 op)). Qed.
Lemma lem5733512 {_120158 _120196 : Type'} : (term854 _120158 _120196) = (term855 _120158 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5733507 _120158 _120196 op)). Qed.
Lemma lem5733513 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5733522 {_120158 _120196 : Type'} : (term856 _120158 _120196) = (term857 _120158 _120196).
Proof. exact (MK_COMB (@lem5733513 _120196) (@lem5733512 _120158 _120196)). Qed.
Lemma lem5733557 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)) = ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)).
Proof. exact (eq_refl ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op))). Qed.
Lemma lem5733558 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term839 _120158 _120196 t f x op) = (term839 _120158 _120196 t f x op).
Proof. exact (fun_ext (fun s : _120158 -> Prop => @lem5733557 _120158 _120196 s t f x op)). Qed.
Lemma lem5733559 {_120158 : Type'} : (@all (_120158 -> Prop)) = (@all (_120158 -> Prop)).
Proof. exact (eq_refl (@all (_120158 -> Prop))). Qed.
Lemma lem5733560 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term841 _120158 _120196 t f x op) = (term841 _120158 _120196 t f x op).
Proof. exact (MK_COMB (@lem5733559 _120158) (@lem5733558 _120158 _120196 t f x op)). Qed.
Lemma lem5733561 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term843 _120158 _120196 f x op) = (term843 _120158 _120196 f x op).
Proof. exact (fun_ext (fun t : _120158 -> Prop => @lem5733560 _120158 _120196 t f x op)). Qed.
Lemma lem5733562 {_120158 : Type'} : (@all (_120158 -> Prop)) = (@all (_120158 -> Prop)).
Proof. exact (eq_refl (@all (_120158 -> Prop))). Qed.
Lemma lem5733563 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term845 _120158 _120196 f x op) = (term845 _120158 _120196 f x op).
Proof. exact (MK_COMB (@lem5733562 _120158) (@lem5733561 _120158 _120196 f x op)). Qed.
Lemma lem5733564 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : (term847 _120158 _120196 x op) = (term847 _120158 _120196 x op).
Proof. exact (fun_ext (fun f : _120158 -> _120196 => @lem5733563 _120158 _120196 f x op)). Qed.
Lemma lem5733565 {_120158 _120196 : Type'} : (@all (_120158 -> _120196)) = (@all (_120158 -> _120196)).
Proof. exact (eq_refl (@all (_120158 -> _120196))). Qed.
Lemma lem5733566 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : (term849 _120158 _120196 x op) = (term849 _120158 _120196 x op).
Proof. exact (MK_COMB (@lem5733565 _120158 _120196) (@lem5733564 _120158 _120196 x op)). Qed.
Lemma lem5733567 {_120158 _120196 : Type'} (op : type1400 _120196) : (term851 _120158 _120196 op) = (term851 _120158 _120196 op).
Proof. exact (fun_ext (fun x : _120158 => @lem5733566 _120158 _120196 x op)). Qed.
Lemma lem5733568 {_120158 : Type'} : (@all _120158) = (@all _120158).
Proof. exact (eq_refl (@all _120158)). Qed.
Lemma lem5733569 {_120158 _120196 : Type'} (op : type1400 _120196) : (term853 _120158 _120196 op) = (term853 _120158 _120196 op).
Proof. exact (MK_COMB (@lem5733568 _120158) (@lem5733567 _120158 _120196 op)). Qed.
Lemma lem5733570 {_120158 _120196 : Type'} : (term855 _120158 _120196) = (term855 _120158 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5733569 _120158 _120196 op)). Qed.
Lemma lem5733571 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5733572 {_120158 _120196 : Type'} : (term857 _120158 _120196) = (term857 _120158 _120196).
Proof. exact (MK_COMB (@lem5733571 _120196) (@lem5733570 _120158 _120196)). Qed.
Lemma lem5733615 {_120158 _120196 : Type'} : (term856 _120158 _120196) = (term857 _120158 _120196).
Proof. exact (TRANS (@lem5733522 _120158 _120196) (@lem5733572 _120158 _120196)). Qed.
Lemma lem5733616 {_120158 _120196 : Type'} : (term857 _120158 _120196) = (term856 _120158 _120196).
Proof. exact (SYM (@lem5733615 _120158 _120196)). Qed.
Lemma lem5733618 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5733619 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)) = (term832 _120158 _120196 s t f x op).
Proof. exact (@lem5733618 ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op))). Qed.
Lemma lem5733620 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term832 _120158 _120196 s t f x op) = ((term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op)).
Proof. exact (SYM (@lem5733619 _120158 _120196 s t f x op)). Qed.
Lemma lem5733621 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : term833 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733627 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) : (term858 _120158 x t) = (@IN _120158 x t).
Proof. exact (@lem16933 (@IN _120158 x t)). Qed.
Lemma lem5733629 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term584 _120158 x s) = (term584 _120158 x s).
Proof. exact (eq_refl (term584 _120158 x s)). Qed.
Lemma lem5733630 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term859 _120158 s x t) = (term860 _120158 s x t).
Proof. exact (MK_COMB (@lem5733629 _120158 x s) (@lem5733627 _120158 x t)). Qed.
Lemma lem5733631 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term861 _120158 s x t) = (term859 _120158 s x t).
Proof. exact (@lem17045 (@IN _120158 x s) (term598 _120158 x t)). Qed.
Lemma lem5733632 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term861 _120158 s x t) = (term860 _120158 s x t).
Proof. exact (TRANS (@lem5733631 _120158 s x t) (@lem5733630 _120158 s x t)). Qed.
Lemma lem5733639 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term578 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5733641 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) : (term862 _120158 s x t) = (term863 _120158 s x t).
Proof. exact (MK_COMB (@lem5733640) (@lem5733632 _120158 s x t)). Qed.
Lemma lem5733642 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term864 _120158 _120196 s t f x op) = (term865 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733641 _120158 s x t) (@lem5733639 _120158 _120196 f x op)). Qed.
Lemma lem5733643 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term866 _120158 _120196 s t f x op) = (term864 _120158 _120196 s t f x op).
Proof. exact (@lem17045 (term15 _120158 s x t) (term78 _120158 _120196 f x op)). Qed.
Lemma lem5733644 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term866 _120158 _120196 s t f x op) = (term865 _120158 _120196 s t f x op).
Proof. exact (TRANS (@lem5733643 _120158 _120196 s t f x op) (@lem5733642 _120158 _120196 s t f x op)). Qed.
Lemma lem5733653 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term578 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733655 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term584 _120158 x s) = (term584 _120158 x s).
Proof. exact (eq_refl (term584 _120158 x s)). Qed.
Lemma lem5733656 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term585 _120158 _120196 s f x op) = (term586 _120158 _120196 s f x op).
Proof. exact (MK_COMB (@lem5733655 _120158 x s) (@lem5733653 _120158 _120196 f x op)). Qed.
Lemma lem5733657 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term404 _120158 _120196 s f x op) = (term585 _120158 _120196 s f x op).
Proof. exact (@lem17045 (@IN _120158 x s) (term78 _120158 _120196 f x op)). Qed.
Lemma lem5733658 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term404 _120158 _120196 s f x op) = (term586 _120158 _120196 s f x op).
Proof. exact (TRANS (@lem5733657 _120158 _120196 s f x op) (@lem5733656 _120158 _120196 s f x op)). Qed.
Lemma lem5733667 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term578 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5733669 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) : (term584 _120158 x t) = (term584 _120158 x t).
Proof. exact (eq_refl (term584 _120158 x t)). Qed.
Lemma lem5733670 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term585 _120158 _120196 t f x op) = (term586 _120158 _120196 t f x op).
Proof. exact (MK_COMB (@lem5733669 _120158 x t) (@lem5733667 _120158 _120196 f x op)). Qed.
Lemma lem5733671 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term404 _120158 _120196 t f x op) = (term585 _120158 _120196 t f x op).
Proof. exact (@lem17045 (@IN _120158 x t) (term78 _120158 _120196 f x op)). Qed.
Lemma lem5733672 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term404 _120158 _120196 t f x op) = (term586 _120158 _120196 t f x op).
Proof. exact (TRANS (@lem5733671 _120158 _120196 t f x op) (@lem5733670 _120158 _120196 t f x op)). Qed.
Lemma lem5733677 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term867 _120158 _120196 t f x op) = (term158 _120158 _120196 t f x op).
Proof. exact (@lem16933 (term158 _120158 _120196 t f x op)). Qed.
Lemma lem5733678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5733679 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term705 _120158 _120196 s f x op) = (term706 _120158 _120196 s f x op).
Proof. exact (MK_COMB (@lem5733678) (@lem5733658 _120158 _120196 s f x op)). Qed.
Lemma lem5733680 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term868 _120158 _120196 s t f x op) = (term869 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733679 _120158 _120196 s f x op) (@lem5733677 _120158 _120196 t f x op)). Qed.
Lemma lem5733681 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term870 _120158 _120196 s t f x op) = (term868 _120158 _120196 s t f x op).
Proof. exact (@lem17045 (term158 _120158 _120196 s f x op) (term404 _120158 _120196 t f x op)). Qed.
Lemma lem5733682 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term870 _120158 _120196 s t f x op) = (term869 _120158 _120196 s t f x op).
Proof. exact (TRANS (@lem5733681 _120158 _120196 s t f x op) (@lem5733680 _120158 _120196 s t f x op)). Qed.
Lemma lem5733684 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term237 _120158 _120196 s f x op) = (term237 _120158 _120196 s f x op).
Proof. exact (eq_refl (term237 _120158 _120196 s f x op)). Qed.
Lemma lem5733685 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term405 _120158 _120196 s t f x op) = (term871 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733684 _120158 _120196 s f x op) (@lem5733672 _120158 _120196 t f x op)). Qed.
Lemma lem5733686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5733687 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term872 _120158 _120196 s t f x op) = (term873 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733686) (@lem5733644 _120158 _120196 s t f x op)). Qed.
Lemma lem5733688 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term874 _120158 _120196 s t f x op) = (term875 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733687 _120158 _120196 s t f x op) (@lem5733685 _120158 _120196 s t f x op)). Qed.
Lemma lem5733690 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term876 _120158 _120196 s t f x op) = (term876 _120158 _120196 s t f x op).
Proof. exact (eq_refl (term876 _120158 _120196 s t f x op)). Qed.
Lemma lem5733691 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term877 _120158 _120196 s t f x op) = (term878 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733690 _120158 _120196 s t f x op) (@lem5733682 _120158 _120196 s t f x op)). Qed.
Lemma lem5733692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5733693 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term879 _120158 _120196 s t f x op) = (term880 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733692) (@lem5733691 _120158 _120196 s t f x op)). Qed.
Lemma lem5733694 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term881 _120158 _120196 s t f x op) = (term882 _120158 _120196 s t f x op).
Proof. exact (MK_COMB (@lem5733693 _120158 _120196 s t f x op) (@lem5733688 _120158 _120196 s t f x op)). Qed.
Lemma lem5733695 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term833 _120158 _120196 s t f x op) = (term881 _120158 _120196 s t f x op).
Proof. exact (@lem17646 (term374 _120158 _120196 s t f x op) (term405 _120158 _120196 s t f x op)). Qed.
Lemma lem5733700 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term833 _120158 _120196 s t f x op) = (term882 _120158 _120196 s t f x op).
Proof. exact (TRANS (@lem5733695 _120158 _120196 s t f x op) (@lem5733694 _120158 _120196 s t f x op)). Qed.
Lemma lem5733849 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : term882 _120158 _120196 s t f x op.
Proof. exact (EQ_MP (@lem5733700 _120158 _120196 s t f x op) (@lem5733621 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733850 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term878 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733851 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term875 _120158 _120196 s t f x op.
Proof. exact (h1). Qed.
Lemma lem5733852 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term869 _120158 _120196 s t f x op.
Proof. exact (proj2 (@lem5733850 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733853 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term374 _120158 _120196 s t f x op.
Proof. exact (proj1 (@lem5733850 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733855 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term15 _120158 s x t.
Proof. exact (proj1 (@lem5733853 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733858 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term586 _120158 _120196 s f x op) : term586 _120158 _120196 s f x op.
Proof. exact (h1). Qed.
Lemma lem5733859 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term158 _120158 _120196 t f x op) : term158 _120158 _120196 t f x op.
Proof. exact (h1). Qed.
Lemma lem5733864 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term871 _120158 _120196 s t f x op.
Proof. exact (proj2 (@lem5733851 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733865 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term865 _120158 _120196 s t f x op.
Proof. exact (proj1 (@lem5733851 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733866 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term586 _120158 _120196 t f x op.
Proof. exact (proj2 (@lem5733864 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733867 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term158 _120158 _120196 s f x op.
Proof. exact (proj1 (@lem5733864 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5733872 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) (h1 : term860 _120158 s x t) : term860 _120158 s x t.
Proof. exact (h1). Qed.
Lemma lem5733876 {_120158 : Type'} (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) (h1 : term860 _120158 s x t) : term860 _120158 s x t.
Proof. exact (h1). Qed.
Lemma lem5733895 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term598 _120158 x s.
Proof. exact (h1). Qed.
Lemma lem5733911 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5733947 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term598 _120158 x s.
Proof. exact (h1). Qed.
Lemma lem5733959 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) : term598 _120158 x t.
Proof. exact (h1). Qed.
Lemma lem5733963 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : @IN _120158 x t) : @IN _120158 x t.
Proof. exact (h1). Qed.
Lemma lem5733979 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5733995 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term598 _120158 x s.
Proof. exact (h1). Qed.
Lemma lem5734007 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734023 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734027 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734035 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term598 _120158 x s.
Proof. exact (h1). Qed.
Lemma lem5734037 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term78 _120158 _120196 f x op.
Proof. exact (proj2 (@lem5733853 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734043 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734049 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term598 _120158 x t.
Proof. exact (proj2 (@lem5733855 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734061 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term598 _120158 x s.
Proof. exact (h1). Qed.
Lemma lem5734067 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) : term598 _120158 x t.
Proof. exact (h1). Qed.
Lemma lem5734069 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : @IN _120158 x t) : @IN _120158 x t.
Proof. exact (h1). Qed.
Lemma lem5734073 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term78 _120158 _120196 f x op.
Proof. exact (proj2 (@lem5733867 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734077 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734085 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term598 _120158 x s.
Proof. exact (h1). Qed.
Lemma lem5734089 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term78 _120158 _120196 f x op.
Proof. exact (proj2 (@lem5733867 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734091 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734097 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term78 _120158 _120196 f x op.
Proof. exact (proj2 (@lem5733867 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734099 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734101 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734146 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : @IN _120158 x s.
Proof. exact (proj1 (@lem5733855 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734147 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term611 _120158 x s.
Proof. exact (fun h0 : term598 _120158 x s => @lem5734146 _120158 _120196 s t f x op h1). Qed.
Lemma lem5734149 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734150 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term611 _120158 x s) = (@IN _120158 x s).
Proof. exact (@lem5734149 (@IN _120158 x s)). Qed.
Lemma lem5734151 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : @IN _120158 x s.
Proof. exact (EQ_MP (@lem5734150 _120158 x s) (@lem5734147 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734154 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734156 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term598 _120158 x s) = (term612 _120158 x s).
Proof. exact (@lem5734154 (@IN _120158 x s)). Qed.
Lemma lem5734159 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term612 _120158 x s.
Proof. exact (EQ_MP (@lem5734156 _120158 x s) (@lem5734035 _120158 x s h1)). Qed.
Lemma lem5734162 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : False.
Proof. exact (@lem5734159 _120158 x s h1 (@lem5734151 _120158 _120196 s t f x op h2)). Qed.
Lemma lem5734163 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5734162 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734165 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734166 : term610 = False.
Proof. exact (@lem5734165 False). Qed.
Lemma lem5734167 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734166) (@lem5734163 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734212 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734213 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120158 _120196 f x op.
Proof. exact (fun h0 : term78 _120158 _120196 f x op => @lem5734212 _120158 _120196 f x op h1). Qed.
Lemma lem5734215 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734216 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term607 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5734215 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734217 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5734216 _120158 _120196 f x op) (@lem5734213 _120158 _120196 f x op h1)). Qed.
Lemma lem5734220 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734222 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term78 _120158 _120196 f x op) = (term609 _120158 _120196 f x op).
Proof. exact (@lem5734220 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734225 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term609 _120158 _120196 f x op.
Proof. exact (EQ_MP (@lem5734222 _120158 _120196 f x op) (@lem5734037 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734228 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5734225 _120158 _120196 s t f x op h1 (@lem5734217 _120158 _120196 f x op h2)). Qed.
Lemma lem5734229 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5734228 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734231 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734232 : term610 = False.
Proof. exact (@lem5734231 False). Qed.
Lemma lem5734233 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734232) (@lem5734229 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734278 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term158 _120158 _120196 t f x op) : @IN _120158 x t.
Proof. exact (proj1 (@lem5733859 _120158 _120196 t f x op h1)). Qed.
Lemma lem5734279 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term158 _120158 _120196 t f x op) : term611 _120158 x t.
Proof. exact (fun h0 : term598 _120158 x t => @lem5734278 _120158 _120196 t f x op h1). Qed.
Lemma lem5734281 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734282 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) : (term611 _120158 x t) = (@IN _120158 x t).
Proof. exact (@lem5734281 (@IN _120158 x t)). Qed.
Lemma lem5734283 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term158 _120158 _120196 t f x op) : @IN _120158 x t.
Proof. exact (EQ_MP (@lem5734282 _120158 x t) (@lem5734279 _120158 _120196 t f x op h1)). Qed.
Lemma lem5734286 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734288 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) : (term598 _120158 x t) = (term612 _120158 x t).
Proof. exact (@lem5734286 (@IN _120158 x t)). Qed.
Lemma lem5734291 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : term612 _120158 x t.
Proof. exact (EQ_MP (@lem5734288 _120158 x t) (@lem5734049 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734294 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : term158 _120158 _120196 t f x op) : False.
Proof. exact (@lem5734291 _120158 _120196 s t f x op h1 (@lem5734283 _120158 _120196 t f x op h2)). Qed.
Lemma lem5734295 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : term158 _120158 _120196 t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5734294 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734297 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734298 : term610 = False.
Proof. exact (@lem5734297 False). Qed.
Lemma lem5734299 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : term158 _120158 _120196 t f x op) : False.
Proof. exact (EQ_MP (@lem5734298) (@lem5734295 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734344 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : @IN _120158 x s.
Proof. exact (proj1 (@lem5733867 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734345 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term611 _120158 x s.
Proof. exact (fun h0 : term598 _120158 x s => @lem5734344 _120158 _120196 s t f x op h1). Qed.
Lemma lem5734347 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734348 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term611 _120158 x s) = (@IN _120158 x s).
Proof. exact (@lem5734347 (@IN _120158 x s)). Qed.
Lemma lem5734349 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : @IN _120158 x s.
Proof. exact (EQ_MP (@lem5734348 _120158 x s) (@lem5734345 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734352 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734354 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term598 _120158 x s) = (term612 _120158 x s).
Proof. exact (@lem5734352 (@IN _120158 x s)). Qed.
Lemma lem5734357 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term612 _120158 x s.
Proof. exact (EQ_MP (@lem5734354 _120158 x s) (@lem5734061 _120158 x s h1)). Qed.
Lemma lem5734360 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (@lem5734357 _120158 x s h1 (@lem5734349 _120158 _120196 s t f x op h2)). Qed.
Lemma lem5734361 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5734360 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734363 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734364 : term610 = False.
Proof. exact (@lem5734363 False). Qed.
Lemma lem5734365 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734364) (@lem5734361 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734410 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : @IN _120158 x t) : @IN _120158 x t.
Proof. exact (h1). Qed.
Lemma lem5734411 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : @IN _120158 x t) : term611 _120158 x t.
Proof. exact (fun h0 : term598 _120158 x t => @lem5734410 _120158 x t h1). Qed.
Lemma lem5734413 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734414 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) : (term611 _120158 x t) = (@IN _120158 x t).
Proof. exact (@lem5734413 (@IN _120158 x t)). Qed.
Lemma lem5734415 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : @IN _120158 x t) : @IN _120158 x t.
Proof. exact (EQ_MP (@lem5734414 _120158 x t) (@lem5734411 _120158 x t h1)). Qed.
Lemma lem5734418 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734420 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) : (term598 _120158 x t) = (term612 _120158 x t).
Proof. exact (@lem5734418 (@IN _120158 x t)). Qed.
Lemma lem5734423 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) : term612 _120158 x t.
Proof. exact (EQ_MP (@lem5734420 _120158 x t) (@lem5734067 _120158 x t h1)). Qed.
Lemma lem5734426 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (@lem5734423 _120158 x t h1 (@lem5734415 _120158 x t h2)). Qed.
Lemma lem5734427 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : term610.
Proof. exact (fun h0 : ~ False => @lem5734426 _120158 x t h1 h2). Qed.
Lemma lem5734429 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734430 : term610 = False.
Proof. exact (@lem5734429 False). Qed.
Lemma lem5734431 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734430) (@lem5734427 _120158 x t h1 h2)). Qed.
Lemma lem5734476 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734477 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120158 _120196 f x op.
Proof. exact (fun h0 : term78 _120158 _120196 f x op => @lem5734476 _120158 _120196 f x op h1). Qed.
Lemma lem5734479 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734480 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term607 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5734479 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734481 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5734480 _120158 _120196 f x op) (@lem5734477 _120158 _120196 f x op h1)). Qed.
Lemma lem5734484 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734486 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term78 _120158 _120196 f x op) = (term609 _120158 _120196 f x op).
Proof. exact (@lem5734484 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734489 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term609 _120158 _120196 f x op.
Proof. exact (EQ_MP (@lem5734486 _120158 _120196 f x op) (@lem5734073 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734492 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5734489 _120158 _120196 s t f x op h1 (@lem5734481 _120158 _120196 f x op h2)). Qed.
Lemma lem5734493 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5734492 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734495 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734496 : term610 = False.
Proof. exact (@lem5734495 False). Qed.
Lemma lem5734497 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734496) (@lem5734493 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734542 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : @IN _120158 x s.
Proof. exact (proj1 (@lem5733867 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734543 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term611 _120158 x s.
Proof. exact (fun h0 : term598 _120158 x s => @lem5734542 _120158 _120196 s t f x op h1). Qed.
Lemma lem5734545 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734546 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term611 _120158 x s) = (@IN _120158 x s).
Proof. exact (@lem5734545 (@IN _120158 x s)). Qed.
Lemma lem5734547 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : @IN _120158 x s.
Proof. exact (EQ_MP (@lem5734546 _120158 x s) (@lem5734543 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734550 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734552 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) : (term598 _120158 x s) = (term612 _120158 x s).
Proof. exact (@lem5734550 (@IN _120158 x s)). Qed.
Lemma lem5734555 {_120158 : Type'} (x : _120158) (s : _120158 -> Prop) (h1 : term598 _120158 x s) : term612 _120158 x s.
Proof. exact (EQ_MP (@lem5734552 _120158 x s) (@lem5734085 _120158 x s h1)). Qed.
Lemma lem5734558 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (@lem5734555 _120158 x s h1 (@lem5734547 _120158 _120196 s t f x op h2)). Qed.
Lemma lem5734559 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : term610.
Proof. exact (fun h0 : ~ False => @lem5734558 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734561 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734562 : term610 = False.
Proof. exact (@lem5734561 False). Qed.
Lemma lem5734563 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734562) (@lem5734559 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734608 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734609 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120158 _120196 f x op.
Proof. exact (fun h0 : term78 _120158 _120196 f x op => @lem5734608 _120158 _120196 f x op h1). Qed.
Lemma lem5734611 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734612 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term607 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5734611 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734613 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5734612 _120158 _120196 f x op) (@lem5734609 _120158 _120196 f x op h1)). Qed.
Lemma lem5734616 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734618 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term78 _120158 _120196 f x op) = (term609 _120158 _120196 f x op).
Proof. exact (@lem5734616 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734621 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term609 _120158 _120196 f x op.
Proof. exact (EQ_MP (@lem5734618 _120158 _120196 f x op) (@lem5734089 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734624 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5734621 _120158 _120196 s t f x op h1 (@lem5734613 _120158 _120196 f x op h2)). Qed.
Lemma lem5734625 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5734624 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734627 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734628 : term610 = False.
Proof. exact (@lem5734627 False). Qed.
Lemma lem5734629 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734628) (@lem5734625 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734674 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5734675 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : term607 _120158 _120196 f x op.
Proof. exact (fun h0 : term78 _120158 _120196 f x op => @lem5734674 _120158 _120196 f x op h1). Qed.
Lemma lem5734677 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734678 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term607 _120158 _120196 f x op) = ((f x) = (@neutral _120196 op)).
Proof. exact (@lem5734677 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734679 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (f x) = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5734678 _120158 _120196 f x op) (@lem5734675 _120158 _120196 f x op h1)). Qed.
Lemma lem5734682 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5734684 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term78 _120158 _120196 f x op) = (term609 _120158 _120196 f x op).
Proof. exact (@lem5734682 ((f x) = (@neutral _120196 op))). Qed.
Lemma lem5734687 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : term609 _120158 _120196 f x op.
Proof. exact (EQ_MP (@lem5734684 _120158 _120196 f x op) (@lem5734097 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734690 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5734687 _120158 _120196 s t f x op h1 (@lem5734679 _120158 _120196 f x op h2)). Qed.
Lemma lem5734691 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5734690 _120158 _120196 s t f x op h1 h2). Qed.
Lemma lem5734693 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5734694 : term610 = False.
Proof. exact (@lem5734693 False). Qed.
Lemma lem5734695 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734694) (@lem5734691 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734696 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734695 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734101 _120158 _120196 f x op h2)). Qed.
Lemma lem5734697 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734696 _120158 _120196 s t f x op h1 h2) (@lem5734101 _120158 _120196 f x op h2)). Qed.
Lemma lem5734698 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734697 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734099 _120158 _120196 f x op h2)). Qed.
Lemma lem5734699 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734698 _120158 _120196 s t f x op h1 h2) (@lem5734099 _120158 _120196 f x op h2)). Qed.
Lemma lem5734700 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734629 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734091 _120158 _120196 f x op h2)). Qed.
Lemma lem5734701 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734700 _120158 _120196 s t f x op h1 h2) (@lem5734091 _120158 _120196 f x op h2)). Qed.
Lemma lem5734702 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734563 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734085 _120158 x s h1)). Qed.
Lemma lem5734703 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734702 _120158 _120196 s t f x op h1 h2) (@lem5734085 _120158 x s h1)). Qed.
Lemma lem5734704 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734497 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734077 _120158 _120196 f x op h2)). Qed.
Lemma lem5734705 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734704 _120158 _120196 s t f x op h1 h2) (@lem5734077 _120158 _120196 f x op h2)). Qed.
Lemma lem5734706 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : (@IN _120158 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120158 x t => @lem5734431 _120158 x t h1 h2) (fun h3 : False => @lem5734069 _120158 x t h2)). Qed.
Lemma lem5734707 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734706 _120158 x t h1 h2) (@lem5734069 _120158 x t h2)). Qed.
Lemma lem5734708 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : (term598 _120158 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x t => @lem5734707 _120158 x t h1 h2) (fun h3 : False => @lem5734067 _120158 x t h1)). Qed.
Lemma lem5734709 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734708 _120158 x t h1 h2) (@lem5734067 _120158 x t h1)). Qed.
Lemma lem5734710 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734365 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734061 _120158 x s h1)). Qed.
Lemma lem5734711 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734710 _120158 _120196 s t f x op h1 h2) (@lem5734061 _120158 x s h1)). Qed.
Lemma lem5734712 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734233 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734043 _120158 _120196 f x op h2)). Qed.
Lemma lem5734713 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734712 _120158 _120196 s t f x op h1 h2) (@lem5734043 _120158 _120196 f x op h2)). Qed.
Lemma lem5734714 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734167 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734035 _120158 x s h1)). Qed.
Lemma lem5734715 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734714 _120158 _120196 s t f x op h1 h2) (@lem5734035 _120158 x s h1)). Qed.
Lemma lem5734716 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734699 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734027 _120158 _120196 f x op h2)). Qed.
Lemma lem5734717 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734716 _120158 _120196 s t f x op h1 h2) (@lem5734027 _120158 _120196 f x op h2)). Qed.
Lemma lem5734718 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734717 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734023 _120158 _120196 f x op h2)). Qed.
Lemma lem5734719 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734718 _120158 _120196 s t f x op h1 h2) (@lem5734023 _120158 _120196 f x op h2)). Qed.
Lemma lem5734720 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734701 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734007 _120158 _120196 f x op h2)). Qed.
Lemma lem5734721 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734720 _120158 _120196 s t f x op h1 h2) (@lem5734007 _120158 _120196 f x op h2)). Qed.
Lemma lem5734722 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734703 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733995 _120158 x s h1)). Qed.
Lemma lem5734723 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734722 _120158 _120196 s t f x op h1 h2) (@lem5733995 _120158 x s h1)). Qed.
Lemma lem5734724 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734705 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733979 _120158 _120196 f x op h2)). Qed.
Lemma lem5734725 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734724 _120158 _120196 s t f x op h1 h2) (@lem5733979 _120158 _120196 f x op h2)). Qed.
Lemma lem5734726 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : (@IN _120158 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120158 x t => @lem5734709 _120158 x t h1 h2) (fun h3 : False => @lem5733963 _120158 x t h2)). Qed.
Lemma lem5734727 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734726 _120158 x t h1 h2) (@lem5733963 _120158 x t h2)). Qed.
Lemma lem5734728 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : (term598 _120158 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x t => @lem5734727 _120158 x t h1 h2) (fun h3 : False => @lem5733959 _120158 x t h1)). Qed.
Lemma lem5734729 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734728 _120158 x t h1 h2) (@lem5733959 _120158 x t h1)). Qed.
Lemma lem5734730 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734711 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733947 _120158 x s h1)). Qed.
Lemma lem5734731 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734730 _120158 _120196 s t f x op h1 h2) (@lem5733947 _120158 x s h1)). Qed.
Lemma lem5734732 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734713 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733911 _120158 _120196 f x op h2)). Qed.
Lemma lem5734733 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734732 _120158 _120196 s t f x op h1 h2) (@lem5733911 _120158 _120196 f x op h2)). Qed.
Lemma lem5734734 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734715 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733895 _120158 x s h1)). Qed.
Lemma lem5734735 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734734 _120158 _120196 s t f x op h1 h2) (@lem5733895 _120158 x s h1)). Qed.
Lemma lem5734736 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734719 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734027 _120158 _120196 f x op h2)). Qed.
Lemma lem5734737 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734736 _120158 _120196 s t f x op h1 h2) (@lem5734027 _120158 _120196 f x op h2)). Qed.
Lemma lem5734738 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734737 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734023 _120158 _120196 f x op h2)). Qed.
Lemma lem5734739 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734738 _120158 _120196 s t f x op h1 h2) (@lem5734023 _120158 _120196 f x op h2)). Qed.
Lemma lem5734740 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734721 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5734007 _120158 _120196 f x op h2)). Qed.
Lemma lem5734741 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734740 _120158 _120196 s t f x op h1 h2) (@lem5734007 _120158 _120196 f x op h2)). Qed.
Lemma lem5734742 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734723 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733995 _120158 x s h1)). Qed.
Lemma lem5734743 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734742 _120158 _120196 s t f x op h1 h2) (@lem5733995 _120158 x s h1)). Qed.
Lemma lem5734744 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734725 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733979 _120158 _120196 f x op h2)). Qed.
Lemma lem5734745 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734744 _120158 _120196 s t f x op h1 h2) (@lem5733979 _120158 _120196 f x op h2)). Qed.
Lemma lem5734746 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : (@IN _120158 x t) = False.
Proof. exact (prop_ext (fun h3 : @IN _120158 x t => @lem5734729 _120158 x t h1 h2) (fun h3 : False => @lem5733963 _120158 x t h2)). Qed.
Lemma lem5734747 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734746 _120158 x t h1 h2) (@lem5733963 _120158 x t h2)). Qed.
Lemma lem5734748 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : (term598 _120158 x t) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x t => @lem5734747 _120158 x t h1 h2) (fun h3 : False => @lem5733959 _120158 x t h1)). Qed.
Lemma lem5734749 {_120158 : Type'} (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : @IN _120158 x t) : False.
Proof. exact (EQ_MP (@lem5734748 _120158 x t h1 h2) (@lem5733959 _120158 x t h1)). Qed.
Lemma lem5734750 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734731 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733947 _120158 x s h1)). Qed.
Lemma lem5734751 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734750 _120158 _120196 s t f x op h1 h2) (@lem5733947 _120158 x s h1)). Qed.
Lemma lem5734752 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (@neutral _120196 op) => @lem5734733 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733911 _120158 _120196 f x op h2)). Qed.
Lemma lem5734753 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5734752 _120158 _120196 s t f x op h1 h2) (@lem5733911 _120158 _120196 f x op h2)). Qed.
Lemma lem5734754 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : (term598 _120158 x s) = False.
Proof. exact (prop_ext (fun h3 : term598 _120158 x s => @lem5734735 _120158 _120196 s t f x op h1 h2) (fun h3 : False => @lem5733895 _120158 x s h1)). Qed.
Lemma lem5734755 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x s) (h2 : term878 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734754 _120158 _120196 s t f x op h1 h2) (@lem5733895 _120158 x s h1)). Qed.
Lemma lem5734756 {_120158 _120196 : Type'} (f : _120158 -> _120196) (op : type1400 _120196) (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) (h3 : term860 _120158 s x t) : False.
Proof. exact (or_elim (@lem5733876 _120158 s x t h3) (fun h0 : term598 _120158 x s => @lem5734743 _120158 _120196 s t f x op h0 h1) (fun h0 : @IN _120158 x t => @lem5734741 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734757 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) (h2 : (f x) = (@neutral _120196 op)) : False.
Proof. exact (or_elim (@lem5733865 _120158 _120196 s t f x op h1) (fun h0 : term860 _120158 s x t => @lem5734756 _120158 _120196 f op s x t h1 h2 h0) (fun h0 : (f x) = (@neutral _120196 op) => @lem5734739 _120158 _120196 s t f x op h1 h2)). Qed.
Lemma lem5734758 {_120158 _120196 : Type'} (f : _120158 -> _120196) (op : type1400 _120196) (s : _120158 -> Prop) (x : _120158) (t : _120158 -> Prop) (h1 : term598 _120158 x t) (h2 : term875 _120158 _120196 s t f x op) (h3 : term860 _120158 s x t) : False.
Proof. exact (or_elim (@lem5733872 _120158 s x t h3) (fun h0 : term598 _120158 x s => @lem5734751 _120158 _120196 s t f x op h0 h2) (fun h0 : @IN _120158 x t => @lem5734749 _120158 x t h1 h0)). Qed.
Lemma lem5734759 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term598 _120158 x t) (h2 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5733865 _120158 _120196 s t f x op h2) (fun h0 : term860 _120158 s x t => @lem5734758 _120158 _120196 f op s x t h1 h2 h0) (fun h0 : (f x) = (@neutral _120196 op) => @lem5734745 _120158 _120196 s t f x op h2 h0)). Qed.
Lemma lem5734760 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term875 _120158 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5733866 _120158 _120196 s t f x op h1) (fun h0 : term598 _120158 x t => @lem5734759 _120158 _120196 s t f x op h0 h1) (fun h0 : (f x) = (@neutral _120196 op) => @lem5734757 _120158 _120196 s t f x op h1 h0)). Qed.
Lemma lem5734761 {_120158 _120196 : Type'} (t : _120158 -> Prop) (s : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) (h2 : term586 _120158 _120196 s f x op) : False.
Proof. exact (or_elim (@lem5733858 _120158 _120196 s f x op h2) (fun h0 : term598 _120158 x s => @lem5734755 _120158 _120196 s t f x op h0 h1) (fun h0 : (f x) = (@neutral _120196 op) => @lem5734753 _120158 _120196 s t f x op h1 h0)). Qed.
Lemma lem5734762 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term878 _120158 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5733852 _120158 _120196 s t f x op h1) (fun h0 : term586 _120158 _120196 s f x op => @lem5734761 _120158 _120196 t s f x op h1 h0) (fun h0 : term158 _120158 _120196 t f x op => @lem5734299 _120158 _120196 s t f x op h1 h0)). Qed.
Lemma lem5734763 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : False.
Proof. exact (or_elim (@lem5733849 _120158 _120196 s t f x op h1) (fun h0 : term878 _120158 _120196 s t f x op => @lem5734762 _120158 _120196 s t f x op h0) (fun h0 : term875 _120158 _120196 s t f x op => @lem5734760 _120158 _120196 s t f x op h0)). Qed.
Lemma lem5734764 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : (term833 _120158 _120196 s t f x op) = False.
Proof. exact (prop_ext (fun h2 : term833 _120158 _120196 s t f x op => @lem5734763 _120158 _120196 s t f x op h1) (fun h2 : False => @lem5733621 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734765 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734764 _120158 _120196 s t f x op h1) (@lem5733621 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734766 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term832 _120158 _120196 s t f x op.
Proof. exact (fun h0 : term833 _120158 _120196 s t f x op => @lem5734765 _120158 _120196 s t f x op h0). Qed.
Lemma lem5734767 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5733620 _120158 _120196 s t f x op) (@lem5734766 _120158 _120196 s t f x op)). Qed.
Lemma lem5734772 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term841 _120158 _120196 t f x op.
Proof. exact (fun s : _120158 -> Prop => @lem5734767 _120158 _120196 s t f x op). Qed.
Lemma lem5734777 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term845 _120158 _120196 f x op.
Proof. exact (fun t : _120158 -> Prop => @lem5734772 _120158 _120196 t f x op). Qed.
Lemma lem5734782 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : term849 _120158 _120196 x op.
Proof. exact (fun f : _120158 -> _120196 => @lem5734777 _120158 _120196 f x op). Qed.
Lemma lem5734787 {_120158 _120196 : Type'} (op : type1400 _120196) : term853 _120158 _120196 op.
Proof. exact (fun x : _120158 => @lem5734782 _120158 _120196 x op). Qed.
Lemma lem5734792 {_120158 _120196 : Type'} : term857 _120158 _120196.
Proof. exact (fun op : type1400 _120196 => @lem5734787 _120158 _120196 op). Qed.
Lemma lem5734793 {_120158 _120196 : Type'} : term856 _120158 _120196.
Proof. exact (EQ_MP (@lem5733616 _120158 _120196) (@lem5734792 _120158 _120196)). Qed.
Lemma lem5734794 {_120158 _120196 : Type'} (op : type1400 _120196) : term883 _120158 _120196 op.
Proof. exact (@lem5734793 _120158 _120196 op). Qed.
Lemma lem5734795 {_120158 _120196 : Type'} (op : type1400 _120196) : (term883 _120158 _120196 op) = (term852 _120158 _120196 op).
Proof. exact (eq_refl (term883 _120158 _120196 op)). Qed.
Lemma lem5734796 {_120158 _120196 : Type'} (op : type1400 _120196) : term852 _120158 _120196 op.
Proof. exact (EQ_MP (@lem5734795 _120158 _120196 op) (@lem5734794 _120158 _120196 op)). Qed.
Lemma lem5734797 {_120158 _120196 : Type'} (op : type1400 _120196) (x : _120158) : term884 _120158 _120196 op x.
Proof. exact (@lem5734796 _120158 _120196 op x). Qed.
Lemma lem5734798 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : (term884 _120158 _120196 op x) = (term848 _120158 _120196 x op).
Proof. exact (eq_refl (term884 _120158 _120196 op x)). Qed.
Lemma lem5734799 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) : term848 _120158 _120196 x op.
Proof. exact (EQ_MP (@lem5734798 _120158 _120196 x op) (@lem5734797 _120158 _120196 op x)). Qed.
Lemma lem5734800 {_120158 _120196 : Type'} (x : _120158) (op : type1400 _120196) (f : _120158 -> _120196) : term885 _120158 _120196 x op f.
Proof. exact (@lem5734799 _120158 _120196 x op f). Qed.
Lemma lem5734801 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term885 _120158 _120196 x op f) = (term844 _120158 _120196 f x op).
Proof. exact (eq_refl (term885 _120158 _120196 x op f)). Qed.
Lemma lem5734802 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term844 _120158 _120196 f x op.
Proof. exact (EQ_MP (@lem5734801 _120158 _120196 f x op) (@lem5734800 _120158 _120196 x op f)). Qed.
Lemma lem5734803 {_120158 _120196 : Type'} (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (t : _120158 -> Prop) : term886 _120158 _120196 f x op t.
Proof. exact (@lem5734802 _120158 _120196 f x op t). Qed.
Lemma lem5734804 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term886 _120158 _120196 f x op t) = (term840 _120158 _120196 t f x op).
Proof. exact (eq_refl (term886 _120158 _120196 f x op t)). Qed.
Lemma lem5734805 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term840 _120158 _120196 t f x op.
Proof. exact (EQ_MP (@lem5734804 _120158 _120196 t f x op) (@lem5734803 _120158 _120196 f x op t)). Qed.
Lemma lem5734806 {_120158 _120196 : Type'} (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (s : _120158 -> Prop) : term887 _120158 _120196 t f x op s.
Proof. exact (@lem5734805 _120158 _120196 t f x op s). Qed.
Lemma lem5734807 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term887 _120158 _120196 t f x op s) = (term832 _120158 _120196 s t f x op).
Proof. exact (eq_refl (term887 _120158 _120196 t f x op s)). Qed.
Lemma lem5734808 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term832 _120158 _120196 s t f x op.
Proof. exact (EQ_MP (@lem5734807 _120158 _120196 s t f x op) (@lem5734806 _120158 _120196 t f x op s)). Qed.
Lemma lem5734810 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term832 _120158 _120196 s t f x op.
Proof. exact (@lem5733446 _120158 _120196 s t f x op (@lem5734808 _120158 _120196 s t f x op)). Qed.
Lemma lem5734811 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : False.
Proof. exact (@lem5734810 _120158 _120196 s t f x op (@lem5733430 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734812 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : (term833 _120158 _120196 s t f x op) = False.
Proof. exact (prop_ext (fun h2 : term833 _120158 _120196 s t f x op => @lem5734811 _120158 _120196 s t f x op h1) (fun h2 : False => @lem5733430 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734813 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) (h1 : term833 _120158 _120196 s t f x op) : False.
Proof. exact (EQ_MP (@lem5734812 _120158 _120196 s t f x op h1) (@lem5733430 _120158 _120196 s t f x op h1)). Qed.
Lemma lem5734814 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : term832 _120158 _120196 s t f x op.
Proof. exact (fun h0 : term833 _120158 _120196 s t f x op => @lem5734813 _120158 _120196 s t f x op h0). Qed.
Lemma lem5734815 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (x : _120158) (op : type1400 _120196) : (term374 _120158 _120196 s t f x op) = (term405 _120158 _120196 s t f x op).
Proof. exact (EQ_MP (@lem5733429 _120158 _120196 s t f x op) (@lem5734814 _120158 _120196 s t f x op)). Qed.
Lemma lem5734817 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5734818 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)) = (term888 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5734817 ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op))). Qed.
Lemma lem5734819 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term888 _120186 _120195 _120196 x s g f op) = ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)).
Proof. exact (SYM (@lem5734818 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5734820 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : term889 _120186 _120195 _120196 x s g f op.
Proof. exact (h1). Qed.
Lemma lem5734823 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term888 _120186 _120195 _120196 x s g f op) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (h1). Qed.
Lemma lem5734824 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term890 _120186 _120195 _120196 x s g f op.
Proof. exact (fun h0 : term888 _120186 _120195 _120196 x s g f op => @lem5734823 _120186 _120195 _120196 x s g f op h0). Qed.
Lemma lem5734825 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term890 _120186 _120195 _120196 x s g f op) : term890 _120186 _120195 _120196 x s g f op.
Proof. exact (h1). Qed.
Lemma lem5734826 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term888 _120186 _120195 _120196 x s g f op) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (h1). Qed.
Lemma lem5734827 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term888 _120186 _120195 _120196 x s g f op) (h2 : term890 _120186 _120195 _120196 x s g f op) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (@lem5734825 _120186 _120195 _120196 x s g f op h2 (@lem5734826 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5734828 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term888 _120186 _120195 _120196 x s g f op) : term891 _120186 _120195 _120196 x s g f op.
Proof. exact (fun h0 : term890 _120186 _120195 _120196 x s g f op => @lem5734827 _120186 _120195 _120196 x s g f op h1 h0). Qed.
Lemma lem5734829 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term890 _120186 _120195 _120196 x s g f op) : term890 _120186 _120195 _120196 x s g f op.
Proof. exact (h1). Qed.
Lemma lem5734830 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term888 _120186 _120195 _120196 x s g f op) (h2 : term890 _120186 _120195 _120196 x s g f op) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (@lem5734828 _120186 _120195 _120196 x s g f op h1 (@lem5734829 _120186 _120195 _120196 x s g f op h2)). Qed.
Lemma lem5734831 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term890 _120186 _120195 _120196 x s g f op) : term890 _120186 _120195 _120196 x s g f op.
Proof. exact (fun h0 : term888 _120186 _120195 _120196 x s g f op => @lem5734830 _120186 _120195 _120196 x s g f op h0 h1). Qed.
Lemma lem5734832 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term892 _120186 _120195 _120196 x s g f op.
Proof. exact (fun h0 : term890 _120186 _120195 _120196 x s g f op => @lem5734831 _120186 _120195 _120196 x s g f op h0). Qed.
Lemma lem5734835 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term890 _120186 _120195 _120196 x s g f op.
Proof. exact (@lem5734832 _120186 _120195 _120196 x s g f op (@lem5734824 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5734836 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term890 _120186 _120195 _120196 x s g f op.
Proof. exact (@lem5734835 _120186 _120195 _120196 x s g f op). Qed.
Lemma lem5734858 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5734859 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term888 _120186 _120195 _120196 x s g f op) = (term893 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5734858 (term889 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5734861 (t : Prop) : (term555 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5734862 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term893 _120186 _120195 _120196 x s g f op) = ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)).
Proof. exact (@lem5734861 ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op))). Qed.
Lemma lem5734863 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term888 _120186 _120195 _120196 x s g f op) = ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)).
Proof. exact (TRANS (@lem5734859 _120186 _120195 _120196 x s g f op) (@lem5734862 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5734968 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term894 _120186 _120195 _120196 s g f op) = (term502 _120186 _120195 _120196 s g f op).
Proof. exact (fun_ext (fun x : _120186 => @lem5734863 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5734969 {_120186 : Type'} : (@all _120186) = (@all _120186).
Proof. exact (eq_refl (@all _120186)). Qed.
Lemma lem5734970 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term895 _120186 _120195 _120196 s g f op) = (term503 _120186 _120195 _120196 s g f op).
Proof. exact (MK_COMB (@lem5734969 _120186) (@lem5734968 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5734975 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term896 _120186 _120195 _120196 g f op) = (term505 _120186 _120195 _120196 g f op).
Proof. exact (fun_ext (fun s : _120195 -> Prop => @lem5734970 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5734976 {_120195 : Type'} : (@all (_120195 -> Prop)) = (@all (_120195 -> Prop)).
Proof. exact (eq_refl (@all (_120195 -> Prop))). Qed.
Lemma lem5734977 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term897 _120186 _120195 _120196 g f op) = (term507 _120186 _120195 _120196 g f op).
Proof. exact (MK_COMB (@lem5734976 _120195) (@lem5734975 _120186 _120195 _120196 g f op)). Qed.
Lemma lem5734982 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term898 _120186 _120195 _120196 f op) = (term509 _120186 _120195 _120196 f op).
Proof. exact (fun_ext (fun g : _120186 -> _120196 => @lem5734977 _120186 _120195 _120196 g f op)). Qed.
Lemma lem5734983 {_120186 _120196 : Type'} : (@all (_120186 -> _120196)) = (@all (_120186 -> _120196)).
Proof. exact (eq_refl (@all (_120186 -> _120196))). Qed.
Lemma lem5734984 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term899 _120186 _120195 _120196 f op) = (term511 _120186 _120195 _120196 f op).
Proof. exact (MK_COMB (@lem5734983 _120186 _120196) (@lem5734982 _120186 _120195 _120196 f op)). Qed.
Lemma lem5734989 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term900 _120186 _120195 _120196 op) = (term513 _120186 _120195 _120196 op).
Proof. exact (fun_ext (fun f : _120195 -> _120186 => @lem5734984 _120186 _120195 _120196 f op)). Qed.
Lemma lem5734990 {_120186 _120195 : Type'} : (@all (_120195 -> _120186)) = (@all (_120195 -> _120186)).
Proof. exact (eq_refl (@all (_120195 -> _120186))). Qed.
Lemma lem5734991 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term901 _120186 _120195 _120196 op) = (term515 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5734990 _120186 _120195) (@lem5734989 _120186 _120195 _120196 op)). Qed.
Lemma lem5734996 {_120186 _120195 _120196 : Type'} : (term902 _120186 _120195 _120196) = (term903 _120186 _120195 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5734991 _120186 _120195 _120196 op)). Qed.
Lemma lem5734997 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5735006 {_120186 _120195 _120196 : Type'} : (term904 _120186 _120195 _120196) = (term905 _120186 _120195 _120196).
Proof. exact (MK_COMB (@lem5734997 _120196) (@lem5734996 _120186 _120195 _120196)). Qed.
Lemma lem5735017 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term497 _120186 _120195 _120196 x s g f x' op) = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term497 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735018 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term499 _120186 _120195 _120196 x s g f op) = (term499 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735017 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735019 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735020 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term500 _120186 _120195 _120196 x s g f op) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735019 _120195) (@lem5735018 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735023 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term78 _120186 _120196 g x op) = (term78 _120186 _120196 g x op).
Proof. exact (eq_refl (term78 _120186 _120196 g x op)). Qed.
Lemma lem5735028 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term906 _120186 _120195 x f x' s) = (term906 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term906 _120186 _120195 x f x' s)). Qed.
Lemma lem5735029 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term907 _120186 _120195 x f s) = (term907 _120186 _120195 x f s).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735028 _120186 _120195 x f x' s)). Qed.
Lemma lem5735030 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735031 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term428 _120186 _120195 x f s) = (term428 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735030 _120195) (@lem5735029 _120186 _120195 x f s)). Qed.
Lemma lem5735032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735033 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term430 _120186 _120195 x f s) = (term430 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735032) (@lem5735031 _120186 _120195 x f s)). Qed.
Lemma lem5735034 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term432 _120186 _120195 _120196 f s g x op) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735033 _120186 _120195 x f s) (@lem5735023 _120186 _120196 g x op)). Qed.
Lemma lem5735035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735036 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term458 _120186 _120195 _120196 f s g x op) = (term458 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735035) (@lem5735034 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735037 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)) = ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)).
Proof. exact (MK_COMB (@lem5735036 _120186 _120195 _120196 f s g x op) (@lem5735020 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735038 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term502 _120186 _120195 _120196 s g f op) = (term502 _120186 _120195 _120196 s g f op).
Proof. exact (fun_ext (fun x : _120186 => @lem5735037 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735039 {_120186 : Type'} : (@all _120186) = (@all _120186).
Proof. exact (eq_refl (@all _120186)). Qed.
Lemma lem5735040 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term503 _120186 _120195 _120196 s g f op) = (term503 _120186 _120195 _120196 s g f op).
Proof. exact (MK_COMB (@lem5735039 _120186) (@lem5735038 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5735041 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term505 _120186 _120195 _120196 g f op) = (term505 _120186 _120195 _120196 g f op).
Proof. exact (fun_ext (fun s : _120195 -> Prop => @lem5735040 _120186 _120195 _120196 s g f op)). Qed.
Lemma lem5735042 {_120195 : Type'} : (@all (_120195 -> Prop)) = (@all (_120195 -> Prop)).
Proof. exact (eq_refl (@all (_120195 -> Prop))). Qed.
Lemma lem5735043 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term507 _120186 _120195 _120196 g f op) = (term507 _120186 _120195 _120196 g f op).
Proof. exact (MK_COMB (@lem5735042 _120195) (@lem5735041 _120186 _120195 _120196 g f op)). Qed.
Lemma lem5735044 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term509 _120186 _120195 _120196 f op) = (term509 _120186 _120195 _120196 f op).
Proof. exact (fun_ext (fun g : _120186 -> _120196 => @lem5735043 _120186 _120195 _120196 g f op)). Qed.
Lemma lem5735045 {_120186 _120196 : Type'} : (@all (_120186 -> _120196)) = (@all (_120186 -> _120196)).
Proof. exact (eq_refl (@all (_120186 -> _120196))). Qed.
Lemma lem5735046 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term511 _120186 _120195 _120196 f op) = (term511 _120186 _120195 _120196 f op).
Proof. exact (MK_COMB (@lem5735045 _120186 _120196) (@lem5735044 _120186 _120195 _120196 f op)). Qed.
Lemma lem5735047 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term513 _120186 _120195 _120196 op) = (term513 _120186 _120195 _120196 op).
Proof. exact (fun_ext (fun f : _120195 -> _120186 => @lem5735046 _120186 _120195 _120196 f op)). Qed.
Lemma lem5735048 {_120186 _120195 : Type'} : (@all (_120195 -> _120186)) = (@all (_120195 -> _120186)).
Proof. exact (eq_refl (@all (_120195 -> _120186))). Qed.
Lemma lem5735049 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term515 _120186 _120195 _120196 op) = (term515 _120186 _120195 _120196 op).
Proof. exact (MK_COMB (@lem5735048 _120186 _120195) (@lem5735047 _120186 _120195 _120196 op)). Qed.
Lemma lem5735050 {_120186 _120195 _120196 : Type'} : (term903 _120186 _120195 _120196) = (term903 _120186 _120195 _120196).
Proof. exact (fun_ext (fun op : type1400 _120196 => @lem5735049 _120186 _120195 _120196 op)). Qed.
Lemma lem5735051 {_120196 : Type'} : (@all (_120196 -> _120196 -> _120196)) = (@all (_120196 -> _120196 -> _120196)).
Proof. exact (eq_refl (@all (_120196 -> _120196 -> _120196))). Qed.
Lemma lem5735052 {_120186 _120195 _120196 : Type'} : (term905 _120186 _120195 _120196) = (term905 _120186 _120195 _120196).
Proof. exact (MK_COMB (@lem5735051 _120196) (@lem5735050 _120186 _120195 _120196)). Qed.
Lemma lem5735105 {_120186 _120195 _120196 : Type'} : (term904 _120186 _120195 _120196) = (term905 _120186 _120195 _120196).
Proof. exact (TRANS (@lem5735006 _120186 _120195 _120196) (@lem5735052 _120186 _120195 _120196)). Qed.
Lemma lem5735106 {_120186 _120195 _120196 : Type'} : (term905 _120186 _120195 _120196) = (term904 _120186 _120195 _120196).
Proof. exact (SYM (@lem5735105 _120186 _120195 _120196)). Qed.
Lemma lem5735108 (p : Prop) : p = (term547 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5735109 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)) = (term888 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5735108 ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op))). Qed.
Lemma lem5735110 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term888 _120186 _120195 _120196 x s g f op) = ((term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op)).
Proof. exact (SYM (@lem5735109 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735111 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : term889 _120186 _120195 _120196 x s g f op.
Proof. exact (h1). Qed.
Lemma lem5735120 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term908 _120186 _120195 x f x' s) = (term909 _120186 _120195 x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN _120195 x' s)). Qed.
Lemma lem5735123 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term906 _120186 _120195 x f x' s) = (term906 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term906 _120186 _120195 x f x' s)). Qed.
Lemma lem5735124 {_120195 : Type'} (P : _120195 -> Prop) : (term910 _120195 P) = (term911 _120195 P).
Proof. exact (@lem18394 _120195 P). Qed.
Lemma lem5735125 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term912 _120186 _120195 x f s) = (term913 _120186 _120195 x f s).
Proof. exact (@lem5735124 _120195 (term907 _120186 _120195 x f s)). Qed.
Lemma lem5735126 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term914 _120186 _120195 x f s x') = (term906 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term914 _120186 _120195 x f s x')). Qed.
Lemma lem5735127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5735128 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term915 _120186 _120195 x f s x') = (term908 _120186 _120195 x f x' s).
Proof. exact (MK_COMB (@lem5735127) (@lem5735126 _120186 _120195 x f x' s)). Qed.
Lemma lem5735129 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term915 _120186 _120195 x f s x') = (term909 _120186 _120195 x f x' s).
Proof. exact (TRANS (@lem5735128 _120186 _120195 x f x' s) (@lem5735120 _120186 _120195 x f x' s)). Qed.
Lemma lem5735130 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term916 _120186 _120195 x f s) = (term917 _120186 _120195 x f s).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735129 _120186 _120195 x f x' s)). Qed.
Lemma lem5735131 {_120195 : Type'} : (@all _120195) = (@all _120195).
Proof. exact (eq_refl (@all _120195)). Qed.
Lemma lem5735132 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term913 _120186 _120195 x f s) = (term918 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735131 _120195) (@lem5735130 _120186 _120195 x f s)). Qed.
Lemma lem5735133 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term912 _120186 _120195 x f s) = (term918 _120186 _120195 x f s).
Proof. exact (TRANS (@lem5735125 _120186 _120195 x f s) (@lem5735132 _120186 _120195 x f s)). Qed.
Lemma lem5735134 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term907 _120186 _120195 x f s) = (term907 _120186 _120195 x f s).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735123 _120186 _120195 x f x' s)). Qed.
Lemma lem5735135 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735136 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term428 _120186 _120195 x f s) = (term428 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735135 _120195) (@lem5735134 _120186 _120195 x f s)). Qed.
Lemma lem5735137 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term78 _120186 _120196 g x op) = (term78 _120186 _120196 g x op).
Proof. exact (eq_refl (term78 _120186 _120196 g x op)). Qed.
Lemma lem5735140 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term578 _120186 _120196 g x op) = ((g x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((g x) = (@neutral _120196 op))). Qed.
Lemma lem5735141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735142 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term919 _120186 _120195 x f s) = (term920 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735141) (@lem5735133 _120186 _120195 x f s)). Qed.
Lemma lem5735143 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term921 _120186 _120195 _120196 f s g x op) = (term922 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735142 _120186 _120195 x f s) (@lem5735140 _120186 _120196 g x op)). Qed.
Lemma lem5735144 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term923 _120186 _120195 _120196 f s g x op) = (term921 _120186 _120195 _120196 f s g x op).
Proof. exact (@lem17045 (term428 _120186 _120195 x f s) (term78 _120186 _120196 g x op)). Qed.
Lemma lem5735145 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term923 _120186 _120195 _120196 f s g x op) = (term922 _120186 _120195 _120196 f s g x op).
Proof. exact (TRANS (@lem5735144 _120186 _120195 _120196 f s g x op) (@lem5735143 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735147 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term430 _120186 _120195 x f s) = (term430 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735146) (@lem5735136 _120186 _120195 x f s)). Qed.
Lemma lem5735148 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term432 _120186 _120195 _120196 f s g x op) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735147 _120186 _120195 x f s) (@lem5735137 _120186 _120196 g x op)). Qed.
Lemma lem5735156 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term924 _120186 _120195 _120196 g f x op) = ((term463 _120186 _120195 _120196 g f x) = (@neutral _120196 op)).
Proof. exact (@lem16933 ((term463 _120186 _120195 _120196 g f x) = (@neutral _120196 op))). Qed.
Lemma lem5735158 {_120195 : Type'} (x : _120195) (s : _120195 -> Prop) : (term584 _120195 x s) = (term584 _120195 x s).
Proof. exact (eq_refl (term584 _120195 x s)). Qed.
Lemma lem5735159 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term925 _120186 _120195 _120196 s g f x op) = (term926 _120186 _120195 _120196 s g f x op).
Proof. exact (MK_COMB (@lem5735158 _120195 x s) (@lem5735156 _120186 _120195 _120196 g f x op)). Qed.
Lemma lem5735160 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term927 _120186 _120195 _120196 s g f x op) = (term925 _120186 _120195 _120196 s g f x op).
Proof. exact (@lem17045 (@IN _120195 x s) (term467 _120186 _120195 _120196 g f x op)). Qed.
Lemma lem5735161 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x : _120195) (op : type1400 _120196) : (term927 _120186 _120195 _120196 s g f x op) = (term926 _120186 _120195 _120196 s g f x op).
Proof. exact (TRANS (@lem5735160 _120186 _120195 _120196 s g f x op) (@lem5735159 _120186 _120195 _120196 s g f x op)). Qed.
Lemma lem5735166 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) : (term928 _120186 _120195 x f x') = (term928 _120186 _120195 x f x').
Proof. exact (eq_refl (term928 _120186 _120195 x f x')). Qed.
Lemma lem5735167 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term929 _120186 _120195 _120196 x s g f x' op) = (term930 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5735166 _120186 _120195 x f x') (@lem5735161 _120186 _120195 _120196 s g f x' op)). Qed.
Lemma lem5735168 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term931 _120186 _120195 _120196 x s g f x' op) = (term929 _120186 _120195 _120196 x s g f x' op).
Proof. exact (@lem17045 (x = (f x')) (term470 _120186 _120195 _120196 s g f x' op)). Qed.
Lemma lem5735169 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term931 _120186 _120195 _120196 x s g f x' op) = (term930 _120186 _120195 _120196 x s g f x' op).
Proof. exact (TRANS (@lem5735168 _120186 _120195 _120196 x s g f x' op) (@lem5735167 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735172 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term497 _120186 _120195 _120196 x s g f x' op) = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term497 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735173 {_120195 : Type'} (P : _120195 -> Prop) : (term910 _120195 P) = (term911 _120195 P).
Proof. exact (@lem18394 _120195 P). Qed.
Lemma lem5735174 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term932 _120186 _120195 _120196 x s g f op) = (term933 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5735173 _120195 (term499 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735175 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term934 _120186 _120195 _120196 x s g f op x') = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term934 _120186 _120195 _120196 x s g f op x')). Qed.
Lemma lem5735176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5735177 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term935 _120186 _120195 _120196 x s g f op x') = (term931 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5735176) (@lem5735175 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735178 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term935 _120186 _120195 _120196 x s g f op x') = (term930 _120186 _120195 _120196 x s g f x' op).
Proof. exact (TRANS (@lem5735177 _120186 _120195 _120196 x s g f x' op) (@lem5735169 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735179 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term936 _120186 _120195 _120196 x s g f op) = (term937 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735178 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735180 {_120195 : Type'} : (@all _120195) = (@all _120195).
Proof. exact (eq_refl (@all _120195)). Qed.
Lemma lem5735181 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term933 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735180 _120195) (@lem5735179 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735182 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term932 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (TRANS (@lem5735174 _120186 _120195 _120196 x s g f op) (@lem5735181 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735183 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term499 _120186 _120195 _120196 x s g f op) = (term499 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735172 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735184 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735185 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term500 _120186 _120195 _120196 x s g f op) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735184 _120195) (@lem5735183 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735187 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term939 _120186 _120195 _120196 f s g x op) = (term940 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735186) (@lem5735145 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735188 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term941 _120186 _120195 _120196 x s g f op) = (term942 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735187 _120186 _120195 _120196 f s g x op) (@lem5735185 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735190 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term943 _120186 _120195 _120196 f s g x op) = (term943 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735189) (@lem5735148 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735191 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term944 _120186 _120195 _120196 x s g f op) = (term945 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735190 _120186 _120195 _120196 f s g x op) (@lem5735182 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735193 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term946 _120186 _120195 _120196 x s g f op) = (term947 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735192) (@lem5735191 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735194 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term948 _120186 _120195 _120196 x s g f op) = (term949 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735193 _120186 _120195 _120196 x s g f op) (@lem5735188 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735195 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term889 _120186 _120195 _120196 x s g f op) = (term948 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem17646 (term432 _120186 _120195 _120196 f s g x op) (term500 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735196 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term889 _120186 _120195 _120196 x s g f op) = (term949 _120186 _120195 _120196 x s g f op).
Proof. exact (TRANS (@lem5735195 _120186 _120195 _120196 x s g f op) (@lem5735194 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735391 {A : Type'} (P : A -> Prop) (Q : Prop) : (term950 A P Q) = (term951 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5735392 {_120195 : Type'} (P : _120195 -> Prop) (Q : Prop) : (term950 _120195 P Q) = (term951 _120195 P Q).
Proof. exact (@lem5735391 _120195 P Q). Qed.
Lemma lem5735393 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term952 _120186 _120195 _120196 f s g x op) = (term953 _120186 _120195 _120196 f s g x op).
Proof. exact (@lem5735392 _120195 (term907 _120186 _120195 x f s) (term78 _120186 _120196 g x op)). Qed.
Lemma lem5735394 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term914 _120186 _120195 x f s x') = (term906 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term914 _120186 _120195 x f s x')). Qed.
Lemma lem5735395 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term954 _120186 _120195 x f s) = (term907 _120186 _120195 x f s).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735394 _120186 _120195 x f x' s)). Qed.
Lemma lem5735396 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735397 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term955 _120186 _120195 x f s) = (term428 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735396 _120195) (@lem5735395 _120186 _120195 x f s)). Qed.
Lemma lem5735398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735399 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term956 _120186 _120195 x f s) = (term430 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735398) (@lem5735397 _120186 _120195 x f s)). Qed.
Lemma lem5735400 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term78 _120186 _120196 g x op) = (term78 _120186 _120196 g x op).
Proof. exact (eq_refl (term78 _120186 _120196 g x op)). Qed.
Lemma lem5735401 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term952 _120186 _120195 _120196 f s g x op) = (term432 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735399 _120186 _120195 x f s) (@lem5735400 _120186 _120196 g x op)). Qed.
Lemma lem5735402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735403 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term957 _120186 _120195 _120196 f s g x op) = (term458 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735402) (@lem5735401 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735404 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term914 _120186 _120195 x f s x') = (term906 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term914 _120186 _120195 x f s x')). Qed.
Lemma lem5735405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735406 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term958 _120186 _120195 x f s x') = (term959 _120186 _120195 x f x' s).
Proof. exact (MK_COMB (@lem5735405) (@lem5735404 _120186 _120195 x f x' s)). Qed.
Lemma lem5735407 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term78 _120186 _120196 g x op) = (term78 _120186 _120196 g x op).
Proof. exact (eq_refl (term78 _120186 _120196 g x op)). Qed.
Lemma lem5735408 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (x' : _120186) (op : type1400 _120196) : (term960 _120186 _120195 _120196 f s x g x' op) = (term961 _120186 _120195 _120196 f x s g x' op).
Proof. exact (MK_COMB (@lem5735406 _120186 _120195 x' f x s) (@lem5735407 _120186 _120196 g x' op)). Qed.
Lemma lem5735409 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term962 _120186 _120195 _120196 f s g x op) = (term963 _120186 _120195 _120196 f s g x op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735408 _120186 _120195 _120196 f x' s g x op)). Qed.
Lemma lem5735410 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735411 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term953 _120186 _120195 _120196 f s g x op) = (term964 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735410 _120195) (@lem5735409 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735412 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : ((term952 _120186 _120195 _120196 f s g x op) = (term953 _120186 _120195 _120196 f s g x op)) = ((term432 _120186 _120195 _120196 f s g x op) = (term964 _120186 _120195 _120196 f s g x op)).
Proof. exact (MK_COMB (@lem5735403 _120186 _120195 _120196 f s g x op) (@lem5735411 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735413 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term432 _120186 _120195 _120196 f s g x op) = (term964 _120186 _120195 _120196 f s g x op).
Proof. exact (EQ_MP (@lem5735412 _120186 _120195 _120196 f s g x op) (@lem5735393 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735415 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term943 _120186 _120195 _120196 f s g x op) = (term965 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735414) (@lem5735413 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735416 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term938 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (eq_refl (term938 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735417 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term945 _120186 _120195 _120196 x s g f op) = (term966 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735415 _120186 _120195 _120196 f s g x op) (@lem5735416 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735419 {A : Type'} (P : A -> Prop) (Q : Prop) : (term950 A P Q) = (term951 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5735420 {_120195 : Type'} (P : _120195 -> Prop) (Q : Prop) : (term950 _120195 P Q) = (term951 _120195 P Q).
Proof. exact (@lem5735419 _120195 P Q). Qed.
Lemma lem5735421 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term967 _120186 _120195 _120196 x s g f op) = (term968 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5735420 _120195 (term963 _120186 _120195 _120196 f s g x op) (term938 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735422 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (x' : _120186) (op : type1400 _120196) : (term969 _120186 _120195 _120196 f s g x' op x) = (term961 _120186 _120195 _120196 f x s g x' op).
Proof. exact (eq_refl (term969 _120186 _120195 _120196 f s g x' op x)). Qed.
Lemma lem5735423 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term970 _120186 _120195 _120196 f s g x op) = (term963 _120186 _120195 _120196 f s g x op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735422 _120186 _120195 _120196 f x' s g x op)). Qed.
Lemma lem5735424 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735425 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term971 _120186 _120195 _120196 f s g x op) = (term964 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735424 _120195) (@lem5735423 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735427 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term972 _120186 _120195 _120196 f s g x op) = (term965 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735426) (@lem5735425 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735428 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term938 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (eq_refl (term938 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735429 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term967 _120186 _120195 _120196 x s g f op) = (term966 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735427 _120186 _120195 _120196 f s g x op) (@lem5735428 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735431 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term973 _120186 _120195 _120196 x s g f op) = (term974 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735430) (@lem5735429 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735432 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (x' : _120186) (op : type1400 _120196) : (term969 _120186 _120195 _120196 f s g x' op x) = (term961 _120186 _120195 _120196 f x s g x' op).
Proof. exact (eq_refl (term969 _120186 _120195 _120196 f s g x' op x)). Qed.
Lemma lem5735433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735434 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (x : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (x' : _120186) (op : type1400 _120196) : (term975 _120186 _120195 _120196 f s g x' op x) = (term976 _120186 _120195 _120196 f x s g x' op).
Proof. exact (MK_COMB (@lem5735433) (@lem5735432 _120186 _120195 _120196 f x s g x' op)). Qed.
Lemma lem5735435 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term938 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (eq_refl (term938 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735436 {_120186 _120195 _120196 : Type'} (x : _120195) (x' : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term977 _120186 _120195 _120196 x x' s g f op) = (term978 _120186 _120195 _120196 x x' s g f op).
Proof. exact (MK_COMB (@lem5735434 _120186 _120195 _120196 f x s g x' op) (@lem5735435 _120186 _120195 _120196 x' s g f op)). Qed.
Lemma lem5735437 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term979 _120186 _120195 _120196 x s g f op) = (term980 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735436 _120186 _120195 _120196 x' x s g f op)). Qed.
Lemma lem5735438 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735439 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term968 _120186 _120195 _120196 x s g f op) = (term981 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735438 _120195) (@lem5735437 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735440 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term967 _120186 _120195 _120196 x s g f op) = (term968 _120186 _120195 _120196 x s g f op)) = ((term966 _120186 _120195 _120196 x s g f op) = (term981 _120186 _120195 _120196 x s g f op)).
Proof. exact (MK_COMB (@lem5735431 _120186 _120195 _120196 x s g f op) (@lem5735439 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735441 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term966 _120186 _120195 _120196 x s g f op) = (term981 _120186 _120195 _120196 x s g f op).
Proof. exact (EQ_MP (@lem5735440 _120186 _120195 _120196 x s g f op) (@lem5735421 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735442 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term945 _120186 _120195 _120196 x s g f op) = (term981 _120186 _120195 _120196 x s g f op).
Proof. exact (TRANS (@lem5735417 _120186 _120195 _120196 x s g f op) (@lem5735441 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735444 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term947 _120186 _120195 _120196 x s g f op) = (term982 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735443) (@lem5735442 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735446 {A : Type'} (P : Prop) (Q : A -> Prop) : (term983 A P Q) = (term984 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5735447 {_120195 : Type'} (P : Prop) (Q : _120195 -> Prop) : (term983 _120195 P Q) = (term984 _120195 P Q).
Proof. exact (@lem5735446 _120195 P Q). Qed.
Lemma lem5735448 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term985 _120186 _120195 _120196 x s g f op) = (term986 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5735447 _120195 (term922 _120186 _120195 _120196 f s g x op) (term499 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735449 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term934 _120186 _120195 _120196 x s g f op x') = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term934 _120186 _120195 _120196 x s g f op x')). Qed.
Lemma lem5735450 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term987 _120186 _120195 _120196 x s g f op) = (term499 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735449 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735451 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735452 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term988 _120186 _120195 _120196 x s g f op) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735451 _120195) (@lem5735450 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735453 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term940 _120186 _120195 _120196 f s g x op) = (term940 _120186 _120195 _120196 f s g x op).
Proof. exact (eq_refl (term940 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735454 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term985 _120186 _120195 _120196 x s g f op) = (term942 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735453 _120186 _120195 _120196 f s g x op) (@lem5735452 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735456 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term989 _120186 _120195 _120196 x s g f op) = (term990 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735455) (@lem5735454 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735457 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term934 _120186 _120195 _120196 x s g f op x') = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term934 _120186 _120195 _120196 x s g f op x')). Qed.
Lemma lem5735458 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term940 _120186 _120195 _120196 f s g x op) = (term940 _120186 _120195 _120196 f s g x op).
Proof. exact (eq_refl (term940 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735459 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term991 _120186 _120195 _120196 x s g f op x') = (term992 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5735458 _120186 _120195 _120196 f s g x op) (@lem5735457 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735460 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term993 _120186 _120195 _120196 x s g f op) = (term994 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735459 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735461 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735462 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term986 _120186 _120195 _120196 x s g f op) = (term995 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735461 _120195) (@lem5735460 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735463 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term985 _120186 _120195 _120196 x s g f op) = (term986 _120186 _120195 _120196 x s g f op)) = ((term942 _120186 _120195 _120196 x s g f op) = (term995 _120186 _120195 _120196 x s g f op)).
Proof. exact (MK_COMB (@lem5735456 _120186 _120195 _120196 x s g f op) (@lem5735462 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735464 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term942 _120186 _120195 _120196 x s g f op) = (term995 _120186 _120195 _120196 x s g f op).
Proof. exact (EQ_MP (@lem5735463 _120186 _120195 _120196 x s g f op) (@lem5735448 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735465 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term949 _120186 _120195 _120196 x s g f op) = (term996 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735444 _120186 _120195 _120196 x s g f op) (@lem5735464 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term997 A P Q) = (term998 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5735468 {_120195 : Type'} (P : _120195 -> Prop) (Q : _120195 -> Prop) : (term997 _120195 P Q) = (term998 _120195 P Q).
Proof. exact (@lem5735467 _120195 P Q). Qed.
Lemma lem5735469 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term999 _120186 _120195 _120196 x s g f op) = (term1000 _120186 _120195 _120196 x s g f op).
Proof. exact (@lem5735468 _120195 (term980 _120186 _120195 _120196 x s g f op) (term994 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735470 {_120186 _120195 _120196 : Type'} (x : _120195) (x' : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1001 _120186 _120195 _120196 x' s g f op x) = (term978 _120186 _120195 _120196 x x' s g f op).
Proof. exact (eq_refl (term1001 _120186 _120195 _120196 x' s g f op x)). Qed.
Lemma lem5735471 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1002 _120186 _120195 _120196 x s g f op) = (term980 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735470 _120186 _120195 _120196 x' x s g f op)). Qed.
Lemma lem5735472 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735473 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1003 _120186 _120195 _120196 x s g f op) = (term981 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735472 _120195) (@lem5735471 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735475 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1004 _120186 _120195 _120196 x s g f op) = (term982 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735474) (@lem5735473 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735476 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1005 _120186 _120195 _120196 x s g f op x') = (term992 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term1005 _120186 _120195 _120196 x s g f op x')). Qed.
Lemma lem5735477 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1006 _120186 _120195 _120196 x s g f op) = (term994 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735476 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735478 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735479 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1007 _120186 _120195 _120196 x s g f op) = (term995 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735478 _120195) (@lem5735477 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735480 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term999 _120186 _120195 _120196 x s g f op) = (term996 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735475 _120186 _120195 _120196 x s g f op) (@lem5735479 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735482 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1008 _120186 _120195 _120196 x s g f op) = (term1009 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735481) (@lem5735480 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735483 {_120186 _120195 _120196 : Type'} (x : _120195) (x' : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1001 _120186 _120195 _120196 x' s g f op x) = (term978 _120186 _120195 _120196 x x' s g f op).
Proof. exact (eq_refl (term1001 _120186 _120195 _120196 x' s g f op x)). Qed.
Lemma lem5735484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735485 {_120186 _120195 _120196 : Type'} (x : _120195) (x' : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1010 _120186 _120195 _120196 x' s g f op x) = (term1011 _120186 _120195 _120196 x x' s g f op).
Proof. exact (MK_COMB (@lem5735484) (@lem5735483 _120186 _120195 _120196 x x' s g f op)). Qed.
Lemma lem5735486 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1005 _120186 _120195 _120196 x s g f op x') = (term992 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term1005 _120186 _120195 _120196 x s g f op x')). Qed.
Lemma lem5735487 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1012 _120186 _120195 _120196 x s g f op x') = (term1013 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5735485 _120186 _120195 _120196 x' x s g f op) (@lem5735486 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735488 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1014 _120186 _120195 _120196 x s g f op) = (term1015 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735487 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735489 {_120195 : Type'} : (@ex _120195) = (@ex _120195).
Proof. exact (eq_refl (@ex _120195)). Qed.
Lemma lem5735490 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1000 _120186 _120195 _120196 x s g f op) = (term1016 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735489 _120195) (@lem5735488 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735491 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : ((term999 _120186 _120195 _120196 x s g f op) = (term1000 _120186 _120195 _120196 x s g f op)) = ((term996 _120186 _120195 _120196 x s g f op) = (term1016 _120186 _120195 _120196 x s g f op)).
Proof. exact (MK_COMB (@lem5735482 _120186 _120195 _120196 x s g f op) (@lem5735490 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735492 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term996 _120186 _120195 _120196 x s g f op) = (term1016 _120186 _120195 _120196 x s g f op).
Proof. exact (EQ_MP (@lem5735491 _120186 _120195 _120196 x s g f op) (@lem5735469 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735494 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term949 _120186 _120195 _120196 x s g f op) = (term1016 _120186 _120195 _120196 x s g f op).
Proof. exact (TRANS (@lem5735465 _120186 _120195 _120196 x s g f op) (@lem5735492 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735495 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term889 _120186 _120195 _120196 x s g f op) = (term1016 _120186 _120195 _120196 x s g f op).
Proof. exact (TRANS (@lem5735196 _120186 _120195 _120196 x s g f op) (@lem5735494 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735496 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : term1016 _120186 _120195 _120196 x s g f op.
Proof. exact (EQ_MP (@lem5735495 _120186 _120195 _120196 x s g f op) (@lem5735111 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5735497 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term1013 _120186 _120195 _120196 x s g f x' op) : term1013 _120186 _120195 _120196 x s g f x' op.
Proof. exact (h1). Qed.
Lemma lem5735528 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term497 _120186 _120195 _120196 x s g f x' op) = (term497 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term497 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735537 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : ((g x) = (@neutral _120196 op)) = ((g x) = (@neutral _120196 op)).
Proof. exact (eq_refl ((g x) = (@neutral _120196 op))). Qed.
Lemma lem5735556 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term909 _120186 _120195 x f x' s) = (term909 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term909 _120186 _120195 x f x' s)). Qed.
Lemma lem5735557 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term917 _120186 _120195 x f s) = (term917 _120186 _120195 x f s).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735556 _120186 _120195 x f x' s)). Qed.
Lemma lem5735558 {_120195 : Type'} : (@all _120195) = (@all _120195).
Proof. exact (eq_refl (@all _120195)). Qed.
Lemma lem5735559 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term918 _120186 _120195 x f s) = (term918 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735558 _120195) (@lem5735557 _120186 _120195 x f s)). Qed.
Lemma lem5735560 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735561 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term920 _120186 _120195 x f s) = (term920 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735560) (@lem5735559 _120186 _120195 x f s)). Qed.
Lemma lem5735562 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term922 _120186 _120195 _120196 f s g x op) = (term922 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735561 _120186 _120195 x f s) (@lem5735537 _120186 _120196 g x op)). Qed.
Lemma lem5735563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5735564 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term940 _120186 _120195 _120196 f s g x op) = (term940 _120186 _120195 _120196 f s g x op).
Proof. exact (MK_COMB (@lem5735563) (@lem5735562 _120186 _120195 _120196 f s g x op)). Qed.
Lemma lem5735565 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term992 _120186 _120195 _120196 x s g f x' op) = (term992 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5735564 _120186 _120195 _120196 f s g x op) (@lem5735528 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735598 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term930 _120186 _120195 _120196 x s g f x' op) = (term930 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term930 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735599 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term937 _120186 _120195 _120196 x s g f op) = (term937 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735598 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735600 {_120195 : Type'} : (@all _120195) = (@all _120195).
Proof. exact (eq_refl (@all _120195)). Qed.
Lemma lem5735601 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term938 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735600 _120195) (@lem5735599 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735632 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term976 _120186 _120195 _120196 f x' s g x op) = (term976 _120186 _120195 _120196 f x' s g x op).
Proof. exact (eq_refl (term976 _120186 _120195 _120196 f x' s g x op)). Qed.
Lemma lem5735633 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term978 _120186 _120195 _120196 x' x s g f op) = (term978 _120186 _120195 _120196 x' x s g f op).
Proof. exact (MK_COMB (@lem5735632 _120186 _120195 _120196 f x' s g x op) (@lem5735601 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5735635 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1011 _120186 _120195 _120196 x' x s g f op) = (term1011 _120186 _120195 _120196 x' x s g f op).
Proof. exact (MK_COMB (@lem5735634) (@lem5735633 _120186 _120195 _120196 x' x s g f op)). Qed.
Lemma lem5735636 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1013 _120186 _120195 _120196 x s g f x' op) = (term1013 _120186 _120195 _120196 x s g f x' op).
Proof. exact (MK_COMB (@lem5735635 _120186 _120195 _120196 x' x s g f op) (@lem5735565 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735637 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term1013 _120186 _120195 _120196 x s g f x' op) : term1013 _120186 _120195 _120196 x s g f x' op.
Proof. exact (EQ_MP (@lem5735636 _120186 _120195 _120196 x s g f x' op) (@lem5735497 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735638 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term978 _120186 _120195 _120196 x' x s g f op.
Proof. exact (h1). Qed.
Lemma lem5735639 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term992 _120186 _120195 _120196 x s g f x' op.
Proof. exact (h1). Qed.
Lemma lem5735640 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term938 _120186 _120195 _120196 x s g f op.
Proof. exact (proj2 (@lem5735638 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735641 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term961 _120186 _120195 _120196 f x' s g x op.
Proof. exact (proj1 (@lem5735638 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735643 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term906 _120186 _120195 x f x' s.
Proof. exact (proj1 (@lem5735641 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735646 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term497 _120186 _120195 _120196 x s g f x' op.
Proof. exact (proj2 (@lem5735639 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735647 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term922 _120186 _120195 _120196 f s g x op.
Proof. exact (proj1 (@lem5735639 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735648 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term470 _120186 _120195 _120196 s g f x' op.
Proof. exact (proj2 (@lem5735646 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735652 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (h1 : term918 _120186 _120195 x f s) : term918 _120186 _120195 x f s.
Proof. exact (h1). Qed.
Lemma lem5735667 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term930 _120186 _120195 _120196 x s g f x' op) = (term930 _120186 _120195 _120196 x s g f x' op).
Proof. exact (eq_refl (term930 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735668 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term937 _120186 _120195 _120196 x s g f op) = (term937 _120186 _120195 _120196 x s g f op).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735667 _120186 _120195 _120196 x s g f x' op)). Qed.
Lemma lem5735669 {_120195 : Type'} : (@all _120195) = (@all _120195).
Proof. exact (eq_refl (@all _120195)). Qed.
Lemma lem5735671 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term938 _120186 _120195 _120196 x s g f op) = (term938 _120186 _120195 _120196 x s g f op).
Proof. exact (MK_COMB (@lem5735669 _120195) (@lem5735668 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5735672 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term938 _120186 _120195 _120196 x s g f op.
Proof. exact (EQ_MP (@lem5735671 _120186 _120195 _120196 x s g f op) (@lem5735640 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735704 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (x' : _120195) (s : _120195 -> Prop) : (term909 _120186 _120195 x f x' s) = (term909 _120186 _120195 x f x' s).
Proof. exact (eq_refl (term909 _120186 _120195 x f x' s)). Qed.
Lemma lem5735705 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term917 _120186 _120195 x f s) = (term917 _120186 _120195 x f s).
Proof. exact (fun_ext (fun x' : _120195 => @lem5735704 _120186 _120195 x f x' s)). Qed.
Lemma lem5735706 {_120195 : Type'} : (@all _120195) = (@all _120195).
Proof. exact (eq_refl (@all _120195)). Qed.
Lemma lem5735708 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) : (term918 _120186 _120195 x f s) = (term918 _120186 _120195 x f s).
Proof. exact (MK_COMB (@lem5735706 _120195) (@lem5735705 _120186 _120195 x f s)). Qed.
Lemma lem5735709 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (h1 : term918 _120186 _120195 x f s) : term918 _120186 _120195 x f s.
Proof. exact (EQ_MP (@lem5735708 _120186 _120195 x f s) (@lem5735652 _120186 _120195 x f s h1)). Qed.
Lemma lem5735725 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : (g x) = (@neutral _120196 op)) : (g x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5735726 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1017 _120186 _120195 _120196 x s g f op _72203.
Proof. exact (@lem5735672 _120186 _120195 _120196 x' x s g f op h1 _72203). Qed.
Lemma lem5735727 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1017 _120186 _120195 _120196 x s g f op _72203) = (term930 _120186 _120195 _120196 x s g f _72203 op).
Proof. exact (eq_refl (term1017 _120186 _120195 _120196 x s g f op _72203)). Qed.
Lemma lem5735729 {_120186 _120195 : Type'} (_72204 : _120195) (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (h1 : term918 _120186 _120195 x f s) : term1018 _120186 _120195 x f s _72204.
Proof. exact (@lem5735709 _120186 _120195 x f s h1 _72204). Qed.
Lemma lem5735730 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1018 _120186 _120195 x f s _72204) = (term909 _120186 _120195 x f _72204 s).
Proof. exact (eq_refl (term1018 _120186 _120195 x f s _72204)). Qed.
Lemma lem5735741 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term930 _120186 _120195 _120196 x s g f _72203 op.
Proof. exact (EQ_MP (@lem5735727 _120186 _120195 _120196 x s g f _72203 op) (@lem5735726 _120186 _120195 _120196 _72203 x' x s g f op h1)). Qed.
Lemma lem5735743 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term78 _120186 _120196 g x op.
Proof. exact (proj2 (@lem5735641 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735745 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : x = (f x').
Proof. exact (proj1 (@lem5735643 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735749 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : x = (f x').
Proof. exact (proj1 (@lem5735646 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735759 {_120186 _120195 : Type'} (_72204 : _120195) (x : _120186) (f : _120195 -> _120186) (s : _120195 -> Prop) (h1 : term918 _120186 _120195 x f s) : term909 _120186 _120195 x f _72204 s.
Proof. exact (EQ_MP (@lem5735730 _120186 _120195 x f _72204 s) (@lem5735729 _120186 _120195 _72204 x f s h1)). Qed.
Lemma lem5735761 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : x = (f x').
Proof. exact (proj1 (@lem5735646 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735767 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : (g x) = (@neutral _120196 op)) : (g x) = (@neutral _120196 op).
Proof. exact (h1). Qed.
Lemma lem5735782 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1019 _120186 _120195 _120196 s g f _72203 op) = (term1019 _120186 _120195 _120196 s g f _72203 op).
Proof. exact (eq_refl (term1019 _120186 _120195 _120196 s g f _72203 op)). Qed.
Lemma lem5735783 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : (term1020 _120186 _120195 _120196 s g f _72203 op x) = (term1021 _120186 _120195 _120196 s g _72203 op f x').
Proof. exact (MK_COMB (@lem5735782 _120186 _120195 _120196 s g f _72203 op) (@lem5735745 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735784 {_120186 _120195 _120196 : Type'} (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1021 _120186 _120195 _120196 s g _72203 op f x') = (term1022 _120186 _120195 _120196 x' s g f _72203 op).
Proof. exact (eq_refl (term1021 _120186 _120195 _120196 s g _72203 op f x')). Qed.
Lemma lem5735785 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) (x : _120186) : (term1023 _120186 _120195 _120196 s g f _72203 op x) = (term1023 _120186 _120195 _120196 s g f _72203 op x).
Proof. exact (eq_refl (term1023 _120186 _120195 _120196 s g f _72203 op x)). Qed.
Lemma lem5735786 {_120186 _120195 _120196 : Type'} (x : _120186) (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : ((term1020 _120186 _120195 _120196 s g f _72203 op x) = (term1021 _120186 _120195 _120196 s g _72203 op f x')) = ((term1020 _120186 _120195 _120196 s g f _72203 op x) = (term1022 _120186 _120195 _120196 x' s g f _72203 op)).
Proof. exact (MK_COMB (@lem5735785 _120186 _120195 _120196 s g f _72203 op x) (@lem5735784 _120186 _120195 _120196 x' s g f _72203 op)). Qed.
Lemma lem5735787 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1020 _120186 _120195 _120196 s g f _72203 op x) = (term930 _120186 _120195 _120196 x s g f _72203 op).
Proof. exact (eq_refl (term1020 _120186 _120195 _120196 s g f _72203 op x)). Qed.
Lemma lem5735788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735789 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1023 _120186 _120195 _120196 s g f _72203 op x) = (term1024 _120186 _120195 _120196 x s g f _72203 op).
Proof. exact (MK_COMB (@lem5735788) (@lem5735787 _120186 _120195 _120196 x s g f _72203 op)). Qed.
Lemma lem5735790 {_120186 _120195 _120196 : Type'} (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1022 _120186 _120195 _120196 x' s g f _72203 op).
Proof. exact (eq_refl (term1022 _120186 _120195 _120196 x' s g f _72203 op)). Qed.
Lemma lem5735791 {_120186 _120195 _120196 : Type'} (x : _120186) (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : ((term1020 _120186 _120195 _120196 s g f _72203 op x) = (term1022 _120186 _120195 _120196 x' s g f _72203 op)) = ((term930 _120186 _120195 _120196 x s g f _72203 op) = (term1022 _120186 _120195 _120196 x' s g f _72203 op)).
Proof. exact (MK_COMB (@lem5735789 _120186 _120195 _120196 x s g f _72203 op) (@lem5735790 _120186 _120195 _120196 x' s g f _72203 op)). Qed.
Lemma lem5735792 {_120186 _120195 _120196 : Type'} (x : _120186) (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : ((term1020 _120186 _120195 _120196 s g f _72203 op x) = (term1021 _120186 _120195 _120196 s g _72203 op f x')) = ((term930 _120186 _120195 _120196 x s g f _72203 op) = (term1022 _120186 _120195 _120196 x' s g f _72203 op)).
Proof. exact (TRANS (@lem5735786 _120186 _120195 _120196 x x' s g f _72203 op) (@lem5735791 _120186 _120195 _120196 x x' s g f _72203 op)). Qed.
Lemma lem5735793 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : (term930 _120186 _120195 _120196 x s g f _72203 op) = (term1022 _120186 _120195 _120196 x' s g f _72203 op).
Proof. exact (EQ_MP (@lem5735792 _120186 _120195 _120196 x x' s g f _72203 op) (@lem5735783 _120186 _120195 _120196 _72203 x' x s g f op h1)). Qed.
Lemma lem5735794 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1022 _120186 _120195 _120196 x' s g f _72203 op.
Proof. exact (EQ_MP (@lem5735793 _120186 _120195 _120196 _72203 x' x s g f op h1) (@lem5735741 _120186 _120195 _120196 _72203 x' x s g f op h1)). Qed.
Lemma lem5735795 {_120186 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) : (term599 _120186 _120196 g op) = (term599 _120186 _120196 g op).
Proof. exact (eq_refl (term599 _120186 _120196 g op)). Qed.
Lemma lem5735796 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : (term600 _120186 _120196 g op x) = (term1025 _120186 _120195 _120196 g op f x').
Proof. exact (MK_COMB (@lem5735795 _120186 _120196 g op) (@lem5735745 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735797 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1025 _120186 _120195 _120196 g op f x') = (term467 _120186 _120195 _120196 g f x' op).
Proof. exact (eq_refl (term1025 _120186 _120195 _120196 g op f x')). Qed.
Lemma lem5735798 {_120186 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x : _120186) : (term601 _120186 _120196 g op x) = (term601 _120186 _120196 g op x).
Proof. exact (eq_refl (term601 _120186 _120196 g op x)). Qed.
Lemma lem5735799 {_120186 _120195 _120196 : Type'} (x : _120186) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term600 _120186 _120196 g op x) = (term1025 _120186 _120195 _120196 g op f x')) = ((term600 _120186 _120196 g op x) = (term467 _120186 _120195 _120196 g f x' op)).
Proof. exact (MK_COMB (@lem5735798 _120186 _120196 g op x) (@lem5735797 _120186 _120195 _120196 g f x' op)). Qed.
Lemma lem5735800 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term600 _120186 _120196 g op x) = (term78 _120186 _120196 g x op).
Proof. exact (eq_refl (term600 _120186 _120196 g op x)). Qed.
Lemma lem5735801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735802 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term601 _120186 _120196 g op x) = (term602 _120186 _120196 g x op).
Proof. exact (MK_COMB (@lem5735801) (@lem5735800 _120186 _120196 g x op)). Qed.
Lemma lem5735803 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term467 _120186 _120195 _120196 g f x' op) = (term467 _120186 _120195 _120196 g f x' op).
Proof. exact (eq_refl (term467 _120186 _120195 _120196 g f x' op)). Qed.
Lemma lem5735804 {_120186 _120195 _120196 : Type'} (x : _120186) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term600 _120186 _120196 g op x) = (term467 _120186 _120195 _120196 g f x' op)) = ((term78 _120186 _120196 g x op) = (term467 _120186 _120195 _120196 g f x' op)).
Proof. exact (MK_COMB (@lem5735802 _120186 _120196 g x op) (@lem5735803 _120186 _120195 _120196 g f x' op)). Qed.
Lemma lem5735805 {_120186 _120195 _120196 : Type'} (x : _120186) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term600 _120186 _120196 g op x) = (term1025 _120186 _120195 _120196 g op f x')) = ((term78 _120186 _120196 g x op) = (term467 _120186 _120195 _120196 g f x' op)).
Proof. exact (TRANS (@lem5735799 _120186 _120195 _120196 x g f x' op) (@lem5735804 _120186 _120195 _120196 x g f x' op)). Qed.
Lemma lem5735806 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : (term78 _120186 _120196 g x op) = (term467 _120186 _120195 _120196 g f x' op).
Proof. exact (EQ_MP (@lem5735805 _120186 _120195 _120196 x g f x' op) (@lem5735796 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735807 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term467 _120186 _120195 _120196 g f x' op.
Proof. exact (EQ_MP (@lem5735806 _120186 _120195 _120196 x' x s g f op h1) (@lem5735743 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735864 {_120186 _120195 : Type'} (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1026 _120186 _120195 f _72204 s) = (term1026 _120186 _120195 f _72204 s).
Proof. exact (eq_refl (term1026 _120186 _120195 f _72204 s)). Qed.
Lemma lem5735865 {_120186 _120195 _120196 : Type'} (_72204 : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : (term1027 _120186 _120195 f _72204 s x) = (term1028 _120186 _120195 _72204 s f x').
Proof. exact (MK_COMB (@lem5735864 _120186 _120195 f _72204 s) (@lem5735749 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735866 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1028 _120186 _120195 _72204 s f x') = (term1029 _120186 _120195 x' f _72204 s).
Proof. exact (eq_refl (term1028 _120186 _120195 _72204 s f x')). Qed.
Lemma lem5735867 {_120186 _120195 : Type'} (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) (x : _120186) : (term1030 _120186 _120195 f _72204 s x) = (term1030 _120186 _120195 f _72204 s x).
Proof. exact (eq_refl (term1030 _120186 _120195 f _72204 s x)). Qed.
Lemma lem5735868 {_120186 _120195 : Type'} (x : _120186) (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : ((term1027 _120186 _120195 f _72204 s x) = (term1028 _120186 _120195 _72204 s f x')) = ((term1027 _120186 _120195 f _72204 s x) = (term1029 _120186 _120195 x' f _72204 s)).
Proof. exact (MK_COMB (@lem5735867 _120186 _120195 f _72204 s x) (@lem5735866 _120186 _120195 x' f _72204 s)). Qed.
Lemma lem5735869 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1027 _120186 _120195 f _72204 s x) = (term909 _120186 _120195 x f _72204 s).
Proof. exact (eq_refl (term1027 _120186 _120195 f _72204 s x)). Qed.
Lemma lem5735870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735871 {_120186 _120195 : Type'} (x : _120186) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1030 _120186 _120195 f _72204 s x) = (term1031 _120186 _120195 x f _72204 s).
Proof. exact (MK_COMB (@lem5735870) (@lem5735869 _120186 _120195 x f _72204 s)). Qed.
Lemma lem5735872 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1029 _120186 _120195 x' f _72204 s) = (term1029 _120186 _120195 x' f _72204 s).
Proof. exact (eq_refl (term1029 _120186 _120195 x' f _72204 s)). Qed.
Lemma lem5735873 {_120186 _120195 : Type'} (x : _120186) (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : ((term1027 _120186 _120195 f _72204 s x) = (term1029 _120186 _120195 x' f _72204 s)) = ((term909 _120186 _120195 x f _72204 s) = (term1029 _120186 _120195 x' f _72204 s)).
Proof. exact (MK_COMB (@lem5735871 _120186 _120195 x f _72204 s) (@lem5735872 _120186 _120195 x' f _72204 s)). Qed.
Lemma lem5735874 {_120186 _120195 : Type'} (x : _120186) (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : ((term1027 _120186 _120195 f _72204 s x) = (term1028 _120186 _120195 _72204 s f x')) = ((term909 _120186 _120195 x f _72204 s) = (term1029 _120186 _120195 x' f _72204 s)).
Proof. exact (TRANS (@lem5735868 _120186 _120195 x x' f _72204 s) (@lem5735873 _120186 _120195 x x' f _72204 s)). Qed.
Lemma lem5735875 {_120186 _120195 _120196 : Type'} (_72204 : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : (term909 _120186 _120195 x f _72204 s) = (term1029 _120186 _120195 x' f _72204 s).
Proof. exact (EQ_MP (@lem5735874 _120186 _120195 x x' f _72204 s) (@lem5735865 _120186 _120195 _120196 _72204 x s g f x' op h1)). Qed.
Lemma lem5735876 {_120186 _120195 _120196 : Type'} (_72204 : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : term1029 _120186 _120195 x' f _72204 s.
Proof. exact (EQ_MP (@lem5735875 _120186 _120195 _120196 _72204 x s g f x' op h2) (@lem5735759 _120186 _120195 _72204 x f s h1)). Qed.
Lemma lem5735918 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term467 _120186 _120195 _120196 g f x' op.
Proof. exact (proj2 (@lem5735648 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735919 {_120186 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) : (term603 _120186 _120196 g op) = (term603 _120186 _120196 g op).
Proof. exact (eq_refl (term603 _120186 _120196 g op)). Qed.
Lemma lem5735920 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : (term604 _120186 _120196 g op x) = (term1032 _120186 _120195 _120196 g op f x').
Proof. exact (MK_COMB (@lem5735919 _120186 _120196 g op) (@lem5735761 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735921 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1032 _120186 _120195 _120196 g op f x') = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op)).
Proof. exact (eq_refl (term1032 _120186 _120195 _120196 g op f x')). Qed.
Lemma lem5735922 {_120186 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x : _120186) : (term605 _120186 _120196 g op x) = (term605 _120186 _120196 g op x).
Proof. exact (eq_refl (term605 _120186 _120196 g op x)). Qed.
Lemma lem5735923 {_120186 _120195 _120196 : Type'} (x : _120186) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term604 _120186 _120196 g op x) = (term1032 _120186 _120195 _120196 g op f x')) = ((term604 _120186 _120196 g op x) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5735922 _120186 _120196 g op x) (@lem5735921 _120186 _120195 _120196 g f x' op)). Qed.
Lemma lem5735924 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term604 _120186 _120196 g op x) = ((g x) = (@neutral _120196 op)).
Proof. exact (eq_refl (term604 _120186 _120196 g op x)). Qed.
Lemma lem5735925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5735926 {_120186 _120196 : Type'} (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) : (term605 _120186 _120196 g op x) = (term606 _120186 _120196 g x op).
Proof. exact (MK_COMB (@lem5735925) (@lem5735924 _120186 _120196 g x op)). Qed.
Lemma lem5735927 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op)) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op)).
Proof. exact (eq_refl ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))). Qed.
Lemma lem5735928 {_120186 _120195 _120196 : Type'} (x : _120186) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term604 _120186 _120196 g op x) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))) = (((g x) = (@neutral _120196 op)) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))).
Proof. exact (MK_COMB (@lem5735926 _120186 _120196 g x op) (@lem5735927 _120186 _120195 _120196 g f x' op)). Qed.
Lemma lem5735929 {_120186 _120195 _120196 : Type'} (x : _120186) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : ((term604 _120186 _120196 g op x) = (term1032 _120186 _120195 _120196 g op f x')) = (((g x) = (@neutral _120196 op)) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))).
Proof. exact (TRANS (@lem5735923 _120186 _120195 _120196 x g f x' op) (@lem5735928 _120186 _120195 _120196 x g f x' op)). Qed.
Lemma lem5735930 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : ((g x) = (@neutral _120196 op)) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op)).
Proof. exact (EQ_MP (@lem5735929 _120186 _120195 _120196 x g f x' op) (@lem5735920 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5735986 {_120186 : Type'} (x : _120186) : x = x.
Proof. exact (@lem21386 _120186 x). Qed.
Lemma lem5735987 {_120186 : Type'} (x : _120186) : x = x.
Proof. exact (@lem5735986 _120186 x). Qed.
Lemma lem5735988 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : (f x') = (f x').
Proof. exact (@lem5735987 _120186 (f x')). Qed.
Lemma lem5735989 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : term1033 _120186 _120195 f x'.
Proof. exact (fun h0 : term1034 _120186 _120195 f x' => @lem5735988 _120186 _120195 f x'). Qed.
Lemma lem5735991 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5735992 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : (term1033 _120186 _120195 f x') = ((f x') = (f x')).
Proof. exact (@lem5735991 ((f x') = (f x'))). Qed.
Lemma lem5735993 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : (f x') = (f x').
Proof. exact (EQ_MP (@lem5735992 _120186 _120195 f x') (@lem5735989 _120186 _120195 f x')). Qed.
Lemma lem5735995 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : @IN _120195 x' s.
Proof. exact (proj2 (@lem5735643 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5735996 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term611 _120195 x' s.
Proof. exact (fun h0 : term598 _120195 x' s => @lem5735995 _120186 _120195 _120196 x' x s g f op h1). Qed.
Lemma lem5735998 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5735999 {_120195 : Type'} (x' : _120195) (s : _120195 -> Prop) : (term611 _120195 x' s) = (@IN _120195 x' s).
Proof. exact (@lem5735998 (@IN _120195 x' s)). Qed.
Lemma lem5736000 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : @IN _120195 x' s.
Proof. exact (EQ_MP (@lem5735999 _120195 x' s) (@lem5735996 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736018 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5736019 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (_72203 : _120195) (s : _120195 -> Prop) : (term926 _120186 _120195 _120196 s g f _72203 op) = (term1035 _120186 _120195 _120196 g f op _72203 s).
Proof. exact (@lem5736018 ((term463 _120186 _120195 _120196 g f _72203) = (@neutral _120196 op)) (term598 _120195 _72203 s)). Qed.
Lemma lem5736027 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) : (term1036 _120186 _120195 x' f _72203) = (term1036 _120186 _120195 x' f _72203).
Proof. exact (eq_refl (term1036 _120186 _120195 x' f _72203)). Qed.
Lemma lem5736028 {_120186 _120195 _120196 : Type'} (x' : _120195) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (_72203 : _120195) (s : _120195 -> Prop) : (term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1037 _120186 _120195 _120196 x' g f op _72203 s).
Proof. exact (MK_COMB (@lem5736027 _120186 _120195 x' f _72203) (@lem5736019 _120186 _120195 _120196 g f op _72203 s)). Qed.
Lemma lem5736032 (q : Prop) (p : Prop) (r : Prop) : (term1038 p q r) = (term1038 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5736033 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1037 _120186 _120195 _120196 x' g f op _72203 s) = (term1039 _120186 _120195 _120196 g op x' f _72203 s).
Proof. exact (@lem5736032 ((term463 _120186 _120195 _120196 g f _72203) = (@neutral _120196 op)) (term1040 _120186 _120195 x' f _72203) (term598 _120195 _72203 s)). Qed.
Lemma lem5736053 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1039 _120186 _120195 _120196 g op x' f _72203 s).
Proof. exact (TRANS (@lem5736028 _120186 _120195 _120196 x' g f op _72203 s) (@lem5736033 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5736055 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1041 _120186 _120195 _120196 x' s g f _72203 op) = (term1042 _120186 _120195 _120196 g op x' f _72203 s).
Proof. exact (MK_COMB (@lem5736054) (@lem5736053 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736075 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1039 _120186 _120195 _120196 g op x' f _72203 s) = (term1039 _120186 _120195 _120196 g op x' f _72203 s).
Proof. exact (eq_refl (term1039 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736076 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : ((term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1039 _120186 _120195 _120196 g op x' f _72203 s)) = ((term1039 _120186 _120195 _120196 g op x' f _72203 s) = (term1039 _120186 _120195 _120196 g op x' f _72203 s)).
Proof. exact (MK_COMB (@lem5736055 _120186 _120195 _120196 g op x' f _72203 s) (@lem5736075 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736078 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5736079 (x : Prop) : (x = x) = True.
Proof. exact (@lem5736078 Prop x). Qed.
Lemma lem5736080 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : ((term1039 _120186 _120195 _120196 g op x' f _72203 s) = (term1039 _120186 _120195 _120196 g op x' f _72203 s)) = True.
Proof. exact (@lem5736079 (term1039 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736081 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : ((term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1039 _120186 _120195 _120196 g op x' f _72203 s)) = True.
Proof. exact (TRANS (@lem5736076 _120186 _120195 _120196 g op x' f _72203 s) (@lem5736080 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736082 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : True = ((term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1039 _120186 _120195 _120196 g op x' f _72203 s)).
Proof. exact (SYM (@lem5736081 _120186 _120195 _120196 g op x' f _72203 s)). Qed.
Lemma lem5736083 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (op : type1400 _120196) (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1022 _120186 _120195 _120196 x' s g f _72203 op) = (term1039 _120186 _120195 _120196 g op x' f _72203 s).
Proof. exact (EQ_MP (@lem5736082 _120186 _120195 _120196 g op x' f _72203 s) (@lem0)). Qed.
Lemma lem5736084 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1039 _120186 _120195 _120196 g op x' f _72203 s.
Proof. exact (EQ_MP (@lem5736083 _120186 _120195 _120196 g op x' f _72203 s) (@lem5735794 _120186 _120195 _120196 _72203 x' x s g f op h1)). Qed.
Lemma lem5736086 (b : Prop) (a : Prop) : (a \/ b) = (term1043 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5736087 {_120186 _120195 _120196 : Type'} (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1039 _120186 _120195 _120196 g op x' f _72203 s) = (term1044 _120186 _120195 _120196 x' s g f _72203 op).
Proof. exact (@lem5736086 (term1029 _120186 _120195 x' f _72203 s) ((term463 _120186 _120195 _120196 g f _72203) = (@neutral _120196 op))). Qed.
Lemma lem5736089 (a : Prop) (b : Prop) : (term1045 a b) = (term1046 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5736090 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1047 _120186 _120195 x' f _72203 s) = (term1048 _120186 _120195 x' f _72203 s).
Proof. exact (@lem5736089 (term1040 _120186 _120195 x' f _72203) (term598 _120195 _72203 s)). Qed.
Lemma lem5736092 (a : Prop) : (term555 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5736093 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) : (term1049 _120186 _120195 x' f _72203) = ((f x') = (f _72203)).
Proof. exact (@lem5736092 ((f x') = (f _72203))). Qed.
Lemma lem5736094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5736095 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) : (term1050 _120186 _120195 x' f _72203) = (term1051 _120186 _120195 x' f _72203).
Proof. exact (MK_COMB (@lem5736094) (@lem5736093 _120186 _120195 x' f _72203)). Qed.
Lemma lem5736097 (a : Prop) : (term555 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5736098 {_120195 : Type'} (_72203 : _120195) (s : _120195 -> Prop) : (term858 _120195 _72203 s) = (@IN _120195 _72203 s).
Proof. exact (@lem5736097 (@IN _120195 _72203 s)). Qed.
Lemma lem5736099 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1048 _120186 _120195 x' f _72203 s) = (term1052 _120186 _120195 x' f _72203 s).
Proof. exact (MK_COMB (@lem5736095 _120186 _120195 x' f _72203) (@lem5736098 _120195 _72203 s)). Qed.
Lemma lem5736100 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1047 _120186 _120195 x' f _72203 s) = (term1052 _120186 _120195 x' f _72203 s).
Proof. exact (TRANS (@lem5736090 _120186 _120195 x' f _72203 s) (@lem5736099 _120186 _120195 x' f _72203 s)). Qed.
Lemma lem5736101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5736102 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72203 : _120195) (s : _120195 -> Prop) : (term1053 _120186 _120195 x' f _72203 s) = (term1054 _120186 _120195 x' f _72203 s).
Proof. exact (MK_COMB (@lem5736101) (@lem5736100 _120186 _120195 x' f _72203 s)). Qed.
Lemma lem5736103 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : ((term463 _120186 _120195 _120196 g f _72203) = (@neutral _120196 op)) = ((term463 _120186 _120195 _120196 g f _72203) = (@neutral _120196 op)).
Proof. exact (eq_refl ((term463 _120186 _120195 _120196 g f _72203) = (@neutral _120196 op))). Qed.
Lemma lem5736104 {_120186 _120195 _120196 : Type'} (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1044 _120186 _120195 _120196 x' s g f _72203 op) = (term1055 _120186 _120195 _120196 x' s g f _72203 op).
Proof. exact (MK_COMB (@lem5736102 _120186 _120195 x' f _72203 s) (@lem5736103 _120186 _120195 _120196 g f _72203 op)). Qed.
Lemma lem5736105 {_120186 _120195 _120196 : Type'} (x' : _120195) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (_72203 : _120195) (op : type1400 _120196) : (term1039 _120186 _120195 _120196 g op x' f _72203 s) = (term1055 _120186 _120195 _120196 x' s g f _72203 op).
Proof. exact (TRANS (@lem5736087 _120186 _120195 _120196 x' s g f _72203 op) (@lem5736104 _120186 _120195 _120196 x' s g f _72203 op)). Qed.
Lemma lem5736107 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1056 _120186 _120195 f x' s.
Proof. exact (conj (@lem5735993 _120186 _120195 f x') (@lem5736000 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736109 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1055 _120186 _120195 _120196 x' s g f _72203 op.
Proof. exact (EQ_MP (@lem5736105 _120186 _120195 _120196 x' s g f _72203 op) (@lem5736084 _120186 _120195 _120196 _72203 x' x s g f op h1)). Qed.
Lemma lem5736110 {_120186 _120195 _120196 : Type'} (_72203 : _120195) (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1055 _120186 _120195 _120196 x' s g f _72203 op.
Proof. exact (@lem5736109 _120186 _120195 _120196 _72203 x' x s g f op h1). Qed.
Lemma lem5736111 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1057 _120186 _120195 _120196 s g f x' op.
Proof. exact (@lem5736110 _120186 _120195 _120196 x' x' x s g f op h1). Qed.
Lemma lem5736114 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : (term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op).
Proof. exact (@lem5736111 _120186 _120195 _120196 x' x s g f op h1 (@lem5736107 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736115 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1058 _120186 _120195 _120196 g f x' op.
Proof. exact (fun h0 : term467 _120186 _120195 _120196 g f x' op => @lem5736114 _120186 _120195 _120196 x' x s g f op h1). Qed.
Lemma lem5736117 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736118 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1058 _120186 _120195 _120196 g f x' op) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op)).
Proof. exact (@lem5736117 ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))). Qed.
Lemma lem5736119 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : (term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5736118 _120186 _120195 _120196 g f x' op) (@lem5736115 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736122 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5736124 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term467 _120186 _120195 _120196 g f x' op) = (term1059 _120186 _120195 _120196 g f x' op).
Proof. exact (@lem5736122 ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))). Qed.
Lemma lem5736127 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term1059 _120186 _120195 _120196 g f x' op.
Proof. exact (EQ_MP (@lem5736124 _120186 _120195 _120196 g f x' op) (@lem5735807 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736130 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : False.
Proof. exact (@lem5736127 _120186 _120195 _120196 x' x s g f op h1 (@lem5736119 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736131 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : term610.
Proof. exact (fun h0 : ~ False => @lem5736130 _120186 _120195 _120196 x' x s g f op h1). Qed.
Lemma lem5736133 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736134 : term610 = False.
Proof. exact (@lem5736133 False). Qed.
Lemma lem5736190 {_120186 : Type'} (x : _120186) : x = x.
Proof. exact (@lem21386 _120186 x). Qed.
Lemma lem5736191 {_120186 : Type'} (x : _120186) : x = x.
Proof. exact (@lem5736190 _120186 x). Qed.
Lemma lem5736192 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : (f x') = (f x').
Proof. exact (@lem5736191 _120186 (f x')). Qed.
Lemma lem5736193 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : term1033 _120186 _120195 f x'.
Proof. exact (fun h0 : term1034 _120186 _120195 f x' => @lem5736192 _120186 _120195 f x'). Qed.
Lemma lem5736195 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736196 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : (term1033 _120186 _120195 f x') = ((f x') = (f x')).
Proof. exact (@lem5736195 ((f x') = (f x'))). Qed.
Lemma lem5736197 {_120186 _120195 : Type'} (f : _120195 -> _120186) (x' : _120195) : (f x') = (f x').
Proof. exact (EQ_MP (@lem5736196 _120186 _120195 f x') (@lem5736193 _120186 _120195 f x')). Qed.
Lemma lem5736199 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : @IN _120195 x' s.
Proof. exact (proj1 (@lem5735648 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5736200 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term611 _120195 x' s.
Proof. exact (fun h0 : term598 _120195 x' s => @lem5736199 _120186 _120195 _120196 x s g f x' op h1). Qed.
Lemma lem5736202 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736203 {_120195 : Type'} (x' : _120195) (s : _120195 -> Prop) : (term611 _120195 x' s) = (@IN _120195 x' s).
Proof. exact (@lem5736202 (@IN _120195 x' s)). Qed.
Lemma lem5736204 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : @IN _120195 x' s.
Proof. exact (EQ_MP (@lem5736203 _120195 x' s) (@lem5736200 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5736206 (a : Prop) (b : Prop) : (term1060 a b) = (term1061 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5736207 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1029 _120186 _120195 x' f _72204 s) = (term1062 _120186 _120195 x' f _72204 s).
Proof. exact (@lem5736206 ((f x') = (f _72204)) (@IN _120195 _72204 s)). Qed.
Lemma lem5736209 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5736210 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1062 _120186 _120195 x' f _72204 s) = (term1063 _120186 _120195 x' f _72204 s).
Proof. exact (@lem5736209 (term1052 _120186 _120195 x' f _72204 s)). Qed.
Lemma lem5736211 {_120186 _120195 : Type'} (x' : _120195) (f : _120195 -> _120186) (_72204 : _120195) (s : _120195 -> Prop) : (term1029 _120186 _120195 x' f _72204 s) = (term1063 _120186 _120195 x' f _72204 s).
Proof. exact (TRANS (@lem5736207 _120186 _120195 x' f _72204 s) (@lem5736210 _120186 _120195 x' f _72204 s)). Qed.
Lemma lem5736213 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term1056 _120186 _120195 f x' s.
Proof. exact (conj (@lem5736197 _120186 _120195 f x') (@lem5736204 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5736215 {_120186 _120195 _120196 : Type'} (_72204 : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : term1063 _120186 _120195 x' f _72204 s.
Proof. exact (EQ_MP (@lem5736211 _120186 _120195 x' f _72204 s) (@lem5735876 _120186 _120195 _120196 _72204 x s g f x' op h1 h2)). Qed.
Lemma lem5736216 {_120186 _120195 _120196 : Type'} (_72204 : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : term1063 _120186 _120195 x' f _72204 s.
Proof. exact (@lem5736215 _120186 _120195 _120196 _72204 x s g f x' op h1 h2). Qed.
Lemma lem5736217 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : term1064 _120186 _120195 f x' s.
Proof. exact (@lem5736216 _120186 _120195 _120196 x' x s g f x' op h1 h2). Qed.
Lemma lem5736220 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : False.
Proof. exact (@lem5736217 _120186 _120195 _120196 x s g f x' op h1 h2 (@lem5736213 _120186 _120195 _120196 x s g f x' op h2)). Qed.
Lemma lem5736221 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : term610.
Proof. exact (fun h0 : ~ False => @lem5736220 _120186 _120195 _120196 x s g f x' op h1 h2). Qed.
Lemma lem5736223 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736224 : term610 = False.
Proof. exact (@lem5736223 False). Qed.
Lemma lem5736280 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : (term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5735930 _120186 _120195 _120196 x s g f x' op h1) (@lem5735767 _120186 _120196 g x op h2)). Qed.
Lemma lem5736281 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : term1058 _120186 _120195 _120196 g f x' op.
Proof. exact (fun h0 : term467 _120186 _120195 _120196 g f x' op => @lem5736280 _120186 _120195 _120196 s f x' g x op h1 h2). Qed.
Lemma lem5736283 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736284 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term1058 _120186 _120195 _120196 g f x' op) = ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op)).
Proof. exact (@lem5736283 ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))). Qed.
Lemma lem5736285 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : (term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op).
Proof. exact (EQ_MP (@lem5736284 _120186 _120195 _120196 g f x' op) (@lem5736281 _120186 _120195 _120196 s f x' g x op h1 h2)). Qed.
Lemma lem5736288 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5736290 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) : (term467 _120186 _120195 _120196 g f x' op) = (term1059 _120186 _120195 _120196 g f x' op).
Proof. exact (@lem5736288 ((term463 _120186 _120195 _120196 g f x') = (@neutral _120196 op))). Qed.
Lemma lem5736293 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : term1059 _120186 _120195 _120196 g f x' op.
Proof. exact (EQ_MP (@lem5736290 _120186 _120195 _120196 g f x' op) (@lem5735918 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5736296 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : False.
Proof. exact (@lem5736293 _120186 _120195 _120196 x s g f x' op h1 (@lem5736285 _120186 _120195 _120196 s f x' g x op h1 h2)). Qed.
Lemma lem5736297 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : term610.
Proof. exact (fun h0 : ~ False => @lem5736296 _120186 _120195 _120196 s f x' g x op h1 h2). Qed.
Lemma lem5736299 (p : Prop) : (term608 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5736300 : term610 = False.
Proof. exact (@lem5736299 False). Qed.
Lemma lem5736302 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5736300) (@lem5736297 _120186 _120195 _120196 s f x' g x op h1 h2)). Qed.
Lemma lem5736303 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : False.
Proof. exact (EQ_MP (@lem5736224) (@lem5736221 _120186 _120195 _120196 x s g f x' op h1 h2)). Qed.
Lemma lem5736304 {_120186 _120195 _120196 : Type'} (x' : _120195) (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term978 _120186 _120195 _120196 x' x s g f op) : False.
Proof. exact (EQ_MP (@lem5736134) (@lem5736131 _120186 _120195 _120196 x' x s g f op h1)). Qed.
Lemma lem5736305 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : ((g x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (g x) = (@neutral _120196 op) => @lem5736302 _120186 _120195 _120196 s f x' g x op h1 h2) (fun h3 : False => @lem5735767 _120186 _120196 g x op h2)). Qed.
Lemma lem5736306 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5736305 _120186 _120195 _120196 s f x' g x op h1 h2) (@lem5735767 _120186 _120196 g x op h2)). Qed.
Lemma lem5736307 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : ((g x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (g x) = (@neutral _120196 op) => @lem5736306 _120186 _120195 _120196 s f x' g x op h1 h2) (fun h3 : False => @lem5735725 _120186 _120196 g x op h2)). Qed.
Lemma lem5736308 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5736307 _120186 _120195 _120196 s f x' g x op h1 h2) (@lem5735725 _120186 _120196 g x op h2)). Qed.
Lemma lem5736309 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : ((g x) = (@neutral _120196 op)) = False.
Proof. exact (prop_ext (fun h3 : (g x) = (@neutral _120196 op) => @lem5736308 _120186 _120195 _120196 s f x' g x op h1 h2) (fun h3 : False => @lem5735725 _120186 _120196 g x op h2)). Qed.
Lemma lem5736310 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (f : _120195 -> _120186) (x' : _120195) (g : _120186 -> _120196) (x : _120186) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) (h2 : (g x) = (@neutral _120196 op)) : False.
Proof. exact (EQ_MP (@lem5736309 _120186 _120195 _120196 s f x' g x op h1 h2) (@lem5735725 _120186 _120196 g x op h2)). Qed.
Lemma lem5736311 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : (term918 _120186 _120195 x f s) = False.
Proof. exact (prop_ext (fun h3 : term918 _120186 _120195 x f s => @lem5736303 _120186 _120195 _120196 x s g f x' op h1 h2) (fun h3 : False => @lem5735709 _120186 _120195 x f s h1)). Qed.
Lemma lem5736312 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term918 _120186 _120195 x f s) (h2 : term992 _120186 _120195 _120196 x s g f x' op) : False.
Proof. exact (EQ_MP (@lem5736311 _120186 _120195 _120196 x s g f x' op h1 h2) (@lem5735709 _120186 _120195 x f s h1)). Qed.
Lemma lem5736313 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term992 _120186 _120195 _120196 x s g f x' op) : False.
Proof. exact (or_elim (@lem5735647 _120186 _120195 _120196 x s g f x' op h1) (fun h0 : term918 _120186 _120195 x f s => @lem5736312 _120186 _120195 _120196 x s g f x' op h0 h1) (fun h0 : (g x) = (@neutral _120196 op) => @lem5736310 _120186 _120195 _120196 s f x' g x op h1 h0)). Qed.
Lemma lem5736314 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term1013 _120186 _120195 _120196 x s g f x' op) : False.
Proof. exact (or_elim (@lem5735637 _120186 _120195 _120196 x s g f x' op h1) (fun h0 : term978 _120186 _120195 _120196 x' x s g f op => @lem5736304 _120186 _120195 _120196 x' x s g f op h0) (fun h0 : term992 _120186 _120195 _120196 x s g f x' op => @lem5736313 _120186 _120195 _120196 x s g f x' op h0)). Qed.
Lemma lem5736315 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term1013 _120186 _120195 _120196 x s g f x' op) : (term1013 _120186 _120195 _120196 x s g f x' op) = False.
Proof. exact (prop_ext (fun h2 : term1013 _120186 _120195 _120196 x s g f x' op => @lem5736314 _120186 _120195 _120196 x s g f x' op h1) (fun h2 : False => @lem5735637 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5736316 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (x' : _120195) (op : type1400 _120196) (h1 : term1013 _120186 _120195 _120196 x s g f x' op) : False.
Proof. exact (EQ_MP (@lem5736315 _120186 _120195 _120196 x s g f x' op h1) (@lem5735637 _120186 _120195 _120196 x s g f x' op h1)). Qed.
Lemma lem5736317 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : False.
Proof. exact (ex_elim (@lem5735496 _120186 _120195 _120196 x s g f op h1) (fun x' : _120195 => fun h0 : term1015 _120186 _120195 _120196 x s g f op x' => @lem5736316 _120186 _120195 _120196 x s g f x' op h0)). Qed.
Lemma lem5736318 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : (term889 _120186 _120195 _120196 x s g f op) = False.
Proof. exact (prop_ext (fun h2 : term889 _120186 _120195 _120196 x s g f op => @lem5736317 _120186 _120195 _120196 x s g f op h1) (fun h2 : False => @lem5735111 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5736319 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : False.
Proof. exact (EQ_MP (@lem5736318 _120186 _120195 _120196 x s g f op h1) (@lem5735111 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5736320 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (fun h0 : term889 _120186 _120195 _120196 x s g f op => @lem5736319 _120186 _120195 _120196 x s g f op h0). Qed.
Lemma lem5736321 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (EQ_MP (@lem5735110 _120186 _120195 _120196 x s g f op) (@lem5736320 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5736326 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term503 _120186 _120195 _120196 s g f op.
Proof. exact (fun x : _120186 => @lem5736321 _120186 _120195 _120196 x s g f op). Qed.
Lemma lem5736331 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term507 _120186 _120195 _120196 g f op.
Proof. exact (fun s : _120195 -> Prop => @lem5736326 _120186 _120195 _120196 s g f op). Qed.
Lemma lem5736336 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : term511 _120186 _120195 _120196 f op.
Proof. exact (fun g : _120186 -> _120196 => @lem5736331 _120186 _120195 _120196 g f op). Qed.
Lemma lem5736341 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : term515 _120186 _120195 _120196 op.
Proof. exact (fun f : _120195 -> _120186 => @lem5736336 _120186 _120195 _120196 f op). Qed.
Lemma lem5736346 {_120186 _120195 _120196 : Type'} : term905 _120186 _120195 _120196.
Proof. exact (fun op : type1400 _120196 => @lem5736341 _120186 _120195 _120196 op). Qed.
Lemma lem5736347 {_120186 _120195 _120196 : Type'} : term904 _120186 _120195 _120196.
Proof. exact (EQ_MP (@lem5735106 _120186 _120195 _120196) (@lem5736346 _120186 _120195 _120196)). Qed.
Lemma lem5736348 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : term1065 _120186 _120195 _120196 op.
Proof. exact (@lem5736347 _120186 _120195 _120196 op). Qed.
Lemma lem5736349 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : (term1065 _120186 _120195 _120196 op) = (term901 _120186 _120195 _120196 op).
Proof. exact (eq_refl (term1065 _120186 _120195 _120196 op)). Qed.
Lemma lem5736350 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : term901 _120186 _120195 _120196 op.
Proof. exact (EQ_MP (@lem5736349 _120186 _120195 _120196 op) (@lem5736348 _120186 _120195 _120196 op)). Qed.
Lemma lem5736351 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) (f : _120195 -> _120186) : term1066 _120186 _120195 _120196 op f.
Proof. exact (@lem5736350 _120186 _120195 _120196 op f). Qed.
Lemma lem5736352 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : (term1066 _120186 _120195 _120196 op f) = (term899 _120186 _120195 _120196 f op).
Proof. exact (eq_refl (term1066 _120186 _120195 _120196 op f)). Qed.
Lemma lem5736353 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : term899 _120186 _120195 _120196 f op.
Proof. exact (EQ_MP (@lem5736352 _120186 _120195 _120196 f op) (@lem5736351 _120186 _120195 _120196 op f)). Qed.
Lemma lem5736354 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) (g : _120186 -> _120196) : term1067 _120186 _120195 _120196 f op g.
Proof. exact (@lem5736353 _120186 _120195 _120196 f op g). Qed.
Lemma lem5736355 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1067 _120186 _120195 _120196 f op g) = (term897 _120186 _120195 _120196 g f op).
Proof. exact (eq_refl (term1067 _120186 _120195 _120196 f op g)). Qed.
Lemma lem5736356 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term897 _120186 _120195 _120196 g f op.
Proof. exact (EQ_MP (@lem5736355 _120186 _120195 _120196 g f op) (@lem5736354 _120186 _120195 _120196 f op g)). Qed.
Lemma lem5736357 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (s : _120195 -> Prop) : term1068 _120186 _120195 _120196 g f op s.
Proof. exact (@lem5736356 _120186 _120195 _120196 g f op s). Qed.
Lemma lem5736358 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1068 _120186 _120195 _120196 g f op s) = (term895 _120186 _120195 _120196 s g f op).
Proof. exact (eq_refl (term1068 _120186 _120195 _120196 g f op s)). Qed.
Lemma lem5736359 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term895 _120186 _120195 _120196 s g f op.
Proof. exact (EQ_MP (@lem5736358 _120186 _120195 _120196 s g f op) (@lem5736357 _120186 _120195 _120196 g f op s)). Qed.
Lemma lem5736360 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (x : _120186) : term1069 _120186 _120195 _120196 s g f op x.
Proof. exact (@lem5736359 _120186 _120195 _120196 s g f op x). Qed.
Lemma lem5736361 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term1069 _120186 _120195 _120196 s g f op x) = (term888 _120186 _120195 _120196 x s g f op).
Proof. exact (eq_refl (term1069 _120186 _120195 _120196 s g f op x)). Qed.
Lemma lem5736362 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (EQ_MP (@lem5736361 _120186 _120195 _120196 x s g f op) (@lem5736360 _120186 _120195 _120196 s g f op x)). Qed.
Lemma lem5736364 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (@lem5734836 _120186 _120195 _120196 x s g f op (@lem5736362 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5736365 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : False.
Proof. exact (@lem5736364 _120186 _120195 _120196 x s g f op (@lem5734820 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5736366 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : (term889 _120186 _120195 _120196 x s g f op) = False.
Proof. exact (prop_ext (fun h2 : term889 _120186 _120195 _120196 x s g f op => @lem5736365 _120186 _120195 _120196 x s g f op h1) (fun h2 : False => @lem5734820 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5736367 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) (h1 : term889 _120186 _120195 _120196 x s g f op) : False.
Proof. exact (EQ_MP (@lem5736366 _120186 _120195 _120196 x s g f op h1) (@lem5734820 _120186 _120195 _120196 x s g f op h1)). Qed.
Lemma lem5736368 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term888 _120186 _120195 _120196 x s g f op.
Proof. exact (fun h0 : term889 _120186 _120195 _120196 x s g f op => @lem5736367 _120186 _120195 _120196 x s g f op h0). Qed.
Lemma lem5736369 {_120186 _120195 _120196 : Type'} (x : _120186) (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : (term432 _120186 _120195 _120196 f s g x op) = (term500 _120186 _120195 _120196 x s g f op).
Proof. exact (EQ_MP (@lem5734819 _120186 _120195 _120196 x s g f op) (@lem5736368 _120186 _120195 _120196 x s g f op)). Qed.
Lemma lem5736370 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : (term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op).
Proof. exact (EQ_MP (@lem5727918 _120011 _120196 x s f x' op) (@lem5729412 _120011 _120196 s x' f x op h1)). Qed.
Lemma lem5736371 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : (term78 _120011 _120196 f x op) = ((term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op)).
Proof. exact (prop_ext (fun h2 : term78 _120011 _120196 f x op => @lem5736370 _120011 _120196 s x' f x op h1) (fun h2 : (term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op) => @lem5726769 _120011 _120196 f x op h1)). Qed.
Lemma lem5736372 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : term78 _120011 _120196 f x op) : (term121 _120011 _120196 x s f x' op) = (term178 _120011 _120196 x s f x' op).
Proof. exact (EQ_MP (@lem5736371 _120011 _120196 s x' f x op h1) (@lem5726769 _120011 _120196 f x op h1)). Qed.
Lemma lem5736373 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term537 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : term78 _120011 _120196 f x op => @lem5736372 _120011 _120196 s x' f x op h0). Qed.
Lemma lem5736374 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op).
Proof. exact (EQ_MP (@lem5726789 _120011 _120196 x s f x' op) (@lem5727913 _120011 _120196 s x' f x op h1)). Qed.
Lemma lem5736375 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : ((f x) = (@neutral _120196 op)) = ((term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op)).
Proof. exact (prop_ext (fun h2 : (f x) = (@neutral _120196 op) => @lem5736374 _120011 _120196 s x' f x op h1) (fun h2 : (term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op) => @lem5726752 _120011 _120196 f x op h1)). Qed.
Lemma lem5736376 {_120011 _120196 : Type'} (s : _120011 -> Prop) (x' : _120011) (f : _120011 -> _120196) (x : _120011) (op : type1400 _120196) (h1 : (f x) = (@neutral _120196 op)) : (term121 _120011 _120196 x s f x' op) = (term158 _120011 _120196 s f x' op).
Proof. exact (EQ_MP (@lem5736375 _120011 _120196 s x' f x op h1) (@lem5726752 _120011 _120196 f x op h1)). Qed.
Lemma lem5736377 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term541 _120011 _120196 x s f x' op.
Proof. exact (fun h0 : (f x) = (@neutral _120196 op) => @lem5736376 _120011 _120196 s x' f x op h0). Qed.
Lemma lem5736378 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term544 _120011 _120196 x s f x' op.
Proof. exact (conj (@lem5736377 _120011 _120196 x s f x' op) (@lem5736373 _120011 _120196 x s f x' op)). Qed.
Lemma lem5736379 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (x' : _120011) (op : type1400 _120196) : term182 _120011 _120196 x s f x' op.
Proof. exact (EQ_MP (@lem5726751 _120011 _120196 x s f x' op) (@lem5736378 _120011 _120196 x s f x' op)). Qed.
Lemma lem5736384 {_120186 _120195 _120196 : Type'} (s : _120195 -> Prop) (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term503 _120186 _120195 _120196 s g f op.
Proof. exact (fun x : _120186 => @lem5736369 _120186 _120195 _120196 x s g f op). Qed.
Lemma lem5736389 {_120186 _120195 _120196 : Type'} (g : _120186 -> _120196) (f : _120195 -> _120186) (op : type1400 _120196) : term507 _120186 _120195 _120196 g f op.
Proof. exact (fun s : _120195 -> Prop => @lem5736384 _120186 _120195 _120196 s g f op). Qed.
Lemma lem5736394 {_120186 _120195 _120196 : Type'} (f : _120195 -> _120186) (op : type1400 _120196) : term511 _120186 _120195 _120196 f op.
Proof. exact (fun g : _120186 -> _120196 => @lem5736389 _120186 _120195 _120196 g f op). Qed.
Lemma lem5736399 {_120186 _120195 _120196 : Type'} (op : type1400 _120196) : term515 _120186 _120195 _120196 op.
Proof. exact (fun f : _120195 -> _120186 => @lem5736394 _120186 _120195 _120196 f op). Qed.
Lemma lem5736404 {_120158 _120196 : Type'} (s : _120158 -> Prop) (t : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : term408 _120158 _120196 s t f op.
Proof. exact (fun x : _120158 => @lem5734815 _120158 _120196 s t f x op). Qed.
Lemma lem5736409 {_120158 _120196 : Type'} (s : _120158 -> Prop) (f : _120158 -> _120196) (op : type1400 _120196) : term412 _120158 _120196 s f op.
Proof. exact (fun t : _120158 -> Prop => @lem5736404 _120158 _120196 s t f op). Qed.
Lemma lem5736414 {_120158 _120196 : Type'} (f : _120158 -> _120196) (op : type1400 _120196) : term416 _120158 _120196 f op.
Proof. exact (fun s : _120158 -> Prop => @lem5736409 _120158 _120196 s f op). Qed.
Lemma lem5736419 {_120158 _120196 : Type'} (op : type1400 _120196) : term420 _120158 _120196 op.
Proof. exact (fun f : _120158 -> _120196 => @lem5736414 _120158 _120196 f op). Qed.
Lemma lem5736420 {_120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term517 _120158 _120186 _120195 _120196 op.
Proof. exact (conj (@lem5736419 _120158 _120196 op) (@lem5736399 _120186 _120195 _120196 op)). Qed.
Lemma lem5736425 {_120120 _120196 : Type'} (s : _120120 -> Prop) (t : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : term352 _120120 _120196 s t f op.
Proof. exact (fun x : _120120 => @lem5733425 _120120 _120196 s t f x op). Qed.
Lemma lem5736430 {_120120 _120196 : Type'} (s : _120120 -> Prop) (f : _120120 -> _120196) (op : type1400 _120196) : term356 _120120 _120196 s f op.
Proof. exact (fun t : _120120 -> Prop => @lem5736425 _120120 _120196 s t f op). Qed.
Lemma lem5736435 {_120120 _120196 : Type'} (f : _120120 -> _120196) (op : type1400 _120196) : term360 _120120 _120196 f op.
Proof. exact (fun s : _120120 -> Prop => @lem5736430 _120120 _120196 s f op). Qed.
Lemma lem5736440 {_120120 _120196 : Type'} (op : type1400 _120196) : term364 _120120 _120196 op.
Proof. exact (fun f : _120120 -> _120196 => @lem5736435 _120120 _120196 f op). Qed.
Lemma lem5736441 {_120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term519 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (conj (@lem5736440 _120120 _120196 op) (@lem5736420 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5736446 {_120082 _120196 : Type'} (s : _120082 -> Prop) (t : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : term298 _120082 _120196 s t f op.
Proof. exact (fun x : _120082 => @lem5732235 _120082 _120196 s t f x op). Qed.
Lemma lem5736451 {_120082 _120196 : Type'} (s : _120082 -> Prop) (f : _120082 -> _120196) (op : type1400 _120196) : term302 _120082 _120196 s f op.
Proof. exact (fun t : _120082 -> Prop => @lem5736446 _120082 _120196 s t f op). Qed.
Lemma lem5736456 {_120082 _120196 : Type'} (f : _120082 -> _120196) (op : type1400 _120196) : term306 _120082 _120196 f op.
Proof. exact (fun s : _120082 -> Prop => @lem5736451 _120082 _120196 s f op). Qed.
Lemma lem5736461 {_120082 _120196 : Type'} (op : type1400 _120196) : term310 _120082 _120196 op.
Proof. exact (fun f : _120082 -> _120196 => @lem5736456 _120082 _120196 f op). Qed.
Lemma lem5736462 {_120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term521 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (conj (@lem5736461 _120082 _120196 op) (@lem5736441 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5736467 {_120044 _120196 : Type'} (s : _120044 -> Prop) (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : term242 _120044 _120196 s f op x.
Proof. exact (fun x' : _120044 => @lem5730554 _120044 _120196 s f op x' x). Qed.
Lemma lem5736472 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) (x : _120044) : term246 _120044 _120196 f op x.
Proof. exact (fun s : _120044 -> Prop => @lem5736467 _120044 _120196 s f op x). Qed.
Lemma lem5736477 {_120044 _120196 : Type'} (f : _120044 -> _120196) (op : type1400 _120196) : term250 _120044 _120196 f op.
Proof. exact (fun x : _120044 => @lem5736472 _120044 _120196 f op x). Qed.
Lemma lem5736482 {_120044 _120196 : Type'} (op : type1400 _120196) : term254 _120044 _120196 op.
Proof. exact (fun f : _120044 -> _120196 => @lem5736477 _120044 _120196 f op). Qed.
Lemma lem5736483 {_120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term523 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (conj (@lem5736482 _120044 _120196 op) (@lem5736462 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5736488 {_120011 _120196 : Type'} (x : _120011) (s : _120011 -> Prop) (f : _120011 -> _120196) (op : type1400 _120196) : term185 _120011 _120196 x s f op.
Proof. exact (fun x' : _120011 => @lem5736379 _120011 _120196 x s f x' op). Qed.
Lemma lem5736493 {_120011 _120196 : Type'} (x : _120011) (f : _120011 -> _120196) (op : type1400 _120196) : term189 _120011 _120196 x f op.
Proof. exact (fun s : _120011 -> Prop => @lem5736488 _120011 _120196 x s f op). Qed.
Lemma lem5736498 {_120011 _120196 : Type'} (f : _120011 -> _120196) (op : type1400 _120196) : term193 _120011 _120196 f op.
Proof. exact (fun x : _120011 => @lem5736493 _120011 _120196 x f op). Qed.
Lemma lem5736503 {_120011 _120196 : Type'} (op : type1400 _120196) : term197 _120011 _120196 op.
Proof. exact (fun f : _120011 -> _120196 => @lem5736498 _120011 _120196 f op). Qed.
Lemma lem5736504 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term525 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (conj (@lem5736503 _120011 _120196 op) (@lem5736483 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5736505 {_119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term526 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (EQ_MP (@lem5726733 _119963 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op) (@lem5736504 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
