Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_INTERSECTION_OF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INTERSECTION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem4848610 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4848611 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4848612 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4848611 t1) (@lem4848610 t1)). Qed.
Lemma lem4848613 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4848612 t1 t2). Qed.
Lemma lem4848614 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4848615 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4848614 t1 t2) (@lem4848613 t1 t2)). Qed.
Lemma lem4848616 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4848615 t1 t2 t3). Qed.
Lemma lem4848617 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4848618 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4848617 t1 t2 t3) (@lem4848616 t1 t2 t3)). Qed.
Lemma lem4848619 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4848618 t1 t2 t3)). Qed.
Lemma lem4848620 {A : Type'} (P : type180 A) : term7 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4848621 {A : Type'} (P : type180 A) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4848622 {A : Type'} (P : type180 A) : term8 A P.
Proof. exact (EQ_MP (@lem4848621 A P) (@lem4848620 A P)). Qed.
Lemma lem4848623 {A : Type'} (P : type180 A) (Q : type686 A) : term9 A P Q.
Proof. exact (@lem4848622 A P Q). Qed.
Lemma lem4848624 {A : Type'} (P : type180 A) (Q : type686 A) : (term9 A P Q) = ((@INTERSECTION_OF A P Q) = (term10 A P Q)).
Proof. exact (eq_refl (term9 A P Q)). Qed.
Lemma lem4848635 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term10 A P Q).
Proof. exact (EQ_MP (@lem4848624 A P Q) (@lem4848623 A P Q)). Qed.
Lemma lem4848636 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) : (@INTERSECTION_OF _111337 P Q) = (term10 _111337 P Q).
Proof. exact (@lem4848635 _111337 P Q). Qed.
Lemma lem4848653 {_111337 : Type'} (s : _111337 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4848654 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (@INTERSECTION_OF _111337 P Q s) = (term11 _111337 P Q s).
Proof. exact (MK_COMB (@lem4848636 _111337 P Q) (@lem4848653 _111337 s)). Qed.
Lemma lem4848656 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4848657 {_111337 : Type'} (f : type686 _111337) (y : _111337 -> Prop) : (term13 _111337 f y) = (f y).
Proof. exact (@lem4848656 (_111337 -> Prop) Prop f y). Qed.
Lemma lem4848658 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term14 _111337 P Q s) = (term11 _111337 P Q s).
Proof. exact (@lem4848657 _111337 (term10 _111337 P Q) s). Qed.
Lemma lem4848659 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term11 _111337 P Q s) = (term15 _111337 P Q s).
Proof. exact (eq_refl (term11 _111337 P Q s)). Qed.
Lemma lem4848660 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) : (term16 _111337 P Q) = (term10 _111337 P Q).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4848659 _111337 P Q s)). Qed.
Lemma lem4848661 {_111337 : Type'} (s : _111337 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4848662 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term14 _111337 P Q s) = (term11 _111337 P Q s).
Proof. exact (MK_COMB (@lem4848660 _111337 P Q) (@lem4848661 _111337 s)). Qed.
Lemma lem4848663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848664 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term17 _111337 P Q s) = (term18 _111337 P Q s).
Proof. exact (MK_COMB (@lem4848663) (@lem4848662 _111337 P Q s)). Qed.
Lemma lem4848665 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term11 _111337 P Q s) = (term15 _111337 P Q s).
Proof. exact (eq_refl (term11 _111337 P Q s)). Qed.
Lemma lem4848666 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : ((term14 _111337 P Q s) = (term11 _111337 P Q s)) = ((term11 _111337 P Q s) = (term15 _111337 P Q s)).
Proof. exact (MK_COMB (@lem4848664 _111337 P Q s) (@lem4848665 _111337 P Q s)). Qed.
Lemma lem4848667 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term11 _111337 P Q s) = (term15 _111337 P Q s).
Proof. exact (EQ_MP (@lem4848666 _111337 P Q s) (@lem4848658 _111337 P Q s)). Qed.
Lemma lem4848684 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (@INTERSECTION_OF _111337 P Q s) = (term15 _111337 P Q s).
Proof. exact (TRANS (@lem4848654 _111337 P Q s) (@lem4848667 _111337 P Q s)). Qed.
Lemma lem4848685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848686 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term19 _111337 P Q s) = (term20 _111337 P Q s).
Proof. exact (MK_COMB (@lem4848685) (@lem4848684 _111337 P Q s)). Qed.
Lemma lem4848687 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4848688 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term21 _111337 P Q R s) = (term22 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4848686 _111337 P Q s) (@lem4848687 _111337 R s)). Qed.
Lemma lem4848691 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term23 _111337 P Q R) = (term24 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4848688 _111337 P Q R s)). Qed.
Lemma lem4848692 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4848693 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term25 _111337 P Q R) = (term26 _111337 P Q R).
Proof. exact (MK_COMB (@lem4848692 _111337) (@lem4848691 _111337 P Q R)). Qed.
Lemma lem4848698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848699 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term27 _111337 P Q R) = (term28 _111337 P Q R).
Proof. exact (MK_COMB (@lem4848698) (@lem4848693 _111337 P Q R)). Qed.
Lemma lem4848714 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term29 _111337 P Q R) = (term29 _111337 P Q R).
Proof. exact (eq_refl (term29 _111337 P Q R)). Qed.
Lemma lem4848715 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term25 _111337 P Q R) = (term29 _111337 P Q R)) = ((term26 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4848699 _111337 P Q R) (@lem4848714 _111337 P Q R)). Qed.
Lemma lem4848718 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term26 _111337 P Q R) = (term29 _111337 P Q R)) = ((term25 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (SYM (@lem4848715 _111337 P Q R)). Qed.
Lemma lem4848720 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4848721 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term26 _111337 P Q R) = (term29 _111337 P Q R)) = (term31 _111337 P Q R).
Proof. exact (@lem4848720 ((term26 _111337 P Q R) = (term29 _111337 P Q R))). Qed.
Lemma lem4848722 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term31 _111337 P Q R) = ((term26 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (SYM (@lem4848721 _111337 P Q R)). Qed.
Lemma lem4848723 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : term32 _111337 P Q R.
Proof. exact (h1). Qed.
Lemma lem4848726 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term31 _111337 P Q R) : term31 _111337 P Q R.
Proof. exact (h1). Qed.
Lemma lem4848727 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term33 _111337 P Q R.
Proof. exact (fun h0 : term31 _111337 P Q R => @lem4848726 _111337 P Q R h0). Qed.
Lemma lem4848728 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term33 _111337 P Q R) : term33 _111337 P Q R.
Proof. exact (h1). Qed.
Lemma lem4848729 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term31 _111337 P Q R) : term31 _111337 P Q R.
Proof. exact (h1). Qed.
Lemma lem4848730 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term31 _111337 P Q R) (h2 : term33 _111337 P Q R) : term31 _111337 P Q R.
Proof. exact (@lem4848728 _111337 P Q R h2 (@lem4848729 _111337 P Q R h1)). Qed.
Lemma lem4848731 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term31 _111337 P Q R) : term34 _111337 P Q R.
Proof. exact (fun h0 : term33 _111337 P Q R => @lem4848730 _111337 P Q R h1 h0). Qed.
Lemma lem4848732 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term33 _111337 P Q R) : term33 _111337 P Q R.
Proof. exact (h1). Qed.
Lemma lem4848733 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term31 _111337 P Q R) (h2 : term33 _111337 P Q R) : term31 _111337 P Q R.
Proof. exact (@lem4848731 _111337 P Q R h1 (@lem4848732 _111337 P Q R h2)). Qed.
Lemma lem4848734 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term33 _111337 P Q R) : term33 _111337 P Q R.
Proof. exact (fun h0 : term31 _111337 P Q R => @lem4848733 _111337 P Q R h0 h1). Qed.
Lemma lem4848735 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term35 _111337 P Q R.
Proof. exact (fun h0 : term33 _111337 P Q R => @lem4848734 _111337 P Q R h0). Qed.
Lemma lem4848738 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term33 _111337 P Q R.
Proof. exact (@lem4848735 _111337 P Q R (@lem4848727 _111337 P Q R)). Qed.
Lemma lem4848739 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term33 _111337 P Q R.
Proof. exact (@lem4848738 _111337 P Q R). Qed.
Lemma lem4848753 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4848754 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term31 _111337 P Q R) = (term36 _111337 P Q R).
Proof. exact (@lem4848753 (term32 _111337 P Q R)). Qed.
Lemma lem4848756 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4848757 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term36 _111337 P Q R) = ((term26 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (@lem4848756 ((term26 _111337 P Q R) = (term29 _111337 P Q R))). Qed.
Lemma lem4848758 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term31 _111337 P Q R) = ((term26 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (TRANS (@lem4848754 _111337 P Q R) (@lem4848757 _111337 P Q R)). Qed.
Lemma lem4848817 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : (term38 _111337 Q R) = (term39 _111337 Q R).
Proof. exact (fun_ext (fun P : type180 _111337 => @lem4848758 _111337 P Q R)). Qed.
Lemma lem4848818 {_111337 : Type'} : (@all (((_111337 -> Prop) -> Prop) -> Prop)) = (@all (((_111337 -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((_111337 -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4848819 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : (term40 _111337 Q R) = (term41 _111337 Q R).
Proof. exact (MK_COMB (@lem4848818 _111337) (@lem4848817 _111337 Q R)). Qed.
Lemma lem4848824 {_111337 : Type'} (R : type686 _111337) : (term42 _111337 R) = (term43 _111337 R).
Proof. exact (fun_ext (fun Q : type686 _111337 => @lem4848819 _111337 Q R)). Qed.
Lemma lem4848825 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4848826 {_111337 : Type'} (R : type686 _111337) : (term44 _111337 R) = (term45 _111337 R).
Proof. exact (MK_COMB (@lem4848825 _111337) (@lem4848824 _111337 R)). Qed.
Lemma lem4848831 {_111337 : Type'} : (term46 _111337) = (term47 _111337).
Proof. exact (fun_ext (fun R : type686 _111337 => @lem4848826 _111337 R)). Qed.
Lemma lem4848832 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4848841 {_111337 : Type'} : (term48 _111337) = (term49 _111337).
Proof. exact (MK_COMB (@lem4848832 _111337) (@lem4848831 _111337)). Qed.
Lemma lem4848842 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term50 _111337 R t) = (term50 _111337 R t).
Proof. exact (eq_refl (term50 _111337 R t)). Qed.
Lemma lem4848847 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term51 _111337 t Q c) = (term51 _111337 t Q c).
Proof. exact (eq_refl (term51 _111337 t Q c)). Qed.
Lemma lem4848848 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term52 _111337 t Q) = (term52 _111337 t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4848847 _111337 t Q c)). Qed.
Lemma lem4848849 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4848850 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term53 _111337 t Q) = (term53 _111337 t Q).
Proof. exact (MK_COMB (@lem4848849 _111337) (@lem4848848 _111337 t Q)). Qed.
Lemma lem4848853 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term54 _111337 P t) = (term54 _111337 P t).
Proof. exact (eq_refl (term54 _111337 P t)). Qed.
Lemma lem4848854 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term55 _111337 P t Q) = (term55 _111337 P t Q).
Proof. exact (MK_COMB (@lem4848853 _111337 P t) (@lem4848850 _111337 t Q)). Qed.
Lemma lem4848855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848856 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term56 _111337 P t Q) = (term56 _111337 P t Q).
Proof. exact (MK_COMB (@lem4848855) (@lem4848854 _111337 P t Q)). Qed.
Lemma lem4848857 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term57 _111337 P Q R t) = (term57 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4848856 _111337 P t Q) (@lem4848842 _111337 R t)). Qed.
Lemma lem4848858 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term58 _111337 P Q R) = (term58 _111337 P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4848857 _111337 P Q R t)). Qed.
Lemma lem4848859 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4848860 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term29 _111337 P Q R) = (term29 _111337 P Q R).
Proof. exact (MK_COMB (@lem4848859 _111337) (@lem4848858 _111337 P Q R)). Qed.
Lemma lem4848861 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4848862 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) : ((@INTERS _111337 u) = s) = ((@INTERS _111337 u) = s).
Proof. exact (eq_refl ((@INTERS _111337 u) = s)). Qed.
Lemma lem4848867 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term51 _111337 u Q c) = (term51 _111337 u Q c).
Proof. exact (eq_refl (term51 _111337 u Q c)). Qed.
Lemma lem4848868 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term52 _111337 u Q) = (term52 _111337 u Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4848867 _111337 u Q c)). Qed.
Lemma lem4848869 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4848870 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term53 _111337 u Q) = (term53 _111337 u Q).
Proof. exact (MK_COMB (@lem4848869 _111337) (@lem4848868 _111337 u Q)). Qed.
Lemma lem4848871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4848872 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term59 _111337 u Q) = (term59 _111337 u Q).
Proof. exact (MK_COMB (@lem4848871) (@lem4848870 _111337 u Q)). Qed.
Lemma lem4848873 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term60 _111337 Q u s) = (term60 _111337 Q u s).
Proof. exact (MK_COMB (@lem4848872 _111337 u Q) (@lem4848862 _111337 u s)). Qed.
Lemma lem4848876 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term54 _111337 P u) = (term54 _111337 P u).
Proof. exact (eq_refl (term54 _111337 P u)). Qed.
Lemma lem4848877 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term61 _111337 P Q u s) = (term61 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4848876 _111337 P u) (@lem4848873 _111337 Q u s)). Qed.
Lemma lem4848878 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term62 _111337 P Q s) = (term62 _111337 P Q s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4848877 _111337 P Q u s)). Qed.
Lemma lem4848879 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4848880 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term15 _111337 P Q s) = (term15 _111337 P Q s).
Proof. exact (MK_COMB (@lem4848879 _111337) (@lem4848878 _111337 P Q s)). Qed.
Lemma lem4848881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848882 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term20 _111337 P Q s) = (term20 _111337 P Q s).
Proof. exact (MK_COMB (@lem4848881) (@lem4848880 _111337 P Q s)). Qed.
Lemma lem4848883 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term22 _111337 P Q R s) = (term22 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4848882 _111337 P Q s) (@lem4848861 _111337 R s)). Qed.
Lemma lem4848884 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term24 _111337 P Q R) = (term24 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4848883 _111337 P Q R s)). Qed.
Lemma lem4848885 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4848886 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term26 _111337 P Q R) = (term26 _111337 P Q R).
Proof. exact (MK_COMB (@lem4848885 _111337) (@lem4848884 _111337 P Q R)). Qed.
Lemma lem4848887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848888 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term28 _111337 P Q R) = (term28 _111337 P Q R).
Proof. exact (MK_COMB (@lem4848887) (@lem4848886 _111337 P Q R)). Qed.
Lemma lem4848889 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term26 _111337 P Q R) = (term29 _111337 P Q R)) = ((term26 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4848888 _111337 P Q R) (@lem4848860 _111337 P Q R)). Qed.
Lemma lem4848890 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : (term39 _111337 Q R) = (term39 _111337 Q R).
Proof. exact (fun_ext (fun P : type180 _111337 => @lem4848889 _111337 P Q R)). Qed.
Lemma lem4848891 {_111337 : Type'} : (@all (((_111337 -> Prop) -> Prop) -> Prop)) = (@all (((_111337 -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((_111337 -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4848892 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : (term41 _111337 Q R) = (term41 _111337 Q R).
Proof. exact (MK_COMB (@lem4848891 _111337) (@lem4848890 _111337 Q R)). Qed.
Lemma lem4848893 {_111337 : Type'} (R : type686 _111337) : (term43 _111337 R) = (term43 _111337 R).
Proof. exact (fun_ext (fun Q : type686 _111337 => @lem4848892 _111337 Q R)). Qed.
Lemma lem4848894 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4848895 {_111337 : Type'} (R : type686 _111337) : (term45 _111337 R) = (term45 _111337 R).
Proof. exact (MK_COMB (@lem4848894 _111337) (@lem4848893 _111337 R)). Qed.
Lemma lem4848896 {_111337 : Type'} : (term47 _111337) = (term47 _111337).
Proof. exact (fun_ext (fun R : type686 _111337 => @lem4848895 _111337 R)). Qed.
Lemma lem4848897 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4848898 {_111337 : Type'} : (term49 _111337) = (term49 _111337).
Proof. exact (MK_COMB (@lem4848897 _111337) (@lem4848896 _111337)). Qed.
Lemma lem4848963 {_111337 : Type'} : (term48 _111337) = (term49 _111337).
Proof. exact (TRANS (@lem4848841 _111337) (@lem4848898 _111337)). Qed.
Lemma lem4848964 {_111337 : Type'} : (term49 _111337) = (term48 _111337).
Proof. exact (SYM (@lem4848963 _111337)). Qed.
Lemma lem4848966 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4848967 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term26 _111337 P Q R) = (term29 _111337 P Q R)) = (term31 _111337 P Q R).
Proof. exact (@lem4848966 ((term26 _111337 P Q R) = (term29 _111337 P Q R))). Qed.
Lemma lem4848968 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term31 _111337 P Q R) = ((term26 _111337 P Q R) = (term29 _111337 P Q R)).
Proof. exact (SYM (@lem4848967 _111337 P Q R)). Qed.
Lemma lem4848969 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : term32 _111337 P Q R.
Proof. exact (h1). Qed.
Lemma lem4848980 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term63 _111337 u Q c) = (term64 _111337 u Q c).
Proof. exact (@lem17362 (@IN (_111337 -> Prop) c u) (Q c)). Qed.
Lemma lem4848985 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term51 _111337 u Q c) = (term65 _111337 u Q c).
Proof. exact (@lem17265 (@IN (_111337 -> Prop) c u) (Q c)). Qed.
Lemma lem4848986 {_111337 : Type'} (P : type686 _111337) : (term66 _111337 P) = (term67 _111337 P).
Proof. exact (@lem18392 (_111337 -> Prop) P). Qed.
Lemma lem4848987 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term68 _111337 u Q) = (term69 _111337 u Q).
Proof. exact (@lem4848986 _111337 (term52 _111337 u Q)). Qed.
Lemma lem4848988 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term70 _111337 u Q c) = (term51 _111337 u Q c).
Proof. exact (eq_refl (term70 _111337 u Q c)). Qed.
Lemma lem4848989 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4848990 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term71 _111337 u Q c) = (term63 _111337 u Q c).
Proof. exact (MK_COMB (@lem4848989) (@lem4848988 _111337 u Q c)). Qed.
Lemma lem4848991 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term71 _111337 u Q c) = (term64 _111337 u Q c).
Proof. exact (TRANS (@lem4848990 _111337 u Q c) (@lem4848980 _111337 u Q c)). Qed.
Lemma lem4848992 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term72 _111337 u Q) = (term73 _111337 u Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4848991 _111337 u Q c)). Qed.
Lemma lem4848993 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4848994 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term69 _111337 u Q) = (term74 _111337 u Q).
Proof. exact (MK_COMB (@lem4848993 _111337) (@lem4848992 _111337 u Q)). Qed.
Lemma lem4848995 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term68 _111337 u Q) = (term74 _111337 u Q).
Proof. exact (TRANS (@lem4848987 _111337 u Q) (@lem4848994 _111337 u Q)). Qed.
Lemma lem4848996 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term52 _111337 u Q) = (term75 _111337 u Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4848985 _111337 u Q c)). Qed.
Lemma lem4848997 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4848998 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term53 _111337 u Q) = (term76 _111337 u Q).
Proof. exact (MK_COMB (@lem4848997 _111337) (@lem4848996 _111337 u Q)). Qed.
Lemma lem4848999 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) : (term77 _111337 u s) = (term77 _111337 u s).
Proof. exact (eq_refl (term77 _111337 u s)). Qed.
Lemma lem4849000 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) : ((@INTERS _111337 u) = s) = ((@INTERS _111337 u) = s).
Proof. exact (eq_refl ((@INTERS _111337 u) = s)). Qed.
Lemma lem4849001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849002 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term78 _111337 u Q) = (term79 _111337 u Q).
Proof. exact (MK_COMB (@lem4849001) (@lem4848995 _111337 u Q)). Qed.
Lemma lem4849003 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term80 _111337 Q u s) = (term81 _111337 Q u s).
Proof. exact (MK_COMB (@lem4849002 _111337 u Q) (@lem4848999 _111337 u s)). Qed.
Lemma lem4849004 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term82 _111337 Q u s) = (term80 _111337 Q u s).
Proof. exact (@lem17045 (term53 _111337 u Q) ((@INTERS _111337 u) = s)). Qed.
Lemma lem4849005 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term82 _111337 Q u s) = (term81 _111337 Q u s).
Proof. exact (TRANS (@lem4849004 _111337 Q u s) (@lem4849003 _111337 Q u s)). Qed.
Lemma lem4849006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849007 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term59 _111337 u Q) = (term83 _111337 u Q).
Proof. exact (MK_COMB (@lem4849006) (@lem4848998 _111337 u Q)). Qed.
Lemma lem4849008 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term60 _111337 Q u s) = (term84 _111337 Q u s).
Proof. exact (MK_COMB (@lem4849007 _111337 u Q) (@lem4849000 _111337 u s)). Qed.
Lemma lem4849010 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term85 _111337 P u) = (term85 _111337 P u).
Proof. exact (eq_refl (term85 _111337 P u)). Qed.
Lemma lem4849011 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term86 _111337 P Q u s) = (term87 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849010 _111337 P u) (@lem4849005 _111337 Q u s)). Qed.
Lemma lem4849012 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term88 _111337 P Q u s) = (term86 _111337 P Q u s).
Proof. exact (@lem17045 (P u) (term60 _111337 Q u s)). Qed.
Lemma lem4849013 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term88 _111337 P Q u s) = (term87 _111337 P Q u s).
Proof. exact (TRANS (@lem4849012 _111337 P Q u s) (@lem4849011 _111337 P Q u s)). Qed.
Lemma lem4849015 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term54 _111337 P u) = (term54 _111337 P u).
Proof. exact (eq_refl (term54 _111337 P u)). Qed.
Lemma lem4849016 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term61 _111337 P Q u s) = (term89 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849015 _111337 P u) (@lem4849008 _111337 Q u s)). Qed.
Lemma lem4849017 {_111337 : Type'} (P : type180 _111337) : (term90 _111337 P) = (term91 _111337 P).
Proof. exact (@lem18394 (type686 _111337) P). Qed.
Lemma lem4849018 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term92 _111337 P Q s) = (term93 _111337 P Q s).
Proof. exact (@lem4849017 _111337 (term62 _111337 P Q s)). Qed.
Lemma lem4849019 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term94 _111337 P Q s u) = (term61 _111337 P Q u s).
Proof. exact (eq_refl (term94 _111337 P Q s u)). Qed.
Lemma lem4849020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4849021 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term95 _111337 P Q s u) = (term88 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849020) (@lem4849019 _111337 P Q u s)). Qed.
Lemma lem4849022 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term95 _111337 P Q s u) = (term87 _111337 P Q u s).
Proof. exact (TRANS (@lem4849021 _111337 P Q u s) (@lem4849013 _111337 P Q u s)). Qed.
Lemma lem4849023 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term96 _111337 P Q s) = (term97 _111337 P Q s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849022 _111337 P Q u s)). Qed.
Lemma lem4849024 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849025 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term93 _111337 P Q s) = (term98 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849024 _111337) (@lem4849023 _111337 P Q s)). Qed.
Lemma lem4849026 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term92 _111337 P Q s) = (term98 _111337 P Q s).
Proof. exact (TRANS (@lem4849018 _111337 P Q s) (@lem4849025 _111337 P Q s)). Qed.
Lemma lem4849027 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term62 _111337 P Q s) = (term99 _111337 P Q s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849016 _111337 P Q u s)). Qed.
Lemma lem4849028 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849029 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term15 _111337 P Q s) = (term100 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849028 _111337) (@lem4849027 _111337 P Q s)). Qed.
Lemma lem4849030 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term101 _111337 R s) = (term101 _111337 R s).
Proof. exact (eq_refl (term101 _111337 R s)). Qed.
Lemma lem4849031 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4849032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849033 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term102 _111337 P Q s) = (term103 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849032) (@lem4849029 _111337 P Q s)). Qed.
Lemma lem4849034 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term104 _111337 P Q R s) = (term105 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849033 _111337 P Q s) (@lem4849030 _111337 R s)). Qed.
Lemma lem4849035 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term106 _111337 P Q R s) = (term104 _111337 P Q R s).
Proof. exact (@lem17362 (term15 _111337 P Q s) (R s)). Qed.
Lemma lem4849036 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term106 _111337 P Q R s) = (term105 _111337 P Q R s).
Proof. exact (TRANS (@lem4849035 _111337 P Q R s) (@lem4849034 _111337 P Q R s)). Qed.
Lemma lem4849037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849038 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term107 _111337 P Q s) = (term108 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849037) (@lem4849026 _111337 P Q s)). Qed.
Lemma lem4849039 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term109 _111337 P Q R s) = (term110 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849038 _111337 P Q s) (@lem4849031 _111337 R s)). Qed.
Lemma lem4849040 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term22 _111337 P Q R s) = (term109 _111337 P Q R s).
Proof. exact (@lem17265 (term15 _111337 P Q s) (R s)). Qed.
Lemma lem4849041 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term22 _111337 P Q R s) = (term110 _111337 P Q R s).
Proof. exact (TRANS (@lem4849040 _111337 P Q R s) (@lem4849039 _111337 P Q R s)). Qed.
Lemma lem4849042 {_111337 : Type'} (P : type686 _111337) : (term66 _111337 P) = (term67 _111337 P).
Proof. exact (@lem18392 (_111337 -> Prop) P). Qed.
Lemma lem4849043 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term111 _111337 P Q R) = (term112 _111337 P Q R).
Proof. exact (@lem4849042 _111337 (term24 _111337 P Q R)). Qed.
Lemma lem4849044 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term113 _111337 P Q R s) = (term22 _111337 P Q R s).
Proof. exact (eq_refl (term113 _111337 P Q R s)). Qed.
Lemma lem4849045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4849046 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term114 _111337 P Q R s) = (term106 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849045) (@lem4849044 _111337 P Q R s)). Qed.
Lemma lem4849047 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term114 _111337 P Q R s) = (term105 _111337 P Q R s).
Proof. exact (TRANS (@lem4849046 _111337 P Q R s) (@lem4849036 _111337 P Q R s)). Qed.
Lemma lem4849048 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term115 _111337 P Q R) = (term116 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849047 _111337 P Q R s)). Qed.
Lemma lem4849049 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849050 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term112 _111337 P Q R) = (term117 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849049 _111337) (@lem4849048 _111337 P Q R)). Qed.
Lemma lem4849051 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term111 _111337 P Q R) = (term117 _111337 P Q R).
Proof. exact (TRANS (@lem4849043 _111337 P Q R) (@lem4849050 _111337 P Q R)). Qed.
Lemma lem4849052 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term24 _111337 P Q R) = (term118 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849041 _111337 P Q R s)). Qed.
Lemma lem4849053 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4849054 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term26 _111337 P Q R) = (term119 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849053 _111337) (@lem4849052 _111337 P Q R)). Qed.
Lemma lem4849065 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term63 _111337 t Q c) = (term64 _111337 t Q c).
Proof. exact (@lem17362 (@IN (_111337 -> Prop) c t) (Q c)). Qed.
Lemma lem4849070 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term51 _111337 t Q c) = (term65 _111337 t Q c).
Proof. exact (@lem17265 (@IN (_111337 -> Prop) c t) (Q c)). Qed.
Lemma lem4849071 {_111337 : Type'} (P : type686 _111337) : (term66 _111337 P) = (term67 _111337 P).
Proof. exact (@lem18392 (_111337 -> Prop) P). Qed.
Lemma lem4849072 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term68 _111337 t Q) = (term69 _111337 t Q).
Proof. exact (@lem4849071 _111337 (term52 _111337 t Q)). Qed.
Lemma lem4849073 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term70 _111337 t Q c) = (term51 _111337 t Q c).
Proof. exact (eq_refl (term70 _111337 t Q c)). Qed.
Lemma lem4849074 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4849075 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term71 _111337 t Q c) = (term63 _111337 t Q c).
Proof. exact (MK_COMB (@lem4849074) (@lem4849073 _111337 t Q c)). Qed.
Lemma lem4849076 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term71 _111337 t Q c) = (term64 _111337 t Q c).
Proof. exact (TRANS (@lem4849075 _111337 t Q c) (@lem4849065 _111337 t Q c)). Qed.
Lemma lem4849077 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term72 _111337 t Q) = (term73 _111337 t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849076 _111337 t Q c)). Qed.
Lemma lem4849078 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849079 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term69 _111337 t Q) = (term74 _111337 t Q).
Proof. exact (MK_COMB (@lem4849078 _111337) (@lem4849077 _111337 t Q)). Qed.
Lemma lem4849080 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term68 _111337 t Q) = (term74 _111337 t Q).
Proof. exact (TRANS (@lem4849072 _111337 t Q) (@lem4849079 _111337 t Q)). Qed.
Lemma lem4849081 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term52 _111337 t Q) = (term75 _111337 t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849070 _111337 t Q c)). Qed.
Lemma lem4849082 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4849083 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term53 _111337 t Q) = (term76 _111337 t Q).
Proof. exact (MK_COMB (@lem4849082 _111337) (@lem4849081 _111337 t Q)). Qed.
Lemma lem4849085 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term85 _111337 P t) = (term85 _111337 P t).
Proof. exact (eq_refl (term85 _111337 P t)). Qed.
Lemma lem4849086 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term120 _111337 P t Q) = (term121 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849085 _111337 P t) (@lem4849080 _111337 t Q)). Qed.
Lemma lem4849087 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term122 _111337 P t Q) = (term120 _111337 P t Q).
Proof. exact (@lem17045 (P t) (term53 _111337 t Q)). Qed.
Lemma lem4849088 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term122 _111337 P t Q) = (term121 _111337 P t Q).
Proof. exact (TRANS (@lem4849087 _111337 P t Q) (@lem4849086 _111337 P t Q)). Qed.
Lemma lem4849090 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term54 _111337 P t) = (term54 _111337 P t).
Proof. exact (eq_refl (term54 _111337 P t)). Qed.
Lemma lem4849091 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term55 _111337 P t Q) = (term123 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849090 _111337 P t) (@lem4849083 _111337 t Q)). Qed.
Lemma lem4849092 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term124 _111337 R t) = (term124 _111337 R t).
Proof. exact (eq_refl (term124 _111337 R t)). Qed.
Lemma lem4849093 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term50 _111337 R t) = (term50 _111337 R t).
Proof. exact (eq_refl (term50 _111337 R t)). Qed.
Lemma lem4849094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849095 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term125 _111337 P t Q) = (term126 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849094) (@lem4849091 _111337 P t Q)). Qed.
Lemma lem4849096 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term127 _111337 P Q R t) = (term128 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849095 _111337 P t Q) (@lem4849092 _111337 R t)). Qed.
Lemma lem4849097 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term129 _111337 P Q R t) = (term127 _111337 P Q R t).
Proof. exact (@lem17362 (term55 _111337 P t Q) (term50 _111337 R t)). Qed.
Lemma lem4849098 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term129 _111337 P Q R t) = (term128 _111337 P Q R t).
Proof. exact (TRANS (@lem4849097 _111337 P Q R t) (@lem4849096 _111337 P Q R t)). Qed.
Lemma lem4849099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849100 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term130 _111337 P t Q) = (term131 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849099) (@lem4849088 _111337 P t Q)). Qed.
Lemma lem4849101 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term132 _111337 P Q R t) = (term133 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849100 _111337 P t Q) (@lem4849093 _111337 R t)). Qed.
Lemma lem4849102 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term57 _111337 P Q R t) = (term132 _111337 P Q R t).
Proof. exact (@lem17265 (term55 _111337 P t Q) (term50 _111337 R t)). Qed.
Lemma lem4849103 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term57 _111337 P Q R t) = (term133 _111337 P Q R t).
Proof. exact (TRANS (@lem4849102 _111337 P Q R t) (@lem4849101 _111337 P Q R t)). Qed.
Lemma lem4849104 {_111337 : Type'} (P : type180 _111337) : (term134 _111337 P) = (term135 _111337 P).
Proof. exact (@lem18392 (type686 _111337) P). Qed.
Lemma lem4849105 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term136 _111337 P Q R) = (term137 _111337 P Q R).
Proof. exact (@lem4849104 _111337 (term58 _111337 P Q R)). Qed.
Lemma lem4849106 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term138 _111337 P Q R t) = (term57 _111337 P Q R t).
Proof. exact (eq_refl (term138 _111337 P Q R t)). Qed.
Lemma lem4849107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4849108 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term139 _111337 P Q R t) = (term129 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849107) (@lem4849106 _111337 P Q R t)). Qed.
Lemma lem4849109 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term139 _111337 P Q R t) = (term128 _111337 P Q R t).
Proof. exact (TRANS (@lem4849108 _111337 P Q R t) (@lem4849098 _111337 P Q R t)). Qed.
Lemma lem4849110 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term140 _111337 P Q R) = (term141 _111337 P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849109 _111337 P Q R t)). Qed.
Lemma lem4849111 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849112 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term137 _111337 P Q R) = (term142 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849111 _111337) (@lem4849110 _111337 P Q R)). Qed.
Lemma lem4849113 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term136 _111337 P Q R) = (term142 _111337 P Q R).
Proof. exact (TRANS (@lem4849105 _111337 P Q R) (@lem4849112 _111337 P Q R)). Qed.
Lemma lem4849114 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term58 _111337 P Q R) = (term143 _111337 P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849103 _111337 P Q R t)). Qed.
Lemma lem4849115 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849116 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term29 _111337 P Q R) = (term144 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849115 _111337) (@lem4849114 _111337 P Q R)). Qed.
Lemma lem4849117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849118 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term145 _111337 P Q R) = (term146 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849117) (@lem4849051 _111337 P Q R)). Qed.
Lemma lem4849119 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term147 _111337 P Q R) = (term148 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849118 _111337 P Q R) (@lem4849116 _111337 P Q R)). Qed.
Lemma lem4849120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849121 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term149 _111337 P Q R) = (term150 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849120) (@lem4849054 _111337 P Q R)). Qed.
Lemma lem4849122 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term151 _111337 P Q R) = (term152 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849121 _111337 P Q R) (@lem4849113 _111337 P Q R)). Qed.
Lemma lem4849123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849124 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term153 _111337 P Q R) = (term154 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849123) (@lem4849122 _111337 P Q R)). Qed.
Lemma lem4849125 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term155 _111337 P Q R) = (term156 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849124 _111337 P Q R) (@lem4849119 _111337 P Q R)). Qed.
Lemma lem4849126 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term32 _111337 P Q R) = (term155 _111337 P Q R).
Proof. exact (@lem17646 (term26 _111337 P Q R) (term29 _111337 P Q R)). Qed.
Lemma lem4849127 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term32 _111337 P Q R) = (term156 _111337 P Q R).
Proof. exact (TRANS (@lem4849126 _111337 P Q R) (@lem4849125 _111337 P Q R)). Qed.
Lemma lem4849542 {A : Type'} (P : A -> Prop) (Q : Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4849543 {_111337 : Type'} (P : type686 _111337) (Q : Prop) : (term159 _111337 P Q) = (term160 _111337 P Q).
Proof. exact (@lem4849542 (_111337 -> Prop) P Q). Qed.
Lemma lem4849544 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term161 _111337 Q u s) = (term162 _111337 Q u s).
Proof. exact (@lem4849543 _111337 (term73 _111337 u Q) (term77 _111337 u s)). Qed.
Lemma lem4849545 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term163 _111337 u Q c) = (term64 _111337 u Q c).
Proof. exact (eq_refl (term163 _111337 u Q c)). Qed.
Lemma lem4849546 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term164 _111337 u Q) = (term73 _111337 u Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849545 _111337 u Q c)). Qed.
Lemma lem4849547 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849548 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term165 _111337 u Q) = (term74 _111337 u Q).
Proof. exact (MK_COMB (@lem4849547 _111337) (@lem4849546 _111337 u Q)). Qed.
Lemma lem4849549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849550 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term166 _111337 u Q) = (term79 _111337 u Q).
Proof. exact (MK_COMB (@lem4849549) (@lem4849548 _111337 u Q)). Qed.
Lemma lem4849551 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) : (term77 _111337 u s) = (term77 _111337 u s).
Proof. exact (eq_refl (term77 _111337 u s)). Qed.
Lemma lem4849552 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term161 _111337 Q u s) = (term81 _111337 Q u s).
Proof. exact (MK_COMB (@lem4849550 _111337 u Q) (@lem4849551 _111337 u s)). Qed.
Lemma lem4849553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849554 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term167 _111337 Q u s) = (term168 _111337 Q u s).
Proof. exact (MK_COMB (@lem4849553) (@lem4849552 _111337 Q u s)). Qed.
Lemma lem4849555 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term163 _111337 u Q c) = (term64 _111337 u Q c).
Proof. exact (eq_refl (term163 _111337 u Q c)). Qed.
Lemma lem4849556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849557 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term169 _111337 u Q c) = (term170 _111337 u Q c).
Proof. exact (MK_COMB (@lem4849556) (@lem4849555 _111337 u Q c)). Qed.
Lemma lem4849558 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) : (term77 _111337 u s) = (term77 _111337 u s).
Proof. exact (eq_refl (term77 _111337 u s)). Qed.
Lemma lem4849559 {_111337 : Type'} (Q : type686 _111337) (c : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) : (term171 _111337 Q c u s) = (term172 _111337 Q c u s).
Proof. exact (MK_COMB (@lem4849557 _111337 u Q c) (@lem4849558 _111337 u s)). Qed.
Lemma lem4849560 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term173 _111337 Q u s) = (term174 _111337 Q u s).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849559 _111337 Q c u s)). Qed.
Lemma lem4849561 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849562 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term162 _111337 Q u s) = (term175 _111337 Q u s).
Proof. exact (MK_COMB (@lem4849561 _111337) (@lem4849560 _111337 Q u s)). Qed.
Lemma lem4849563 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : ((term161 _111337 Q u s) = (term162 _111337 Q u s)) = ((term81 _111337 Q u s) = (term175 _111337 Q u s)).
Proof. exact (MK_COMB (@lem4849554 _111337 Q u s) (@lem4849562 _111337 Q u s)). Qed.
Lemma lem4849564 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term81 _111337 Q u s) = (term175 _111337 Q u s).
Proof. exact (EQ_MP (@lem4849563 _111337 Q u s) (@lem4849544 _111337 Q u s)). Qed.
Lemma lem4849565 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term85 _111337 P u) = (term85 _111337 P u).
Proof. exact (eq_refl (term85 _111337 P u)). Qed.
Lemma lem4849566 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term87 _111337 P Q u s) = (term176 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849565 _111337 P u) (@lem4849564 _111337 Q u s)). Qed.
Lemma lem4849568 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4849569 {_111337 : Type'} (P : Prop) (Q : type686 _111337) : (term179 _111337 P Q) = (term180 _111337 P Q).
Proof. exact (@lem4849568 (_111337 -> Prop) P Q). Qed.
Lemma lem4849570 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term181 _111337 P Q u s) = (term182 _111337 P Q u s).
Proof. exact (@lem4849569 _111337 (term183 _111337 P u) (term174 _111337 Q u s)). Qed.
Lemma lem4849571 {_111337 : Type'} (Q : type686 _111337) (c : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) : (term184 _111337 Q u s c) = (term172 _111337 Q c u s).
Proof. exact (eq_refl (term184 _111337 Q u s c)). Qed.
Lemma lem4849572 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term185 _111337 Q u s) = (term174 _111337 Q u s).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849571 _111337 Q c u s)). Qed.
Lemma lem4849573 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849574 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term186 _111337 Q u s) = (term175 _111337 Q u s).
Proof. exact (MK_COMB (@lem4849573 _111337) (@lem4849572 _111337 Q u s)). Qed.
Lemma lem4849575 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term85 _111337 P u) = (term85 _111337 P u).
Proof. exact (eq_refl (term85 _111337 P u)). Qed.
Lemma lem4849576 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term181 _111337 P Q u s) = (term176 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849575 _111337 P u) (@lem4849574 _111337 Q u s)). Qed.
Lemma lem4849577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849578 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term187 _111337 P Q u s) = (term188 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849577) (@lem4849576 _111337 P Q u s)). Qed.
Lemma lem4849579 {_111337 : Type'} (Q : type686 _111337) (c : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) : (term184 _111337 Q u s c) = (term172 _111337 Q c u s).
Proof. exact (eq_refl (term184 _111337 Q u s c)). Qed.
Lemma lem4849580 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term85 _111337 P u) = (term85 _111337 P u).
Proof. exact (eq_refl (term85 _111337 P u)). Qed.
Lemma lem4849581 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) : (term189 _111337 P Q u s c) = (term190 _111337 P Q c u s).
Proof. exact (MK_COMB (@lem4849580 _111337 P u) (@lem4849579 _111337 Q c u s)). Qed.
Lemma lem4849582 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term191 _111337 P Q u s) = (term192 _111337 P Q u s).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849581 _111337 P Q c u s)). Qed.
Lemma lem4849583 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849584 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term182 _111337 P Q u s) = (term193 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849583 _111337) (@lem4849582 _111337 P Q u s)). Qed.
Lemma lem4849585 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : ((term181 _111337 P Q u s) = (term182 _111337 P Q u s)) = ((term176 _111337 P Q u s) = (term193 _111337 P Q u s)).
Proof. exact (MK_COMB (@lem4849578 _111337 P Q u s) (@lem4849584 _111337 P Q u s)). Qed.
Lemma lem4849586 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term176 _111337 P Q u s) = (term193 _111337 P Q u s).
Proof. exact (EQ_MP (@lem4849585 _111337 P Q u s) (@lem4849570 _111337 P Q u s)). Qed.
Lemma lem4849587 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term87 _111337 P Q u s) = (term193 _111337 P Q u s).
Proof. exact (TRANS (@lem4849566 _111337 P Q u s) (@lem4849586 _111337 P Q u s)). Qed.
Lemma lem4849588 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term97 _111337 P Q s) = (term194 _111337 P Q s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849587 _111337 P Q u s)). Qed.
Lemma lem4849589 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849590 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term98 _111337 P Q s) = (term195 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849589 _111337) (@lem4849588 _111337 P Q s)). Qed.
Lemma lem4849592 {A B : Type'} (P : type1413 A B) : (term196 A B P) = (term197 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4849593 {_111337 : Type'} (P : type174 _111337) : (term198 _111337 P) = (term199 _111337 P).
Proof. exact (@lem4849592 (type686 _111337) (_111337 -> Prop) P). Qed.
Lemma lem4849594 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term200 _111337 P Q s) = (term201 _111337 P Q s).
Proof. exact (@lem4849593 _111337 (term202 _111337 P Q s)). Qed.
Lemma lem4849595 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term203 _111337 P Q s u) = (term192 _111337 P Q u s).
Proof. exact (eq_refl (term203 _111337 P Q s u)). Qed.
Lemma lem4849596 {_111337 : Type'} (c : _111337 -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4849597 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (c : _111337 -> Prop) : (term204 _111337 P Q s u c) = (term205 _111337 P Q u s c).
Proof. exact (MK_COMB (@lem4849595 _111337 P Q u s) (@lem4849596 _111337 c)). Qed.
Lemma lem4849598 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) : (term205 _111337 P Q u s c) = (term190 _111337 P Q c u s).
Proof. exact (eq_refl (term205 _111337 P Q u s c)). Qed.
Lemma lem4849599 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) : (term204 _111337 P Q s u c) = (term190 _111337 P Q c u s).
Proof. exact (TRANS (@lem4849597 _111337 P Q u s c) (@lem4849598 _111337 P Q c u s)). Qed.
Lemma lem4849600 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term206 _111337 P Q s u) = (term192 _111337 P Q u s).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849599 _111337 P Q c u s)). Qed.
Lemma lem4849601 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849602 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term207 _111337 P Q s u) = (term193 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849601 _111337) (@lem4849600 _111337 P Q u s)). Qed.
Lemma lem4849603 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term208 _111337 P Q s) = (term194 _111337 P Q s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849602 _111337 P Q u s)). Qed.
Lemma lem4849604 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849605 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term200 _111337 P Q s) = (term195 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849604 _111337) (@lem4849603 _111337 P Q s)). Qed.
Lemma lem4849606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849607 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term209 _111337 P Q s) = (term210 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849606) (@lem4849605 _111337 P Q s)). Qed.
Lemma lem4849608 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term203 _111337 P Q s u) = (term192 _111337 P Q u s).
Proof. exact (eq_refl (term203 _111337 P Q s u)). Qed.
Lemma lem4849609 {_111337 : Type'} (c : type178 _111337) (u : type686 _111337) : (c u) = (c u).
Proof. exact (eq_refl (c u)). Qed.
Lemma lem4849610 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) (c : type178 _111337) (u : type686 _111337) : (term211 _111337 P Q s c u) = (term212 _111337 P Q s c u).
Proof. exact (MK_COMB (@lem4849608 _111337 P Q u s) (@lem4849609 _111337 c u)). Qed.
Lemma lem4849611 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term212 _111337 P Q s c u) = (term213 _111337 P Q c u s).
Proof. exact (eq_refl (term212 _111337 P Q s c u)). Qed.
Lemma lem4849612 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term211 _111337 P Q s c u) = (term213 _111337 P Q c u s).
Proof. exact (TRANS (@lem4849610 _111337 P Q s c u) (@lem4849611 _111337 P Q c u s)). Qed.
Lemma lem4849613 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (s : _111337 -> Prop) : (term214 _111337 P Q s c) = (term215 _111337 P Q c s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849612 _111337 P Q c u s)). Qed.
Lemma lem4849614 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849615 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (s : _111337 -> Prop) : (term216 _111337 P Q s c) = (term217 _111337 P Q c s).
Proof. exact (MK_COMB (@lem4849614 _111337) (@lem4849613 _111337 P Q c s)). Qed.
Lemma lem4849616 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term218 _111337 P Q s) = (term219 _111337 P Q s).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849615 _111337 P Q c s)). Qed.
Lemma lem4849617 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849618 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term201 _111337 P Q s) = (term220 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849617 _111337) (@lem4849616 _111337 P Q s)). Qed.
Lemma lem4849619 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : ((term200 _111337 P Q s) = (term201 _111337 P Q s)) = ((term195 _111337 P Q s) = (term220 _111337 P Q s)).
Proof. exact (MK_COMB (@lem4849607 _111337 P Q s) (@lem4849618 _111337 P Q s)). Qed.
Lemma lem4849620 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term195 _111337 P Q s) = (term220 _111337 P Q s).
Proof. exact (EQ_MP (@lem4849619 _111337 P Q s) (@lem4849594 _111337 P Q s)). Qed.
Lemma lem4849621 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term98 _111337 P Q s) = (term220 _111337 P Q s).
Proof. exact (TRANS (@lem4849590 _111337 P Q s) (@lem4849620 _111337 P Q s)). Qed.
Lemma lem4849622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849623 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term108 _111337 P Q s) = (term221 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849622) (@lem4849621 _111337 P Q s)). Qed.
Lemma lem4849624 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4849625 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term110 _111337 P Q R s) = (term222 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849623 _111337 P Q s) (@lem4849624 _111337 R s)). Qed.
Lemma lem4849627 {A : Type'} (P : A -> Prop) (Q : Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4849628 {_111337 : Type'} (P : type72 _111337) (Q : Prop) : (term223 _111337 P Q) = (term224 _111337 P Q).
Proof. exact (@lem4849627 (type178 _111337) P Q). Qed.
Lemma lem4849629 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term225 _111337 P Q R s) = (term226 _111337 P Q R s).
Proof. exact (@lem4849628 _111337 (term219 _111337 P Q s) (R s)). Qed.
Lemma lem4849630 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (s : _111337 -> Prop) : (term227 _111337 P Q s c) = (term217 _111337 P Q c s).
Proof. exact (eq_refl (term227 _111337 P Q s c)). Qed.
Lemma lem4849631 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term228 _111337 P Q s) = (term219 _111337 P Q s).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849630 _111337 P Q c s)). Qed.
Lemma lem4849632 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849633 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term229 _111337 P Q s) = (term220 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849632 _111337) (@lem4849631 _111337 P Q s)). Qed.
Lemma lem4849634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849635 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term230 _111337 P Q s) = (term221 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849634) (@lem4849633 _111337 P Q s)). Qed.
Lemma lem4849636 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4849637 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term225 _111337 P Q R s) = (term222 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849635 _111337 P Q s) (@lem4849636 _111337 R s)). Qed.
Lemma lem4849638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849639 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term231 _111337 P Q R s) = (term232 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849638) (@lem4849637 _111337 P Q R s)). Qed.
Lemma lem4849640 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (s : _111337 -> Prop) : (term227 _111337 P Q s c) = (term217 _111337 P Q c s).
Proof. exact (eq_refl (term227 _111337 P Q s c)). Qed.
Lemma lem4849641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849642 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (s : _111337 -> Prop) : (term233 _111337 P Q s c) = (term234 _111337 P Q c s).
Proof. exact (MK_COMB (@lem4849641) (@lem4849640 _111337 P Q c s)). Qed.
Lemma lem4849643 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4849644 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term235 _111337 P Q c R s) = (term236 _111337 P Q c R s).
Proof. exact (MK_COMB (@lem4849642 _111337 P Q c s) (@lem4849643 _111337 R s)). Qed.
Lemma lem4849645 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term237 _111337 P Q R s) = (term238 _111337 P Q R s).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849644 _111337 P Q c R s)). Qed.
Lemma lem4849646 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849647 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term226 _111337 P Q R s) = (term239 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849646 _111337) (@lem4849645 _111337 P Q R s)). Qed.
Lemma lem4849648 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : ((term225 _111337 P Q R s) = (term226 _111337 P Q R s)) = ((term222 _111337 P Q R s) = (term239 _111337 P Q R s)).
Proof. exact (MK_COMB (@lem4849639 _111337 P Q R s) (@lem4849647 _111337 P Q R s)). Qed.
Lemma lem4849649 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term222 _111337 P Q R s) = (term239 _111337 P Q R s).
Proof. exact (EQ_MP (@lem4849648 _111337 P Q R s) (@lem4849629 _111337 P Q R s)). Qed.
Lemma lem4849650 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term110 _111337 P Q R s) = (term239 _111337 P Q R s).
Proof. exact (TRANS (@lem4849625 _111337 P Q R s) (@lem4849649 _111337 P Q R s)). Qed.
Lemma lem4849651 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term118 _111337 P Q R) = (term240 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849650 _111337 P Q R s)). Qed.
Lemma lem4849652 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4849653 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term119 _111337 P Q R) = (term241 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849652 _111337) (@lem4849651 _111337 P Q R)). Qed.
Lemma lem4849655 {A B : Type'} (P : type1413 A B) : (term196 A B P) = (term197 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4849656 {_111337 : Type'} (P : type578 _111337) : (term242 _111337 P) = (term243 _111337 P).
Proof. exact (@lem4849655 (_111337 -> Prop) (type178 _111337) P). Qed.
Lemma lem4849657 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term244 _111337 P Q R) = (term245 _111337 P Q R).
Proof. exact (@lem4849656 _111337 (term246 _111337 P Q R)). Qed.
Lemma lem4849658 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term247 _111337 P Q R s) = (term238 _111337 P Q R s).
Proof. exact (eq_refl (term247 _111337 P Q R s)). Qed.
Lemma lem4849659 {_111337 : Type'} (c : type178 _111337) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4849660 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) (c : type178 _111337) : (term248 _111337 P Q R s c) = (term249 _111337 P Q R s c).
Proof. exact (MK_COMB (@lem4849658 _111337 P Q R s) (@lem4849659 _111337 c)). Qed.
Lemma lem4849661 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term249 _111337 P Q R s c) = (term236 _111337 P Q c R s).
Proof. exact (eq_refl (term249 _111337 P Q R s c)). Qed.
Lemma lem4849662 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term248 _111337 P Q R s c) = (term236 _111337 P Q c R s).
Proof. exact (TRANS (@lem4849660 _111337 P Q R s c) (@lem4849661 _111337 P Q c R s)). Qed.
Lemma lem4849663 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term250 _111337 P Q R s) = (term238 _111337 P Q R s).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849662 _111337 P Q c R s)). Qed.
Lemma lem4849664 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849665 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term251 _111337 P Q R s) = (term239 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849664 _111337) (@lem4849663 _111337 P Q R s)). Qed.
Lemma lem4849666 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term252 _111337 P Q R) = (term240 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849665 _111337 P Q R s)). Qed.
Lemma lem4849667 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4849668 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term244 _111337 P Q R) = (term241 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849667 _111337) (@lem4849666 _111337 P Q R)). Qed.
Lemma lem4849669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849670 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term253 _111337 P Q R) = (term254 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849669) (@lem4849668 _111337 P Q R)). Qed.
Lemma lem4849671 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term247 _111337 P Q R s) = (term238 _111337 P Q R s).
Proof. exact (eq_refl (term247 _111337 P Q R s)). Qed.
Lemma lem4849672 {_111337 : Type'} (c : type598 _111337) (s : _111337 -> Prop) : (c s) = (c s).
Proof. exact (eq_refl (c s)). Qed.
Lemma lem4849673 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term255 _111337 P Q R c s) = (term256 _111337 P Q R c s).
Proof. exact (MK_COMB (@lem4849671 _111337 P Q R s) (@lem4849672 _111337 c s)). Qed.
Lemma lem4849674 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term256 _111337 P Q R c s) = (term257 _111337 P Q c R s).
Proof. exact (eq_refl (term256 _111337 P Q R c s)). Qed.
Lemma lem4849675 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term255 _111337 P Q R c s) = (term257 _111337 P Q c R s).
Proof. exact (TRANS (@lem4849673 _111337 P Q R c s) (@lem4849674 _111337 P Q c R s)). Qed.
Lemma lem4849676 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term258 _111337 P Q R c) = (term259 _111337 P Q c R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849675 _111337 P Q c R s)). Qed.
Lemma lem4849677 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4849678 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term260 _111337 P Q R c) = (term261 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4849677 _111337) (@lem4849676 _111337 P Q c R)). Qed.
Lemma lem4849679 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term262 _111337 P Q R) = (term263 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4849678 _111337 P Q c R)). Qed.
Lemma lem4849680 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849681 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term245 _111337 P Q R) = (term264 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849680 _111337) (@lem4849679 _111337 P Q R)). Qed.
Lemma lem4849682 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term244 _111337 P Q R) = (term245 _111337 P Q R)) = ((term241 _111337 P Q R) = (term264 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4849670 _111337 P Q R) (@lem4849681 _111337 P Q R)). Qed.
Lemma lem4849683 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term241 _111337 P Q R) = (term264 _111337 P Q R).
Proof. exact (EQ_MP (@lem4849682 _111337 P Q R) (@lem4849657 _111337 P Q R)). Qed.
Lemma lem4849684 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term119 _111337 P Q R) = (term264 _111337 P Q R).
Proof. exact (TRANS (@lem4849653 _111337 P Q R) (@lem4849683 _111337 P Q R)). Qed.
Lemma lem4849685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849686 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term150 _111337 P Q R) = (term265 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849685) (@lem4849684 _111337 P Q R)). Qed.
Lemma lem4849687 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term142 _111337 P Q R) = (term142 _111337 P Q R).
Proof. exact (eq_refl (term142 _111337 P Q R)). Qed.
Lemma lem4849688 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term152 _111337 P Q R) = (term266 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849686 _111337 P Q R) (@lem4849687 _111337 P Q R)). Qed.
Lemma lem4849690 {A : Type'} (P : A -> Prop) (Q : Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4849691 {_111337 : Type'} (P : type123 _111337) (Q : Prop) : (term269 _111337 P Q) = (term270 _111337 P Q).
Proof. exact (@lem4849690 (type598 _111337) P Q). Qed.
Lemma lem4849692 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term271 _111337 P Q R) = (term272 _111337 P Q R).
Proof. exact (@lem4849691 _111337 (term263 _111337 P Q R) (term142 _111337 P Q R)). Qed.
Lemma lem4849693 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term273 _111337 P Q R c) = (term261 _111337 P Q c R).
Proof. exact (eq_refl (term273 _111337 P Q R c)). Qed.
Lemma lem4849694 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term274 _111337 P Q R) = (term263 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4849693 _111337 P Q c R)). Qed.
Lemma lem4849695 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849696 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term275 _111337 P Q R) = (term264 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849695 _111337) (@lem4849694 _111337 P Q R)). Qed.
Lemma lem4849697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849698 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term276 _111337 P Q R) = (term265 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849697) (@lem4849696 _111337 P Q R)). Qed.
Lemma lem4849699 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term142 _111337 P Q R) = (term142 _111337 P Q R).
Proof. exact (eq_refl (term142 _111337 P Q R)). Qed.
Lemma lem4849700 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term271 _111337 P Q R) = (term266 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849698 _111337 P Q R) (@lem4849699 _111337 P Q R)). Qed.
Lemma lem4849701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849702 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term277 _111337 P Q R) = (term278 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849701) (@lem4849700 _111337 P Q R)). Qed.
Lemma lem4849703 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term273 _111337 P Q R c) = (term261 _111337 P Q c R).
Proof. exact (eq_refl (term273 _111337 P Q R c)). Qed.
Lemma lem4849704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849705 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term279 _111337 P Q R c) = (term280 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4849704) (@lem4849703 _111337 P Q c R)). Qed.
Lemma lem4849706 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term142 _111337 P Q R) = (term142 _111337 P Q R).
Proof. exact (eq_refl (term142 _111337 P Q R)). Qed.
Lemma lem4849707 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term281 _111337 c P Q R) = (term282 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849705 _111337 P Q c R) (@lem4849706 _111337 P Q R)). Qed.
Lemma lem4849708 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term283 _111337 P Q R) = (term284 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4849707 _111337 c P Q R)). Qed.
Lemma lem4849709 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849710 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term272 _111337 P Q R) = (term285 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849709 _111337) (@lem4849708 _111337 P Q R)). Qed.
Lemma lem4849711 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term271 _111337 P Q R) = (term272 _111337 P Q R)) = ((term266 _111337 P Q R) = (term285 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4849702 _111337 P Q R) (@lem4849710 _111337 P Q R)). Qed.
Lemma lem4849712 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term266 _111337 P Q R) = (term285 _111337 P Q R).
Proof. exact (EQ_MP (@lem4849711 _111337 P Q R) (@lem4849692 _111337 P Q R)). Qed.
Lemma lem4849714 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4849715 {_111337 : Type'} (P : Prop) (Q : type180 _111337) : (term288 _111337 P Q) = (term289 _111337 P Q).
Proof. exact (@lem4849714 (type686 _111337) P Q). Qed.
Lemma lem4849716 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term290 _111337 c P Q R) = (term291 _111337 c P Q R).
Proof. exact (@lem4849715 _111337 (term261 _111337 P Q c R) (term141 _111337 P Q R)). Qed.
Lemma lem4849717 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term292 _111337 P Q R t) = (term128 _111337 P Q R t).
Proof. exact (eq_refl (term292 _111337 P Q R t)). Qed.
Lemma lem4849718 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term293 _111337 P Q R) = (term141 _111337 P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849717 _111337 P Q R t)). Qed.
Lemma lem4849719 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849720 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term294 _111337 P Q R) = (term142 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849719 _111337) (@lem4849718 _111337 P Q R)). Qed.
Lemma lem4849721 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term280 _111337 P Q c R) = (term280 _111337 P Q c R).
Proof. exact (eq_refl (term280 _111337 P Q c R)). Qed.
Lemma lem4849722 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term290 _111337 c P Q R) = (term282 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849721 _111337 P Q c R) (@lem4849720 _111337 P Q R)). Qed.
Lemma lem4849723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849724 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term295 _111337 c P Q R) = (term296 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849723) (@lem4849722 _111337 c P Q R)). Qed.
Lemma lem4849725 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term292 _111337 P Q R t) = (term128 _111337 P Q R t).
Proof. exact (eq_refl (term292 _111337 P Q R t)). Qed.
Lemma lem4849726 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term280 _111337 P Q c R) = (term280 _111337 P Q c R).
Proof. exact (eq_refl (term280 _111337 P Q c R)). Qed.
Lemma lem4849727 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term297 _111337 c P Q R t) = (term298 _111337 c P Q R t).
Proof. exact (MK_COMB (@lem4849726 _111337 P Q c R) (@lem4849725 _111337 P Q R t)). Qed.
Lemma lem4849728 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term299 _111337 c P Q R) = (term300 _111337 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849727 _111337 c P Q R t)). Qed.
Lemma lem4849729 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849730 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term291 _111337 c P Q R) = (term301 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849729 _111337) (@lem4849728 _111337 c P Q R)). Qed.
Lemma lem4849731 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term290 _111337 c P Q R) = (term291 _111337 c P Q R)) = ((term282 _111337 c P Q R) = (term301 _111337 c P Q R)).
Proof. exact (MK_COMB (@lem4849724 _111337 c P Q R) (@lem4849730 _111337 c P Q R)). Qed.
Lemma lem4849732 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term282 _111337 c P Q R) = (term301 _111337 c P Q R).
Proof. exact (EQ_MP (@lem4849731 _111337 c P Q R) (@lem4849716 _111337 c P Q R)). Qed.
Lemma lem4849733 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term284 _111337 P Q R) = (term302 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4849732 _111337 c P Q R)). Qed.
Lemma lem4849734 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849735 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term285 _111337 P Q R) = (term303 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849734 _111337) (@lem4849733 _111337 P Q R)). Qed.
Lemma lem4849736 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term266 _111337 P Q R) = (term303 _111337 P Q R).
Proof. exact (TRANS (@lem4849712 _111337 P Q R) (@lem4849735 _111337 P Q R)). Qed.
Lemma lem4849737 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term152 _111337 P Q R) = (term303 _111337 P Q R).
Proof. exact (TRANS (@lem4849688 _111337 P Q R) (@lem4849736 _111337 P Q R)). Qed.
Lemma lem4849738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849739 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term154 _111337 P Q R) = (term304 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849738) (@lem4849737 _111337 P Q R)). Qed.
Lemma lem4849741 {A : Type'} (P : A -> Prop) (Q : Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4849742 {_111337 : Type'} (P : type180 _111337) (Q : Prop) : (term305 _111337 P Q) = (term306 _111337 P Q).
Proof. exact (@lem4849741 (type686 _111337) P Q). Qed.
Lemma lem4849743 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term307 _111337 P Q R s) = (term308 _111337 P Q R s).
Proof. exact (@lem4849742 _111337 (term99 _111337 P Q s) (term101 _111337 R s)). Qed.
Lemma lem4849744 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term309 _111337 P Q s u) = (term89 _111337 P Q u s).
Proof. exact (eq_refl (term309 _111337 P Q s u)). Qed.
Lemma lem4849745 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term310 _111337 P Q s) = (term99 _111337 P Q s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849744 _111337 P Q u s)). Qed.
Lemma lem4849746 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849747 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term311 _111337 P Q s) = (term100 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849746 _111337) (@lem4849745 _111337 P Q s)). Qed.
Lemma lem4849748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849749 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (s : _111337 -> Prop) : (term312 _111337 P Q s) = (term103 _111337 P Q s).
Proof. exact (MK_COMB (@lem4849748) (@lem4849747 _111337 P Q s)). Qed.
Lemma lem4849750 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term101 _111337 R s) = (term101 _111337 R s).
Proof. exact (eq_refl (term101 _111337 R s)). Qed.
Lemma lem4849751 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term307 _111337 P Q R s) = (term105 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849749 _111337 P Q s) (@lem4849750 _111337 R s)). Qed.
Lemma lem4849752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849753 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term313 _111337 P Q R s) = (term314 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849752) (@lem4849751 _111337 P Q R s)). Qed.
Lemma lem4849754 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term309 _111337 P Q s u) = (term89 _111337 P Q u s).
Proof. exact (eq_refl (term309 _111337 P Q s u)). Qed.
Lemma lem4849755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849756 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term315 _111337 P Q s u) = (term316 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4849755) (@lem4849754 _111337 P Q u s)). Qed.
Lemma lem4849757 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term101 _111337 R s) = (term101 _111337 R s).
Proof. exact (eq_refl (term101 _111337 R s)). Qed.
Lemma lem4849758 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term317 _111337 P Q u R s) = (term318 _111337 P Q u R s).
Proof. exact (MK_COMB (@lem4849756 _111337 P Q u s) (@lem4849757 _111337 R s)). Qed.
Lemma lem4849759 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term319 _111337 P Q R s) = (term320 _111337 P Q R s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849758 _111337 P Q u R s)). Qed.
Lemma lem4849760 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849761 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term308 _111337 P Q R s) = (term321 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849760 _111337) (@lem4849759 _111337 P Q R s)). Qed.
Lemma lem4849762 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : ((term307 _111337 P Q R s) = (term308 _111337 P Q R s)) = ((term105 _111337 P Q R s) = (term321 _111337 P Q R s)).
Proof. exact (MK_COMB (@lem4849753 _111337 P Q R s) (@lem4849761 _111337 P Q R s)). Qed.
Lemma lem4849763 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term105 _111337 P Q R s) = (term321 _111337 P Q R s).
Proof. exact (EQ_MP (@lem4849762 _111337 P Q R s) (@lem4849743 _111337 P Q R s)). Qed.
Lemma lem4849764 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term116 _111337 P Q R) = (term322 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849763 _111337 P Q R s)). Qed.
Lemma lem4849765 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849766 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term117 _111337 P Q R) = (term323 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849765 _111337) (@lem4849764 _111337 P Q R)). Qed.
Lemma lem4849767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849768 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term146 _111337 P Q R) = (term324 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849767) (@lem4849766 _111337 P Q R)). Qed.
Lemma lem4849770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4849771 {_111337 : Type'} (P : Prop) (Q : type686 _111337) : (term179 _111337 P Q) = (term180 _111337 P Q).
Proof. exact (@lem4849770 (_111337 -> Prop) P Q). Qed.
Lemma lem4849772 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term325 _111337 P t Q) = (term326 _111337 P t Q).
Proof. exact (@lem4849771 _111337 (term183 _111337 P t) (term73 _111337 t Q)). Qed.
Lemma lem4849773 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term163 _111337 t Q c) = (term64 _111337 t Q c).
Proof. exact (eq_refl (term163 _111337 t Q c)). Qed.
Lemma lem4849774 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term164 _111337 t Q) = (term73 _111337 t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849773 _111337 t Q c)). Qed.
Lemma lem4849775 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849776 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term165 _111337 t Q) = (term74 _111337 t Q).
Proof. exact (MK_COMB (@lem4849775 _111337) (@lem4849774 _111337 t Q)). Qed.
Lemma lem4849777 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term85 _111337 P t) = (term85 _111337 P t).
Proof. exact (eq_refl (term85 _111337 P t)). Qed.
Lemma lem4849778 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term325 _111337 P t Q) = (term121 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849777 _111337 P t) (@lem4849776 _111337 t Q)). Qed.
Lemma lem4849779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849780 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term327 _111337 P t Q) = (term328 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849779) (@lem4849778 _111337 P t Q)). Qed.
Lemma lem4849781 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term163 _111337 t Q c) = (term64 _111337 t Q c).
Proof. exact (eq_refl (term163 _111337 t Q c)). Qed.
Lemma lem4849782 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term85 _111337 P t) = (term85 _111337 P t).
Proof. exact (eq_refl (term85 _111337 P t)). Qed.
Lemma lem4849783 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term329 _111337 P t Q c) = (term330 _111337 P t Q c).
Proof. exact (MK_COMB (@lem4849782 _111337 P t) (@lem4849781 _111337 t Q c)). Qed.
Lemma lem4849784 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term331 _111337 P t Q) = (term332 _111337 P t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849783 _111337 P t Q c)). Qed.
Lemma lem4849785 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849786 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term326 _111337 P t Q) = (term333 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849785 _111337) (@lem4849784 _111337 P t Q)). Qed.
Lemma lem4849787 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : ((term325 _111337 P t Q) = (term326 _111337 P t Q)) = ((term121 _111337 P t Q) = (term333 _111337 P t Q)).
Proof. exact (MK_COMB (@lem4849780 _111337 P t Q) (@lem4849786 _111337 P t Q)). Qed.
Lemma lem4849788 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term121 _111337 P t Q) = (term333 _111337 P t Q).
Proof. exact (EQ_MP (@lem4849787 _111337 P t Q) (@lem4849772 _111337 P t Q)). Qed.
Lemma lem4849789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849790 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term131 _111337 P t Q) = (term334 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849789) (@lem4849788 _111337 P t Q)). Qed.
Lemma lem4849791 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term50 _111337 R t) = (term50 _111337 R t).
Proof. exact (eq_refl (term50 _111337 R t)). Qed.
Lemma lem4849792 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term133 _111337 P Q R t) = (term335 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849790 _111337 P t Q) (@lem4849791 _111337 R t)). Qed.
Lemma lem4849794 {A : Type'} (P : A -> Prop) (Q : Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4849795 {_111337 : Type'} (P : type686 _111337) (Q : Prop) : (term159 _111337 P Q) = (term160 _111337 P Q).
Proof. exact (@lem4849794 (_111337 -> Prop) P Q). Qed.
Lemma lem4849796 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term336 _111337 P Q R t) = (term337 _111337 P Q R t).
Proof. exact (@lem4849795 _111337 (term332 _111337 P t Q) (term50 _111337 R t)). Qed.
Lemma lem4849797 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term338 _111337 P t Q c) = (term330 _111337 P t Q c).
Proof. exact (eq_refl (term338 _111337 P t Q c)). Qed.
Lemma lem4849798 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term339 _111337 P t Q) = (term332 _111337 P t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849797 _111337 P t Q c)). Qed.
Lemma lem4849799 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849800 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term340 _111337 P t Q) = (term333 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849799 _111337) (@lem4849798 _111337 P t Q)). Qed.
Lemma lem4849801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849802 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term341 _111337 P t Q) = (term334 _111337 P t Q).
Proof. exact (MK_COMB (@lem4849801) (@lem4849800 _111337 P t Q)). Qed.
Lemma lem4849803 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term50 _111337 R t) = (term50 _111337 R t).
Proof. exact (eq_refl (term50 _111337 R t)). Qed.
Lemma lem4849804 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term336 _111337 P Q R t) = (term335 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849802 _111337 P t Q) (@lem4849803 _111337 R t)). Qed.
Lemma lem4849805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849806 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term342 _111337 P Q R t) = (term343 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849805) (@lem4849804 _111337 P Q R t)). Qed.
Lemma lem4849807 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term338 _111337 P t Q c) = (term330 _111337 P t Q c).
Proof. exact (eq_refl (term338 _111337 P t Q c)). Qed.
Lemma lem4849808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849809 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term344 _111337 P t Q c) = (term345 _111337 P t Q c).
Proof. exact (MK_COMB (@lem4849808) (@lem4849807 _111337 P t Q c)). Qed.
Lemma lem4849810 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term50 _111337 R t) = (term50 _111337 R t).
Proof. exact (eq_refl (term50 _111337 R t)). Qed.
Lemma lem4849811 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : _111337 -> Prop) (R : type686 _111337) (t : type686 _111337) : (term346 _111337 P Q c R t) = (term347 _111337 P Q c R t).
Proof. exact (MK_COMB (@lem4849809 _111337 P t Q c) (@lem4849810 _111337 R t)). Qed.
Lemma lem4849812 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term348 _111337 P Q R t) = (term349 _111337 P Q R t).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849811 _111337 P Q c R t)). Qed.
Lemma lem4849813 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849814 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term337 _111337 P Q R t) = (term350 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849813 _111337) (@lem4849812 _111337 P Q R t)). Qed.
Lemma lem4849815 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : ((term336 _111337 P Q R t) = (term337 _111337 P Q R t)) = ((term335 _111337 P Q R t) = (term350 _111337 P Q R t)).
Proof. exact (MK_COMB (@lem4849806 _111337 P Q R t) (@lem4849814 _111337 P Q R t)). Qed.
Lemma lem4849816 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term335 _111337 P Q R t) = (term350 _111337 P Q R t).
Proof. exact (EQ_MP (@lem4849815 _111337 P Q R t) (@lem4849796 _111337 P Q R t)). Qed.
Lemma lem4849817 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term133 _111337 P Q R t) = (term350 _111337 P Q R t).
Proof. exact (TRANS (@lem4849792 _111337 P Q R t) (@lem4849816 _111337 P Q R t)). Qed.
Lemma lem4849818 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term143 _111337 P Q R) = (term351 _111337 P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849817 _111337 P Q R t)). Qed.
Lemma lem4849819 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849820 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term144 _111337 P Q R) = (term352 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849819 _111337) (@lem4849818 _111337 P Q R)). Qed.
Lemma lem4849822 {A B : Type'} (P : type1413 A B) : (term196 A B P) = (term197 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4849823 {_111337 : Type'} (P : type174 _111337) : (term198 _111337 P) = (term199 _111337 P).
Proof. exact (@lem4849822 (type686 _111337) (_111337 -> Prop) P). Qed.
Lemma lem4849824 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term353 _111337 P Q R) = (term354 _111337 P Q R).
Proof. exact (@lem4849823 _111337 (term355 _111337 P Q R)). Qed.
Lemma lem4849825 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term356 _111337 P Q R t) = (term349 _111337 P Q R t).
Proof. exact (eq_refl (term356 _111337 P Q R t)). Qed.
Lemma lem4849826 {_111337 : Type'} (c : _111337 -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4849827 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (c : _111337 -> Prop) : (term357 _111337 P Q R t c) = (term358 _111337 P Q R t c).
Proof. exact (MK_COMB (@lem4849825 _111337 P Q R t) (@lem4849826 _111337 c)). Qed.
Lemma lem4849828 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : _111337 -> Prop) (R : type686 _111337) (t : type686 _111337) : (term358 _111337 P Q R t c) = (term347 _111337 P Q c R t).
Proof. exact (eq_refl (term358 _111337 P Q R t c)). Qed.
Lemma lem4849829 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : _111337 -> Prop) (R : type686 _111337) (t : type686 _111337) : (term357 _111337 P Q R t c) = (term347 _111337 P Q c R t).
Proof. exact (TRANS (@lem4849827 _111337 P Q R t c) (@lem4849828 _111337 P Q c R t)). Qed.
Lemma lem4849830 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term359 _111337 P Q R t) = (term349 _111337 P Q R t).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4849829 _111337 P Q c R t)). Qed.
Lemma lem4849831 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849832 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term360 _111337 P Q R t) = (term350 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4849831 _111337) (@lem4849830 _111337 P Q R t)). Qed.
Lemma lem4849833 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term361 _111337 P Q R) = (term351 _111337 P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849832 _111337 P Q R t)). Qed.
Lemma lem4849834 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849835 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term353 _111337 P Q R) = (term352 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849834 _111337) (@lem4849833 _111337 P Q R)). Qed.
Lemma lem4849836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849837 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term362 _111337 P Q R) = (term363 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849836) (@lem4849835 _111337 P Q R)). Qed.
Lemma lem4849838 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term356 _111337 P Q R t) = (term349 _111337 P Q R t).
Proof. exact (eq_refl (term356 _111337 P Q R t)). Qed.
Lemma lem4849839 {_111337 : Type'} (c : type178 _111337) (t : type686 _111337) : (c t) = (c t).
Proof. exact (eq_refl (c t)). Qed.
Lemma lem4849840 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (c : type178 _111337) (t : type686 _111337) : (term364 _111337 P Q R c t) = (term365 _111337 P Q R c t).
Proof. exact (MK_COMB (@lem4849838 _111337 P Q R t) (@lem4849839 _111337 c t)). Qed.
Lemma lem4849841 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) (t : type686 _111337) : (term365 _111337 P Q R c t) = (term366 _111337 P Q c R t).
Proof. exact (eq_refl (term365 _111337 P Q R c t)). Qed.
Lemma lem4849842 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) (t : type686 _111337) : (term364 _111337 P Q R c t) = (term366 _111337 P Q c R t).
Proof. exact (TRANS (@lem4849840 _111337 P Q R c t) (@lem4849841 _111337 P Q c R t)). Qed.
Lemma lem4849843 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term367 _111337 P Q R c) = (term368 _111337 P Q c R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849842 _111337 P Q c R t)). Qed.
Lemma lem4849844 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849845 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term369 _111337 P Q R c) = (term370 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4849844 _111337) (@lem4849843 _111337 P Q c R)). Qed.
Lemma lem4849846 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term371 _111337 P Q R) = (term372 _111337 P Q R).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849845 _111337 P Q c R)). Qed.
Lemma lem4849847 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849848 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term354 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849847 _111337) (@lem4849846 _111337 P Q R)). Qed.
Lemma lem4849849 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term353 _111337 P Q R) = (term354 _111337 P Q R)) = ((term352 _111337 P Q R) = (term373 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4849837 _111337 P Q R) (@lem4849848 _111337 P Q R)). Qed.
Lemma lem4849850 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term352 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (EQ_MP (@lem4849849 _111337 P Q R) (@lem4849824 _111337 P Q R)). Qed.
Lemma lem4849851 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term144 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (TRANS (@lem4849820 _111337 P Q R) (@lem4849850 _111337 P Q R)). Qed.
Lemma lem4849852 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term148 _111337 P Q R) = (term374 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849768 _111337 P Q R) (@lem4849851 _111337 P Q R)). Qed.
Lemma lem4849854 {A : Type'} (P : A -> Prop) (Q : Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4849855 {_111337 : Type'} (P : type686 _111337) (Q : Prop) : (term375 _111337 P Q) = (term376 _111337 P Q).
Proof. exact (@lem4849854 (_111337 -> Prop) P Q). Qed.
Lemma lem4849856 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term377 _111337 P Q R) = (term378 _111337 P Q R).
Proof. exact (@lem4849855 _111337 (term322 _111337 P Q R) (term373 _111337 P Q R)). Qed.
Lemma lem4849857 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term379 _111337 P Q R s) = (term321 _111337 P Q R s).
Proof. exact (eq_refl (term379 _111337 P Q R s)). Qed.
Lemma lem4849858 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term380 _111337 P Q R) = (term322 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849857 _111337 P Q R s)). Qed.
Lemma lem4849859 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849860 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term381 _111337 P Q R) = (term323 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849859 _111337) (@lem4849858 _111337 P Q R)). Qed.
Lemma lem4849861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849862 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term382 _111337 P Q R) = (term324 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849861) (@lem4849860 _111337 P Q R)). Qed.
Lemma lem4849863 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term373 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (eq_refl (term373 _111337 P Q R)). Qed.
Lemma lem4849864 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term377 _111337 P Q R) = (term374 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849862 _111337 P Q R) (@lem4849863 _111337 P Q R)). Qed.
Lemma lem4849865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849866 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term383 _111337 P Q R) = (term384 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849865) (@lem4849864 _111337 P Q R)). Qed.
Lemma lem4849867 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term379 _111337 P Q R s) = (term321 _111337 P Q R s).
Proof. exact (eq_refl (term379 _111337 P Q R s)). Qed.
Lemma lem4849868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849869 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term385 _111337 P Q R s) = (term386 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849868) (@lem4849867 _111337 P Q R s)). Qed.
Lemma lem4849870 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term373 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (eq_refl (term373 _111337 P Q R)). Qed.
Lemma lem4849871 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term387 _111337 s P Q R) = (term388 _111337 s P Q R).
Proof. exact (MK_COMB (@lem4849869 _111337 P Q R s) (@lem4849870 _111337 P Q R)). Qed.
Lemma lem4849872 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term389 _111337 P Q R) = (term390 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849871 _111337 s P Q R)). Qed.
Lemma lem4849873 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849874 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term378 _111337 P Q R) = (term391 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849873 _111337) (@lem4849872 _111337 P Q R)). Qed.
Lemma lem4849875 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term377 _111337 P Q R) = (term378 _111337 P Q R)) = ((term374 _111337 P Q R) = (term391 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4849866 _111337 P Q R) (@lem4849874 _111337 P Q R)). Qed.
Lemma lem4849876 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term374 _111337 P Q R) = (term391 _111337 P Q R).
Proof. exact (EQ_MP (@lem4849875 _111337 P Q R) (@lem4849856 _111337 P Q R)). Qed.
Lemma lem4849878 {A : Type'} (P : A -> Prop) (Q : Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4849879 {_111337 : Type'} (P : type180 _111337) (Q : Prop) : (term305 _111337 P Q) = (term306 _111337 P Q).
Proof. exact (@lem4849878 (type686 _111337) P Q). Qed.
Lemma lem4849880 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term392 _111337 s P Q R) = (term393 _111337 s P Q R).
Proof. exact (@lem4849879 _111337 (term320 _111337 P Q R s) (term373 _111337 P Q R)). Qed.
Lemma lem4849881 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term394 _111337 P Q R s u) = (term318 _111337 P Q u R s).
Proof. exact (eq_refl (term394 _111337 P Q R s u)). Qed.
Lemma lem4849882 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term395 _111337 P Q R s) = (term320 _111337 P Q R s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849881 _111337 P Q u R s)). Qed.
Lemma lem4849883 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849884 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term396 _111337 P Q R s) = (term321 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849883 _111337) (@lem4849882 _111337 P Q R s)). Qed.
Lemma lem4849885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849886 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term397 _111337 P Q R s) = (term386 _111337 P Q R s).
Proof. exact (MK_COMB (@lem4849885) (@lem4849884 _111337 P Q R s)). Qed.
Lemma lem4849887 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term373 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (eq_refl (term373 _111337 P Q R)). Qed.
Lemma lem4849888 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term392 _111337 s P Q R) = (term388 _111337 s P Q R).
Proof. exact (MK_COMB (@lem4849886 _111337 P Q R s) (@lem4849887 _111337 P Q R)). Qed.
Lemma lem4849889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849890 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term398 _111337 s P Q R) = (term399 _111337 s P Q R).
Proof. exact (MK_COMB (@lem4849889) (@lem4849888 _111337 s P Q R)). Qed.
Lemma lem4849891 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term394 _111337 P Q R s u) = (term318 _111337 P Q u R s).
Proof. exact (eq_refl (term394 _111337 P Q R s u)). Qed.
Lemma lem4849892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4849893 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term400 _111337 P Q R s u) = (term401 _111337 P Q u R s).
Proof. exact (MK_COMB (@lem4849892) (@lem4849891 _111337 P Q u R s)). Qed.
Lemma lem4849894 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term373 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (eq_refl (term373 _111337 P Q R)). Qed.
Lemma lem4849895 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term402 _111337 s u P Q R) = (term403 _111337 u s P Q R).
Proof. exact (MK_COMB (@lem4849893 _111337 P Q u R s) (@lem4849894 _111337 P Q R)). Qed.
Lemma lem4849896 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term404 _111337 s P Q R) = (term405 _111337 s P Q R).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849895 _111337 u s P Q R)). Qed.
Lemma lem4849897 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849898 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term393 _111337 s P Q R) = (term406 _111337 s P Q R).
Proof. exact (MK_COMB (@lem4849897 _111337) (@lem4849896 _111337 s P Q R)). Qed.
Lemma lem4849899 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term392 _111337 s P Q R) = (term393 _111337 s P Q R)) = ((term388 _111337 s P Q R) = (term406 _111337 s P Q R)).
Proof. exact (MK_COMB (@lem4849890 _111337 s P Q R) (@lem4849898 _111337 s P Q R)). Qed.
Lemma lem4849900 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term388 _111337 s P Q R) = (term406 _111337 s P Q R).
Proof. exact (EQ_MP (@lem4849899 _111337 s P Q R) (@lem4849880 _111337 s P Q R)). Qed.
Lemma lem4849902 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4849903 {_111337 : Type'} (P : Prop) (Q : type72 _111337) : (term407 _111337 P Q) = (term408 _111337 P Q).
Proof. exact (@lem4849902 (type178 _111337) P Q). Qed.
Lemma lem4849904 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term409 _111337 u s P Q R) = (term410 _111337 u s P Q R).
Proof. exact (@lem4849903 _111337 (term318 _111337 P Q u R s) (term372 _111337 P Q R)). Qed.
Lemma lem4849905 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term411 _111337 P Q R c) = (term370 _111337 P Q c R).
Proof. exact (eq_refl (term411 _111337 P Q R c)). Qed.
Lemma lem4849906 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term412 _111337 P Q R) = (term372 _111337 P Q R).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849905 _111337 P Q c R)). Qed.
Lemma lem4849907 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849908 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term413 _111337 P Q R) = (term373 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849907 _111337) (@lem4849906 _111337 P Q R)). Qed.
Lemma lem4849909 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term401 _111337 P Q u R s) = (term401 _111337 P Q u R s).
Proof. exact (eq_refl (term401 _111337 P Q u R s)). Qed.
Lemma lem4849910 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term409 _111337 u s P Q R) = (term403 _111337 u s P Q R).
Proof. exact (MK_COMB (@lem4849909 _111337 P Q u R s) (@lem4849908 _111337 P Q R)). Qed.
Lemma lem4849911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849912 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term414 _111337 u s P Q R) = (term415 _111337 u s P Q R).
Proof. exact (MK_COMB (@lem4849911) (@lem4849910 _111337 u s P Q R)). Qed.
Lemma lem4849913 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term411 _111337 P Q R c) = (term370 _111337 P Q c R).
Proof. exact (eq_refl (term411 _111337 P Q R c)). Qed.
Lemma lem4849914 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term401 _111337 P Q u R s) = (term401 _111337 P Q u R s).
Proof. exact (eq_refl (term401 _111337 P Q u R s)). Qed.
Lemma lem4849915 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term416 _111337 u s P Q R c) = (term417 _111337 u s P Q c R).
Proof. exact (MK_COMB (@lem4849914 _111337 P Q u R s) (@lem4849913 _111337 P Q c R)). Qed.
Lemma lem4849916 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term418 _111337 u s P Q R) = (term419 _111337 u s P Q R).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4849915 _111337 u s P Q c R)). Qed.
Lemma lem4849917 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849918 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term410 _111337 u s P Q R) = (term420 _111337 u s P Q R).
Proof. exact (MK_COMB (@lem4849917 _111337) (@lem4849916 _111337 u s P Q R)). Qed.
Lemma lem4849919 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term409 _111337 u s P Q R) = (term410 _111337 u s P Q R)) = ((term403 _111337 u s P Q R) = (term420 _111337 u s P Q R)).
Proof. exact (MK_COMB (@lem4849912 _111337 u s P Q R) (@lem4849918 _111337 u s P Q R)). Qed.
Lemma lem4849920 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term403 _111337 u s P Q R) = (term420 _111337 u s P Q R).
Proof. exact (EQ_MP (@lem4849919 _111337 u s P Q R) (@lem4849904 _111337 u s P Q R)). Qed.
Lemma lem4849921 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term405 _111337 s P Q R) = (term421 _111337 s P Q R).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4849920 _111337 u s P Q R)). Qed.
Lemma lem4849922 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849923 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term406 _111337 s P Q R) = (term422 _111337 s P Q R).
Proof. exact (MK_COMB (@lem4849922 _111337) (@lem4849921 _111337 s P Q R)). Qed.
Lemma lem4849924 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term388 _111337 s P Q R) = (term422 _111337 s P Q R).
Proof. exact (TRANS (@lem4849900 _111337 s P Q R) (@lem4849923 _111337 s P Q R)). Qed.
Lemma lem4849925 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term390 _111337 P Q R) = (term423 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849924 _111337 s P Q R)). Qed.
Lemma lem4849926 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849927 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term391 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849926 _111337) (@lem4849925 _111337 P Q R)). Qed.
Lemma lem4849928 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term374 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (TRANS (@lem4849876 _111337 P Q R) (@lem4849927 _111337 P Q R)). Qed.
Lemma lem4849929 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term148 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (TRANS (@lem4849852 _111337 P Q R) (@lem4849928 _111337 P Q R)). Qed.
Lemma lem4849930 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term156 _111337 P Q R) = (term425 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849739 _111337 P Q R) (@lem4849929 _111337 P Q R)). Qed.
Lemma lem4849934 {A : Type'} (P : A -> Prop) (Q : Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4849935 {_111337 : Type'} (P : type123 _111337) (Q : Prop) : (term426 _111337 P Q) = (term427 _111337 P Q).
Proof. exact (@lem4849934 (type598 _111337) P Q). Qed.
Lemma lem4849936 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term428 _111337 P Q R) = (term429 _111337 P Q R).
Proof. exact (@lem4849935 _111337 (term302 _111337 P Q R) (term424 _111337 P Q R)). Qed.
Lemma lem4849937 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term430 _111337 P Q R c) = (term301 _111337 c P Q R).
Proof. exact (eq_refl (term430 _111337 P Q R c)). Qed.
Lemma lem4849938 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term431 _111337 P Q R) = (term302 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4849937 _111337 c P Q R)). Qed.
Lemma lem4849939 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849940 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term432 _111337 P Q R) = (term303 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849939 _111337) (@lem4849938 _111337 P Q R)). Qed.
Lemma lem4849941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849942 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term433 _111337 P Q R) = (term304 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849941) (@lem4849940 _111337 P Q R)). Qed.
Lemma lem4849943 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term424 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (eq_refl (term424 _111337 P Q R)). Qed.
Lemma lem4849944 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term428 _111337 P Q R) = (term425 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849942 _111337 P Q R) (@lem4849943 _111337 P Q R)). Qed.
Lemma lem4849945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849946 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term434 _111337 P Q R) = (term435 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849945) (@lem4849944 _111337 P Q R)). Qed.
Lemma lem4849947 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term430 _111337 P Q R c) = (term301 _111337 c P Q R).
Proof. exact (eq_refl (term430 _111337 P Q R c)). Qed.
Lemma lem4849948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849949 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term436 _111337 P Q R c) = (term437 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849948) (@lem4849947 _111337 c P Q R)). Qed.
Lemma lem4849950 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term424 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (eq_refl (term424 _111337 P Q R)). Qed.
Lemma lem4849951 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term438 _111337 c P Q R) = (term439 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849949 _111337 c P Q R) (@lem4849950 _111337 P Q R)). Qed.
Lemma lem4849952 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term440 _111337 P Q R) = (term441 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4849951 _111337 c P Q R)). Qed.
Lemma lem4849953 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4849954 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term429 _111337 P Q R) = (term442 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849953 _111337) (@lem4849952 _111337 P Q R)). Qed.
Lemma lem4849955 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term428 _111337 P Q R) = (term429 _111337 P Q R)) = ((term425 _111337 P Q R) = (term442 _111337 P Q R)).
Proof. exact (MK_COMB (@lem4849946 _111337 P Q R) (@lem4849954 _111337 P Q R)). Qed.
Lemma lem4849956 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term425 _111337 P Q R) = (term442 _111337 P Q R).
Proof. exact (EQ_MP (@lem4849955 _111337 P Q R) (@lem4849936 _111337 P Q R)). Qed.
Lemma lem4849960 {A : Type'} (P : A -> Prop) (Q : Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4849961 {_111337 : Type'} (P : type180 _111337) (Q : Prop) : (term443 _111337 P Q) = (term444 _111337 P Q).
Proof. exact (@lem4849960 (type686 _111337) P Q). Qed.
Lemma lem4849962 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term445 _111337 c P Q R) = (term446 _111337 c P Q R).
Proof. exact (@lem4849961 _111337 (term300 _111337 c P Q R) (term424 _111337 P Q R)). Qed.
Lemma lem4849963 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term447 _111337 c P Q R t) = (term298 _111337 c P Q R t).
Proof. exact (eq_refl (term447 _111337 c P Q R t)). Qed.
Lemma lem4849964 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term448 _111337 c P Q R) = (term300 _111337 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849963 _111337 c P Q R t)). Qed.
Lemma lem4849965 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849966 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term449 _111337 c P Q R) = (term301 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849965 _111337) (@lem4849964 _111337 c P Q R)). Qed.
Lemma lem4849967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849968 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term450 _111337 c P Q R) = (term437 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849967) (@lem4849966 _111337 c P Q R)). Qed.
Lemma lem4849969 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term424 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (eq_refl (term424 _111337 P Q R)). Qed.
Lemma lem4849970 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term445 _111337 c P Q R) = (term439 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849968 _111337 c P Q R) (@lem4849969 _111337 P Q R)). Qed.
Lemma lem4849971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849972 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term451 _111337 c P Q R) = (term452 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849971) (@lem4849970 _111337 c P Q R)). Qed.
Lemma lem4849973 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term447 _111337 c P Q R t) = (term298 _111337 c P Q R t).
Proof. exact (eq_refl (term447 _111337 c P Q R t)). Qed.
Lemma lem4849974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4849975 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term453 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (MK_COMB (@lem4849974) (@lem4849973 _111337 c P Q R t)). Qed.
Lemma lem4849976 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term424 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (eq_refl (term424 _111337 P Q R)). Qed.
Lemma lem4849977 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term455 _111337 c t P Q R) = (term456 _111337 c t P Q R).
Proof. exact (MK_COMB (@lem4849975 _111337 c P Q R t) (@lem4849976 _111337 P Q R)). Qed.
Lemma lem4849978 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term457 _111337 c P Q R) = (term458 _111337 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4849977 _111337 c t P Q R)). Qed.
Lemma lem4849979 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4849980 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term446 _111337 c P Q R) = (term459 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4849979 _111337) (@lem4849978 _111337 c P Q R)). Qed.
Lemma lem4849981 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term445 _111337 c P Q R) = (term446 _111337 c P Q R)) = ((term439 _111337 c P Q R) = (term459 _111337 c P Q R)).
Proof. exact (MK_COMB (@lem4849972 _111337 c P Q R) (@lem4849980 _111337 c P Q R)). Qed.
Lemma lem4849982 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term439 _111337 c P Q R) = (term459 _111337 c P Q R).
Proof. exact (EQ_MP (@lem4849981 _111337 c P Q R) (@lem4849962 _111337 c P Q R)). Qed.
Lemma lem4849984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4849985 {_111337 : Type'} (P : Prop) (Q : type686 _111337) : (term179 _111337 P Q) = (term180 _111337 P Q).
Proof. exact (@lem4849984 (_111337 -> Prop) P Q). Qed.
Lemma lem4849986 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term460 _111337 c t P Q R) = (term461 _111337 c t P Q R).
Proof. exact (@lem4849985 _111337 (term298 _111337 c P Q R t) (term423 _111337 P Q R)). Qed.
Lemma lem4849987 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term462 _111337 P Q R s) = (term422 _111337 s P Q R).
Proof. exact (eq_refl (term462 _111337 P Q R s)). Qed.
Lemma lem4849988 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term463 _111337 P Q R) = (term423 _111337 P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849987 _111337 s P Q R)). Qed.
Lemma lem4849989 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4849990 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term464 _111337 P Q R) = (term424 _111337 P Q R).
Proof. exact (MK_COMB (@lem4849989 _111337) (@lem4849988 _111337 P Q R)). Qed.
Lemma lem4849991 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (eq_refl (term454 _111337 c P Q R t)). Qed.
Lemma lem4849992 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term460 _111337 c t P Q R) = (term456 _111337 c t P Q R).
Proof. exact (MK_COMB (@lem4849991 _111337 c P Q R t) (@lem4849990 _111337 P Q R)). Qed.
Lemma lem4849993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4849994 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term465 _111337 c t P Q R) = (term466 _111337 c t P Q R).
Proof. exact (MK_COMB (@lem4849993) (@lem4849992 _111337 c t P Q R)). Qed.
Lemma lem4849995 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term462 _111337 P Q R s) = (term422 _111337 s P Q R).
Proof. exact (eq_refl (term462 _111337 P Q R s)). Qed.
Lemma lem4849996 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (eq_refl (term454 _111337 c P Q R t)). Qed.
Lemma lem4849997 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term467 _111337 c t P Q R s) = (term468 _111337 c t s P Q R).
Proof. exact (MK_COMB (@lem4849996 _111337 c P Q R t) (@lem4849995 _111337 s P Q R)). Qed.
Lemma lem4849998 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term469 _111337 c t P Q R) = (term470 _111337 c t P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4849997 _111337 c t s P Q R)). Qed.
Lemma lem4849999 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4850000 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term461 _111337 c t P Q R) = (term471 _111337 c t P Q R).
Proof. exact (MK_COMB (@lem4849999 _111337) (@lem4849998 _111337 c t P Q R)). Qed.
Lemma lem4850001 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term460 _111337 c t P Q R) = (term461 _111337 c t P Q R)) = ((term456 _111337 c t P Q R) = (term471 _111337 c t P Q R)).
Proof. exact (MK_COMB (@lem4849994 _111337 c t P Q R) (@lem4850000 _111337 c t P Q R)). Qed.
Lemma lem4850002 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term456 _111337 c t P Q R) = (term471 _111337 c t P Q R).
Proof. exact (EQ_MP (@lem4850001 _111337 c t P Q R) (@lem4849986 _111337 c t P Q R)). Qed.
Lemma lem4850004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4850005 {_111337 : Type'} (P : Prop) (Q : type180 _111337) : (term472 _111337 P Q) = (term473 _111337 P Q).
Proof. exact (@lem4850004 (type686 _111337) P Q). Qed.
Lemma lem4850006 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term474 _111337 c t s P Q R) = (term475 _111337 c t s P Q R).
Proof. exact (@lem4850005 _111337 (term298 _111337 c P Q R t) (term421 _111337 s P Q R)). Qed.
Lemma lem4850007 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term476 _111337 s P Q R u) = (term420 _111337 u s P Q R).
Proof. exact (eq_refl (term476 _111337 s P Q R u)). Qed.
Lemma lem4850008 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term477 _111337 s P Q R) = (term421 _111337 s P Q R).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850007 _111337 u s P Q R)). Qed.
Lemma lem4850009 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850010 {_111337 : Type'} (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term478 _111337 s P Q R) = (term422 _111337 s P Q R).
Proof. exact (MK_COMB (@lem4850009 _111337) (@lem4850008 _111337 s P Q R)). Qed.
Lemma lem4850011 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (eq_refl (term454 _111337 c P Q R t)). Qed.
Lemma lem4850012 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term474 _111337 c t s P Q R) = (term468 _111337 c t s P Q R).
Proof. exact (MK_COMB (@lem4850011 _111337 c P Q R t) (@lem4850010 _111337 s P Q R)). Qed.
Lemma lem4850013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4850014 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term479 _111337 c t s P Q R) = (term480 _111337 c t s P Q R).
Proof. exact (MK_COMB (@lem4850013) (@lem4850012 _111337 c t s P Q R)). Qed.
Lemma lem4850015 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term476 _111337 s P Q R u) = (term420 _111337 u s P Q R).
Proof. exact (eq_refl (term476 _111337 s P Q R u)). Qed.
Lemma lem4850016 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (eq_refl (term454 _111337 c P Q R t)). Qed.
Lemma lem4850017 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term481 _111337 c t s P Q R u) = (term482 _111337 c t u s P Q R).
Proof. exact (MK_COMB (@lem4850016 _111337 c P Q R t) (@lem4850015 _111337 u s P Q R)). Qed.
Lemma lem4850018 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term483 _111337 c t s P Q R) = (term484 _111337 c t s P Q R).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850017 _111337 c t u s P Q R)). Qed.
Lemma lem4850019 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850020 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term475 _111337 c t s P Q R) = (term485 _111337 c t s P Q R).
Proof. exact (MK_COMB (@lem4850019 _111337) (@lem4850018 _111337 c t s P Q R)). Qed.
Lemma lem4850021 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term474 _111337 c t s P Q R) = (term475 _111337 c t s P Q R)) = ((term468 _111337 c t s P Q R) = (term485 _111337 c t s P Q R)).
Proof. exact (MK_COMB (@lem4850014 _111337 c t s P Q R) (@lem4850020 _111337 c t s P Q R)). Qed.
Lemma lem4850022 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term468 _111337 c t s P Q R) = (term485 _111337 c t s P Q R).
Proof. exact (EQ_MP (@lem4850021 _111337 c t s P Q R) (@lem4850006 _111337 c t s P Q R)). Qed.
Lemma lem4850024 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4850025 {_111337 : Type'} (P : Prop) (Q : type72 _111337) : (term486 _111337 P Q) = (term487 _111337 P Q).
Proof. exact (@lem4850024 (type178 _111337) P Q). Qed.
Lemma lem4850026 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term488 _111337 c t u s P Q R) = (term489 _111337 c t u s P Q R).
Proof. exact (@lem4850025 _111337 (term298 _111337 c P Q R t) (term419 _111337 u s P Q R)). Qed.
Lemma lem4850027 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term490 _111337 u s P Q R c) = (term417 _111337 u s P Q c R).
Proof. exact (eq_refl (term490 _111337 u s P Q R c)). Qed.
Lemma lem4850028 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term491 _111337 u s P Q R) = (term419 _111337 u s P Q R).
Proof. exact (fun_ext (fun c : type178 _111337 => @lem4850027 _111337 u s P Q c R)). Qed.
Lemma lem4850029 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4850030 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term492 _111337 u s P Q R) = (term420 _111337 u s P Q R).
Proof. exact (MK_COMB (@lem4850029 _111337) (@lem4850028 _111337 u s P Q R)). Qed.
Lemma lem4850031 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (eq_refl (term454 _111337 c P Q R t)). Qed.
Lemma lem4850032 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term488 _111337 c t u s P Q R) = (term482 _111337 c t u s P Q R).
Proof. exact (MK_COMB (@lem4850031 _111337 c P Q R t) (@lem4850030 _111337 u s P Q R)). Qed.
Lemma lem4850033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4850034 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term493 _111337 c t u s P Q R) = (term494 _111337 c t u s P Q R).
Proof. exact (MK_COMB (@lem4850033) (@lem4850032 _111337 c t u s P Q R)). Qed.
Lemma lem4850035 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c : type178 _111337) (R : type686 _111337) : (term490 _111337 u s P Q R c) = (term417 _111337 u s P Q c R).
Proof. exact (eq_refl (term490 _111337 u s P Q R c)). Qed.
Lemma lem4850036 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (eq_refl (term454 _111337 c P Q R t)). Qed.
Lemma lem4850037 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term495 _111337 c t u s P Q R c') = (term496 _111337 c t u s P Q c' R).
Proof. exact (MK_COMB (@lem4850036 _111337 c P Q R t) (@lem4850035 _111337 u s P Q c' R)). Qed.
Lemma lem4850038 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term497 _111337 c t u s P Q R) = (term498 _111337 c t u s P Q R).
Proof. exact (fun_ext (fun c' : type178 _111337 => @lem4850037 _111337 c t u s P Q c' R)). Qed.
Lemma lem4850039 {_111337 : Type'} : (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex (((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4850040 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term489 _111337 c t u s P Q R) = (term499 _111337 c t u s P Q R).
Proof. exact (MK_COMB (@lem4850039 _111337) (@lem4850038 _111337 c t u s P Q R)). Qed.
Lemma lem4850041 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : ((term488 _111337 c t u s P Q R) = (term489 _111337 c t u s P Q R)) = ((term482 _111337 c t u s P Q R) = (term499 _111337 c t u s P Q R)).
Proof. exact (MK_COMB (@lem4850034 _111337 c t u s P Q R) (@lem4850040 _111337 c t u s P Q R)). Qed.
Lemma lem4850042 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term482 _111337 c t u s P Q R) = (term499 _111337 c t u s P Q R).
Proof. exact (EQ_MP (@lem4850041 _111337 c t u s P Q R) (@lem4850026 _111337 c t u s P Q R)). Qed.
Lemma lem4850043 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term484 _111337 c t s P Q R) = (term500 _111337 c t s P Q R).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850042 _111337 c t u s P Q R)). Qed.
Lemma lem4850044 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850045 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term485 _111337 c t s P Q R) = (term501 _111337 c t s P Q R).
Proof. exact (MK_COMB (@lem4850044 _111337) (@lem4850043 _111337 c t s P Q R)). Qed.
Lemma lem4850046 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term468 _111337 c t s P Q R) = (term501 _111337 c t s P Q R).
Proof. exact (TRANS (@lem4850022 _111337 c t s P Q R) (@lem4850045 _111337 c t s P Q R)). Qed.
Lemma lem4850047 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term470 _111337 c t P Q R) = (term502 _111337 c t P Q R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4850046 _111337 c t s P Q R)). Qed.
Lemma lem4850048 {_111337 : Type'} : (@ex (_111337 -> Prop)) = (@ex (_111337 -> Prop)).
Proof. exact (eq_refl (@ex (_111337 -> Prop))). Qed.
Lemma lem4850049 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term471 _111337 c t P Q R) = (term503 _111337 c t P Q R).
Proof. exact (MK_COMB (@lem4850048 _111337) (@lem4850047 _111337 c t P Q R)). Qed.
Lemma lem4850050 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term456 _111337 c t P Q R) = (term503 _111337 c t P Q R).
Proof. exact (TRANS (@lem4850002 _111337 c t P Q R) (@lem4850049 _111337 c t P Q R)). Qed.
Lemma lem4850051 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term458 _111337 c P Q R) = (term504 _111337 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4850050 _111337 c t P Q R)). Qed.
Lemma lem4850052 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> Prop)) = (@ex ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850053 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term459 _111337 c P Q R) = (term505 _111337 c P Q R).
Proof. exact (MK_COMB (@lem4850052 _111337) (@lem4850051 _111337 c P Q R)). Qed.
Lemma lem4850054 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term439 _111337 c P Q R) = (term505 _111337 c P Q R).
Proof. exact (TRANS (@lem4849982 _111337 c P Q R) (@lem4850053 _111337 c P Q R)). Qed.
Lemma lem4850055 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term441 _111337 P Q R) = (term506 _111337 P Q R).
Proof. exact (fun_ext (fun c : type598 _111337 => @lem4850054 _111337 c P Q R)). Qed.
Lemma lem4850056 {_111337 : Type'} : (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)) = (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop)).
Proof. exact (eq_refl (@ex ((_111337 -> Prop) -> ((_111337 -> Prop) -> Prop) -> _111337 -> Prop))). Qed.
Lemma lem4850057 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term442 _111337 P Q R) = (term507 _111337 P Q R).
Proof. exact (MK_COMB (@lem4850056 _111337) (@lem4850055 _111337 P Q R)). Qed.
Lemma lem4850058 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term425 _111337 P Q R) = (term507 _111337 P Q R).
Proof. exact (TRANS (@lem4849956 _111337 P Q R) (@lem4850057 _111337 P Q R)). Qed.
Lemma lem4850060 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term156 _111337 P Q R) = (term507 _111337 P Q R).
Proof. exact (TRANS (@lem4849930 _111337 P Q R) (@lem4850058 _111337 P Q R)). Qed.
Lemma lem4850061 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term32 _111337 P Q R) = (term507 _111337 P Q R).
Proof. exact (TRANS (@lem4849127 _111337 P Q R) (@lem4850060 _111337 P Q R)). Qed.
Lemma lem4850062 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : term507 _111337 P Q R.
Proof. exact (EQ_MP (@lem4850061 _111337 P Q R) (@lem4848969 _111337 P Q R h1)). Qed.
Lemma lem4850063 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term505 _111337 c P Q R) : term505 _111337 c P Q R.
Proof. exact (h1). Qed.
Lemma lem4850064 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term503 _111337 c t P Q R) : term503 _111337 c t P Q R.
Proof. exact (h1). Qed.
Lemma lem4850065 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term501 _111337 c t s P Q R) : term501 _111337 c t s P Q R.
Proof. exact (h1). Qed.
Lemma lem4850066 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term499 _111337 c t u s P Q R) : term499 _111337 c t u s P Q R.
Proof. exact (h1). Qed.
Lemma lem4850067 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term496 _111337 c t u s P Q c' R) : term496 _111337 c t u s P Q c' R.
Proof. exact (h1). Qed.
Lemma lem4850100 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (t : type686 _111337) : (term366 _111337 P Q c' R t) = (term366 _111337 P Q c' R t).
Proof. exact (eq_refl (term366 _111337 P Q c' R t)). Qed.
Lemma lem4850101 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term368 _111337 P Q c' R) = (term368 _111337 P Q c' R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4850100 _111337 P Q c' R t)). Qed.
Lemma lem4850102 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850103 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term370 _111337 P Q c' R) = (term370 _111337 P Q c' R).
Proof. exact (MK_COMB (@lem4850102 _111337) (@lem4850101 _111337 P Q c' R)). Qed.
Lemma lem4850108 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term101 _111337 R s) = (term101 _111337 R s).
Proof. exact (eq_refl (term101 _111337 R s)). Qed.
Lemma lem4850115 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) : ((@INTERS _111337 u) = s) = ((@INTERS _111337 u) = s).
Proof. exact (eq_refl ((@INTERS _111337 u) = s)). Qed.
Lemma lem4850128 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term65 _111337 u Q c) = (term65 _111337 u Q c).
Proof. exact (eq_refl (term65 _111337 u Q c)). Qed.
Lemma lem4850129 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term75 _111337 u Q) = (term75 _111337 u Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4850128 _111337 u Q c)). Qed.
Lemma lem4850130 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850131 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term76 _111337 u Q) = (term76 _111337 u Q).
Proof. exact (MK_COMB (@lem4850130 _111337) (@lem4850129 _111337 u Q)). Qed.
Lemma lem4850132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850133 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term83 _111337 u Q) = (term83 _111337 u Q).
Proof. exact (MK_COMB (@lem4850132) (@lem4850131 _111337 u Q)). Qed.
Lemma lem4850134 {_111337 : Type'} (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term84 _111337 Q u s) = (term84 _111337 Q u s).
Proof. exact (MK_COMB (@lem4850133 _111337 u Q) (@lem4850115 _111337 u s)). Qed.
Lemma lem4850139 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term54 _111337 P u) = (term54 _111337 P u).
Proof. exact (eq_refl (term54 _111337 P u)). Qed.
Lemma lem4850140 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term89 _111337 P Q u s) = (term89 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4850139 _111337 P u) (@lem4850134 _111337 Q u s)). Qed.
Lemma lem4850141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850142 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term316 _111337 P Q u s) = (term316 _111337 P Q u s).
Proof. exact (MK_COMB (@lem4850141) (@lem4850140 _111337 P Q u s)). Qed.
Lemma lem4850143 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term318 _111337 P Q u R s) = (term318 _111337 P Q u R s).
Proof. exact (MK_COMB (@lem4850142 _111337 P Q u s) (@lem4850108 _111337 R s)). Qed.
Lemma lem4850144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850145 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term401 _111337 P Q u R s) = (term401 _111337 P Q u R s).
Proof. exact (MK_COMB (@lem4850144) (@lem4850143 _111337 P Q u R s)). Qed.
Lemma lem4850146 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term417 _111337 u s P Q c' R) = (term417 _111337 u s P Q c' R).
Proof. exact (MK_COMB (@lem4850145 _111337 P Q u R s) (@lem4850103 _111337 P Q c' R)). Qed.
Lemma lem4850153 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term124 _111337 R t) = (term124 _111337 R t).
Proof. exact (eq_refl (term124 _111337 R t)). Qed.
Lemma lem4850166 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term65 _111337 t Q c) = (term65 _111337 t Q c).
Proof. exact (eq_refl (term65 _111337 t Q c)). Qed.
Lemma lem4850167 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term75 _111337 t Q) = (term75 _111337 t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4850166 _111337 t Q c)). Qed.
Lemma lem4850168 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850169 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term76 _111337 t Q) = (term76 _111337 t Q).
Proof. exact (MK_COMB (@lem4850168 _111337) (@lem4850167 _111337 t Q)). Qed.
Lemma lem4850174 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term54 _111337 P t) = (term54 _111337 P t).
Proof. exact (eq_refl (term54 _111337 P t)). Qed.
Lemma lem4850175 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term123 _111337 P t Q) = (term123 _111337 P t Q).
Proof. exact (MK_COMB (@lem4850174 _111337 P t) (@lem4850169 _111337 t Q)). Qed.
Lemma lem4850176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850177 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) (Q : type686 _111337) : (term126 _111337 P t Q) = (term126 _111337 P t Q).
Proof. exact (MK_COMB (@lem4850176) (@lem4850175 _111337 P t Q)). Qed.
Lemma lem4850178 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term128 _111337 P Q R t) = (term128 _111337 P Q R t).
Proof. exact (MK_COMB (@lem4850177 _111337 P t Q) (@lem4850153 _111337 R t)). Qed.
Lemma lem4850181 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4850222 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term508 _111337 P Q c u s) = (term508 _111337 P Q c u s).
Proof. exact (eq_refl (term508 _111337 P Q c u s)). Qed.
Lemma lem4850223 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term509 _111337 P Q c s) = (term509 _111337 P Q c s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850222 _111337 P Q c u s)). Qed.
Lemma lem4850224 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850225 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term510 _111337 P Q c s) = (term510 _111337 P Q c s).
Proof. exact (MK_COMB (@lem4850224 _111337) (@lem4850223 _111337 P Q c s)). Qed.
Lemma lem4850226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4850227 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term511 _111337 P Q c s) = (term511 _111337 P Q c s).
Proof. exact (MK_COMB (@lem4850226) (@lem4850225 _111337 P Q c s)). Qed.
Lemma lem4850228 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term257 _111337 P Q c R s) = (term257 _111337 P Q c R s).
Proof. exact (MK_COMB (@lem4850227 _111337 P Q c s) (@lem4850181 _111337 R s)). Qed.
Lemma lem4850229 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term259 _111337 P Q c R) = (term259 _111337 P Q c R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4850228 _111337 P Q c R s)). Qed.
Lemma lem4850230 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850231 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term261 _111337 P Q c R) = (term261 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4850230 _111337) (@lem4850229 _111337 P Q c R)). Qed.
Lemma lem4850232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850233 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term280 _111337 P Q c R) = (term280 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4850232) (@lem4850231 _111337 P Q c R)). Qed.
Lemma lem4850234 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term298 _111337 c P Q R t) = (term298 _111337 c P Q R t).
Proof. exact (MK_COMB (@lem4850233 _111337 P Q c R) (@lem4850178 _111337 P Q R t)). Qed.
Lemma lem4850235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4850236 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) : (term454 _111337 c P Q R t) = (term454 _111337 c P Q R t).
Proof. exact (MK_COMB (@lem4850235) (@lem4850234 _111337 c P Q R t)). Qed.
Lemma lem4850237 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term496 _111337 c t u s P Q c' R) = (term496 _111337 c t u s P Q c' R).
Proof. exact (MK_COMB (@lem4850236 _111337 c P Q R t) (@lem4850146 _111337 u s P Q c' R)). Qed.
Lemma lem4850238 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term496 _111337 c t u s P Q c' R) : term496 _111337 c t u s P Q c' R.
Proof. exact (EQ_MP (@lem4850237 _111337 c t u s P Q c' R) (@lem4850067 _111337 c t u s P Q c' R h1)). Qed.
Lemma lem4850239 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term298 _111337 c P Q R t.
Proof. exact (h1). Qed.
Lemma lem4850240 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term417 _111337 u s P Q c' R.
Proof. exact (h1). Qed.
Lemma lem4850241 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term128 _111337 P Q R t.
Proof. exact (proj2 (@lem4850239 _111337 c P Q R t h1)). Qed.
Lemma lem4850242 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term261 _111337 P Q c R.
Proof. exact (proj1 (@lem4850239 _111337 c P Q R t h1)). Qed.
Lemma lem4850244 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term123 _111337 P t Q.
Proof. exact (proj1 (@lem4850241 _111337 c P Q R t h1)). Qed.
Lemma lem4850245 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term76 _111337 t Q.
Proof. exact (proj2 (@lem4850244 _111337 c P Q R t h1)). Qed.
Lemma lem4850247 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term370 _111337 P Q c' R.
Proof. exact (proj2 (@lem4850240 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850248 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term318 _111337 P Q u R s.
Proof. exact (proj1 (@lem4850240 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850250 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term89 _111337 P Q u s.
Proof. exact (proj1 (@lem4850248 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850251 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term84 _111337 Q u s.
Proof. exact (proj2 (@lem4850250 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850254 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term76 _111337 u Q.
Proof. exact (proj1 (@lem4850251 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850256 {A : Type'} (P : A -> Prop) (Q : Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4850257 {_111337 : Type'} (P : type180 _111337) (Q : Prop) : (term514 _111337 P Q) = (term515 _111337 P Q).
Proof. exact (@lem4850256 (type686 _111337) P Q). Qed.
Lemma lem4850258 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term516 _111337 P Q c R s) = (term517 _111337 P Q c R s).
Proof. exact (@lem4850257 _111337 (term509 _111337 P Q c s) (R s)). Qed.
Lemma lem4850259 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term518 _111337 P Q c s u) = (term508 _111337 P Q c u s).
Proof. exact (eq_refl (term518 _111337 P Q c s u)). Qed.
Lemma lem4850260 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term519 _111337 P Q c s) = (term509 _111337 P Q c s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850259 _111337 P Q c u s)). Qed.
Lemma lem4850261 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850262 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term520 _111337 P Q c s) = (term510 _111337 P Q c s).
Proof. exact (MK_COMB (@lem4850261 _111337) (@lem4850260 _111337 P Q c s)). Qed.
Lemma lem4850263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4850264 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (s : _111337 -> Prop) : (term521 _111337 P Q c s) = (term511 _111337 P Q c s).
Proof. exact (MK_COMB (@lem4850263) (@lem4850262 _111337 P Q c s)). Qed.
Lemma lem4850265 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4850266 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term516 _111337 P Q c R s) = (term257 _111337 P Q c R s).
Proof. exact (MK_COMB (@lem4850264 _111337 P Q c s) (@lem4850265 _111337 R s)). Qed.
Lemma lem4850267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4850268 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term522 _111337 P Q c R s) = (term523 _111337 P Q c R s).
Proof. exact (MK_COMB (@lem4850267) (@lem4850266 _111337 P Q c R s)). Qed.
Lemma lem4850269 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term518 _111337 P Q c s u) = (term508 _111337 P Q c u s).
Proof. exact (eq_refl (term518 _111337 P Q c s u)). Qed.
Lemma lem4850270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4850271 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term524 _111337 P Q c s u) = (term525 _111337 P Q c u s).
Proof. exact (MK_COMB (@lem4850270) (@lem4850269 _111337 P Q c u s)). Qed.
Lemma lem4850272 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4850273 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term526 _111337 P Q c u R s) = (term527 _111337 P Q c u R s).
Proof. exact (MK_COMB (@lem4850271 _111337 P Q c u s) (@lem4850272 _111337 R s)). Qed.
Lemma lem4850274 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term528 _111337 P Q c R s) = (term529 _111337 P Q c R s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850273 _111337 P Q c u R s)). Qed.
Lemma lem4850275 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850276 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term517 _111337 P Q c R s) = (term530 _111337 P Q c R s).
Proof. exact (MK_COMB (@lem4850275 _111337) (@lem4850274 _111337 P Q c R s)). Qed.
Lemma lem4850277 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : ((term516 _111337 P Q c R s) = (term517 _111337 P Q c R s)) = ((term257 _111337 P Q c R s) = (term530 _111337 P Q c R s)).
Proof. exact (MK_COMB (@lem4850268 _111337 P Q c R s) (@lem4850276 _111337 P Q c R s)). Qed.
Lemma lem4850278 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term257 _111337 P Q c R s) = (term530 _111337 P Q c R s).
Proof. exact (EQ_MP (@lem4850277 _111337 P Q c R s) (@lem4850258 _111337 P Q c R s)). Qed.
Lemma lem4850279 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term259 _111337 P Q c R) = (term531 _111337 P Q c R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4850278 _111337 P Q c R s)). Qed.
Lemma lem4850280 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850281 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term261 _111337 P Q c R) = (term532 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4850280 _111337) (@lem4850279 _111337 P Q c R)). Qed.
Lemma lem4850282 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4850299 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term533 _111337 Q c u s) = (term534 _111337 Q c u s).
Proof. exact (@lem19699 (term535 _111337 c s u) (term536 _111337 Q c s u) (term77 _111337 u s)). Qed.
Lemma lem4850302 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term85 _111337 P u) = (term85 _111337 P u).
Proof. exact (eq_refl (term85 _111337 P u)). Qed.
Lemma lem4850303 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term508 _111337 P Q c u s) = (term537 _111337 P Q c u s).
Proof. exact (MK_COMB (@lem4850302 _111337 P u) (@lem4850299 _111337 Q c u s)). Qed.
Lemma lem4850310 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term537 _111337 P Q c u s) = (term538 _111337 P Q c u s).
Proof. exact (@lem19490 (term539 _111337 c u s) (term183 _111337 P u) (term540 _111337 Q c u s)). Qed.
Lemma lem4850311 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term508 _111337 P Q c u s) = (term538 _111337 P Q c u s).
Proof. exact (TRANS (@lem4850303 _111337 P Q c u s) (@lem4850310 _111337 P Q c u s)). Qed.
Lemma lem4850312 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4850313 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (s : _111337 -> Prop) : (term525 _111337 P Q c u s) = (term541 _111337 P Q c u s).
Proof. exact (MK_COMB (@lem4850312) (@lem4850311 _111337 P Q c u s)). Qed.
Lemma lem4850314 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term527 _111337 P Q c u R s) = (term542 _111337 P Q c u R s).
Proof. exact (MK_COMB (@lem4850313 _111337 P Q c u s) (@lem4850282 _111337 R s)). Qed.
Lemma lem4850321 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term542 _111337 P Q c u R s) = (term543 _111337 P Q c u R s).
Proof. exact (@lem19699 (term544 _111337 P c u s) (term545 _111337 P Q c u s) (R s)). Qed.
Lemma lem4850322 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (u : type686 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term527 _111337 P Q c u R s) = (term543 _111337 P Q c u R s).
Proof. exact (TRANS (@lem4850314 _111337 P Q c u R s) (@lem4850321 _111337 P Q c u R s)). Qed.
Lemma lem4850323 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term529 _111337 P Q c R s) = (term546 _111337 P Q c R s).
Proof. exact (fun_ext (fun u : type686 _111337 => @lem4850322 _111337 P Q c u R s)). Qed.
Lemma lem4850324 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850325 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (s : _111337 -> Prop) : (term530 _111337 P Q c R s) = (term547 _111337 P Q c R s).
Proof. exact (MK_COMB (@lem4850324 _111337) (@lem4850323 _111337 P Q c R s)). Qed.
Lemma lem4850326 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term531 _111337 P Q c R) = (term548 _111337 P Q c R).
Proof. exact (fun_ext (fun s : _111337 -> Prop => @lem4850325 _111337 P Q c R s)). Qed.
Lemma lem4850327 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850328 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term532 _111337 P Q c R) = (term549 _111337 P Q c R).
Proof. exact (MK_COMB (@lem4850327 _111337) (@lem4850326 _111337 P Q c R)). Qed.
Lemma lem4850329 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) : (term261 _111337 P Q c R) = (term549 _111337 P Q c R).
Proof. exact (TRANS (@lem4850281 _111337 P Q c R) (@lem4850328 _111337 P Q c R)). Qed.
Lemma lem4850330 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term549 _111337 P Q c R.
Proof. exact (EQ_MP (@lem4850329 _111337 P Q c R) (@lem4850242 _111337 c P Q R t h1)). Qed.
Lemma lem4850346 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term65 _111337 t Q c) = (term65 _111337 t Q c).
Proof. exact (eq_refl (term65 _111337 t Q c)). Qed.
Lemma lem4850347 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term75 _111337 t Q) = (term75 _111337 t Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4850346 _111337 t Q c)). Qed.
Lemma lem4850348 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850350 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) : (term76 _111337 t Q) = (term76 _111337 t Q).
Proof. exact (MK_COMB (@lem4850348 _111337) (@lem4850347 _111337 t Q)). Qed.
Lemma lem4850351 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term76 _111337 t Q.
Proof. exact (EQ_MP (@lem4850350 _111337 t Q) (@lem4850245 _111337 c P Q R t h1)). Qed.
Lemma lem4850353 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term50 _111337 R t) = (term50 _111337 R t).
Proof. exact (eq_refl (term50 _111337 R t)). Qed.
Lemma lem4850370 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (t : type686 _111337) : (term550 _111337 P Q c' t) = (term551 _111337 P Q c' t).
Proof. exact (@lem19490 (term552 _111337 c' t) (term183 _111337 P t) (term553 _111337 Q c' t)). Qed.
Lemma lem4850371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4850372 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (t : type686 _111337) : (term554 _111337 P Q c' t) = (term555 _111337 P Q c' t).
Proof. exact (MK_COMB (@lem4850371) (@lem4850370 _111337 P Q c' t)). Qed.
Lemma lem4850373 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (t : type686 _111337) : (term366 _111337 P Q c' R t) = (term556 _111337 P Q c' R t).
Proof. exact (MK_COMB (@lem4850372 _111337 P Q c' t) (@lem4850353 _111337 R t)). Qed.
Lemma lem4850380 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (t : type686 _111337) : (term556 _111337 P Q c' R t) = (term557 _111337 P Q c' R t).
Proof. exact (@lem19699 (term558 _111337 P c' t) (term559 _111337 P Q c' t) (term50 _111337 R t)). Qed.
Lemma lem4850381 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (t : type686 _111337) : (term366 _111337 P Q c' R t) = (term557 _111337 P Q c' R t).
Proof. exact (TRANS (@lem4850373 _111337 P Q c' R t) (@lem4850380 _111337 P Q c' R t)). Qed.
Lemma lem4850382 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term368 _111337 P Q c' R) = (term560 _111337 P Q c' R).
Proof. exact (fun_ext (fun t : type686 _111337 => @lem4850381 _111337 P Q c' R t)). Qed.
Lemma lem4850383 {_111337 : Type'} : (@all ((_111337 -> Prop) -> Prop)) = (@all ((_111337 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111337 -> Prop) -> Prop))). Qed.
Lemma lem4850385 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) : (term370 _111337 P Q c' R) = (term561 _111337 P Q c' R).
Proof. exact (MK_COMB (@lem4850383 _111337) (@lem4850382 _111337 P Q c' R)). Qed.
Lemma lem4850386 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term561 _111337 P Q c' R.
Proof. exact (EQ_MP (@lem4850385 _111337 P Q c' R) (@lem4850247 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850402 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (c : _111337 -> Prop) : (term65 _111337 u Q c) = (term65 _111337 u Q c).
Proof. exact (eq_refl (term65 _111337 u Q c)). Qed.
Lemma lem4850403 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term75 _111337 u Q) = (term75 _111337 u Q).
Proof. exact (fun_ext (fun c : _111337 -> Prop => @lem4850402 _111337 u Q c)). Qed.
Lemma lem4850404 {_111337 : Type'} : (@all (_111337 -> Prop)) = (@all (_111337 -> Prop)).
Proof. exact (eq_refl (@all (_111337 -> Prop))). Qed.
Lemma lem4850406 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) : (term76 _111337 u Q) = (term76 _111337 u Q).
Proof. exact (MK_COMB (@lem4850404 _111337) (@lem4850403 _111337 u Q)). Qed.
Lemma lem4850407 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term76 _111337 u Q.
Proof. exact (EQ_MP (@lem4850406 _111337 u Q) (@lem4850254 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850412 {_111337 : Type'} (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term562 _111337 P Q c R _60147.
Proof. exact (@lem4850330 _111337 c P Q R t h1 _60147). Qed.
Lemma lem4850413 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term562 _111337 P Q c R _60147) = (term547 _111337 P Q c R _60147).
Proof. exact (eq_refl (term562 _111337 P Q c R _60147)). Qed.
Lemma lem4850414 {_111337 : Type'} (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term547 _111337 P Q c R _60147.
Proof. exact (EQ_MP (@lem4850413 _111337 P Q c R _60147) (@lem4850412 _111337 _60147 c P Q R t h1)). Qed.
Lemma lem4850415 {_111337 : Type'} (_60147 : _111337 -> Prop) (_60148 : type686 _111337) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term563 _111337 P Q c R _60147 _60148.
Proof. exact (@lem4850414 _111337 _60147 c P Q R t h1 _60148). Qed.
Lemma lem4850416 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term563 _111337 P Q c R _60147 _60148) = (term543 _111337 P Q c _60148 R _60147).
Proof. exact (eq_refl (term563 _111337 P Q c R _60147 _60148)). Qed.
Lemma lem4850417 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term543 _111337 P Q c _60148 R _60147.
Proof. exact (EQ_MP (@lem4850416 _111337 P Q c _60148 R _60147) (@lem4850415 _111337 _60147 _60148 c P Q R t h1)). Qed.
Lemma lem4850418 {_111337 : Type'} (_60149 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term564 _111337 t Q _60149.
Proof. exact (@lem4850351 _111337 c P Q R t h1 _60149). Qed.
Lemma lem4850419 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (_60149 : _111337 -> Prop) : (term564 _111337 t Q _60149) = (term65 _111337 t Q _60149).
Proof. exact (eq_refl (term564 _111337 t Q _60149)). Qed.
Lemma lem4850421 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term565 _111337 P Q c' R _60150.
Proof. exact (@lem4850386 _111337 u s P Q c' R h1 _60150). Qed.
Lemma lem4850422 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term565 _111337 P Q c' R _60150) = (term557 _111337 P Q c' R _60150).
Proof. exact (eq_refl (term565 _111337 P Q c' R _60150)). Qed.
Lemma lem4850423 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term557 _111337 P Q c' R _60150.
Proof. exact (EQ_MP (@lem4850422 _111337 P Q c' R _60150) (@lem4850421 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4850424 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term564 _111337 u Q _60151.
Proof. exact (@lem4850407 _111337 u s P Q c' R h1 _60151). Qed.
Lemma lem4850425 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (_60151 : _111337 -> Prop) : (term564 _111337 u Q _60151) = (term65 _111337 u Q _60151).
Proof. exact (eq_refl (term564 _111337 u Q _60151)). Qed.
Lemma lem4850427 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term566 _111337 P Q c _60148 R _60147.
Proof. exact (proj2 (@lem4850417 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4850428 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term567 _111337 P c _60148 R _60147.
Proof. exact (proj1 (@lem4850417 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4850429 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term568 _111337 P Q c' R _60150.
Proof. exact (proj2 (@lem4850423 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4850430 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term569 _111337 P c' R _60150.
Proof. exact (proj1 (@lem4850423 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4850432 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term124 _111337 R t.
Proof. exact (proj2 (@lem4850241 _111337 c P Q R t h1)). Qed.
Lemma lem4850440 {_111337 : Type'} (_60149 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term65 _111337 t Q _60149.
Proof. exact (EQ_MP (@lem4850419 _111337 t Q _60149) (@lem4850418 _111337 _60149 c P Q R t h1)). Qed.
Lemma lem4850444 {_111337 : Type'} (P : type180 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term567 _111337 P c _60148 R _60147) = (term570 _111337 P c _60148 R _60147).
Proof. exact (@lem4848619 (term183 _111337 P _60148) (term539 _111337 c _60148 _60147) (R _60147)). Qed.
Lemma lem4850451 {_111337 : Type'} (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term571 _111337 c _60148 R _60147) = (term572 _111337 c _60148 R _60147).
Proof. exact (@lem4848619 (term535 _111337 c _60147 _60148) (term77 _111337 _60148 _60147) (R _60147)). Qed.
Lemma lem4850452 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term85 _111337 P _60148) = (term85 _111337 P _60148).
Proof. exact (eq_refl (term85 _111337 P _60148)). Qed.
Lemma lem4850455 {_111337 : Type'} (P : type180 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term570 _111337 P c _60148 R _60147) = (term573 _111337 P c _60148 R _60147).
Proof. exact (MK_COMB (@lem4850452 _111337 P _60148) (@lem4850451 _111337 c _60148 R _60147)). Qed.
Lemma lem4850457 {_111337 : Type'} (P : type180 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term567 _111337 P c _60148 R _60147) = (term573 _111337 P c _60148 R _60147).
Proof. exact (TRANS (@lem4850444 _111337 P c _60148 R _60147) (@lem4850455 _111337 P c _60148 R _60147)). Qed.
Lemma lem4850458 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term573 _111337 P c _60148 R _60147.
Proof. exact (EQ_MP (@lem4850457 _111337 P c _60148 R _60147) (@lem4850428 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4850462 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term566 _111337 P Q c _60148 R _60147) = (term574 _111337 P Q c _60148 R _60147).
Proof. exact (@lem4848619 (term183 _111337 P _60148) (term540 _111337 Q c _60148 _60147) (R _60147)). Qed.
Lemma lem4850469 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term575 _111337 Q c _60148 R _60147) = (term576 _111337 Q c _60148 R _60147).
Proof. exact (@lem4848619 (term536 _111337 Q c _60147 _60148) (term77 _111337 _60148 _60147) (R _60147)). Qed.
Lemma lem4850470 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term85 _111337 P _60148) = (term85 _111337 P _60148).
Proof. exact (eq_refl (term85 _111337 P _60148)). Qed.
Lemma lem4850473 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term574 _111337 P Q c _60148 R _60147) = (term577 _111337 P Q c _60148 R _60147).
Proof. exact (MK_COMB (@lem4850470 _111337 P _60148) (@lem4850469 _111337 Q c _60148 R _60147)). Qed.
Lemma lem4850475 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term566 _111337 P Q c _60148 R _60147) = (term577 _111337 P Q c _60148 R _60147).
Proof. exact (TRANS (@lem4850462 _111337 P Q c _60148 R _60147) (@lem4850473 _111337 P Q c _60148 R _60147)). Qed.
Lemma lem4850476 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term577 _111337 P Q c _60148 R _60147.
Proof. exact (EQ_MP (@lem4850475 _111337 P Q c _60148 R _60147) (@lem4850427 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4850478 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term101 _111337 R s.
Proof. exact (proj2 (@lem4850248 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850488 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : (@INTERS _111337 u) = s.
Proof. exact (proj2 (@lem4850251 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850499 {_111337 : Type'} (P : type180 _111337) (c' : type178 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term569 _111337 P c' R _60150) = (term578 _111337 P c' R _60150).
Proof. exact (@lem4848619 (term183 _111337 P _60150) (term552 _111337 c' _60150) (term50 _111337 R _60150)). Qed.
Lemma lem4850511 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term568 _111337 P Q c' R _60150) = (term579 _111337 P Q c' R _60150).
Proof. exact (@lem4848619 (term183 _111337 P _60150) (term553 _111337 Q c' _60150) (term50 _111337 R _60150)). Qed.
Lemma lem4850513 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : s = (@INTERS _111337 u).
Proof. exact (SYM (@lem4850488 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850528 {_111337 : Type'} (R : type686 _111337) : (term580 _111337 R) = (term580 _111337 R).
Proof. exact (eq_refl (term580 _111337 R)). Qed.
Lemma lem4850529 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : (term581 _111337 R s) = (term582 _111337 R u).
Proof. exact (MK_COMB (@lem4850528 _111337 R) (@lem4850513 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850530 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) : (term582 _111337 R u) = (term124 _111337 R u).
Proof. exact (eq_refl (term582 _111337 R u)). Qed.
Lemma lem4850531 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term583 _111337 R s) = (term583 _111337 R s).
Proof. exact (eq_refl (term583 _111337 R s)). Qed.
Lemma lem4850532 {_111337 : Type'} (s : _111337 -> Prop) (R : type686 _111337) (u : type686 _111337) : ((term581 _111337 R s) = (term582 _111337 R u)) = ((term581 _111337 R s) = (term124 _111337 R u)).
Proof. exact (MK_COMB (@lem4850531 _111337 R s) (@lem4850530 _111337 R u)). Qed.
Lemma lem4850533 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term581 _111337 R s) = (term101 _111337 R s).
Proof. exact (eq_refl (term581 _111337 R s)). Qed.
Lemma lem4850534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4850535 {_111337 : Type'} (R : type686 _111337) (s : _111337 -> Prop) : (term583 _111337 R s) = (term584 _111337 R s).
Proof. exact (MK_COMB (@lem4850534) (@lem4850533 _111337 R s)). Qed.
Lemma lem4850536 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) : (term124 _111337 R u) = (term124 _111337 R u).
Proof. exact (eq_refl (term124 _111337 R u)). Qed.
Lemma lem4850537 {_111337 : Type'} (s : _111337 -> Prop) (R : type686 _111337) (u : type686 _111337) : ((term581 _111337 R s) = (term124 _111337 R u)) = ((term101 _111337 R s) = (term124 _111337 R u)).
Proof. exact (MK_COMB (@lem4850535 _111337 R s) (@lem4850536 _111337 R u)). Qed.
Lemma lem4850538 {_111337 : Type'} (s : _111337 -> Prop) (R : type686 _111337) (u : type686 _111337) : ((term581 _111337 R s) = (term582 _111337 R u)) = ((term101 _111337 R s) = (term124 _111337 R u)).
Proof. exact (TRANS (@lem4850532 _111337 s R u) (@lem4850537 _111337 s R u)). Qed.
Lemma lem4850539 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : (term101 _111337 R s) = (term124 _111337 R u).
Proof. exact (EQ_MP (@lem4850538 _111337 s R u) (@lem4850529 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850540 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term124 _111337 R u.
Proof. exact (EQ_MP (@lem4850539 _111337 u s P Q c' R h1) (@lem4850478 _111337 u s P Q c' R h1)). Qed.
Lemma lem4850568 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term65 _111337 u Q _60151.
Proof. exact (EQ_MP (@lem4850425 _111337 u Q _60151) (@lem4850424 _111337 _60151 u s P Q c' R h1)). Qed.
Lemma lem4850582 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term578 _111337 P c' R _60150.
Proof. exact (EQ_MP (@lem4850499 _111337 P c' R _60150) (@lem4850430 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4850596 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term579 _111337 P Q c' R _60150.
Proof. exact (EQ_MP (@lem4850511 _111337 P Q c' R _60150) (@lem4850429 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4850680 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : P t.
Proof. exact (proj1 (@lem4850244 _111337 c P Q R t h1)). Qed.
Lemma lem4850681 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term585 _111337 P t.
Proof. exact (fun h0 : term183 _111337 P t => @lem4850680 _111337 c P Q R t h1). Qed.
Lemma lem4850683 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4850684 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term585 _111337 P t) = (P t).
Proof. exact (@lem4850683 (P t)). Qed.
Lemma lem4850685 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : P t.
Proof. exact (EQ_MP (@lem4850684 _111337 P t) (@lem4850681 _111337 c P Q R t h1)). Qed.
Lemma lem4850687 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : P t.
Proof. exact (proj1 (@lem4850244 _111337 c P Q R t h1)). Qed.
Lemma lem4850688 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term585 _111337 P t.
Proof. exact (fun h0 : term183 _111337 P t => @lem4850687 _111337 c P Q R t h1). Qed.
Lemma lem4850690 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4850691 {_111337 : Type'} (P : type180 _111337) (t : type686 _111337) : (term585 _111337 P t) = (P t).
Proof. exact (@lem4850690 (P t)). Qed.
Lemma lem4850692 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : P t.
Proof. exact (EQ_MP (@lem4850691 _111337 P t) (@lem4850688 _111337 c P Q R t h1)). Qed.
Lemma lem4850694 {_111337 : Type'} (x : _111337 -> Prop) : x = x.
Proof. exact (@lem21386 (_111337 -> Prop) x). Qed.
Lemma lem4850695 {_111337 : Type'} (x : _111337 -> Prop) : x = x.
Proof. exact (@lem4850694 _111337 x). Qed.
Lemma lem4850696 {_111337 : Type'} (t : type686 _111337) : (@INTERS _111337 t) = (@INTERS _111337 t).
Proof. exact (@lem4850695 _111337 (@INTERS _111337 t)). Qed.
Lemma lem4850697 {_111337 : Type'} (t : type686 _111337) : term587 _111337 t.
Proof. exact (fun h0 : term588 _111337 t => @lem4850696 _111337 t). Qed.
Lemma lem4850699 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4850700 {_111337 : Type'} (t : type686 _111337) : (term587 _111337 t) = ((@INTERS _111337 t) = (@INTERS _111337 t)).
Proof. exact (@lem4850699 ((@INTERS _111337 t) = (@INTERS _111337 t))). Qed.
Lemma lem4850701 {_111337 : Type'} (t : type686 _111337) : (@INTERS _111337 t) = (@INTERS _111337 t).
Proof. exact (EQ_MP (@lem4850700 _111337 t) (@lem4850697 _111337 t)). Qed.
Lemma lem4850704 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) : term124 _111337 R t.
Proof. exact (h1). Qed.
Lemma lem4850705 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) : term589 _111337 R t.
Proof. exact (fun h0 : term50 _111337 R t => @lem4850704 _111337 R t h1). Qed.
Lemma lem4850707 (p : Prop) : (term590 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4850708 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term589 _111337 R t) = (term124 _111337 R t).
Proof. exact (@lem4850707 (term50 _111337 R t)). Qed.
Lemma lem4850709 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) : term124 _111337 R t.
Proof. exact (EQ_MP (@lem4850708 _111337 R t) (@lem4850705 _111337 R t h1)). Qed.
Lemma lem4850715 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4850716 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term573 _111337 P c _60148 R _60147) = (term591 _111337 c P _60148 R _60147).
Proof. exact (@lem4850715 (term535 _111337 c _60147 _60148) (term183 _111337 P _60148) (term592 _111337 _60148 R _60147)). Qed.
Lemma lem4850740 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4850741 {_111337 : Type'} (R : type686 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term592 _111337 _60148 R _60147) = (term593 _111337 R _60148 _60147).
Proof. exact (@lem4850740 (R _60147) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4850749 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term85 _111337 P _60148) = (term85 _111337 P _60148).
Proof. exact (eq_refl (term85 _111337 P _60148)). Qed.
Lemma lem4850750 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term594 _111337 P _60148 R _60147) = (term595 _111337 P R _60148 _60147).
Proof. exact (MK_COMB (@lem4850749 _111337 P _60148) (@lem4850741 _111337 R _60148 _60147)). Qed.
Lemma lem4850754 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4850755 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term595 _111337 P R _60148 _60147) = (term596 _111337 R P _60148 _60147).
Proof. exact (@lem4850754 (R _60147) (term183 _111337 P _60148) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4850773 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term594 _111337 P _60148 R _60147) = (term596 _111337 R P _60148 _60147).
Proof. exact (TRANS (@lem4850750 _111337 P R _60148 _60147) (@lem4850755 _111337 R P _60148 _60147)). Qed.
Lemma lem4850774 {_111337 : Type'} (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term597 _111337 c _60147 _60148) = (term597 _111337 c _60147 _60148).
Proof. exact (eq_refl (term597 _111337 c _60147 _60148)). Qed.
Lemma lem4850775 {_111337 : Type'} (c : type598 _111337) (R : type686 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term591 _111337 c P _60148 R _60147) = (term598 _111337 c R P _60148 _60147).
Proof. exact (MK_COMB (@lem4850774 _111337 c _60147 _60148) (@lem4850773 _111337 R P _60148 _60147)). Qed.
Lemma lem4850779 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4850780 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term598 _111337 c R P _60148 _60147) = (term599 _111337 R c P _60148 _60147).
Proof. exact (@lem4850779 (R _60147) (term535 _111337 c _60147 _60148) (term600 _111337 P _60148 _60147)). Qed.
Lemma lem4850808 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term591 _111337 c P _60148 R _60147) = (term599 _111337 R c P _60148 _60147).
Proof. exact (TRANS (@lem4850775 _111337 c R P _60148 _60147) (@lem4850780 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850809 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term573 _111337 P c _60148 R _60147) = (term599 _111337 R c P _60148 _60147).
Proof. exact (TRANS (@lem4850716 _111337 c P _60148 R _60147) (@lem4850808 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4850811 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term601 _111337 P c _60148 R _60147) = (term602 _111337 R c P _60148 _60147).
Proof. exact (MK_COMB (@lem4850810) (@lem4850809 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850835 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4850836 {_111337 : Type'} (R : type686 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term592 _111337 _60148 R _60147) = (term593 _111337 R _60148 _60147).
Proof. exact (@lem4850835 (R _60147) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4850844 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term85 _111337 P _60148) = (term85 _111337 P _60148).
Proof. exact (eq_refl (term85 _111337 P _60148)). Qed.
Lemma lem4850845 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term594 _111337 P _60148 R _60147) = (term595 _111337 P R _60148 _60147).
Proof. exact (MK_COMB (@lem4850844 _111337 P _60148) (@lem4850836 _111337 R _60148 _60147)). Qed.
Lemma lem4850849 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4850850 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term595 _111337 P R _60148 _60147) = (term596 _111337 R P _60148 _60147).
Proof. exact (@lem4850849 (R _60147) (term183 _111337 P _60148) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4850868 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term594 _111337 P _60148 R _60147) = (term596 _111337 R P _60148 _60147).
Proof. exact (TRANS (@lem4850845 _111337 P R _60148 _60147) (@lem4850850 _111337 R P _60148 _60147)). Qed.
Lemma lem4850869 {_111337 : Type'} (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term597 _111337 c _60147 _60148) = (term597 _111337 c _60147 _60148).
Proof. exact (eq_refl (term597 _111337 c _60147 _60148)). Qed.
Lemma lem4850870 {_111337 : Type'} (c : type598 _111337) (R : type686 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term591 _111337 c P _60148 R _60147) = (term598 _111337 c R P _60148 _60147).
Proof. exact (MK_COMB (@lem4850869 _111337 c _60147 _60148) (@lem4850868 _111337 R P _60148 _60147)). Qed.
Lemma lem4850874 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4850875 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term598 _111337 c R P _60148 _60147) = (term599 _111337 R c P _60148 _60147).
Proof. exact (@lem4850874 (R _60147) (term535 _111337 c _60147 _60148) (term600 _111337 P _60148 _60147)). Qed.
Lemma lem4850903 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term591 _111337 c P _60148 R _60147) = (term599 _111337 R c P _60148 _60147).
Proof. exact (TRANS (@lem4850870 _111337 c R P _60148 _60147) (@lem4850875 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850904 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : ((term573 _111337 P c _60148 R _60147) = (term591 _111337 c P _60148 R _60147)) = ((term599 _111337 R c P _60148 _60147) = (term599 _111337 R c P _60148 _60147)).
Proof. exact (MK_COMB (@lem4850811 _111337 R c P _60148 _60147) (@lem4850903 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4850907 (x : Prop) : (x = x) = True.
Proof. exact (@lem4850906 Prop x). Qed.
Lemma lem4850908 {_111337 : Type'} (R : type686 _111337) (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : ((term599 _111337 R c P _60148 _60147) = (term599 _111337 R c P _60148 _60147)) = True.
Proof. exact (@lem4850907 (term599 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850909 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : ((term573 _111337 P c _60148 R _60147) = (term591 _111337 c P _60148 R _60147)) = True.
Proof. exact (TRANS (@lem4850904 _111337 R c P _60148 _60147) (@lem4850908 _111337 R c P _60148 _60147)). Qed.
Lemma lem4850910 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : True = ((term573 _111337 P c _60148 R _60147) = (term591 _111337 c P _60148 R _60147)).
Proof. exact (SYM (@lem4850909 _111337 c P _60148 R _60147)). Qed.
Lemma lem4850911 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term573 _111337 P c _60148 R _60147) = (term591 _111337 c P _60148 R _60147).
Proof. exact (EQ_MP (@lem4850910 _111337 c P _60148 R _60147) (@lem0)). Qed.
Lemma lem4850912 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term591 _111337 c P _60148 R _60147.
Proof. exact (EQ_MP (@lem4850911 _111337 c P _60148 R _60147) (@lem4850458 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4850914 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4850915 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term591 _111337 c P _60148 R _60147) = (term604 _111337 P R c _60147 _60148).
Proof. exact (@lem4850914 (term594 _111337 P _60148 R _60147) (term535 _111337 c _60147 _60148)). Qed.
Lemma lem4850917 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4850918 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term607 _111337 P _60148 R _60147) = (term608 _111337 P _60148 R _60147).
Proof. exact (@lem4850917 (term183 _111337 P _60148) (term592 _111337 _60148 R _60147)). Qed.
Lemma lem4850920 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4850921 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term609 _111337 P _60148) = (P _60148).
Proof. exact (@lem4850920 (P _60148)). Qed.
Lemma lem4850922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850923 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term610 _111337 P _60148) = (term54 _111337 P _60148).
Proof. exact (MK_COMB (@lem4850922) (@lem4850921 _111337 P _60148)). Qed.
Lemma lem4850925 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4850926 {_111337 : Type'} (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term611 _111337 _60148 R _60147) = (term612 _111337 _60148 R _60147).
Proof. exact (@lem4850925 (term77 _111337 _60148 _60147) (R _60147)). Qed.
Lemma lem4850928 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4850929 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term613 _111337 _60148 _60147) = ((@INTERS _111337 _60148) = _60147).
Proof. exact (@lem4850928 ((@INTERS _111337 _60148) = _60147)). Qed.
Lemma lem4850930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4850931 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term614 _111337 _60148 _60147) = (term615 _111337 _60148 _60147).
Proof. exact (MK_COMB (@lem4850930) (@lem4850929 _111337 _60148 _60147)). Qed.
Lemma lem4850932 {_111337 : Type'} (R : type686 _111337) (_60147 : _111337 -> Prop) : (term101 _111337 R _60147) = (term101 _111337 R _60147).
Proof. exact (eq_refl (term101 _111337 R _60147)). Qed.
Lemma lem4850933 {_111337 : Type'} (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term612 _111337 _60148 R _60147) = (term616 _111337 _60148 R _60147).
Proof. exact (MK_COMB (@lem4850931 _111337 _60148 _60147) (@lem4850932 _111337 R _60147)). Qed.
Lemma lem4850934 {_111337 : Type'} (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term611 _111337 _60148 R _60147) = (term616 _111337 _60148 R _60147).
Proof. exact (TRANS (@lem4850926 _111337 _60148 R _60147) (@lem4850933 _111337 _60148 R _60147)). Qed.
Lemma lem4850935 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term608 _111337 P _60148 R _60147) = (term617 _111337 P _60148 R _60147).
Proof. exact (MK_COMB (@lem4850923 _111337 P _60148) (@lem4850934 _111337 _60148 R _60147)). Qed.
Lemma lem4850936 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term607 _111337 P _60148 R _60147) = (term617 _111337 P _60148 R _60147).
Proof. exact (TRANS (@lem4850918 _111337 P _60148 R _60147) (@lem4850935 _111337 P _60148 R _60147)). Qed.
Lemma lem4850937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4850938 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term618 _111337 P _60148 R _60147) = (term619 _111337 P _60148 R _60147).
Proof. exact (MK_COMB (@lem4850937) (@lem4850936 _111337 P _60148 R _60147)). Qed.
Lemma lem4850939 {_111337 : Type'} (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term535 _111337 c _60147 _60148) = (term535 _111337 c _60147 _60148).
Proof. exact (eq_refl (term535 _111337 c _60147 _60148)). Qed.
Lemma lem4850940 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term604 _111337 P R c _60147 _60148) = (term620 _111337 P R c _60147 _60148).
Proof. exact (MK_COMB (@lem4850938 _111337 P _60148 R _60147) (@lem4850939 _111337 c _60147 _60148)). Qed.
Lemma lem4850941 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term591 _111337 c P _60148 R _60147) = (term620 _111337 P R c _60147 _60148).
Proof. exact (TRANS (@lem4850915 _111337 P R c _60147 _60148) (@lem4850940 _111337 P R c _60147 _60148)). Qed.
Lemma lem4850943 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) : term621 _111337 R t.
Proof. exact (conj (@lem4850701 _111337 t) (@lem4850709 _111337 R t h1)). Qed.
Lemma lem4850944 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term622 _111337 P R t.
Proof. exact (conj (@lem4850692 _111337 c P Q R t h2) (@lem4850943 _111337 R t h1)). Qed.
Lemma lem4850946 {_111337 : Type'} (_60147 : _111337 -> Prop) (_60148 : type686 _111337) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term620 _111337 P R c _60147 _60148.
Proof. exact (EQ_MP (@lem4850941 _111337 P R c _60147 _60148) (@lem4850912 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4850947 {_111337 : Type'} (_60147 : _111337 -> Prop) (_60148 : type686 _111337) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term620 _111337 P R c _60147 _60148.
Proof. exact (@lem4850946 _111337 _60147 _60148 c P Q R t h1). Qed.
Lemma lem4850948 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term623 _111337 P R c t.
Proof. exact (@lem4850947 _111337 (@INTERS _111337 t) t c P Q R t h1). Qed.
Lemma lem4850951 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term624 _111337 c t.
Proof. exact (@lem4850948 _111337 c P Q R t h2 (@lem4850944 _111337 c P Q R t h1 h2)). Qed.
Lemma lem4850952 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term625 _111337 c t.
Proof. exact (fun h0 : term626 _111337 c t => @lem4850951 _111337 c P Q R t h1 h2). Qed.
Lemma lem4850954 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4850955 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) : (term625 _111337 c t) = (term624 _111337 c t).
Proof. exact (@lem4850954 (term624 _111337 c t)). Qed.
Lemma lem4850956 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term624 _111337 c t.
Proof. exact (EQ_MP (@lem4850955 _111337 c t) (@lem4850952 _111337 c P Q R t h1 h2)). Qed.
Lemma lem4850962 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4850963 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : (term65 _111337 t Q _60149) = (term627 _111337 Q _60149 t).
Proof. exact (@lem4850962 (Q _60149) (term628 _111337 _60149 t)). Qed.
Lemma lem4850969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4850970 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : (term629 _111337 t Q _60149) = (term630 _111337 Q _60149 t).
Proof. exact (MK_COMB (@lem4850969) (@lem4850963 _111337 Q _60149 t)). Qed.
Lemma lem4850976 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : (term627 _111337 Q _60149 t) = (term627 _111337 Q _60149 t).
Proof. exact (eq_refl (term627 _111337 Q _60149 t)). Qed.
Lemma lem4850977 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : ((term65 _111337 t Q _60149) = (term627 _111337 Q _60149 t)) = ((term627 _111337 Q _60149 t) = (term627 _111337 Q _60149 t)).
Proof. exact (MK_COMB (@lem4850970 _111337 Q _60149 t) (@lem4850976 _111337 Q _60149 t)). Qed.
Lemma lem4850979 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4850980 (x : Prop) : (x = x) = True.
Proof. exact (@lem4850979 Prop x). Qed.
Lemma lem4850981 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : ((term627 _111337 Q _60149 t) = (term627 _111337 Q _60149 t)) = True.
Proof. exact (@lem4850980 (term627 _111337 Q _60149 t)). Qed.
Lemma lem4850982 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : ((term65 _111337 t Q _60149) = (term627 _111337 Q _60149 t)) = True.
Proof. exact (TRANS (@lem4850977 _111337 Q _60149 t) (@lem4850981 _111337 Q _60149 t)). Qed.
Lemma lem4850983 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : True = ((term65 _111337 t Q _60149) = (term627 _111337 Q _60149 t)).
Proof. exact (SYM (@lem4850982 _111337 Q _60149 t)). Qed.
Lemma lem4850984 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) (t : type686 _111337) : (term65 _111337 t Q _60149) = (term627 _111337 Q _60149 t).
Proof. exact (EQ_MP (@lem4850983 _111337 Q _60149 t) (@lem0)). Qed.
Lemma lem4850985 {_111337 : Type'} (_60149 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term627 _111337 Q _60149 t.
Proof. exact (EQ_MP (@lem4850984 _111337 Q _60149 t) (@lem4850440 _111337 _60149 c P Q R t h1)). Qed.
Lemma lem4850987 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4850988 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (_60149 : _111337 -> Prop) : (term627 _111337 Q _60149 t) = (term631 _111337 t Q _60149).
Proof. exact (@lem4850987 (term628 _111337 _60149 t) (Q _60149)). Qed.
Lemma lem4850990 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4850991 {_111337 : Type'} (_60149 : _111337 -> Prop) (t : type686 _111337) : (term632 _111337 _60149 t) = (@IN (_111337 -> Prop) _60149 t).
Proof. exact (@lem4850990 (@IN (_111337 -> Prop) _60149 t)). Qed.
Lemma lem4850992 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4850993 {_111337 : Type'} (_60149 : _111337 -> Prop) (t : type686 _111337) : (term633 _111337 _60149 t) = (term634 _111337 _60149 t).
Proof. exact (MK_COMB (@lem4850992) (@lem4850991 _111337 _60149 t)). Qed.
Lemma lem4850994 {_111337 : Type'} (Q : type686 _111337) (_60149 : _111337 -> Prop) : (Q _60149) = (Q _60149).
Proof. exact (eq_refl (Q _60149)). Qed.
Lemma lem4850995 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (_60149 : _111337 -> Prop) : (term631 _111337 t Q _60149) = (term51 _111337 t Q _60149).
Proof. exact (MK_COMB (@lem4850993 _111337 _60149 t) (@lem4850994 _111337 Q _60149)). Qed.
Lemma lem4850996 {_111337 : Type'} (t : type686 _111337) (Q : type686 _111337) (_60149 : _111337 -> Prop) : (term627 _111337 Q _60149 t) = (term51 _111337 t Q _60149).
Proof. exact (TRANS (@lem4850988 _111337 t Q _60149) (@lem4850995 _111337 t Q _60149)). Qed.
Lemma lem4850999 {_111337 : Type'} (_60149 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term51 _111337 t Q _60149.
Proof. exact (EQ_MP (@lem4850996 _111337 t Q _60149) (@lem4850985 _111337 _60149 c P Q R t h1)). Qed.
Lemma lem4851000 {_111337 : Type'} (_60149 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term51 _111337 t Q _60149.
Proof. exact (@lem4850999 _111337 _60149 c P Q R t h1). Qed.
Lemma lem4851001 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term635 _111337 Q c t.
Proof. exact (@lem4851000 _111337 (term636 _111337 c t) c P Q R t h1). Qed.
Lemma lem4851004 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term637 _111337 Q c t.
Proof. exact (@lem4851001 _111337 c P Q R t h2 (@lem4850956 _111337 c P Q R t h1 h2)). Qed.
Lemma lem4851005 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term638 _111337 Q c t.
Proof. exact (fun h0 : term639 _111337 Q c t => @lem4851004 _111337 c P Q R t h1 h2). Qed.
Lemma lem4851007 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851008 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (t : type686 _111337) : (term638 _111337 Q c t) = (term637 _111337 Q c t).
Proof. exact (@lem4851007 (term637 _111337 Q c t)). Qed.
Lemma lem4851009 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term637 _111337 Q c t.
Proof. exact (EQ_MP (@lem4851008 _111337 Q c t) (@lem4851005 _111337 c P Q R t h1 h2)). Qed.
Lemma lem4851011 {_111337 : Type'} (x : _111337 -> Prop) : x = x.
Proof. exact (@lem21386 (_111337 -> Prop) x). Qed.
Lemma lem4851012 {_111337 : Type'} (x : _111337 -> Prop) : x = x.
Proof. exact (@lem4851011 _111337 x). Qed.
Lemma lem4851013 {_111337 : Type'} (t : type686 _111337) : (@INTERS _111337 t) = (@INTERS _111337 t).
Proof. exact (@lem4851012 _111337 (@INTERS _111337 t)). Qed.
Lemma lem4851014 {_111337 : Type'} (t : type686 _111337) : term587 _111337 t.
Proof. exact (fun h0 : term588 _111337 t => @lem4851013 _111337 t). Qed.
Lemma lem4851016 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851017 {_111337 : Type'} (t : type686 _111337) : (term587 _111337 t) = ((@INTERS _111337 t) = (@INTERS _111337 t)).
Proof. exact (@lem4851016 ((@INTERS _111337 t) = (@INTERS _111337 t))). Qed.
Lemma lem4851018 {_111337 : Type'} (t : type686 _111337) : (@INTERS _111337 t) = (@INTERS _111337 t).
Proof. exact (EQ_MP (@lem4851017 _111337 t) (@lem4851014 _111337 t)). Qed.
Lemma lem4851044 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4851045 {_111337 : Type'} (R : type686 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term592 _111337 _60148 R _60147) = (term593 _111337 R _60148 _60147).
Proof. exact (@lem4851044 (R _60147) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4851053 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term640 _111337 Q c _60147 _60148) = (term640 _111337 Q c _60147 _60148).
Proof. exact (eq_refl (term640 _111337 Q c _60147 _60148)). Qed.
Lemma lem4851054 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (R : type686 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term576 _111337 Q c _60148 R _60147) = (term641 _111337 Q c R _60148 _60147).
Proof. exact (MK_COMB (@lem4851053 _111337 Q c _60147 _60148) (@lem4851045 _111337 R _60148 _60147)). Qed.
Lemma lem4851058 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4851059 {_111337 : Type'} (R : type686 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term641 _111337 Q c R _60148 _60147) = (term642 _111337 R Q c _60148 _60147).
Proof. exact (@lem4851058 (R _60147) (term536 _111337 Q c _60147 _60148) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4851077 {_111337 : Type'} (R : type686 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term576 _111337 Q c _60148 R _60147) = (term642 _111337 R Q c _60148 _60147).
Proof. exact (TRANS (@lem4851054 _111337 Q c R _60148 _60147) (@lem4851059 _111337 R Q c _60148 _60147)). Qed.
Lemma lem4851078 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term85 _111337 P _60148) = (term85 _111337 P _60148).
Proof. exact (eq_refl (term85 _111337 P _60148)). Qed.
Lemma lem4851079 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term577 _111337 P Q c _60148 R _60147) = (term643 _111337 P R Q c _60148 _60147).
Proof. exact (MK_COMB (@lem4851078 _111337 P _60148) (@lem4851077 _111337 R Q c _60148 _60147)). Qed.
Lemma lem4851083 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4851084 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term643 _111337 P R Q c _60148 _60147) = (term644 _111337 R P Q c _60148 _60147).
Proof. exact (@lem4851083 (R _60147) (term183 _111337 P _60148) (term540 _111337 Q c _60148 _60147)). Qed.
Lemma lem4851112 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term577 _111337 P Q c _60148 R _60147) = (term644 _111337 R P Q c _60148 _60147).
Proof. exact (TRANS (@lem4851079 _111337 P R Q c _60148 _60147) (@lem4851084 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4851114 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term645 _111337 P Q c _60148 R _60147) = (term646 _111337 R P Q c _60148 _60147).
Proof. exact (MK_COMB (@lem4851113) (@lem4851112 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851142 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term644 _111337 R P Q c _60148 _60147) = (term644 _111337 R P Q c _60148 _60147).
Proof. exact (eq_refl (term644 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851143 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : ((term577 _111337 P Q c _60148 R _60147) = (term644 _111337 R P Q c _60148 _60147)) = ((term644 _111337 R P Q c _60148 _60147) = (term644 _111337 R P Q c _60148 _60147)).
Proof. exact (MK_COMB (@lem4851114 _111337 R P Q c _60148 _60147) (@lem4851142 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851145 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4851146 (x : Prop) : (x = x) = True.
Proof. exact (@lem4851145 Prop x). Qed.
Lemma lem4851147 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : ((term644 _111337 R P Q c _60148 _60147) = (term644 _111337 R P Q c _60148 _60147)) = True.
Proof. exact (@lem4851146 (term644 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851148 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : ((term577 _111337 P Q c _60148 R _60147) = (term644 _111337 R P Q c _60148 _60147)) = True.
Proof. exact (TRANS (@lem4851143 _111337 R P Q c _60148 _60147) (@lem4851147 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851149 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : True = ((term577 _111337 P Q c _60148 R _60147) = (term644 _111337 R P Q c _60148 _60147)).
Proof. exact (SYM (@lem4851148 _111337 R P Q c _60148 _60147)). Qed.
Lemma lem4851150 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term577 _111337 P Q c _60148 R _60147) = (term644 _111337 R P Q c _60148 _60147).
Proof. exact (EQ_MP (@lem4851149 _111337 R P Q c _60148 _60147) (@lem0)). Qed.
Lemma lem4851151 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term644 _111337 R P Q c _60148 _60147.
Proof. exact (EQ_MP (@lem4851150 _111337 R P Q c _60148 _60147) (@lem4850476 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4851153 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4851154 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term644 _111337 R P Q c _60148 _60147) = (term647 _111337 P Q c _60148 R _60147).
Proof. exact (@lem4851153 (term545 _111337 P Q c _60148 _60147) (R _60147)). Qed.
Lemma lem4851156 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4851157 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term648 _111337 P Q c _60148 _60147) = (term649 _111337 P Q c _60148 _60147).
Proof. exact (@lem4851156 (term183 _111337 P _60148) (term540 _111337 Q c _60148 _60147)). Qed.
Lemma lem4851159 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851160 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term609 _111337 P _60148) = (P _60148).
Proof. exact (@lem4851159 (P _60148)). Qed.
Lemma lem4851161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851162 {_111337 : Type'} (P : type180 _111337) (_60148 : type686 _111337) : (term610 _111337 P _60148) = (term54 _111337 P _60148).
Proof. exact (MK_COMB (@lem4851161) (@lem4851160 _111337 P _60148)). Qed.
Lemma lem4851164 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4851165 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term650 _111337 Q c _60148 _60147) = (term651 _111337 Q c _60148 _60147).
Proof. exact (@lem4851164 (term536 _111337 Q c _60147 _60148) (term77 _111337 _60148 _60147)). Qed.
Lemma lem4851167 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851168 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term652 _111337 Q c _60147 _60148) = (term653 _111337 Q c _60147 _60148).
Proof. exact (@lem4851167 (term653 _111337 Q c _60147 _60148)). Qed.
Lemma lem4851169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851170 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60147 : _111337 -> Prop) (_60148 : type686 _111337) : (term654 _111337 Q c _60147 _60148) = (term655 _111337 Q c _60147 _60148).
Proof. exact (MK_COMB (@lem4851169) (@lem4851168 _111337 Q c _60147 _60148)). Qed.
Lemma lem4851172 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851173 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term613 _111337 _60148 _60147) = ((@INTERS _111337 _60148) = _60147).
Proof. exact (@lem4851172 ((@INTERS _111337 _60148) = _60147)). Qed.
Lemma lem4851174 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term651 _111337 Q c _60148 _60147) = (term656 _111337 Q c _60148 _60147).
Proof. exact (MK_COMB (@lem4851170 _111337 Q c _60147 _60148) (@lem4851173 _111337 _60148 _60147)). Qed.
Lemma lem4851175 {_111337 : Type'} (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term650 _111337 Q c _60148 _60147) = (term656 _111337 Q c _60148 _60147).
Proof. exact (TRANS (@lem4851165 _111337 Q c _60148 _60147) (@lem4851174 _111337 Q c _60148 _60147)). Qed.
Lemma lem4851176 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term649 _111337 P Q c _60148 _60147) = (term657 _111337 P Q c _60148 _60147).
Proof. exact (MK_COMB (@lem4851162 _111337 P _60148) (@lem4851175 _111337 Q c _60148 _60147)). Qed.
Lemma lem4851177 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term648 _111337 P Q c _60148 _60147) = (term657 _111337 P Q c _60148 _60147).
Proof. exact (TRANS (@lem4851157 _111337 P Q c _60148 _60147) (@lem4851176 _111337 P Q c _60148 _60147)). Qed.
Lemma lem4851178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4851179 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (_60147 : _111337 -> Prop) : (term658 _111337 P Q c _60148 _60147) = (term659 _111337 P Q c _60148 _60147).
Proof. exact (MK_COMB (@lem4851178) (@lem4851177 _111337 P Q c _60148 _60147)). Qed.
Lemma lem4851180 {_111337 : Type'} (R : type686 _111337) (_60147 : _111337 -> Prop) : (R _60147) = (R _60147).
Proof. exact (eq_refl (R _60147)). Qed.
Lemma lem4851181 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term647 _111337 P Q c _60148 R _60147) = (term660 _111337 P Q c _60148 R _60147).
Proof. exact (MK_COMB (@lem4851179 _111337 P Q c _60148 _60147) (@lem4851180 _111337 R _60147)). Qed.
Lemma lem4851182 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c : type598 _111337) (_60148 : type686 _111337) (R : type686 _111337) (_60147 : _111337 -> Prop) : (term644 _111337 R P Q c _60148 _60147) = (term660 _111337 P Q c _60148 R _60147).
Proof. exact (TRANS (@lem4851154 _111337 P Q c _60148 R _60147) (@lem4851181 _111337 P Q c _60148 R _60147)). Qed.
Lemma lem4851184 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term661 _111337 Q c t.
Proof. exact (conj (@lem4851009 _111337 c P Q R t h1 h2) (@lem4851018 _111337 t)). Qed.
Lemma lem4851185 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term662 _111337 P Q c t.
Proof. exact (conj (@lem4850685 _111337 c P Q R t h2) (@lem4851184 _111337 c P Q R t h1 h2)). Qed.
Lemma lem4851187 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term660 _111337 P Q c _60148 R _60147.
Proof. exact (EQ_MP (@lem4851182 _111337 P Q c _60148 R _60147) (@lem4851151 _111337 _60148 _60147 c P Q R t h1)). Qed.
Lemma lem4851188 {_111337 : Type'} (_60148 : type686 _111337) (_60147 : _111337 -> Prop) (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term660 _111337 P Q c _60148 R _60147.
Proof. exact (@lem4851187 _111337 _60148 _60147 c P Q R t h1). Qed.
Lemma lem4851189 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term663 _111337 P Q c R t.
Proof. exact (@lem4851188 _111337 t (@INTERS _111337 t) c P Q R t h1). Qed.
Lemma lem4851192 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term124 _111337 R t) (h2 : term298 _111337 c P Q R t) : term50 _111337 R t.
Proof. exact (@lem4851189 _111337 c P Q R t h2 (@lem4851185 _111337 c P Q R t h1 h2)). Qed.
Lemma lem4851193 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term664 _111337 R t.
Proof. exact (fun h0 : term124 _111337 R t => @lem4851192 _111337 c P Q R t h0 h1). Qed.
Lemma lem4851195 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851196 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term664 _111337 R t) = (term50 _111337 R t).
Proof. exact (@lem4851195 (term50 _111337 R t)). Qed.
Lemma lem4851197 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term50 _111337 R t.
Proof. exact (EQ_MP (@lem4851196 _111337 R t) (@lem4851193 _111337 c P Q R t h1)). Qed.
Lemma lem4851200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4851202 {_111337 : Type'} (R : type686 _111337) (t : type686 _111337) : (term124 _111337 R t) = (term665 _111337 R t).
Proof. exact (@lem4851200 (term50 _111337 R t)). Qed.
Lemma lem4851205 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term665 _111337 R t.
Proof. exact (EQ_MP (@lem4851202 _111337 R t) (@lem4850432 _111337 c P Q R t h1)). Qed.
Lemma lem4851208 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : False.
Proof. exact (@lem4851205 _111337 c P Q R t h1 (@lem4851197 _111337 c P Q R t h1)). Qed.
Lemma lem4851209 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : term666.
Proof. exact (fun h0 : ~ False => @lem4851208 _111337 c P Q R t h1). Qed.
Lemma lem4851211 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851212 : term666 = False.
Proof. exact (@lem4851211 False). Qed.
Lemma lem4851213 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (t : type686 _111337) (h1 : term298 _111337 c P Q R t) : False.
Proof. exact (EQ_MP (@lem4851212) (@lem4851209 _111337 c P Q R t h1)). Qed.
Lemma lem4851215 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : P u.
Proof. exact (proj1 (@lem4850250 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851216 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term585 _111337 P u.
Proof. exact (fun h0 : term183 _111337 P u => @lem4851215 _111337 u s P Q c' R h1). Qed.
Lemma lem4851218 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851219 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term585 _111337 P u) = (P u).
Proof. exact (@lem4851218 (P u)). Qed.
Lemma lem4851220 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : P u.
Proof. exact (EQ_MP (@lem4851219 _111337 P u) (@lem4851216 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851222 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : P u.
Proof. exact (proj1 (@lem4850250 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851223 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term585 _111337 P u.
Proof. exact (fun h0 : term183 _111337 P u => @lem4851222 _111337 u s P Q c' R h1). Qed.
Lemma lem4851225 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851226 {_111337 : Type'} (P : type180 _111337) (u : type686 _111337) : (term585 _111337 P u) = (P u).
Proof. exact (@lem4851225 (P u)). Qed.
Lemma lem4851227 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : P u.
Proof. exact (EQ_MP (@lem4851226 _111337 P u) (@lem4851223 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851230 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) (h1 : term124 _111337 R u) : term124 _111337 R u.
Proof. exact (h1). Qed.
Lemma lem4851231 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) (h1 : term124 _111337 R u) : term589 _111337 R u.
Proof. exact (fun h0 : term50 _111337 R u => @lem4851230 _111337 R u h1). Qed.
Lemma lem4851233 (p : Prop) : (term590 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4851234 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) : (term589 _111337 R u) = (term124 _111337 R u).
Proof. exact (@lem4851233 (term50 _111337 R u)). Qed.
Lemma lem4851235 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) (h1 : term124 _111337 R u) : term124 _111337 R u.
Proof. exact (EQ_MP (@lem4851234 _111337 R u) (@lem4851231 _111337 R u h1)). Qed.
Lemma lem4851241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4851242 {_111337 : Type'} (c' : type178 _111337) (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term578 _111337 P c' R _60150) = (term667 _111337 c' P R _60150).
Proof. exact (@lem4851241 (term552 _111337 c' _60150) (term183 _111337 P _60150) (term50 _111337 R _60150)). Qed.
Lemma lem4851256 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4851257 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term668 _111337 P R _60150) = (term669 _111337 R P _60150).
Proof. exact (@lem4851256 (term50 _111337 R _60150) (term183 _111337 P _60150)). Qed.
Lemma lem4851263 {_111337 : Type'} (c' : type178 _111337) (_60150 : type686 _111337) : (term670 _111337 c' _60150) = (term670 _111337 c' _60150).
Proof. exact (eq_refl (term670 _111337 c' _60150)). Qed.
Lemma lem4851264 {_111337 : Type'} (c' : type178 _111337) (R : type686 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term667 _111337 c' P R _60150) = (term671 _111337 c' R P _60150).
Proof. exact (MK_COMB (@lem4851263 _111337 c' _60150) (@lem4851257 _111337 R P _60150)). Qed.
Lemma lem4851268 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4851269 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term671 _111337 c' R P _60150) = (term672 _111337 R c' P _60150).
Proof. exact (@lem4851268 (term50 _111337 R _60150) (term552 _111337 c' _60150) (term183 _111337 P _60150)). Qed.
Lemma lem4851285 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term667 _111337 c' P R _60150) = (term672 _111337 R c' P _60150).
Proof. exact (TRANS (@lem4851264 _111337 c' R P _60150) (@lem4851269 _111337 R c' P _60150)). Qed.
Lemma lem4851286 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term578 _111337 P c' R _60150) = (term672 _111337 R c' P _60150).
Proof. exact (TRANS (@lem4851242 _111337 c' P R _60150) (@lem4851285 _111337 R c' P _60150)). Qed.
Lemma lem4851287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4851288 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term673 _111337 P c' R _60150) = (term674 _111337 R c' P _60150).
Proof. exact (MK_COMB (@lem4851287) (@lem4851286 _111337 R c' P _60150)). Qed.
Lemma lem4851302 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4851303 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term668 _111337 P R _60150) = (term669 _111337 R P _60150).
Proof. exact (@lem4851302 (term50 _111337 R _60150) (term183 _111337 P _60150)). Qed.
Lemma lem4851309 {_111337 : Type'} (c' : type178 _111337) (_60150 : type686 _111337) : (term670 _111337 c' _60150) = (term670 _111337 c' _60150).
Proof. exact (eq_refl (term670 _111337 c' _60150)). Qed.
Lemma lem4851310 {_111337 : Type'} (c' : type178 _111337) (R : type686 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term667 _111337 c' P R _60150) = (term671 _111337 c' R P _60150).
Proof. exact (MK_COMB (@lem4851309 _111337 c' _60150) (@lem4851303 _111337 R P _60150)). Qed.
Lemma lem4851314 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4851315 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term671 _111337 c' R P _60150) = (term672 _111337 R c' P _60150).
Proof. exact (@lem4851314 (term50 _111337 R _60150) (term552 _111337 c' _60150) (term183 _111337 P _60150)). Qed.
Lemma lem4851331 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : (term667 _111337 c' P R _60150) = (term672 _111337 R c' P _60150).
Proof. exact (TRANS (@lem4851310 _111337 c' R P _60150) (@lem4851315 _111337 R c' P _60150)). Qed.
Lemma lem4851332 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : ((term578 _111337 P c' R _60150) = (term667 _111337 c' P R _60150)) = ((term672 _111337 R c' P _60150) = (term672 _111337 R c' P _60150)).
Proof. exact (MK_COMB (@lem4851288 _111337 R c' P _60150) (@lem4851331 _111337 R c' P _60150)). Qed.
Lemma lem4851334 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4851335 (x : Prop) : (x = x) = True.
Proof. exact (@lem4851334 Prop x). Qed.
Lemma lem4851336 {_111337 : Type'} (R : type686 _111337) (c' : type178 _111337) (P : type180 _111337) (_60150 : type686 _111337) : ((term672 _111337 R c' P _60150) = (term672 _111337 R c' P _60150)) = True.
Proof. exact (@lem4851335 (term672 _111337 R c' P _60150)). Qed.
Lemma lem4851337 {_111337 : Type'} (c' : type178 _111337) (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : ((term578 _111337 P c' R _60150) = (term667 _111337 c' P R _60150)) = True.
Proof. exact (TRANS (@lem4851332 _111337 R c' P _60150) (@lem4851336 _111337 R c' P _60150)). Qed.
Lemma lem4851338 {_111337 : Type'} (c' : type178 _111337) (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : True = ((term578 _111337 P c' R _60150) = (term667 _111337 c' P R _60150)).
Proof. exact (SYM (@lem4851337 _111337 c' P R _60150)). Qed.
Lemma lem4851339 {_111337 : Type'} (c' : type178 _111337) (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term578 _111337 P c' R _60150) = (term667 _111337 c' P R _60150).
Proof. exact (EQ_MP (@lem4851338 _111337 c' P R _60150) (@lem0)). Qed.
Lemma lem4851340 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term667 _111337 c' P R _60150.
Proof. exact (EQ_MP (@lem4851339 _111337 c' P R _60150) (@lem4850582 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4851342 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4851343 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term667 _111337 c' P R _60150) = (term675 _111337 P R c' _60150).
Proof. exact (@lem4851342 (term668 _111337 P R _60150) (term552 _111337 c' _60150)). Qed.
Lemma lem4851345 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4851346 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term676 _111337 P R _60150) = (term677 _111337 P R _60150).
Proof. exact (@lem4851345 (term183 _111337 P _60150) (term50 _111337 R _60150)). Qed.
Lemma lem4851348 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851349 {_111337 : Type'} (P : type180 _111337) (_60150 : type686 _111337) : (term609 _111337 P _60150) = (P _60150).
Proof. exact (@lem4851348 (P _60150)). Qed.
Lemma lem4851350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851351 {_111337 : Type'} (P : type180 _111337) (_60150 : type686 _111337) : (term610 _111337 P _60150) = (term54 _111337 P _60150).
Proof. exact (MK_COMB (@lem4851350) (@lem4851349 _111337 P _60150)). Qed.
Lemma lem4851352 {_111337 : Type'} (R : type686 _111337) (_60150 : type686 _111337) : (term124 _111337 R _60150) = (term124 _111337 R _60150).
Proof. exact (eq_refl (term124 _111337 R _60150)). Qed.
Lemma lem4851353 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term677 _111337 P R _60150) = (term678 _111337 P R _60150).
Proof. exact (MK_COMB (@lem4851351 _111337 P _60150) (@lem4851352 _111337 R _60150)). Qed.
Lemma lem4851354 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term676 _111337 P R _60150) = (term678 _111337 P R _60150).
Proof. exact (TRANS (@lem4851346 _111337 P R _60150) (@lem4851353 _111337 P R _60150)). Qed.
Lemma lem4851355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4851356 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term679 _111337 P R _60150) = (term680 _111337 P R _60150).
Proof. exact (MK_COMB (@lem4851355) (@lem4851354 _111337 P R _60150)). Qed.
Lemma lem4851357 {_111337 : Type'} (c' : type178 _111337) (_60150 : type686 _111337) : (term552 _111337 c' _60150) = (term552 _111337 c' _60150).
Proof. exact (eq_refl (term552 _111337 c' _60150)). Qed.
Lemma lem4851358 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term675 _111337 P R c' _60150) = (term681 _111337 P R c' _60150).
Proof. exact (MK_COMB (@lem4851356 _111337 P R _60150) (@lem4851357 _111337 c' _60150)). Qed.
Lemma lem4851359 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term667 _111337 c' P R _60150) = (term681 _111337 P R c' _60150).
Proof. exact (TRANS (@lem4851343 _111337 P R c' _60150) (@lem4851358 _111337 P R c' _60150)). Qed.
Lemma lem4851361 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term678 _111337 P R u.
Proof. exact (conj (@lem4851227 _111337 u s P Q c' R h2) (@lem4851235 _111337 R u h1)). Qed.
Lemma lem4851363 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term681 _111337 P R c' _60150.
Proof. exact (EQ_MP (@lem4851359 _111337 P R c' _60150) (@lem4851340 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4851364 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term681 _111337 P R c' _60150.
Proof. exact (@lem4851363 _111337 _60150 u s P Q c' R h1). Qed.
Lemma lem4851365 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term681 _111337 P R c' u.
Proof. exact (@lem4851364 _111337 u u s P Q c' R h1). Qed.
Lemma lem4851368 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term552 _111337 c' u.
Proof. exact (@lem4851365 _111337 u s P Q c' R h2 (@lem4851361 _111337 u s P Q c' R h1 h2)). Qed.
Lemma lem4851369 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term682 _111337 c' u.
Proof. exact (fun h0 : term683 _111337 c' u => @lem4851368 _111337 u s P Q c' R h1 h2). Qed.
Lemma lem4851371 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851372 {_111337 : Type'} (c' : type178 _111337) (u : type686 _111337) : (term682 _111337 c' u) = (term552 _111337 c' u).
Proof. exact (@lem4851371 (term552 _111337 c' u)). Qed.
Lemma lem4851373 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term552 _111337 c' u.
Proof. exact (EQ_MP (@lem4851372 _111337 c' u) (@lem4851369 _111337 u s P Q c' R h1 h2)). Qed.
Lemma lem4851379 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4851380 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : (term65 _111337 u Q _60151) = (term627 _111337 Q _60151 u).
Proof. exact (@lem4851379 (Q _60151) (term628 _111337 _60151 u)). Qed.
Lemma lem4851386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4851387 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : (term629 _111337 u Q _60151) = (term630 _111337 Q _60151 u).
Proof. exact (MK_COMB (@lem4851386) (@lem4851380 _111337 Q _60151 u)). Qed.
Lemma lem4851393 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : (term627 _111337 Q _60151 u) = (term627 _111337 Q _60151 u).
Proof. exact (eq_refl (term627 _111337 Q _60151 u)). Qed.
Lemma lem4851394 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : ((term65 _111337 u Q _60151) = (term627 _111337 Q _60151 u)) = ((term627 _111337 Q _60151 u) = (term627 _111337 Q _60151 u)).
Proof. exact (MK_COMB (@lem4851387 _111337 Q _60151 u) (@lem4851393 _111337 Q _60151 u)). Qed.
Lemma lem4851396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4851397 (x : Prop) : (x = x) = True.
Proof. exact (@lem4851396 Prop x). Qed.
Lemma lem4851398 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : ((term627 _111337 Q _60151 u) = (term627 _111337 Q _60151 u)) = True.
Proof. exact (@lem4851397 (term627 _111337 Q _60151 u)). Qed.
Lemma lem4851399 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : ((term65 _111337 u Q _60151) = (term627 _111337 Q _60151 u)) = True.
Proof. exact (TRANS (@lem4851394 _111337 Q _60151 u) (@lem4851398 _111337 Q _60151 u)). Qed.
Lemma lem4851400 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : True = ((term65 _111337 u Q _60151) = (term627 _111337 Q _60151 u)).
Proof. exact (SYM (@lem4851399 _111337 Q _60151 u)). Qed.
Lemma lem4851401 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) (u : type686 _111337) : (term65 _111337 u Q _60151) = (term627 _111337 Q _60151 u).
Proof. exact (EQ_MP (@lem4851400 _111337 Q _60151 u) (@lem0)). Qed.
Lemma lem4851402 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term627 _111337 Q _60151 u.
Proof. exact (EQ_MP (@lem4851401 _111337 Q _60151 u) (@lem4850568 _111337 _60151 u s P Q c' R h1)). Qed.
Lemma lem4851404 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4851405 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (_60151 : _111337 -> Prop) : (term627 _111337 Q _60151 u) = (term631 _111337 u Q _60151).
Proof. exact (@lem4851404 (term628 _111337 _60151 u) (Q _60151)). Qed.
Lemma lem4851407 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851408 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) : (term632 _111337 _60151 u) = (@IN (_111337 -> Prop) _60151 u).
Proof. exact (@lem4851407 (@IN (_111337 -> Prop) _60151 u)). Qed.
Lemma lem4851409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4851410 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) : (term633 _111337 _60151 u) = (term634 _111337 _60151 u).
Proof. exact (MK_COMB (@lem4851409) (@lem4851408 _111337 _60151 u)). Qed.
Lemma lem4851411 {_111337 : Type'} (Q : type686 _111337) (_60151 : _111337 -> Prop) : (Q _60151) = (Q _60151).
Proof. exact (eq_refl (Q _60151)). Qed.
Lemma lem4851412 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (_60151 : _111337 -> Prop) : (term631 _111337 u Q _60151) = (term51 _111337 u Q _60151).
Proof. exact (MK_COMB (@lem4851410 _111337 _60151 u) (@lem4851411 _111337 Q _60151)). Qed.
Lemma lem4851413 {_111337 : Type'} (u : type686 _111337) (Q : type686 _111337) (_60151 : _111337 -> Prop) : (term627 _111337 Q _60151 u) = (term51 _111337 u Q _60151).
Proof. exact (TRANS (@lem4851405 _111337 u Q _60151) (@lem4851412 _111337 u Q _60151)). Qed.
Lemma lem4851416 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term51 _111337 u Q _60151.
Proof. exact (EQ_MP (@lem4851413 _111337 u Q _60151) (@lem4851402 _111337 _60151 u s P Q c' R h1)). Qed.
Lemma lem4851417 {_111337 : Type'} (_60151 : _111337 -> Prop) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term51 _111337 u Q _60151.
Proof. exact (@lem4851416 _111337 _60151 u s P Q c' R h1). Qed.
Lemma lem4851418 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term684 _111337 Q c' u.
Proof. exact (@lem4851417 _111337 (c' u) u s P Q c' R h1). Qed.
Lemma lem4851421 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term685 _111337 Q c' u.
Proof. exact (@lem4851418 _111337 u s P Q c' R h2 (@lem4851373 _111337 u s P Q c' R h1 h2)). Qed.
Lemma lem4851422 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term686 _111337 Q c' u.
Proof. exact (fun h0 : term553 _111337 Q c' u => @lem4851421 _111337 u s P Q c' R h1 h2). Qed.
Lemma lem4851424 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851425 {_111337 : Type'} (Q : type686 _111337) (c' : type178 _111337) (u : type686 _111337) : (term686 _111337 Q c' u) = (term685 _111337 Q c' u).
Proof. exact (@lem4851424 (term685 _111337 Q c' u)). Qed.
Lemma lem4851426 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term685 _111337 Q c' u.
Proof. exact (EQ_MP (@lem4851425 _111337 Q c' u) (@lem4851422 _111337 u s P Q c' R h1 h2)). Qed.
Lemma lem4851442 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4851443 {_111337 : Type'} (R : type686 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term687 _111337 Q c' R _60150) = (term688 _111337 R Q c' _60150).
Proof. exact (@lem4851442 (term50 _111337 R _60150) (term553 _111337 Q c' _60150)). Qed.
Lemma lem4851449 {_111337 : Type'} (P : type180 _111337) (_60150 : type686 _111337) : (term85 _111337 P _60150) = (term85 _111337 P _60150).
Proof. exact (eq_refl (term85 _111337 P _60150)). Qed.
Lemma lem4851450 {_111337 : Type'} (P : type180 _111337) (R : type686 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term579 _111337 P Q c' R _60150) = (term689 _111337 P R Q c' _60150).
Proof. exact (MK_COMB (@lem4851449 _111337 P _60150) (@lem4851443 _111337 R Q c' _60150)). Qed.
Lemma lem4851454 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4851455 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term689 _111337 P R Q c' _60150) = (term690 _111337 R P Q c' _60150).
Proof. exact (@lem4851454 (term50 _111337 R _60150) (term183 _111337 P _60150) (term553 _111337 Q c' _60150)). Qed.
Lemma lem4851471 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term579 _111337 P Q c' R _60150) = (term690 _111337 R P Q c' _60150).
Proof. exact (TRANS (@lem4851450 _111337 P R Q c' _60150) (@lem4851455 _111337 R P Q c' _60150)). Qed.
Lemma lem4851472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4851473 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term691 _111337 P Q c' R _60150) = (term692 _111337 R P Q c' _60150).
Proof. exact (MK_COMB (@lem4851472) (@lem4851471 _111337 R P Q c' _60150)). Qed.
Lemma lem4851489 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term690 _111337 R P Q c' _60150) = (term690 _111337 R P Q c' _60150).
Proof. exact (eq_refl (term690 _111337 R P Q c' _60150)). Qed.
Lemma lem4851490 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : ((term579 _111337 P Q c' R _60150) = (term690 _111337 R P Q c' _60150)) = ((term690 _111337 R P Q c' _60150) = (term690 _111337 R P Q c' _60150)).
Proof. exact (MK_COMB (@lem4851473 _111337 R P Q c' _60150) (@lem4851489 _111337 R P Q c' _60150)). Qed.
Lemma lem4851492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4851493 (x : Prop) : (x = x) = True.
Proof. exact (@lem4851492 Prop x). Qed.
Lemma lem4851494 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : ((term690 _111337 R P Q c' _60150) = (term690 _111337 R P Q c' _60150)) = True.
Proof. exact (@lem4851493 (term690 _111337 R P Q c' _60150)). Qed.
Lemma lem4851495 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : ((term579 _111337 P Q c' R _60150) = (term690 _111337 R P Q c' _60150)) = True.
Proof. exact (TRANS (@lem4851490 _111337 R P Q c' _60150) (@lem4851494 _111337 R P Q c' _60150)). Qed.
Lemma lem4851496 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : True = ((term579 _111337 P Q c' R _60150) = (term690 _111337 R P Q c' _60150)).
Proof. exact (SYM (@lem4851495 _111337 R P Q c' _60150)). Qed.
Lemma lem4851497 {_111337 : Type'} (R : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term579 _111337 P Q c' R _60150) = (term690 _111337 R P Q c' _60150).
Proof. exact (EQ_MP (@lem4851496 _111337 R P Q c' _60150) (@lem0)). Qed.
Lemma lem4851498 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term690 _111337 R P Q c' _60150.
Proof. exact (EQ_MP (@lem4851497 _111337 R P Q c' _60150) (@lem4850596 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4851500 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4851501 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term690 _111337 R P Q c' _60150) = (term693 _111337 P Q c' R _60150).
Proof. exact (@lem4851500 (term559 _111337 P Q c' _60150) (term50 _111337 R _60150)). Qed.
Lemma lem4851503 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4851504 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term694 _111337 P Q c' _60150) = (term695 _111337 P Q c' _60150).
Proof. exact (@lem4851503 (term183 _111337 P _60150) (term553 _111337 Q c' _60150)). Qed.
Lemma lem4851506 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851507 {_111337 : Type'} (P : type180 _111337) (_60150 : type686 _111337) : (term609 _111337 P _60150) = (P _60150).
Proof. exact (@lem4851506 (P _60150)). Qed.
Lemma lem4851508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851509 {_111337 : Type'} (P : type180 _111337) (_60150 : type686 _111337) : (term610 _111337 P _60150) = (term54 _111337 P _60150).
Proof. exact (MK_COMB (@lem4851508) (@lem4851507 _111337 P _60150)). Qed.
Lemma lem4851511 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4851512 {_111337 : Type'} (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term696 _111337 Q c' _60150) = (term685 _111337 Q c' _60150).
Proof. exact (@lem4851511 (term685 _111337 Q c' _60150)). Qed.
Lemma lem4851513 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term695 _111337 P Q c' _60150) = (term697 _111337 P Q c' _60150).
Proof. exact (MK_COMB (@lem4851509 _111337 P _60150) (@lem4851512 _111337 Q c' _60150)). Qed.
Lemma lem4851514 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term694 _111337 P Q c' _60150) = (term697 _111337 P Q c' _60150).
Proof. exact (TRANS (@lem4851504 _111337 P Q c' _60150) (@lem4851513 _111337 P Q c' _60150)). Qed.
Lemma lem4851515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4851516 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (_60150 : type686 _111337) : (term698 _111337 P Q c' _60150) = (term699 _111337 P Q c' _60150).
Proof. exact (MK_COMB (@lem4851515) (@lem4851514 _111337 P Q c' _60150)). Qed.
Lemma lem4851517 {_111337 : Type'} (R : type686 _111337) (_60150 : type686 _111337) : (term50 _111337 R _60150) = (term50 _111337 R _60150).
Proof. exact (eq_refl (term50 _111337 R _60150)). Qed.
Lemma lem4851518 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term693 _111337 P Q c' R _60150) = (term700 _111337 P Q c' R _60150).
Proof. exact (MK_COMB (@lem4851516 _111337 P Q c' _60150) (@lem4851517 _111337 R _60150)). Qed.
Lemma lem4851519 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (_60150 : type686 _111337) : (term690 _111337 R P Q c' _60150) = (term700 _111337 P Q c' R _60150).
Proof. exact (TRANS (@lem4851501 _111337 P Q c' R _60150) (@lem4851518 _111337 P Q c' R _60150)). Qed.
Lemma lem4851521 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term697 _111337 P Q c' u.
Proof. exact (conj (@lem4851220 _111337 u s P Q c' R h2) (@lem4851426 _111337 u s P Q c' R h1 h2)). Qed.
Lemma lem4851523 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term700 _111337 P Q c' R _60150.
Proof. exact (EQ_MP (@lem4851519 _111337 P Q c' R _60150) (@lem4851498 _111337 _60150 u s P Q c' R h1)). Qed.
Lemma lem4851524 {_111337 : Type'} (_60150 : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term700 _111337 P Q c' R _60150.
Proof. exact (@lem4851523 _111337 _60150 u s P Q c' R h1). Qed.
Lemma lem4851525 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term700 _111337 P Q c' R u.
Proof. exact (@lem4851524 _111337 u u s P Q c' R h1). Qed.
Lemma lem4851528 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term124 _111337 R u) (h2 : term417 _111337 u s P Q c' R) : term50 _111337 R u.
Proof. exact (@lem4851525 _111337 u s P Q c' R h2 (@lem4851521 _111337 u s P Q c' R h1 h2)). Qed.
Lemma lem4851529 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term664 _111337 R u.
Proof. exact (fun h0 : term124 _111337 R u => @lem4851528 _111337 u s P Q c' R h0 h1). Qed.
Lemma lem4851531 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851532 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) : (term664 _111337 R u) = (term50 _111337 R u).
Proof. exact (@lem4851531 (term50 _111337 R u)). Qed.
Lemma lem4851533 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term50 _111337 R u.
Proof. exact (EQ_MP (@lem4851532 _111337 R u) (@lem4851529 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851536 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4851538 {_111337 : Type'} (R : type686 _111337) (u : type686 _111337) : (term124 _111337 R u) = (term665 _111337 R u).
Proof. exact (@lem4851536 (term50 _111337 R u)). Qed.
Lemma lem4851541 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term665 _111337 R u.
Proof. exact (EQ_MP (@lem4851538 _111337 R u) (@lem4850540 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851544 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : False.
Proof. exact (@lem4851541 _111337 u s P Q c' R h1 (@lem4851533 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851545 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : term666.
Proof. exact (fun h0 : ~ False => @lem4851544 _111337 u s P Q c' R h1). Qed.
Lemma lem4851547 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4851548 : term666 = False.
Proof. exact (@lem4851547 False). Qed.
Lemma lem4851550 {_111337 : Type'} (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term417 _111337 u s P Q c' R) : False.
Proof. exact (EQ_MP (@lem4851548) (@lem4851545 _111337 u s P Q c' R h1)). Qed.
Lemma lem4851551 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term496 _111337 c t u s P Q c' R) : False.
Proof. exact (or_elim (@lem4850238 _111337 c t u s P Q c' R h1) (fun h0 : term298 _111337 c P Q R t => @lem4851213 _111337 c P Q R t h0) (fun h0 : term417 _111337 u s P Q c' R => @lem4851550 _111337 u s P Q c' R h0)). Qed.
Lemma lem4851552 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term496 _111337 c t u s P Q c' R) : (term496 _111337 c t u s P Q c' R) = False.
Proof. exact (prop_ext (fun h2 : term496 _111337 c t u s P Q c' R => @lem4851551 _111337 c t u s P Q c' R h1) (fun h2 : False => @lem4850238 _111337 c t u s P Q c' R h1)). Qed.
Lemma lem4851553 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (c' : type178 _111337) (R : type686 _111337) (h1 : term496 _111337 c t u s P Q c' R) : False.
Proof. exact (EQ_MP (@lem4851552 _111337 c t u s P Q c' R h1) (@lem4850238 _111337 c t u s P Q c' R h1)). Qed.
Lemma lem4851554 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (u : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term499 _111337 c t u s P Q R) : False.
Proof. exact (ex_elim (@lem4850066 _111337 c t u s P Q R h1) (fun c' : type178 _111337 => fun h0 : term498 _111337 c t u s P Q R c' => @lem4851553 _111337 c t u s P Q c' R h0)). Qed.
Lemma lem4851555 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (s : _111337 -> Prop) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term501 _111337 c t s P Q R) : False.
Proof. exact (ex_elim (@lem4850065 _111337 c t s P Q R h1) (fun u : type686 _111337 => fun h0 : term500 _111337 c t s P Q R u => @lem4851554 _111337 c t u s P Q R h0)). Qed.
Lemma lem4851556 {_111337 : Type'} (c : type598 _111337) (t : type686 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term503 _111337 c t P Q R) : False.
Proof. exact (ex_elim (@lem4850064 _111337 c t P Q R h1) (fun s : _111337 -> Prop => fun h0 : term502 _111337 c t P Q R s => @lem4851555 _111337 c t s P Q R h0)). Qed.
Lemma lem4851557 {_111337 : Type'} (c : type598 _111337) (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term505 _111337 c P Q R) : False.
Proof. exact (ex_elim (@lem4850063 _111337 c P Q R h1) (fun t : type686 _111337 => fun h0 : term504 _111337 c P Q R t => @lem4851556 _111337 c t P Q R h0)). Qed.
Lemma lem4851558 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : False.
Proof. exact (ex_elim (@lem4850062 _111337 P Q R h1) (fun c : type598 _111337 => fun h0 : term506 _111337 P Q R c => @lem4851557 _111337 c P Q R h0)). Qed.
Lemma lem4851559 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : (term32 _111337 P Q R) = False.
Proof. exact (prop_ext (fun h2 : term32 _111337 P Q R => @lem4851558 _111337 P Q R h1) (fun h2 : False => @lem4848969 _111337 P Q R h1)). Qed.
Lemma lem4851560 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : False.
Proof. exact (EQ_MP (@lem4851559 _111337 P Q R h1) (@lem4848969 _111337 P Q R h1)). Qed.
Lemma lem4851561 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term31 _111337 P Q R.
Proof. exact (fun h0 : term32 _111337 P Q R => @lem4851560 _111337 P Q R h0). Qed.
Lemma lem4851562 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term26 _111337 P Q R) = (term29 _111337 P Q R).
Proof. exact (EQ_MP (@lem4848968 _111337 P Q R) (@lem4851561 _111337 P Q R)). Qed.
Lemma lem4851567 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : term41 _111337 Q R.
Proof. exact (fun P : type180 _111337 => @lem4851562 _111337 P Q R). Qed.
Lemma lem4851572 {_111337 : Type'} (R : type686 _111337) : term45 _111337 R.
Proof. exact (fun Q : type686 _111337 => @lem4851567 _111337 Q R). Qed.
Lemma lem4851577 {_111337 : Type'} : term49 _111337.
Proof. exact (fun R : type686 _111337 => @lem4851572 _111337 R). Qed.
Lemma lem4851578 {_111337 : Type'} : term48 _111337.
Proof. exact (EQ_MP (@lem4848964 _111337) (@lem4851577 _111337)). Qed.
Lemma lem4851579 {_111337 : Type'} (R : type686 _111337) : term701 _111337 R.
Proof. exact (@lem4851578 _111337 R). Qed.
Lemma lem4851580 {_111337 : Type'} (R : type686 _111337) : (term701 _111337 R) = (term44 _111337 R).
Proof. exact (eq_refl (term701 _111337 R)). Qed.
Lemma lem4851581 {_111337 : Type'} (R : type686 _111337) : term44 _111337 R.
Proof. exact (EQ_MP (@lem4851580 _111337 R) (@lem4851579 _111337 R)). Qed.
Lemma lem4851582 {_111337 : Type'} (R : type686 _111337) (Q : type686 _111337) : term702 _111337 R Q.
Proof. exact (@lem4851581 _111337 R Q). Qed.
Lemma lem4851583 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : (term702 _111337 R Q) = (term40 _111337 Q R).
Proof. exact (eq_refl (term702 _111337 R Q)). Qed.
Lemma lem4851584 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) : term40 _111337 Q R.
Proof. exact (EQ_MP (@lem4851583 _111337 Q R) (@lem4851582 _111337 R Q)). Qed.
Lemma lem4851585 {_111337 : Type'} (Q : type686 _111337) (R : type686 _111337) (P : type180 _111337) : term703 _111337 Q R P.
Proof. exact (@lem4851584 _111337 Q R P). Qed.
Lemma lem4851586 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term703 _111337 Q R P) = (term31 _111337 P Q R).
Proof. exact (eq_refl (term703 _111337 Q R P)). Qed.
Lemma lem4851587 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term31 _111337 P Q R.
Proof. exact (EQ_MP (@lem4851586 _111337 P Q R) (@lem4851585 _111337 Q R P)). Qed.
Lemma lem4851589 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term31 _111337 P Q R.
Proof. exact (@lem4848739 _111337 P Q R (@lem4851587 _111337 P Q R)). Qed.
Lemma lem4851590 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : False.
Proof. exact (@lem4851589 _111337 P Q R (@lem4848723 _111337 P Q R h1)). Qed.
Lemma lem4851591 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : (term32 _111337 P Q R) = False.
Proof. exact (prop_ext (fun h2 : term32 _111337 P Q R => @lem4851590 _111337 P Q R h1) (fun h2 : False => @lem4848723 _111337 P Q R h1)). Qed.
Lemma lem4851592 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) (h1 : term32 _111337 P Q R) : False.
Proof. exact (EQ_MP (@lem4851591 _111337 P Q R h1) (@lem4848723 _111337 P Q R h1)). Qed.
Lemma lem4851593 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : term31 _111337 P Q R.
Proof. exact (fun h0 : term32 _111337 P Q R => @lem4851592 _111337 P Q R h0). Qed.
Lemma lem4851594 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term26 _111337 P Q R) = (term29 _111337 P Q R).
Proof. exact (EQ_MP (@lem4848722 _111337 P Q R) (@lem4851593 _111337 P Q R)). Qed.
Lemma lem4851595 {_111337 : Type'} (P : type180 _111337) (Q : type686 _111337) (R : type686 _111337) : (term25 _111337 P Q R) = (term29 _111337 P Q R).
Proof. exact (EQ_MP (@lem4848718 _111337 P Q R) (@lem4851594 _111337 P Q R)). Qed.
