Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4845732_term_abbrevs.
Require Import UNION_OF_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Lemma lem4845634 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4845635 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4845636 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4845635 A P) (@lem4845634 A P)). Qed.
Lemma lem4845637 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4845636 A P Q). Qed.
Lemma lem4845638 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4845649 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4845638 A P Q) (@lem4845637 A P Q)). Qed.
Lemma lem4845650 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) : (@UNION_OF _111301 P Q) = (term3 _111301 P Q).
Proof. exact (@lem4845649 _111301 P Q). Qed.
Lemma lem4845667 {_111301 : Type'} (s : _111301 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4845668 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (@UNION_OF _111301 P Q s) = (term4 _111301 P Q s).
Proof. exact (MK_COMB (@lem4845650 _111301 P Q) (@lem4845667 _111301 s)). Qed.
Lemma lem4845670 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4845671 {_111301 : Type'} (f : type686 _111301) (y : _111301 -> Prop) : (term6 _111301 f y) = (f y).
Proof. exact (@lem4845670 (_111301 -> Prop) Prop f y). Qed.
Lemma lem4845672 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term7 _111301 P Q s) = (term4 _111301 P Q s).
Proof. exact (@lem4845671 _111301 (term3 _111301 P Q) s). Qed.
Lemma lem4845673 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term4 _111301 P Q s) = (term8 _111301 P Q s).
Proof. exact (eq_refl (term4 _111301 P Q s)). Qed.
Lemma lem4845674 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) : (term9 _111301 P Q) = (term3 _111301 P Q).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4845673 _111301 P Q s)). Qed.
Lemma lem4845675 {_111301 : Type'} (s : _111301 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4845676 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term7 _111301 P Q s) = (term4 _111301 P Q s).
Proof. exact (MK_COMB (@lem4845674 _111301 P Q) (@lem4845675 _111301 s)). Qed.
Lemma lem4845677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845678 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term10 _111301 P Q s) = (term11 _111301 P Q s).
Proof. exact (MK_COMB (@lem4845677) (@lem4845676 _111301 P Q s)). Qed.
Lemma lem4845679 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term4 _111301 P Q s) = (term8 _111301 P Q s).
Proof. exact (eq_refl (term4 _111301 P Q s)). Qed.
Lemma lem4845680 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : ((term7 _111301 P Q s) = (term4 _111301 P Q s)) = ((term4 _111301 P Q s) = (term8 _111301 P Q s)).
Proof. exact (MK_COMB (@lem4845678 _111301 P Q s) (@lem4845679 _111301 P Q s)). Qed.
Lemma lem4845681 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term4 _111301 P Q s) = (term8 _111301 P Q s).
Proof. exact (EQ_MP (@lem4845680 _111301 P Q s) (@lem4845672 _111301 P Q s)). Qed.
Lemma lem4845698 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (@UNION_OF _111301 P Q s) = (term8 _111301 P Q s).
Proof. exact (TRANS (@lem4845668 _111301 P Q s) (@lem4845681 _111301 P Q s)). Qed.
Lemma lem4845699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4845700 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term12 _111301 P Q s) = (term13 _111301 P Q s).
Proof. exact (MK_COMB (@lem4845699) (@lem4845698 _111301 P Q s)). Qed.
Lemma lem4845701 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4845702 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term14 _111301 P Q R s) = (term15 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4845700 _111301 P Q s) (@lem4845701 _111301 R s)). Qed.
Lemma lem4845705 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term16 _111301 P Q R) = (term17 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4845702 _111301 P Q R s)). Qed.
Lemma lem4845706 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4845707 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term18 _111301 P Q R) = (term19 _111301 P Q R).
Proof. exact (MK_COMB (@lem4845706 _111301) (@lem4845705 _111301 P Q R)). Qed.
Lemma lem4845712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845713 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term20 _111301 P Q R) = (term21 _111301 P Q R).
Proof. exact (MK_COMB (@lem4845712) (@lem4845707 _111301 P Q R)). Qed.
Lemma lem4845728 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term22 _111301 P Q R) = (term22 _111301 P Q R).
Proof. exact (eq_refl (term22 _111301 P Q R)). Qed.
Lemma lem4845729 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term18 _111301 P Q R) = (term22 _111301 P Q R)) = ((term19 _111301 P Q R) = (term22 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4845713 _111301 P Q R) (@lem4845728 _111301 P Q R)). Qed.
Lemma lem4845732 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term19 _111301 P Q R) = (term22 _111301 P Q R)) = ((term18 _111301 P Q R) = (term22 _111301 P Q R)).
Proof. exact (SYM (@lem4845729 _111301 P Q R)). Qed.
