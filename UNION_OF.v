Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_OF_term_abbrevs.
Lemma lem4841025 {A : Type'} : (@UNION_OF A) = (term0 A).
Proof. exact (@UNION_OF_def A). Qed.
Lemma lem4841026 {A : Type'} (_60032 : type180 A) : _60032 = _60032.
Proof. exact (eq_refl _60032). Qed.
Lemma lem4841027 {A : Type'} (_60032 : type180 A) : (@UNION_OF A _60032) = (term1 A _60032).
Proof. exact (MK_COMB (@lem4841025 A) (@lem4841026 A _60032)). Qed.
Lemma lem4841028 {A : Type'} (_60032 : type180 A) : (term1 A _60032) = (term2 A _60032).
Proof. exact (eq_refl (term1 A _60032)). Qed.
Lemma lem4841029 {A : Type'} (_60032 : type180 A) : (@UNION_OF A _60032) = (term2 A _60032).
Proof. exact (TRANS (@lem4841027 A _60032) (@lem4841028 A _60032)). Qed.
Lemma lem4841030 {A : Type'} (_60033 : type686 A) : _60033 = _60033.
Proof. exact (eq_refl _60033). Qed.
Lemma lem4841031 {A : Type'} (_60032 : type180 A) (_60033 : type686 A) : (@UNION_OF A _60032 _60033) = (term3 A _60032 _60033).
Proof. exact (MK_COMB (@lem4841029 A _60032) (@lem4841030 A _60033)). Qed.
Lemma lem4841032 {A : Type'} (_60032 : type180 A) (_60033 : type686 A) : (term3 A _60032 _60033) = (term4 A _60032 _60033).
Proof. exact (eq_refl (term3 A _60032 _60033)). Qed.
Lemma lem4841033 {A : Type'} (_60032 : type180 A) (_60033 : type686 A) : (@UNION_OF A _60032 _60033) = (term4 A _60032 _60033).
Proof. exact (TRANS (@lem4841031 A _60032 _60033) (@lem4841032 A _60032 _60033)). Qed.
Lemma lem4841034 {A : Type'} (_60032 : type180 A) : term5 A _60032.
Proof. exact (fun _60033 : type686 A => @lem4841033 A _60032 _60033). Qed.
Lemma lem4841035 {A : Type'} : term6 A.
Proof. exact (fun _60032 : type180 A => @lem4841034 A _60032). Qed.
Lemma lem4841036 {A : Type'} (_60032 : type180 A) : term7 A _60032.
Proof. exact (@lem4841035 A _60032). Qed.
Lemma lem4841037 {A : Type'} (_60032 : type180 A) : (term7 A _60032) = (term5 A _60032).
Proof. exact (eq_refl (term7 A _60032)). Qed.
Lemma lem4841038 {A : Type'} (_60032 : type180 A) : term5 A _60032.
Proof. exact (EQ_MP (@lem4841037 A _60032) (@lem4841036 A _60032)). Qed.
Lemma lem4841039 {A : Type'} (_60032 : type180 A) (_60033 : type686 A) : term8 A _60032 _60033.
Proof. exact (@lem4841038 A _60032 _60033). Qed.
Lemma lem4841040 {A : Type'} (_60032 : type180 A) (_60033 : type686 A) : (term8 A _60032 _60033) = ((@UNION_OF A _60032 _60033) = (term4 A _60032 _60033)).
Proof. exact (eq_refl (term8 A _60032 _60033)). Qed.
Lemma lem4841041 {A : Type'} (_60032 : type180 A) (_60033 : type686 A) : (@UNION_OF A _60032 _60033) = (term4 A _60032 _60033).
Proof. exact (EQ_MP (@lem4841040 A _60032 _60033) (@lem4841039 A _60032 _60033)). Qed.
Lemma lem4841084 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term4 A P Q).
Proof. exact (@lem4841041 A P Q). Qed.
Lemma lem4841085 {A : Type'} (P : type180 A) : term5 A P.
Proof. exact (fun Q : type686 A => @lem4841084 A P Q). Qed.
Lemma lem4841086 {A : Type'} : term6 A.
Proof. exact (fun P : type180 A => @lem4841085 A P). Qed.
