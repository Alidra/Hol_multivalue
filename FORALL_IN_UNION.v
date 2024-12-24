Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import IN_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3208705 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem3208706 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3208707 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3208706 A s) (@lem3208705 A s)). Qed.
Lemma lem3208708 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3208707 A s t). Qed.
Lemma lem3208709 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3208710 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3208709 A s t) (@lem3208708 A s t)). Qed.
Lemma lem3208711 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3208710 A s t x). Qed.
Lemma lem3208712 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s t x) = ((term5 A x s t) = (term6 A s x t)).
Proof. exact (eq_refl (term4 A s t x)). Qed.
Lemma lem3208735 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3208712 A s x t) (@lem3208711 A s t x)). Qed.
Lemma lem3208736 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem3208735 A s x t). Qed.
Lemma lem3208739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3208740 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (MK_COMB (@lem3208739) (@lem3208736 A s x t)). Qed.
Lemma lem3208741 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3208742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term9 A s t P x) = (term10 A s t P x).
Proof. exact (MK_COMB (@lem3208740 A s x t) (@lem3208741 A P x)). Qed.
Lemma lem3208745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term11 A s t P) = (term12 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3208742 A s t P x)). Qed.
Lemma lem3208746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3208747 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term13 A s t P) = (term14 A s t P).
Proof. exact (MK_COMB (@lem3208746 A) (@lem3208745 A s t P)). Qed.
Lemma lem3208752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208753 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term15 A s t P) = (term16 A s t P).
Proof. exact (MK_COMB (@lem3208752) (@lem3208747 A s t P)). Qed.
Lemma lem3208768 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term17 A s t P).
Proof. exact (eq_refl (term17 A s t P)). Qed.
Lemma lem3208769 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term13 A s t P) = (term17 A s t P)) = ((term14 A s t P) = (term17 A s t P)).
Proof. exact (MK_COMB (@lem3208753 A s t P) (@lem3208768 A s t P)). Qed.
Lemma lem3208772 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term18 A s P) = (term19 A s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3208769 A s t P)). Qed.
Lemma lem3208773 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3208774 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term20 A s P) = (term21 A s P).
Proof. exact (MK_COMB (@lem3208773 A) (@lem3208772 A s P)). Qed.
Lemma lem3208779 {A : Type'} (P : A -> Prop) : (term22 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3208774 A s P)). Qed.
Lemma lem3208780 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3208781 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem3208780 A) (@lem3208779 A P)). Qed.
Lemma lem3208786 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3208781 A P)). Qed.
Lemma lem3208787 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3208788 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem3208787 A) (@lem3208786 A)). Qed.
Lemma lem3208793 {A : Type'} : (term29 A) = (term28 A).
Proof. exact (SYM (@lem3208788 A)). Qed.
Lemma lem3208795 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3208796 {A : Type'} : (term29 A) = (term31 A).
Proof. exact (@lem3208795 (term29 A)). Qed.
Lemma lem3208797 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (SYM (@lem3208796 A)). Qed.
Lemma lem3208798 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3208801 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3208802 {A : Type'} : term33 A.
Proof. exact (fun h0 : term31 A => @lem3208801 A h0). Qed.
Lemma lem3208803 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3208804 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3208805 {A : Type'} (h1 : term31 A) (h2 : term33 A) : term31 A.
Proof. exact (@lem3208803 A h2 (@lem3208804 A h1)). Qed.
Lemma lem3208806 {A : Type'} (h1 : term31 A) : term34 A.
Proof. exact (fun h0 : term33 A => @lem3208805 A h1 h0). Qed.
Lemma lem3208807 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3208808 {A : Type'} (h1 : term31 A) (h2 : term33 A) : term31 A.
Proof. exact (@lem3208806 A h1 (@lem3208807 A h2)). Qed.
Lemma lem3208809 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (fun h0 : term31 A => @lem3208808 A h0 h1). Qed.
Lemma lem3208810 {A : Type'} : term35 A.
Proof. exact (fun h0 : term33 A => @lem3208809 A h0). Qed.
Lemma lem3208813 {A : Type'} : term33 A.
Proof. exact (@lem3208810 A (@lem3208802 A)). Qed.
Lemma lem3208814 {A : Type'} : term33 A.
Proof. exact (@lem3208813 A). Qed.
Lemma lem3208816 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3208817 {A : Type'} : (term31 A) = (term36 A).
Proof. exact (@lem3208816 (term32 A)). Qed.
Lemma lem3208819 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3208820 {A : Type'} : (term36 A) = (term29 A).
Proof. exact (@lem3208819 (term29 A)). Qed.
Lemma lem3208859 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (TRANS (@lem3208817 A) (@lem3208820 A)). Qed.
Lemma lem3208864 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term38 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term38 A t P x)). Qed.
Lemma lem3208865 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term39 A t P) = (term39 A t P).
Proof. exact (fun_ext (fun x : A => @lem3208864 A t P x)). Qed.
Lemma lem3208866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3208867 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term40 A t P) = (term40 A t P).
Proof. exact (MK_COMB (@lem3208866 A) (@lem3208865 A t P)). Qed.
Lemma lem3208872 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem3208873 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term39 A s P) = (term39 A s P).
Proof. exact (fun_ext (fun x : A => @lem3208872 A s P x)). Qed.
Lemma lem3208874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3208875 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term40 A s P) = (term40 A s P).
Proof. exact (MK_COMB (@lem3208874 A) (@lem3208873 A s P)). Qed.
Lemma lem3208876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3208877 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term41 A s P) = (term41 A s P).
Proof. exact (MK_COMB (@lem3208876) (@lem3208875 A s P)). Qed.
Lemma lem3208878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term17 A s t P).
Proof. exact (MK_COMB (@lem3208877 A s P) (@lem3208867 A t P)). Qed.
Lemma lem3208887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term10 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term10 A s t P x)). Qed.
Lemma lem3208888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term12 A s t P) = (term12 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3208887 A s t P x)). Qed.
Lemma lem3208889 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3208890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term14 A s t P) = (term14 A s t P).
Proof. exact (MK_COMB (@lem3208889 A) (@lem3208888 A s t P)). Qed.
Lemma lem3208891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208892 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term16 A s t P) = (term16 A s t P).
Proof. exact (MK_COMB (@lem3208891) (@lem3208890 A s t P)). Qed.
Lemma lem3208893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term14 A s t P) = (term17 A s t P)) = ((term14 A s t P) = (term17 A s t P)).
Proof. exact (MK_COMB (@lem3208892 A s t P) (@lem3208878 A s t P)). Qed.
Lemma lem3208894 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term19 A s P) = (term19 A s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3208893 A s t P)). Qed.
Lemma lem3208895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3208896 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term21 A s P) = (term21 A s P).
Proof. exact (MK_COMB (@lem3208895 A) (@lem3208894 A s P)). Qed.
Lemma lem3208897 {A : Type'} (P : A -> Prop) : (term23 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3208896 A s P)). Qed.
Lemma lem3208898 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3208899 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem3208898 A) (@lem3208897 A P)). Qed.
Lemma lem3208900 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3208899 A P)). Qed.
Lemma lem3208901 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3208902 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem3208901 A) (@lem3208900 A)). Qed.
Lemma lem3208951 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (TRANS (@lem3208859 A) (@lem3208902 A)). Qed.
Lemma lem3208952 {A : Type'} : (term29 A) = (term31 A).
Proof. exact (SYM (@lem3208951 A)). Qed.
Lemma lem3208954 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3208955 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term14 A s t P) = (term17 A s t P)) = (term42 A s t P).
Proof. exact (@lem3208954 ((term14 A s t P) = (term17 A s t P))). Qed.
Lemma lem3208956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term42 A s t P) = ((term14 A s t P) = (term17 A s t P)).
Proof. exact (SYM (@lem3208955 A s t P)). Qed.
Lemma lem3208957 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : term43 A s t P.
Proof. exact (h1). Qed.
Lemma lem3208966 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term45 A s x t).
Proof. exact (@lem17160 (@IN A x s) (@IN A x t)). Qed.
Lemma lem3208971 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3208976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term46 A s t P x) = (term47 A s t P x).
Proof. exact (@lem17362 (term6 A s x t) (P x)). Qed.
Lemma lem3208977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3208978 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term48 A s x t) = (term49 A s x t).
Proof. exact (MK_COMB (@lem3208977) (@lem3208966 A s x t)). Qed.
Lemma lem3208979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term50 A s t P x) = (term51 A s t P x).
Proof. exact (MK_COMB (@lem3208978 A s x t) (@lem3208971 A P x)). Qed.
Lemma lem3208980 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term10 A s t P x) = (term50 A s t P x).
Proof. exact (@lem17265 (term6 A s x t) (P x)). Qed.
Lemma lem3208981 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term10 A s t P x) = (term51 A s t P x).
Proof. exact (TRANS (@lem3208980 A s t P x) (@lem3208979 A s t P x)). Qed.
Lemma lem3208982 {A : Type'} (P : A -> Prop) : (term52 A P) = (term53 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3208983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term54 A s t P) = (term55 A s t P).
Proof. exact (@lem3208982 A (term12 A s t P)). Qed.
Lemma lem3208984 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term56 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term56 A s t P x)). Qed.
Lemma lem3208985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3208986 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term57 A s t P x) = (term46 A s t P x).
Proof. exact (MK_COMB (@lem3208985) (@lem3208984 A s t P x)). Qed.
Lemma lem3208987 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term57 A s t P x) = (term47 A s t P x).
Proof. exact (TRANS (@lem3208986 A s t P x) (@lem3208976 A s t P x)). Qed.
Lemma lem3208988 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term58 A s t P) = (term59 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3208987 A s t P x)). Qed.
Lemma lem3208989 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3208990 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term55 A s t P) = (term60 A s t P).
Proof. exact (MK_COMB (@lem3208989 A) (@lem3208988 A s t P)). Qed.
Lemma lem3208991 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term54 A s t P) = (term60 A s t P).
Proof. exact (TRANS (@lem3208983 A s t P) (@lem3208990 A s t P)). Qed.
Lemma lem3208992 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term12 A s t P) = (term61 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3208981 A s t P x)). Qed.
Lemma lem3208993 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3208994 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term14 A s t P) = (term62 A s t P).
Proof. exact (MK_COMB (@lem3208993 A) (@lem3208992 A s t P)). Qed.
Lemma lem3209003 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term63 A s P x) = (term64 A s P x).
Proof. exact (@lem17362 (@IN A x s) (P x)). Qed.
Lemma lem3209008 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term65 A s P x).
Proof. exact (@lem17265 (@IN A x s) (P x)). Qed.
Lemma lem3209009 {A : Type'} (P : A -> Prop) : (term52 A P) = (term53 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3209010 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term66 A s P) = (term67 A s P).
Proof. exact (@lem3209009 A (term39 A s P)). Qed.
Lemma lem3209011 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term68 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term68 A s P x)). Qed.
Lemma lem3209012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3209013 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term69 A s P x) = (term63 A s P x).
Proof. exact (MK_COMB (@lem3209012) (@lem3209011 A s P x)). Qed.
Lemma lem3209014 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term69 A s P x) = (term64 A s P x).
Proof. exact (TRANS (@lem3209013 A s P x) (@lem3209003 A s P x)). Qed.
Lemma lem3209015 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term70 A s P) = (term71 A s P).
Proof. exact (fun_ext (fun x : A => @lem3209014 A s P x)). Qed.
Lemma lem3209016 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209017 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term67 A s P) = (term72 A s P).
Proof. exact (MK_COMB (@lem3209016 A) (@lem3209015 A s P)). Qed.
Lemma lem3209018 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term66 A s P) = (term72 A s P).
Proof. exact (TRANS (@lem3209010 A s P) (@lem3209017 A s P)). Qed.
Lemma lem3209019 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term39 A s P) = (term73 A s P).
Proof. exact (fun_ext (fun x : A => @lem3209008 A s P x)). Qed.
Lemma lem3209020 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209021 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term40 A s P) = (term74 A s P).
Proof. exact (MK_COMB (@lem3209020 A) (@lem3209019 A s P)). Qed.
Lemma lem3209030 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term63 A t P x) = (term64 A t P x).
Proof. exact (@lem17362 (@IN A x t) (P x)). Qed.
Lemma lem3209035 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term38 A t P x) = (term65 A t P x).
Proof. exact (@lem17265 (@IN A x t) (P x)). Qed.
Lemma lem3209036 {A : Type'} (P : A -> Prop) : (term52 A P) = (term53 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3209037 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term66 A t P) = (term67 A t P).
Proof. exact (@lem3209036 A (term39 A t P)). Qed.
Lemma lem3209038 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term68 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term68 A t P x)). Qed.
Lemma lem3209039 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3209040 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term69 A t P x) = (term63 A t P x).
Proof. exact (MK_COMB (@lem3209039) (@lem3209038 A t P x)). Qed.
Lemma lem3209041 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term69 A t P x) = (term64 A t P x).
Proof. exact (TRANS (@lem3209040 A t P x) (@lem3209030 A t P x)). Qed.
Lemma lem3209042 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term70 A t P) = (term71 A t P).
Proof. exact (fun_ext (fun x : A => @lem3209041 A t P x)). Qed.
Lemma lem3209043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209044 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term67 A t P) = (term72 A t P).
Proof. exact (MK_COMB (@lem3209043 A) (@lem3209042 A t P)). Qed.
Lemma lem3209045 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term66 A t P) = (term72 A t P).
Proof. exact (TRANS (@lem3209037 A t P) (@lem3209044 A t P)). Qed.
Lemma lem3209046 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term39 A t P) = (term73 A t P).
Proof. exact (fun_ext (fun x : A => @lem3209035 A t P x)). Qed.
Lemma lem3209047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209048 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term40 A t P) = (term74 A t P).
Proof. exact (MK_COMB (@lem3209047 A) (@lem3209046 A t P)). Qed.
Lemma lem3209049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209050 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term75 A s P) = (term76 A s P).
Proof. exact (MK_COMB (@lem3209049) (@lem3209018 A s P)). Qed.
Lemma lem3209051 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term77 A s t P) = (term78 A s t P).
Proof. exact (MK_COMB (@lem3209050 A s P) (@lem3209045 A t P)). Qed.
Lemma lem3209052 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term79 A s t P) = (term77 A s t P).
Proof. exact (@lem17045 (term40 A s P) (term40 A t P)). Qed.
Lemma lem3209053 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term79 A s t P) = (term78 A s t P).
Proof. exact (TRANS (@lem3209052 A s t P) (@lem3209051 A s t P)). Qed.
Lemma lem3209054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209055 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term41 A s P) = (term80 A s P).
Proof. exact (MK_COMB (@lem3209054) (@lem3209021 A s P)). Qed.
Lemma lem3209056 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term81 A s t P).
Proof. exact (MK_COMB (@lem3209055 A s P) (@lem3209048 A t P)). Qed.
Lemma lem3209057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209058 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term82 A s t P) = (term83 A s t P).
Proof. exact (MK_COMB (@lem3209057) (@lem3208991 A s t P)). Qed.
Lemma lem3209059 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term84 A s t P) = (term85 A s t P).
Proof. exact (MK_COMB (@lem3209058 A s t P) (@lem3209056 A s t P)). Qed.
Lemma lem3209060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209061 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term86 A s t P) = (term87 A s t P).
Proof. exact (MK_COMB (@lem3209060) (@lem3208994 A s t P)). Qed.
Lemma lem3209062 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term88 A s t P) = (term89 A s t P).
Proof. exact (MK_COMB (@lem3209061 A s t P) (@lem3209053 A s t P)). Qed.
Lemma lem3209063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209064 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term90 A s t P) = (term91 A s t P).
Proof. exact (MK_COMB (@lem3209063) (@lem3209062 A s t P)). Qed.
Lemma lem3209065 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term92 A s t P) = (term93 A s t P).
Proof. exact (MK_COMB (@lem3209064 A s t P) (@lem3209059 A s t P)). Qed.
Lemma lem3209066 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term43 A s t P) = (term92 A s t P).
Proof. exact (@lem17646 (term14 A s t P) (term17 A s t P)). Qed.
Lemma lem3209067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term43 A s t P) = (term93 A s t P).
Proof. exact (TRANS (@lem3209066 A s t P) (@lem3209065 A s t P)). Qed.
Lemma lem3209310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3209311 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (@lem3209310 A P Q). Qed.
Lemma lem3209312 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term96 A s t P) = (term97 A s t P).
Proof. exact (@lem3209311 A (term71 A s P) (term71 A t P)). Qed.
Lemma lem3209313 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term98 A s P x) = (term64 A s P x).
Proof. exact (eq_refl (term98 A s P x)). Qed.
Lemma lem3209314 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term99 A s P) = (term71 A s P).
Proof. exact (fun_ext (fun x : A => @lem3209313 A s P x)). Qed.
Lemma lem3209315 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209316 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term100 A s P) = (term72 A s P).
Proof. exact (MK_COMB (@lem3209315 A) (@lem3209314 A s P)). Qed.
Lemma lem3209317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209318 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term101 A s P) = (term76 A s P).
Proof. exact (MK_COMB (@lem3209317) (@lem3209316 A s P)). Qed.
Lemma lem3209319 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term98 A t P x) = (term64 A t P x).
Proof. exact (eq_refl (term98 A t P x)). Qed.
Lemma lem3209320 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term99 A t P) = (term71 A t P).
Proof. exact (fun_ext (fun x : A => @lem3209319 A t P x)). Qed.
Lemma lem3209321 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209322 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term100 A t P) = (term72 A t P).
Proof. exact (MK_COMB (@lem3209321 A) (@lem3209320 A t P)). Qed.
Lemma lem3209323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term96 A s t P) = (term78 A s t P).
Proof. exact (MK_COMB (@lem3209318 A s P) (@lem3209322 A t P)). Qed.
Lemma lem3209324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209325 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term102 A s t P) = (term103 A s t P).
Proof. exact (MK_COMB (@lem3209324) (@lem3209323 A s t P)). Qed.
Lemma lem3209326 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term98 A s P x) = (term64 A s P x).
Proof. exact (eq_refl (term98 A s P x)). Qed.
Lemma lem3209327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209328 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term104 A s P x) = (term105 A s P x).
Proof. exact (MK_COMB (@lem3209327) (@lem3209326 A s P x)). Qed.
Lemma lem3209329 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term98 A t P x) = (term64 A t P x).
Proof. exact (eq_refl (term98 A t P x)). Qed.
Lemma lem3209330 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term106 A s t P x) = (term107 A s t P x).
Proof. exact (MK_COMB (@lem3209328 A s P x) (@lem3209329 A t P x)). Qed.
Lemma lem3209331 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term108 A s t P) = (term109 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209330 A s t P x)). Qed.
Lemma lem3209332 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209333 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term97 A s t P) = (term110 A s t P).
Proof. exact (MK_COMB (@lem3209332 A) (@lem3209331 A s t P)). Qed.
Lemma lem3209334 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term96 A s t P) = (term97 A s t P)) = ((term78 A s t P) = (term110 A s t P)).
Proof. exact (MK_COMB (@lem3209325 A s t P) (@lem3209333 A s t P)). Qed.
Lemma lem3209335 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term78 A s t P) = (term110 A s t P).
Proof. exact (EQ_MP (@lem3209334 A s t P) (@lem3209312 A s t P)). Qed.
Lemma lem3209336 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term87 A s t P) = (term87 A s t P).
Proof. exact (eq_refl (term87 A s t P)). Qed.
Lemma lem3209337 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term89 A s t P) = (term111 A s t P).
Proof. exact (MK_COMB (@lem3209336 A s t P) (@lem3209335 A s t P)). Qed.
Lemma lem3209339 {A : Type'} (P : Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3209340 {A : Type'} (P : Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (@lem3209339 A P Q). Qed.
Lemma lem3209341 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term114 A s t P) = (term115 A s t P).
Proof. exact (@lem3209340 A (term62 A s t P) (term109 A s t P)). Qed.
Lemma lem3209342 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term116 A s t P x) = (term107 A s t P x).
Proof. exact (eq_refl (term116 A s t P x)). Qed.
Lemma lem3209343 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term117 A s t P) = (term109 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209342 A s t P x)). Qed.
Lemma lem3209344 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209345 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term118 A s t P) = (term110 A s t P).
Proof. exact (MK_COMB (@lem3209344 A) (@lem3209343 A s t P)). Qed.
Lemma lem3209346 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term87 A s t P) = (term87 A s t P).
Proof. exact (eq_refl (term87 A s t P)). Qed.
Lemma lem3209347 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term114 A s t P) = (term111 A s t P).
Proof. exact (MK_COMB (@lem3209346 A s t P) (@lem3209345 A s t P)). Qed.
Lemma lem3209348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209349 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term119 A s t P) = (term120 A s t P).
Proof. exact (MK_COMB (@lem3209348) (@lem3209347 A s t P)). Qed.
Lemma lem3209350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term116 A s t P x) = (term107 A s t P x).
Proof. exact (eq_refl (term116 A s t P x)). Qed.
Lemma lem3209351 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term87 A s t P) = (term87 A s t P).
Proof. exact (eq_refl (term87 A s t P)). Qed.
Lemma lem3209352 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term121 A s t P x) = (term122 A s t P x).
Proof. exact (MK_COMB (@lem3209351 A s t P) (@lem3209350 A s t P x)). Qed.
Lemma lem3209353 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term123 A s t P) = (term124 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209352 A s t P x)). Qed.
Lemma lem3209354 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209355 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term115 A s t P) = (term125 A s t P).
Proof. exact (MK_COMB (@lem3209354 A) (@lem3209353 A s t P)). Qed.
Lemma lem3209356 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term114 A s t P) = (term115 A s t P)) = ((term111 A s t P) = (term125 A s t P)).
Proof. exact (MK_COMB (@lem3209349 A s t P) (@lem3209355 A s t P)). Qed.
Lemma lem3209357 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term111 A s t P) = (term125 A s t P).
Proof. exact (EQ_MP (@lem3209356 A s t P) (@lem3209341 A s t P)). Qed.
Lemma lem3209358 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term89 A s t P) = (term125 A s t P).
Proof. exact (TRANS (@lem3209337 A s t P) (@lem3209357 A s t P)). Qed.
Lemma lem3209359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209360 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term91 A s t P) = (term126 A s t P).
Proof. exact (MK_COMB (@lem3209359) (@lem3209358 A s t P)). Qed.
Lemma lem3209362 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3209363 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (@lem3209362 A P Q). Qed.
Lemma lem3209364 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term129 A s t P) = (term130 A s t P).
Proof. exact (@lem3209363 A (term59 A s t P) (term81 A s t P)). Qed.
Lemma lem3209365 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term131 A s t P x) = (term47 A s t P x).
Proof. exact (eq_refl (term131 A s t P x)). Qed.
Lemma lem3209366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term132 A s t P) = (term59 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209365 A s t P x)). Qed.
Lemma lem3209367 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term133 A s t P) = (term60 A s t P).
Proof. exact (MK_COMB (@lem3209367 A) (@lem3209366 A s t P)). Qed.
Lemma lem3209369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209370 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term134 A s t P) = (term83 A s t P).
Proof. exact (MK_COMB (@lem3209369) (@lem3209368 A s t P)). Qed.
Lemma lem3209371 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term81 A s t P) = (term81 A s t P).
Proof. exact (eq_refl (term81 A s t P)). Qed.
Lemma lem3209372 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term129 A s t P) = (term85 A s t P).
Proof. exact (MK_COMB (@lem3209370 A s t P) (@lem3209371 A s t P)). Qed.
Lemma lem3209373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209374 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term135 A s t P) = (term136 A s t P).
Proof. exact (MK_COMB (@lem3209373) (@lem3209372 A s t P)). Qed.
Lemma lem3209375 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term131 A s t P x) = (term47 A s t P x).
Proof. exact (eq_refl (term131 A s t P x)). Qed.
Lemma lem3209376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209377 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term137 A s t P x) = (term138 A s t P x).
Proof. exact (MK_COMB (@lem3209376) (@lem3209375 A s t P x)). Qed.
Lemma lem3209378 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term81 A s t P) = (term81 A s t P).
Proof. exact (eq_refl (term81 A s t P)). Qed.
Lemma lem3209379 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term139 A x s t P) = (term140 A x s t P).
Proof. exact (MK_COMB (@lem3209377 A s t P x) (@lem3209378 A s t P)). Qed.
Lemma lem3209380 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term141 A s t P) = (term142 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209379 A x s t P)). Qed.
Lemma lem3209381 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209382 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term130 A s t P) = (term143 A s t P).
Proof. exact (MK_COMB (@lem3209381 A) (@lem3209380 A s t P)). Qed.
Lemma lem3209383 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term129 A s t P) = (term130 A s t P)) = ((term85 A s t P) = (term143 A s t P)).
Proof. exact (MK_COMB (@lem3209374 A s t P) (@lem3209382 A s t P)). Qed.
Lemma lem3209384 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term85 A s t P) = (term143 A s t P).
Proof. exact (EQ_MP (@lem3209383 A s t P) (@lem3209364 A s t P)). Qed.
Lemma lem3209385 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term93 A s t P) = (term144 A s t P).
Proof. exact (MK_COMB (@lem3209360 A s t P) (@lem3209384 A s t P)). Qed.
Lemma lem3209387 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3209388 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (@lem3209387 A P Q). Qed.
Lemma lem3209389 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term145 A s t P) = (term146 A s t P).
Proof. exact (@lem3209388 A (term124 A s t P) (term142 A s t P)). Qed.
Lemma lem3209390 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term147 A s t P x) = (term122 A s t P x).
Proof. exact (eq_refl (term147 A s t P x)). Qed.
Lemma lem3209391 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term148 A s t P) = (term124 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209390 A s t P x)). Qed.
Lemma lem3209392 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209393 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term149 A s t P) = (term125 A s t P).
Proof. exact (MK_COMB (@lem3209392 A) (@lem3209391 A s t P)). Qed.
Lemma lem3209394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209395 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term150 A s t P) = (term126 A s t P).
Proof. exact (MK_COMB (@lem3209394) (@lem3209393 A s t P)). Qed.
Lemma lem3209396 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term151 A s t P x) = (term140 A x s t P).
Proof. exact (eq_refl (term151 A s t P x)). Qed.
Lemma lem3209397 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term152 A s t P) = (term142 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209396 A x s t P)). Qed.
Lemma lem3209398 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209399 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term153 A s t P) = (term143 A s t P).
Proof. exact (MK_COMB (@lem3209398 A) (@lem3209397 A s t P)). Qed.
Lemma lem3209400 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term145 A s t P) = (term144 A s t P).
Proof. exact (MK_COMB (@lem3209395 A s t P) (@lem3209399 A s t P)). Qed.
Lemma lem3209401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209402 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term154 A s t P) = (term155 A s t P).
Proof. exact (MK_COMB (@lem3209401) (@lem3209400 A s t P)). Qed.
Lemma lem3209403 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term147 A s t P x) = (term122 A s t P x).
Proof. exact (eq_refl (term147 A s t P x)). Qed.
Lemma lem3209404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209405 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term156 A s t P x) = (term157 A s t P x).
Proof. exact (MK_COMB (@lem3209404) (@lem3209403 A s t P x)). Qed.
Lemma lem3209406 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term151 A s t P x) = (term140 A x s t P).
Proof. exact (eq_refl (term151 A s t P x)). Qed.
Lemma lem3209407 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term158 A s t P x) = (term159 A x s t P).
Proof. exact (MK_COMB (@lem3209405 A s t P x) (@lem3209406 A x s t P)). Qed.
Lemma lem3209408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term160 A s t P) = (term161 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209407 A x s t P)). Qed.
Lemma lem3209409 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3209410 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term146 A s t P) = (term162 A s t P).
Proof. exact (MK_COMB (@lem3209409 A) (@lem3209408 A s t P)). Qed.
Lemma lem3209411 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term145 A s t P) = (term146 A s t P)) = ((term144 A s t P) = (term162 A s t P)).
Proof. exact (MK_COMB (@lem3209402 A s t P) (@lem3209410 A s t P)). Qed.
Lemma lem3209412 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term144 A s t P) = (term162 A s t P).
Proof. exact (EQ_MP (@lem3209411 A s t P) (@lem3209389 A s t P)). Qed.
Lemma lem3209414 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term93 A s t P) = (term162 A s t P).
Proof. exact (TRANS (@lem3209385 A s t P) (@lem3209412 A s t P)). Qed.
Lemma lem3209415 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term43 A s t P) = (term162 A s t P).
Proof. exact (TRANS (@lem3209067 A s t P) (@lem3209414 A s t P)). Qed.
Lemma lem3209416 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : term162 A s t P.
Proof. exact (EQ_MP (@lem3209415 A s t P) (@lem3208957 A s t P h1)). Qed.
Lemma lem3209417 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term159 A x s t P) : term159 A x s t P.
Proof. exact (h1). Qed.
Lemma lem3209430 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term65 A t P x) = (term65 A t P x).
Proof. exact (eq_refl (term65 A t P x)). Qed.
Lemma lem3209431 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term73 A t P) = (term73 A t P).
Proof. exact (fun_ext (fun x : A => @lem3209430 A t P x)). Qed.
Lemma lem3209432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209433 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term74 A t P) = (term74 A t P).
Proof. exact (MK_COMB (@lem3209432 A) (@lem3209431 A t P)). Qed.
Lemma lem3209446 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term65 A s P x) = (term65 A s P x).
Proof. exact (eq_refl (term65 A s P x)). Qed.
Lemma lem3209447 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term73 A s P) = (term73 A s P).
Proof. exact (fun_ext (fun x : A => @lem3209446 A s P x)). Qed.
Lemma lem3209448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209449 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term74 A s P) = (term74 A s P).
Proof. exact (MK_COMB (@lem3209448 A) (@lem3209447 A s P)). Qed.
Lemma lem3209450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209451 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term80 A s P) = (term80 A s P).
Proof. exact (MK_COMB (@lem3209450) (@lem3209449 A s P)). Qed.
Lemma lem3209452 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term81 A s t P) = (term81 A s t P).
Proof. exact (MK_COMB (@lem3209451 A s P) (@lem3209433 A t P)). Qed.
Lemma lem3209475 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term138 A s t P x) = (term138 A s t P x).
Proof. exact (eq_refl (term138 A s t P x)). Qed.
Lemma lem3209476 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term140 A x s t P) = (term140 A x s t P).
Proof. exact (MK_COMB (@lem3209475 A s t P x) (@lem3209452 A s t P)). Qed.
Lemma lem3209505 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term107 A s t P x) = (term107 A s t P x).
Proof. exact (eq_refl (term107 A s t P x)). Qed.
Lemma lem3209528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term51 A s t P x) = (term51 A s t P x).
Proof. exact (eq_refl (term51 A s t P x)). Qed.
Lemma lem3209529 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term61 A s t P) = (term61 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209528 A s t P x)). Qed.
Lemma lem3209530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term62 A s t P) = (term62 A s t P).
Proof. exact (MK_COMB (@lem3209530 A) (@lem3209529 A s t P)). Qed.
Lemma lem3209532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3209533 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term87 A s t P) = (term87 A s t P).
Proof. exact (MK_COMB (@lem3209532) (@lem3209531 A s t P)). Qed.
Lemma lem3209534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term122 A s t P x) = (term122 A s t P x).
Proof. exact (MK_COMB (@lem3209533 A s t P) (@lem3209505 A s t P x)). Qed.
Lemma lem3209535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3209536 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term157 A s t P x) = (term157 A s t P x).
Proof. exact (MK_COMB (@lem3209535) (@lem3209534 A s t P x)). Qed.
Lemma lem3209537 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term159 A x s t P) = (term159 A x s t P).
Proof. exact (MK_COMB (@lem3209536 A s t P x) (@lem3209476 A x s t P)). Qed.
Lemma lem3209538 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term159 A x s t P) : term159 A x s t P.
Proof. exact (EQ_MP (@lem3209537 A x s t P) (@lem3209417 A x s t P h1)). Qed.
Lemma lem3209539 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term122 A s t P x.
Proof. exact (h1). Qed.
Lemma lem3209540 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term140 A x s t P.
Proof. exact (h1). Qed.
Lemma lem3209541 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term107 A s t P x.
Proof. exact (proj2 (@lem3209539 A s t P x h1)). Qed.
Lemma lem3209542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term62 A s t P.
Proof. exact (proj1 (@lem3209539 A s t P x h1)). Qed.
Lemma lem3209543 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A s P x) : term64 A s P x.
Proof. exact (h1). Qed.
Lemma lem3209544 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A t P x) : term64 A t P x.
Proof. exact (h1). Qed.
Lemma lem3209549 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term81 A s t P.
Proof. exact (proj2 (@lem3209540 A x s t P h1)). Qed.
Lemma lem3209550 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term47 A s t P x.
Proof. exact (proj1 (@lem3209540 A x s t P h1)). Qed.
Lemma lem3209551 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term74 A t P.
Proof. exact (proj2 (@lem3209549 A x s t P h1)). Qed.
Lemma lem3209552 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term74 A s P.
Proof. exact (proj1 (@lem3209549 A x s t P h1)). Qed.
Lemma lem3209554 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term6 A s x t.
Proof. exact (proj1 (@lem3209550 A x s t P h1)). Qed.
Lemma lem3209574 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term51 A s t P x) = (term163 A s t P x).
Proof. exact (@lem19699 (term164 A x s) (term164 A x t) (P x)). Qed.
Lemma lem3209575 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term61 A s t P) = (term165 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209574 A s t P x)). Qed.
Lemma lem3209576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209578 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term62 A s t P) = (term166 A s t P).
Proof. exact (MK_COMB (@lem3209576 A) (@lem3209575 A s t P)). Qed.
Lemma lem3209579 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term166 A s t P.
Proof. exact (EQ_MP (@lem3209578 A s t P) (@lem3209542 A s t P x h1)). Qed.
Lemma lem3209605 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term51 A s t P x) = (term163 A s t P x).
Proof. exact (@lem19699 (term164 A x s) (term164 A x t) (P x)). Qed.
Lemma lem3209606 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term61 A s t P) = (term165 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3209605 A s t P x)). Qed.
Lemma lem3209607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209609 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term62 A s t P) = (term166 A s t P).
Proof. exact (MK_COMB (@lem3209607 A) (@lem3209606 A s t P)). Qed.
Lemma lem3209610 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term166 A s t P.
Proof. exact (EQ_MP (@lem3209609 A s t P) (@lem3209542 A s t P x h1)). Qed.
Lemma lem3209626 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term65 A s P x) = (term65 A s P x).
Proof. exact (eq_refl (term65 A s P x)). Qed.
Lemma lem3209627 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term73 A s P) = (term73 A s P).
Proof. exact (fun_ext (fun x : A => @lem3209626 A s P x)). Qed.
Lemma lem3209628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209630 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term74 A s P) = (term74 A s P).
Proof. exact (MK_COMB (@lem3209628 A) (@lem3209627 A s P)). Qed.
Lemma lem3209631 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term74 A s P.
Proof. exact (EQ_MP (@lem3209630 A s P) (@lem3209552 A x s t P h1)). Qed.
Lemma lem3209652 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3209673 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term65 A t P x) = (term65 A t P x).
Proof. exact (eq_refl (term65 A t P x)). Qed.
Lemma lem3209674 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term73 A t P) = (term73 A t P).
Proof. exact (fun_ext (fun x : A => @lem3209673 A t P x)). Qed.
Lemma lem3209675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3209677 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term74 A t P) = (term74 A t P).
Proof. exact (MK_COMB (@lem3209675 A) (@lem3209674 A t P)). Qed.
Lemma lem3209678 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term74 A t P.
Proof. exact (EQ_MP (@lem3209677 A t P) (@lem3209551 A x s t P h1)). Qed.
Lemma lem3209686 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3209687 {A : Type'} (_32996 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term167 A s t P _32996.
Proof. exact (@lem3209579 A s t P x h1 _32996). Qed.
Lemma lem3209688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (_32996 : A) : (term167 A s t P _32996) = (term163 A s t P _32996).
Proof. exact (eq_refl (term167 A s t P _32996)). Qed.
Lemma lem3209689 {A : Type'} (_32996 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term163 A s t P _32996.
Proof. exact (EQ_MP (@lem3209688 A s t P _32996) (@lem3209687 A _32996 s t P x h1)). Qed.
Lemma lem3209690 {A : Type'} (_32997 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term167 A s t P _32997.
Proof. exact (@lem3209610 A s t P x h1 _32997). Qed.
Lemma lem3209691 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (_32997 : A) : (term167 A s t P _32997) = (term163 A s t P _32997).
Proof. exact (eq_refl (term167 A s t P _32997)). Qed.
Lemma lem3209692 {A : Type'} (_32997 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term163 A s t P _32997.
Proof. exact (EQ_MP (@lem3209691 A s t P _32997) (@lem3209690 A _32997 s t P x h1)). Qed.
Lemma lem3209693 {A : Type'} (_32998 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term168 A s P _32998.
Proof. exact (@lem3209631 A x s t P h1 _32998). Qed.
Lemma lem3209694 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32998 : A) : (term168 A s P _32998) = (term65 A s P _32998).
Proof. exact (eq_refl (term168 A s P _32998)). Qed.
Lemma lem3209702 {A : Type'} (_33001 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term168 A t P _33001.
Proof. exact (@lem3209678 A x s t P h1 _33001). Qed.
Lemma lem3209703 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33001 : A) : (term168 A t P _33001) = (term65 A t P _33001).
Proof. exact (eq_refl (term168 A t P _33001)). Qed.
Lemma lem3209712 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A s P x) : term169 A P x.
Proof. exact (proj2 (@lem3209543 A s P x h1)). Qed.
Lemma lem3209718 {A : Type'} (_32996 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term65 A s P _32996.
Proof. exact (proj1 (@lem3209689 A _32996 s t P x h1)). Qed.
Lemma lem3209728 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A t P x) : term169 A P x.
Proof. exact (proj2 (@lem3209544 A t P x h1)). Qed.
Lemma lem3209740 {A : Type'} (_32997 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term65 A t P _32997.
Proof. exact (proj2 (@lem3209692 A _32997 s t P x h1)). Qed.
Lemma lem3209746 {A : Type'} (_32998 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term65 A s P _32998.
Proof. exact (EQ_MP (@lem3209694 A s P _32998) (@lem3209693 A _32998 x s t P h1)). Qed.
Lemma lem3209754 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term169 A P x.
Proof. exact (proj2 (@lem3209550 A x s t P h1)). Qed.
Lemma lem3209756 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3209768 {A : Type'} (_33001 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term65 A t P _33001.
Proof. exact (EQ_MP (@lem3209703 A t P _33001) (@lem3209702 A _33001 x s t P h1)). Qed.
Lemma lem3209770 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term169 A P x.
Proof. exact (proj2 (@lem3209550 A x s t P h1)). Qed.
Lemma lem3209772 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3209774 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A s P x) : @IN A x s.
Proof. exact (proj1 (@lem3209543 A s P x h1)). Qed.
Lemma lem3209775 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A s P x) : term170 A x s.
Proof. exact (fun h0 : term164 A x s => @lem3209774 A s P x h1). Qed.
Lemma lem3209777 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209778 {A : Type'} (x : A) (s : A -> Prop) : (term170 A x s) = (@IN A x s).
Proof. exact (@lem3209777 (@IN A x s)). Qed.
Lemma lem3209779 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A s P x) : @IN A x s.
Proof. exact (EQ_MP (@lem3209778 A x s) (@lem3209775 A s P x h1)). Qed.
Lemma lem3209785 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3209786 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : (term65 A s P _32996) = (term172 A P _32996 s).
Proof. exact (@lem3209785 (P _32996) (term164 A _32996 s)). Qed.
Lemma lem3209792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209793 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : (term173 A s P _32996) = (term174 A P _32996 s).
Proof. exact (MK_COMB (@lem3209792) (@lem3209786 A P _32996 s)). Qed.
Lemma lem3209799 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : (term172 A P _32996 s) = (term172 A P _32996 s).
Proof. exact (eq_refl (term172 A P _32996 s)). Qed.
Lemma lem3209800 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : ((term65 A s P _32996) = (term172 A P _32996 s)) = ((term172 A P _32996 s) = (term172 A P _32996 s)).
Proof. exact (MK_COMB (@lem3209793 A P _32996 s) (@lem3209799 A P _32996 s)). Qed.
Lemma lem3209802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3209803 (x : Prop) : (x = x) = True.
Proof. exact (@lem3209802 Prop x). Qed.
Lemma lem3209804 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : ((term172 A P _32996 s) = (term172 A P _32996 s)) = True.
Proof. exact (@lem3209803 (term172 A P _32996 s)). Qed.
Lemma lem3209805 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : ((term65 A s P _32996) = (term172 A P _32996 s)) = True.
Proof. exact (TRANS (@lem3209800 A P _32996 s) (@lem3209804 A P _32996 s)). Qed.
Lemma lem3209806 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : True = ((term65 A s P _32996) = (term172 A P _32996 s)).
Proof. exact (SYM (@lem3209805 A P _32996 s)). Qed.
Lemma lem3209807 {A : Type'} (P : A -> Prop) (_32996 : A) (s : A -> Prop) : (term65 A s P _32996) = (term172 A P _32996 s).
Proof. exact (EQ_MP (@lem3209806 A P _32996 s) (@lem0)). Qed.
Lemma lem3209808 {A : Type'} (_32996 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term172 A P _32996 s.
Proof. exact (EQ_MP (@lem3209807 A P _32996 s) (@lem3209718 A _32996 s t P x h1)). Qed.
Lemma lem3209810 (b : Prop) (a : Prop) : (a \/ b) = (term175 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3209811 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32996 : A) : (term172 A P _32996 s) = (term176 A s P _32996).
Proof. exact (@lem3209810 (term164 A _32996 s) (P _32996)). Qed.
Lemma lem3209813 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3209814 {A : Type'} (_32996 : A) (s : A -> Prop) : (term177 A _32996 s) = (@IN A _32996 s).
Proof. exact (@lem3209813 (@IN A _32996 s)). Qed.
Lemma lem3209815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3209816 {A : Type'} (_32996 : A) (s : A -> Prop) : (term178 A _32996 s) = (term179 A _32996 s).
Proof. exact (MK_COMB (@lem3209815) (@lem3209814 A _32996 s)). Qed.
Lemma lem3209817 {A : Type'} (P : A -> Prop) (_32996 : A) : (P _32996) = (P _32996).
Proof. exact (eq_refl (P _32996)). Qed.
Lemma lem3209818 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32996 : A) : (term176 A s P _32996) = (term38 A s P _32996).
Proof. exact (MK_COMB (@lem3209816 A _32996 s) (@lem3209817 A P _32996)). Qed.
Lemma lem3209819 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32996 : A) : (term172 A P _32996 s) = (term38 A s P _32996).
Proof. exact (TRANS (@lem3209811 A s P _32996) (@lem3209818 A s P _32996)). Qed.
Lemma lem3209822 {A : Type'} (_32996 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term38 A s P _32996.
Proof. exact (EQ_MP (@lem3209819 A s P _32996) (@lem3209808 A _32996 s t P x h1)). Qed.
Lemma lem3209823 {A : Type'} (_32996 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term38 A s P _32996.
Proof. exact (@lem3209822 A _32996 s t P x h1). Qed.
Lemma lem3209824 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term38 A s P x.
Proof. exact (@lem3209823 A x s t P x h1). Qed.
Lemma lem3209827 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A s P x) : P x.
Proof. exact (@lem3209824 A s t P x h1 (@lem3209779 A s P x h2)). Qed.
Lemma lem3209828 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A s P x) : term180 A P x.
Proof. exact (fun h0 : term169 A P x => @lem3209827 A t s P x h1 h2). Qed.
Lemma lem3209830 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209831 {A : Type'} (P : A -> Prop) (x : A) : (term180 A P x) = (P x).
Proof. exact (@lem3209830 (P x)). Qed.
Lemma lem3209832 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A s P x) : P x.
Proof. exact (EQ_MP (@lem3209831 A P x) (@lem3209828 A t s P x h1 h2)). Qed.
Lemma lem3209835 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3209837 {A : Type'} (P : A -> Prop) (x : A) : (term169 A P x) = (term181 A P x).
Proof. exact (@lem3209835 (P x)). Qed.
Lemma lem3209840 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A s P x) : term181 A P x.
Proof. exact (EQ_MP (@lem3209837 A P x) (@lem3209712 A s P x h1)). Qed.
Lemma lem3209843 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A s P x) : False.
Proof. exact (@lem3209840 A s P x h2 (@lem3209832 A t s P x h1 h2)). Qed.
Lemma lem3209844 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A s P x) : term182.
Proof. exact (fun h0 : ~ False => @lem3209843 A t s P x h1 h2). Qed.
Lemma lem3209846 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209847 : term182 = False.
Proof. exact (@lem3209846 False). Qed.
Lemma lem3209848 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A s P x) : False.
Proof. exact (EQ_MP (@lem3209847) (@lem3209844 A t s P x h1 h2)). Qed.
Lemma lem3209850 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A t P x) : @IN A x t.
Proof. exact (proj1 (@lem3209544 A t P x h1)). Qed.
Lemma lem3209851 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A t P x) : term170 A x t.
Proof. exact (fun h0 : term164 A x t => @lem3209850 A t P x h1). Qed.
Lemma lem3209853 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209854 {A : Type'} (x : A) (t : A -> Prop) : (term170 A x t) = (@IN A x t).
Proof. exact (@lem3209853 (@IN A x t)). Qed.
Lemma lem3209855 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A t P x) : @IN A x t.
Proof. exact (EQ_MP (@lem3209854 A x t) (@lem3209851 A t P x h1)). Qed.
Lemma lem3209861 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3209862 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : (term65 A t P _32997) = (term172 A P _32997 t).
Proof. exact (@lem3209861 (P _32997) (term164 A _32997 t)). Qed.
Lemma lem3209868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209869 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : (term173 A t P _32997) = (term174 A P _32997 t).
Proof. exact (MK_COMB (@lem3209868) (@lem3209862 A P _32997 t)). Qed.
Lemma lem3209875 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : (term172 A P _32997 t) = (term172 A P _32997 t).
Proof. exact (eq_refl (term172 A P _32997 t)). Qed.
Lemma lem3209876 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : ((term65 A t P _32997) = (term172 A P _32997 t)) = ((term172 A P _32997 t) = (term172 A P _32997 t)).
Proof. exact (MK_COMB (@lem3209869 A P _32997 t) (@lem3209875 A P _32997 t)). Qed.
Lemma lem3209878 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3209879 (x : Prop) : (x = x) = True.
Proof. exact (@lem3209878 Prop x). Qed.
Lemma lem3209880 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : ((term172 A P _32997 t) = (term172 A P _32997 t)) = True.
Proof. exact (@lem3209879 (term172 A P _32997 t)). Qed.
Lemma lem3209881 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : ((term65 A t P _32997) = (term172 A P _32997 t)) = True.
Proof. exact (TRANS (@lem3209876 A P _32997 t) (@lem3209880 A P _32997 t)). Qed.
Lemma lem3209882 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : True = ((term65 A t P _32997) = (term172 A P _32997 t)).
Proof. exact (SYM (@lem3209881 A P _32997 t)). Qed.
Lemma lem3209883 {A : Type'} (P : A -> Prop) (_32997 : A) (t : A -> Prop) : (term65 A t P _32997) = (term172 A P _32997 t).
Proof. exact (EQ_MP (@lem3209882 A P _32997 t) (@lem0)). Qed.
Lemma lem3209884 {A : Type'} (_32997 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term172 A P _32997 t.
Proof. exact (EQ_MP (@lem3209883 A P _32997 t) (@lem3209740 A _32997 s t P x h1)). Qed.
Lemma lem3209886 (b : Prop) (a : Prop) : (a \/ b) = (term175 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3209887 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_32997 : A) : (term172 A P _32997 t) = (term176 A t P _32997).
Proof. exact (@lem3209886 (term164 A _32997 t) (P _32997)). Qed.
Lemma lem3209889 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3209890 {A : Type'} (_32997 : A) (t : A -> Prop) : (term177 A _32997 t) = (@IN A _32997 t).
Proof. exact (@lem3209889 (@IN A _32997 t)). Qed.
Lemma lem3209891 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3209892 {A : Type'} (_32997 : A) (t : A -> Prop) : (term178 A _32997 t) = (term179 A _32997 t).
Proof. exact (MK_COMB (@lem3209891) (@lem3209890 A _32997 t)). Qed.
Lemma lem3209893 {A : Type'} (P : A -> Prop) (_32997 : A) : (P _32997) = (P _32997).
Proof. exact (eq_refl (P _32997)). Qed.
Lemma lem3209894 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_32997 : A) : (term176 A t P _32997) = (term38 A t P _32997).
Proof. exact (MK_COMB (@lem3209892 A _32997 t) (@lem3209893 A P _32997)). Qed.
Lemma lem3209895 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_32997 : A) : (term172 A P _32997 t) = (term38 A t P _32997).
Proof. exact (TRANS (@lem3209887 A t P _32997) (@lem3209894 A t P _32997)). Qed.
Lemma lem3209898 {A : Type'} (_32997 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term38 A t P _32997.
Proof. exact (EQ_MP (@lem3209895 A t P _32997) (@lem3209884 A _32997 s t P x h1)). Qed.
Lemma lem3209899 {A : Type'} (_32997 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term38 A t P _32997.
Proof. exact (@lem3209898 A _32997 s t P x h1). Qed.
Lemma lem3209900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : term38 A t P x.
Proof. exact (@lem3209899 A x s t P x h1). Qed.
Lemma lem3209903 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A t P x) : P x.
Proof. exact (@lem3209900 A s t P x h1 (@lem3209855 A t P x h2)). Qed.
Lemma lem3209904 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A t P x) : term180 A P x.
Proof. exact (fun h0 : term169 A P x => @lem3209903 A s t P x h1 h2). Qed.
Lemma lem3209906 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209907 {A : Type'} (P : A -> Prop) (x : A) : (term180 A P x) = (P x).
Proof. exact (@lem3209906 (P x)). Qed.
Lemma lem3209908 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A t P x) : P x.
Proof. exact (EQ_MP (@lem3209907 A P x) (@lem3209904 A s t P x h1 h2)). Qed.
Lemma lem3209911 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3209913 {A : Type'} (P : A -> Prop) (x : A) : (term169 A P x) = (term181 A P x).
Proof. exact (@lem3209911 (P x)). Qed.
Lemma lem3209916 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term64 A t P x) : term181 A P x.
Proof. exact (EQ_MP (@lem3209913 A P x) (@lem3209728 A t P x h1)). Qed.
Lemma lem3209919 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A t P x) : False.
Proof. exact (@lem3209916 A t P x h2 (@lem3209908 A s t P x h1 h2)). Qed.
Lemma lem3209920 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A t P x) : term182.
Proof. exact (fun h0 : ~ False => @lem3209919 A s t P x h1 h2). Qed.
Lemma lem3209922 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209923 : term182 = False.
Proof. exact (@lem3209922 False). Qed.
Lemma lem3209924 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) (h2 : term64 A t P x) : False.
Proof. exact (EQ_MP (@lem3209923) (@lem3209920 A s t P x h1 h2)). Qed.
Lemma lem3209926 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3209927 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term170 A x s.
Proof. exact (fun h0 : term164 A x s => @lem3209926 A x s h1). Qed.
Lemma lem3209929 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209930 {A : Type'} (x : A) (s : A -> Prop) : (term170 A x s) = (@IN A x s).
Proof. exact (@lem3209929 (@IN A x s)). Qed.
Lemma lem3209931 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem3209930 A x s) (@lem3209927 A x s h1)). Qed.
Lemma lem3209937 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3209938 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : (term65 A s P _32998) = (term172 A P _32998 s).
Proof. exact (@lem3209937 (P _32998) (term164 A _32998 s)). Qed.
Lemma lem3209944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3209945 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : (term173 A s P _32998) = (term174 A P _32998 s).
Proof. exact (MK_COMB (@lem3209944) (@lem3209938 A P _32998 s)). Qed.
Lemma lem3209951 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : (term172 A P _32998 s) = (term172 A P _32998 s).
Proof. exact (eq_refl (term172 A P _32998 s)). Qed.
Lemma lem3209952 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : ((term65 A s P _32998) = (term172 A P _32998 s)) = ((term172 A P _32998 s) = (term172 A P _32998 s)).
Proof. exact (MK_COMB (@lem3209945 A P _32998 s) (@lem3209951 A P _32998 s)). Qed.
Lemma lem3209954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3209955 (x : Prop) : (x = x) = True.
Proof. exact (@lem3209954 Prop x). Qed.
Lemma lem3209956 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : ((term172 A P _32998 s) = (term172 A P _32998 s)) = True.
Proof. exact (@lem3209955 (term172 A P _32998 s)). Qed.
Lemma lem3209957 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : ((term65 A s P _32998) = (term172 A P _32998 s)) = True.
Proof. exact (TRANS (@lem3209952 A P _32998 s) (@lem3209956 A P _32998 s)). Qed.
Lemma lem3209958 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : True = ((term65 A s P _32998) = (term172 A P _32998 s)).
Proof. exact (SYM (@lem3209957 A P _32998 s)). Qed.
Lemma lem3209959 {A : Type'} (P : A -> Prop) (_32998 : A) (s : A -> Prop) : (term65 A s P _32998) = (term172 A P _32998 s).
Proof. exact (EQ_MP (@lem3209958 A P _32998 s) (@lem0)). Qed.
Lemma lem3209960 {A : Type'} (_32998 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term172 A P _32998 s.
Proof. exact (EQ_MP (@lem3209959 A P _32998 s) (@lem3209746 A _32998 x s t P h1)). Qed.
Lemma lem3209962 (b : Prop) (a : Prop) : (a \/ b) = (term175 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3209963 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32998 : A) : (term172 A P _32998 s) = (term176 A s P _32998).
Proof. exact (@lem3209962 (term164 A _32998 s) (P _32998)). Qed.
Lemma lem3209965 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3209966 {A : Type'} (_32998 : A) (s : A -> Prop) : (term177 A _32998 s) = (@IN A _32998 s).
Proof. exact (@lem3209965 (@IN A _32998 s)). Qed.
Lemma lem3209967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3209968 {A : Type'} (_32998 : A) (s : A -> Prop) : (term178 A _32998 s) = (term179 A _32998 s).
Proof. exact (MK_COMB (@lem3209967) (@lem3209966 A _32998 s)). Qed.
Lemma lem3209969 {A : Type'} (P : A -> Prop) (_32998 : A) : (P _32998) = (P _32998).
Proof. exact (eq_refl (P _32998)). Qed.
Lemma lem3209970 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32998 : A) : (term176 A s P _32998) = (term38 A s P _32998).
Proof. exact (MK_COMB (@lem3209968 A _32998 s) (@lem3209969 A P _32998)). Qed.
Lemma lem3209971 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_32998 : A) : (term172 A P _32998 s) = (term38 A s P _32998).
Proof. exact (TRANS (@lem3209963 A s P _32998) (@lem3209970 A s P _32998)). Qed.
Lemma lem3209974 {A : Type'} (_32998 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term38 A s P _32998.
Proof. exact (EQ_MP (@lem3209971 A s P _32998) (@lem3209960 A _32998 x s t P h1)). Qed.
Lemma lem3209975 {A : Type'} (_32998 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term38 A s P _32998.
Proof. exact (@lem3209974 A _32998 x s t P h1). Qed.
Lemma lem3209976 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term38 A s P x.
Proof. exact (@lem3209975 A x x s t P h1). Qed.
Lemma lem3209979 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : P x.
Proof. exact (@lem3209976 A x s t P h1 (@lem3209931 A x s h2)). Qed.
Lemma lem3209980 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : term180 A P x.
Proof. exact (fun h0 : term169 A P x => @lem3209979 A t P x s h1 h2). Qed.
Lemma lem3209982 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209983 {A : Type'} (P : A -> Prop) (x : A) : (term180 A P x) = (P x).
Proof. exact (@lem3209982 (P x)). Qed.
Lemma lem3209984 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : P x.
Proof. exact (EQ_MP (@lem3209983 A P x) (@lem3209980 A t P x s h1 h2)). Qed.
Lemma lem3209987 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3209989 {A : Type'} (P : A -> Prop) (x : A) : (term169 A P x) = (term181 A P x).
Proof. exact (@lem3209987 (P x)). Qed.
Lemma lem3209992 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term181 A P x.
Proof. exact (EQ_MP (@lem3209989 A P x) (@lem3209754 A x s t P h1)). Qed.
Lemma lem3209995 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (@lem3209992 A x s t P h1 (@lem3209984 A t P x s h1 h2)). Qed.
Lemma lem3209996 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : term182.
Proof. exact (fun h0 : ~ False => @lem3209995 A t P x s h1 h2). Qed.
Lemma lem3209998 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3209999 : term182 = False.
Proof. exact (@lem3209998 False). Qed.
Lemma lem3210000 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3209999) (@lem3209996 A t P x s h1 h2)). Qed.
Lemma lem3210002 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3210003 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : term170 A x t.
Proof. exact (fun h0 : term164 A x t => @lem3210002 A x t h1). Qed.
Lemma lem3210005 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3210006 {A : Type'} (x : A) (t : A -> Prop) : (term170 A x t) = (@IN A x t).
Proof. exact (@lem3210005 (@IN A x t)). Qed.
Lemma lem3210007 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (EQ_MP (@lem3210006 A x t) (@lem3210003 A x t h1)). Qed.
Lemma lem3210013 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3210014 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : (term65 A t P _33001) = (term172 A P _33001 t).
Proof. exact (@lem3210013 (P _33001) (term164 A _33001 t)). Qed.
Lemma lem3210020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210021 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : (term173 A t P _33001) = (term174 A P _33001 t).
Proof. exact (MK_COMB (@lem3210020) (@lem3210014 A P _33001 t)). Qed.
Lemma lem3210027 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : (term172 A P _33001 t) = (term172 A P _33001 t).
Proof. exact (eq_refl (term172 A P _33001 t)). Qed.
Lemma lem3210028 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : ((term65 A t P _33001) = (term172 A P _33001 t)) = ((term172 A P _33001 t) = (term172 A P _33001 t)).
Proof. exact (MK_COMB (@lem3210021 A P _33001 t) (@lem3210027 A P _33001 t)). Qed.
Lemma lem3210030 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3210031 (x : Prop) : (x = x) = True.
Proof. exact (@lem3210030 Prop x). Qed.
Lemma lem3210032 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : ((term172 A P _33001 t) = (term172 A P _33001 t)) = True.
Proof. exact (@lem3210031 (term172 A P _33001 t)). Qed.
Lemma lem3210033 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : ((term65 A t P _33001) = (term172 A P _33001 t)) = True.
Proof. exact (TRANS (@lem3210028 A P _33001 t) (@lem3210032 A P _33001 t)). Qed.
Lemma lem3210034 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : True = ((term65 A t P _33001) = (term172 A P _33001 t)).
Proof. exact (SYM (@lem3210033 A P _33001 t)). Qed.
Lemma lem3210035 {A : Type'} (P : A -> Prop) (_33001 : A) (t : A -> Prop) : (term65 A t P _33001) = (term172 A P _33001 t).
Proof. exact (EQ_MP (@lem3210034 A P _33001 t) (@lem0)). Qed.
Lemma lem3210036 {A : Type'} (_33001 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term172 A P _33001 t.
Proof. exact (EQ_MP (@lem3210035 A P _33001 t) (@lem3209768 A _33001 x s t P h1)). Qed.
Lemma lem3210038 (b : Prop) (a : Prop) : (a \/ b) = (term175 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3210039 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33001 : A) : (term172 A P _33001 t) = (term176 A t P _33001).
Proof. exact (@lem3210038 (term164 A _33001 t) (P _33001)). Qed.
Lemma lem3210041 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3210042 {A : Type'} (_33001 : A) (t : A -> Prop) : (term177 A _33001 t) = (@IN A _33001 t).
Proof. exact (@lem3210041 (@IN A _33001 t)). Qed.
Lemma lem3210043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3210044 {A : Type'} (_33001 : A) (t : A -> Prop) : (term178 A _33001 t) = (term179 A _33001 t).
Proof. exact (MK_COMB (@lem3210043) (@lem3210042 A _33001 t)). Qed.
Lemma lem3210045 {A : Type'} (P : A -> Prop) (_33001 : A) : (P _33001) = (P _33001).
Proof. exact (eq_refl (P _33001)). Qed.
Lemma lem3210046 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33001 : A) : (term176 A t P _33001) = (term38 A t P _33001).
Proof. exact (MK_COMB (@lem3210044 A _33001 t) (@lem3210045 A P _33001)). Qed.
Lemma lem3210047 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33001 : A) : (term172 A P _33001 t) = (term38 A t P _33001).
Proof. exact (TRANS (@lem3210039 A t P _33001) (@lem3210046 A t P _33001)). Qed.
Lemma lem3210050 {A : Type'} (_33001 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term38 A t P _33001.
Proof. exact (EQ_MP (@lem3210047 A t P _33001) (@lem3210036 A _33001 x s t P h1)). Qed.
Lemma lem3210051 {A : Type'} (_33001 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term38 A t P _33001.
Proof. exact (@lem3210050 A _33001 x s t P h1). Qed.
Lemma lem3210052 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term38 A t P x.
Proof. exact (@lem3210051 A x x s t P h1). Qed.
Lemma lem3210055 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : P x.
Proof. exact (@lem3210052 A x s t P h1 (@lem3210007 A x t h2)). Qed.
Lemma lem3210056 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : term180 A P x.
Proof. exact (fun h0 : term169 A P x => @lem3210055 A s P x t h1 h2). Qed.
Lemma lem3210058 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3210059 {A : Type'} (P : A -> Prop) (x : A) : (term180 A P x) = (P x).
Proof. exact (@lem3210058 (P x)). Qed.
Lemma lem3210060 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : P x.
Proof. exact (EQ_MP (@lem3210059 A P x) (@lem3210056 A s P x t h1 h2)). Qed.
Lemma lem3210063 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3210065 {A : Type'} (P : A -> Prop) (x : A) : (term169 A P x) = (term181 A P x).
Proof. exact (@lem3210063 (P x)). Qed.
Lemma lem3210068 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : term181 A P x.
Proof. exact (EQ_MP (@lem3210065 A P x) (@lem3209770 A x s t P h1)). Qed.
Lemma lem3210071 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (@lem3210068 A x s t P h1 (@lem3210060 A s P x t h1 h2)). Qed.
Lemma lem3210072 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : term182.
Proof. exact (fun h0 : ~ False => @lem3210071 A s P x t h1 h2). Qed.
Lemma lem3210074 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3210075 : term182 = False.
Proof. exact (@lem3210074 False). Qed.
Lemma lem3210076 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3210075) (@lem3210072 A s P x t h1 h2)). Qed.
Lemma lem3210077 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3210076 A s P x t h1 h2) (fun h3 : False => @lem3209772 A x t h2)). Qed.
Lemma lem3210078 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3210077 A s P x t h1 h2) (@lem3209772 A x t h2)). Qed.
Lemma lem3210079 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3210000 A t P x s h1 h2) (fun h3 : False => @lem3209756 A x s h2)). Qed.
Lemma lem3210080 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3210079 A t P x s h1 h2) (@lem3209756 A x s h2)). Qed.
Lemma lem3210081 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3210078 A s P x t h1 h2) (fun h3 : False => @lem3209686 A x t h2)). Qed.
Lemma lem3210082 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3210081 A s P x t h1 h2) (@lem3209686 A x t h2)). Qed.
Lemma lem3210083 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3210080 A t P x s h1 h2) (fun h3 : False => @lem3209652 A x s h2)). Qed.
Lemma lem3210084 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3210083 A t P x s h1 h2) (@lem3209652 A x s h2)). Qed.
Lemma lem3210085 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3210082 A s P x t h1 h2) (fun h3 : False => @lem3209686 A x t h2)). Qed.
Lemma lem3210086 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3210085 A s P x t h1 h2) (@lem3209686 A x t h2)). Qed.
Lemma lem3210087 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3210084 A t P x s h1 h2) (fun h3 : False => @lem3209652 A x s h2)). Qed.
Lemma lem3210088 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term140 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3210087 A t P x s h1 h2) (@lem3209652 A x s h2)). Qed.
Lemma lem3210089 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term140 A x s t P) : False.
Proof. exact (or_elim (@lem3209554 A x s t P h1) (fun h0 : @IN A x s => @lem3210088 A t P x s h1 h0) (fun h0 : @IN A x t => @lem3210086 A s P x t h1 h0)). Qed.
Lemma lem3210090 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term122 A s t P x) : False.
Proof. exact (or_elim (@lem3209541 A s t P x h1) (fun h0 : term64 A s P x => @lem3209848 A t s P x h1 h0) (fun h0 : term64 A t P x => @lem3209924 A s t P x h1 h0)). Qed.
Lemma lem3210091 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term159 A x s t P) : False.
Proof. exact (or_elim (@lem3209538 A x s t P h1) (fun h0 : term122 A s t P x => @lem3210090 A s t P x h0) (fun h0 : term140 A x s t P => @lem3210089 A x s t P h0)). Qed.
Lemma lem3210092 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term159 A x s t P) : (term159 A x s t P) = False.
Proof. exact (prop_ext (fun h2 : term159 A x s t P => @lem3210091 A x s t P h1) (fun h2 : False => @lem3209538 A x s t P h1)). Qed.
Lemma lem3210093 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term159 A x s t P) : False.
Proof. exact (EQ_MP (@lem3210092 A x s t P h1) (@lem3209538 A x s t P h1)). Qed.
Lemma lem3210094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : False.
Proof. exact (ex_elim (@lem3209416 A s t P h1) (fun x : A => fun h0 : term161 A s t P x => @lem3210093 A x s t P h0)). Qed.
Lemma lem3210095 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : (term43 A s t P) = False.
Proof. exact (prop_ext (fun h2 : term43 A s t P => @lem3210094 A s t P h1) (fun h2 : False => @lem3208957 A s t P h1)). Qed.
Lemma lem3210096 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : False.
Proof. exact (EQ_MP (@lem3210095 A s t P h1) (@lem3208957 A s t P h1)). Qed.
Lemma lem3210097 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : term42 A s t P.
Proof. exact (fun h0 : term43 A s t P => @lem3210096 A s t P h0). Qed.
Lemma lem3210098 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term14 A s t P) = (term17 A s t P).
Proof. exact (EQ_MP (@lem3208956 A s t P) (@lem3210097 A s t P)). Qed.
Lemma lem3210103 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term21 A s P.
Proof. exact (fun t : A -> Prop => @lem3210098 A s t P). Qed.
Lemma lem3210108 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (fun s : A -> Prop => @lem3210103 A s P). Qed.
Lemma lem3210113 {A : Type'} : term29 A.
Proof. exact (fun P : A -> Prop => @lem3210108 A P). Qed.
Lemma lem3210114 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem3208952 A) (@lem3210113 A)). Qed.
Lemma lem3210116 {A : Type'} : term31 A.
Proof. exact (@lem3208814 A (@lem3210114 A)). Qed.
Lemma lem3210117 {A : Type'} (h1 : term32 A) : False.
Proof. exact (@lem3210116 A (@lem3208798 A h1)). Qed.
Lemma lem3210118 {A : Type'} (h1 : term32 A) : (term32 A) = False.
Proof. exact (prop_ext (fun h2 : term32 A => @lem3210117 A h1) (fun h2 : False => @lem3208798 A h1)). Qed.
Lemma lem3210119 {A : Type'} (h1 : term32 A) : False.
Proof. exact (EQ_MP (@lem3210118 A h1) (@lem3208798 A h1)). Qed.
Lemma lem3210120 {A : Type'} : term31 A.
Proof. exact (fun h0 : term32 A => @lem3210119 A h0). Qed.
Lemma lem3210121 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem3208797 A) (@lem3210120 A)). Qed.
Lemma lem3210122 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3208793 A) (@lem3210121 A)). Qed.
